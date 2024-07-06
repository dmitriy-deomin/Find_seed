use std::fs::{File, OpenOptions};
use std::{fs, io, thread};
use std::collections::HashSet;
use std::io::{BufRead, BufReader, BufWriter, Lines, Read, stdout, Write};
use std::path::Path;
use std::str::FromStr;
use std::sync::{Arc, mpsc};
use std::time::{Duration, Instant};
use base58::{FromBase58, ToBase58};
use bech32::{segwit, hrp};
use bincode::{deserialize_from, serialize_into};
use bip32::{DerivationPath, ExtendedPrivateKey, XPrv};
use bip32::secp256k1::ecdsa::SigningKey;
use bip39::{Language, Mnemonic, Seed};
use rand::{Rng, thread_rng};
use rand::seq::SliceRandom;
use ripemd::{Ripemd160, Digest as Ripemd160Digest};

use crate::color::{blue, cyan, green, magenta, red};
use rustils::parse::boolean::string_to_bool;
use sha2::{Sha256, Digest};
use sv::util::hash160;
use tiny_keccak::{Hasher, Keccak};


#[cfg(not(windows))]
use rust_secp256k1::{PublicKey, Secp256k1, SecretKey};

#[cfg(windows)]
mod ice_library;

#[cfg(windows)]
use ice_library::IceLibrary;

mod color;
mod data;

pub const LEGACY_BTC: u8 = 0x00;
pub const LEGACY_BTG: u8 = 0x26;
pub const LEGACY_DASH: u8 = 0x4C;
pub const BIP49_BTC: u8 = 0x05;
pub const BIP49_BTG: u8 = 0x17;
pub const BIP49_DASH: u8 = 0x10;
pub const LEGACY_DOGE: u8 = 0x1E;
pub const BIP49_DOGE: u8 = 0x16;
pub const LEGACY_LTC: u8 = 0x30;

const BACKSPACE: char = 8u8 as char;
const FILE_CONFIG: &str = "confSeed.txt";
const FILE_LIST: &str = "bip39.txt";


#[tokio::main]
async fn main() {
    let version: &str = env!("CARGO_PKG_VERSION");
    println!("{}", blue("==================="));
    println!("{}{}", blue("FIND SEED v:"), magenta(version));
    println!("{}", blue("==================="));

    //Чтение настроек, и если их нет создадим
    //-----------------------------------------------------------------
    let conf = match lines_from_file(&FILE_CONFIG) {
        Ok(text) => { text }
        Err(_) => {
            add_v_file(&FILE_CONFIG, data::get_conf_text().to_string());
            lines_from_file(&FILE_CONFIG).unwrap()
        }
    };

    //рандом
    let mut rng = rand::thread_rng();

    //количество ядер процессора
    let count_cpu = num_cpus::get();

    let cpu_core: usize = first_word(&conf[0].to_string()).to_string().parse::<usize>().unwrap();
    let mut dlinn_a_pasvord: usize = first_word(&conf[1].to_string()).to_string().parse::<usize>().unwrap();
    let mut alvabet = first_word(&conf[2].to_string()).to_string();
    let len_uvelichenie = string_to_bool(first_word(&conf[3].to_string()).to_string());
    let start_perebor = first_word(&conf[4].to_string()).to_string();
    let mode: usize = first_word(&conf[5].to_string()).to_string().parse::<usize>().unwrap();
    let comb_perebor_left_: usize = first_word(&conf[6].to_string()).to_string().parse::<usize>().unwrap();
    let show_info = string_to_bool(first_word(&conf[7].to_string()).to_string());
    let rand_alfabet = string_to_bool(first_word(&conf[8].to_string()).to_string());
    let size_rand_alfabet = first_word(&conf[9].to_string()).to_string().parse::<usize>().unwrap();
    let time_save_tekushego_bodbora = first_word(&conf[10].to_string()).to_string().parse::<u32>().unwrap();
    //---------------------------------------------------------------------

    //если укажут меньше или 0
    let comb_perebor_left = if comb_perebor_left_ >= 0 {
        comb_perebor_left_
    } else { 1 };

    //база со всеми адресами
    let mut database: HashSet<[u8; 20]> = HashSet::new();


    //проверим есть ли общая база
    if fs::metadata(Path::new("database.bin")).is_ok() {
        println!("{}", blue("--"));
        println!("{}", green("файл database.bin уже существует,конвертирование пропущено"));
        println!("{}", green("ЗАГРУЗКА БАЗЫ ИЗ database.bin"));
        // Загрузим HashSet из файла load_from_file-однопоточно
        database = match load_from_file("database.bin") {
            Ok(loaded_set) => {
                println!("{}", green(format!("ГОТОВО, В БАЗЕ:{} АДРЕСОВ", loaded_set.len())));
                loaded_set
            }
            Err(e) => {
                eprintln!("{}", red(format!("ОШИБКА: {}", e)));
                return;
            }
        };

        println!("{}", blue("--"));
    } else {
        println!("{}", blue("--"));
        //провереряем если файл с хешами BTC
        //--------------------------------------------------------------------------------------------
        if fs::metadata(Path::new("btc_h160.bin")).is_ok() {
            println!("{}", green("файл btc_h160.bin уже существует,конвертирование пропущено"));
        } else {
            //проверяем есть ли файл(создаём) и считаем сколько строк
            let len_btc_txt = get_len_find_create("btc.txt");

            println!("{}", blue("конвертирование адресов в h160 и сохранение в btc_h160.bin"));
            //конвертируем в h160 и записываем в файл рядом
            //создаём файл
            let mut file = File::create("btc_h160.bin").unwrap();
            //ищем в списке нужные делаем им харакири и ложим обрубки в файл
            let mut len_btc = 0;
            for (index, address) in get_bufer_file("btc.txt").lines().enumerate() {
                let address = address.expect("Ошибка чтения адреса со строки");

                //адреса с bc1...
                let binding = if address.starts_with("bc1") {
                    bip84_to_h160(address)
                } else {
                    //адреса 1.. 3...
                    match address.from_base58() {
                        Ok(value) => {
                            let mut a: [u8; 20] = [0; 20];
                            if value.len() >= 21 {
                                a.copy_from_slice(&value.as_slice()[1..21]);
                                a
                            } else {
                                eprintln!("{}", red(format!("ОШИБКА, АДРЕС НЕ ВАЛИДЕН строка: {} {}", index + 1, address)));
                                continue; // Skip this address and move to the next
                            }
                        }
                        Err(_) => {
                            eprintln!("{}", red(format!("ОШИБКА ДЕКОДИРОВАНИЯ В base58 строка: {} {}", index + 1, address)));
                            continue; // Skip this address and move to the next
                        }
                    }
                };


                if let Err(e) = file.write_all(&binding) {
                    eprintln!("Не удалось записать в файл: {}", e);
                } else {
                    len_btc = len_btc + 1;
                }
            }
            println!("{}", blue(format!("конвертировано адресов в h160:{}/{}", green(len_btc_txt), green(len_btc))));
        }
        //-----------------------------------------------------------------------------------------------

        println!("{}", blue("--"));
        //провереряем если файл с хешами BTC
        //--------------------------------------------------------------------------------------------
        if fs::metadata(Path::new("btc_h160.bin")).is_ok() {
            println!("{}", green("файл btc_h160.bin уже существует,конвертирование пропущено"));
        } else {
            //проверяем есть ли файл(создаём) и считаем сколько строк
            let len_btc_txt = get_len_find_create("btc.txt");

            println!("{}", blue("конвертирование адресов в h160 и сохранение в btc_h160.bin"));
            //конвертируем в h160 и записываем в файл рядом
            //создаём файл
            let mut file = File::create("btc_h160.bin").unwrap();
            //ищем в списке нужные делаем им харакири и ложим обрубки в файл
            let mut len_btc = 0;
            for (index, address) in get_bufer_file("btc.txt").lines().enumerate() {
                let address = address.expect("Ошибка чтения адреса со строки");

                //адреса с bc1...
                let binding = if address.starts_with("bc1") {
                    bip84_to_h160(address)
                } else {
                    //адреса 1.. 3...
                    match address.from_base58() {
                        Ok(value) => {
                            let mut a: [u8; 20] = [0; 20];
                            if value.len() >= 21 {
                                a.copy_from_slice(&value.as_slice()[1..21]);
                                a
                            } else {
                                eprintln!("{}", red(format!("ОШИБКА, АДРЕС НЕ ВАЛИДЕН строка: {} {}", index + 1, address)));
                                continue; // Skip this address and move to the next
                            }
                        }
                        Err(_) => {
                            eprintln!("{}", red(format!("ОШИБКА ДЕКОДИРОВАНИЯ В base58 строка: {} {}", index + 1, address)));
                            continue; // Skip this address and move to the next
                        }
                    }
                };


                if let Err(e) = file.write_all(&binding) {
                    eprintln!("Не удалось записать в файл: {}", e);
                } else {
                    len_btc = len_btc + 1;
                }
            }
            println!("{}", blue(format!("конвертировано адресов в h160:{}/{}", green(len_btc_txt), green(len_btc))));
        }
        //-----------------------------------------------------------------------------------------------


        println!("{}", blue("--"));

        //провереряем если файл с хешами DOGECOIN
        //--------------------------------------------------------------------------------------------
        if fs::metadata(Path::new("dogecoin_h160.bin")).is_ok() {
            println!("{}", green("файл dogecoin_h160.bin уже существует,конвертирование пропущено"));
        } else {
            //проверяем есть ли файл(создаём) и считаем сколько строк
            let len_btc_txt = get_len_find_create("dogecoin.txt");

            println!("{}", blue("конвертирование адресов в h160 и сохранение в dogecoin_h160.bin"));
            //конвертируем в h160 и записываем в файл рядом
            //создаём файл
            let mut file = File::create("dogecoin_h160.bin").unwrap();
            //ищем в списке нужные делаем им харакири и ложим обрубки в файл
            let mut len_btc = 0;
            for (index, address) in get_bufer_file("dogecoin.txt").lines().enumerate() {
                let binding = match address.expect("REASON").from_base58() {
                    Ok(value) => value,
                    Err(_err) => {
                        eprintln!("{}", red(format!("ОШИБКА ДЕКОДИРОВАНИЯ В base58 строка:{}", index + 1)));
                        continue; // Пропускаем этот адрес и переходим к следующему
                    }
                };

                let mut a: [u8; 20] = [0; 20];

                if binding.len() >= 21 {
                    a.copy_from_slice(&binding.as_slice()[1..21]);
                    if let Err(e) = file.write_all(&a) {
                        eprintln!("Не удалось записать в файл: {}", e);
                    } else {
                        len_btc = len_btc + 1;
                    }
                } else {
                    eprintln!("{}", red(format!("ОШИБКА,АДРЕСС НЕ ВАЛИДЕН строка:{}", index + 1)));
                }
            }
            println!("{}", blue(format!("конвертировано адресов в h160:{}/{}", green(len_btc_txt), green(len_btc))));
        }
        //-----------------------------------------------------------------------------------------------

        println!("{}", blue("--"));

        //провереряем если файл с хешами ETH
        //--------------------------------------------------------------------------------------------
        if fs::metadata(Path::new("eth.bin")).is_ok() {
            println!("{}", green("файл eth.bin уже существует,конвертирование пропущено"));
        } else {
            //проверяем есть ли файл(создаём) и считаем сколько строк
            let len_eth_txt = get_len_find_create("eth.txt");

            println!("{}", blue("конвертирование адресов и сохранение в eth.bin"));

            let file = OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open("eth.bin")
                .unwrap();
            let mut writer = BufWriter::new(file);

            let mut len_eth = 0;
            let mut invalid_addresses = Vec::new();

            for (index, line) in get_bufer_file("eth.txt").lines().enumerate() {
                match line {
                    Ok(address) => match eth_address_to_bytes(&address) {
                        Ok(bytes) => {
                            if let Err(e) = writer.write_all(&bytes) {
                                eprintln!("Не удалось записать в файл: {}", e);
                            } else {
                                len_eth += 1;
                            }
                        }
                        Err(e) => {
                            invalid_addresses.push((index, address, e));
                        }
                    },
                    Err(e) => {
                        invalid_addresses.push((index, "".to_string(), e.to_string()));
                    }
                }
            }

            println!("{}", blue(format!("конвертировано адресов:{}/{}", green(len_eth_txt), green(len_eth))));

            if !invalid_addresses.is_empty() {
                println!("Invalid addresses:");
                for (index, address, error) in invalid_addresses {
                    println!("Line {}: {} ({})", index + 1, address, error);
                }
            }
        }
        //-----------------------------------------------------------------------------------------------

        //провереряем если файл с хешами TRX
        println!("{}", blue("--"));
        //провереряем если файл с хешами BTC
        //--------------------------------------------------------------------------------------------
        if fs::metadata(Path::new("trx_h160.bin")).is_ok() {
            println!("{}", green("файл trx_h160.bin уже существует,конвертирование пропущено"));
        } else {
            //проверяем есть ли файл(создаём) и считаем сколько строк
            let len_trx_txt = get_len_find_create("trx.txt");

            println!("{}", blue("конвертирование адресов в h160 и сохранение в trx_h160.bin"));
            //конвертируем в h160 и записываем в файл рядом
            //создаём файл
            let mut file = File::create("trx_h160.bin").unwrap();
            //ищем в списке нужные делаем им харакири и ложим обрубки в файл
            let mut len_trx = 0;
            for (index, address) in get_bufer_file("trx.txt").lines().enumerate() {
                let binding = match address.expect("REASON").from_base58() {
                    Ok(value) => value,
                    Err(_err) => {
                        eprintln!("{}", red(format!("ОШИБКА ДЕКОДИРОВАНИЯ В base58 строка:{}", index + 1)));
                        continue; // Пропускаем этот адрес и переходим к следующему
                    }
                };

                let mut a: [u8; 20] = [0; 20];

                if binding.len() >= 21 {
                    a.copy_from_slice(&binding.as_slice()[1..21]);
                    if let Err(e) = file.write_all(&a) {
                        eprintln!("Не удалось записать в файл: {}", e);
                    } else {
                        len_trx = len_trx + 1;
                    }
                } else {
                    eprintln!("{}", red(format!("ОШИБКА,АДРЕСС НЕ ВАЛИДЕН строка:{}", index + 1)));
                }
            }
            println!("{}", blue(format!("конвертировано адресов в h160:{}/{}", green(len_trx_txt), green(len_trx))));
        }
        //-----------------------------------------------------------------------------------------------
        println!("{}", blue("--"));


        //************************************************************************************************
        // запись BTC в базу
        let mut colichestvo_btc = 0;
        println!("{}", blue("ЗАПИСЬ BTC ДАННЫХ В БАЗУ.."));
        let mut old_len_baza = database.len();
        let file = File::open("btc_h160.bin").expect("неудалось открыть файл");
        let mut reader = BufReader::new(file);
        loop {
            let mut array = [0u8; 20];
            match reader.read_exact(&mut array) {
                Ok(_) => {
                    colichestvo_btc = colichestvo_btc + 1;
                    database.insert(array);
                }
                Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                _ => {}
            }
        }
        println!("{}{}", blue("Данные BTC успешно загружены в базу:"), green(format!("{}/{colichestvo_btc} шт", database.len() - old_len_baza)));
        println!("{}", blue("--"));


        // запись TRX в базу
        let mut colichestvo_trx = 0;
        println!("{}", blue("ЗАПИСЬ TRX ДАННЫХ В БАЗУ.."));
        let file = File::open("trx_h160.bin").expect("неудалось открыть файл");
        old_len_baza = database.len();
        let mut reader = BufReader::new(file);
        loop {
            let mut array = [0u8; 20];
            match reader.read_exact(&mut array) {
                Ok(_) => {
                    colichestvo_trx = colichestvo_trx + 1;
                    database.insert(array);
                }
                Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                _ => {}
            }
        }
        println!("{}{}", blue("Данные TRX успешно загружены в базу:"), green(format!("{}/{colichestvo_trx} шт", database.len() - old_len_baza)));
        println!("{}", blue("--"));


        // запись DOGECOIN в базу
        let mut colichestvo_dogecoin = 0;
        old_len_baza = database.len();
        println!("{}", blue("ЗАПИСЬ DOGECOIN ДАННЫХ В БАЗУ.."));
        let file = File::open("dogecoin_h160.bin").expect("неудалось открыть файл");
        let mut reader = BufReader::new(file);
        loop {
            let mut array = [0u8; 20];
            match reader.read_exact(&mut array) {
                Ok(_) => {
                    colichestvo_dogecoin = colichestvo_dogecoin + 1;
                    database.insert(array);
                }
                Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                _ => {}
            }
        }
        println!("{}{}", blue("Данные DOGECOIN успешно загружены в базу:"), green(format!("{}/{colichestvo_dogecoin} шт", database.len() - old_len_baza)));
        println!("{}", blue("--"));

        //запись ETH в базу
        let mut colichestvo_eth = 0;
        old_len_baza = database.len();
        println!("{}", blue("ЗАПИСЬ ETH ДАННЫХ В БАЗУ.."));
        let file = File::open("eth.bin").expect("неудалось открыть файл");
        let mut reader = BufReader::new(file);
        loop {
            let mut array = [0u8; 20];
            match reader.read_exact(&mut array) {
                Ok(_) => {
                    colichestvo_eth = colichestvo_eth + 1;
                    database.insert(array);
                }
                Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
                _ => {}
            }
        }
        println!("{}{}", blue("Данные ETH успешно загружены в базу:"), green(format!("{}/{colichestvo_eth} шт", database.len() - old_len_baza)));

        println!("{}", blue("--"));
        println!("{}{}", blue("ИТОГО ЗАГРУЖЕННО В БАЗУ:"), green(format!("{}/{} шт", database.len(), colichestvo_btc + colichestvo_eth + colichestvo_dogecoin + colichestvo_trx)));
        println!("{}", blue("--"));

        // Сохраним HashSet в файл
        println!("{}", blue("СОХРАНЕНИЕ ОБШЕЙ БАЗЫ В database.bin"));
        match save_to_file(&database, "database.bin") {
            Ok(_) => println!("{}", blue("ГОТОВО")),
            Err(e) => eprintln!("{}", red(format!("ОШИБКА {}", e))),
        }
        println!("{}", blue("--"));
    }

    //проверка есть ли в базе вообще чего
    if database.len() == 0 {
        println!("{}", red("БАЗА ПУСТА\nпоместите рядом с программой текстовые файлы со списком адресов:\nbtc.txt,eth.txt,trx.txt,dogecoin.txt"));
        jdem_user_to_close_programm();
        return;
    }


    //ИНфо блок
    //||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
    println!("{}", blue("************************************"));
    println!("{}{}{}", blue("КОЛИЧЕСТВО ЯДЕР ПРОЦЕССОРА:"), green(cpu_core), blue(format!("/{count_cpu}")));
    println!("{}{}", blue("ДЛИНА ПАРОЛЯ:"), green(dlinn_a_pasvord));

    //алфавит
    //-------------------------------------------------------------------------
    //пустой список
    let mut lines = vec!["первый".to_string()];
    if alvabet == "bip39.txt" {
        println!("{}", blue("ИСПОЛЬЗОВАНИЕ bip39.txt ВМЕСТО АЛФАВИТА"));
        get_len_find_create(FILE_LIST);
        //если включенно рандомный список
        let list = read_lines(FILE_LIST);
        println!("{}", blue("-ОБРАБОТКА bip39.txt"));
        // Преобразуем строки в вектор
        lines = list.filter_map(Result::ok).collect::<Vec<String>>();
        if rand_alfabet { lines = get_rand_list(lines, size_rand_alfabet) };
        if rand_alfabet {
            println!("{}{}", blue("СЛУЧАЙНЫЕ ИЗ СПИСКА:"), green("ВКЛЮЧЕННО"));
            println!("{}{}", blue("-КОЛИЧЕСТВО СЛУЧАЙНЫХ ИЗ СПИСКА:"), green(size_rand_alfabet));
            println!("{}{}", blue("-СПИСОК:"), green(lines.join(" ")));
        };
        println!("{}", blue("-ГОТОВО"));
        println!("{}{}", blue("КОЛИЧЕСТВО ЗНАКОВ ПЕРЕБОРА СЛЕВА:"), green(comb_perebor_left));
    }
    //-------------------------------------------------------------------------------
    if mode > 2 {
        println!("{}", red("!!!"));
        println!("{}", red(format!("{mode} ТАКОГО РЕЖИМА РАБОТА ПОКА НЕТ\nесть:\n0 последовательный перебор\n1 рандом\n2 комбинированый")));
        println!("{}", red("!!!"));
        jdem_user_to_close_programm();
        return;
    }
    println!("{}{}", blue("РЕЖИМ ГЕНЕРАЦИИ ПАРОЛЯ:"), green(get_mode_text(mode)));

    if show_info {
        println!("{}{}", blue("ОТОБРАЖЕНИЕ СКОРОСТИ И ТЕКУЩЕГО ПОДБОРА:"), green("ВКЛЮЧЕННО"));
    } else {
        println!("{}{}", blue("ОТОБРАЖЕНИЕ СКОРОСТИ И ТЕКУЩЕГО ПОДБОРА:"), green("ОТКЛЮЧЕННО"));
        println!("{}{}", blue("-ВРЕМЯ АВТОСОХРАНЕНИЯ ТЕКУЩЕГО ПОДБОРА:"), green(time_save_tekushego_bodbora.clone()));
    }

    println!("{}", blue("************************************"));
    //|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

    //главные каналы
    let (main_sender, main_receiver) = mpsc::channel();

    // Запускаем выбраное количество потоков(ядер) постоянно работающих
    //----------------------------------------------------------------------------------
    //будет храниться список запушеных потоков(каналов для связи)
    let mut channels = Vec::new();

    let database = Arc::new(database);

    for ch in 0..cpu_core {
        //создаём для каждого потока отдельный канал для связи
        let (sender, receiver) = mpsc::channel();

        let database_cl = database.clone();

        //главный поток
        let main_sender = main_sender.clone();

        #[cfg(windows)]
        let ice_library = {
            let lib = IceLibrary::new();
            lib.init_secp256_lib();
            lib
        };

        //для всего остального
        #[cfg(not(windows))]
        let secp = Secp256k1::new();

        // let mut start = Instant::now();
        // start.elapsed()

        thread::spawn(move || {
            loop {
                let password_string: String = receiver.recv().unwrap_or("error".to_string());

                let mut start = Instant::now();

                //получаем все возможные
                let mut list_mnemonik = Vec::new();
                for i in 0..2048 {
                    let mut mnemonic_test = String::from(format!("{password_string} "));
                    let word_end = data::WORDS[i as usize].to_string();
                    mnemonic_test.push_str(&word_end);
                    if Mnemonic::validate(&mnemonic_test, Language::English).is_ok() {
                        list_mnemonik.push(mnemonic_test);
                    }
                }

                // println!("validete {:?}",start.elapsed());
                // start = Instant::now();

                for mnemonic_x in list_mnemonik {

                    //готовим
                    let mnemonic = Mnemonic::from_phrase(&mnemonic_x, Language::English).unwrap();
                    let seed = Seed::new(&mnemonic, "");
                    let xprv = XPrv::new(seed.as_bytes()).expect("Failed to create XPrv from seed");

                    // println!("seed {:?}",start.elapsed());
                    // start = Instant::now();

                    //ETH
                    //*******************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/44'/60'/0'/0/0");
                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_u = {
                        ice_library.privatekey_to_publickey(&h)
                    };

                    #[cfg(not(windows))]
                    let pk_u= {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        public_key.serialize_uncompressed()
                    };
                    //----------------------------------------------------------------------------
                    if database_cl.contains(&get_eth_kessak_from_public_key(pk_u)) {
                        if password_string!="инициализация"{
                            let adr_eth = hex::encode(get_eth_kessak_from_public_key(pk_u));
                            print_and_save_eth(hex::encode(&h), format!("ETH: 0x{adr_eth}"), &mnemonic_x);
                        }
                    }
                    //*******************************************************************************
                    // println!("eth {:?}",start.elapsed());
                    // start = Instant::now();

                    //TRX
                    //*******************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/44'/195'/0'/0/0");
                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_u = {
                        ice_library.privatekey_to_publickey(&h)
                    };

                    #[cfg(not(windows))]
                    let pk_u = {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        public_key.serialize_uncompressed()
                    };
                    //----------------------------------------------------------------------------
                    if database_cl.contains(&get_eth_kessak_from_public_key(pk_u)) {
                        if password_string!="инициализация" {
                            let adr_eth = hex::encode(get_eth_kessak_from_public_key(pk_u));
                            let adr_trx = get_trx_from_eth(adr_eth);
                            print_and_save_eth(hex::encode(&h), format!("TRX: {adr_trx}"), &mnemonic_x);
                        }
                    }
                    //*******************************************************************************

                    // println!("trx {:?}",start.elapsed());
                    // start = Instant::now();

                    //BTC bip 44
                    //**********************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/44'/0'/0'/0/0");

                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_c = {
                        let p = ice_library.privatekey_to_publickey(&h);
                        ice_library.publickey_uncompres_to_compres(&p)
                    };

                    #[cfg(not(windows))]
                    let pk_c = {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        public_key.serialize()
                    };
                    //----------------------------------------------------------------------------
                    //получем из них хеш160
                    let h160c = hash160(&pk_c[0..]).0;

                    //проверка наличия в базе BTC compress
                    if database_cl.contains(&h160c) {
                        if password_string!="инициализация" {
                            let address_btc = get_legacy(h160c, LEGACY_BTC);
                            let address = format!("BTC: {}", address_btc);
                            let private_key_c = hex_to_wif_compressed(&h.to_vec());
                            print_and_save(hex::encode(&h), &private_key_c, address, &mnemonic_x);
                        }
                    }

                    // println!("btc 44 {:?}",start.elapsed());
                    // start = Instant::now();

                    //BTC bip 49
                    //**********************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/49'/0'/0'/0/0");

                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_c = {
                        let p = ice_library.privatekey_to_publickey(&h);
                       ice_library.publickey_uncompres_to_compres(&p)
                    };

                    #[cfg(not(windows))]
                    let pk_c = {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        public_key.serialize()
                    };
                    //----------------------------------------------------------------------------
                    //получем из них хеш160
                    let h160c = hash160(&pk_c[0..]).0;
                    let bip49_hash160 = bip_49_hash160c(h160c);

                    //проверка наличия в базе BTC bip49 3.....
                    if database_cl.contains(&bip49_hash160) {
                        if password_string!="инициализация" {
                            let address_btc = get_bip49_address(&bip49_hash160, BIP49_BTC);
                            let address = format!("BTC: {}", address_btc);
                            let private_key_c = hex_to_wif_compressed(&h.to_vec());
                            print_and_save(hex::encode(&h), &private_key_c, address, &mnemonic_x);
                        }
                    }
                    //*******************************************************************************

                    // println!("btc 49 {:?}",start.elapsed());
                    // start = Instant::now();

                    //BTC bip 84
                    //**********************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/84'/0'/0'/0/0");

                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_c = {
                        let p = ice_library.privatekey_to_publickey(&h);
                       ice_library.publickey_uncompres_to_compres(&p)
                    };

                    #[cfg(not(windows))]
                    let (pk_u, pk_c) = {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        (public_key.serialize_uncompressed(), public_key.serialize())
                    };
                    //----------------------------------------------------------------------------
                    //получем из них хеш160
                    let h160c = hash160(&pk_c[0..]).0;

                    //проверка наличия в базе BTC compress
                    if database_cl.contains(&h160c) {
                        if password_string!="инициализация" {
                            let address_btc_bip84 = segwit::encode(hrp::BC, segwit::VERSION_0, &h160c).unwrap();
                            let address = format!("BTC: {}", address_btc_bip84);
                            let private_key_c = hex_to_wif_compressed(&h.to_vec());
                            print_and_save(hex::encode(&h), &private_key_c, address, &mnemonic_x);
                        }
                    }

                    // println!("btc 84 {:?}",start.elapsed());
                    // start = Instant::now();

                    //DOGY bip 44
                    //**********************************************************************************
                    let h = get_private_key_from_seed(&xprv,"m/44'/3'/0'/0/0");

                    // Получаем публичный ключ для разных систем , адрюха не дружит с ice_library
                    //------------------------------------------------------------------------
                    #[cfg(windows)]
                    let pk_c = {
                        let p = ice_library.privatekey_to_publickey(&h);
                        ice_library.publickey_uncompres_to_compres(&p)
                    };

                    #[cfg(not(windows))]
                    let pk_c = {
                        // Создаем секретный ключ из байт
                        let secret_key = SecretKey::from_slice(&h).expect("32 bytes, within curve order");
                        let public_key = PublicKey::from_secret_key(&secp, &secret_key);
                        public_key.serialize()
                    };
                    //----------------------------------------------------------------------------
                    //получем из них хеш160
                    let h160c = hash160(&pk_c[0..]).0;

                    //проверка наличия в базе BTC compress
                    if database_cl.contains(&h160c) {
                        if password_string!="инициализация" {
                            let address_btc = get_legacy(h160c, LEGACY_BTC);
                            let address = format!("DOGY: {}", address_btc);
                            let private_key_c = hex_to_wif_compressed(&h.to_vec());
                            print_and_save(hex::encode(&h), &private_key_c, address, &mnemonic_x);
                        }
                    }

                    // println!("dogy {:?}",start.elapsed());
                    // start = Instant::now();

                }
                //шлём в главный поток для получения следующей задачи
                main_sender.send(ch).unwrap();
            }
        });
        //зажигание хз костыль получился(выполняеться один раз при запуске потока)
       sender.send("инициализация".to_string()).unwrap();
       //sender.send("modify expand fever race brave rent frost creek ridge mountain protect".to_string()).unwrap();
        //sender.send("1".to_string()).unwrap();
        channels.push(sender);
    }
    //---------------------------------------------------------------------------------------------


    //подготовка к запуску главного цикла
    //-----------------------------------------------------------------------------------------
    //для измерения скорости
    let mut start = Instant::now();
    let mut speed: u32 = 0;
    let one_sek = Duration::from_secs(1);

    let charset_len = lines.len();

    //состовляем начальную позицию
    let mut current_combination = vec![0; dlinn_a_pasvord];

    // Разбиение строки на слова
    let start_perebor_list: Vec<&str> = start_perebor.split_whitespace().collect();
    //заполняем страртовыми значениями для фраз
    for d in comb_perebor_left..dlinn_a_pasvord {
        let position = match start_perebor_list.get(d) {
            Some(&ch) => {
                // Находим позицию слова в charset_chars
                lines.iter().position(|c| c == ch).unwrap_or_else(|| {
                    eprintln!("{}", format!("Слово:{} из *начала перебора* не найдено, установлено первое из алфавита", ch));
                    0
                })
            }
            None => rng.gen_range(0..charset_len),
        };
        current_combination[d] = position;
    }


    //-----------------------------------------------------------------------------------

    //--ГЛАВНЫЙ ЦИКЛ
    // слушаем ответы потоков и если есть шлём новую задачу
    let mut password_string = "stroka".to_string();
    //----------------------------------------------------------------------------------------------
    for received in main_receiver {
        let ch = received;

        // последовательный перебор
        if mode == 0 {
            let mut i = dlinn_a_pasvord;
            while i > 0 {
                i -= 1;
                if current_combination[i] + 1 < charset_len {
                    current_combination[i] += 1;
                    break;
                } else {
                    current_combination[i] = 0;
                }
            }

            if i == 0 && current_combination[0] == charset_len - 1 {
                //если включенно увеличение длинны увеличим иначе выйдем из цикла
                if len_uvelichenie {
                    println!("{}{}", blue(format!("ДЛИНА ПАРОЛЯ:{}", green(dlinn_a_pasvord))), magenta(format!(" ПЕРЕБРАТА за:{:?}", start.elapsed())));
                    dlinn_a_pasvord = dlinn_a_pasvord + 1;
                    current_combination = vec![0; dlinn_a_pasvord];
                    println!("{}{:?}", blue("ТЕКУЩАЯ ДЛИНА ПАРОЛЯ:"), green(dlinn_a_pasvord));
                } else {
                    println!("{}", blue(format!("ГОТОВО,перебраты все возможные из {} длинной {}", alvabet, dlinn_a_pasvord)));
                    jdem_user_to_close_programm();
                    break;
                }
            }

            let mut s = String::new();
            for i in current_combination.iter() {
                s.push_str(lines.get(*i).unwrap());
                s.push(' ');
            }

            password_string = s.trim().to_string();
        }

        //случайный набор строк по длинне
        if mode == 1 {
            let mut k = String::new(); // Создаем пустую строку
            for _ in 0..dlinn_a_pasvord {
                let rand = lines.get(rng.gen_range(0..lines.len())).unwrap();
                k.push_str(rand);
                k.push(' '); // Добавляем разделитель между словами
            }
            k.pop(); // Удаляем последний пробел
            password_string = k;
        }

        //комбенированый режим
        if mode == 2 {
            //будем переберать слева указаное количество
            let mut i = comb_perebor_left;
            while i > 0 {
                i -= 1;
                if current_combination[i] + 1 < charset_len {
                    current_combination[i] += 1;
                    break;
                } else {
                    current_combination[i] = 0;
                }
            }

            if i == 0 && current_combination[0] == charset_len - 1 {
                for f in 0..dlinn_a_pasvord {
                    //заполняем слева начальными значениями
                    if f < comb_perebor_left {
                        current_combination[f] = 0;
                    } else {
                        //остальные рандомно
                        current_combination[f] = rng.gen_range(0..charset_len);
                    }
                }
            }
            let mut s = String::new();
            for i in current_combination.iter() {
                s.push_str(lines.get(*i).unwrap());
                s.push(' ');
            }

            password_string = s.trim().to_string();
        }

        speed = speed + 128;
        if show_info {
            //измеряем скорость и шлём прогресс
            if start.elapsed() >= one_sek {
                let mut stdout = stdout();
                print!("{}\r{}", BACKSPACE, green(format!("SPEED:{speed}/s|{}", format!("{}", password_string))));
                stdout.flush().unwrap();
                start = Instant::now();
                speed = 0;
            }
        } else {
            // или через некоторое время будем сохранять в файл текущий подбор
            if speed > time_save_tekushego_bodbora {
                println!("{}{}", blue("ТЕКУЩИЙ ПОДБОР:"), green(password_string.clone()));

                let alf = format!("List.txt Длинна{}", dlinn_a_pasvord);

                add_v_file("ТЕКУЩИЙ ПОДБОР.txt", format!("{} {}\n", password_string.clone(), alf));
                speed = 0;
            }
        }
        // Отправляем новую в свободный канал
        channels[ch].send(password_string.clone()).unwrap();
    }
}
//------------------------------------------------------------------------------------

fn get_mode_text(mode: usize) -> String {
    match mode {
        0 => "ПОСЛЕДОВАТЕЛЬНЫЙ ПЕРЕБОР".to_string(),
        1 => "РАНДОМ".to_string(),
        2 => "КОМБИНИРОВАННЫЙ".to_string(),
        _ => { red("ХЗ").to_string() }
    }
}

fn lines_from_file(filename: impl AsRef<Path>) -> io::Result<Vec<String>> {
    BufReader::new(File::open(filename)?).lines().collect()
}

fn add_v_file(name: &str, data: String) {
    OpenOptions::new()
        .read(true)
        .append(true)
        .create(true)
        .open(name)
        .expect("cannot open file")
        .write(data.as_bytes())
        .expect("write failed");
}

fn hex_to_wif_compressed(raw_hex: &Vec<u8>) -> String {
    if raw_hex.len() == 32 {
        let mut v = [0; 38];
        v[0] = 0x80;
        v[1..33].copy_from_slice(&raw_hex[..]);
        v[33] = 0x01;
        let checksum = sha256d(&v[0..34]);
        v[34..38].copy_from_slice(&checksum[0..4]);
        v.to_base58()
    } else {
        format!("Ошибка hex меньше 64 :'{}'", hex::encode(raw_hex).to_string())
    }
}

fn hex_to_wif_uncompressed(raw_hex: &Vec<u8>) -> String {
    if raw_hex.len() == 32 {
        let mut v = [0; 37];
        v[0] = 0x80;
        v[1..33].copy_from_slice(&raw_hex[..]);
        let checksum = sha256d(&v[0..33]);
        v[33..37].copy_from_slice(&checksum[0..4]);
        v.to_base58()
    } else { format!("Ошибка hex меньше 64 :'{}'", hex::encode(raw_hex).to_string()) }
}


fn print_and_save(hex: String, key: &String, addres: String, password_string: &String) {
    println!("{}", cyan("\n!!!!!!!!!!!!!!!!!!!!!!FOUND!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"));
    println!("{}{}", cyan("СИД:"), cyan(password_string));
    println!("{}{}", cyan("HEX:"), cyan(hex.clone()));
    println!("{}{}", cyan("PRIVATE KEY:"), cyan(key));
    println!("{}{}", cyan("АДРЕСС:"), cyan(addres.clone()));
    let s = format!("СИД:{}\nHEX:{}\nPRIVATE KEY: {}\nАДРЕСС {}\n\n", password_string, hex, key, addres);
    add_v_file("FOUND.txt", s);
    println!("{}", cyan("СОХРАНЕНО В FOUND.txt"));
    println!("{}", cyan("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"));
}

fn print_and_save_eth(hex: String, addres: String, password_string: &String) {
    println!("{}", cyan("\n!!!!!!!!!!!!!!!!!!!!!!FOUND!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"));
    println!("{}{}", cyan("СИД:"), cyan(password_string));
    println!("{}{}", cyan("HEX:"), cyan(hex.clone()));
    println!("{}{}", cyan("АДРЕСС:"), cyan(addres.clone()));
    let s = format!("СИД:{}\nHEX:{}\nАДРЕСС {}\n\n", password_string, hex, addres);
    add_v_file("FOUND.txt", s);
    println!("{}", cyan("СОХРАНЕНО В FOUND.txt"));
    println!("{}", cyan("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"));
}

fn sha256d(data: &[u8]) -> [u8; 32] {
    let digest1 = Sha256::digest(data);
    let digest2 = Sha256::digest(&digest1);
    let mut result = [0u8; 32];
    result.copy_from_slice(&digest2);
    result
}

pub fn get_legacy(hash160: [u8; 20], coin: u8) -> String {
    let mut v = Vec::with_capacity(23);
    v.push(coin);
    v.extend_from_slice(&hash160);
    let checksum = sha256d(&v);
    v.extend_from_slice(&checksum[0..4]);
    let b: &[u8] = v.as_ref();
    b.to_base58()
}

//ETH
pub fn get_eth_kessak_from_public_key(public_key_u: [u8; 65]) -> [u8; 20] {
    let mut output = [0u8; 32];
    let mut hasher = Keccak::v256();
    hasher.update(public_key_u.split_first().unwrap().1);
    hasher.finalize(&mut output);

    let mut result = [0u8; 20];
    result.copy_from_slice(&output[12..32]);
    result
}

fn eth_address_to_bytes(address: &str) -> Result<[u8; 20], String> {
    let hex_str = if address.starts_with("0x") {
        &address[2..]
    } else {
        address
    };

    match hex::decode(hex_str) {
        Ok(decoded) => {
            if decoded.len() == 20 {
                let mut bytes = [0u8; 20];
                bytes.copy_from_slice(&decoded);
                Ok(bytes)
            } else {
                Err(format!("Invalid length for address: {}", address))
            }
        }
        Err(_) => Err(format!("Decoding failed for address: {}", address)),
    }
}

//bip49------------------------------------------------------
pub fn bip_49_hash160c(hash160c: [u8; 20]) -> [u8; 20] {
    let mut v = [0u8; 22]; // 22 байта, так как 1 байт для 0x00, 1 байт для 0x14 и 20 байт для hash160c
    v[0] = 0x00;
    v[1] = 0x14;
    v[2..].copy_from_slice(&hash160c);

    let digest2 = Sha256::digest(&v);
    let hash160_3 = Ripemd160::digest(&digest2);

    let mut result = [0u8; 20];
    result.copy_from_slice(&hash160_3);
    result
}

pub fn get_bip49_address(hash160_3: &[u8; 20], coin: u8) -> String {
    let mut v = [0u8; 25];
    v[0] = coin;
    v[1..21].copy_from_slice(hash160_3);

    let checksum = sha256d(&v[..21]);
    v[21..25].copy_from_slice(&checksum[0..4]);

    v.to_base58().to_string()
}
//------------------------------------------------------------------------

// TRX
pub fn get_trx_from_eth(eth: String) -> String {
    let mut v = Vec::with_capacity(50);
    v.push(0x41);
    v.extend_from_slice(hex::decode(eth).unwrap().as_slice());
    let checksum = sha256d(&v);
    v.extend_from_slice(&checksum[0..4]);
    let b: &[u8] = v.as_ref();
    b.to_base58()
}

fn first_word(s: &String) -> &str {
    s.trim().split_whitespace().next().unwrap_or("")
}

//если txt есть считем его строки, иначе создадим и посчитаем
pub fn get_len_find_create(coin: &str) -> usize {
    match fs::metadata(Path::new(coin)) {
        Ok(_) => {
            let lines = get_lines(coin);
            println!("{}{}", blue("НАЙДЕН ФАЙЛ:"), green(format!("{coin}:{lines} строк")));
            lines
        }
        Err(_) => {
            print!("{}{}", blue("ФАЙЛ НЕ НАЙДЕН,ИСПОЛЬЗУЕМ ВСТРОЕНЫЙ:"), green(format!("{coin}:")));
            let dockerfile = match coin {
                "btc.txt" => { include_str!("btc.txt") }
                "dogecoin.txt" => { include_str!("dogecoin.txt") }
                "eth.txt" => { include_str!("eth.txt") }
                "trx.txt" => { include_str!("trx.txt") }
                "bip39.txt" => { include_str!("bip39.txt") }
                _ => { include_str!("btc.txt") }
            };
            add_v_file(coin, dockerfile.to_string());
            let lines = get_lines(coin);
            println!("{}", green(format!("{} строк", lines)));
            lines
        }
    }
}

pub(crate) fn get_bufer_file(file: &str) -> BufReader<File> {
    let file = File::open(file).expect("Не удалось открыть файл");
    BufReader::new(file)
}

// Функция для чтения строк из файла
pub(crate) fn read_lines(file: &str) -> Lines<BufReader<File>> {
    let file = File::open(file).expect("Не удалось открыть файл");
    BufReader::new(file).lines()
}

pub(crate) fn get_lines(file: &str) -> usize {
    let file = File::open(file).expect("Unable to open the file");
    let reader = BufReader::new(file);
    let mut line_count = 0;
    for _line in reader.lines() {
        line_count += 1;
    }
    line_count
}

fn jdem_user_to_close_programm() {
    // Ожидание ввода пользователя для завершения программы
    println!("{}", blue("Нажмите Enter, чтобы завершить программу..."));
    let mut input = String::new();
    io::stdin().read_line(&mut input).expect("Ошибка чтения строки");
}


//берем случайные символы из строки
fn get_rand_alfabet(alvabet: String, size_rand_alfabet: usize) -> String {
    let mut rng = thread_rng();
    let mut charset_chars: Vec<char> = alvabet.chars().collect();

    // Перемешиваем символы
    charset_chars.shuffle(&mut rng);

    // Берем первые size_rand_alfabet символов
    let selected_chars: Vec<char> = charset_chars.into_iter().take(size_rand_alfabet).collect();

    // Создаем строку из выбранных символов
    selected_chars.into_iter().collect()
}

//составляем случайный список из полного
fn get_rand_list(mut list: Vec<String>, size_rand_alfabet: usize) -> Vec<String> {
    let mut rng = thread_rng();
    // Перемешиваем символы
    list.shuffle(&mut rng);

    // Берем первые size_rand_alfabet символов
    let selected_chars: Vec<String> = list.into_iter().take(size_rand_alfabet).collect();

    // Создаем строку из выбранных символов
    selected_chars.into_iter().collect()
}

fn bip84_to_h160(address: String) -> [u8; 20] {
    let (_hrp, _version, program) = segwit::decode(&address).expect("valid address");

    if program.len() == 20 {
        // Convert Vec<u8> to [u8; 20]
        let mut h160 = [0u8; 20];
        h160.copy_from_slice(&program);
        h160
    } else {
        [0u8; 20]
    }
}


//сохранение и загрузка базы из файла
fn save_to_file(set: &HashSet<[u8; 20]>, file_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    match File::create(file_path) {
        Ok(file) => {
            let writer = BufWriter::new(file);
            match serialize_into(writer, set) {
                Ok(_) => Ok(()),
                Err(e) => Err(Box::new(e)),
            }
        }
        Err(e) => Err(Box::new(e)),
    }
}

fn load_from_file(file_path: &str) -> Result<HashSet<[u8; 20]>, Box<dyn std::error::Error>> {
    match File::open(file_path) {
        Ok(file) => {
            let reader = BufReader::new(file);
            match deserialize_from(reader) {
                Ok(set) => Ok(set),
                Err(e) => Err(Box::new(e)),
            }
        }
        Err(e) => Err(Box::new(e)),
    }
}

fn get_private_key_from_seed(xprv: &ExtendedPrivateKey<SigningKey>, der:&str) -> [u8; 32] {
    let derivation_path = DerivationPath::from_str(der).expect("Failed to create DerivationPath from string");

    let mut child_xprv = xprv.clone();
    for index in derivation_path.into_iter() {
        child_xprv = child_xprv.derive_child(index).expect("Failed to derive child key");
    }

    child_xprv.private_key().to_bytes().into()
}