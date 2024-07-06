use std::ffi::CString;
use libloading::{Library, Symbol};
use std::os::raw::c_char;
use std::path::Path;
use once_cell::sync::Lazy;

pub struct IceLibrary {
    init_secp256_lib: Symbol<'static, unsafe extern "C" fn()>,
    privatekey_to_publickey: Symbol<'static, unsafe extern "C" fn(*const c_char, *mut u8)>,
}

/// Statically known path to library.
#[cfg(target_os = "linux")]
pub fn lib_path() -> &'static Path {
    Path::new("ice_secp256k1.so")
}

/// Statically known path to library.
#[cfg(target_os = "windows")]
pub fn lib_path() -> &'static Path {
    Path::new("ice_secp256k1.dll")
}

impl IceLibrary {
    // Создание новой библиотеки и загрузка .dll файла
    pub fn new() -> Self {
        static LIB: Lazy<Library> = Lazy::new(|| {
            unsafe { Library::new(lib_path()) }
                .expect("Не удалось загрузить библиотеку ice_secp256k1")
        });

        unsafe {
            let init_secp256_lib: Symbol<unsafe extern "C" fn()> = LIB.get(b"init_secp256_lib")
                .expect("Не удалось загрузить функцию init_secp256_lib");
            let privatekey_to_publickey: Symbol<unsafe extern "C" fn(*const c_char, *mut u8)> =
                LIB.get(b"scalar_multiplication")
                    .expect("Не удалось загрузить функцию scalar_multiplication");

            IceLibrary {
                init_secp256_lib,
                privatekey_to_publickey,
            }
        }
    }

    // Инициализация библиотеки secp256
    pub(crate) fn init_secp256_lib(&self) {
        unsafe {
            (self.init_secp256_lib)();
        }
    }

    // Преобразование приватного ключа в публичный
    pub fn privatekey_to_publickey(&self, hex: &[u8]) -> [u8; 65] {
        // Преобразование массива байтов в строку hex
        let hex_string = hex::encode(hex);

        // Создание CString из строки hex
        let private_key = CString::new(hex_string)
            .expect("Не удалось создать CString из hex");

        let mut res = [0u8; 65];

        // Вызов функции из библиотеки
        unsafe {
            (self.privatekey_to_publickey)(private_key.as_ptr(), res.as_mut_ptr());
        }

        res
    }

    // Преобразование публичного ключа из несжатого в сжатый формат
    pub fn publickey_uncompres_to_compres(&self, pub_hex: &[u8; 65]) -> [u8; 33] {
        let mut result = [0u8; 33];
        result[0] = if pub_hex[64] % 2 == 0 { 2 } else { 3 }; // Определение первого байта
        result[1..].copy_from_slice(&pub_hex[1..33]); // Копирование оставшихся байт
        result
    }
}