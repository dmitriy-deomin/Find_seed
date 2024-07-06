use std::fmt::Display;
use console::{style, StyledObject};

pub fn green(text:impl Display) -> StyledObject<String> {
    style(text.to_string()).green()
}
pub fn blue(text:impl Display) -> StyledObject<String> {
    style(text.to_string()).cyan()
}
pub fn magenta(text:impl Display) -> StyledObject<String> {
    style(text.to_string()).magenta()
}
pub fn red(text:impl Display) -> StyledObject<String> {
    style(text.to_string()).red()
}
pub fn cyan(text:impl Display) -> StyledObject<String> {
    style(text.to_string()).cyan()
}

// pub fn color_bool(b: bool) ->String{
//     let colored= if b{
//         format!("{}",style("true").green())
//     }else {
//         format!("{}",style("false").red())
//     };
//     colored
// }