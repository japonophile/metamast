extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;
extern crate regex;

pub mod mm_parser;

extern crate mockall;

pub mod io {
    use std::fs;

    pub struct FileIO {
    }

    use mockall::automock;
    #[automock]
    pub trait IO {
        fn slurp(&self, filename: &str) -> String;
    }

    impl IO for FileIO {
        fn slurp(&self, filename: &str) -> String {
            return fs::read_to_string(filename)
                .expect("Could not read file");
        }
    }
}

