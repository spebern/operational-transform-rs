#![allow(dead_code)]

use clap::{AppSettings, Arg, Command};
use xtaskops::ops;
use xtaskops::tasks;

fn main() -> Result<(), anyhow::Error> {
    let cli = Command::new("xtask")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommand(
            Command::new("coverage").arg(
                Arg::new("dev")
                    .short('d')
                    .long("dev")
                    .help("generate an html report")
                    .takes_value(false),
            ),
        )
        .subcommand(Command::new("vars"))
        .subcommand(Command::new("ci"))
        .subcommand(Command::new("powerset"))
        .subcommand(Command::new("bloat-deps"))
        .subcommand(Command::new("bloat-time"))
        .subcommand(Command::new("docs"));
    let matches = cli.get_matches();

    let root = ops::root_dir();
    let res = match matches.subcommand() {
        Some(("coverage", sm)) => tasks::coverage(sm.is_present("dev")),
        Some(("vars", _)) => {
            println!("root: {:?}", root);
            Ok(())
        }
        Some(("ci", _)) => tasks::ci(),
        Some(("docs", _)) => tasks::docs(),
        Some(("powerset", _)) => tasks::powerset(),
        Some(("bloat-deps", _)) => tasks::bloat_deps(),
        Some(("bloat-time", _)) => tasks::bloat_time(),
        _ => unreachable!("unreachable branch"),
    };
    res
}
