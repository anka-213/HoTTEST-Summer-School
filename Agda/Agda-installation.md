# Instructions on how to get Agda 2.6.2.2

## Online

Thanks to Amélia Liao, there's an online version available at https://hcomp.io/,
which means you won't have to install anything.  But if you would like to
install Agda locally, please see below.

## Mac

If you're a Mac user who already uses homebrew, the process is painless: just
run `brew install` agda and get ready to wait a while.

If you're a Mac user who doesn't already use homebrew, follow the instructions
here to get it working: https://brew.sh/

## Linux

If you're an Arch or Fedora user, then `pacman -S agda` or `yum install agda`
should work. See also https://pastebin.com/jj2c2dqR for Arch instructions.

If you're Debian/Ubuntu, then you should install Agda through `cabal`, because
the Agda in the repositories of the operating system is outdated. See
https://agda.readthedocs.io/en/v2.6.2.2/getting-started/installation.html for
instructions.

## Windows

For Windows, see https://pastebin.com/Zguv4743. (Thanks Todd Waugh Ambridge!)

## Editing Agda code

Most people use emacs with agda-mode to edit, but you can also use neovim with
cornelis or vscode with the agda-mode port.

To get emacs with agda-mode set up, there's a tutorial here:
https://agda.readthedocs.io/en/v2.6.2.2/getting-started/installation.html#running-the-agda-mode-program

To get neovim with corenlis setup, there's installation instructions on their
github: https://github.com/isovector/cornelis

To get the vscode plugin setup, see here:
https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

## Checking that everything works

After installing Agda, you should check that it's installed correctly by
type-checking the Hello, Agda! program. See here:
https://agda.readthedocs.io/en/v2.6.2.2/getting-started/hello-world.html#hello-agda

## Getting help

If you're having trouble installing Agda, please ask for help in the
`#agda-installation` channel on the summer school's Discord server.