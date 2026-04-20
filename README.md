# Formalization Seminar SoSe 2026 Uni Greifswald

This the course webpage for a seminar on formalization in Lean at the Universität Greifswald in summer semester 2026. The goal is to learn something about formalization of mathematics and how to use the proof assistant Lean.

## Some Theoretical Background

Here are some sources about the underlying theoretical aspects:

 - [Spartan Type Theory](https://math.andrej.com/wp-content/uploads/2017/12/Spartan-Type-Theory.pdf) by [Andrej Bauer](https://www.andrej.com/)
 - [An Introduction to Univalent Foundations for Mathematicians](https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/S0273-0979-2018-01616-9.pdf) (the first 5 sections) by Dan Grayson
 - [Naive Type Theory](https://people.cs.nott.ac.uk/psztxa/publ/fomus19.pdf) by [Thorsten Altenkirch](https://people.cs.nott.ac.uk/psztxa/)
 - [Type Theory](https://plato.stanford.edu/entries/type-theory/) in Stanford Encyclopedia of Philosophy
 - [Introduction to Type Theory](https://www.cs.ru.nl/~herman/PUBS/IntroTT-improved.pdf) by [Herman Geuvers](https://www.cs.ru.nl/~herman/)

 Here are some sources about various proof assistants: 
 - [Proof Assistants: history, ideas and future](https://www.cs.ru.nl/~herman/PUBS/proofassistants.pdf) by [Herman Geuvers](https://www.cs.ru.nl/~herman/)
 - [The Seventeen Provers of the World](https://www.cs.ru.nl/~freek/comparison/comparison.pdf) by [Freek Wiedijk](https://www.cs.ru.nl/staff/Freek.Wiedijk/)

## Some First Steps before the First Steps

Before starting with installations on your computer, you could try some of these games online (however, not required):

- [The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
- [The Set Theory Game](https://adam.math.hhu.de/#/g/djvelleman/stg4)

## Setting Lean Up on your Computer

Participation in the seminar requires several local installations on your own computer.

Please following steps (before starting the steps read the whole instructions once):

- Follow the steps outlined in the following [instructions](https://leanprover-community.github.io/get_started.html) 
- **Note:** Part of the installation involves installing [Visual Studio Code](https://code.visualstudio.com/) (where we write Lean code) and [git](https://git-scm.com/) (for version control)
- **Warning:** if you are using Windows you might have to deactivate your anti-virus during the installation process!
- **Small Change:** In the step **Set up Lean 4 project** click on **Download an existing project** (third bullet point). Choose `Git repository URL`, enter `https://github.com/nimarasekh/Formalization-SoSe26` and then select a folder where you want to download this repository, and specify a folder name. Then press `Create project folder` and wait a few minutes.

* When you have downloaded the repository a message appears allowing you to open the project folder.
To test that everything is working, open the repository and open the file `Formalization-SoSe26/Cover.lean`.
The file should be ready a few seconds later. Try out the `CLICK HERE` in the file and see if you get the correct responses.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.

## Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on a laptop that is more than 10 years old or on a chromebook, since Lean does use a moderate amount of recourses.
You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions at the bottom of this file.

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

## Update repository

I will update the lectures and exercises as we go along. In order to get the most recent updates you have to **pull** the changes. There are several options:

- Open the terminal in VS Code (``ctrl+` ``/``cmd+` ``) and then write `git pull` and press `enter`.
- Open the `Source Control` tab in VS Code (third icon in the top-left, or `ctrl+shift+G`/`cmd+shift+G`) and then under `⋯` (More actions) you can click `Pull` to get the latest changes.
- **Note:** If you use `Source Control` you should *not* press `Sync`, since that will try to upload your changes to the assignment files to GitHub (you don't have the rights to do this).
- Occasionally there is an update to the Lean version for the repository, in which case you will be informed. In that case after
<!-- You can commit by writing a non-empty commit message and then pressing `Commit` (you can answer "Yes" or "Always" when it asks you if you want to stage all changes.).  -->
<!-- Troubleshooting: if you have configured git pull to use rebase, then you
have to commit the changes first.  -->


We might at some point update the version of Lean for the repository (we will tell you when this happens). In that case it is necessary to get the new Mathlib cache via the following steps.

- *Do not* restart a Lean file (which will prompt Lean to rebuild Mathlib on your laptop).
- If pulling happened via terminal, then still in the terminal run `lake exe cache get!` (or `~/.elan/bin/lake exe cache get!` if `lake` cannot be found).
- In the VS Code window `∀ > Project Actions... > Fetch Mathlib Build Cache` and wait for the cache to download.
- After it has finished, you might have to restart the Lean file, and then Lean should be compiling your file in less than a minute.

If this fails, try the following steps:
- Close VSCode (if it is open)
- Open terminal on your computer **in** the `LeanCourse24` folder.
- Run `lake exe cache get!` (or `~/.elan/bin/lake exe cache get!` if `lake` cannot be found).
- Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
- Now you can reopen VSCode and restart the file (if prompted).

<!--
## Setting Up this Project on your Computer

As part of this course you need to set up this project on your own computer:

- Clone the repository to your local computer so that you can start working with it. 
-->

## Setting Things Up Online

If there are any challenges with the local installation, here are some (temporary) online solutions:

- There is an online option for experimentation with Lean: [Lean Online](https://live.lean-lang.org/)
- A more advanced option is to work with the project via GitHub Codespaces:

<a href='https://codespaces.new/nimarasekh/Formalization-SoSe26' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

- Another option to work with the project is via Ona:
  
[![Open in Ona](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/nimarasekh/Formalization-SoSe26)

## Learning Material

- The learning material consists of lectures and exercises that can be found in this repository.
- No other material is mandatory, but recommended material can be found further below.

## Additional Learning Material

Here are some interesting books and learning material, that will serve the basis for the lectures here:
- [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) by [Patrick Massot](https://github.com/PatrickMassot)
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) by [Heather Macbeth](https://hrmacbeth.github.io/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) by [Jeremy Avigad](https://github.com/avigad) and [Patrick Massot](https://github.com/PatrickMassot) 
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) by [Jeremy Avigad](https://github.com/avigad), [Leonardo de Moura](https://leodemoura.github.io/), [Soonho Kong](https://github.com/soonhokong) and [Sebastian Ullrich](https://github.com/kha)

## Formalization and AI

Here are some interesting efforts to integrate advanced AI into Lean.
- [Aristotle](https://aristotle.harmonic.fun/) by [Harmonic](https://harmonic.fun/)
- [Gauss](https://www.math.inc/gauss) by [Math.inc](https://www.math.inc/)


## Some Other Recommendations

- It is recommended to make a [GitHub](https://github.com/) account now. It will become mandatory later on for the projects.
<!--
- There is a [Zulip channel](https://leanprover.zulipchat.com/) that has a lot of useful information.
-->

## Acknowledgement

The course material and exercises are heavily influenced by [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).