# coq-elpi codespace
Quick way to try λProlog (lambda-Prolog) via github codespace vscode web editor, without local installations.

## Using Codespaces with this Repository

To use Codespaces with this repository, follow these steps:

1. Open the repository in GitHub.
2. Click on the "Code" button and select "Open with Codespaces".
3. If you don't have a Codespace already, create a new one.
4. The Codespace will automatically use the configuration in the `.devcontainer` directory to set up the development environment.
5. Once the Codespace is ready, you will have coq-epli installed and *almost* ready to use in the vscode web environment.
   - Just refresh the browser tab if syntax highlighting for Coq-Elip script (`*.v` extension files) does not work in vscode web right after the codespace setup.
   - Downgrade VsCoq extension to mach the installed vscoq-language-server. Disable auto update for VsCoq and install specific version 2.2.1 of VsCoq. (See the [vscode doc](https://code.visualstudio.com/docs/editor/extension-marketplace#_install-an-extension) on how to install specific version of an extension.)


After launching the codespace, you are ready to run examples in the [Tutorial on the Elpi programming language](https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html).

See [coq-elpi](https://github.com/LPCIC/coq-elpi) repository for further details.
