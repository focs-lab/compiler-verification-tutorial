# Provenance of this directory

This directory is an archival copy of the material published at

    https://xavierleroy.org/courses/EUTypes-2019/

for Xavier Leroy's course *Proving the correctness of a compiler*, given at
the EUTypes 2019 summer school on Types for Programming and Verification
(Ohrid, Macedonia, 30 August – 4 September 2019).

It is kept here for reference, so that the Lean 4 port in the parent
directory can be read alongside the development it was translated from.
Nothing in the Lean development depends on these files.

## Contents

| Path | What it is |
| --- | --- |
| `sources/` | the Coq sources, unpacked from `compilerverif.zip` |
| `compilerverif.zip` | the Coq sources as distributed |
| `html/` | the Coq sources pretty-printed by `coq2html` |
| `index.html`, `style.css` | the course page as published |
| `slides.pdf` | the lecture slides |
| `compcert-CACM.pdf` | X. Leroy, *Formal verification of a realistic compiler*, CACM 52(7), 2009 |
| `compcert-backend.pdf` | X. Leroy, *A formally verified compiler back-end* |

## Licensing

The **Coq sources** (`sources/`, `compilerverif.zip`, and the `html/`
rendering of them) are copyright 2019, 2025 Xavier Leroy and are distributed
under the GNU Lesser General Public License, version 2.1 or (at your option)
any later version — see `sources/LICENSE.md`. That licence is what permits
the Lean translation in the parent directory, which is distributed under the
same terms.

The **slides, the course page, and the two papers** are *not* covered by that
licence. They are Xavier Leroy's own copyrighted works, mirrored here for
private study and teaching reference only. They should not be redistributed;
if this repository is ever made public, remove them and link to the original
page instead.
