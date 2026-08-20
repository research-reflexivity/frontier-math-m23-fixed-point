# Third-party notices

The repository's Apache-2.0, CC BY-NC-SA 4.0, and CC0 declarations apply only
to rights held by Reflexivity, Inc. They do not relicense third-party
materials.

## GAP and GAP packages

The computational certificates invoke GAP and packages including
PrimGrp, TransGrp, and SmallGrp as external runtime dependencies. The
local development environment uses GAP 4.16.0.

GAP and these packages are distributed under the GNU General Public
License, version 2 or, at the user's option, any later version
(`GPL-2.0-or-later`). They are not bundled in this repository.

- GAP: https://www.gap-system.org/
- License: https://www.gnu.org/licenses/old-licenses/gpl-2.0.html

## PARI/GP

The arithmetic certificates invoke PARI/GP as an external runtime
dependency. PARI/GP is copyright the PARI Group and is distributed under
`GPL-2.0-or-later`. It is not bundled in this repository.

- PARI/GP: https://pari.math.u-bordeaux.fr/
- License: https://www.gnu.org/licenses/old-licenses/gpl-2.0.html

## Primary mathematical source

The \(M_{23}\) realization, published degree-23 equation, branch-cycle
description, and Galois fixed-point theorem are due to:

X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, and S. Zhang,
*The Mathieu group \(M_{23}\) is a Galois group over
\(\mathbf Q\)*, arXiv:2608.08538 (2026).

The authors' data repository is:

https://github.com/shaowuz/m23isgalois

At the time this notice was prepared, that external repository did not
provide an explicit software license. No license grant for its source
code is implied here. Before copying or redistributing any upstream
implementation, obtain permission or an explicit license from its
copyright holders.

The exact integral coefficient table in `data/Fint_coefficients_Z.gp`
was generated within the Reflexivity companion optimal-model work from
the published mathematical model. The CC0 dedication covers only rights
held by Reflexivity and does not assert ownership of the underlying
published equation or uncopyrightable mathematical facts.
