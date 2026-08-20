# A Fano plane in the special fibre of an explicit \(M_{23}\)-cover

Companion certificates for the papers
[A Fano plane in the special fibre of an explicit \(M_{23}\)-cover](paper/LeLay_M23_Special_Fibre_Fano_Plane_Draft_2026-08-20.pdf)
and
[Affine frames and outer-twisted descent in an explicit \(M_{23}\)-cover](paper/LeLay_M23_Affine_Frames_Outer_Twisted_Descent_Draft_2026-08-20.pdf)
by François Le Lay (Reflexivity).
This repository is
<https://github.com/research-reflexivity/frontier-math-m23-fixed-point>.
The companion optimal-model note is
<https://github.com/research-reflexivity/frontier-math-m23-optimal-model>.

Huang--Jackson--Lee--Poonen--Pries--Zhang realized \(M_{23}\) over
\(\mathbf Q\) from a seven-element Nielsen class with a Galois fixed
point they described as occurring “miraculously.”  These papers do not
independently reprove that fixed point.  The Fano paper gives the
arithmetic analysis of the fibre over the rational branch point \(T=0\):
the factorization \(23^4H_7R_8^2\), the Fano-plane incidence on the seven
simple roots, the arithmetically equivalent point and line fields, the
degree-\(1344\) and degree-\(2688\) Galois extensions and their ramification
at \(2,3,23\), and the action of complex conjugation on the Nielsen classes.
It also records the canonical 168-element torsor of translation-reduced
affine frames on the roots of the ramification octic.

The companion paper identifies that torsor with the 168 point--line
correlations of the Fano plane and proves, for the explicit rational cover,
the transport identity

\[
\rho_{R_8}(\sigma)=\operatorname{pair}(w_{\sigma^{-1}}).
\]

The identity is at the level of permutations of the eight ramification
points, before quotienting to affine frames.  Its consequence is
outer-twisted descent of the oriented-cut correlation.  It does not produce
a bare Galois-fixed point--line bijection, a preferred rational affine frame,
or an action of arbitrary abstract elements of \(\widehat{GT}\).

The ordinary-node assertion for the 84 singular fibres is an imported
input, cited in the paper to a companion optimal-model computation.

## Reproduce

You need [GAP](https://www.gap-system.org/) (developed against 4.16)
and [PARI/GP](https://pari.math.u-bordeaux.fr/) on `PATH` as `gap` and
`gp`.  Override either executable if needed:

```sh
make verify GAP=/path/to/gap GP=/path/to/gp
```

Individual targets are the names in the papers’ certificate tables.
For the outer-twisted companion, run:

```sh
make twin-fano-incidence
make oriented-cut-hurwitz-torsor
make affine-frame-correlation-torsor
make gt-boundary-transport
```

The last target reruns the exact finite inputs and audits the standard
tame-specialization proof with its logical exclusions.

The additional `special-fibre-frobenius-scan` target checks
the ten factorization-type pairs at the 348,508 Frobenius elements reported
after that table.  Other large checks include the degree-1344 splitting
field of `R8`, 9,889 transvection primes, and the central square class at
fourteen completely split primes.  The splitting-field and full
central-layer discriminant computations need a large PARI stack (the
scripts request up to 12 GB).

## Layout

- `paper/` — the two publication PDFs
- `scripts/` — GAP (`.g`) and PARI/GP (`.gp`) certificates
- `data/Fint_coefficients_Z.gp` — exact integral model of the published cover
- `results/` — summaries written by the certificates

## Licensing

Copyright 2026 Reflexivity, Inc.

- Software and scripts: [Apache License 2.0](LICENSE)
- This README, third-party notices, and the paper PDFs: [CC BY-NC-SA 4.0](LICENSE-CC-BY-NC-SA-4.0)
- Original generated data and certificate outputs in `data/` and
  `results/`: [CC0 1.0](LICENSE-CC0-1.0), to the extent Reflexivity
  holds the relevant rights

These licenses do not relicense third-party materials.  See
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Primary source

X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, and S. Zhang,
*The Mathieu group \(M_{23}\) is a Galois group over \(\mathbf Q\)*,
[arXiv:2608.08538](https://arxiv.org/abs/2608.08538) (2026).
