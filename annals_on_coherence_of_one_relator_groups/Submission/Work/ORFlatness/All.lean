/-
# N9: flatness of `D_{K[G]} ⊗_K I_{K[G]}` implies weak dimension at most one

This directory contains node **N9** of the route design (`ROUTE_LEAD.md`): the formalisation of
Section 5.3 of Jaikin-Zapirain--Linton, *On the coherence of one-relator groups and their
group algebras*, Annals of Math 201 (2025), in the single two-cell case, together with the
noncommutative homological algebra it needs.

## Statement of the node

Let `K` be a commutative ring (`K` a field in the application), `G` a group, `S` a `K`-algebra
with an algebra homomorphism `φ : K[G] → S` (in the application `S = D_{K[G]}` is the Linnell
division `K[G]`-ring, but nothing below uses that), and let `C` be a `K[G]`-module standing for
the augmentation ideal `I_{K[G]}`.  From

* an exact sequence `0 → A →f B →g C → 0` (`Work.ORFlatness.tor1Vanishes_diagonal_jl*` take
  `f.range = g.ker` and `g` surjective; `C` is the augmentation ideal in the application),
* Claim 5.8 (`hB`), Lemma 5.1 together with Claim 5.9 and `char K ∤ l` (`hA`), and the duality
  of Lemma 5.2 (`hswap`),

one concludes that the `K[G]`-module `S ⊗[K] C` is flat — on **both** sides — and hence that
`Tor₂^{K[G]}(S, M) = 0` for every left `K[G]`-module `M` (once the duality chain of Lemma 5.2,
`hchain`, is supplied).

## Vocabulary

* `Work.ORFlatness.BalTensor R X N` (`Tensor.lean`): the balanced tensor product of a right
  `R`-module `X` and a left `R`-module `N` over an arbitrary ring `R`, as the quotient of
  `X ⊗[ℤ] N` by the balancing relations.  API: `mk`, `mk_add_left`, `mk_add_right`,
  `mk_smul_right`, `mk_zsmul_left`, `mk_zsmul_right`, `mem_closure_mk`,
  `closure_range_mk_eq_top`, `ext`, `lift`, `lift_mk`, `map`, `map_mk`, `map_id`, `map_comp`,
  `map_surjective`.
* `Work.ORFlatness.LeftFlat R M` (`Flat.lean`): the left `R`-module `M` is flat, i.e.
  tensoring on the right by `M` preserves injective maps of right `R`-modules.
* `Work.ORFlatness.RightFlat R X` (`Flat.lean`): the right `R`-module `X` is flat, i.e.
  tensoring on the left by `X` preserves injective maps of left `R`-modules.
  (Mathlib's `Module.Flat` is only available for commutative rings; these two notions are
  equivalent to it in the commutative case, see `leftFlat_iff_moduleFlat`.)
* `Work.ORFlatness.Tor1Vanishes R X N` (`Flat.lean`): the dimension criterion for
  `Tor₁^R(X, N) = 0` (`X` right, `N` left): some projective presentation `0 → K → P → X → 0`
  of `X` has `K ⊗[R] N → P ⊗[R] N` injective.
* `Work.ORFlatness.ProjPres R X` (`Flat.lean`): projective presentations of a right module.
* `Work.ORFlatness.Tor2Vanishes R X N` (`Tor2.lean`): `Tor₂^R(X, N) = 0` in syzygy form.
* `Work.ORFlatness.diagModule` (`Diagonal.lean`): for `X` a *right* `K[G]`-module, the *left*
  `K[G]`-module structure on `S ⊗[K] X` with `g • (s ⊗ x) = (φ g * s * (φ g)⁻¹) ⊗ (x · g⁻¹)`.
* `Work.ORFlatness.diagRightModule` (`DiagonalRight.lean`): for `X` a *left* `K[G]`-module, the
  *right* `K[G]`-module structure on `S ⊗[K] X` with `(s ⊗ x) · g = (s * φ g) ⊗ (g⁻¹ • x)`.

## Flatness criteria

* `Work.ORFlatness.Tor1Vanishes.of_leftFlat` and
  `Work.ORFlatness.leftFlat_iff_forall_tor1Vanishes` (`FlatCrit.lean`):
  `LeftFlat R M ↔ ∀ X, Tor1Vanishes R X M`.
* `Work.ORFlatness.rightFlat_of_forall_tor1Vanishes` (`RightFlatCrit.lean`):
  `(∀ N, Tor1Vanishes R X N) → RightFlat R X` (the direction needed below).
* `Work.ORFlatness.rightFlat_of_projective`, `Work.ORFlatness.leftFlat_of_projective`:
  projective modules are flat.
* `Work.ORFlatness.range_map_eq_ker_map`, `Work.ORFlatness.range_map_eq_ker_map_right`
  (`Submission/Work/ORFlatness/`): right exactness of `BalTensor` in each variable.
* `Work.ORFlatness.injective_of_tor1Vanishes`, `Work.ORFlatness.injective_of_tor1Vanishes_right`:
  dimension shifting (converse direction).
* `Work.ORFlatness.tor1Vanishes_of_shortExact`, `Work.ORFlatness.tor1Vanishes_of_shortExact_right`:
  dimension shifting (forward direction).

## Main results

Left `K[G]`-module `S ⊗[K] C` (Jaikin-Zapirain--Linton, Theorem 5.6, `JLMain.lean`):

* `Work.ORFlatness.tor1Vanishes_diagonal_jl`
* `Work.ORFlatness.leftFlat_diagonal_jl` (takes the reduction hypothesis `hred`)
* `Work.ORFlatness.leftFlat_diagonal_jl_of_testFamily` (no `hred`; recommended)

Right `K[G]`-module `S ⊗[K] C` (the same theorem "by symmetry", `JLRightMain.lean`):

* `Work.ORFlatness.tor1Vanishes_diagonal_jl_right`
* `Work.ORFlatness.rightFlat_diagonal_jl`

`Tor₂` (Jaikin-Zapirain--Linton, Theorem 1.7):

* `Work.ORFlatness.tor2Vanishes_of_flat_augmentation` (`Tor2.lean`)
* `Work.ORFlatness.torVanishes_of_flatDiagonal`, `Work.ORFlatness.torTwoVanishes_of_flatDiagonal`
  (`Tor2ORCoherence.lean`): `Tor₂^{K[G]}(S, M) = 0` for all `M`, in the vocabulary of N10.
* `Work.ORFlatness.torTwoVanishes_diagonal_jl_right` (`Tor2ORCoherence.lean`): the assembled
  statement, from the mirror of Theorem 5.6 and the duality chain, concluding
  `Work.ORCoherence.TorTwoVanishes φ.toRingHom`.

Instantiation at the augmentation ideal (`AugIdealFlatness.lean`):

* `Work.ORFlatness.leftFlat_diagonal_augIdeal`, `Work.ORFlatness.rightFlat_diagonal_augIdeal`
  (`Work.ORFlatness.exists_augIdeal_rightModule` supplies the right `K[G]`-module structure on
  the augmentation ideal, which is two-sided).

In the vocabulary of N1 (`IsFlatDiagonal.lean`):

* `Work.ORFlatness.leftFlat_iff_isFlatLeft`, `Work.ORFlatness.rightFlat_iff_isFlatRight`:
  `LeftFlat`/`RightFlat` (this area) coincide with `Work.ORHomAlg.IsFlatLeft`/`IsFlatRight`;
* `Work.ORFlatness.isFlatLeft_diagonal_jl`, `Work.ORFlatness.isFlatRight_diagonal_jl`: the two
  flatness theorems of Theorem 5.6 restated as `Work.ORHomAlg.IsFlatLeft`/`IsFlatRight`;
* in the commutative case `Work.ORFlatness.leftFlat_iff_moduleFlat` identifies `LeftFlat` with
  Mathlib's `Module.Flat`.

For the node's title ("flatness implies weak dimension at most one"): the conclusion delivered
here is `∀ M, Tor₂^{K[G]}(S, M) = 0`, i.e. `Work.ORCoherence.TorVanishes φ.toRingHom`, which is
the form N10 consumes (`Work.ORCoherence.TorTwoVanishes f`).  The equivalent statement
`Work.ORHomAlg.weakDimLe (K[G]) S 1` (vanishing of `Tor_k` for all `k ≥ 2`) follows from it by
the standard dimension-shifting argument, which needs the long exact sequence for
`Work.ORHomAlg.Tor`; at the time of writing `Work.ORHomAlg` provides `isFlatRight_iff_torOne`
and `Tor.subsingleton_succ` but not the long exact sequence, so that passage is not formalised
here.

## How to use the area

For the coherence of `K[G]` (node N10) the relevant interface is
`Work.ORFlatness.torTwoVanishes_diagonal_jl_right`, whose conclusion
`Work.ORCoherence.TorTwoVanishes φ.toRingHom` is exactly the hypothesis of
`Work.ORCoherence.coherent_of_embeds_semisimple`.  Its hypotheses are Claim 5.8, Lemma 5.1
(with Claim 5.9), the duality of Lemma 5.2 in the form `hswap`, and the duality chain of
Lemma 5.2 in the form `hchain`.  See the module documentation of `JLRightMain.lean` and
`Tor2ORCoherence.lean` for the precise statements.
-/
import Submission.Work.ORFlatness.Tensor
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.FlatCrit
import Submission.Work.ORFlatness.RightFlatCrit
import Submission.Work.ORFlatness.Diagonal
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORFlatness.JLMain
import Submission.Work.ORFlatness.JLRightMain
import Submission.Work.ORFlatness.Tor2
import Submission.Work.ORFlatness.Tor2ORCoherence
import Submission.Work.ORFlatness.AugIdealFlatness
import Submission.Work.ORFlatness.leftFlat_diagonal_jl_of_testFamily
import Submission.Work.ORFlatness.range_map_eq_ker_map
import Submission.Work.ORFlatness.range_map_eq_ker_map_right
import Submission.Work.ORFlatness.injective_of_tor1Vanishes
import Submission.Work.ORFlatness.injective_of_tor1Vanishes_right
import Submission.Work.ORFlatness.tor1Vanishes_of_shortExact
import Submission.Work.ORFlatness.tor1Vanishes_of_shortExact_right
import Submission.Work.ORFlatness.projPres_exists
import Submission.Work.ORFlatness.injective_map_of_retract
import Submission.Work.ORFlatness.exists_retraction_of_projective_cokernel
import Submission.Work.ORFlatness.rightFlat_of_projective
import Submission.Work.ORFlatness.rightFlat_of_retract
import Submission.Work.ORFlatness.leftFlat_of_testFamily
import Submission.Work.ORFlatness.exists_compatibleKStructure
import Submission.Work.ORFlatness.leftFlat_iff_isFlatLeft
import Submission.Work.ORFlatness.rightFlat_iff_isFlatRight
import Submission.Work.ORFlatness.IsFlatDiagonal
import Submission.Work.ORFlatness.exists_augIdeal_rightModule
import Submission.Work.ORFlatness.leftFlat_of_linearEquiv
import Submission.Work.ORFlatness.leftFlat_of_projective
