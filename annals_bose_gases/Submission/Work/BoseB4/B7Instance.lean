import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.AnnOf_ann_comm
import Submission.Work.BoseB4.AnnOf_creOf_ccr
import Submission.Work.BoseB4.Bomb_self_eq_zero
import Submission.Work.BoseB4.Bomb_self_nonneg
import Submission.Work.BoseB4.Bomb_symm
import Submission.Work.BoseB4.CreOf_annOf_adjoint
import Submission.Work.BoseB4.CreOf_cre_comm
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.B7Instance` — inhabiting node B7's Fock interface

`Work.BoseB7.FockData` (`Submission/Work/BoseB7/FockDefs.lean`) is explicitly
documented as *"the interface (what `B4` must supply)"*: a mode system on
`(2π/ℓ)ℤ³` with the box commutator `ccrKernel`, a Fock form `bp` and `a† = a*`.
This module supplies it, from the real bosonic Fock space of
`Work.BoseB4.RealFock` / `Work.BoseB4.ModeFock`:

* `b7FockData kmom hkmom f` — the **generic instantiation**.  The one-particle
  space is `Fin m → ℝ` (the caller picks an orthonormal basis of the span of the
  mode vectors and passes coordinates `f i`), `a i = annOf (f i)`,
  `aDag i = creOf (f i)`, `bp = bomb m`, and
  `ccrK i j = gram (f i) (f j)` = the Gram product of the one-particle mode
  vectors.
* `b7FockDataBox kmom hkmom ell hatChiSq hatChi f hgram` — the **box
  instantiation**: same, but with `ccrK` *forced* to be FS `eq:Commutator_general`
  `ccrKernel ℓ hatChiSq hatChi (kmom i) (kmom j)`, the hypothesis `hgram` being
  the box identity
  `⟪Q(e^{ik_i x}χ_Λ), Q(e^{ik_j x}χ_Λ)⟫ = χ̂²((k_i−k_j)ℓ) − χ̂(k_iℓ)·χ̂(k_jℓ)`.

`hgram` is the *only* box input: it is the standard computation of the inner
product of the localised plane waves in `L²(Λ)` (`⟨e^{ikx}χ_Λ, e^{ik'x}χ_Λ⟩ =
∫_Λ e^{i(k−k')x}dx`, normalised), which the corpus's `L²(Λ)` / Fourier machinery
supplies.  Everything else — the mode system, its CCR package, the Fock form, the
adjointness `a† = a*` and the positivity/definiteness of `bp` — is *proved* here.

`Work.BoseB4.Gram` removes even the existence obligation: *every* symmetric
positive semidefinite kernel on `Mode` is `gram f` for some `f`
(`Work.BoseB4.Exists_gram_iff`), so the box instantiation
`b7FockDataBox` is non-vacuous as soon as `ccrKernel` is symmetric and PSD, which
is exactly its meaning as a Gram matrix of the localised plane waves.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- **The generic `B7` Fock interface**: the real bosonic Fock space over
`m` coordinate modes, with the mode system given by the one-particle coordinate
vectors `f i`, and commutator kernel equal to their Gram matrix. -/
noncomputable def b7FockData {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (m : ℕ) (f : Mode → Fin m → ℝ) : BoseB7.FockData Mode where
  H := RealFock m
  instAddCommGroup := inferInstance
  instModule := inferInstance
  kmom := kmom
  kmom_neg := hkmom
  a := fun i => annOf m (f i)
  aDag := fun i => creOf m (f i)
  ann_comm := fun i j => AnnOf_ann_comm (f i) (f j)
  cre_comm := fun i j => CreOf_cre_comm (f i) (f j)
  ccrK := fun i j => gram (f i) (f j)
  ccr := fun i j => AnnOf_creOf_ccr (f i) (f j)
  bp := bomb m
  bp_symm := fun x y => Bomb_symm x y
  bp_nonneg := fun x => Bomb_self_nonneg x
  bp_def := fun _ h => Bomb_self_eq_zero h
  aDag_adjoint := fun i x y => CreOf_annOf_adjoint (f i) x y

/-- **The box instantiation of the `B7` Fock interface.**  Same construction, but
the commutator kernel is FS `eq:Commutator_general`'s `ccrKernel` — the hypothesis
`hgram` is the `L²(Λ)` computation of the Gram products of the localised plane
waves `Q(e^{ikx}χ_Λ)`. -/
noncomputable def b7FockDataBox {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (ell : ℝ) (hatChiSq hatChi : EuclideanSpace ℝ (Fin 3) → ℝ)
    (m : ℕ) (f : Mode → Fin m → ℝ)
    (hgram : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ell hatChiSq hatChi (kmom i) (kmom j)) :
    BoseB7.FockData Mode where
  H := RealFock m
  instAddCommGroup := inferInstance
  instModule := inferInstance
  kmom := kmom
  kmom_neg := hkmom
  a := fun i => annOf m (f i)
  aDag := fun i => creOf m (f i)
  ann_comm := fun i j => AnnOf_ann_comm (f i) (f j)
  cre_comm := fun i j => CreOf_cre_comm (f i) (f j)
  ccrK := fun i j => BoseB7.ccrKernel ell hatChiSq hatChi (kmom i) (kmom j)
  ccr := fun i j => by
    rw [← hgram i j]
    exact AnnOf_creOf_ccr (f i) (f j)
  bp := bomb m
  bp_symm := fun x y => Bomb_symm x y
  bp_nonneg := fun x => Bomb_self_nonneg x
  bp_def := fun _ h => Bomb_self_eq_zero h
  aDag_adjoint := fun i x y => CreOf_annOf_adjoint (f i) x y

end Work.BoseB4
