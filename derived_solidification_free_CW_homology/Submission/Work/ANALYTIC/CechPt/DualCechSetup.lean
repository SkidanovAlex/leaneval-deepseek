import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualComplex
import Submission.Work.ANALYTIC.CechPt.CechTermDefs
import Submission.Work.ANALYTIC.CechPt.LevelModelDefs
import Submission.Work.ANALYTIC.CechPt.cechTermLevelProjections
import Submission.Work.ANALYTIC.CechPt.level_acyclic

/-!
# The dual Čech complex of the Cantor cover, in its "locally constant functions" model

`Work.ANALYTIC.CechPt.DualAugContractible` (in `CechPt/DualComplex.lean`) asserts that the
augmented complex

`𝟙 ⟶ (ℤ[C_0] ⟹ 𝟙) ⟶ (ℤ[C_1] ⟹ 𝟙) ⟶ ⋯`

is contractible, where `C_p = cechTerm p` is the `p`-th term of the Čech nerve of the binary
expansion and `X ⟹ 𝟙` is the internal hom into the unit.

This module sets up the *abelian group* model of that complex which is used for the proof:
the terms are the groups of locally constant `ℤ`-valued functions

`DualC p = C(cechTerm p, ℤ)`,

the differential `dualD p` is the alternating sum of the pullbacks along the face maps
`cechFace p i` (this is the transpose of the Čech differential `dR p` of `DualComplex.lean`), and
the augmentation `dualAug` is the "constant function `1`" map `ℤ ⟶ C(cechTerm 0, ℤ)`.

The proof of `DualAugContractible` then runs through the (paper's, REFS/04 §1) statement that

`0 ⟶ ℤ ⟶ C(C_0,ℤ) ⟶ C(C_1,ℤ) ⟶ ⋯`

is an exact complex of free abelian groups, hence contractible, transported back to the light
condensed setting along the canonical identification `(ℤ[T] ⟹ 𝟙) ≅ C(T,ℤ)_disc`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- The abelian group of locally constant `ℤ`-valued functions on the `p`-th Čech term. -/
abbrev DualC (p : ℕ) : Type := LocallyConstant ↥(cechTerm p) ℤ

/-- The underlying function of the differential: `f ↦ (x ↦ Σ_i (-1)^i f (cechFace p i x))`. -/
def dualDfun (p : ℕ) (f : DualC p) : ↥(cechTerm (p + 1)) → ℤ :=
  fun x => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) * f ((cechFace p i) x)

theorem isLocallyConstant_dualDfun (p : ℕ) (f : DualC p) : IsLocallyConstant (dualDfun p f) := by
  rw [IsLocallyConstant.iff_continuous]
  refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
  exact f.continuous.comp (cechFace p i).hom.hom.continuous

/-- The differential of the dual Čech complex on locally constant functions:
`(df)(x) = Σ_i (-1)^i f (cechFace p i x)`.  This is the transpose of `dR p`. -/
def dualD (p : ℕ) : DualC p →ₗ[ℤ] DualC (p + 1) where
  toFun f := ⟨dualDfun p f, isLocallyConstant_dualDfun p f⟩
  map_add' f g := by
    ext x
    change dualDfun p (f + g) x = dualDfun p f x + dualDfun p g x
    simp only [dualDfun, LocallyConstant.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    change dualDfun p (c • f) x = c * dualDfun p f x
    simp only [dualDfun, LocallyConstant.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The value of the differential: `(dualD p f) x = Σ_i (-1)^i f (cechFace p i x)`. -/
theorem dualD_apply (p : ℕ) (f : DualC p) (x : ↥(cechTerm (p + 1))) :
    dualD p f x = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) * f ((cechFace p i) x) := rfl

/-- The augmentation of the dual complex: the constant function `1`, i.e. the map
`k ↦ (fun _ ↦ k)`. -/
def dualAug : ℤ →ₗ[ℤ] DualC 0 :=
  LinearMap.toSpanSingleton ℤ (DualC 0) (1 : DualC 0)

/-- The augmentation is the "constant function" map. -/
@[simp]
theorem dualAug_apply (k : ℤ) (x : ↥(cechTerm 0)) : dualAug k x = k := by
  show (LinearMap.toSpanSingleton ℤ (DualC 0) (1 : DualC 0)) k x = k
  rw [LinearMap.toSpanSingleton_apply, LocallyConstant.smul_apply, LocallyConstant.one_apply,
    smul_eq_mul, mul_one]

/-! ## Compatibility of the level projections with the face maps

`cechTerm p` is the inverse limit of the level-`n` dyadic nerves `Level.lev (2^(n+1)) p` along
the projections `lvlOf p n` (`Submission/Work/ANALYTIC/CechPt/cechTermLevelProjections.lean`).
Deleting the `i`-th coordinate commutes with the truncation of the coordinates to `n+1` binary
digits, whence the level projection is a map of simplicial objects.  This is the input to the
computation of `dualD` on the level model. -/

theorem lvlOf_cechFace (p n : ℕ) (i : Fin (p + 2)) (x : ↥(cechTerm (p + 1))) :
    lvlOf p n ((cechFace p i) x) = Level.face i (lvlOf (p + 1) n x) := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  simp only [lvlOf, Level.face, cechFace_apply]

end Work.ANALYTIC.CechPt
