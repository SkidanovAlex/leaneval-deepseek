import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.ANALYTIC.exists_pairMor
import Submission.Work.ANALYTIC.eaZeroSlice
import Submission.Work.ATOM.Toolkit.PP_desc

/-!
# The primed null-sequence tower of AN1 (REFS/03 §2)

This module builds the *primed* tower `F' : P ⊗ P ⟶ P` of REFS/03 §2, `(k, e_j) ↦ e_j·[j ≥ k]`,
together with the identity `h₇ = s' ≫ F' = 𝟙 P` of the scheme of REFS/03 §1.  It deliberately does
NOT import `Submission.Work.ANALYTIC.cBounded_solidEquiv` (which imports this module), so that the
final assembly can use `Work.ANALYTIC.FP` without a cycle.

`F'` is obtained by descending, along the presentation `P ⊗ P = coker (EApp)`, the explicit map
`chi : ℤ[(ℕ∪∞)²] ⟶ P` induced by the continuous map `pairMor` of
`Submission/Work/ANALYTIC/exists_pairMor.lean`.  The identity `h₇` is proved by comparing the
composite `P_proj ≫ s'` with `zmap (zeroSlice (ℕ∪∞)) ≫ EApp` and using `EApp ≫ F' = chi` together
with `zeroSlice ≫ pairMor = 𝟙`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- `zmap` is a functor, so it preserves composition. -/
theorem zmap_comp' {S T U : LightProfinite.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map_comp f g

/-- The constant `∞`-map out of a light profinite set is killed by `P_proj`. -/
theorem const_infty_comp (S : LightProfinite.{0}) :
    Work.ATOM.zmap (Work.ATOM.toPt S ≫ LightCondensed.ι) ≫ LightCondensed.P_proj = 0 := by
  rw [zmap_comp', Category.assoc]
  rw [show Work.ATOM.zmap LightCondensed.ι = LightCondensed.P_map from rfl]
  rw [show LightCondensed.P_map ≫ LightCondensed.P_proj = 0 from
    cokernel.condition LightCondensed.P_map, comp_zero]

/-- The map `ℤ[(ℕ∪∞)²] ⟶ P` underlying the primed family `F'`: it sends the generator
`[(k,j)]` to `e_j` if `j ≥ k` and to `0` otherwise. -/
noncomputable def chi : Work.ATOM.zfree ((ℕ∪{∞}) ⊗ (ℕ∪{∞})) ⟶ LightCondensed.P :=
  Work.ATOM.zmap Work.ANALYTIC.pairMor ≫ LightCondensed.P_proj

/-- `pairMor` sends the `∞`-slice of the first variable to `∞`. -/
theorem pairMor_infty_fst_eq :
    MonoidalCategory.whiskerRight LightCondensed.ι (ℕ∪{∞}) ≫ Work.ANALYTIC.pairMor =
      Work.ATOM.toPt _ ≫ LightCondensed.ι := by
  apply ConcreteCategory.hom_ext
  intro p
  show Work.ANALYTIC.pairMor (⟨(∞ : ℕ∪{∞}), p.2⟩ : ↥((ℕ∪{∞}) ⊗ (ℕ∪{∞}))) =
    LightCondensed.ι PUnit.unit
  rw [Work.ANALYTIC.pairMor_apply, Work.ANALYTIC.pairFun_infty_fst]
  rfl

/-- `pairMor` sends the `∞`-slice of the second variable to `∞`. -/
theorem pairMor_infty_snd_eq :
    MonoidalCategory.whiskerLeft (ℕ∪{∞}) LightCondensed.ι ≫ Work.ANALYTIC.pairMor =
      Work.ATOM.toPt _ ≫ LightCondensed.ι := by
  apply ConcreteCategory.hom_ext
  intro p
  show Work.ANALYTIC.pairMor (⟨p.1, (∞ : ℕ∪{∞})⟩ : ↥((ℕ∪{∞}) ⊗ (ℕ∪{∞}))) =
    LightCondensed.ι PUnit.unit
  rw [Work.ANALYTIC.pairMor_apply, Work.ANALYTIC.pairFun_infty_snd]
  rfl

/-- The `∞`-slice in the first variable is killed by `chi`. -/
theorem chi_infty_fst :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι (ℕ∪{∞})) ≫ chi = 0 := by
  rw [chi, ← Category.assoc, ← zmap_comp', pairMor_infty_fst_eq, const_infty_comp]

/-- The `∞`-slice in the second variable is killed by `chi`. -/
theorem chi_infty_snd :
    Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) LightCondensed.ι) ≫ chi = 0 := by
  rw [chi, ← Category.assoc, ← zmap_comp', pairMor_infty_snd_eq, const_infty_comp]

/-- **The primed family `F' : P ⊗ P ⟶ P` of REFS/03 §2**, obtained by descending `chi`. -/
noncomputable def FP : LightCondensed.P ⊗ LightCondensed.P ⟶ LightCondensed.P :=
  Classical.choose (Work.ATOM.Toolkit.PP_desc chi chi_infty_fst chi_infty_snd)

/-- The characterizing property of `FP`. -/
theorem FP_spec : Work.ATOM.EApp ≫ FP = chi :=
  (Classical.choose_spec (Work.ATOM.Toolkit.PP_desc chi chi_infty_fst chi_infty_snd)).1

/-- The section `s' = e₀ ⊗ - : P ⟶ P ⊗ P`. -/
noncomputable def sPrimeZ : LightCondensed.P ⟶ LightCondensed.P ⊗ LightCondensed.P :=
  (λ_ LightCondensed.P).inv ≫ (Work.ANALYTIC.ePointZ 0 ▷ LightCondensed.P)

/-- The composite `zeroSlice (ℕ∪∞) ≫ pairMor` is the identity. -/
theorem zeroSlice_pairMor :
    Work.ANALYTIC.zeroSlice (ℕ∪{∞}) ≫ Work.ANALYTIC.pairMor = 𝟙 (ℕ∪{∞}) := by
  apply ConcreteCategory.hom_ext
  intro j
  show Work.ANALYTIC.pairFun (Work.ANALYTIC.zeroSlice (ℕ∪{∞}) j) = j
  rw [Work.ANALYTIC.zeroSlice_apply]
  cases j with
  | none =>
      show Work.ANALYTIC.pairFunP (((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)) = ∞
      exact Work.ANALYTIC.pairFunP_infty_snd ((0 : ℕ) : OnePoint ℕ)
  | some m =>
      show Work.ANALYTIC.pairFunP (((0 : ℕ) : OnePoint ℕ), ((m : ℕ) : OnePoint ℕ)) =
        ((m : ℕ) : OnePoint ℕ)
      rw [Work.ANALYTIC.pairFunP_finite]; simp

/-- **The identity `h₇` of REFS/03 §1**: `s' ≫ F' = 𝟙 P`. -/
theorem h7_scheme : sPrimeZ ≫ FP = 𝟙 LightCondensed.P := by
  apply P_cancel
  rw [← Category.assoc]
  have key : LightCondensed.P_proj ≫ sPrimeZ =
      Work.ATOM.zmap (Work.ANALYTIC.zeroSlice (ℕ∪{∞})) ≫ Work.ATOM.EApp := by
    have ha : LightCondensed.P_proj ≫ (λ_ LightCondensed.P).inv =
        (λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫
          (𝟙_ LightCondAb ◁ LightCondensed.P_proj) := by
      have h := id_whiskerLeft (C := LightCondAb) LightCondensed.P_proj
      rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [show sPrimeZ = (λ_ LightCondensed.P).inv ≫ (Work.ANALYTIC.ePointZ 0 ▷
      LightCondensed.P) from rfl]
    rw [← Category.assoc, ha, Category.assoc, whisker_exchange]
    rw [← Category.assoc, show (λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫
        (Work.ANALYTIC.ePointZ 0 ▷ Work.ATOM.zfree (ℕ∪{∞})) =
        Work.ATOM.zmap (Work.ANALYTIC.zeroSlice (ℕ∪{∞})) ≫ Work.ATOM.EA (ℕ∪{∞}) from
      Work.ANALYTIC.eaZeroSlice (ℕ∪{∞})]
    rw [Category.assoc]
    rw [show Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj) =
      Work.ATOM.EApp from rfl]
  rw [key, Category.assoc]
  have key2 : Work.ATOM.zmap (Work.ANALYTIC.zeroSlice (ℕ∪{∞})) ≫ chi =
      LightCondensed.P_proj := by
    show Work.ATOM.zmap (Work.ANALYTIC.zeroSlice (ℕ∪{∞})) ≫
      (Work.ATOM.zmap Work.ANALYTIC.pairMor ≫ LightCondensed.P_proj) =
        LightCondensed.P_proj
    rw [← Category.assoc, ← zmap_comp', zeroSlice_pairMor]
    simp
  rw [FP_spec, key2, Category.comp_id]

end Work.ANALYTIC
