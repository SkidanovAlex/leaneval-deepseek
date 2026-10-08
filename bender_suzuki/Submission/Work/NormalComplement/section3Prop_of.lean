import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec3_prop1
import Submission.Work.NormalComplement.sec3_cor_case1
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.section2Corollary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Ch. III §2 Corollary + §3 assembled** (pp. 176–178): `Work.NormalComplement.Section3Prop`,
i.e. if `E = W ⊓ D` is not in case (D2), then `D` has a normal complement in `H`.

Pure glue over the case split `¬ IsD2 ⟺ C_V(K) ≠ 1 ∨ E' ⊓ V = ⊥ ∨ NoCentralizedNormal`:

* `C_V(K) ≠ 1`: Ch. II §4 Prop. 4 (b) (the P4 clause of `hC4`) gives `H = C_H(Inv H)·D`, and
  `Section2CorollaryProp` (`hS2c`) gives the conclusion;
* `E' ⊓ V = ⊥`: `Design.sec3_cor_case1` gives the `FrobPacket`, then `Section3Prop2` (`hS32`,
  proved as `Work.NormalComplement.section3_prop2`) gives the conclusion;
* `NoCentralizedNormal H t`: `Design.sec3_prop1` gives the `FrobPacket`, then `hS32`.

Note `Setup3` carries `E ≠ ⊥`, which `Section3Prop` does not assume: split on
`W ⊓ twoPoint H t = ⊥` first, where the conclusion is immediate with `Q = W`.

Import `Submission.Work.NormalComplement.sec3_prop1`, `...sec3_cor_case1`, `...section3_prop2`,
`...section2Corollary` by path. -/
theorem section3Prop_of (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp)
    (hS2c : Work.NormalComplement.Section2CorollaryProp)
    (hS32 : Work.NormalComplement.Section3Prop2) :
    Work.NormalComplement.Section3Prop := by
  intro G _ _ hSit H hH t ht htH W hWle hNorm hSup hD1 hNotD2
  -- Case `E = W ⊓ D = ⊥`: the conclusion is immediate with `Q = W`.
  by_cases hE : W ⊓ twoPoint H t = ⊥
  · exact ⟨W, hWle, hNorm, hE, hSup⟩
  · -- Otherwise `E ≠ ⊥`, so the standing data of §3 hold.
    have hSetup : Design.Setup3 G H t W :=
      ⟨hSit, hH, ht, htH, hWle, hNorm, hSup, hE, hD1⟩
    -- `¬ IsD2` is the disjunction `¬A ∨ ¬B ∨ ¬C` for `IsD2 = A ∧ B ∧ C`.
    have hD2 : ¬ IsD2 H t W := hNotD2
    unfold IsD2 at hD2
    rcases (not_and_or.mp hD2) with hA | hBC
    · -- `¬A`: `NoCentralizedNormal H t`; §3 Prop. 1 gives the `FrobPacket`, then §3 Prop. 2.
      have hN : Design.NoCentralizedNormal H t := by
        intro X hX hXV hVn
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨?_, ?_⟩
        · -- `1 ∈ C_K(X)`
          simp [Design.CK, Kset, invertedBy]
        · -- `C_K(X)` is a subsingleton
          intro k hk
          have hkK : k ∈ Kset (twoPoint H t) t := hk.1
          have hkC : k ∈ Subgroup.centralizer (X : Set G) := hk.2
          by_contra hk1
          exact hA ⟨X, hX, hXV, hVn, k, hkK, hk1, fun x hx => by
            have hcomm : k * x = x * k := (hkC x hx).symm
            rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]⟩
      have hFrob : Design.FrobPacket H t W :=
        sec3_prop1 hFT hC4 hMod hV hVII hSetup hN
      exact hS32 G hSit H hH t ht htH W hWle hNorm hSup hFrob
    · rcases (not_and_or.mp hBC) with hB | hC
      · -- `¬B`: `C_V(K) ≠ 1`; Ch. II §4 Prop. 4 (b) gives `H = C_H(Inv H)·D`, then §2 Corollary.
        have hCV :
            centD H t ⊓ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) ≠ ⊥ := hB
        have hP4b := (hC4 G hSit H hH t ht htH).2.2.2.2.2
        have hHinv := hP4b hCV
        exact hS2c G hSit H hH t ht htH hHinv
      · -- `¬C`: `E' ⊓ V = ⊥`; §3 Corollary case 1 gives the `FrobPacket`, then §3 Prop. 2.
        have hE'V : Design.Ecomm H t W ⊓ centD H t = ⊥ := not_not.mp hC
        have hFrob : Design.FrobPacket H t W := sec3_cor_case1 hFT hSetup hE'V
        exact hS32 G hSit H hH t ht htH W hWle hNorm hSup hFrob

end Work.NormalComplement
