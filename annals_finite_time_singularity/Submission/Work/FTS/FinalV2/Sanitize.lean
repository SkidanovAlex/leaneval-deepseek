import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.Final.Assembly
import Submission.Work.FTS.Final.ExtG.dynOK_extG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Sanitize` — the sanitiser `gS` (curric-46 lead install, 2026-10-10)

REVIEW F1 item 3 (`cbc/fts_regexport_design_REVIEW.md`): the PROVED `gS` block of
`cbc/fts_regexport_design.lean` §1, verbatim. `gS α h` keeps `h` on `z > 0, θ ∈ [0,π/2]`, is `0` on
`z ≤ 0` and `−F_*` off `[0,π/2]`. Conjunct (7″) of `Inputs'` is stated on `extG (gS α (tauExt g))`;
the adapter fires on `extG (gS α g)` and transports `hsmall` (`extG_gS_of_mem`), `hMer`/`hW`
(`merProfile_gS`) and `hHid` (`physOmega_gS`). `hsuppOut_gS` makes `GalMin.hsuppOut` trivial.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG extG_of_nonpos extG_of_pos)

set_option autoImplicit false

/-- **The sanitiser.** Keeps `h` on `z > 0, θ ∈ [0,π/2]`; sets it to `0` on `z ≤ 0` (so the
`z = 0` values read by `R5Parts.hRz0` are honest) and to `−F_*` for `θ ∉ [0,π/2]` (so that
`GalMin.hsuppOut` holds trivially). `extG (gS α h) = extG h` at every `θ ∈ [0,π/2]`
(`extG_gS_of_mem`), and the firing reads only those `θ` (`merProfile_gS`, `physOmega_gS`). -/
def gS (α : ℝ) (h : Fam) : Fam := fun z θ τ =>
  if 0 < z then (if 0 ≤ θ ∧ θ ≤ π / 2 then h z θ τ else - Work.Construction.Fstar (pExp α) z θ)
  else 0

theorem extG_gS_of_mem (α : ℝ) (h : Fam) {z θ τ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2) :
    extG (gS α h) z θ τ = extG h z θ τ := by
  by_cases hz : z ≤ 0
  · rw [extG_of_nonpos hz, extG_of_nonpos hz]
  · have hz' : 0 < z := lt_of_not_ge hz
    have hfun : (fun s => gS α h z θ s) = fun s => h z θ s := by
      funext s; simp [gS, hz', hθ0, hθ1]
    simp only [Work.FTS.RegPkgGal.extG, hz, ite_false]
    rw [hfun]
    simp [gS, hz', hθ0, hθ1]

/-- `GalMin.hsuppOut` is automatic for a sanitised family. -/
theorem hsuppOut_gS (α S : ℝ) (h : Fam) :
    ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → θ ∉ Work.Spaces.Iθ →
      Work.FTS.Regularity.profFull α (extG (gS α h)) z θ τ = 0 := by
  refine ⟨1, one_pos, fun τ hτ z θ hz hθ => ?_⟩
  have hz' : 0 < z := by linarith
  have hθ' : ¬ (0 ≤ θ ∧ θ ≤ π / 2) := fun hh => hθ hh
  rw [Work.FTS.Regularity.profFull_apply, extG_of_pos hz' hτ.1]
  simp [gS, hz', hθ']

theorem profile_gS (α : ℝ) (h : Fam) (τ Z θ : ℝ) (hθ : |θ| ≤ π / 2) :
    Work.ConstructionInstance.profile (pExp α)
        (Work.FTS.Regularity.gSlice (extG (gS α h)) τ) Z θ
      = Work.ConstructionInstance.profile (pExp α)
        (Work.FTS.Regularity.gSlice (extG h) τ) Z θ := by
  have hb := abs_le.mp hθ
  unfold Work.ConstructionInstance.profile
  split_ifs with h0
  · simp only [Work.FTS.Regularity.gSlice, extG_gS_of_mem α h h0 hb.2]
  · have h1 : 0 ≤ -θ := by linarith
    have h2 : -θ ≤ π / 2 := by linarith
    simp only [Work.FTS.Regularity.gSlice, extG_gS_of_mem α h h1 h2]

theorem abs_arctan_le (x : ℝ) : |Real.arctan x| ≤ π / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩

/-- **Adapter transport (8′)/(10′)/hW**: the meridian profile does not see the sanitiser. -/
theorem merProfile_gS (α : ℝ) (A B : ℝ → ℝ) (h : Fam) (C : Work.FTS.Physical.PhysClock) :
    Work.FTS.Physical.merProfile α A B (extG (gS α h)) C
      = Work.FTS.Physical.merProfile α A B (extG h) C := by
  funext r z t
  simp only [Work.FTS.Physical.merProfile]
  rw [profile_gS α h _ _ (Work.Cyl.thetaP r z) (by unfold Work.Cyl.thetaP; exact abs_arctan_le _)]

/-- **Adapter transport (9′)/firing**: the physical vorticity does not see the sanitiser. -/
theorem physOmega_gS (α : ℝ) (A B : ℝ → ℝ) (h : Fam) (C : Work.FTS.Physical.PhysClock) :
    Work.FTS.Physical.physOmega α A B (extG (gS α h)) C
      = Work.FTS.Physical.physOmega α A B (extG h) C := by
  funext x t
  simp only [Work.FTS.Physical.physOmega, Work.FTS.Regularity.physVort,
    Work.ConstructionInstance.omegaSz]
  rw [profile_gS α h _ _ (Work.Cyl.theta x) (by unfold Work.Cyl.theta; exact abs_arctan_le _)]

end Work.FTS.FinalV2
