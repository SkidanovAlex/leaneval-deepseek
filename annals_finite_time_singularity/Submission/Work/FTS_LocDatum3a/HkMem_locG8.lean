/-
# `Work.FTS_LocDatum3a.HkMem_locG8` — the localised datum `locG6 α L β` lies in `ℋ⁸`

Chapter `FTS_LocDatum3a` produces clause (3a′) of the strong-solution interface: the localised
order-`6` datum `locG6 α L β = Work.FTS.LocData.locG α L β (hLoc α)` of the chapter
`Submission/Work/FTS/LocData6/` is regular data of the `ε`-scheme.  Its class-C clause needs the
weighted honesty of the datum at order `8` (`Work.Spaces.HkMem α 8 (locG6 α L β)`, consumed by
`Work.FTS.StrongEps.softClass_Jeps` as the `mem8` field), one order above the delivered
`Work.FTS.Nonlin.RegQ α 6` of `Submission.Work.FTS.LocData6.RegQ6`.  This module supplies it.

## The route

`locG6 α L β` is **separable** (`Work.FTS.LocDataExt.locG_eq_locR_Gam`):

  `locG6 α L β = locR α L β(z) · Γ(θ)`,  `locR α L β z = -(α/c)·zfarR L z + β·bumpZ z`,

so the whole content is the generic separable majorant
`Work.FTS.LocDataExt.HkIntegrand_sepGam_le` at `k = 8`, whose two inputs are

* the **radial** bound `(D_z^j (locR α L β) z · w z)² ≤ R/(1+z)²` for `j ≤ 8`
  (`Work.FTS_LocDatum3a.hB_locR8_of_FMjet`, from the order-`8` jets of the far factor
  `(1 - χ(·/L))·F_*` — `Work.FTS_LocDatum3a.oneSubChi_jet_le8` and
  `Work.FTS_LocDatum3a.zfarR_jet_le8_of_jets`, with the profile bound taken as a hypothesis — and
  the bounded, compactly supported bump `bumpZ`);
* the **angular** bound `(D_θ^iΓ)² ≤ 10¹⁴·Γ²` for `i ≤ 8` (`hGam8` below, the square of
  `Work.FTS_LocDatum3a.DthIter_Gam_abs_le8`).

Both are integrated against the single majorant `K·angMaj α θ/(1+z)²`
(`Work.FTS.LocData.angMaj`), which is integrable on `[0,∞) × [0,π/2]` for `0 < α ≤ 1`
(`Work.FTS.LocData.integrableOn_angMaj_majorant`), giving `HkMem α 8 (locG6 α L β)` by
domination (`Work.FTS.LocData.HkMem_of_majorant`).  This is the order-`8` instance of the
chain that produced `Work.FTS.LocData6.HkMem_locG6`.

Everything rests on `[propext, Classical.choice, Quot.sound]` only.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS_LocDatum3a.DthIter_Gam_abs_le8
import Submission.Work.FTS_LocDatum3a.FM_jet8safe
import Submission.Work.FTS_LocDatum3a.hB_locR8_of_FMjet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## The angular jet bound at order `8` -/

/-- The squared angular jet bound `(D_θ^i Γ)² ≤ 10¹⁴·Γ²` on `Iθ`, for `i ≤ 8`, obtained by
squaring `|D_θ^i Γ| ≤ 10⁷·Γ` (`DthIter_Gam_abs_le8`). -/
theorem hGam8 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 8) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le8 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h14 : ((10000000 : ℝ)) ^ 2 = (10 : ℝ) ^ 14 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10000000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h14]

/-! ## The target -/

/-- **The localised order-`6` datum lies in `ℋ⁸`.**  For `0 < α ≤ 1`, `1 ≤ L` and every `β`,
`Work.Spaces.HkMem α 8 (locG6 α L β)`: the weighted `ℋ⁸`-integrand of the datum is dominated by
the integrable majorant `K·angMaj α θ/(1+z)²`.

This is the order-`8` companion of `Work.FTS.LocData6.HkMem_locG6` (and the `mem8` input of
`Work.FTS.StrongEps.softClass_Jeps` for the datum `locG6 α L β` of clause (3a′)). -/
theorem HkMem_locG8 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.Spaces.HkMem α 8 (Work.FTS.LocData6.locG6 α L β) := by
  obtain ⟨CF, hCF, hF⟩ := FM_jet8safe
  obtain ⟨R, hR0, hB⟩ := hB_locR8_of_FMjet α L β hα hα1 hL hCF hF
  have hΓ : ∀ i ≤ 8, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ') ^ 2 :=
    fun i hi θ' hθ' => hGam8 α hα hα1 hi hθ'
  -- the separability of the datum: `locG6 α L β = locR α L β(z)·Γ(θ)`
  have hloc : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ := by
    rw [Work.FTS.LocData6.locG6_eq]
    exact Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  -- joint continuity of the integrand on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 8 (Work.FTS.LocData6.locG6 α L β) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hsq : Work.FTS.LocData.SmoothQuad (Work.FTS.LocData6.locG6 α L β) := by
      rw [hloc]
      exact Work.FTS.LocDataExt.smoothQuad_sepGam
        (Work.FTS.LocDataExt.contDiffOn_locR α L β)
    exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 8 _ hsq
  -- membership by domination with the integrable majorant
  refine Work.FTS.LocData.HkMem_of_majorant (f := Work.FTS.LocData6.locG6 α L β)
    (M := fun z θ => (((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R
      * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 8 hcont ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      ((((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R)
      hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      ((((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R)
      hα hα1).2
  · -- the pointwise bound: the generic separable majorant at `k = 8`
    intro z hz θ hθ
    rw [hloc]
    exact Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 8
      (ρ := Work.FTS.LocDataExt.locR α L β) (R := R) (Rθ := (10 : ℝ) ^ 14)
      hR0 (by norm_num) hB hΓ hz hθ

end Work.FTS_LocDatum3a
