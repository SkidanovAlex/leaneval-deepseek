/-
# `E1Norm/Main` — the `ℋⁿ`-bound for the transfer defect `E1 α f`

The transfer defect of `Transfer/Profiles.lean` is the separated product

  `E1 α f = (D_θΓ) · radA α f`,   `radA α f z = -(ampA α z)L₁₂ f(z) + (ampB α z/c(α))C₀ f`

of the angular profile `a = D_θΓ` and a *radial* profile.  This file assembles the estimate

  `|E1 α f|²_{ℋⁿ} ≤ C·α²·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`   (`0 < α ≤ 1`, `n ≤ 3`),

with `C` independent of `α`, `n` and `f`, from two independent halves:

* `E1Norm.E1_angRad_le` — the **angular** half: the separated-product bound
  `|E1 α f|²_{ℋⁿ} ≤ C·α²·∫_z ∑_{j≤n}(D_z^j(radA α f))²w²`, proved from the pointwise angular data
  `|D_θΓ| ≤ K₁αΓ`, `|D_θ^i(D_θΓ)| ≤ K₂αΓ(sin²2θ+α)` (`E1Norm/Lop_iter_LopGam_Gamma_bound`,
  `E1Norm/Lop_iter_LopGam_gauge_bound`) and the gauge mass bound
  `∫_θ (Γ(sin²2θ+α))²sin(2θ)^{-γ} ≤ 1000` (`E1Norm/GaugeMass.gauge_mass`);
* `E1Norm.radA_sum_le` — the **radial** half:
  `∫_z ∑_{j≤n}(D_z^j(radA α f))²w² ≤ C·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`, proved from the Hardy
  inequality for `L₁₂`, the level-`n` angular-moment bounds `E1Norm.Qang_sq_w_sq_le_HkSq`, the
  bound `(C₀ f)² ≤ 64|f|²_{ℋⁿ}` (`E1Norm.C0_sq_le_HkSq`) and the explicit-profile bounds
  `E1Norm.amp_iter_bounds` and `E1Norm.ampA_uniform_bound`.

The `α²` is exactly the `α`-smallness of `D_θΓ`; the mixed slots cost `(K₂α)²·1000` and the pure
slots `(K₁α)²·10⁴`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Radial
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Qang_sq_w_sq_le_HkSq
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.C0_sq_le_HkSq
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.amp_iter_bounds
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.E1_angRad_le
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadA
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two elementary inputs -/

/-- **A uniform bound on the `D_z`-iterates of `ampA β`** (`β`-independent, unlike
`E2pkg.ampA_dzdIter_bound` whose constant is existentially quantified for each `β`). -/
theorem ampA_uniform_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ b : ℕ, b ≤ 4 →
      ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Elliptic.DzdIter b (ampA β) z| ≤ K := by
  obtain ⟨K₀, hK₀, hbd⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 4
  refine ⟨20 * K₀ + 1, by linarith, ?_⟩
  intro β hβ hβ1 b hb z hz
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c β := (Work.Spaces.c_bounds β hβ hβ1).1
  have hcpos : 0 < Work.Spaces.c β := by linarith
  have h2c : 2 / Work.Spaces.c β ≤ 20 := by
    rw [div_le_iff₀ hcpos]; linarith
  have hb' : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ := hbd b hb z hz
  calc |Work.Elliptic.DzdIter b (ampA β) z|
      = |Work.Spaces.Zop^[b] (ampA β) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[b] (fun z : ℝ => (2 / Work.Spaces.c β) * (z / (1 + z) ^ 2)) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c β)
          * Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
    _ = |2 / Work.Spaces.c β| * |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| :=
        abs_mul _ _
    _ = (2 / Work.Spaces.c β) * |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c β) * K₀ := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ ≤ 20 * K₀ + 1 := by
        have h := mul_le_mul_of_nonneg_right h2c hK₀
        linarith

/-- **`ℋⁿ`-membership from the coercivity class.**  `CoerAdm α f` gives `ℋ⁵`-membership, and
`ℋᵏ`-membership is monotone in `k` in the interior class. -/
theorem HkMem_of_coerAdm (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hn : n ≤ 5) : Work.Spaces.HkMem α n f := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have h5 : Work.Spaces.HkMem α 5 f := hf.reg.2.1
  have aux : ∀ m : ℕ, Work.Spaces.HkMem α (n + m) f → Work.Spaces.HkMem α n f := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ k ih =>
        intro h
        refine ih (Work.GalerkinFix.RegQ.HkMem_mono_Q (k := n + k) hsm ?_)
        simpa only [Nat.add_succ] using h
  exact aux (5 - n) (by rw [Nat.add_sub_of_le hn]; exact h5)

/-- The radial square sum `∑_{j≤n}(D_z^j(radA α f))²w²` is integrable for `f ∈ CoerAdm α`. -/
theorem radSum_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) :
    MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
  MeasureTheory.integrable_finsetSum _ (fun j hj =>
    Work.FTS.CoercivityFix.Transfer.E1Parts.RadA α hα hα1 f hf j (by
      have := Finset.mem_range.mp hj; omega))

/-! ## The squared `ℋⁿ`-bound for `E1` -/

/-- **The `ℋⁿ`-bound for the transfer defect, squared form.**  For `0 < α ≤ 1`, `n ≤ 3` and
`f ∈ CoerAdm α` with `HkMem α n f`,

  `|E1 α f|²_{ℋⁿ} ≤ C·α²·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`. -/
theorem E1_hkSq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → n ≤ 3 →
      Work.FTS.Nonlin.CoerAdm α f → Work.Spaces.HkMem α n f →
      Work.Spaces.HkSq α n (E1 α f)
        ≤ C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cang, hCangpos, hCang⟩ := E1_angRad_le
  obtain ⟨Kb, hKbpos, hKb⟩ := amp_iter_bounds
  obtain ⟨KA, hKApos, hKA⟩ := ampA_uniform_bound
  have hKth : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  obtain ⟨Crad, hCradpos, hCrad⟩ := radA_sum_le (CQ := ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ ^ 2) (CC := 64) (Kb := Kb) (K := KA) hKth
      (by norm_num) hKbpos hKApos.le
    (fun β m g hβ hβ1 hsm hmem i hi => Qang_sq_w_sq_le_HkSq m β g hβ hβ1 hsm hmem i hi)
    (fun β m g hβ hβ1 hg hmem => C0_sq_le_HkSq β hβ hβ1 m hg hmem)
    (fun β hβ hβ1 => hKb β hβ hβ1)
    (fun β hβ hβ1 b hb z hz => hKA β hβ hβ1 b hb z hz)
  refine ⟨Cang * Crad + 1, by positivity, ?_⟩
  intro α n f hα hα1 hn hf hmem
  have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  have h1 := hCang α n f hα hα1 hn (radSum_integrable α hα hα1 n hn hf)
  have h2 := (hCrad α n f hα hα1 hn hf hmem).2
  have h3 : (0 : ℝ) ≤ Cang * α ^ 2 := by positivity
  have h5 : (0 : ℝ) ≤ α ^ 2
      * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  calc Work.Spaces.HkSq α n (E1 α f)
      ≤ Cang * α ^ 2 * (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (radA α f) z) ^ 2 * (Work.Spaces.w z) ^ 2) := h1
    _ ≤ Cang * α ^ 2 * (Crad * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = (Cang * Crad) * α ^ 2
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
    _ ≤ (Cang * Crad + 1) * α ^ 2
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
        rw [show (Cang * Crad) * α ^ 2
              * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Cang * Crad) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring,
          show (Cang * Crad + 1) * α ^ 2
              * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
            = (Cang * Crad + 1) * (α ^ 2 * (Work.Spaces.HkSq α n f
              + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) from by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) h5

end Work.FTS.CoercivityFix.Transfer.E1Norm
