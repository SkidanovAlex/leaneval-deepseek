import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.NRow19T2Parts.Eta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- **The (γ)-family**: the weighted `∂_z^l D_θ^i`-bound for `Z₁₉`. -/
theorem Z19_gam_bound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    (hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs)) {C2 : ℝ}
    (hC2 : ∀ m j : ℕ, m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
      (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2)
    (hC2nn : 0 ≤ C2) :
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
        ≤ 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ) := by
  intro i l hi hli z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hl4 : l ≤ 4 := by omega
  have hi4 : i ≤ 4 := by omega
  have hKsm : Work.FTS.EllipticEst.SmoothOpen (K19 α Φs) := hAsm.mul smoothOpen_H2f
  have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
  have hPhi0 : 0 ≤ PhiAng α θ := PhiAng_nonneg hα hθI
  have hTB0 : 0 ≤ TB19 := TB19_nonneg
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hAraw : (1 + z) * Work.Spaces.w z * z ^ l = (1 + z) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  have hAraw0 : 0 ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 := by positivity
  have hwnn : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l := by
    rw [Work.Spaces.w]; positivity
  -- the Leibniz rule
  have hout := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
    (fun z θ => c19 α θ) (K19 α Φs) (smoothOpen_c19 α) hKsm z hz θ hθ
  have hout' : |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
            * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ| := by
    rw [show Z19 α Φs = (fun z θ => (fun z θ => c19 α θ) z θ * K19 α Φs z θ) from rfl]
    exact hout
  -- the `c19`-factor
  have hfac1 : ∀ c a : ℕ,
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ (if c = 0 then |Work.Spaces.dthU^[a] (c19 α) θ| else 0) := by
    intro c a
    rw [Work.FTS.NonlinRows.DthIter_theta_only (c19 α) a,
      Work.FTS.Nonlinear.Open.Row19Prep.pzIter_theta_only]
    simp only []
    by_cases hc0 : c = 0
    · rw [if_pos hc0, if_pos hc0]
    · rw [if_neg hc0, if_neg hc0, abs_zero]
  have hfac1w : ∀ c a : ℕ,
      (1 + z) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ| := by
    intro c a
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · subst hc0
      rw [pow_zero, one_mul]
      exact hfac1 0 a
    · have hle : |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ| ≤ 0 :=
        (hfac1 c a).trans (le_of_eq (by
          simp only [if_neg (Nat.pos_iff_ne_zero.mp hcpos)]))
      have hz0 : |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ| = 0 :=
        le_antisymm hle (abs_nonneg _)
      rw [hz0, mul_zero]
      exact abs_nonneg _
  -- the `K19`-factor
  have hfac2 : ∀ c a : ℕ, c ≤ l → a ≤ i →
      |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|
        ≤ 257 * ∑ c' ∈ Finset.range (l - c + 1),
            |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
              * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
    fun c a _ _ => K19_pz_Dth_le hAsm (by omega) (by omega) z hz θ hθ
  -- the angular-jet bounds
  have hdth : ∀ a : ℕ, a ≤ 4 →
      |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * (1 + TB19) * Work.Spaces.Gam α θ := by
    intro a ha
    have h1 := dthU_c19_le_MGa hα hα1 ha θ hθI
    have h2 := MGa_le hα.le hα1 a
    have hG := Gam_nonneg' hα hθI
    calc |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * MGa α a * Work.Spaces.Gam α θ := h1
      _ ≤ 10 * α * (1 + TB19) * Work.Spaces.Gam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hG
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hkey : ∀ a : ℕ, a ≤ i →
      |Work.Spaces.dthU^[a] (c19 α) θ| * Psi19 α (i - a) θ
        ≤ 10 * α * (1 + TB19) * PhiAng α θ := by
    intro a hai
    by_cases hia : i - a = 0
    · have haei : a = i := by omega
      have h1 := dthU_c19_le_MGa hα hα1 (show i ≤ 4 by omega) θ hθI
      have h2 : MGa α i = α * TB19 := by
        rw [MGa, if_neg (by omega : i ≠ 0)]
      have h3 : α * Work.Spaces.Gam α θ ≤ PhiAng α θ := alpha_Gam_le_PhiAng hα hθI
      have hG := Gam_nonneg' hα hθI
      rw [Psi19, if_pos hia, mul_one, haei]
      calc |Work.Spaces.dthU^[i] (c19 α) θ| ≤ 10 * α * MGa α i * Work.Spaces.Gam α θ := h1
        _ = 10 * α * TB19 * (α * Work.Spaces.Gam α θ) := by rw [h2]; ring
        _ ≤ 10 * α * TB19 * PhiAng α θ := by
            refine mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ 10 * α * (1 + TB19) * PhiAng α θ := by nlinarith [hTB0, hPhi0, hα]
    · rw [Psi19, if_neg hia]
      have h1 := hdth a (by omega)
      have hG := Gam_le_one' hα hθI
      calc |Work.Spaces.dthU^[a] (c19 α) θ| * PhiAng α θ
          ≤ (10 * α * (1 + TB19) * Work.Spaces.Gam α θ) * PhiAng α θ :=
            mul_le_mul_of_nonneg_right h1 hPhi0
        _ ≤ (10 * α * (1 + TB19) * 1) * PhiAng α θ := by
            refine mul_le_mul_of_nonneg_right ?_ hPhi0
            exact mul_le_mul_of_nonneg_left hG (by positivity)
        _ = 10 * α * (1 + TB19) * PhiAng α θ := by ring
  have hK0 : 0 ≤ (10 * α * (1 + TB19) * PhiAng α θ)
      * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2) :=
    mul_nonneg (by positivity) (mul_nonneg hL0 hC2nn)
  -- the per-term bound
  have hmul : ∀ c a : ℕ, c ≤ l → a ≤ i →
      (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        ≤ (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
    intro c a hcl hai
    have hX : (1 + z) ^ c
        * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ| := hfac1w c a
    have hsplit1 : (1 + z) ^ 3 * z ^ l / z ^ 2
        = (1 + z) ^ c * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c) := by
      have hp : (0 : ℝ) < (1 + z) ^ c := pow_pos hz1 _
      exact (mul_div_cancel₀ _ (ne_of_gt hp)).symm
    have hstep1 : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        = ((1 + z) ^ c
              * |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|) := by
      nth_rewrite 1 [hsplit1]
      ring
    rw [hstep1]
    have hcw : 0 ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c := by positivity
    have hY := hfac2 c a hcl hai
    have hYw : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
          * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|
        ≤ 257 * ∑ c' ∈ Finset.range (l - c + 1),
            ((1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by
      have hmul' := mul_le_mul_of_nonneg_left hY hcw
      refine hmul'.trans (le_of_eq ?_)
      have h1 : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
            * (257 * ∑ c' ∈ Finset.range (l - c + 1),
                |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
          = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
              * ∑ c' ∈ Finset.range (l - c + 1),
                |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by ring
      rw [h1, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      have hsp : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
          = (1 + z) ^ c'
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')) := by
        have h1 : (1 + z) ^ (c + c') = (1 + z) ^ c * (1 + z) ^ c' := pow_add _ _ _
        rw [h1, mul_div_assoc']
        rw [show (1 + z) ^ c' * ((1 + z) ^ 3 * z ^ l / z ^ 2)
              / ((1 + z) ^ c * (1 + z) ^ c')
            = ((1 + z) ^ 3 * z ^ l / z ^ 2) * (1 + z) ^ c'
              / ((1 + z) ^ c * (1 + z) ^ c') from by ring]
        rw [mul_div_mul_right]
        exact ne_of_gt (pow_pos hz1 c')
      rw [hsp]
      ring
    refine (mul_le_mul hX hYw (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)).trans ?_
    -- now bound `|dthU^a c19| * 257 * Σ_{c'} ((1+z)^{c'}|Y'|)*((A/(1+z)^{c+c'})|Z|)`
    have hsum2 : (∑ c' ∈ Finset.range (l - c + 1),
          ((1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ (((l - c + 1 : ℕ)) : ℝ)
            * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2) := by
      have h1 : ∀ c' ∈ Finset.range (l - c + 1),
          ((1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
            * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
          ≤ (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 := by
        intro c' hc'
        rw [Finset.mem_range] at hc'
        have hc'0 : (0 : ℝ) ≤ (1 + z) ^ c' := by positivity
        have hY'' := Work.Spaces.factor_bound α hα (A19 α Φs) hAmem c' (i - a)
          (by omega) (fun _ => by omega) z θ hzI hθI
        have hYabs : |(z + 1) ^ c' * Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
            = (1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ| := by
          rw [show (z : ℝ) + 1 = 1 + z by ring, abs_mul, abs_of_nonneg hc'0]
        rw [hYabs] at hY''
        have hY''' : (1 + z) ^ c'
              * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|
            ≤ Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ := by
          simpa only [Psi19, PhiAng] using hY''
        have hZ := hC2 l (l - c - c') hl4 (by omega) z hz
        have hlc : l - (l - c - c') = c + c' := by omega
        rw [hlc] at hZ
        have hZ' : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
            * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2 := by
          rwa [← hAraw]
        exact mul_le_mul hY''' hZ' (mul_nonneg (by positivity) (abs_nonneg _))
          (mul_nonneg hL0 (Psi19_nonneg hα hθI))
      calc (∑ c' ∈ Finset.range (l - c + 1),
            ((1 + z) ^ c'
                * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
              * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                  * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
          ≤ ∑ _c' ∈ Finset.range (l - c + 1),
              (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 :=
            Finset.sum_le_sum h1
        _ = (((l - c + 1 : ℕ)) : ℝ)
              * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc |Work.Spaces.dthU^[a] (c19 α) θ|
          * (257 * ∑ c' ∈ Finset.range (l - c + 1),
              ((1 + z) ^ c'
                  * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) (A19 α Φs)) z θ|)
                * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                    * |deriv^[l - c - c'] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ |Work.Spaces.dthU^[a] (c19 α) θ|
            * (257 * ((((l - c + 1 : ℕ)) : ℝ)
                * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum2 (by norm_num)) (abs_nonneg _)
      _ ≤ |Work.Spaces.dthU^[a] (c19 α) θ|
            * (257 * (5 * ((Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2))) := by
          have hc : 0 ≤ (Work.Spaces.WlInf α 4 (A19 α Φs) * Psi19 α (i - a) θ) * C2 :=
            mul_nonneg (mul_nonneg hL0 (Psi19_nonneg hα hθI)) hC2nn
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ hc
          have : l - c + 1 ≤ 5 := by omega
          exact_mod_cast this
      _ = (|Work.Spaces.dthU^[a] (c19 α) θ| * Psi19 α (i - a) θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by ring
      _ ≤ (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
          have hc : 0 ≤ 257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)) := by positivity
          exact mul_le_mul_of_nonneg_right (hkey a hai) hc
  -- the sum bounds
  have hsumAB : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
      ≤ 125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))) := by
    have hK1 : 0 ≤ (10 * α * (1 + TB19) * PhiAng α θ)
        * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by positivity
    have hstep : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
        ≤ ∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
            (10 * α * (1 + TB19) * PhiAng α θ)
              * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))) := by
      refine Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => ?_
      rw [Finset.mem_range] at hc ha
      exact hmul c a (by omega) (by omega)
    refine hstep.trans ?_
    · have h2 : (∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
          (10 * α * (1 + TB19) * PhiAng α θ)
            * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))))
          = (((l + 1) * (i + 1) : ℕ) : ℝ)
            * ((10 * α * (1 + TB19) * PhiAng α θ)
              * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))) := by
        rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [h2]
      refine mul_le_mul_of_nonneg_right ?_ hK1
      have h1 : ((l + 1) * (i + 1) : ℕ) ≤ 25 := by
        have a1 : l + 1 ≤ 5 := by omega
        have a2 : i + 1 ≤ 5 := by omega
        calc (l + 1) * (i + 1) ≤ 5 * 5 := Nat.mul_le_mul a1 a2
          _ = 25 := rfl
      have h2' : (((l + 1) * (i + 1) : ℕ) : ℝ) ≤ 25 := by exact_mod_cast h1
      linarith
  -- assembly
  have h1 : |(1 + z) * Work.Spaces.w z * z ^ l
        * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      = (1 + z) ^ 3 * z ^ l / z ^ 2
          * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ| := by
    rw [hAraw, abs_mul, abs_of_nonneg hAraw0]
  rw [h1]
  have h2 : (1 + z) ^ 3 * z ^ l / z ^ 2
        * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (Z19 α Φs)) z θ|
      ≤ 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)) := by
    have hs := mul_le_mul_of_nonneg_left hout' hAraw0
    have he : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
        = 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) ^ 3 * z ^ l / z ^ 2
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)) := by
      rw [show (1 + z) ^ 3 * z ^ l / z ^ 2
            * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
          = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2
              * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|)
          from by ring]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
    rw [he] at hs
    exact hs
  refine h2.trans ?_
  have h3 : (257 : ℝ) * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ => c19 α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (K19 α Φs)) z θ|))
      ≤ 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))))) :=
    mul_le_mul_of_nonneg_left hsumAB (by norm_num)
  refine h3.trans ?_
  have h4 : 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
        * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))))
      ≤ 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ) := by
    have hcoef : 257 * (125 * (10 * (1 + TB19) * (257 * 5 * C2)))
        ≤ 200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)) := by
      nlinarith [hC2nn, hTB0]
    have hcoef2 : 257 * (125 * ((10 * α * (1 + TB19) * PhiAng α θ)
          * (257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2)))))
        = (257 * (125 * (10 * (1 + TB19) * (257 * 5 * C2))))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs) * PhiAng α θ) := by ring
    have hcoef3 : 200000 * ((CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) * PhiAng α θ)
        = (200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs) * PhiAng α θ) := by
      rw [CZ19]; ring
    rw [hcoef2, hcoef3]
    exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg (mul_nonneg hα.le hL0) hPhi0)
  exact h4

end Work.FTS.NonlinRows
