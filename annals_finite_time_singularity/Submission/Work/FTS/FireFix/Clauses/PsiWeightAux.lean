import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Clauses.PsiWt.aesm_pth_abs
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_sin_rpow_mul_cos_rpow
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_cos_sq_sin_rpow
import Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_indic_Iic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FireFix.Clauses.PsiWeightAux`

The vocabulary and the two analytic pointwise lemmas underlying
`Work.FTS.FireFix.Clauses.integrableOn_psi_weight`:

* `psiWq1` .. `psiWq4` -- the four summands of the majorant (`1_{q.1 <= L}`, `sin^{a-1}cos^{2a}`,
  `(D_theta g)^2 sin(2theta)^{-gamma}`, `cos^2 theta sin(2theta)^{gamma-2}`);
* `psiWinner`, `psiWmaj`, `psiWpsi` -- the inner bracket, the majorant and the goal integrand;
* `psiMeasurableRpowConst` -- `x |-> x^r` is measurable for every real `r`;
* `psiIntegrableOnConstMul` -- `IntegrableOn` is stable under left multiplication by a constant;
* `psiTwoMulSqrtLe` -- the AM-GM inequality `2 sqrt a sqrt b <= a + b`;
* `psiWmajNonneg` -- the majorant is nonnegative on the strip;
* `psiWpsiLeWmaj` -- the pointwise bound `|psiWpsi q| <= psiWmaj q` on the strip off `q.2 = 0`.

The proof of `psiWpsiLeWmaj` is an explicit case analysis on `q.1 <= L` with the rpow bookkeeping
`(b q.1)^s q.1^{1/a-1} = b^s q.1^{2/(3a)-1}` etc.; the `|d_theta g|` block is closed by AM-GM
`2 sqrt(A^2 s2^{-g}) sqrt(c^2 s2^{g-2}) <= A^2 s2^{-g} + c^2 s2^{g-2}`.
-/

open MeasureTheory Set Filter Topology

namespace Work.FTS.FireFix.Clauses

set_option maxHeartbeats 1000000


/-- The `(q.1 ≤ L)` cutoff. -/
noncomputable def psiWq1 (L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => if q.1 ≤ L then (1 : ℝ) else 0

/-- The angular `sin^{α-1}cos^{2α}` piece. -/
noncomputable def psiWq2 (α L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α) * psiWq1 L q

/-- The `(D_θg)² sin(2θ)^{-γ}` piece. -/
noncomputable def psiWq3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Work.Spaces.Dth f q.1 (abs q.2)) ^ 2
    * (Real.sin (2 * abs q.2)) ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α)))

/-- The `cos²θ sin(2θ)^{γ-2}` piece. -/
noncomputable def psiWq4 (γ L : ℝ) : ℝ × ℝ → ℝ :=
  fun q => (Real.cos q.2) ^ 2 * (Real.sin (2 * abs q.2)) ^ (γ - 2) * psiWq1 L q

/-- The inner bracket of the goal integrand. -/
noncomputable def psiWinner (α Ca Cb Cc : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q => Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
    + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
    + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α - 1)
        + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
      / ((B τ * q.1) ^ (1 / (3 * α)))

/-- The majorant. -/
noncomputable def psiWmaj (α Ca Cb Cc L : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q =>
    (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
        + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q
      + Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          * psiWq2 α L q
      + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q
      + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q

/-- The goal integrand. -/
noncomputable def psiWpsi (α Ca Cb Cc L : ℝ) (B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ)
    (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun q : ℝ × ℝ =>
    (if q.1 ≤ L then psiWinner α Ca Cb Cc B g τ q else 0) * q.1 ^ (1 / α - 1) * Real.cos q.2

/-- `x ↦ x^r` is measurable for every real `r`. -/
theorem psiMeasurableRpowConst (r : ℝ) : Measurable (fun x : ℝ => x ^ r) := by
  by_cases hr : 0 ≤ r
  · exact (Real.continuous_rpow_const hr).measurable
  · push_neg at hr
    have hcomp : (fun x : ℝ => x ^ r) = (fun y : ℝ => y ^ (-r)) ∘ (fun x : ℝ => x⁻¹) := by
      funext x
      have hx : x ^ r = x⁻¹ ^ (-r) := by
        conv_lhs => rw [show r = -(-r) from by ring]
        rw [Real.rpow_neg_eq_inv_rpow]
      simpa [Function.comp_apply] using hx
    rw [hcomp]
    exact ((Real.continuous_rpow_const (by linarith)).measurable).comp measurable_inv

theorem psiIntegrableOnConstMul {c : ℝ} {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : MeasureTheory.IntegrableOn f s) :
    MeasureTheory.IntegrableOn (fun q => c * f q) s := by
  change MeasureTheory.Integrable (fun q => c * f q) (MeasureTheory.volume.restrict s)
  change MeasureTheory.Integrable f (MeasureTheory.volume.restrict s) at hf
  exact hf.const_mul c

/-- `2 √a √b ≤ a + b`. -/
theorem psiTwoMulSqrtLe {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- Nonnegativity of the majorant on the strip. -/
theorem psiWmajNonneg {α Ca Cb Cc L : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hb : 0 < B τ) (hL : 0 ≤ L)
    {q : ℝ × ℝ} (hq : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ psiWmaj α Ca Cb Cc L B g τ q := by
  have hcos : 0 ≤ Real.cos q.2 := le_of_lt (Real.cos_pos_of_mem_Ioo hq)
  have habs : |q.2| < Real.pi / 2 := abs_lt.mpr hq
  have hsin2 : 0 ≤ Real.sin (2 * |q.2|) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    linarith [Real.pi_pos]
  have hsina : 0 ≤ Real.sin |q.2| :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  have h1 : 0 ≤ psiWq1 L q := by simp only [psiWq1]; split <;> norm_num
  have h2 : 0 ≤ psiWq2 α L q := by
    simp only [psiWq2]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hsina _)
      (Real.rpow_nonneg hcos _)) h1
  have h4 : 0 ≤ psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q := by
    simp only [psiWq4]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin2 _)) h1
  have h3 : 0 ≤ psiWq3 α (Work.FTS.Regularity.gSlice g τ) q := by
    simp only [psiWq3]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin2 _)
  have hb1 : 0 ≤ (B τ) ^ (- (1 / (3 * α))) := Real.rpow_nonneg hb.le _
  have hm1 : 0 ≤ L ^ (2 / (3 * α) - 1) := Real.rpow_nonneg hL _
  have hm2 : 0 ≤ L ^ (2 / (3 * α)) := Real.rpow_nonneg hL _
  have hb2 : 0 ≤ (B τ) ^ (1 - 1 / (3 * α)) := Real.rpow_nonneg hb.le _
  unfold psiWmaj
  have e1 : 0 ≤ (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
      + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α)))) * psiWq1 L q :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hCa hb1) hm1)
      (mul_nonneg (mul_nonneg hCb hb2) hm2)) h1
  have e2 : 0 ≤ Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
      * psiWq2 α L q :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (by norm_num))
      (sq_nonneg α)) hb1) hm1) h2
  have e3 : 0 ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
      * psiWq3 α (Work.FTS.Regularity.gSlice g τ) q :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCc hb1) hm1) (by norm_num)) h3
  have e4 : 0 ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
      * psiWq4 (Work.Spaces.gam (Work.FTS.Regularity.pExp α)) L q :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hCc hb1) hm1) (by norm_num)) h4
  linarith

/-- The pointwise bound. -/
theorem psiWpsiLeWmaj {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {Ca Cb Cc L : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hL : 0 ≤ L)
    {q : ℝ × ℝ} (hq1 : 0 < q.1)
    (hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hq0 : q.2 ≠ 0) :
    ‖psiWpsi α Ca Cb Cc L B g τ q‖ ≤ psiWmaj α Ca Cb Cc L B g τ q := by
  have hα : 0 < α := h.hα
  have hb : 0 < B τ := h.hB τ hτ
  have hcos : 0 < Real.cos q.2 := Real.cos_pos_of_mem_Ioo hq2
  have hcosne : Real.cos q.2 ≠ 0 := ne_of_gt hcos
  have hcosle : Real.cos q.2 ≤ 1 := Real.cos_le_one _
  have habsx : |q.2| < Real.pi / 2 := abs_lt.mpr hq2
  have hsin2pos : 0 < Real.sin (2 * |q.2|) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    linarith [Real.pi_pos]
  have h3a : (3 : ℝ) * α ≠ 0 := by positivity
  have hαne : α ≠ 0 := ne_of_gt hα
  have hsina : 0 ≤ Real.sin |q.2| :=
    Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  have hA1 : (1 : ℝ) / α = 3 / (3 * α) := by
    rw [div_eq_div_iff hαne h3a]; ring
  have hkey1 : 1 / α - 1 + (- (1 / (3 * α))) = 2 / (3 * α) - 1 := by
    have h3 : (3 : ℝ) / (3 * α) - 1 / (3 * α) = 2 / (3 * α) := by
      rw [div_sub_div_same]; norm_num
    rw [hA1]; linarith
  have hkey2 : 1 - 1 / (3 * α) + (1 / α - 1) = 2 / (3 * α) := by
    have h3 : (3 : ℝ) / (3 * α) - 1 / (3 * α) = 2 / (3 * α) := by
      rw [div_sub_div_same]; norm_num
    rw [hA1]; linarith
  have hkey3 : (3 * α - 1) / (3 * α) = 1 - 1 / (3 * α) := by
    rw [← div_sub_div_same, div_self h3a]
  have hexp1 : (0 : ℝ) ≤ 2 / (3 * α) - 1 := by
    rw [sub_nonneg, one_le_div (by positivity : (0 : ℝ) < 3 * α)]; linarith [h.hα13]
  by_cases hLq : q.1 ≤ L
  · have hqL : q.1 ≤ L := hLq
    have hXpos : 0 < (B τ * q.1) ^ (1 / (3 * α)) :=
      Real.rpow_pos_of_pos (mul_pos hb hq1) _
    have hYnn : 0 ≤ (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) :=
      Real.rpow_nonneg (mul_nonneg hb.le hq1.le) _
    have hZnn : 0 ≤ q.1 ^ (1 / α - 1) := Real.rpow_nonneg hq1.le _
    have hsann : 0 ≤ (Real.sin (abs q.2)) ^ (α - 1) := Real.rpow_nonneg hsina _
    have hc2nn : 0 ≤ (Real.cos q.2) ^ (2 * α - 1) := Real.rpow_nonneg hcos.le _
    have hWnn : 0 ≤ (Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (Real.cos q.2) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α)))) * q.1 ^ (1 / α - 1) * Real.cos q.2 := by
      have h1 : 0 ≤ Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2) :=
        div_nonneg hCa (le_of_lt (mul_pos hXpos hcos))
      have h2 : 0 ≤ Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) := mul_nonneg hCb hYnn
      have h3 : 0 ≤ Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
          * (Real.cos q.2) ^ (2 * α - 1)
          + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|)
          / ((B τ * q.1) ^ (1 / (3 * α))) :=
        div_nonneg (mul_nonneg hCc (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 200) (sq_nonneg α))
            hsann) hc2nn) (abs_nonneg _))) hXpos.le
      exact mul_nonneg (mul_nonneg (add_nonneg (add_nonneg h1 h2) h3) hZnn) hcos.le
    have hcancel : ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * Real.cos q.2
        = ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ := by
      rw [mul_inv, show ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ * (Real.cos q.2)⁻¹ * Real.cos q.2
        = ((B τ * q.1) ^ (1 / (3 * α)))⁻¹ * ((Real.cos q.2)⁻¹ * Real.cos q.2) from by ring,
        inv_mul_cancel₀ hcosne, mul_one]
    have hZinv : ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        = (B τ) ^ (- (1 / (3 * α))) * q.1 ^ (- (1 / (3 * α))) := by
      rw [← Real.rpow_neg (mul_nonneg hb.le hq1.le), Real.mul_rpow hb.le hq1.le]
    have hZmul : q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        = (B τ) ^ (- (1 / (3 * α))) * q.1 ^ (2 / (3 * α) - 1) := by
      rw [hZinv,
        show q.1 ^ (1 / α - 1) * ((B τ) ^ (- (1 / (3 * α))) * q.1 ^ (- (1 / (3 * α))))
          = (B τ) ^ (- (1 / (3 * α))) * (q.1 ^ (1 / α - 1) * q.1 ^ (- (1 / (3 * α)))) from by
            ring,
        ← Real.rpow_add hq1, hkey1]
    have hZmul3 : q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹
        ≤ (B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1) := by
      rw [hZmul]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq1.le hqL hexp1)
        (Real.rpow_nonneg hb.le _)
    have hZmul2 : (B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)
        = (B τ) ^ (1 - 1 / (3 * α)) * q.1 ^ (2 / (3 * α)) := by
      rw [Real.mul_rpow hb.le hq1.le,
        show (B τ ^ (1 - 1 / (3 * α)) * q.1 ^ (1 - 1 / (3 * α))) * q.1 ^ (1 / α - 1)
          = (B τ) ^ (1 - 1 / (3 * α)) * (q.1 ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) from by
            ring,
        ← Real.rpow_add hq1, hkey2]
    have hZmul4 : (B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)
        ≤ (B τ) ^ (1 - 1 / (3 * α)) * L ^ (2 / (3 * α)) := by
      rw [hZmul2]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq1.le hqL (by positivity))
        (Real.rpow_nonneg hb.le _)
    have hterm1 : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) := by
      have heq : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Ca * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹) := by
        rw [div_eq_mul_inv,
          show Ca * ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * q.1 ^ (1 / α - 1)
            * Real.cos q.2
            = Ca * (((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)⁻¹ * Real.cos q.2)
              * q.1 ^ (1 / α - 1) from by ring,
          hcancel]
        ring
      rw [heq]
      calc Ca * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
          ≤ Ca * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
            mul_le_mul_of_nonneg_left hZmul3 hCa
        _ = Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) := by ring
    have hterm2 : Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))) := by
      have heq : Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α))
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * Real.cos q.2 := by
        rw [hkey3]; ring
      rw [heq]
      have hYnn2 : 0 ≤ (B τ * q.1) ^ (1 - 1 / (3 * α)) :=
        Real.rpow_nonneg (mul_nonneg hb.le hq1.le) _
      have hb2 : 0 ≤ Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) :=
        mul_nonneg hCb (mul_nonneg hYnn2 hZnn)
      calc Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * Real.cos q.2
          ≤ Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) * 1 :=
            mul_le_mul_of_nonneg_left hcosle hb2
        _ = Cb * ((B τ * q.1) ^ (1 - 1 / (3 * α)) * q.1 ^ (1 / α - 1)) := by ring
        _ ≤ Cb * ((B τ) ^ (1 - 1 / (3 * α)) * L ^ (2 / (3 * α))) :=
            mul_le_mul_of_nonneg_left hZmul4 hCb
        _ = Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))) := by ring
    have hterm3 : Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
          * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
        * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
          * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)) := by
      have hcpow : (Real.cos q.2) ^ (2 * α - 1) * Real.cos q.2
          = (Real.cos q.2) ^ (2 * α) := by
        have h := Real.rpow_add hcos (2 * α - 1) 1
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        ring
      have heq : Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
          * q.1 ^ (1 / α - 1) * Real.cos q.2
          = Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * ((Real.cos q.2) ^ (2 * α - 1) * Real.cos q.2) := by
        rw [div_eq_mul_inv]; ring
      rw [heq, hcpow]
      have hc2nn2 : 0 ≤ (Real.cos q.2) ^ (2 * α) := Real.rpow_nonneg hcos.le _
      have hstep : Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (Real.cos q.2) ^ (2 * α)
          ≤ Cc * 200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
            * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1))
            * (Real.cos q.2) ^ (2 * α) := by
        refine mul_le_mul_of_nonneg_right ?_ hc2nn2
        exact mul_le_mul_of_nonneg_left hZmul3
          (mul_nonneg (mul_nonneg (mul_nonneg hCc (by norm_num)) (sq_nonneg α)) hsann)
      calc _ ≤ _ := hstep
        _ = Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
              * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)) := by ring
    have hterm4 : Cc * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|
          / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
          * ((Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)) ^ 2
              * (Real.sin (2 * abs q.2))
                  ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α)))
            + (Real.cos q.2) ^ 2
              * (Real.sin (2 * abs q.2))
                  ^ (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 2)) := by
      set P := Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2) with hP
      set D := Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2) with hD
      set s2 := Real.sin (2 * abs q.2) with hs2
      set gc := Work.Spaces.gam (Work.FTS.Regularity.pExp α) with hgc
      have hDdef : D = s2 * P := by rw [hD, hs2, hP]; rfl
      have hs2pos : 0 < s2 := by rw [hs2]; exact hsin2pos
      have hD2 : D ^ 2 = s2 ^ (2 : ℝ) * P ^ 2 := by
        rw [hDdef, mul_pow, Real.rpow_two]
      have hA3 : D ^ 2 * s2 ^ (- gc) = P ^ 2 * s2 ^ (2 - gc) := by
        have e1 : s2 ^ (2 : ℝ) * s2 ^ (- gc) = s2 ^ ((2 : ℝ) - gc) := by
          rw [← Real.rpow_add hs2pos (x := s2) (y := (2 : ℝ)) (z := -gc),
            show (2 : ℝ) + -gc = 2 - gc from by ring]
        rw [hD2,
          show s2 ^ (2 : ℝ) * P ^ 2 * s2 ^ (- gc)
            = P ^ 2 * (s2 ^ (2 : ℝ) * s2 ^ (- gc)) from by ring, e1]
      have hW3 : (0:ℝ) ≤ D ^ 2 * s2 ^ (- gc) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs2pos.le _)
      have hW4 : (0:ℝ) ≤ (Real.cos q.2) ^ 2 * s2 ^ (gc - 2) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs2pos.le _)
      have hprod : D ^ 2 * s2 ^ (- gc) * ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
          = (|P| * Real.cos q.2) ^ 2 := by
        have e2 : s2 ^ (2 - gc) * s2 ^ (gc - 2) = 1 := by
          rw [← Real.rpow_add hs2pos (x := s2) (y := 2 - gc) (z := gc - 2)]
          rw [show 2 - gc + (gc - 2) = 0 from by ring, Real.rpow_zero]
        rw [hA3,
          show P ^ 2 * s2 ^ (2 - gc) * ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
            = P ^ 2 * (Real.cos q.2) ^ 2 * (s2 ^ (2 - gc) * s2 ^ (gc - 2)) from by ring,
          e2, mul_one,
          show (|P| * Real.cos q.2) ^ 2 = P ^ 2 * (Real.cos q.2) ^ 2 from by
            rw [mul_pow, sq_abs]]
      have hsqrt : Real.sqrt (D ^ 2 * s2 ^ (- gc))
            * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))
          = |P| * Real.cos q.2 := by
        rw [← Real.sqrt_mul hW3, hprod, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mul_nonneg (abs_nonneg _) hcos.le)]
      have heq : Cc * |P| / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1)
            * Real.cos q.2
          = Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (|P| * Real.cos q.2) := by
        rw [div_eq_mul_inv]; ring
      rw [heq, ← hsqrt]
      have hbnd : Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
          ≤ Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
        mul_le_mul_of_nonneg_left hZmul3 hCc
      have hsnn : 0 ≤ Real.sqrt (D ^ 2 * s2 ^ (- gc))
          * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hconstnn : 0 ≤ Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)) :=
        mul_nonneg hCc (mul_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hL _))
      calc Cc * (q.1 ^ (1 / α - 1) * ((B τ * q.1) ^ (1 / (3 * α)))⁻¹)
            * (Real.sqrt (D ^ 2 * s2 ^ (- gc))
              * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2)))
          ≤ (Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)))
            * (Real.sqrt (D ^ 2 * s2 ^ (- gc))
              * Real.sqrt ((Real.cos q.2) ^ 2 * s2 ^ (gc - 2))) :=
            mul_le_mul_of_nonneg_right hbnd hsnn
        _ ≤ (Cc * ((B τ) ^ (- (1 / (3 * α))) * L ^ (2 / (3 * α) - 1)))
            * ((D ^ 2 * s2 ^ (- gc) + (Real.cos q.2) ^ 2 * s2 ^ (gc - 2)) / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hconstnn
            linarith [psiTwoMulSqrtLe hW3 hW4]
        _ = (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
            * ((D ^ 2 * s2 ^ (- gc)
              + (Real.cos q.2) ^ 2 * s2 ^ (gc - 2))) := by ring
    simp only [psiWpsi, psiWinner, psiWmaj, psiWq1, psiWq2, psiWq3, psiWq4, if_pos hLq, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hWnn]
    have hsum : Ca / ((B τ * q.1) ^ (1 / (3 * α)) * Real.cos q.2)
          * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cb * (B τ * q.1) ^ ((3 * α - 1) / (3 * α)) * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cc * (200 * α ^ 2 * (Real.sin (abs q.2)) ^ (α - 1)
              * (Real.cos q.2) ^ (2 * α - 1)) / ((B τ * q.1) ^ (1 / (3 * α)))
            * q.1 ^ (1 / α - 1) * Real.cos q.2
        + Cc * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)|
            / ((B τ * q.1) ^ (1 / (3 * α))) * q.1 ^ (1 / α - 1) * Real.cos q.2
        ≤ (Ca * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
            + Cb * (B τ) ^ (1 - 1 / (3 * α)) * (L ^ (2 / (3 * α))))
          + (Cc * 200 * α ^ 2 * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1))
              * ((Real.sin (abs q.2)) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)))
          + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
              * ((Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (abs q.2)) ^ 2
                  * (Real.sin (2 * abs q.2))
                      ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
          + (Cc * (B τ) ^ (- (1 / (3 * α))) * (L ^ (2 / (3 * α) - 1)) / 2)
              * ((Real.cos q.2) ^ 2
                  * (Real.sin (2 * abs q.2))
                      ^ (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 2)) := by
      linarith [hterm1, hterm2, hterm3, hterm4]
    refine le_trans (le_of_eq ?_) hsum
    ring
  · have hW : psiWpsi α Ca Cb Cc L B g τ q = 0 := by
      simp only [psiWpsi, psiWinner, if_neg hLq, zero_mul]
    rw [hW, norm_zero]
    exact psiWmajNonneg hCa hCb hCc hb hL hq2


end Work.FTS.FireFix.Clauses
