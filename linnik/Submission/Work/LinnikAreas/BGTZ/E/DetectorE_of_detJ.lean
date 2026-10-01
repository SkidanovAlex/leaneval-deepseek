import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorContour
import Submission.Work.LinnikAreas.BGTZ.DetectorResidueBound

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ.E

/-- `1 <= a`, `1 <= b` give `1 <= a * b` (for real numbers). -/
private lemma one_le_mul_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h0 : (0 : ℝ) ≤ a - 1 := by linarith
  have h1 : (0 : ℝ) ≤ b - 1 := by linarith
  nlinarith [mul_nonneg h0 h1]

/-- `detNE >= 1`: every factor is `>= 1` when `A >= 1`, `q >= 1`, `T >= 4`, `0 < 1-β₁ <= 1` and
`R >= 200`. -/
theorem one_le_detNE {A β₁ T : ℝ} {q R : ℕ} [NeZero q] (hA : 1 ≤ A) (hq : 1 ≤ q)
    (hT : 4 ≤ T) (hδ0 : 0 < 1 - β₁) (hδ1 : 1 - β₁ ≤ 1) (hR : 200 ≤ R) :
    1 ≤ Work.LinnikAreas.BGTZ.detNE A q β₁ T R := by
  rw [Work.LinnikAreas.BGTZ.detNE]
  have h1 : (1 : ℝ) ≤ A ^ 8 := one_le_pow₀ hA
  have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (8 * Work.LinnikAreas.BGTZ.thA) :=
    Real.one_le_rpow (by exact_mod_cast hq) (by norm_num [Work.LinnikAreas.BGTZ.thA])
  have h3 : (1 : ℝ) ≤ Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
    Real.one_le_exp (by positivity)
  have h4 : (1 : ℝ) ≤ T ^ (4 * Work.LinnikAreas.BGTZ.thA) :=
    Real.one_le_rpow (by linarith) (by norm_num [Work.LinnikAreas.BGTZ.thA])
  have h5 : (1 : ℝ) ≤ (1 - β₁) ^ (-6 : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos hδ0 hδ1 (by norm_num : (-6 : ℝ) ≤ 0)
    simpa using h
  have h6 : (1 : ℝ) ≤ (1 + Real.log (R : ℝ)) ^ 18 := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
    exact one_le_pow₀ (by linarith [Real.log_nonneg hR1])
  have h := one_le_mul_one_le h1
    (one_le_mul_one_le h2 (one_le_mul_one_le h3 (one_le_mul_one_le h4 (one_le_mul_one_le h5 h6))))
  simpa only [mul_assoc] using h

/-- **From the shifted-line bound to the corrected detector interface.**

`BGTZ_ROUTE_LEAD.md` section 2.5: combine the contour shift `norm detector <= detResBound + norm
detJ` (`DetectorContour`, proved), the residue bound
`detResBound <= (2-b1)(1-b1)N^{1-rho.re}/(1-rho.re)` (`DetectorResidueBound`, proved) and the
shifted-line bound `norm detJ <= 2(1-b1)N^{1-rho.re}` (the hypothesis `hJt`), with the choices
`CR = max 1 C_res` and `CN = max 1 ((KJ*CR)^2)`. -/
theorem DetectorE_of_detJ
    (hJt : ∃ KJ : ℝ, 0 < KJ ∧ ∀ (CR : ℝ), 1 ≤ CR → ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
      ∀ {A : ℝ}, 1 ≤ A → Work.LinnikAreas.BGTZ.HypA A Work.LinnikAreas.BGTZ.thA →
      ∀ {R : ℕ} {θw : ℕ → ℝ}, Work.LinnikAreas.BGTZ.IsSieveWeight R θw →
      (R : ℝ) ≤ 2 * CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ →
      ∀ (T : ℝ) {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → 1 + |ρ.im| ≤ T →
      ∀ (N : ℕ), 1 ≤ N →
        max 1 ((KJ * CR) ^ 2) * Work.LinnikAreas.BGTZ.detNE A q β₁ T R ≤ (N : ℝ) →
        ‖Work.LinnikAreas.BGTZ.detJ χ₁ χ R θw N ρ‖ ≤ 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re)) :
    Work.LinnikAreas.BGTZ.DetectorPropE := by
  obtain ⟨CR0, hCR0pos, hRes⟩ := Work.LinnikAreas.BGTZ.DetectorResidueBound
  obtain ⟨KJ, hKJpos, hDetJ⟩ := hJt
  refine ⟨max 1 CR0, le_max_left _ _, max 1 ((KJ * max 1 CR0) ^ 2),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro q hqinst hq χ₁ hχ₁ hχ₁ne β₁ hβ₁lt hzm hβ₁big A Cz hA1 hA hZ R hR200 hRlo hRhi θw hθw
    hGraham χ T hT4 ρ hzero hρre34 hρimT N hNsize
  set CR : ℝ := max 1 CR0 with hCRdef
  have hCR1 : 1 ≤ CR := le_max_left _ _
  have hCR0le : CR0 ≤ CR := le_max_right _ _
  have hδpos : 0 < 1 - β₁ := by linarith
  have hδle1 : 1 - β₁ ≤ 1 := by
    have hlog1 : (1 : ℝ) < 10 * Real.log (q : ℝ) := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
      have hlog2 : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h2
      have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have hlt : 1 - β₁ < 1 / (10 * Real.log (q : ℝ)) := by linarith
    have hdiv : 1 / (10 * Real.log (q : ℝ)) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hq1 : 1 ≤ q := by omega
  have hN1 : 1 ≤ N := by
    have hdet : (1 : ℝ) ≤ Work.LinnikAreas.BGTZ.detNE A q β₁ T R :=
      one_le_detNE hA1 hq1 hT4 hδpos hδle1 hR200
    have hmax : (1 : ℝ) ≤ max 1 ((KJ * CR) ^ 2) := le_max_left _ _
    have h := mul_le_mul hmax hdet (by norm_num)
      (le_trans zero_le_one (le_max_left (1 : ℝ) ((KJ * CR) ^ 2)))
    have h2 : (1 : ℝ) ≤ (N : ℝ) := le_trans (by simpa using h) hNsize
    exact_mod_cast h2
  have hρimT2 : |ρ.im| ≤ T := by linarith [abs_nonneg ρ.im]
  have hre : (1 / 2 : ℝ) < ρ.re := by linarith
  have hρlt : ρ.re < 1 := det_rho_re_lt_one hq χ₁ χ hχ₁ne hzero hre
  have h1 := Work.LinnikAreas.BGTZ.DetectorContour (q := q) hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hzm hβ₁big
    hA hZ hR200 hθw T hT4 (ρ := ρ) hzero hre hρimT2 (N := N) hN1
  have hsxnn : (0 : ℝ) ≤ sieveX A q β₁ := by
    rw [sieveX]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg A) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
        (Real.exp_pos _).le)
      (Real.rpow_nonneg hδpos.le _)
  have hRloR : CR0 * A ^ 2 * (q : ℝ) ^ (2 * (1 / 4 + 1 / 100 : ℝ))
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) := by
    have hsx : CR0 * A ^ 2 * (q : ℝ) ^ (2 * (1 / 4 + 1 / 100 : ℝ))
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
        = CR0 * sieveX A q β₁ := by rw [sieveX]; ring
    rw [hsx]
    exact le_trans (mul_le_mul_of_nonneg_right hCR0le hsxnn) hRlo
  have h2 := hRes q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hzm hβ₁big (A := A) (θ := 1 / 4 + 1 / 100)
    (Cz := Cz) hA hZ hR200 hRloR hθw hGraham (ρ := ρ) hzero hre N
  have h3 := hDetJ CR hCR1 q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hA1 hA hθw hRhi T (ρ := ρ)
    hρre34 hρlt hρimT N hN1 hNsize
  have h3b : ‖detJ χ₁ χ R θw N ρ‖ ≤ (1 - β₁) * (N : ℝ) ^ (1 - ρ.re) / (ρ.re - 1 / 2) := by
    refine le_trans h3 ?_
    have hpos : (0 : ℝ) < ρ.re - 1 / 2 := by linarith
    rw [le_div_iff₀ hpos]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - ρ.re) := Real.rpow_nonneg (by positivity) _
    have hkey : 2 * (ρ.re - 1 / 2) ≤ 1 := by linarith
    have hk := mul_le_mul_of_nonneg_right hkey hδpos.le
    nlinarith [hk, hN0, hδpos]
  calc ‖detector χ₁ χ N θw ρ‖
      ≤ detResBound χ₁ χ R θw N ρ + ‖detJ χ₁ χ R θw N ρ‖ := h1
    _ ≤ (2 - β₁) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) / (1 - ρ.re)
          + (1 - β₁) * (N : ℝ) ^ (1 - ρ.re) / (ρ.re - 1 / 2) := add_le_add h2 h3b
    _ = ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) := by ring

end Work.LinnikAreas.BGTZ.E
