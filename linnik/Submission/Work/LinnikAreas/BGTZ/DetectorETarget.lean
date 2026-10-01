import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs
import Submission.Work.LinnikAreas.BGTZ.DetectorContour
import Submission.Work.LinnikAreas.BGTZ.DetectorResidueBound
import Submission.Work.LinnikAreas.BGTZ.E.detJ_le_target

/-!
# The last step of the BGTZ/E detector: from the `detJ` bound to `DetectorPropE`

`BGTZ_ROUTE_LEAD.md` section 2.5 finishes the detector by combining

* the contour shift `norm detector <= detResBound + norm detJ` (`DetectorContour`, proved),
* the residue bound `detResBound <= (2-b1)(1-b1)N^{1-rho.re}/(1-rho.re)` (`DetectorResidueBound`,
  proved),
* the shifted-line bound `norm detJ <= 2(1-b1)N^{1-rho.re}` (the statement `DetJTarget` below, i.e.
  L7 of the route: L6 `detJ_le` plus the arithmetic `detJTargetArith`),

with the choices `CR = max 1 C_res` and `CN = max 1 ((KJ*CR)^2)`.  The zero `rho` of the detector
case satisfies `rho.re < 1` by `det_rho_re_lt_one` (`DetectorContourCore`), which is what turns
`2(1-b1)N^{1-rho.re}` into the `1/(rho.re - 1/2)` term of the interface.

The shifted-line statement is isolated as the `Prop` `DetJTarget` so that the wiring below is
independent of the proof of `detJ_le`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- **The shifted-line bound of the detector** (L7 of `BGTZ_ROUTE_LEAD.md` section 3), the form the
assembly needs: it follows from L6 `detJ_le` by the arithmetic `detJTargetArith`. -/
def DetJTarget : Prop :=
  ∃ KJ : ℝ, 0 < KJ ∧ ∀ (CR : ℝ), 1 ≤ CR → ∀ (q : ℕ) [NeZero q], 400000 < q →
    ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
    ∀ {A : ℝ}, 1 ≤ A → HypA A thA → ∀ {R : ℕ}, 200 ≤ R → ∀ {θw : ℕ → ℝ}, IsSieveWeight R θw →
    (R : ℝ) ≤ 2 * CR * sieveX A q β₁ →
    ∀ (T : ℝ) {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → 1 + |ρ.im| ≤ T →
    ∀ (N : ℕ), 1 ≤ N → max 1 ((KJ * CR) ^ 2) * detNE A q β₁ T R ≤ (N : ℝ) →
      ‖detJ χ₁ χ R θw N ρ‖ ≤ 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re)

/-- `1 <= a`, `1 <= b` give `1 <= a * b` (for real numbers). -/
private lemma one_le_mul_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h0 : (0 : ℝ) ≤ a - 1 := by linarith
  have h1 : (0 : ℝ) ≤ b - 1 := by linarith
  nlinarith [mul_nonneg h0 h1]

/-- `detNE >= 1`: every factor is `>= 1` when `A >= 1`, `q >= 1`, `T >= 4`, `0 < 1-β₁ <= 1` and
`R >= 200`. -/
theorem one_le_detNE {A β₁ T : ℝ} {q R : ℕ} [NeZero q] (hA : 1 ≤ A) (hq : 1 ≤ q)
    (hT : 4 ≤ T) (hδ0 : 0 < 1 - β₁) (hδ1 : 1 - β₁ ≤ 1) (hR : 200 ≤ R) :
    1 ≤ detNE A q β₁ T R := by
  rw [detNE]
  have h1 : (1 : ℝ) ≤ A ^ 8 := one_le_pow₀ hA
  have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (8 * thA) :=
    Real.one_le_rpow (by exact_mod_cast hq) (by norm_num [thA])
  have h3 : (1 : ℝ) ≤ Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
    Real.one_le_exp (by positivity)
  have h4 : (1 : ℝ) ≤ T ^ (4 * thA) := Real.one_le_rpow (by linarith) (by norm_num [thA])
  have h5 : (1 : ℝ) ≤ (1 - β₁) ^ (-6 : ℝ) := by
    have h := Real.rpow_le_rpow_of_nonpos hδ0 hδ1 (by norm_num : (-6 : ℝ) ≤ 0)
    simpa using h
  have h6 : (1 : ℝ) ≤ (1 + Real.log (R : ℝ)) ^ 18 := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
    exact one_le_pow₀ (by linarith [Real.log_nonneg hR1])
  have h := one_le_mul_one_le h1
    (one_le_mul_one_le h2 (one_le_mul_one_le h3 (one_le_mul_one_le h4 (one_le_mul_one_le h5 h6))))
  simpa only [mul_assoc] using h

/-- `(exp y)^n = exp (n y)`. -/
private lemma exp_pow_nat (y : ℝ) (n : ℕ) : (Real.exp y) ^ n = Real.exp ((n : ℝ) * y) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

/-- **From the shifted-line bound to the corrected detector interface.** -/
theorem DetectorE_of_DetJTarget (hK : DetJTarget) : DetectorPropE := by
  obtain ⟨CR0, hCR0pos, hRes⟩ := Work.LinnikAreas.BGTZ.DetectorResidueBound
  obtain ⟨KJ, hKJpos, hDetJ⟩ := hK
  refine ⟨max 1 CR0, le_max_left _ _, max 1 ((KJ * max 1 CR0) ^ 2),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro q _ hq χ₁ hχ₁ hχ₁ne β₁ hβ₁lt hzm hβ₁big A Cz hA1 hA hZ R hR200 hRlo hRhi θw hθw hGraham
    χ T hT4 ρ hzero hρre34 hρimT N hNsize
  set CR : ℝ := max 1 CR0 with hCRdef
  have hCR1 : 1 ≤ CR := le_max_left _ _
  have hCR0le : CR0 ≤ CR := le_max_right _ _
  have hδpos : 0 < 1 - β₁ := by linarith
  have hq1 : 1 ≤ q := by omega
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hLq1 : (1 : ℝ) < Real.log (q : ℝ) := by
    have hq400000 : (400000 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 400000 ≤ q)
    have h1 : Real.log (Real.exp 1) < Real.log 400000 :=
      Real.log_lt_log (Real.exp_pos 1) (by have h := Real.exp_one_lt_three; linarith)
    rw [Real.log_exp] at h1
    exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) hq400000)
  have hδle1 : 1 - β₁ ≤ 1 := by
    have h10 : 0 < 10 * Real.log (q : ℝ) := by linarith
    have h1 : 1 - β₁ < 1 / (10 * Real.log (q : ℝ)) := by linarith [hβ₁big]
    have h2 : 1 / (10 * Real.log (q : ℝ)) ≤ 1 := by
      rw [div_le_one h10]
      linarith
    linarith
  have hN1 : 1 ≤ N := by
    have hdet : (1 : ℝ) ≤ detNE A q β₁ T R := one_le_detNE hA1 hq1 hT4 hδpos hδle1 hR200
    have hmax : (1 : ℝ) ≤ max 1 ((KJ * CR) ^ 2) := le_max_left _ _
    have h := mul_le_mul hmax hdet (by norm_num) (by positivity)
    have h2 : (1 : ℝ) ≤ (N : ℝ) := le_trans (by simpa using h) hNsize
    exact_mod_cast h2
  have hρimT2 : |ρ.im| ≤ T := by linarith [abs_nonneg ρ.im]
  have hre : (1 / 2 : ℝ) < ρ.re := by linarith
  have hρlt : ρ.re < 1 := det_rho_re_lt_one hq χ₁ χ hχ₁ne hzero hre
  have h1 := Work.LinnikAreas.BGTZ.DetectorContour (q := q) hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hzm hβ₁big
    hA hZ hR200 hθw T hT4 (ρ := ρ) hzero hre hρimT2 (N := N) hN1
  have hRloR : CR0 * A ^ 2 * (q : ℝ) ^ (2 * (1 / 4 + 1 / 100 : ℝ))
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) := by
    have hsx : CR0 * A ^ 2 * (q : ℝ) ^ (2 * (1 / 4 + 1 / 100 : ℝ))
        * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
        = CR0 * sieveX A q β₁ := by rw [sieveX]; ring
    rw [hsx]
    have hsxnn : 0 ≤ sieveX A q β₁ := by
      rw [sieveX]
      have hA2 : (0 : ℝ) ≤ A ^ 2 := by positivity
      have hqpow : (0 : ℝ) ≤ (q : ℝ) ^ (2 * thA) := Real.rpow_nonneg (by positivity) _
      have he : (0 : ℝ) ≤ Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
        (Real.exp_pos _).le
      have hd : (0 : ℝ) ≤ (1 - β₁) ^ (-2 : ℝ) := Real.rpow_nonneg hδpos.le _
      exact mul_nonneg (mul_nonneg (mul_nonneg hA2 hqpow) he) hd
    exact le_trans (mul_le_mul_of_nonneg_right hCR0le hsxnn) hRlo
  have h2 := hRes q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hzm hβ₁big (A := A) (θ := 1 / 4 + 1 / 100)
    (Cz := Cz) hA hZ hR200 hRloR hθw hGraham (ρ := ρ) hzero hre N
  have h3 := hDetJ CR hCR1 q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hA1 hA hR200 hθw hRhi T (ρ := ρ)
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
    _ = ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) := by
        ring


/-- **L7's `detJ_le_target` from L6 `detJ_le` and the arithmetic `detJTargetArith`.**

The conclusion `norm detJ <= 2(1-b1)N^{1-rho.re}` of `DetJTarget` is the critical-line `detJ` bound
(`detJ_le`, the hypothesis `hK`) with the size hypotheses `R <= 2*CR*sieveX` and
`max 1 ((KJ*CR)^2)*detNE <= N` absorbed into the constants: squaring the target inequality turns it
into exactly those two hypotheses (`detJTargetArith`). -/
theorem DetJTarget_of_detJ_le
    (harith : ∀ {KJ CR A q E T R N δ γ θ : ℝ},
      (0 < KJ) → (1 ≤ CR) → (1 ≤ A) → (1 ≤ q) → (1 ≤ E) → (0 < δ) → (0 < θ) → (1 ≤ N)
      → (1 < R) → (1 + |γ| ≤ T)
      → R ≤ 2 * CR * (A ^ 2 * q ^ (2 * θ) * E ^ 2 * δ ^ (-2 : ℝ))
      → (KJ * CR) ^ 2 * (A ^ 8 * q ^ (8 * θ) * E ^ 8 * T ^ (4 * θ) * δ ^ (-6 : ℝ)
            * (1 + Real.log R) ^ 18) ≤ N
      → KJ * A ^ 2 * q ^ (2 * θ) * E ^ 2 * (1 + |γ|) ^ (2 * θ) * (R * (1 + Real.log R) ^ 9)
            ≤ 2 * δ * Real.sqrt N)
    (hK : ∃ KJ : ℝ, 0 < KJ ∧ ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
      ∀ {A : ℝ}, 1 ≤ A → HypA A thA → ∀ {R : ℕ} {θw : ℕ → ℝ}, IsSieveWeight R θw →
      ∀ {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → ∀ {N : ℕ}, 1 ≤ N →
        ‖detJ χ₁ χ R θw N ρ‖ ≤ KJ * A ^ 2 * (q : ℝ) ^ (2 * thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * thA) * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
          * (N : ℝ) ^ ((1 / 2 : ℝ) - ρ.re)) :
    DetJTarget := by
  obtain ⟨KJ, hKJpos, hDetJ⟩ := hK
  refine ⟨KJ, hKJpos, ?_⟩
  intro CR hCR q _ hq χ₁ χ hχ₁ hχ₁ne β₁ hβ₁lt A hA1 hA R hR200 θw hθw hRhi T ρ hρre34 hρlt hρimT
    N hN1 hNsize
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  set E : ℝ := Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) with hEdef
  set δ : ℝ := 1 - β₁ with hδdef
  have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hEq : E ^ 2 = Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
    rw [hEdef]
    simpa only [Nat.cast_ofNat] using exp_pow_nat ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) 2
  have hEq8 : E ^ 8 = Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
    rw [hEdef]
    simpa only [Nat.cast_ofNat] using exp_pow_nat ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) 8
  have hRle : (R : ℝ) ≤ 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * thA) * E ^ 2 * δ ^ (-2 : ℝ)) := by
    rw [sieveX] at hRhi
    calc (R : ℝ) ≤ 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * thA)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)) := hRhi
      _ = 2 * CR * (A ^ 2 * (q : ℝ) ^ (2 * thA) * E ^ 2 * δ ^ (-2 : ℝ)) := by
          rw [hEq, hδdef]
  have hNge : (KJ * CR) ^ 2 * (A ^ 8 * (q : ℝ) ^ (8 * thA) * E ^ 8 * T ^ (4 * thA)
      * δ ^ (-6 : ℝ) * (1 + Real.log (R : ℝ)) ^ 18) ≤ (N : ℝ) := by
    rw [detNE] at hNsize
    rw [← hEq8] at hNsize
    refine le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_) hNsize
    have h1 : (0 : ℝ) ≤ A ^ 8 := by positivity
    have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (8 * thA) := Real.rpow_nonneg (by positivity) _
    have h3 : (0 : ℝ) ≤ E ^ 8 := by rw [hEdef]; positivity
    have h4 : (0 : ℝ) ≤ T ^ (4 * thA) :=
      Real.rpow_nonneg (by linarith [abs_nonneg ρ.im, hρimT]) _
    have h5 : (0 : ℝ) ≤ δ ^ (-6 : ℝ) := by
      rw [hδdef]; exact Real.rpow_nonneg (by linarith) _
    have h6 : (0 : ℝ) ≤ (1 + Real.log (R : ℝ)) ^ 18 := by
      apply pow_nonneg
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (R : ℝ))]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5) h6
  have harith1 := harith (KJ := KJ) (CR := CR) (A := A) (q := (q : ℝ)) (E := E) (T := T)
    (R := (R : ℝ)) (N := (N : ℝ)) (δ := δ) (γ := ρ.im) (θ := thA)
    hKJpos hCR hA1 hq1 hE1 hδpos (by norm_num [thA]) hN1R hR1 hρimT hRle hNge
  have harith2 : KJ * A ^ 2 * (q : ℝ) ^ (2 * thA)
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 + |ρ.im|) ^ (2 * thA)
      * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9) ≤ 2 * (1 - β₁) * Real.sqrt (N : ℝ) := by
    rw [hEq, hδdef] at harith1
    exact harith1
  have hdetJ := hDetJ q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hA1 hA hθw hρre34 hρlt (N := N) hN1
  have hsplit : (N : ℝ) ^ (1 - ρ.re) = (N : ℝ) ^ (1 / 2 - ρ.re) * Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
    congr 1
    ring
  calc ‖detJ χ₁ χ R θw N ρ‖
      ≤ KJ * A ^ 2 * (q : ℝ) ^ (2 * thA) * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (1 + |ρ.im|) ^ (2 * thA) * ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ 9)
          * (N : ℝ) ^ ((1 / 2 : ℝ) - ρ.re) := hdetJ
    _ ≤ 2 * (1 - β₁) * Real.sqrt (N : ℝ) * (N : ℝ) ^ (1 / 2 - ρ.re) :=
        mul_le_mul_of_nonneg_right harith2 (Real.rpow_nonneg (by positivity) _)
    _ = 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re) := by rw [hsplit]; ring


/-- **The `detJ` target statement of `BGTZ_ROUTE_LEAD.md` section 3** (`detJ_le_target`, the shape
the route document and `BGTZ/E/detJ_le_target.lean` use, without the hypothesis `200 <= R`) implies
the form `DetJTarget` consumed by `DetectorE_of_DetJTarget`. -/
theorem DetJTarget_of_detJ_le_target
    (h : ∃ KJ : ℝ, 0 < KJ ∧ ∀ (CR : ℝ), 1 ≤ CR → ∀ (q : ℕ) [NeZero q], 400000 < q →
      ∀ (χ₁ χ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 →
      ∀ {A : ℝ}, 1 ≤ A → HypA A thA → ∀ {R : ℕ} {θw : ℕ → ℝ}, IsSieveWeight R θw →
      (R : ℝ) ≤ 2 * CR * sieveX A q β₁ →
      ∀ (T : ℝ) {ρ : ℂ}, 3 / 4 ≤ ρ.re → ρ.re < 1 → 1 + |ρ.im| ≤ T →
      ∀ (N : ℕ), 1 ≤ N → max 1 ((KJ * CR) ^ 2) * detNE A q β₁ T R ≤ (N : ℝ) →
        ‖detJ χ₁ χ R θw N ρ‖ ≤ 2 * (1 - β₁) * (N : ℝ) ^ (1 - ρ.re)) :
    DetJTarget := by
  obtain ⟨KJ, hKJpos, hbody⟩ := h
  refine ⟨KJ, hKJpos, ?_⟩
  intro CR hCR q _ hq χ₁ χ hχ₁ hχ₁ne β₁ hβ₁lt A hA1 hA R hR200 θw hθw hRhi T ρ hρre34 hρlt hρimT
    N hN1 hNsize
  exact hbody CR hCR q hq χ₁ χ hχ₁ hχ₁ne hβ₁lt hA1 hA hθw hRhi T hρre34 hρlt hρimT N hN1 hNsize


/-- **`DetectorPropE` from the workspace**: the `detJ` target statement of the route document
(`BGTZ/E/detJ_le_target.lean`, proved from `BGTZ/E/detJ_le.lean`) fed into the wiring above. -/
theorem DetectorPropE_of_workspace : DetectorPropE :=
  DetectorE_of_DetJTarget (DetJTarget_of_detJ_le_target Work.LinnikAreas.BGTZ.E.detJ_le_target)

end Work.LinnikAreas.BGTZ
