/-
# ZeroFreeTables/Rep9/Assembly — assembling `HBLemma9_1_rep`

The target `Work.ZeroFreeTables.HBLemma9_1_rep` is assembled here from

* `Rep9/Algebra.lean` (**proved**) — the algebraic endgame `ineq913_diag_of_derived`,
* `Rep9/combination_diag` (**proved**) — HB (9.1) at the diagonal,
* `Rep9/logDerivHyp_quarter` (**proved**) — HB Lemma 3.1 at `φ = 1/2`,
* the per-point analytic bounds `Rep9/{masterP3M,principalBoundM,imprimCorrM,nearSum_bounds,caseC_extra2,nearSum_primitive_le}`
  (statements final, proofs in flight).  Import them here once they are `sorry`-free.

Every constant and every step of the remaining assembly is written out in `Rep9/NOTES.md`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Rep9.Algebra
import Submission.Work.ZeroFreeTables.Rep9.combination_diag
import Submission.Work.ZeroFreeTables.Rep9.logDerivHyp_quarter
import Submission.Work.ZeroFreeTables.Rep9.masterP3M
import Submission.Work.ZeroFreeTables.Rep9.principalBoundAmended
import Submission.Work.ZeroFreeTables.Rep9.nearSum_bounds
import Submission.Work.ZeroFreeTables.Rep9.nearSum_primitive_le
import Submission.Work.ZeroFreeTables.Rep9.imprimCorrBounded
import Submission.Work.ZeroFreeTables.Rep9.order3_extraM
import Submission.Work.ZeroFreeTables.Rep9.P3_div_le
import Submission.Work.ZeroFreeTables.Rep9.caseC_near
import Submission.Work.ZeroFreeTables.Rep9.caseC_far
import Submission.Work.ZeroFreeTables.P9.Setup
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBRepZeroC_defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables.Rep9

open Work.ZeroFreeTables Work.LinnikContract

/-- `Re P₃(r) = P₃R r` for real `r`. -/
theorem P3_ofReal_re (r : ℝ) : (P3 ((r : ℝ) : ℂ)).re = P3R r := by
  have h : P3 ((r : ℝ) : ℂ) = ((P3R r : ℝ) : ℂ) := by
    simp only [P3, P3R]; push_cast; ring
  rw [h, Complex.ofReal_re]

/-- `x ≤ y` from `x³ ≤ y³`, `x, y ≥ 0`. -/
theorem cube_le_cube {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^3 ≤ y^3) : x ≤ y := by
  by_contra hlt
  push_neg at hlt
  have h1 : 0 < x - y := by linarith only [hlt]
  have h2 : 0 < x^2 + x*y + y^2 := by nlinarith only [sq_nonneg (x + y/2), sq_nonneg y, hx, hy, h1, hlt]
  have h3 : (x - y) * (x^2 + x*y + y^2) = x^3 - y^3 := by ring
  linarith only [mul_pos h1 h2, h3, h, h1, h2]

/-- `Kond K > 0` for `K > 0`. -/
theorem Kond_pos {K : ℝ} (hK : 0 < K) : 0 < Kond K :=
  lt_min (by positivity) (by positivity)

/-- `λ₁ ≤ a·(Kond K + 1)` from the side condition `cond913 λ λ a K` (for `K > 0`). -/
theorem lam_le_of_cond913 {a K lam : ℝ} (ha : 0 < a) (hK : 0 < K) (hlam : 0 ≤ lam)
    (h : cond913 lam lam a K) : lam ≤ a * (Kond K + 1) := by
  have hcube := cond913_cube_le (a := a) (K := K) (lam := lam) ha hlam h
  have hK1 : 1 ≤ Kond K + 1 := by have := Kond_pos hK; linarith only [this]
  have hx0 : 0 ≤ (a + lam)/a := by positivity
  have hC0 : 0 ≤ (Kond K + 1) := by linarith only [hK1]
  have hstep : (a+lam)/a ≤ Kond K + 1 := by
    apply cube_le_cube hx0 hC0
    have hCC : Kond K + 1 ≤ (Kond K + 1)^3 := by
      simpa using pow_le_pow_right₀ hK1 (by norm_num : (1:ℕ) ≤ 3)
    linarith only [hcube, hCC]
  have h2 : a + lam ≤ a * (Kond K + 1) := by
    rw [div_le_iff₀ ha] at hstep; linarith only [hstep]
  linarith only [ha, h2]

/-- `Kond K = 4K` when `K ≤ 1/2`, `= K + 3/(4K)` when `K ≥ 1/2`. -/
theorem Kond_eq_of_le_half {K : ℝ} (hK : 0 < K) (h : K ≤ 1/2) : Kond K = 4*K := by
  have h4K : 0 < 4*K := by linarith only [hK]
  rw [Kond, min_eq_right]
  have h1 : 3*K ≤ 3/(4*K) := by
    rw [le_div_iff₀ h4K]
    linarith only [pow_le_pow_left₀ hK.le h 2, hK, h]
  linarith only [h1]

/-- `Kond K = K + 3/(4K)` when `K ≥ 1/2`. -/
theorem Kond_eq_of_half_le {K : ℝ} (hK : 0 < K) (h : 1/2 ≤ K) : Kond K = K + 3/(4*K) := by
  have h4K : 0 < 4*K := by linarith only [hK]
  rw [Kond, min_eq_left]
  have h1 : 3/(4*K) ≤ 3*K := by
    rw [div_le_iff₀ h4K]
    linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h 2, h]
  linarith only [h1]

/-- `K + 1/4 ≤ K² + K + 1 − K·Kond K`. -/
theorem slack_ge_Kquarter {K : ℝ} (hK : 0 < K) :
    K + 1/4 ≤ K^2 + K + 1 - K * Kond K := by
  by_cases h : K ≤ 1/2
  · rw [Kond_eq_of_le_half hK h]
    linarith only [pow_le_pow_left₀ hK.le h 2, hK, h]
  · push_neg at h
    rw [Kond_eq_of_half_le hK h.le]
    have h2 : K * (3/(4*K)) = 3/4 := by field_simp
    linarith only [h2.le, h2.ge, h2]

/-- `1/4 + 1/(48K) ≤ 1/6 + (K²+K+1−K·Kond K)/(12K)` for `K > 0`. -/
theorem quarter_plus_le_side {K : ℝ} (hK : 0 < K) :
    1/4 + 1/(48*K) ≤ 1/6 + (K^2 + K + 1 - K * Kond K)/(12*K) := by
  have hS0 : K + 1/4 ≤ K^2 + K + 1 - K * Kond K := slack_ge_Kquarter hK
  have h3 : (K + 1/4)/(12*K) ≤ (K^2 + K + 1 - K * Kond K)/(12*K) :=
    div_le_div_of_nonneg_right hS0 (by positivity)
  have h4 : 1/6 + (K + 1/4)/(12*K) = 1/4 + 1/(48*K) := by
    first | (field_simp; ring) | field_simp
  linarith only [h3, h4]

/-- **The algebraic endgame, in polynomial form.**  If `C = c·(K²+3K+3/2)` satisfies the
side condition in the cleared form `C·48K ≤ (12K+1)(K²+3K+3/2)` and the derived inequality
with the coefficient `C`, then `ineq913` holds (for every `ε > 0`). -/
theorem ineq913_diag_of_derived_poly {a K C ε lam : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hε : 0 < ε) (hlam : 0 ≤ lam)
    (hx3 : ((a + lam)/a)^3 ≤ Kond K + 1)
    (hc : C * (48*K) ≤ (12*K + 1) * (K^2 + 3*K + 3/2))
    (hD : 0 ≤ (K^2 + K + 1/2) * P3R ((a+lam)/a) - (2*K^2 + 4*K + 3/2) * P3R 1
            + (a+lam) * C) :
    ineq913 lam lam a K ε := by
  set Sp : ℝ := K^2 + 3*K + 3/2 with hSpdef
  have hSppos : 0 < Sp := by rw [hSpdef]; positivity
  have hc' : C/Sp ≤ 1/6 + (K^2 + K + 1 - K * Kond K)/(12*K) := by
    refine le_trans ?_ (quarter_plus_le_side hK)
    have h1 : (1/4 + 1/(48*K))*Sp*(48*K) = (12*K+1)*Sp := by
      first | (field_simp; ring) | field_simp
    have h2 : C*(48*K) ≤ (1/4 + 1/(48*K))*Sp*(48*K) := by
      rw [h1]
      rw [hSpdef]
      exact hc
    rw [div_le_iff₀ hSppos]
    exact le_of_mul_le_mul_right h2 (by positivity : (0:ℝ) < 48*K)
  have hD' : 0 ≤ (K^2+K+1/2)*P3R ((a+lam)/a) - (2*K^2+4*K+3/2)*P3R 1
      + (a+lam)*(C/Sp)*Sp := by
    have h : (a+lam)*(C/Sp)*Sp = (a+lam)*C := by
      rw [mul_assoc, div_mul_cancel₀ C (ne_of_gt hSppos)]
    linarith only [hD, h.le, h.ge, h]
  exact ineq913_diag_of_derived (a := a) (K := K) (c := C/Sp) (ε := ε) (lam := lam)
    ha hK hε hlam hx3 hc' hD'

/-- `(K + 1/2)(Kond K + 1) ≤ 2(K² + 2K + 3/4)`. -/
theorem A2_mul_Kond_le {K : ℝ} (hK : 0 < K) :
    (K + 1/2) * (Kond K + 1) ≤ 2 * (K^2 + 2*K + 3/4) := by
  by_cases h : K ≤ 1/2
  · rw [Kond_eq_of_le_half hK h]
    linarith only [pow_le_pow_left₀ hK.le h 2, hK, h]
  · push_neg at h
    rw [Kond_eq_of_half_le hK h.le]
    have hexp : (K + 1/2) * (K + 3/(4*K) + 1)
        = (K + 1/2) * (K+1) + (K + 1/2) * (3/(4*K)) := by ring
    have h1 : (K + 1/2) * (3/(4*K)) = 3/4 + 3/(8*K) := by field_simp; ring
    have h2 : (K + 1/2) * (K+1) = K^2 + 3*K/2 + 1/2 := by ring
    have h3 : 3/(8*K) ≤ 3/4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*K)]
      linarith only [h]
    have h4 : (1/2:ℝ)^2 ≤ K^2 := pow_le_pow_left₀ (by norm_num) h.le 2
    rw [hexp, h1, h2]
    linarith only [h3, h4, h, hK]


/-! ## The assembly

The three case lemmas below are the assembly of the target from the pieces; their statements are
final.  With `L = log q`, `λ = lamOf q ρ₁`, `γ = ρ₁.im`, `α = a+λ`, `σ = 1+a/L`, and the
constants `e = 1/(768K)`, `e₀ = e(K²+3K+3/2)/(2(K²+K+1/2))`, `M = a(Kond K+1)`, each case

1. gets `δ, L₀` from `logDerivHyp_quarter (e := e)`, the threshold of `masterP3M`
   `(c := 1/4+e, e := e, M := M)`, of `principalBoundM (e := e₀, M := M)` and of
   `imprimCorrM (e := e, M := M)`, and takes `q₀` so that `log q ≥` all of them and `M/log q ≤ δ`;
2. builds the four per-point bounds at `σ`, `σ+iγ`, `σ+2iγ`, `σ+3iγ` (using
   `nearSum_bounds` for the near sums, `nearSum_primitive_le` to pass to the primitive
   character, and `caseC_extra2` in the order-2 case);
3. combines them with `combination_diag` and finishes with
   `Algebra.ineq913_diag_of_derived (c := 1/4 + 2.5e)` — the constants satisfy
   `1/4 + 2.5e ≤ 1/6 + slack₀/(12K)` because `slack₀ ≥ K + 1/4` (`slack_ge_quarter`). -/


/-! ## The per-point bound for an arbitrary non-principal character

`pointBound` composes the three landed pieces: `imprimCorrBounded` (pass from `χ` to its primitive
character), `masterP3M` (the `P₃` master bound for a primitive character, with its
`LogDerivHyp` supplied by `logDerivHyp_quarter`) and `nearSum_primitive_le` (the near sums agree). -/
theorem pointBound {a e M : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) :
    ∃ q₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {lam₁ : ℝ}, 0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a / Real.log (q:ℝ) → |s.im| ≤ 4 →
        SigmaP3L q (Real.log q) χ s a lam₁
          ≤ -P3NearSumL q (Real.log q) χ s a lam₁ δ + (a + lam₁) * (1/4 + e) := by
  obtain ⟨L₀L, δ, hδ0, hδ1, hlog⟩ := logDerivHyp_quarter (e := e/3) (by positivity)
  obtain ⟨L₀m, hmast⟩ := masterP3M (a := a) (δ := δ) (c := 1/4 + e/3) (e := e/3) (M := M)
    ha hδ0 hδ1 (by positivity)
  obtain ⟨L₀i, himp⟩ := imprimCorrBounded (a := a) (e := e/3) (M := M) ha (by positivity) hM
  refine ⟨max (max (Nat.ceil (Real.exp L₀L)) (Nat.ceil (Real.exp L₀m)))
      (max (Nat.ceil (Real.exp L₀i)) 5) + 1, δ, hδ0, hδ1, ?_⟩
  intro q hq inst χ hχ lam₁ hlam0 hlamM s hsre hsim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hceL : Nat.ceil (Real.exp L₀L) ≤ q := by omega
  have hceM : Nat.ceil (Real.exp L₀m) ≤ q := by omega
  have hceI : Nat.ceil (Real.exp L₀i) ≤ q := by omega
  have hexpL : Real.exp L₀L ≤ (q:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceL)
  have hexpM : Real.exp L₀m ≤ (q:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceM)
  have hexpI : Real.exp L₀i ≤ (q:ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceI)
  have hLL : L₀L ≤ L := by
    rw [hLdef]
    calc L₀L = Real.log (Real.exp L₀L) := (Real.log_exp L₀L).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexpL
  have hLm : L₀m ≤ L := by
    rw [hLdef]
    calc L₀m = Real.log (Real.exp L₀m) := (Real.log_exp L₀m).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexpM
  have hLi : L₀i ≤ L := by
    rw [hLdef]
    calc L₀i = Real.log (Real.exp L₀i) := (Real.log_exp L₀i).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexpI
  have hχprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hχprimne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    have h2 := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact h2.symm
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ L := by
    have hle : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    rw [hLdef]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor))
      (by exact_mod_cast hle)
  have hlogd : LogDerivHyp χ.primitiveCharacter δ L (1/4 + e/3) :=
    hlog χ.primitiveCharacter hχprimne hχprim hLL hlogN
  have hm := hmast χ.primitiveCharacter hχprimne hχprim hLm hlogN hlam0 hlamM hlogd s hsre hsim
  have hi := himp χ hχ hLi (le_of_eq hLdef.symm) hlam0 hlamM s hsre hsim
  have hn := nearSum_primitive_le hq2 χ hχ L s a lam₁ δ hδ0.le hδ1
  have hkey : (a + lam₁) * ((1/4 + e/3) + e/3) = (a + lam₁) * (1/4 + 2*e/3) := by ring
  linarith only [hm, hi, hn, hkey, inst, this]

/-- **Generic case**, primitive `χ₁` with `χ₁² ≠ 1`, `χ₁³ ≠ 1`. -/
theorem generic_case_prim {a K ε : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
      χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 ≠ 1 →
      cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
      ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε := by
  set e : ℝ := 1/(768*K) with he
  have hepos : 0 < e := by rw [he]; positivity
  set e0 : ℝ := e * (K^2+3*K+3/2) / (2*(K^2+K+1/2)) with he0
  have he0pos : 0 < e0 := by rw [he0]; positivity
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (le_of_lt ha) (by linarith only [Kond_pos hK, hK])
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ := pointBound (a := a) (e := e) (M := M) ha hepos hMnn
  obtain ⟨L₀p, hprinc⟩ := principalBoundAmended (a := a) (e := e0) (M := M) ha he0pos
  refine ⟨max (max q₀b (Nat.ceil (Real.exp L₀p)))
      (max (Nat.ceil (Real.exp (max (M/δ) 10))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hmin hZ hmult hχ2 hχ3 hcond
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hqb : q₀b ≤ q := by omega
  have hLp : L₀p ≤ L := by
    have hce : Nat.ceil (Real.exp L₀p) ≤ q := by omega
    have hexp : Real.exp L₀p ≤ (q:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
    rw [hLdef]
    calc L₀p = Real.log (Real.exp L₀p) := (Real.log_exp L₀p).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hLnb : Real.exp (max (M/δ) 10) ≤ (q:ℝ) := by
    have h2 : (Nat.ceil (Real.exp (max (M/δ) 10)) : ℝ) ≤ (q:ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max (M/δ) 10)) ≤ q)
    exact le_trans (Nat.le_ceil _) h2
  have hMδ : M/δ ≤ L := by
    rw [hLdef]
    calc M/δ ≤ max (M/δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * L := by
    have h' : M/δ ≤ L := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith only [h']
  have h10 : (10:ℝ) ≤ L := by
    rw [hLdef]
    calc (10:ℝ) ≤ max (M/δ) 10 := le_max_right _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  -- facts about the pair
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.P9.lamOf_nonneg hZ
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]; exact lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / L ≤ δ := by
    rw [div_le_iff₀ hLpos]; exact le_trans hlamM hMlt
  have hγ1 : |ρ₁.im| ≤ 1 := hZ.2.2
  have hχ1ne : χ₁ ≠ 1 := hZ.1
  have hcube := cond913_cube_le (a := a) (K := K) (lam := lamOf q ρ₁) ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith only [ha, hlam0]
  set σ : ℂ := ((1 + a / L : ℝ) : ℂ) with hσ
  -- the four per-point bounds
  have hcomb := combination_diag (q := q) χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K)
    hq2 ha hK hγ1 hlam0 hχ1ne
  have hσeq : (((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) = σ := by rw [hσ, hLdef]
  have hcomb' := hcomb
  rw [hσeq] at hcomb'
  -- (0) principal character at σ
  have hσre : σ.re = 1 + a/L := by rw [hσ]; simp
  have hσim : |σ.im| ≤ 4 := by rw [hσ]; simp
  have hb0 : SigmaP3L q L (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P3R (al/a) + al*e0 := by
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      σ hσre hσim
    have hz : (a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)) = ((al/a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a/L : ℝ)) : ℂ) := by
        have hcast : ((1 + a/L : ℝ) : ℂ) - 1 = (((1 + a/L) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * (L : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hLpos)
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)))).re = P3R (al/a) := by
      rw [hz]; exact P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal] using h
  -- (1) χ₁ at σ + iγ
  have hb1 : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al*(1/4 + e) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hδ0, hδ1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM _ hsre hsim
    have h3 : (2:ℝ) * P3R 1 ≤ P3NearSumL q L χ₁
        (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
        (γ' := 2 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).1
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- (2) χ₁² at σ + 2iγ and (3) χ₁³ at σ + 3iγ
  have hb2 : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ 0 + al*(1/4 + e) := by
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hδ0, hδ1]
    have h1 := hpb q hqb (χ₁^2) (fun hcon => hχ2 hcon) hlam0 hlamM _ hsre hsim
    have h3 : (0:ℝ) ≤ P3NearSumL q L (χ₁^2)
        (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
        (γ' := 2 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).2 (χ₁^2) (fun hcon => hχ2 hcon)
        (by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]; linarith only [hγ1, hδ0, hδ1])
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
          = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  have hb3 : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ 0 + al*(1/4 + e) := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hδ0, hδ1]
    have h1 := hpb q hqb (χ₁^3) (fun hcon => hχ3 hcon) hlam0 hlamM _ hsre hsim
    have h3 : (0:ℝ) ≤ P3NearSumL q L (χ₁^3)
        (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
        (γ' := 3 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).2 (χ₁^3)
        (fun hcon => hχ3 hcon)
        (by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)]; linarith only [hγ1, hδ0, hδ1])
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
          = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- assemble (D)
  have hD : 0 ≤ (K^2 + K + 1/2) * P3R (al/a) - (2*K^2 + 4*K + 3/2) * P3R 1
      + al * (1/4 + 3*e/2) * (K^2 + 3*K + 3/2) := by
    have hK2 : (0:ℝ) < K^2 + K + 1/2 := by positivity
    have hK3 : (0:ℝ) < K^2 + 2*K + 3/4 := by positivity
    have hK5 : (0:ℝ) < K + 1/2 := by linarith only [hK, hδ0, hδ1]
    have he0v : (K^2+K+1/2)*e0 = e/2 * (K^2+3*K+3/2) := by
      first | (rw [he0]; field_simp; ring) | (rw [he0]; field_simp)
    have i0 := mul_le_mul_of_nonneg_left hb0 hK2.le
    have i1 := mul_le_mul_of_nonneg_left hb1 hK3.le
    have i2 := mul_le_mul_of_nonneg_left hb2 (show (0:ℝ) ≤ K + 1/2 by linarith only [hK, hδ0, hδ1])
    have i3 := mul_le_mul_of_nonneg_left hb3 (show (0:ℝ) ≤ 1/4 by norm_num)
    nlinarith only [hcomb', i0, i1, i2, i3, he0v, mul_nonneg (le_of_lt halpos) hε.le, inst, hcomb, hb3, ha, hδ0, hδ1, hlam0]
  -- the endgame
  have hc : (1/4 + 3*e/2) ≤ 1/6 + (K^2 + K + 1 - K * Kond K)/(12*K) := by
    have h1 := slack_ge_Kquarter hK
    have h2 : (0:ℝ) < 12*K := by positivity
    have h3 : (K + 1/4)/(12*K) ≤ (K^2 + K + 1 - K * Kond K)/(12*K) :=
      div_le_div_of_nonneg_right h1 h2.le
    have h4 : 1/6 + (K + 1/4)/(12*K) = 1/4 + 1/(48*K) := by field_simp; ring
    have h5 : 3*e/2 ≤ 1/(48*K) := by
      have h6 := mul_le_mul_of_nonneg_left he.le (show (0:ℝ) ≤ 3/2 by norm_num)
      have h7 : (3/2)*(1/(768*K)) = 1/(512*K) := by ring
      have h8 : 1/(512*K) ≤ 1/(48*K) := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 512*K) (by positivity : (0:ℝ) < 48*K)]
        linarith only [hK]
      linarith only [h6, h7.le, h7.ge, h8, h7]
    linarith only [h3, h4, h5]
  exact ineq913_diag_of_derived (a := a) (K := K) (c := 1/4 + 3*e/2) (ε := ε)
    (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hc hD

/-- **Order-3 case**: `χ₁³ = 1`, `χ₁² ≠ 1`. -/
theorem order3_case_prim {a K ε : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
      χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 = 1 →
      cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
      ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε := by
  set S : ℝ := K^2 + 3*K + 3/2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (min (1/(768*K)) (1/12)) (min (29*a*S/(768*K)) (a*S/(24*K))) with hedef
  have hepos : 0 < e := by
    rw [hedef]
    exact lt_min (lt_min (by positivity) (by norm_num))
      (lt_min (by positivity) (by positivity))
  have heA : e ≤ min (1/(768*K)) (1/12) := min_le_left _ _
  have heB : e ≤ min (29*a*S/(768*K)) (a*S/(24*K)) := min_le_right _ _
  have he1 : e ≤ 1/(768*K) := le_trans heA (min_le_left _ _)
  have he12 : e ≤ 1/12 := le_trans heA (min_le_right _ _)
  have he3 : e ≤ a*S/(24*K) := le_trans heB (min_le_right _ _)
  set e0 : ℝ := e * S / (2*(K^2+K+1/2)) with he0def
  have he0pos : 0 < e0 := by rw [he0def]; positivity
  have he0le : e0 ≤ 3*e/2 := by
    rw [he0def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K^2+K+1/2))]
    have h1 : K^2 + 3*K + 3/2 ≤ 3*(K^2+K+1/2) := by linarith only [sq_nonneg K, hK]
    have h2 : e * (K^2 + 3*K + 3/2) ≤ e * (3*(K^2+K+1/2)) :=
      mul_le_mul_of_nonneg_left h1 hepos.le
    have h3 : (3*e/2) * (2*(K^2+K+1/2)) = e * (3*(K^2+K+1/2)) := by ring
    rw [hSdef]
    linarith only [h2, h3.le, h3.ge]
  have he0quarter : e0 ≤ 1/4 + e := by linarith only [he0le, he12, hepos]
  -- polynomial forms of the size conditions on `e`, `e0`
  have he1' : 768*K*e ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left he1 (by positivity : (0:ℝ) ≤ 768*K)
    have h2 : (768*K)*(1/(768*K)) = 1 := by
      field_simp
    linarith only [h, h2.le, h2.ge, h2]
  have h768 : 768*K*e*S ≤ S := by
    have h := mul_le_mul_of_nonneg_right he1' hSpos.le
    simpa using h
  have he0v : (K^2+K+1/2)*e0 = e*S/2 := by
    first | (rw [he0def]; field_simp; ring) | (rw [he0def]; field_simp)
  have he0les : e0 ≤ e*S := by
    have hA0 : (1:ℝ)/2 ≤ K^2+K+1/2 := by linarith only [sq_nonneg K, hK]
    have hnn : 0 ≤ e*S := mul_nonneg hepos.le hSpos.le
    have h1 : (e*S)*1 ≤ (e*S)*(2*(K^2+K+1/2)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hA0] : (1:ℝ) ≤ 2*(K^2+K+1/2)) hnn
    rw [he0def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K^2+K+1/2))]
    linarith only [h1]
  have h84 : 84*K*e*S ≤ S/2 := by
    have h1 : 84*K*e*S = (84/768)*(768*K*e*S) := by ring
    have h2 : (84/768)*(768*K*e*S) ≤ (84/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (84/768)*S ≤ (1/2:ℝ)*S :=
      mul_le_mul_of_nonneg_right (by norm_num) hSpos.le
    have h4 : (1/2:ℝ)*S = S/2 := by ring
    linarith only [h1.le, h1.ge, h2, h3, h4.le, h4.ge, hSpos, h768]
  have hSge : (3:ℝ)/2 ≤ S := by rw [hSdef]; linarith only [sq_nonneg K, hK.le]
  set ex : ℝ := e/(4*a*S) with hexdef
  have hexle : ex ≤ 1/(96*K) := by
    have h := div_le_div_of_nonneg_right he3 (by positivity : (0:ℝ) ≤ 4*a*S)
    have h3 : (a*S/(24*K))/(4*a*S) = 1/(96*K) := by
      first | (field_simp; ring) | field_simp
    linarith only [h, h3.le, h3.ge, h3]
  have hexSp : 48*K*(ex*S) ≤ S/2 := by
    have h := mul_le_mul_of_nonneg_right hexle hSpos.le
    have h4 : 48*K*(ex*S) ≤ 48*K*((1/(96*K))*S) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 48*K*((1/(96*K))*S) = S/2 := by
      first | (field_simp; ring) | field_simp
    linarith only [h4, h2.le, h2.ge, h2]
  set CN : ℝ := (K^2+K+1/2)*e0 + (S - 1/4)*(1/4+e) + (1/4)*e0 with hCNdef
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (le_of_lt ha) (by linarith only [Kond_pos hK, hepos, he12, hK])
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ := pointBound (a := a) (e := e) (M := M) ha hepos hMnn
  obtain ⟨L₀p, hprinc⟩ := principalBoundAmended (a := a) (e := e0) (M := M) ha he0pos
  obtain ⟨q₀x, hextra⟩ := order3_extraM (a := a) (δ := δ) (e := e) (M := M)
    ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max q₀b q₀x) (max (max (Nat.ceil (Real.exp L₀p))
      (Nat.ceil (Real.exp (max (M/δ) 10)))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hmin hZ hmult hχ2 hχ3eq hcond
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hqb : q₀b ≤ q := by omega
  have hqx : q₀x ≤ q := by omega
  have hLp : L₀p ≤ L := by
    have hce : Nat.ceil (Real.exp L₀p) ≤ q := by omega
    have hexp : Real.exp L₀p ≤ (q:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
    rw [hLdef]
    calc L₀p = Real.log (Real.exp L₀p) := (Real.log_exp L₀p).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hLnb : Real.exp (max (M/δ) 10) ≤ (q:ℝ) := by
    have h2 : (Nat.ceil (Real.exp (max (M/δ) 10)) : ℝ) ≤ (q:ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max (M/δ) 10)) ≤ q)
    exact le_trans (Nat.le_ceil _) h2
  have hMδ : M/δ ≤ L := by
    rw [hLdef]
    calc M/δ ≤ max (M/δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * L := by
    have h' : M/δ ≤ L := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith only [h']
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.P9.lamOf_nonneg hZ
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]; exact lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / L ≤ δ := by
    rw [div_le_iff₀ hLpos]; exact le_trans hlamM hMlt
  have hγ1 : |ρ₁.im| ≤ 1 := hZ.2.2
  have hχ1ne : χ₁ ≠ 1 := hZ.1
  have hcube := cond913_cube_le (a := a) (K := K) (lam := lamOf q ρ₁) ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith only [ha, hlam0]
  have hale : a ≤ al := by rw [hal]; linarith only [hlam0]
  set σ : ℂ := ((1 + a / L : ℝ) : ℂ) with hσ
  set μ : ℝ := 3 * ρ₁.im * L with hμ
  set P0 : ℝ := P3R (al/a) with hP0def
  set Φa : ℝ := (P3 ((al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I))).re with hΦadef
  set Φ2 : ℝ := (P3 ((al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I))).re with hΦ2def
  set W : ℝ := P3NearSumL q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ
    with hWdef
  have hcomb := combination_diag (q := q) χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K)
    hq2 ha hK hγ1 hlam0 hχ1ne
  have hσeq : (((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) = σ := by rw [hσ, hLdef]
  have hcomb' := hcomb
  rw [hσeq] at hcomb'
  have hσre : σ.re = 1 + a/L := by rw [hσ]; simp
  have hσim : |σ.im| ≤ 4 := by rw [hσ]; simp
  -- (0) principal character at σ
  have hb0 : SigmaP3L q L (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P0 + al*e0 := by
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      σ hσre hσim
    have hz : (a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)) = ((al/a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a/L : ℝ)) : ℂ) := by
        have hcast : ((1 + a/L : ℝ) : ℂ) - 1 = (((1 + a/L) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * (L : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hLpos)
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)))).re = P0 := by
      rw [hz]; exact P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal, hP0def] using h
  -- (1) χ₁ at σ + iγ  (multiplicity ≥ 2 gives −2P₃(1))
  have hb1 : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al*(1/4 + e) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM _ hsre hsim
    have h3 : (2:ℝ) * P3R 1 ≤ P3NearSumL q L χ₁
        (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
        (γ' := 2 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).1
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- (2) χ₁² at σ + 2iγ  (the near sum `W`)
  have hb2 : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W + al*(1/4 + e) := by
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h1 := hpb q hqb (χ₁^2) (fun hcon => hχ2 hcon) hlam0 hlamM _ hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h1
    simpa [hWdef] using h1
  have hWnn : 0 ≤ W := by
    have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
      (γ' := 2 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).2 (χ₁^2)
      (fun hcon => hχ2 hcon)
      (by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]; linarith only [hγ1, hepos, he12])
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h
    simpa [hWdef] using h
  -- (3) χ₁³ = 1 at σ + 3iγ  (principal)
  have hb3 : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ Φa + al*e0 := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have hz : (a + lamOf q ρ₁) / (((σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1) * (L : ℂ))
        = (al : ℂ) / ((a : ℂ) + ((μ : ℝ) : ℂ) * Complex.I) := by
      have hσ3 : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
          = (((a / L : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ]; push_cast; ring
      have hL3 : (((((a / L : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I) * (L : ℂ))
          = ((a : ℂ) + (((3 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I) := by
        rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a (ne_of_gt hLpos)]
        rw [show ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I * (L : ℂ)
            = (((3 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [hσ3, hL3, hμ, hal, ← Complex.ofReal_add]
    rw [hz] at h
    simpa [hal, hχ3eq, hΦadef] using h
  by_cases hnear : ‖(1 : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ### NEAR branch: `2Φ(α,α,μ) ≤ W` dominates the pole term `Φ(α,a,μ)`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hxk := (hextra q hqx χ₁ ρ₁ hmin hZ hmult hχ3eq hδlam' hlamM).1 hnear
    have hxs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / (((↑a : ℂ) + ↑(lamOf q ρ₁))
        + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hxk' : 2 * Φ2 ≤ W := by
      rw [hxs, hxz] at hxk
      simpa [hWdef, hΦ2def] using hxk
    have hΦ2nn : 0 ≤ Φ2 := by
      rw [hΦ2def]
      exact P9.PhiG_nonneg (x := al) (y := al) (t := μ) halpos le_rfl
    have hdiv := P3_div_le (x := al) (y := a) (t := μ) ha hale
    have hΦale : Φa ≤ (al/a)^3 * Φ2 := by simpa [hΦadef, hΦ2def] using hdiv
    have hpair : (1/4) * Φa ≤ (K + 1/2) * W := by
      have hKd : Kond K ≤ 4*K := min_le_right _ _
      have h4 : (1/4)*(al/a)^3 ≤ 2*(K+1/2) := by linarith only [hcube, hKd, hK, hepos, he12]
      have h2 : (1/4) * Φa ≤ (1/4) * ((al/a)^3 * Φ2) :=
        mul_le_mul_of_nonneg_left hΦale (by norm_num)
      have h3 : (1/4) * ((al/a)^3 * Φ2) = ((1/4)*(al/a)^3) * Φ2 := by ring
      have h5 : ((1/4)*(al/a)^3) * Φ2 ≤ (2*(K+1/2)) * Φ2 :=
        mul_le_mul_of_nonneg_right h4 hΦ2nn
      have h7 : (K+1/2)*(2*Φ2) ≤ (K+1/2)*W :=
        mul_le_mul_of_nonneg_left hxk' (by linarith only [hK, hepos, he12])
      have h8 : (2*(K+1/2))*Φ2 = (K+1/2)*(2*Φ2) := by ring
      linarith only [h2, h3, h5, h7, h8, hdiv]
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith only [hK, hepos, he12]
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/4+e))
          + (K+1/2)*(-W + al*(1/4+e)) + (1/4)*(Φa + al*e0)
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
            + ((1/4)*Φa - (K+1/2)*W) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
          + ((1/4)*Φa - (K+1/2)*W) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge, inst, hcomb, hb3, hsum]
      linarith only [hlow, hpair, inst, hcomb, hb3, i0, i1, i2, hsum]
    have hcp : CN*(48*K) ≤ 12*K*S + S/2 := by
      have h1 : CN*(48*K) = 48*K*(K^2+K+1/2)*e0 + 48*K*((S-1/4)*(1/4+e))
          + 12*K*e0 := by rw [hCNdef]; ring
      have h2 : 48*K*(K^2+K+1/2)*e0 = 24*K*e*S := by
        linear_combination (48*K) * he0v
      have h3 : 12*K*e0 ≤ 12*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0les (show (0:ℝ) ≤ 12*K by positivity)
        have h' : (12:ℝ)*K*(e*S) = 12*K*e*S := by ring
        linarith only [h, h'.le, h'.ge]
      have h4 : 48*K*((S-1/4)*(1/4+e)) = 12*K*S + 48*K*e*S - 3*K - 12*K*e := by ring
      have h5 : (0:ℝ) ≤ 3*K + 12*K*e := by positivity
      have h6 : 24*K*e*S + (12*K*S + 48*K*e*S - 3*K - 12*K*e) + 12*K*e*S
          ≤ 12*K*S + 84*K*e*S := by linarith only [h5]
      have h7 : 12*K*S + 84*K*e*S ≤ 12*K*S + S/2 := by linarith only [h84, hepos, he12, h768, hSge]
      linarith only [h1.le, h1.ge, h2.le, h2.ge, h3, h4.le, h4.ge, h6, h7, hepos, he12, h768, hSge, h1, h2, h5]
    have hcp' : CN*(48*K) ≤ (12*K+1)*S := by
      have h8 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [hcp, h8.le, h8.ge, hSpos.le]
    exact ineq913_diag_of_derived_poly (a := a) (K := K) (C := CN) (ε := ε)
      (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcp' hD
  · -- ### FAR branch: `Φ(α,a,μ) ≤ e`, absorbed by the extra error `ex`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hfar := (hextra q hqx χ₁ ρ₁ hmin hZ hmult hχ3eq hδlam' hlamM).2 hnear
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / ((↑a : ℂ)
        + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hfar' : Φa ≤ e := by
      rw [hxz] at hfar
      simpa [hΦadef] using hfar
    have hexb : e/4 ≤ al*(ex*S) := by
      have h1 : al*(ex*S) = al*e/(4*a) := by
        rw [hexdef]
        first | (field_simp; ring) | field_simp | ring_nf
      have h2 : a*e/(4*a) = e/4 := by
        first | (field_simp; ring) | field_simp
      have h3 : a*e/(4*a) ≤ al*e/(4*a) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hale hepos.le) (by positivity)
      rw [h1, ← h2]
      exact h3
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*(CN + ex*S) := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith only [hK, hepos, he12]
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/4+e))
          + (K+1/2)*(-W + al*(1/4+e)) + (1/4)*(Φa + al*e0)
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
            + ((1/4)*Φa - (K+1/2)*W) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
          + ((1/4)*Φa - (K+1/2)*W) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge, inst, hcomb, hb3, hsum]
      have hdrop : (1/4)*Φa - (K+1/2)*W ≤ (1/4)*e := by
        have hW2 : (0:ℝ) ≤ (K+1/2)*W := mul_nonneg (by linarith only [hK, hepos, he12]) hWnn
        linarith only [hfar', hW2]
      have hsum2 : al*(CN + ex*S) = al*CN + al*(ex*S) := by ring
      rw [hsum2]
      linarith only [hlow, hdrop, hexb, inst, hcomb, hb3, i0, i1, i2, hsum]
    have hcp : CN*(48*K) ≤ 12*K*S + S/2 := by
      have h1 : CN*(48*K) = 48*K*(K^2+K+1/2)*e0 + 48*K*((S-1/4)*(1/4+e))
          + 12*K*e0 := by rw [hCNdef]; ring
      have h2 : 48*K*(K^2+K+1/2)*e0 = 24*K*e*S := by
        linear_combination (48*K) * he0v
      have h3 : 12*K*e0 ≤ 12*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0les (show (0:ℝ) ≤ 12*K by positivity)
        have h' : (12:ℝ)*K*(e*S) = 12*K*e*S := by ring
        linarith only [h, h'.le, h'.ge]
      have h4 : 48*K*((S-1/4)*(1/4+e)) = 12*K*S + 48*K*e*S - 3*K - 12*K*e := by ring
      have h5 : (0:ℝ) ≤ 3*K + 12*K*e := by positivity
      have h6 : 24*K*e*S + (12*K*S + 48*K*e*S - 3*K - 12*K*e) + 12*K*e*S
          ≤ 12*K*S + 84*K*e*S := by linarith only [h5]
      have h7 : 12*K*S + 84*K*e*S ≤ 12*K*S + S/2 := by linarith only [h84, hepos, he12, h768, hSge]
      linarith only [h1.le, h1.ge, h2.le, h2.ge, h3, h4.le, h4.ge, h6, h7, hepos, he12, h768, hSge, h1, h2, h5]
    have hcf : (CN + ex*S)*(48*K) ≤ (12*K+1)*S := by
      have h1 : (CN + ex*S)*(48*K) = CN*(48*K) + 48*K*(ex*S) := by ring
      have h2 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [h1.le, h1.ge, hcp, hexSp, h2.le, h2.ge]
    exact ineq913_diag_of_derived_poly (a := a) (K := K) (C := CN + ex*S) (ε := ε)
      (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcf hD


/-- **Order-2 case**: `χ₁² = 1`, `ρ₁.im ≠ 0`. -/
theorem order2_case_prim {a K ε : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
      χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
      ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε := by
  set S : ℝ := K^2 + 3*K + 3/2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (min (1/(768*K)) (1/12))
      (min (29*a*S/(768*K)) (a*S/(96*K*(K+1/2)))) with hedef
  have hepos : 0 < e := by
    rw [hedef]
    exact lt_min (lt_min (by positivity) (by norm_num))
      (lt_min (by positivity) (by positivity))
  have heA : e ≤ min (1/(768*K)) (1/12) := min_le_left _ _
  have heB : e ≤ min (29*a*S/(768*K)) (a*S/(96*K*(K+1/2))) := min_le_right _ _
  have he1 : e ≤ 1/(768*K) := le_trans heA (min_le_left _ _)
  have he12 : e ≤ 1/12 := le_trans heA (min_le_right _ _)
  have he4 : e ≤ a*S/(96*K*(K+1/2)) := le_trans heB (min_le_right _ _)
  set e0 : ℝ := e * S / (2*(K^2+K+1/2)) with he0def
  have he0pos : 0 < e0 := by rw [he0def]; positivity
  have he0le : e0 ≤ 3*e/2 := by
    rw [he0def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K^2+K+1/2))]
    have h1 : K^2 + 3*K + 3/2 ≤ 3*(K^2+K+1/2) := by linarith only [sq_nonneg K, hK]
    have h2 : e * (K^2 + 3*K + 3/2) ≤ e * (3*(K^2+K+1/2)) :=
      mul_le_mul_of_nonneg_left h1 hepos.le
    have h3 : (3*e/2) * (2*(K^2+K+1/2)) = e * (3*(K^2+K+1/2)) := by ring
    rw [hSdef]
    linarith only [h2, h3.le, h3.ge]
  have he0quarter : e0 ≤ 1/4 + e := by linarith only [he0le, he12, hepos]
  -- polynomial forms of the size conditions
  have he1' : 768*K*e ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left he1 (by positivity : (0:ℝ) ≤ 768*K)
    have h2 : (768*K)*(1/(768*K)) = 1 := by
      field_simp
    linarith only [h, h2.le, h2.ge, h2]
  have h768 : 768*K*e*S ≤ S := by
    have h := mul_le_mul_of_nonneg_right he1' hSpos.le
    simpa using h
  have h24 : 24*K*e*S ≤ S/32 := by
    have h1 : 24*K*e*S = (24/768)*(768*K*e*S) := by ring
    have h2 : (24/768)*(768*K*e*S) ≤ (24/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (24/768)*S = S/32 := by ring
    linarith only [h1.le, h1.ge, h2, h3.le, h3.ge, h768]
  have h48 : 48*K*e*S ≤ S/16 := by
    have h1 : 48*K*e*S = (48/768)*(768*K*e*S) := by ring
    have h2 : (48/768)*(768*K*e*S) ≤ (48/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (48/768)*S = S/16 := by ring
    linarith only [h1.le, h1.ge, h2, h3.le, h3.ge, h768]
  have he0v : (K^2+K+1/2)*e0 = e*S/2 := by
    first | (rw [he0def]; field_simp; ring) | (rw [he0def]; field_simp)
  have hA2e0 : (K+1/2)*e0 ≤ e*S := by
    have hK1 : K + 1/2 ≤ 2*(K^2+K+1/2) := by linarith only [sq_nonneg K, hK, hepos, he12]
    have h1 : (K+1/2)*e0 ≤ (2*(K^2+K+1/2))*e0 :=
      mul_le_mul_of_nonneg_right hK1 he0pos.le
    have h2 : (2*(K^2+K+1/2))*e0 = e*S := by linarith only [he0v]
    linarith only [h1, h2.le, h2.ge, he0v]
  have hA1e : 48*K*((K^2+2*K+3/4)*e) ≤ (K^2+2*K+3/4)/16 := by
    have h := mul_le_mul_of_nonneg_left he1' (by positivity : (0:ℝ) ≤ K^2+2*K+3/4)
    have h2 : 48*K*((K^2+2*K+3/4)*e) = ((K^2+2*K+3/4)*(768*K*e))/16 := by ring
    linarith only [h, h2.le, h2.ge]
  have h12e : 12*K*e ≤ 1/64 := by
    have h1 : 12*K*e = (12/768)*(768*K*e) := by ring
    have h2 : (12/768)*(768*K*e) ≤ (12/768)*1 :=
      mul_le_mul_of_nonneg_left he1' (by norm_num)
    have h3 : (12/768)*1 = 1/64 := by norm_num
    linarith only [h1.le, h1.ge, h2, h3.le, h3.ge, he1']
  have hSge : (3:ℝ)/2 ≤ S := by rw [hSdef]; linarith only [sq_nonneg K, hK.le]
  set ex : ℝ := (K+1/2)*e/(a*S) with hexdef
  have hexle : ex ≤ 1/(96*K) := by
    rw [hexdef, div_le_iff₀ (by positivity : (0:ℝ) < a*S)]
    have h1 : (K+1/2)*e ≤ (K+1/2)*(a*S/(96*K*(K+1/2))) :=
      mul_le_mul_of_nonneg_left he4 (by linarith only [hK, hepos, he12])
    have h2 : (K+1/2)*(a*S/(96*K*(K+1/2))) = (1/(96*K))*(a*S) := by
      first | (field_simp; ring) | field_simp
    linarith only [h1, h2.le, h2.ge, h2]
  have hexSp : 48*K*(ex*S) ≤ S/2 := by
    have h := mul_le_mul_of_nonneg_right hexle hSpos.le
    have h4 : 48*K*(ex*S) ≤ 48*K*((1/(96*K))*S) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 48*K*((1/(96*K))*S) = S/2 := by
      first | (field_simp; ring) | field_simp
    linarith only [h4, h2.le, h2.ge, h2]
  set C2 : ℝ := (K^2+K+1/2)*e0 + (K^2+2*K+3/4)*(1/4+e) + (K+1/2)*e0
      + (1/4)*(1/4+e) with hC2def
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (le_of_lt ha) (by linarith only [Kond_pos hK, hepos, he12, hK])
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ := pointBound (a := a) (e := e) (M := M) ha hepos hMnn
  obtain ⟨L₀p, hprinc⟩ := principalBoundAmended (a := a) (e := e0) (M := M) ha he0pos
  obtain ⟨q₀c, hnearC⟩ := caseC_near (a := a) (δ := δ) ha hδ0 hδ1
  obtain ⟨q₀f, hfarC⟩ := caseC_far (a := a) (δ := δ) (e := e) (M := M) ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max (max q₀b q₀c) q₀f) (max (max (Nat.ceil (Real.exp L₀p))
      (Nat.ceil (Real.exp (max (M/δ) 10)))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hmin hZ hmult hsq him hcond
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hqb : q₀b ≤ q := by omega
  have hqc : q₀c ≤ q := by omega
  have hqf : q₀f ≤ q := by omega
  have hLp : L₀p ≤ L := by
    have hce : Nat.ceil (Real.exp L₀p) ≤ q := by omega
    have hexp : Real.exp L₀p ≤ (q:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
    rw [hLdef]
    calc L₀p = Real.log (Real.exp L₀p) := (Real.log_exp L₀p).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hLnb : Real.exp (max (M/δ) 10) ≤ (q:ℝ) := by
    have h2 : (Nat.ceil (Real.exp (max (M/δ) 10)) : ℝ) ≤ (q:ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max (M/δ) 10)) ≤ q)
    exact le_trans (Nat.le_ceil _) h2
  have hMδ : M/δ ≤ L := by
    rw [hLdef]
    calc M/δ ≤ max (M/δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * L := by
    have h' : M/δ ≤ L := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith only [h']
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.P9.lamOf_nonneg hZ
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]; exact lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / L ≤ δ := by
    rw [div_le_iff₀ hLpos]; exact le_trans hlamM hMlt
  have hγ1 : |ρ₁.im| ≤ 1 := hZ.2.2
  have hχ1ne : χ₁ ≠ 1 := hZ.1
  have hcube := cond913_cube_le (a := a) (K := K) (lam := lamOf q ρ₁) ha hlam0 hcond
  have hχ3ne : χ₁^3 ≠ 1 := by
    intro hcon
    exact hχ1ne (by
      have h2 : χ₁^3 = χ₁^2 * χ₁ := by
        rw [show (3:ℕ) = 2+1 from rfl, pow_succ]
      rw [h2, hsq, one_mul] at hcon
      exact hcon)
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith only [ha, hlam0]
  have hale : a ≤ al := by rw [hal]; linarith only [hlam0]
  set σ : ℂ := ((1 + a / L : ℝ) : ℂ) with hσ
  set μ : ℝ := 2 * ρ₁.im * L with hμ
  set P0 : ℝ := P3R (al/a) with hP0def
  set Ψ : ℝ := (P3 ((al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I))).re with hΨdef
  set Φ2 : ℝ := (P3 ((al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I))).re with hΦ2def
  set W1 : ℝ := P3NearSumL q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ
    with hW1def
  set W3 : ℝ := P3NearSumL q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ
    with hW3def
  have hcomb := combination_diag (q := q) χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K)
    hq2 ha hK hγ1 hlam0 hχ1ne
  have hσeq : (((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) = σ := by rw [hσ, hLdef]
  have hcomb' := hcomb
  rw [hσeq] at hcomb'
  have hσre : σ.re = 1 + a/L := by rw [hσ]; simp
  have hσim : |σ.im| ≤ 4 := by rw [hσ]; simp
  -- (0) principal character at σ
  have hb0 : SigmaP3L q L (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P0 + al*e0 := by
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      σ hσre hσim
    have hz : (a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)) = ((al/a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a/L : ℝ)) : ℂ) := by
        have hcast : ((1 + a/L : ℝ) : ℂ) - 1 = (((1 + a/L) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * (L : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hLpos)
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)))).re = P0 := by
      rw [hz]; exact P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal, hP0def] using h
  -- (1) χ₁ at σ + iγ  (near sum `W1`)
  have hb1w : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W1 + al*(1/4 + e) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM _ hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h1
    simpa [hW1def] using h1
  have hb1 : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al*(1/4 + e) := by
    have h3 : (2:ℝ) * P3R 1 ≤ W1 := by
      have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
        (γ' := 2 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).1
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      simpa [hW1def] using h
    linarith only [hb1w, h3, inst]
  have hW1nn : 0 ≤ W1 := by
    have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
      (γ' := ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).2 χ₁ hχ1ne
      (by linarith only [hγ1, hepos, he12])
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h
    simpa [hW1def] using h
  -- (2) χ₁² = 1 at σ + 2iγ  (principal, pole at distance `a + iμ`)
  have hb2 : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ Ψ + al*e0 := by
    rw [hsq]
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have hz : (a + lamOf q ρ₁) / (((σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1) * (L : ℂ))
        = (al : ℂ) / ((a : ℂ) + ((μ : ℝ) : ℂ) * Complex.I) := by
      have hσ2' : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
          = (((a / L : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ]; push_cast; ring
      have hL2 : (((((a / L : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) * (L : ℂ))
          = ((a : ℂ) + (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I) := by
        rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a (ne_of_gt hLpos)]
        rw [show ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I * (L : ℂ)
            = (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [hσ2', hL2, hμ, hal, ← Complex.ofReal_add]
    rw [hz] at h
    simpa [hal, hΨdef] using h
  -- (3) χ₁³ = χ₁ at σ + 3iγ  (near sum `W3`)
  have hb3 : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W3 + al*(1/4 + e) := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by
      rw [hσ]; simp
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 4 := by
      simp [hσ, Complex.add_im, Complex.mul_im]; linarith only [hγ1, hepos, he12]
    have h1 := hpb q hqb (χ₁^3) (fun hcon => hχ3ne hcon) hlam0 hlamM _ hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h1
    simpa [hW3def] using h1
  have hW3nn : 0 ≤ W3 := by
    have h := (nearSum_bounds (q := q) (χ₁ := χ₁) (ρ₁ := ρ₁) (a := a) (δ := δ)
      (γ' := 3 * ρ₁.im) hq2 hmin hZ hmult ha hδ0 hδ1 hδlam).2 (χ₁^3)
      (fun hcon => hχ3ne hcon)
      (by rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)]; linarith only [hγ1, hepos, he12])
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h
    simpa [hW3def] using h
  by_cases hnear : ‖(1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ### NEAR branch: the conjugate zero dominates `Σ(σ+iγ,χ₁)`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hnc := hnearC q hqc χ₁ ρ₁ hmin hZ hmult hsq him hδlam' hnear
    have hxs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / (((↑a : ℂ) + ↑(lamOf q ρ₁))
        + ((2 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hnc' : (2:ℝ) * P3R 1 + 2 * Φ2 ≤ W1 := by
      rw [hxs, hxz] at hnc
      simpa [hW1def, hΦ2def] using hnc
    have hb1' : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ -(2 * P3R 1) - 2 * Φ2 + al*(1/4 + e) := by linarith only [hb1w, hnc', inst]
    have hΦ2nn : 0 ≤ Φ2 := by
      rw [hΦ2def]
      exact P9.PhiG_nonneg (x := al) (y := al) (t := μ) halpos le_rfl
    have hΨle : Ψ ≤ (al/a)^3 * Φ2 := by
      exact (by simpa [hΨdef, hΦ2def] using P3_div_le (x := al) (y := a) (t := μ) ha hale)
    have hpair : (K+1/2)*Ψ ≤ 2*(K^2+2*K+3/4)*Φ2 := by
      have hKd : (K+1/2)*(Kond K+1) ≤ 2*(K^2+2*K+3/4) := A2_mul_Kond_le hK
      have h1 : (K+1/2)*((al/a)^3) ≤ (K+1/2)*(Kond K+1) :=
        mul_le_mul_of_nonneg_left hcube (by linarith only [hK, hepos, he12])
      calc (K+1/2)*Ψ ≤ (K+1/2)*((al/a)^3 * Φ2) :=
            mul_le_mul_of_nonneg_left hΨle (by linarith only [hK, hepos, he12])
        _ = ((K+1/2)*((al/a)^3)) * Φ2 := by ring
        _ ≤ ((K+1/2)*(Kond K+1)) * Φ2 := mul_le_mul_of_nonneg_right h1 hΦ2nn
        _ ≤ (2*(K^2+2*K+3/4)) * Φ2 := mul_le_mul_of_nonneg_right hKd hΦ2nn
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith only [hK, hepos, he12]
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1' hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0)
          + (K^2+2*K+3/4)*(-(2*P3R 1) - 2*Φ2 + al*(1/4+e))
          + (K+1/2)*(Ψ + al*e0) + (1/4)*(-W3 + al*(1/4+e))
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2
            + ((K+1/2)*Ψ - 2*(K^2+2*K+3/4)*Φ2 - (1/4)*W3) := by
        rw [hC2def]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2
          + ((K+1/2)*Ψ - 2*(K^2+2*K+3/4)*Φ2 - (1/4)*W3) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      linarith only [hlow, hpair, hW3nn]
    have hcp : C2*(48*K) ≤ 12*K*S + S/2 := by
      have h1 : C2*(48*K) = 48*K*((K^2+K+1/2)*e0) + 48*K*((K^2+2*K+3/4)*(1/4+e))
          + 48*K*((K+1/2)*e0) + 48*K*((1/4)*(1/4+e)) := by rw [hC2def]; ring
      have h2 : 48*K*((K^2+K+1/2)*e0) = 24*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0v.le (show (0:ℝ) ≤ 48*K by positivity)
        have h' := mul_le_mul_of_nonneg_left he0v.ge (show (0:ℝ) ≤ 48*K by positivity)
        linarith only [h, h']
      have h3 : 48*K*((K^2+2*K+3/4)*(1/4+e))
          = 12*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e) := by ring
      have h4 : 48*K*((K+1/2)*e0) ≤ 48*K*(e*S) :=
        mul_le_mul_of_nonneg_left hA2e0 (by positivity)
      have h5 : 48*K*((1/4)*(1/4+e)) = 3*K + 12*K*e := by ring
      have h6 : 12*K*S = 12*K*(K^2+2*K+3/4) + 12*K*(K+3/4) := by rw [hSdef]; ring
      have h7 : 24*K*e*S + (12*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e))
          + 48*K*(e*S) + (3*K + 12*K*e) ≤ 12*K*S + S/2 := by
        have hA : 12*K*(K+3/4) + 13*S/32 ≥ (K^2+2*K+3/4)/16 + 3*K + 1/64 := by
          rw [hSdef]; linarith only [sq_nonneg K, hK]
        have h32 : S/2 - 3*S/32 = 13*S/32 := by ring
        linarith only [hA, h32.le, h32.ge, h6, h24, h48, hA1e, h12e]
      linarith only [h1.le, h1.ge, h2.le, h2.ge, h3.le, h3.ge, h4, h5.le, h5.ge, h7]
    have hcp' : C2*(48*K) ≤ (12*K+1)*S := by
      have h8 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [hcp, h8.le, h8.ge, hSpos.le]
    exact ineq913_diag_of_derived_poly (a := a) (K := K) (C := C2) (ε := ε)
      (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcp' hD
  · -- ### FAR branch: the pole term `Ψ ≤ e` is absorbed by the extra error `ex`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hfar := hfarC q hqf χ₁ ρ₁ hZ hlamM him hnear
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / ((↑a : ℂ)
        + ((2 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hfar' : Ψ ≤ e := by
      rw [hxz] at hfar
      simpa [hΨdef] using hfar
    have hb2' : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ e + al*e0 := by linarith only [hb2, hfar', inst]
    have hb3' : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ 0 + al*(1/4 + e) := by linarith only [hb3, hW3nn, inst]
    have hexb : (K+1/2)*e ≤ al*(ex*S) := by
      have h1 : al*(ex*S) = al*(K+1/2)*e/a := by
        rw [hexdef]
        first | (field_simp; ring) | field_simp | ring_nf
      have h3a : a*(K+1/2)*e ≤ al*(K+1/2)*e := by
        have h := mul_le_mul_of_nonneg_right hale (show (0:ℝ) ≤ K+1/2 by linarith only [hK, hepos, he12])
        have h' := mul_le_mul_of_nonneg_right h hepos.le
        linarith only [h']
      have h3 : a*(K+1/2)*e/a ≤ al*(K+1/2)*e/a :=
        div_le_div_of_nonneg_right h3a ha.le
      have h2 : a*(K+1/2)*e/a = (K+1/2)*e := by
        first | (field_simp; ring) | field_simp
      rw [h1, ← h2]
      exact h3
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*(C2 + ex*S) := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith only [hK, hepos, he12]
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2' hA2
      have i3 := mul_le_mul_of_nonneg_left hb3' hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/4+e))
          + (K+1/2)*(e + al*e0) + (1/4)*(0 + al*(1/4+e))
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 + (K+1/2)*e := by
        rw [hC2def]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 + (K+1/2)*e := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      have hsum2 : al*(C2 + ex*S) = al*C2 + al*(ex*S) := by ring
      rw [hsum2]
      linarith only [hlow, hexb]
    have hcp : C2*(48*K) ≤ 12*K*S + S/2 := by
      have h1 : C2*(48*K) = 48*K*((K^2+K+1/2)*e0) + 48*K*((K^2+2*K+3/4)*(1/4+e))
          + 48*K*((K+1/2)*e0) + 48*K*((1/4)*(1/4+e)) := by rw [hC2def]; ring
      have h2 : 48*K*((K^2+K+1/2)*e0) = 24*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0v.le (show (0:ℝ) ≤ 48*K by positivity)
        have h' := mul_le_mul_of_nonneg_left he0v.ge (show (0:ℝ) ≤ 48*K by positivity)
        linarith only [h, h']
      have h3 : 48*K*((K^2+2*K+3/4)*(1/4+e))
          = 12*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e) := by ring
      have h4 : 48*K*((K+1/2)*e0) ≤ 48*K*(e*S) :=
        mul_le_mul_of_nonneg_left hA2e0 (by positivity)
      have h5 : 48*K*((1/4)*(1/4+e)) = 3*K + 12*K*e := by ring
      have h6 : 12*K*S = 12*K*(K^2+2*K+3/4) + 12*K*(K+3/4) := by rw [hSdef]; ring
      have h7 : 24*K*e*S + (12*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e))
          + 48*K*(e*S) + (3*K + 12*K*e) ≤ 12*K*S + S/2 := by
        have hA : 12*K*(K+3/4) + 13*S/32 ≥ (K^2+2*K+3/4)/16 + 3*K + 1/64 := by
          rw [hSdef]; linarith only [sq_nonneg K, hK]
        have h32 : S/2 - 3*S/32 = 13*S/32 := by ring
        linarith only [hA, h32.le, h32.ge, h6, h24, h48, hA1e, h12e]
      linarith only [h1.le, h1.ge, h2.le, h2.ge, h3.le, h3.ge, h4, h5.le, h5.ge, h7]
    have hcf : (C2 + ex*S)*(48*K) ≤ (12*K+1)*S := by
      have h1 : (C2 + ex*S)*(48*K) = C2*(48*K) + 48*K*(ex*S) := by ring
      have h2 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [h1.le, h1.ge, hcp, hexSp, h2.le, h2.ge]
    exact ineq913_diag_of_derived_poly (a := a) (K := K) (C := C2 + ex*S) (ε := ε)
      (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcf hD

/-- **The target** from the three cases. -/
theorem HBLemma9_1_rep_of_cases
    (hgen : ∀ a K ε : ℝ, 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
        χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 ≠ 1 → cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
        ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε)
    (h3 : ∀ a K ε : ℝ, 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
        χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 = 1 → cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
        ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε)
    (h2 : ∀ a K ε : ℝ, 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → 2 ≤ zeroMult χ₁ ρ₁ →
        χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → cond913 (lamOf q ρ₁) (lamOf q ρ₁) a K →
        ineq913 (lamOf q ρ₁) (lamOf q ρ₁) a K ε) :
    HBLemma9_1_rep := by
  unfold HBLemma9_1_rep
  intro a K ε ha hK hε
  obtain ⟨q₁, hq₁⟩ := hgen a K ε ha hK hε
  obtain ⟨q₃, hq₃⟩ := h3 a K ε ha hK hε
  obtain ⟨q₂, hq₂⟩ := h2 a K ε ha hK hε
  refine ⟨max (max q₁ q₃) q₂, ?_⟩
  intro q hq inst χ₁ ρ₁ hmin hnot hZ hmult hcond
  have hle1 : q₁ ≤ q := by omega
  have hle3 : q₃ ≤ q := by omega
  have hle2 : q₂ ≤ q := by omega
  by_cases hχ2 : χ₁ ^ 2 = 1
  · have him : ρ₁.im ≠ 0 := by
      intro h0
      exact hnot ⟨hχ2, h0⟩
    exact hq₂ q hle2 χ₁ ρ₁ hmin hZ hmult hχ2 him hcond
  · by_cases hχ3 : χ₁ ^ 3 = 1
    · exact hq₃ q hle3 χ₁ ρ₁ hmin hZ hmult hχ2 hχ3 hcond
    · exact hq₁ q hle1 χ₁ ρ₁ hmin hZ hmult hχ2 hχ3 hcond


end Work.ZeroFreeTables.Rep9
