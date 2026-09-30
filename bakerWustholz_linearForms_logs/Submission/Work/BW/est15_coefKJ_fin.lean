import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.finitePlace_basic
import Submission.Work.BW.posLog_w_prod_zpow_le
import Submission.Work.BW.auxIdx_div_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `Real.log x ≤ Real.posLog x` for every real `x` (`posLog` is `max 0 (log ·)`). -/
lemma log_le_posLog_fin (x : ℝ) : Real.log x ≤ Real.posLog x := by
  rw [Real.posLog_apply]; exact le_max_right _ _

/-- Splitting `log` over a product of a finite place's values.  If `B` and `C` are nonnegative
and dominate `log (w a)` resp. `log⁺ (w b)`, then `log (w (a * b)) ≤ B + C`.  This is the form
that survives `w a = 0` or `w b = 0` (where `Real.log 0 = 0` and the nonnegativity of `B`, `C`
takes over). -/
lemma log_w_mul_le_fin {K : Type*} [Field K] [NumberField K]
    (w : NumberField.FinitePlace K) (a b : K) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : Real.log (w a) ≤ B) (hb : Real.posLog (w b) ≤ C) :
    Real.log (w (a * b)) ≤ B + C := by
  rw [map_mul]
  rcases eq_or_ne (w a) 0 with h | h
  · rw [h, zero_mul, Real.log_zero]; linarith
  rcases eq_or_ne (w b) 0 with h' | h'
  · rw [h', mul_zero, Real.log_zero]; linarith
  · rw [Real.log_mul h h']
    have hl : Real.log (w b) ≤ Real.posLog (w b) := log_le_posLog_fin _
    linarith

/-- The Kummer term `estCf` is nonnegative: `2Jh(D₀+1) ≥ 0` and `-log (w 2) ≥ 0`
because `0 < w 2 ≤ 1` for a finite place. -/
lemma estCf_nonneg {K : Type*} [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ)
    (σ : Fin r → ℝ) (J : ℕ) (w : NumberField.FinitePlace K) : 0 ≤ estCf K b v σ J w := by
  obtain ⟨h2pos, h2le, -, -, -⟩ := finitePlace_basic (K := K) w
  have hlog : Real.log (w (2 : K)) ≤ 0 := Real.log_nonpos h2pos.le h2le
  rw [estCf]
  refine mul_nonneg (by positivity) ?_
  linarith

/-- The `α'`-monomial term `estMon` is nonnegative. -/
lemma estMon_nonneg_fin {K : Type*} [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ)
    (β : Fin r → K) (J : ℕ) (s : ℤ) (w : K → ℝ) : 0 ≤ estMon K σ β J s w := by
  rw [estMon]
  refine mul_nonneg (div_nonneg ?_ (by positivity))
    (Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) Real.posLog_nonneg)
  exact_mod_cast abs_nonneg s

theorem est15_coefKJ_fin {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (w : NumberField.FinitePlace K)
    (hfin : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      Real.log (w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
        ≤ estCf K b v σ J w)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    Real.log (w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
      ≤ estCf K b v σ J w + estMon K σ (fun j => estBeta s (α' j)) J s w := by
  classical
  rw [coefKJ_eq_coefPart_mul]
  refine log_w_mul_le_fin w _ _ (estCf_nonneg b v σ J w)
    (estMon_nonneg_fin σ (fun j => estBeta s (α' j)) J s w) (hfin lm) ?_
  rw [estMon]
  exact posLog_w_prod_zpow_le w α' s J (fun j => (lm.2.2 j : ℕ) / 2 ^ J) (pDj r (dK K) σ)
    (fun j => auxIdx_div_pow_le lm J j)

end Work.BW
