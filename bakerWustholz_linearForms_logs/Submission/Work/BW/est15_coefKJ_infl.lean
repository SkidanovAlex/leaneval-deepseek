import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.thetaRatQ_log_le
import Submission.Work.BW.acH_lower
import Submission.Work.BW.log_infinitePlace_zpow_le
import Submission.Work.BW.estPi_bound_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW (15) at descent level `J`: the Archimedean (`estCi`/`estMon`) inflation of `coefKJ`

This file bounds `log |coefKJ … λ|_w` at an *infinite* place `w` by the `w`-independent
`Π`/`u`/`Θ` contribution `estCi` plus the explicit `α'`-monomial contribution `estMon`.

Since `coefKJ = (Π(λ):K) · u(h)^{t₀} · (Θ(λ):K) · ∏_j (α'_j)^{s⌊λ_j/2^J⌋}`, the whole content is
that `log` of a product is at most the sum of the bounds of the factors, *with nonnegative*
bounds (so that vanishing factors cause no trouble), together with
* the `Θ`-bound `thetaJ_infl_log_le` and
* the monomial bound `log_infinitePlace_zpow_le`.

-/


namespace Work.BW

open NumberField

/-- `log x ≤ log y` whenever `0 ≤ x`, `1 ≤ y` and `x ≤ y`.  (The `0 < x` case is
`Real.log_le_log`; the vanishing case is the trivial `0 ≤ log y`.) -/
lemma log_le_log_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.log_zero]; exact Real.log_nonneg hy
  · exact Real.log_le_log h hxy

/-- From `0 ≤ x` and `log x ≤ A` conclude `x ≤ exp A`. -/
lemma le_exp_of_log_le {x A : ℝ} (hx : 0 ≤ x) (h : Real.log x ≤ A) : x ≤ Real.exp A := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0] at h ⊢; exact le_of_lt (Real.exp_pos A)
  · rw [← Real.exp_log h0]; exact Real.exp_le_exp.mpr h

/-- Comparison of finite products of nonnegative reals (the `MulLeftMono`-instance is absent for
`ℝ`, so we do the induction by hand). -/
lemma prod_le_prod_real {ι : Type*} {x y : ι → ℝ} {s : Finset ι}
    (hx : ∀ i ∈ s, 0 ≤ x i) (h : ∀ i ∈ s, x i ≤ y i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∏ i ∈ s, x i ≤ ∏ i ∈ s, y i := by
  classical
  revert hx h hy
  induction s using Finset.induction with
  | empty => intro; simp
  | insert a s ha ih =>
    intro hx h hy
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))
          (fun i hi => hy i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (hy a (Finset.mem_insert_self a s))

/-- `log |ab|_w ≤ A + B` from `log |a|_w ≤ A`, `log |b|_w ≤ B` and `0 ≤ A`, `0 ≤ B`.  The
nonnegativity of the bounds is exactly what makes this valid also when a factor vanishes. -/
lemma log_w_mul_le {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K) {a b : K} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : Real.log (w a) ≤ A) (hb : Real.log (w b) ≤ B) :
    Real.log (w (a * b)) ≤ A + B := by
  have hxa : w a ≤ Real.exp A := le_exp_of_log_le (w.1.nonneg a) ha
  have hxb : w b ≤ Real.exp B := le_exp_of_log_le (w.1.nonneg b) hb
  have hmul : w a * w b ≤ Real.exp (A + B) := by
    have h := mul_le_mul hxa hxb (w.1.nonneg b) (le_of_lt (Real.exp_pos A))
    rwa [← Real.exp_add] at h
  rw [show w (a * b) = w a * w b by simpa using AbsoluteValue.map_mul w.1 a b]
  have hthis := log_le_log_of_nonneg (mul_nonneg (w.1.nonneg a) (w.1.nonneg b))
    (Real.one_le_exp (by linarith)) hmul
  simpa only [InfinitePlace.coe_apply, Real.log_exp] using hthis

/-- The finite-product version of `log_w_mul_le`. -/
lemma log_w_fintype_prod_le {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    {ι : Type*} [Fintype ι] (f : ι → K) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hf : ∀ i, Real.log (w (f i)) ≤ B i) :
    Real.log (w (∏ i, f i)) ≤ ∑ i, B i := by
  have hprod : w (∏ i, f i) = ∏ i, w (f i) := by
    simpa using AbsoluteValue.map_prod w.1 f Finset.univ
  have hxy : ∏ i, w (f i) ≤ ∏ i, Real.exp (B i) :=
    prod_le_prod_real (fun i _ => w.1.nonneg (f i))
      (fun i _ => le_exp_of_log_le (w.1.nonneg (f i)) (hf i))
      (fun i _ => le_of_lt (Real.exp_pos (B i)))
  have hexp : (∏ i, Real.exp (B i)) = Real.exp (∑ i, B i) := by
    rw [Real.exp_sum]
  rw [hprod]
  have hthis := log_le_log_of_nonneg (Finset.prod_nonneg fun i _ => w.1.nonneg (f i))
    (Real.one_le_exp (Finset.sum_nonneg fun i _ => hB i)) (hxy.trans (le_of_eq hexp))
  simpa only [InfinitePlace.coe_apply, Real.log_exp] using hthis

/-- `1 ≤ u(k) = lcm(1,…,k)`. -/
lemma one_le_ulcm (k : ℕ) : 1 ≤ ulcm k := by
  have hne : ulcm k ≠ 0 := by
    rw [ulcm, Finset.lcm_ne_zero_iff]
    intro x _; omega
  omega

/-- `1 ≤ μ = 57 r d`. -/
lemma mu57_ge_one {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r) :
    1 ≤ mu57 K r := by
  have hd : 1 ≤ dK K := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    simp only [dK]
    omega
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  rw [mu57]
  nlinarith [hr2, hd1]

/-- `estMon` is always nonnegative. -/
lemma estMon_nonneg {K : Type*} [Field K] [NumberField K] {r : ℕ} (σ : Fin r → ℝ)
    (β : Fin r → K) (J : ℕ) (s : ℤ) (w : InfinitePlace K) :
    0 ≤ estMon K σ β J s w := by
  rw [estMon]
  apply mul_nonneg
  · refine div_nonneg ?_ (by positivity)
    rw [Int.cast_abs]
    exact abs_nonneg _
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg

theorem est15_coefKJ_infl {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℤ)
    (w : NumberField.InfinitePlace K)
    (hPi : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      Real.log (w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K)))
        ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)))
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    Real.log (w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
      ≤ estCi K b v σ J t0 t s + estMon K σ (fun j => estBeta s (α' j)) J s w := by
  classical
  -- ### nonnegativity of the four bound-pieces
  have hnPi : 0 ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)) :=
    estPi_bound_nonneg H t
  have hnU : 0 ≤ (t0 : ℝ) * Real.log (ulcm (acH K b v)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast one_le_ulcm _))
  have hnMu : 1 ≤ mu57 K r := mu57_ge_one H.hr
  have hmu_pos : 0 < mu57 K r := lt_of_lt_of_le zero_lt_one hnMu
  have hlogmu : 0 ≤ Real.log (mu57 K r) := Real.log_nonneg hnMu
  have hX : 0 ≤ 1 + Real.log (mu57 K r) + 1 / mu57 K r := by
    have := one_div_pos.mpr hmu_pos
    linarith
  have hnθ : 0 ≤ ((acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1)) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r)
        + ((((lm.2.1 : ℕ) : ℝ) + 1)) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| / mu57 K r := by
    apply add_nonneg
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hX
    · exact div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hmu_pos.le
  have hnMono : 0 ≤ estMon K σ (fun j => estBeta s (α' j)) J s w :=
    estMon_nonneg σ (fun j => estBeta s (α' j)) J s w
  -- ### bounds for the four factor groups
  have hA_le : Real.log (w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
        t lm : ℚ) : K))) ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)) :=
    hPi lm
  have hU0 : w (((ulcm (acH K b v) : ℚ) : K)) = (ulcm (acH K b v) : ℝ) := by
    rw [Rat.cast_natCast]
    exact InfinitePlace.map_natCast w _
  have hU_le : Real.log (w ((((ulcm (acH K b v) : ℚ) : K)) ^ t0))
      ≤ (t0 : ℝ) * Real.log (ulcm (acH K b v)) := by
    have hp : w ((((ulcm (acH K b v) : ℚ) : K)) ^ t0)
        = (w (((ulcm (acH K b v) : ℚ) : K))) ^ t0 := by
      simpa using map_pow w.1 (((ulcm (acH K b v) : ℚ) : K)) t0
    rw [hp, hU0, Real.log_pow]
  have hC_le : Real.log (w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
        J t0 s lm : ℚ) : K)))
      ≤ ((acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1)) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r)
        + ((((lm.2.1 : ℕ) : ℝ) + 1)) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| / mu57 K r := by
    -- `k = h ≥ 1` (`acH_lower`), the `w`-value is the complex norm of the rational `Θ`
    have hh1 : 1 ≤ acH K b v := by have := (acH_lower H).1; omega
    have hbridge : w (((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)
          J t0 s lm : ℚ) : K))
        = ‖((thetaJ (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 s lm : ℚ) : ℂ)‖ := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.apply]
      congr 1
      exact map_ratCast w.embedding _
    rw [hbridge, thetaJ]
    have hmain := thetaRatQ_log_le (acH K b v) hh1 ((lm.2.1 : ℕ) + 1) t0
      ((s : ℚ) / (2 : ℚ) ^ J + ((lm.1 : ℕ) : ℚ)) (mu57 K r) hnMu
    have hl : ((((lm.2.1 : ℕ) + 1 : ℕ)) : ℝ) = ((lm.2.1 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hx : ((((s : ℚ) / (2 : ℚ) ^ J + ((lm.1 : ℕ) : ℚ) : ℚ)) : ℝ)
        = (s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ) := by push_cast; ring
    rw [hl, hx] at hmain
    exact hmain
  have hD_le : Real.log (w (∏ j : Fin r, (α' j) ^ (s * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℤ))))
      ≤ estMon K σ (fun j => estBeta s (α' j)) J s w := by
    rw [estMon, Finset.mul_sum]
    refine log_w_fintype_prod_le w
      (fun j : Fin r => (α' j) ^ (s * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℤ)))
      (fun j : Fin r => ((|s| : ℤ) : ℝ) / 2 ^ J *
        ((pDj r (dK K) σ j : ℝ) * Real.posLog (w (estBeta s (α' j))))) ?_ ?_
    · intro j
      refine mul_nonneg (div_nonneg ?_ (by positivity))
        (mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg)
      rw [Int.cast_abs]
      exact abs_nonneg _
    · intro j
      have hb := log_infinitePlace_zpow_le w (α' j) s ((lm.2.2 j : ℕ) / 2 ^ J)
      have hle : (lm.2.2 j : ℕ) ≤ pDj r (dK K) σ j := Nat.lt_succ_iff.mp (lm.2.2 j).isLt
      have hq : (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) ≤ (pDj r (dK K) σ j : ℝ) / 2 ^ J := by
        have hpow : (((2 : ℕ) ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by norm_num [Nat.cast_pow]
        have h1 : (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) ≤ ((lm.2.2 j : ℕ) : ℝ) / (2 : ℝ) ^ J := by
          have h := Nat.cast_div_le (m := (lm.2.2 j : ℕ)) (n := 2 ^ J) (α := ℝ)
          rw [hpow] at h
          exact h
        have h2 : ((lm.2.2 j : ℕ) : ℝ) ≤ (pDj r (dK K) σ j : ℝ) := by exact_mod_cast hle
        have h3 : ((lm.2.2 j : ℕ) : ℝ) / 2 ^ J ≤ (pDj r (dK K) σ j : ℝ) / 2 ^ J :=
          div_le_div_of_nonneg_right h2 (by positivity)
        linarith
      have hstep : ((|s| : ℝ) * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ))
          ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * (pDj r (dK K) σ j : ℝ) := by
        rw [Int.cast_abs]
        have hmm := mul_le_mul_of_nonneg_left hq (abs_nonneg (s : ℝ))
        calc (|(s : ℝ)| * ↑((lm.2.2 j : ℕ) / 2 ^ J))
            ≤ |(s : ℝ)| * ((pDj r (dK K) σ j : ℝ) / 2 ^ J) := hmm
          _ = (|(s : ℝ)| / 2 ^ J) * (pDj r (dK K) σ j : ℝ) := by ring
      calc Real.log (w ((α' j) ^ (s * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℤ))))
          ≤ ((|s| : ℝ) * (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ)) *
              Real.posLog (w (estBeta s (α' j))) := hb
        _ ≤ ((((|s| : ℤ) : ℝ) / 2 ^ J) * (pDj r (dK K) σ j : ℝ)) *
              Real.posLog (w (estBeta s (α' j))) :=
              mul_le_mul_of_nonneg_right hstep Real.posLog_nonneg
        _ = ((|s| : ℤ) : ℝ) / 2 ^ J *
              ((pDj r (dK K) σ j : ℝ) * Real.posLog (w (estBeta s (α' j)))) := by ring
  -- ### the Θ-term is dominated by the three `estCi` summands it replaces
  have hθC : ((acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1)) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r)
        + ((((lm.2.1 : ℕ) : ℝ) + 1)) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| / mu57 K r
      ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r)
        + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / mu57 K r
        + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r := by
    have hh : 0 ≤ (acH K b v : ℝ) := Nat.cast_nonneg _
    have hlen : (((lm.2.1 : ℕ) : ℝ) + 1) ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) := by
      have hle : (lm.2.1 : ℕ) ≤ pD0 r (dK K) σ := Nat.lt_succ_iff.mp (lm.2.1).isLt
      have := Nat.cast_le (α := ℝ).mpr hle
      linarith
    -- first summand
    have ht1 : (acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r)
        ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
          (1 + Real.log (mu57 K r) + 1 / mu57 K r) := by
      have hA1 : (acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1)
          ≤ (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlen hh
      calc (acH K b v : ℝ) * (((lm.2.1 : ℕ) : ℝ) + 1) *
              (1 + Real.log (mu57 K r) + 1 / mu57 K r)
          ≤ (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) *
              (1 + Real.log (mu57 K r) + 1 / mu57 K r) :=
            mul_le_mul_of_nonneg_right hA1 hX
        _ = (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
              (1 + Real.log (mu57 K r) + 1 / mu57 K r) := by ring
    -- `|z| ≤ 2^{-J}|s| + h`
    have hz : |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)|
        ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) + (acH K b v : ℝ) := by
      have h1 : |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)|
          ≤ |(s : ℝ) / 2 ^ J| + |((lm.1 : ℕ) : ℝ)| := abs_add_le _ _
      have h2 : |(s : ℝ) / 2 ^ J| = ((|s| : ℤ) : ℝ) / 2 ^ J := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ J by positivity), Int.cast_abs]
      have h3 : |((lm.1 : ℕ) : ℝ)| = ((lm.1 : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      have h4 : ((lm.1 : ℕ) : ℝ) ≤ (acH K b v : ℝ) := by
        have := (lm.1).isLt
        exact_mod_cast (Nat.le_of_lt this)
      linarith [h1, h2, h3, h4]
    -- second summand
    have ht2 : ((((lm.2.1 : ℕ) : ℝ) + 1)) *
          |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| / mu57 K r
        ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / mu57 K r
          + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r := by
      have hb1 : (((lm.2.1 : ℕ) : ℝ) + 1) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)|
          ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)
              * ((((|s| : ℤ) : ℝ) / 2 ^ J) + (acH K b v : ℝ)) :=
        calc (((lm.2.1 : ℕ) : ℝ) + 1) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)|
            ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| :=
              mul_le_mul_of_nonneg_right hlen (abs_nonneg _)
          _ ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)
              * ((((|s| : ℤ) : ℝ) / 2 ^ J) + (acH K b v : ℝ)) :=
              mul_le_mul_of_nonneg_left hz (by positivity)
      calc (((lm.2.1 : ℕ) : ℝ) + 1) * |(s : ℝ) / 2 ^ J + ((lm.1 : ℕ) : ℝ)| / mu57 K r
          ≤ (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)
              * ((((|s| : ℤ) : ℝ) / 2 ^ J) + (acH K b v : ℝ)) / mu57 K r :=
            div_le_div_of_nonneg_right hb1 hmu_pos.le
        _ = (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / mu57 K r
              + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (((|s| : ℤ) : ℝ) / 2 ^ J) / mu57 K r := by
            rw [mul_add, add_div]; ring
    linarith [ht1, ht2]
  -- ### multiply the four factor-bounds together
  have h1 := log_w_mul_le w hnPi hnU hA_le hU_le
  have h2 := log_w_mul_le w (add_nonneg hnPi hnU) hnθ h1 hC_le
  have h3 := log_w_mul_le w (by linarith [hnPi, hnU, hnθ]) hnMono h2 hD_le
  rw [coefKJ]
  refine h3.trans ?_
  rw [estCi]
  linarith [hθC]

end Work.BW
