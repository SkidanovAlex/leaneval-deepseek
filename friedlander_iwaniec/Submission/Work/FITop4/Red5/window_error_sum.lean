/-
# `Submission.Work.FITop4.Red5.window_error_sum` — summing the `T2`/`T3` window errors

The round-5 reduction splits the outer `m`-sum over the window ladder
`M_j = MnOf x N j` (`j ∈ Fin (JJN x N + 1)`).  Each window contributes an error
`c2 · T2RHS + c3 · T3RHS`.  This file bounds the *total* error over the whole ladder:

  `∑_j (c2 · T2RHS(M_j) + c3 · T3RHS(M_j)) ≤ c (c2 + c3) θ x^{3/4} (log x)^{100}`.

The three ingredients are

* the geometric-sum bound `2^{JJN} M₀ ≤ x / N` (`Red5NumC.hpowJJN`), which makes
  `∑_j (M_j N)^{1/4}` and `∑_j (M_j N)^{3/4}` geometric series bounded by
  `2^{1/4} x^{1/4}/(2^{1/4}-1)` and `2^{3/4} x^{3/4}/(2^{3/4}-1)`;
* the coprimality admissibility `N ≤ ϑ θ √x` (`Red5NumC.hcop`) together with `ϑ ≤ 1/4`,
  which turns the `M_j^{1/4}N^{5/4}` term into `θ x^{3/4}`;
* the `Pz`-condition `Pz⁻¹ ≤ ϑ θ (log x)^{100}` (`Red5NumC.hPz`) together with
  `ϑ (log x)^{100} ≤ 1`, which absorbs the `Pz⁻¹ M_j^{3/4}N^{3/4}` term.
-/
import Mathlib
import Submission.Work.FITop4.Red5.Red5NumC

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The finite geometric sum `∑_{j<n} r^j ≤ r^n/(r-1)` for `r > 1`. -/
private lemma geom_sum_fin_le {r : ℝ} (hr : 1 < r) (n : ℕ) :
    (∑ j : Fin n, r ^ (j : ℕ)) ≤ r ^ n / (r - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) n, geom_sum_eq (ne_of_gt hr) n]
  apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ r - 1)
  have h : (1 : ℝ) ≤ r ^ n := one_le_pow₀ hr.le
  linarith

/-- `(c^j)^e = (c^e)^j` for a natural power inside a real power. -/
private lemma rpow_nat_pow_comm (c : ℝ) (hc : 0 ≤ c) (j : ℕ) (e : ℝ) :
    (c ^ j : ℝ) ^ e = (c ^ e) ^ (j : ℕ) := by
  rw [show (c ^ j : ℝ) = c ^ ((j : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  rw [show (c ^ e) ^ (j : ℕ) = (c ^ e) ^ ((j : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  exact calc (c ^ ((j : ℕ) : ℝ)) ^ e
      = c ^ (((j : ℕ) : ℝ) * e) := (Real.rpow_mul hc _ _).symm
    _ = c ^ (e * ((j : ℕ) : ℝ)) := by rw [mul_comm]
    _ = (c ^ e) ^ ((j : ℕ) : ℝ) := Real.rpow_mul hc _ _

/-- `MnOf x N j ≤ 2^j M₀` for every ladder index. -/
private lemma MnOf_le_two_pow_mul (x N j : ℕ) : MnOf x N j ≤ 2 ^ j * M0N x N := by
  by_cases h : j < JJN x N
  · rw [MnOf_of_lt h]
  · rw [MnOf_of_not_lt h]
    calc MtopN x N ≤ 2 ^ (JJN x N) * M0N x N := le_of_lt (MtopN_lt_two_pow_JJN x N)
      _ ≤ 2 ^ j * M0N x N := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The geometric bound on the ladder: for every real exponent `e > 0`,

  `∑_j (M_j · N)^e ≤ (2x)^e / (2^e - 1)`. -/
private lemma sum_MnN_rpow_le (x N : ℕ) (e : ℝ) (he : 0 < e)
    (hN : (0 : ℝ) < (N : ℝ))
    (hpow : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) ≤ (x : ℝ) / (N : ℝ)) :
    (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ e)
      ≤ (2 * (x : ℝ)) ^ e / ((2 : ℝ) ^ e - 1) := by
  set r : ℝ := (2 : ℝ) ^ e with hrdef
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) he
  have hrm1 : 0 < r - 1 := by linarith
  have hn0 : 0 ≤ (N : ℝ) := le_of_lt hN
  have hM00 : 0 ≤ (M0N x N : ℝ) := Nat.cast_nonneg _
  -- `2^(JJN+1) · M₀ · N ≤ 2x`
  have hpow2 : (2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ) * (N : ℝ) ≤ 2 * (x : ℝ) := by
    have h1 : ((2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ)) * (N : ℝ) ≤ (x : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hpow hn0
      rwa [div_mul_cancel₀ _ (ne_of_gt hN)] at hm
    have h2 : (2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ) * (N : ℝ)
        = 2 * (((2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ)) * (N : ℝ)) := by
      rw [pow_succ]; ring
    rw [h2]; linarith
  have hexp2 : ((2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ) * (N : ℝ))
      = ((2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ)) * (N : ℝ) := by ring
  have hterm : ∀ j : Fin (JJN x N + 1),
      ((MnOf x N j : ℝ) * (N : ℝ)) ^ e
        ≤ ((M0N x N : ℝ) * (N : ℝ)) ^ e * r ^ (j : ℕ) := by
    intro j
    have h1 : (MnOf x N j : ℝ) ≤ (2 : ℝ) ^ (j : ℕ) * (M0N x N : ℝ) := by
      exact_mod_cast MnOf_le_two_pow_mul x N j
    have hle : (MnOf x N j : ℝ) * (N : ℝ) ≤ ((2 : ℝ) ^ (j : ℕ) * (M0N x N : ℝ)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hn0
    have hA : ((2 : ℝ) ^ (j : ℕ) * (M0N x N : ℝ)) * (N : ℝ)
        = (2 : ℝ) ^ (j : ℕ) * ((M0N x N : ℝ) * (N : ℝ)) := by ring
    calc ((MnOf x N j : ℝ) * (N : ℝ)) ^ e
        ≤ (((2 : ℝ) ^ (j : ℕ) * (M0N x N : ℝ)) * (N : ℝ)) ^ e :=
          Real.rpow_le_rpow (by positivity) hle he.le
      _ = ((2 : ℝ) ^ (j : ℕ) * ((M0N x N : ℝ) * (N : ℝ))) ^ e := by rw [hA]
      _ = r ^ (j : ℕ) * (((M0N x N : ℝ) * (N : ℝ)) ^ e) := by
          rw [Real.mul_rpow (x := (2 : ℝ) ^ (j : ℕ)) (y := (M0N x N : ℝ) * (N : ℝ)) (z := e)
                (by positivity) (by positivity),
              rpow_nat_pow_comm 2 (by norm_num) (j : ℕ) e, hrdef]
      _ = ((M0N x N : ℝ) * (N : ℝ)) ^ e * r ^ (j : ℕ) := by ring
  have hsum : (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ e)
      ≤ ((M0N x N : ℝ) * (N : ℝ)) ^ e * (∑ j : Fin (JJN x N + 1), r ^ (j : ℕ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hkey : ((M0N x N : ℝ) * (N : ℝ)) ^ e * r ^ (JJN x N + 1)
      = ((2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ) * (N : ℝ)) ^ e := by
    rw [hexp2, Real.mul_rpow (x := (2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ)) (y := (N : ℝ)) (z := e)
          (by positivity) hn0,
        Real.mul_rpow (x := (2 : ℝ) ^ (JJN x N + 1)) (y := (M0N x N : ℝ)) (z := e)
          (by positivity) hM00,
        rpow_nat_pow_comm 2 (by norm_num) (JJN x N + 1) e, ← hrdef,
        Real.mul_rpow (x := (M0N x N : ℝ)) (y := (N : ℝ)) (z := e) hM00 hn0]
    ring
  calc (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ e)
      ≤ ((M0N x N : ℝ) * (N : ℝ)) ^ e * (∑ j : Fin (JJN x N + 1), r ^ (j : ℕ)) := hsum
    _ ≤ ((M0N x N : ℝ) * (N : ℝ)) ^ e * (r ^ (JJN x N + 1) / (r - 1)) :=
        mul_le_mul_of_nonneg_left (geom_sum_fin_le hr1 (JJN x N + 1)) (by positivity)
    _ = (((M0N x N : ℝ) * (N : ℝ)) ^ e * r ^ (JJN x N + 1)) / (r - 1) := by
        rw [mul_div_assoc']
    _ = ((2 : ℝ) ^ (JJN x N + 1) * (M0N x N : ℝ) * (N : ℝ)) ^ e / (r - 1) := by rw [hkey]
    _ ≤ (2 * (x : ℝ)) ^ e / (r - 1) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hpow2 he.le) hrm1.le
    _ = (2 * (x : ℝ)) ^ e / ((2 : ℝ) ^ e - 1) := by rw [hrdef]

theorem window_error_sum :
    ∃ c : ℝ, 0 < c ∧ ∀ (x N Pz : ℕ) (η c2 c3 θ : ℝ),
      Work.FITop4.Red5.Red5NumC x N Pz η → 0 ≤ c2 → 0 ≤ c3 →
      θ = Work.FITop4.thetaOf x Work.FITop4.Asave →
      (∀ j : Fin (Work.FITop4.Red5.JJN x N + 1),
          (Work.FITop4.Red5.MnOf x N j : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ)) →
      (∑ j : Fin (Work.FITop4.Red5.JJN x N + 1),
        (c2 * Work.FITop4.Red5.T2RHS x N (Work.FITop4.Red5.MnOf x N j) Pz θ
         + c3 * Work.FITop4.Red5.T3RHS x N (Work.FITop4.Red5.MnOf x N j) θ))
      ≤ c * (c2 + c3) * (θ * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ)) := by
  set r4 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with hr4
  set r34 : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 4) with hr34
  have hr4pos : 0 < r4 := by rw [hr4]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hr34pos : 0 < r34 := by rw [hr34]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hr4gt : 1 < r4 := by rw [hr4]; exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hr34gt : 1 < r34 := by rw [hr34]; exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hr4d : 0 < r4 - 1 := by linarith
  have hr34d : 0 < r34 - 1 := by linarith
  refine ⟨r4 / (4 * (r4 - 1)) + 2 * (r34 / (r34 - 1)), ?_, ?_⟩
  · have h1 : 0 < r4 / (4 * (r4 - 1)) := div_pos hr4pos (by linarith)
    have h2 : 0 < r34 / (r34 - 1) := div_pos hr34pos hr34d
    linarith
  · intro x N Pz η c2 c3 θ hRed hc2 hc3 hθ hMN
    -- ## Basic positivity and normalisations
    have hx1 : 1 ≤ x := by have := hRed.hx4; omega
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hxn0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
    have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hRed.hlog1
    -- `N > 0` (forced by `2^JJN M₀ ≤ x/N`)
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      by_contra hcon
      have hcon' : (N : ℝ) ≤ 0 := le_of_not_gt hcon
      have hN0 : (N : ℝ) = 0 := le_antisymm hcon' (Nat.cast_nonneg N)
      have h := hRed.hpowJJN
      rw [hN0, div_zero] at h
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (JJN x N) := one_le_pow₀ (by norm_num)
      have h2 : (2 : ℝ) ≤ (M0N x N : ℝ) := by exact_mod_cast M0N_ge_two x N
      have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) := by nlinarith [h1, h2]
      linarith
    have hn0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
    set L : ℝ := (Real.log (x : ℝ)) ^ (100 : ℕ) with hL
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    have hthpos : 0 < θ := by rw [hθ]; exact hRed.ht0
    have hth0 : 0 ≤ θ := le_of_lt hthpos
    -- `ϑ · (log x)^100 ≤ 1`
    have hvL : varthetaOf x Asave * L ≤ 1 := by
      rw [hL, varthetaOf, ← Real.rpow_natCast (Real.log (x : ℝ)) 100,
        ← Real.rpow_add hlogpos (-Asave) ((100 : ℕ) : ℝ)]
      apply Real.rpow_le_one_of_one_le_of_nonpos hRed.hlog1
      unfold Asave; norm_num
    -- `N ≤ (1/4) θ √x`
    have hnle : (N : ℝ) ≤ (1 / 4) * θ * (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have h1 : (N : ℝ) ≤ varthetaOf x Asave * θ * (x : ℝ) ^ ((1 : ℝ) / 2) := by
        have h := hRed.hcop
        rwa [← hθ] at h
      have hu : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hxn0 _
      have h2 : varthetaOf x Asave * θ * (x : ℝ) ^ ((1 : ℝ) / 2)
          ≤ (1 / 4) * θ * (x : ℝ) ^ ((1 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hu
        exact mul_le_mul_of_nonneg_right hRed.hv14 hth0
      linarith
    -- ## The geometric bounds on the two ladders
    have hU1 := sum_MnN_rpow_le x N ((1 : ℝ) / 4) (by norm_num) hNpos hRed.hpowJJN
    have hU3 := sum_MnN_rpow_le x N ((3 : ℝ) / 4) (by norm_num) hNpos hRed.hpowJJN
    set S1 : ℝ := ∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4)
      with hS1def
    set S3 : ℝ := ∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)
      with hS3def
    have hS1 : S1 ≤ (r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hS1def]
      have h := hU1
      rw [Real.mul_rpow (x := (2 : ℝ)) (y := (x : ℝ)) (z := ((1 : ℝ) / 4)) (by norm_num) hxn0,
        ← hr4] at h
      calc (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
          ≤ r4 * (x : ℝ) ^ ((1 : ℝ) / 4) / (r4 - 1) := h
        _ = (r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4) := by ring
    have hS3 : S3 ≤ (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [hS3def]
      have h := hU3
      rw [Real.mul_rpow (x := (2 : ℝ)) (y := (x : ℝ)) (z := ((3 : ℝ) / 4)) (by norm_num) hxn0,
        ← hr34] at h
      calc (∑ j : Fin (JJN x N + 1), ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4))
          ≤ r34 * (x : ℝ) ^ ((3 : ℝ) / 4) / (r34 - 1) := h
        _ = (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
    -- ## Termwise identity
    have hterm : ∀ j : Fin (JJN x N + 1),
        c2 * T2RHS x N (MnOf x N j) Pz θ + c3 * T3RHS x N (MnOf x N j) θ
          = L * (c2 * ((N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
              + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)
                * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
      intro j
      have hfirst : (MnOf x N j : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4)
          = (N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4) := by
        have hn54 : (N : ℝ) ^ ((5 : ℝ) / 4) = (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [show (5 : ℝ) / 4 = 1 + 1 / 4 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
        have hmr : ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4)
            = (MnOf x N j : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.mul_rpow (Nat.cast_nonneg _) (le_of_lt hNpos)
        rw [hn54, hmr]; ring
      have hsecond : (MnOf x N j : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4)
          = ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) :=
        (Real.mul_rpow (Nat.cast_nonneg _) (le_of_lt hNpos)).symm
      simp only [T2RHS, T3RHS]
      rw [hfirst, hsecond, ← hL]
      ring
    -- ## Sum algebra
    have hG : (∑ j : Fin (JJN x N + 1), (N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
        = (N : ℝ) * S1 := by
      rw [hS1def]
      exact (Finset.mul_sum Finset.univ
        (fun j : Fin (JJN x N + 1) => ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
        (N : ℝ)).symm
    have hsum_eq : (∑ j : Fin (JJN x N + 1),
        (c2 * T2RHS x N (MnOf x N j) Pz θ + c3 * T3RHS x N (MnOf x N j) θ))
        = L * (c2 * ((N : ℝ) * S1) + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ) * S3) := by
      have h1 : (∑ j : Fin (JJN x N + 1),
          (c2 * T2RHS x N (MnOf x N j) Pz θ + c3 * T3RHS x N (MnOf x N j) θ))
          = ∑ j : Fin (JJN x N + 1), L * (
              c2 * ((N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
              + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)
                * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
      have h2 : (∑ j : Fin (JJN x N + 1), L * (
              c2 * ((N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
              + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)
                * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)))
          = L * (∑ j : Fin (JJN x N + 1), (
              c2 * ((N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
              + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)
                * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4))) :=
        (Finset.mul_sum Finset.univ _ L).symm
      have h3 : (∑ j : Fin (JJN x N + 1), (
              c2 * ((N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4))
              + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)
                * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)))
          = c2 * ((N : ℝ) * S1) + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ) * S3 := by
        rw [Finset.sum_add_distrib,
          (Finset.mul_sum Finset.univ (fun j : Fin (JJN x N + 1) =>
            (N : ℝ) * ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4)) c2).symm,
          (Finset.mul_sum Finset.univ (fun j : Fin (JJN x N + 1) =>
            ((MnOf x N j : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4))
            (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ)).symm,
          hG, ← hS3def]
      rw [h1, h2, h3]
    -- ## The size of the bracket
    have hC : c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ ≤ θ * (2 * (c2 + c3)) := by
      have hpz : (Pz : ℝ)⁻¹ ≤ varthetaOf x Asave * θ * L := by
        have h := hRed.hPz
        rw [← hθ, ← hL] at h
        exact h
      have hvLn0 : 0 ≤ varthetaOf x Asave * L := mul_nonneg (le_of_lt hRed.hv0) hL0
      have h2 : c2 * (Pz : ℝ)⁻¹ ≤ c2 * θ := by
        calc c2 * (Pz : ℝ)⁻¹ ≤ c2 * (varthetaOf x Asave * θ * L) :=
              mul_le_mul_of_nonneg_left hpz hc2
          _ = θ * (c2 * (varthetaOf x Asave * L)) := by ring
          _ ≤ θ * (c2 * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvL hc2) hth0
          _ = c2 * θ := by ring
      have h4 : 0 ≤ θ * c3 := mul_nonneg hth0 hc3
      have h3 : c2 * θ + (c2 + c3) * θ = θ * (2 * (c2 + c3)) - θ * c3 := by ring
      linarith
    have hnS1 : (N : ℝ) * S1 ≤ θ * (r4 / (4 * (r4 - 1))) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
      have hrb : 0 ≤ (r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_nonneg (div_nonneg (le_of_lt hr4pos) (le_of_lt hr4d)) (Real.rpow_nonneg hxn0 _)
      have h1 : (N : ℝ) * S1 ≤ (N : ℝ) * ((r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hS1 hn0
      have h2 : (N : ℝ) * ((r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4))
          ≤ ((1 / 4) * θ * (x : ℝ) ^ ((1 : ℝ) / 2))
              * ((r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hnle hrb
      have h3 : ((1 / 4) * θ * (x : ℝ) ^ ((1 : ℝ) / 2))
              * ((r4 / (r4 - 1)) * (x : ℝ) ^ ((1 : ℝ) / 4))
          = θ * (r4 / (4 * (r4 - 1))) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
        have huu : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 4)
            = (x : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [show (3 : ℝ) / 4 = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hxpos]
        rw [← huu]
        rw [← sub_eq_zero]
        field_simp
        ring
      linarith
    have hS3nn : 0 ≤ S3 := by
      rw [hS3def]
      exact Finset.sum_nonneg
        (fun j _ => Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hn0) _)
    have hCnn : 0 ≤ θ * (2 * (c2 + c3)) := mul_nonneg hth0 (by nlinarith [hc2, hc3])
    have hB : (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ) * S3
        ≤ θ * (2 * (c2 + c3)) * (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
      have h1 : (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ) * S3 ≤ (θ * (2 * (c2 + c3))) * S3 :=
        mul_le_mul_of_nonneg_right hC hS3nn
      have h2 : (θ * (2 * (c2 + c3))) * S3
          ≤ θ * (2 * (c2 + c3)) * (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
        calc (θ * (2 * (c2 + c3))) * S3
            ≤ (θ * (2 * (c2 + c3))) * ((r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left hS3 hCnn
          _ = θ * (2 * (c2 + c3)) * (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
      linarith
    have hA : c2 * ((N : ℝ) * S1) ≤ c2 * (θ * (r4 / (4 * (r4 - 1))) * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hnS1 hc2
    -- ## Assembly
    calc (∑ j : Fin (JJN x N + 1),
          (c2 * T2RHS x N (MnOf x N j) Pz θ + c3 * T3RHS x N (MnOf x N j) θ))
        = L * (c2 * ((N : ℝ) * S1) + (c2 * (Pz : ℝ)⁻¹ + (c2 + c3) * θ) * S3) := hsum_eq
      _ ≤ L * (c2 * (θ * (r4 / (4 * (r4 - 1))) * (x : ℝ) ^ ((3 : ℝ) / 4))
            + θ * (2 * (c2 + c3)) * (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (by linarith) hL0
      _ ≤ (r4 / (4 * (r4 - 1)) + 2 * (r34 / (r34 - 1))) * (c2 + c3)
            * (θ * (x : ℝ) ^ ((3 : ℝ) / 4) * L) := by
          have key : (r4 / (4 * (r4 - 1)) + 2 * (r34 / (r34 - 1))) * (c2 + c3)
                * (θ * (x : ℝ) ^ ((3 : ℝ) / 4) * L)
              - L * (c2 * (θ * (r4 / (4 * (r4 - 1))) * (x : ℝ) ^ ((3 : ℝ) / 4))
                  + θ * (2 * (c2 + c3)) * (r34 / (r34 - 1)) * (x : ℝ) ^ ((3 : ℝ) / 4))
              = L * θ * (x : ℝ) ^ ((3 : ℝ) / 4) * (r4 / (4 * (r4 - 1))) * c3 := by ring
          have hnn : 0 ≤ L * θ * (x : ℝ) ^ ((3 : ℝ) / 4) * (r4 / (4 * (r4 - 1))) * c3 :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL0 hth0)
              (Real.rpow_nonneg hxn0 _)) (le_of_lt (div_pos hr4pos (by linarith)))) hc3
          linarith

end

end Work.FITop4.Red5
