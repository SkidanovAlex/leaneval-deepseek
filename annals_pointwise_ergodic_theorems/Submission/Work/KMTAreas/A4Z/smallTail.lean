/-
# The small-`N` branch of `Work.KMTAreas.A4Z.lipTwoGenTail` (`lip-2` with the tail clauses)

For `N^d ≤ C δ^{-K}` the second dual function `Ã_N^{**}(f,h)` truncated to the window of radius
`A N^d` already satisfies *all* the clauses of `Work.KMTAreas.A4Z.LipOutputGenTwoTail`: its Fourier
transform is supported in the (vacuous) major arcs `majorArc ρ 0 0 = Set.univ`, its pairing with `g`
is `⟨Ã_N(f,g), h⟩` by the transposition identity, and the truncation makes the `ℓ¹`-fringe clause
hold with equality (mass `0`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4.lipMajorArcZeroZero

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-- The second dual function is bounded by `1` when `f` and `h` are. -/
theorem norm_AhalfTranspose₂_le_one {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {f h : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (x : ℤ) :
    ‖AhalfTranspose₂ N P f h x‖ ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [AhalfTranspose₂]
  have hnorm : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnorm]
  have hcard : ‖∑ n ∈ Finset.Ioc (N / 2) N,
      f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖
        ≤ ∑ n ∈ Finset.Ioc (N / 2) N,
            ‖f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc (N / 2) N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul]
          exact mul_le_one₀ (hf _) (norm_nonneg _) (hh _)
      _ = ((Finset.Ioc (N / 2) N).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (N : ℝ) := by
          rw [Nat.card_Ioc]
          push_cast
          exact_mod_cast Nat.sub_le N (N / 2)
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * (N : ℝ) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 1 := inv_mul_cancel₀ hNpos.ne'

/-- **The `ℓ²`-tail bound for a function supported in `[-R,R]`**: the mass outside any ball of
radius `T` is at most `2R + 1` times the square of the sup bound. -/
theorem l2tail_of_support {G : ℤ → ℂ} {R : ℕ} (hGsupp : ∀ x : ℤ, R < x.natAbs → G x = 0)
    (hG1 : ∀ x : ℤ, ‖G x‖ ≤ 1) (T : ℝ) :
    (∑' x : ℤ, (if T < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)) ≤ 2 * (R : ℝ) + 1 := by
  have hsplit : (∑' x : ℤ, (if T < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
      = ∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
          (if T < |(x : ℝ)| then ‖G x‖ ^ 2 else 0) :=
    tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) (R : ℤ))
      (f := fun x : ℤ => (if T < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)) (fun x hx => by
        have hx' : R < x.natAbs := by
          rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
          rcases hx with h | h <;> omega
        rw [hGsupp x hx']; simp)
  rw [hsplit]
  have hsum : ∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (if T < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
      ≤ ∑ _x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (1 : ℝ) :=
    Finset.sum_le_sum fun x _ => by
      by_cases hx : T < |(x : ℝ)|
      · rw [if_pos hx]
        nlinarith [norm_nonneg (G x), hG1 x]
      · rw [if_neg hx]; positivity
  have hcard : ∑ _x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (1 : ℝ) ≤ 2 * (R : ℝ) + 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card ≤ 2 * R + 1 := by
      rw [Int.card_Icc]; omega
    exact_mod_cast hc
  linarith [hsum, hcard]

/-- The real absolute value of an integer, in terms of `x.natAbs`. -/
theorem abs_cast_eq_natAbs (x : ℤ) : |(x : ℝ)| = (x.natAbs : ℝ) := by
  have h1 : |(x : ℝ)| = ((|x| : ℤ) : ℝ) := by rw [Int.cast_abs]
  have h2 : ((|x| : ℤ) : ℝ) = ((x.natAbs : ℤ) : ℝ) := by
    congr 1
    exact (Int.natCast_natAbs x).symm
  have h3 : ((x.natAbs : ℤ) : ℝ) = (x.natAbs : ℝ) := by simp
  rw [h1, h2, h3]

/-- **The small-`N` branch of Proposition `lip-2` with the tail clauses.** -/
theorem smallTail (P : Polynomial ℤ) : ∀ A : ℝ, 1 ≤ A → ∃ C K C0 K2 : ℝ,
    0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      (N : ℝ) ^ P.natDegree ≤ C * δ⁻¹ ^ K →
      ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
        (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖G x‖) ∧
        (∑' x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        FourierSupportIn G (majorArc ρ l k) ∧
        (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ ∧
        (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0)
          ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
        (∀ R : ℝ, 1 ≤ R →
          ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
            ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree) := by
  intro A hA
  refine ⟨4, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro ρ hρ0 hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hfb hgb hhb hcorr hsmall
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hδinvpos : (0 : ℝ) < δ⁻¹ := lt_of_lt_of_le zero_lt_one hδinv1
  have hsmall' : (N : ℝ) ^ P.natDegree ≤ 4 * δ⁻¹ := by simpa [Real.rpow_one] using hsmall
  have hAδ : (1 : ℝ) ≤ A * δ⁻¹ := by
    have h := mul_le_mul hA hδinv1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hA0)
    simpa using h
  have h1goal : (1 : ℝ) ≤ 4 * A * δ⁻¹ := by
    have h4 : (1 : ℝ) ≤ 4 * (A * δ⁻¹) := by linarith [hAδ]
    have hEq : 4 * (A * δ⁻¹) = 4 * A * δ⁻¹ := by ring
    linarith [h4, hEq]
  -- the truncation window
  set R : ℕ := ⌊A * (N : ℝ) ^ P.natDegree⌋₊ with hRdef
  have hRle : (R : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := Nat.floor_le (by positivity)
  have hN0R : N₀ ≤ R := Nat.le_floor hN0hi
  have hAN1 : (1 : ℝ) ≤ A * (N : ℝ) ^ P.natDegree :=
    one_le_mul_of_one_le_of_one_le hA hNd1
  have hN0ge1 : 1 ≤ N₀ := by
    have h2 : (1 : ℝ) / 2 ≤ (N₀ : ℝ) := by linarith [hAN1, hN0lo]
    have h3 : (0 : ℝ) < (N₀ : ℝ) := by linarith
    have h4 : 0 < N₀ := by exact_mod_cast h3
    omega
  have hR1 : 1 ≤ R := le_trans hN0ge1 hN0R
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  -- the candidate: the second dual function truncated to the window
  set G : ℤ → ℂ := fun x => if x.natAbs ≤ R then AhalfTranspose₂ N P f h x else 0 with hGdef
  have hGvan : ∀ x : ℤ, R < x.natAbs → G x = 0 := by
    intro x hx
    simp only [hGdef]
    rw [if_neg (not_le.mpr hx)]
  have hG1 : ∀ x : ℤ, ‖G x‖ ≤ 1 := by
    intro x
    simp only [hGdef]
    by_cases hx : x.natAbs ≤ R
    · rw [if_pos hx]; exact norm_AhalfTranspose₂_le_one hN P hfb hhb x
    · rw [if_neg hx]; simp
  refine ⟨G, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the sup bound
    intro x
    rw [Real.rpow_one]
    exact le_trans (hG1 x) h1goal
  · -- (2) summability
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(R : ℤ)) (R : ℤ)) fun x hx => ?_
    have hx' : R < x.natAbs := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h <;> omega
    rw [hGvan x hx', norm_zero]
  · -- (3) the `ℓ¹` bound
    rw [Real.rpow_one]
    have h3 : (∑' x : ℤ, ‖G x‖) ≤ 2 * (R : ℝ) + 1 := by
      have hsupp : SupportIn G R := hGvan
      have h := ellOne_le_of_supportIn G R hsupp (C := 1) (fun x => hG1 x)
      simpa [ellOne] using h
    have h4a : 2 * (R : ℝ) + 1 ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by linarith [hRle, hAN1]
    have h4b : 3 * (A * (N : ℝ) ^ P.natDegree) ≤ 4 * A * δ⁻¹ * (N : ℝ) ^ P.natDegree := by
      have h3δ : (3 : ℝ) ≤ 4 * δ⁻¹ := by linarith [hδinv1]
      have hANpos : (0 : ℝ) < A * (N : ℝ) ^ P.natDegree := mul_pos hA0 hNdpos
      calc 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ (4 * δ⁻¹) * (A * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right h3δ (le_of_lt hANpos)
        _ = 4 * A * δ⁻¹ * (N : ℝ) ^ P.natDegree := by ring
    linarith [h3, h4a, h4b]
  · -- (4) Fourier support: the major arcs at `(0,0)` are everything
    rw [Work.KMTAreas.A4.lipMajorArcZeroZero hρ0 hρ1]
    exact fun ξ hξ => absurd (Set.mem_univ ξ) hξ
  · -- (5) the linear scale
    rw [pow_zero, Real.rpow_one]
    exact h1goal
  · -- (6) the continuous scale
    have h6 : (1 : ℝ) ≤ 4 * A * δ⁻¹ / (N : ℝ) ^ P.natDegree := by
      rw [le_div_iff₀ hNdpos, one_mul]
      have h4 : 4 * δ⁻¹ ≤ 4 * A * δ⁻¹ := by
        have hm : (1 : ℝ) * δ⁻¹ ≤ A * δ⁻¹ :=
          mul_le_mul_of_nonneg_right hA hδinvpos.le
        rw [one_mul] at hm
        have h4' : 4 * δ⁻¹ ≤ 4 * (A * δ⁻¹) :=
          mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
        have hEq4 : 4 * (A * δ⁻¹) = 4 * A * δ⁻¹ := by ring
        linarith [h4', hEq4]
      exact le_trans hsmall' h4
    rw [zpow_zero, Real.rpow_one]
    exact h6
  · -- (7) the correlation
    have hGg : bilinPair g G = bilinPair (AhalfTranspose₂ N P f h) g := by
      rw [bilinPair, bilinPair]
      refine tsum_congr fun x => ?_
      by_cases hx : x.natAbs ≤ R
      · have hGx : G x = AhalfTranspose₂ N P f h x := by
          simp only [hGdef]; rw [if_pos hx]
        rw [hGx]; ring
      · have hGx : G x = 0 := by simp only [hGdef]; rw [if_neg hx]
        have hxN : N₀ < x.natAbs := lt_of_le_of_lt hN0R (lt_of_not_ge hx)
        rw [hGx, mul_zero, hgs x hxN, mul_zero]
    have htr : bilinPair (AhalfTranspose₂ N P f h) g = bilinPair (AhalfZ N P f g) h :=
      (bilinPair_AhalfZ_eq_transpose₂ (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hgs)
        (FinSupp.of_supportIn hhs) N P).symm
    have h7 : δ ^ (1 : ℝ) * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ := by
      rw [hGg, htr]
      simpa [Real.rpow_one] using hcorr
    simpa [Real.rpow_one] using h7
  · -- (8) the `ℓ¹`-fringe clause: the truncation vanishes outside the window
    have hzero : (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0))
        = ∑' _x : ℤ, (0 : ℝ) := by
      refine tsum_congr fun x => ?_
      by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
      · have hxR : R < x.natAbs := by
          have h1 : A * (N : ℝ) ^ P.natDegree < (x.natAbs : ℝ) := by
            rwa [abs_cast_eq_natAbs] at hx
          exact_mod_cast lt_of_le_of_lt hRle h1
        rw [if_pos hx, hGvan x hxR, norm_zero]
      · rw [if_neg hx]
    rw [hzero, tsum_zero]
    exact div_nonneg (mul_nonneg (Real.rpow_pos_of_pos hδ0 1).le hNdpos.le) (by norm_num)
  · -- (9) the `ℓ²`-tail clause, from the support bound
    intro R' hR'
    have htail := l2tail_of_support hGvan hG1 (R' * (N : ℝ) ^ P.natDegree)
    have hR'pos : (0 : ℝ) < R' := lt_of_lt_of_le zero_lt_one hR'
    have hRHS : (1 : ℝ) ^ 2 * R' ^ (-(1 : ℝ)) * (4 * A * δ⁻¹ ^ (1 : ℝ)) ^ 2
        * (N : ℝ) ^ P.natDegree
        = 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree / R' := by
      rw [Real.rpow_neg_one, Real.rpow_one, one_pow, one_mul, div_eq_mul_inv]
      ring
    rw [hRHS]
    have hRHSnn : (0 : ℝ) ≤ 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree / R' := by
      have h1 : (0 : ℝ) ≤ 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) (sq_nonneg (δ⁻¹)))
          hNdpos.le
      exact div_nonneg h1 hR'pos.le
    by_cases hbig : A ≤ R'
    · -- nothing survives the truncation
      have hzero : (∑' x : ℤ, (if R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
          = ∑' _x : ℤ, (0 : ℝ) := by
        refine tsum_congr fun x => ?_
        by_cases hx : R' * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
        · have hxR : R < x.natAbs := by
            by_contra hcon
            have h1 : |(x : ℝ)| ≤ (R : ℝ) := by
              rw [abs_cast_eq_natAbs]; exact_mod_cast not_lt.mp hcon
            have h3 : A * (N : ℝ) ^ P.natDegree ≤ R' * (N : ℝ) ^ P.natDegree :=
              mul_le_mul_of_nonneg_right hbig hNdpos.le
            linarith [h1, hRle, h3, hx]
          rw [if_pos hx, hGvan x hxR]; simp
        · rw [if_neg hx]
      rw [hzero, tsum_zero]
      exact hRHSnn
    · -- the crude support bound suffices
      have hR'A : R' < A := lt_of_not_ge hbig
      refine htail.trans ?_
      have h7 : 2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by linarith [hR1']
      have h8 : 3 * (R : ℝ) ≤ 3 * (A * (N : ℝ) ^ P.natDegree) := by linarith [hRle]
      have h9 : 3 * (A * (N : ℝ) ^ P.natDegree)
          ≤ 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree / R' := by
        rw [le_div_iff₀ hR'pos]
        have hstep1 : 3 * (A * (N : ℝ) ^ P.natDegree) * R'
            ≤ 3 * (A * (N : ℝ) ^ P.natDegree) * A :=
          mul_le_mul_of_nonneg_left hR'A.le (by positivity)
        have hstep2 : 3 * (A * (N : ℝ) ^ P.natDegree) * A
            = 3 * A ^ 2 * (N : ℝ) ^ P.natDegree := by ring
        have hstep3 : 3 * A ^ 2 * (N : ℝ) ^ P.natDegree
            ≤ 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree := by
          have hδ2 : (1 : ℝ) ≤ (δ⁻¹) ^ 2 := one_le_pow₀ hδinv1
          have h3δ : (3 : ℝ) ≤ 16 * (δ⁻¹) ^ 2 := by linarith [hδ2]
          have hANnn : (0 : ℝ) ≤ A ^ 2 * (N : ℝ) ^ P.natDegree := by positivity
          calc 3 * A ^ 2 * (N : ℝ) ^ P.natDegree
              = 3 * (A ^ 2 * (N : ℝ) ^ P.natDegree) := by ring
            _ ≤ (16 * (δ⁻¹) ^ 2) * (A ^ 2 * (N : ℝ) ^ P.natDegree) :=
                mul_le_mul_of_nonneg_right h3δ hANnn
            _ = 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree := by ring
        calc 3 * (A * (N : ℝ) ^ P.natDegree) * R'
            ≤ 3 * (A * (N : ℝ) ^ P.natDegree) * A := hstep1
          _ = 3 * A ^ 2 * (N : ℝ) ^ P.natDegree := hstep2
          _ ≤ 16 * A ^ 2 * (δ⁻¹) ^ 2 * (N : ℝ) ^ P.natDegree := hstep3
      linarith [h7, h8, h9]

end Work.KMTAreas.A4Z
