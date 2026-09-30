import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Polynomial growth on an interval (Lemma `poly_growth`)

If a polynomial `P` of degree `≤ k` is bounded by `C` on the interval `[a, a+L]`, then
`|P s| ≤ C (k+1) (k(N+1)+1)^k` for every `s` with `|s - a| ≤ N L`.

The proof writes `P` in the Lagrange basis at the `k+1` equally spaced nodes
`x i = a + i·(L/k)` (`Lagrange.eq_interpolate`), and bounds each basis polynomial
`ℓᵢ(s) = ∏_{j≠i} (s - x_j)/(x_i - x_j)` by `(k(N+1))^k`, using that the nodes are
`L/k`-separated and that each is within `(N+1)L` of `s`.
-/

namespace Work.BMF

open Polynomial Finset

/-- Basic geometry of the equally spaced nodes `x i = a + i·(L/k)` of `Fin (k+1)`, for
`k ≥ 1` and `L > 0`: they all lie in `[a, a+L]`, are within `L` of `a`, and are pairwise
separated by at least `L/k`. -/
theorem poly_growth_nodes (k : ℕ) (hk : 1 ≤ k) (a L : ℝ) (hL : 0 < L) :
    (∀ i : Fin (k + 1), (a + (i : ℝ) * (L / (k : ℝ))) ∈ Set.Icc a (a + L)) ∧
    (∀ i : Fin (k + 1), |(a + (i : ℝ) * (L / (k : ℝ))) - a| ≤ L) ∧
    (∀ i j : Fin (k + 1), i ≠ j →
      L / (k : ℝ) ≤ |(a + (i : ℝ) * (L / (k : ℝ))) - (a + (j : ℝ) * (L / (k : ℝ)))|) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdpos : 0 < L / (k : ℝ) := div_pos hL hkpos
  have hik : ∀ i : Fin (k + 1), (i : ℝ) ≤ (k : ℝ) := by
    intro i
    have h : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
    exact_mod_cast h
  have hkL : (k : ℝ) * (L / (k : ℝ)) = L := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · have h : 0 ≤ (i : ℝ) * (L / (k : ℝ)) := by positivity
      linarith
    · have h : (i : ℝ) * (L / (k : ℝ)) ≤ (k : ℝ) * (L / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (hik i) (le_of_lt hdpos)
      linarith
  · intro i
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
    have h : (i : ℝ) * (L / (k : ℝ)) ≤ (k : ℝ) * (L / (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (hik i) (le_of_lt hdpos)
    linarith
  · intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h1 : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
          have h : i.val + 1 ≤ j.val := hlt
          exact_mod_cast h
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hle : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
          have h : j.val + 1 ≤ i.val := hgt
          exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
    have key : (a + (i : ℝ) * (L / (k : ℝ))) - (a + (j : ℝ) * (L / (k : ℝ)))
        = ((i : ℝ) - (j : ℝ)) * (L / (k : ℝ)) := by ring
    rw [key, abs_mul, abs_of_nonneg (le_of_lt hdpos)]
    calc L / (k : ℝ) = 1 * (L / (k : ℝ)) := by ring
      _ ≤ |(i : ℝ) - (j : ℝ)| * (L / (k : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hdpos)

/-- The `i`-th Lagrange basis polynomial for the full node set `Fin (k+1)`, evaluated at `s`,
is at most `(M/d)^k`: each of its `k` factors is a quotient of a distance `≤ M` to a node by
a pairwise node distance `≥ d > 0`. -/
theorem poly_growth_lagrange_bound (k : ℕ) (x : Fin (k + 1) → ℝ) (d M : ℝ) (hd : 0 < d)
    (hM : 0 ≤ M) (i : Fin (k + 1)) (s : ℝ)
    (hsp : ∀ j : Fin (k + 1), j ≠ i → d ≤ |x i - x j|)
    (hdist : ∀ j : Fin (k + 1), |s - x j| ≤ M) :
    |(Lagrange.basis Finset.univ x i).eval s| ≤ (M / d) ^ k := by
  have hcard : (Finset.univ.erase i : Finset (Fin (k + 1))).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hMd : 0 ≤ M / d := div_nonneg hM (le_of_lt hd)
  simp only [Lagrange.basis]
  rw [Polynomial.eval_prod, Finset.abs_prod]
  have hbd : ∀ j ∈ Finset.univ.erase i,
      |Polynomial.eval s (Lagrange.basisDivisor (x i) (x j))| ≤ M / d := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hxd : d ≤ |x i - x j| := hsp j hji
    have hpos : 0 < |x i - x j| := lt_of_lt_of_le hd hxd
    have h1 : |x i - x j|⁻¹ ≤ d⁻¹ := (inv_le_inv₀ hpos hd).mpr hxd
    have h2 : |s - x j| ≤ M := hdist j
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [abs_mul, abs_inv]
    calc |x i - x j|⁻¹ * |s - x j| ≤ d⁻¹ * M := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = M / d := by ring
  calc ∏ j ∈ Finset.univ.erase i, |Polynomial.eval s (Lagrange.basisDivisor (x i) (x j))|
      ≤ ∏ j ∈ Finset.univ.erase i, (M / d) :=
          Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => hbd j hj)
    _ = (M / d) ^ (Finset.univ.erase i).card := by rw [Finset.prod_const]
    _ = (M / d) ^ k := by rw [hcard]

theorem poly_growth (k : ℕ) (C N a L : ℝ) (hL : 0 < L) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    ∀ P : Polynomial ℝ, P ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) →
      (∀ t ∈ Set.Icc a (a + L), |P.eval t| ≤ C) →
      ∀ s : ℝ, |s - a| ≤ N * L → |P.eval s| ≤ C * ((k : ℝ) + 1) * ((k : ℝ) * (N + 1) + 1) ^ k := by
  intro P hP hbound s hs
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `P` is constant.
    subst hk0
    have hdeg : P.degree ≤ (0 : WithBot ℕ) := (Polynomial.mem_degreeLE).mp hP
    have hPc : P = Polynomial.C (P.coeff 0) := Polynomial.degree_le_zero_iff.mp hdeg
    have ha : a ∈ Set.Icc a (a + L) := ⟨le_rfl, by linarith⟩
    have hb := hbound a ha
    rw [hPc] at hb
    simp only [Polynomial.eval_C] at hb
    rw [hPc]
    simp only [Polynomial.eval_C]
    simpa using hb
  · -- `k ≥ 1`: Lagrange interpolation at the equally spaced nodes.
    have hk1 : 1 ≤ k := hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hdpos : 0 < L / (k : ℝ) := div_pos hL hkpos
    obtain ⟨hn1, hn2, hn3⟩ := poly_growth_nodes k hk1 a L hL
    let x : Fin (k + 1) → ℝ := fun i => a + (i : ℝ) * (L / (k : ℝ))
    have hx_mem : ∀ i, x i ∈ Set.Icc a (a + L) := fun i => hn1 i
    have hx_d : ∀ i, |x i - a| ≤ L := fun i => hn2 i
    have hx_sp : ∀ i j, i ≠ j → L / (k : ℝ) ≤ |x i - x j| := fun i j => hn3 i j
    have hinj : Function.Injective x := by
      intro i j hij
      by_contra hne
      have h := hx_sp i j hne
      rw [hij] at h
      simp only [sub_self, abs_zero] at h
      exact absurd h (not_le.mpr hdpos)
    have hdeg : P.degree ≤ (k : WithBot ℕ) := (Polynomial.mem_degreeLE).mp hP
    have hLag := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin (k + 1))))
        (v := x) (f := P) (by simpa using Set.injOn_univ.mpr hinj) (by
          rw [Finset.card_univ, Fintype.card_fin]
          exact lt_of_le_of_lt hdeg (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self k)))
    have hsum_eq : P.eval s = ∑ i, P.eval (x i) * (Lagrange.basis Finset.univ x i).eval s := by
      conv_lhs => rw [hLag, Lagrange.interpolate_apply]
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C]
    have hxs : ∀ j : Fin (k + 1), |s - x j| ≤ (N + 1) * L := by
      intro j
      have h1 : |s - a| ≤ N * L := hs
      have h2 : |a - x j| ≤ L := by
        have h := hx_d j
        rwa [abs_sub_comm] at h
      calc |s - x j| = |(s - a) + (a - x j)| := by congr 1; ring
        _ ≤ |s - a| + |a - x j| := abs_add_le _ _
        _ ≤ N * L + L := add_le_add h1 h2
        _ = (N + 1) * L := by ring
    have hterm : ∀ i, |(Lagrange.basis Finset.univ x i).eval s| ≤ ((k : ℝ) * (N + 1)) ^ k := by
      intro i
      have hb := poly_growth_lagrange_bound k x (L / (k : ℝ)) ((N + 1) * L) hdpos (by positivity)
        i s (fun j hj => hx_sp i j (Ne.symm hj)) (fun j => hxs j)
      have hrw : (((N + 1) * L) / (L / (k : ℝ))) = (k : ℝ) * (N + 1) := by field_simp
      rwa [hrw] at hb
    rw [hsum_eq]
    calc |∑ i, P.eval (x i) * (Lagrange.basis Finset.univ x i).eval s|
        ≤ ∑ i, |P.eval (x i) * (Lagrange.basis Finset.univ x i).eval s| :=
            Finset.abs_sum_le_sum_abs
              (fun i => P.eval (x i) * (Lagrange.basis Finset.univ x i).eval s) Finset.univ
      _ = ∑ i, |P.eval (x i)| * |(Lagrange.basis Finset.univ x i).eval s| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [abs_mul]
      _ ≤ ∑ i, C * ((k : ℝ) * (N + 1)) ^ k := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (hbound (x i) (hx_mem i)) (hterm i) (abs_nonneg _) hC
      _ = ((k : ℝ) + 1) * (C * ((k : ℝ) * (N + 1)) ^ k) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
      _ ≤ C * ((k : ℝ) + 1) * ((k : ℝ) * (N + 1) + 1) ^ k := by
            have hX : 0 ≤ (k : ℝ) * (N + 1) := by positivity
            have hp : ((k : ℝ) * (N + 1)) ^ k ≤ ((k : ℝ) * (N + 1) + 1) ^ k :=
              pow_le_pow_left₀ hX (by linarith) k
            have hCk : 0 ≤ C * ((k : ℝ) + 1) := by positivity
            calc ((k : ℝ) + 1) * (C * ((k : ℝ) * (N + 1)) ^ k)
                = C * ((k : ℝ) + 1) * ((k : ℝ) * (N + 1)) ^ k := by ring
              _ ≤ C * ((k : ℝ) + 1) * ((k : ℝ) * (N + 1) + 1) ^ k :=
                    mul_le_mul_of_nonneg_left hp hCk

end Work.BMF
