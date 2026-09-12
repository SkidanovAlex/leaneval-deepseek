import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.DiophantineApproximation.Dirichlet

open scoped BigOperators

/-! # Dirichlet-type polynomial lemma

We prove that for every real `ξ`, degree bound `n` and integer bound `Q ≥ 1`
there is a non-zero integer polynomial `P` of degree at most `n`, all of whose
coefficients are bounded by `Q` in absolute value, with `|P(ξ)| ≤ c·Q^(-n)`
for a constant `c > 0` depending only on `n` and `ξ`.

## Proof

Box (pigeonhole) argument on the `(Q+1)^(n+1)` polynomials
`Σ aᵢ ξⁱ` with `0 ≤ aᵢ ≤ Q`. All of these numbers lie in `[-B, B]` where
`B = (n+1)·Q·max 1 |ξ|ⁿ`; subdividing into `(Q+1)^(n+1)-1` intervals of equal
length, two distinct coefficient vectors `f ≠ g` produce values at distance
`≤ 2B/((Q+1)^(n+1)-1) ≤ c·Q^(-n)`. Their difference is the desired polynomial.
-/

-- ============================================================
-- Lemma 1: pigeonhole for finitely many reals in a bounded interval.
-- ============================================================

lemma exists_pair_abs_sub_le_of_card_gt_one {B : ℝ} (hB : 0 < B) {ι : Type*}
    [Fintype ι] (v : ι → ℝ) (hv : ∀ i, |v i| ≤ B)
    (hcard : 2 ≤ Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ |v i - v j| ≤ 2 * B / ((Fintype.card ι - 1 : ℕ) : ℝ) := by
  classical
  let m := Fintype.card ι
  have hm : 2 ≤ m := by simpa [m] using hcard
  have hm1 : (0 : ℝ) < (m - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  let delta : ℝ := 2 * B / ((m - 1 : ℕ) : ℝ)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos (mul_pos (by norm_num) hB) hm1
  have hlen : ((m - 1 : ℕ) : ℝ) * delta = 2 * B := by
    dsimp [delta]
    field_simp [ne_of_gt hm1]
  let box : ι → Fin (m - 1) := fun k =>
    if hk : v k = B then ⟨m - 2, by omega⟩
    else
      have hle0 : 0 ≤ v k + B := by
        have hge : -B ≤ v k := (abs_le.mp (hv k)).1
        linarith
      have ht0 : 0 ≤ (v k + B) / delta := div_nonneg hle0 (le_of_lt hdelta)
      have hlt : (v k + B) / delta < (m - 1 : ℕ) := by
        have hxle : v k ≤ B := (abs_le.mp (hv k)).2
        have hxlt : v k < B := lt_of_le_of_ne hxle hk
        rw [div_lt_iff₀ hdelta]
        calc
          v k + B < 2 * B := by linarith
          _ = ((m - 1 : ℕ) : ℝ) * delta := hlen.symm
      ⟨Nat.floor ((v k + B) / delta), (Nat.floor_lt ht0).2 hlt⟩
  -- each point lies in its box
  have hmcast : ((m - 2 : ℕ) : ℝ) + 1 = ((m - 1 : ℕ) : ℝ) := by
    have hsub : (m - 2 : ℕ) + 1 = m - 1 := by omega
    have := congrArg (fun q : ℕ => (q : ℝ)) hsub
    simpa [Nat.cast_add] using this
  have hmem : ∀ k : ι,
      (((box k : ℕ) : ℝ) * delta ≤ v k + B) ∧
      (v k + B ≤ (((box k : ℕ) : ℝ) + 1) * delta) := by
    intro k
    by_cases hk : v k = B
    · have hbk : (box k : ℕ) = m - 2 := by simp [box, hk]
      constructor
      · calc
          ((box k : ℕ) : ℝ) * delta = ((m - 2 : ℕ) : ℝ) * delta := by rw [hbk]
          _ ≤ ((m - 1 : ℕ) : ℝ) * delta := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast (by omega : (m - 2 : ℕ) ≤ (m - 1 : ℕ))) (le_of_lt hdelta)
          _ = 2 * B := hlen
          _ = v k + B := by rw [hk]; ring
      · have heq : v k + B = (((box k : ℕ) : ℝ) + 1) * delta := by
          calc
            v k + B = 2 * B := by rw [hk]; ring
            _ = ((m - 1 : ℕ) : ℝ) * delta := hlen.symm
            _ = (((m - 2 : ℕ) : ℝ) + 1) * delta := by rw [← hmcast]
            _ = (((box k : ℕ) : ℝ) + 1) * delta := by rw [← hbk]
        exact le_of_eq heq
    · have hle : |v k| ≤ B := hv k
      have hxle : v k ≤ B := (abs_le.mp hle).2
      have hxlt : v k < B := lt_of_le_of_ne hxle hk
      have hge : -B ≤ v k := (abs_le.mp hle).1
      let t : ℝ := (v k + B) / delta
      have ht0 : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (by linarith) (le_of_lt hdelta)
      have hbk : (box k : ℕ) = Nat.floor t := by
        simp [box, hk, t]
      constructor
      · calc
          ((box k : ℕ) : ℝ) * delta = (Nat.floor t : ℝ) * delta := by rw [hbk]
          _ ≤ t * delta := by
            exact mul_le_mul_of_nonneg_right (Nat.floor_le ht0) (le_of_lt hdelta)
          _ = v k + B := by
            dsimp [t]
            field_simp [ne_of_gt hdelta]
      · calc
          v k + B = t * delta := by
            dsimp [t]
            field_simp [ne_of_gt hdelta]
          _ ≤ ((Nat.floor t : ℝ) + 1) * delta := by
            exact le_of_lt (mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t) hdelta)
          _ = (((box k : ℕ) : ℝ) + 1) * delta := by rw [hbk]
  -- pigeonhole
  have hcardbox : Fintype.card (Fin (m - 1)) < Fintype.card ι := by
    dsimp [m]
    rw [Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hboxeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (f := box) hcardbox
  have hidx : ((box i : ℕ) : ℝ) = ((box j : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun q : Fin (m - 1) => (q : ℕ)) hboxeq
  refine ⟨i, j, hij, ?_⟩
  have hi' : ((box i : ℕ) : ℝ) * delta ≤ v i + B ∧ v i + B ≤ (((box i : ℕ) : ℝ) + 1) * delta := hmem i
  have hj' : ((box j : ℕ) : ℝ) * delta ≤ v j + B ∧ v j + B ≤ (((box j : ℕ) : ℝ) + 1) * delta := hmem j
  have hdist : |v i - v j| ≤ delta := by
    have hlo2 : ((box i : ℕ) : ℝ) * delta ≤ v j + B := by
      simpa [hidx] using hj'.1
    have hhi2 : v j + B ≤ (((box i : ℕ) : ℝ) + 1) * delta := by
      simpa [hidx] using hj'.2
    apply abs_sub_le_iff.mpr
    constructor <;> nlinarith
  simpa [m, delta] using hdist

-- ============================================================
-- Lemma 2: the values Σ aᵢ ξⁱ (0 ≤ aᵢ ≤ Q) are bounded by B.
-- ============================================================

private lemma abs_val_le (n Q : ℕ) (ξ : ℝ) (f : Fin (n + 1) → Fin (Q + 1)) :
    |∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)| ≤
      ((n + 1 : ℕ) : ℝ) * (Q : ℝ) * max (1 : ℝ) (|ξ| ^ n) := by
  let M : ℝ := max (1 : ℝ) (|ξ| ^ n)
  have hM : 0 ≤ M := by dsimp [M]; exact le_trans zero_le_one (le_max_left _ _)
  have hxiM : ∀ i : Fin (n + 1), |ξ| ^ (i : ℕ) ≤ M := by
    intro i
    by_cases hle : |ξ| ≤ 1
    · have hp : |ξ| ^ (i : ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg ξ) hle
      exact le_trans hp (le_max_left _ _)
    · have hge : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hle)
      have hp : |ξ| ^ (i : ℕ) ≤ |ξ| ^ n := pow_le_pow_right₀ hge (by omega : (i : ℕ) ≤ n)
      exact le_trans hp (le_max_right _ _)
  calc
    |∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)| ≤
        ∑ j : Fin (n + 1), |((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun j : Fin (n + 1) => ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ))
              (Finset.univ : Finset (Fin (n + 1))))
    _ = ∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * |ξ| ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg, abs_pow]
        exact_mod_cast (Nat.zero_le (f j : ℕ))
    _ ≤ ∑ j : Fin (n + 1), (Q : ℝ) * M := by
        apply Finset.sum_le_sum
        intro j hj
        have hf : ((f j : ℕ) : ℝ) ≤ (Q : ℝ) := by
          exact_mod_cast (Nat.lt_succ_iff.mp (f j).isLt)
        exact mul_le_mul hf (hxiM j) (pow_nonneg (abs_nonneg ξ) _)
          (by exact_mod_cast (Nat.zero_le Q))
    _ = ((n + 1 : ℕ) : ℝ) * (Q : ℝ) * M := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

-- ============================================================
-- Lemma 3: two distinct coefficient vectors give a nonzero
-- polynomial with bounded coefficients, evaluating to the
-- difference of the values.
-- ============================================================

private lemma poly_eval_eq_sub (n Q : ℕ) (ξ : ℝ) (f g : Fin (n + 1) → Fin (Q + 1)) :
    (((∑ j : Fin (n + 1),
        Polynomial.monomial (j : ℕ) (((f j : ℕ) : ℤ) - ((g j : ℕ) : ℤ))).map
          (Int.castRingHom ℝ))).eval ξ =
      (∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)) -
      (∑ j : Fin (n + 1), ((g j : ℕ) : ℝ) * ξ ^ (j : ℕ)) := by
  rw [Polynomial.eval_map]
  rw [Polynomial.eval₂_finsetSum]
  simp [Polynomial.eval₂_monomial]

-- ============================================================
-- Main theorem
-- ============================================================

theorem poly_small_value (n : ℕ) (ξ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q : ℕ, 0 < Q → ∃ P : Polynomial ℤ, P ≠ 0 ∧
      Polynomial.natDegree P ≤ n ∧
      (∀ i : ℕ, i ≤ n → (P.coeff i).natAbs ≤ Q) ∧
      |(P.map (Int.castRingHom ℝ)).eval ξ| ≤ c * ((Q : ℝ) ^ (-(n : ℝ))) := by
  classical
  let M : ℝ := max (1 : ℝ) (|ξ| ^ n)
  let c : ℝ := 2 * ((n + 1 : ℕ) : ℝ) * M
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (mul_pos (by norm_num) h1) hMpos
  refine ⟨c, hcpos, ?_⟩
  intro Q hQ
  let κ : Type := Fin (n + 1) → Fin (Q + 1)
  let m : ℕ := (Q + 1) ^ (n + 1)
  have hcardκ : Fintype.card κ = m := by
    dsimp [κ, m]
    simp
  have hm2 : 2 ≤ Fintype.card κ := by
    rw [hcardκ]
    dsimp [m]
    -- 2 ≤ (Q+1)^{n+1}
    have hQ1 : 2 ≤ Q + 1 := by omega
    have hpq : 2 ^ (n + 1) ≤ (Q + 1) ^ (n + 1) := Nat.pow_le_pow_left hQ1 (n + 1)
    have h2 : 2 ≤ 2 ^ (n + 1) := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n + 1)
      -- this : 2^1 ≤ 2^(n+1)
      simpa using this
    omega
  have hm2m : 2 ≤ m := by omega
  let B : ℝ := ((n + 1 : ℕ) : ℝ) * (Q : ℝ) * M
  have hB : 0 < B := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    dsimp [B]
    exact mul_pos (mul_pos h1 hQpos) hMpos
  have hbound : ∀ f : κ, |∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)| ≤ B := by
    intro f
    exact abs_val_le n Q ξ f
  obtain ⟨f, g, hfg, hdist⟩ :=
    exists_pair_abs_sub_le_of_card_gt_one (B := B) hB
      (fun f : κ => ∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)) hbound hm2
  let P : Polynomial ℤ :=
    ∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (((f j : ℕ) : ℤ) - ((g j : ℕ) : ℤ))
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · -- P ≠ 0
    have hfg' : ∃ j : Fin (n + 1), f j ≠ g j := by
      by_contra h
      apply hfg
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hfg' with ⟨j0, hj0⟩
    intro hP0
    have hc0 : P.coeff (j0 : ℕ) = 0 := by simp [hP0]
    have hc1 : P.coeff (j0 : ℕ) = ((f j0 : ℕ) : ℤ) - ((g j0 : ℕ) : ℤ) := by
      dsimp [P]
      let c : Fin (n + 1) → ℤ := fun j => ((f j : ℕ) : ℤ) - ((g j : ℕ) : ℤ)
      change (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (c j)).coeff (j0 : ℕ) = c j0
      simp [Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b hb hbne
        have hbj : (b : ℕ) ≠ (j0 : ℕ) := by
          intro h; apply hbne; exact Fin.ext h
        simp [hbj]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    have hdiff : ((f j0 : ℕ) : ℤ) - ((g j0 : ℕ) : ℤ) ≠ 0 := by
      intro hz
      apply hj0
      apply Fin.ext
      exact Int.ofNat.inj (sub_eq_zero.mp hz)
    exact hdiff (by simpa [hc1] using hc0)
  · -- natDegree ≤ n
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    dsimp [P]
    let c : Fin (n + 1) → ℤ := fun j => ((f j : ℕ) : ℤ) - ((g j : ℕ) : ℤ)
    change (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (c j)).coeff N = 0
    simp [Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro j hj
    have hjN : (j : ℕ) ≠ N := by
      have hjlt : (j : ℕ) < n + 1 := j.isLt
      omega
    simp [hjN]
  · -- coefficient bounds
    intro i hi
    have hi' : i < n + 1 := by omega
    let ji : Fin (n + 1) := ⟨i, hi'⟩
    have hci : P.coeff i = ((f ji : ℕ) : ℤ) - ((g ji : ℕ) : ℤ) := by
      dsimp [P, ji]
      let c : Fin (n + 1) → ℤ := fun j => ((f j : ℕ) : ℤ) - ((g j : ℕ) : ℤ)
      change (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ) (c j)).coeff i = c ⟨i, hi'⟩
      simp [Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single ⟨i, hi'⟩]
      · simp
      · intro b hb hbne
        have hbi : (b : ℕ) ≠ i := by
          intro h; apply hbne; exact Fin.ext h
        simp [hbi]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    have habs : |(P.coeff i)| ≤ (Q : ℤ) := by
      rw [hci]
      have hf1 : (0 : ℤ) ≤ (f ji : ℕ) := by exact_mod_cast (Nat.zero_le _)
      have hf2 : (f ji : ℕ) ≤ Q := Nat.lt_succ_iff.mp (f ji).isLt
      have hg2 : (g ji : ℕ) ≤ Q := Nat.lt_succ_iff.mp (g ji).isLt
      rw [abs_le]
      constructor <;> omega
    have hnat' : (P.coeff i).natAbs ≤ Q := by
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs
    exact hnat' 
  · -- |P(ξ)| ≤ c * Q^(-n)
    have heval : |(P.map (Int.castRingHom ℝ)).eval ξ| =
        |(∑ j : Fin (n + 1), ((f j : ℕ) : ℝ) * ξ ^ (j : ℕ)) -
         (∑ j : Fin (n + 1), ((g j : ℕ) : ℝ) * ξ ^ (j : ℕ))| := by
      rw [poly_eval_eq_sub n Q ξ f g]
    have hmain : |(P.map (Int.castRingHom ℝ)).eval ξ| ≤
        2 * B / ((m - 1 : ℕ) : ℝ) := by
      rw [heval]
      simpa [hcardκ] using hdist
    let Qn : ℝ := (Q : ℝ) ^ n
    have hQr0 : 0 ≤ (Q : ℝ) := by exact_mod_cast (Nat.zero_le Q)
    have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
    have hQnpos : 0 < Qn := by
      dsimp [Qn]
      exact pow_pos hQr n
    have hrpow : (Q : ℝ) ^ (-(n : ℝ)) = Qn⁻¹ := by
      dsimp [Qn]
      rw [Real.rpow_neg hQr0]
      rw [Real.rpow_natCast]
    have hm1pos : 0 < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < m - 1)
    have hmpow : (Q : ℝ) ^ (n + 1) ≤ ((m - 1 : ℕ) : ℝ) := by
      have hqpow : 1 ≤ Q ^ n := by
        have hq : 1 ≤ Q := by omega
        simpa using (Nat.pow_le_pow_left hq n : 1 ^ n ≤ Q ^ n)
      have hleq : Q ^ (n + 1) + 1 ≤ (Q + 1) ^ (n + 1) := by
        calc
          Q ^ (n + 1) + 1 ≤ Q ^ (n + 1) + Q ^ n := by omega
          _ = (Q + 1) * Q ^ n := by
            rw [pow_succ]
            ring
          _ ≤ (Q + 1) * (Q + 1) ^ n :=
            Nat.mul_le_mul_left (Q + 1) (Nat.pow_le_pow_left (by omega : Q ≤ Q + 1) n)
          _ = (Q + 1) ^ (n + 1) := by
            rw [pow_succ]
            ring
      have hnat : Q ^ (n + 1) ≤ m - 1 := by
        dsimp [m]
        omega
      have hc : (Q : ℝ) ^ (n + 1) ≤ ((m - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      exact hc
    have hQpow : (Q : ℝ) ^ (n + 1) = (Q : ℝ) * Qn := by
      dsimp [Qn]
      rw [pow_succ]
      ring
    -- goal: |eval| ≤ c·(Q:ℝ)^(-(n:ℝ)); rewrite the exponent
    rw [hrpow]
    -- show |eval| ≤ c·Qn⁻¹  ⟺ |eval|·Qn ≤ c
    rw [← div_eq_mul_inv]
    rw [le_div_iff₀ hQnpos]
    calc
      |(P.map (Int.castRingHom ℝ)).eval ξ| * Qn ≤ (2 * B / ((m - 1 : ℕ) : ℝ)) * Qn := by
        exact mul_le_mul_of_nonneg_right hmain (le_of_lt hQnpos)
      _ ≤ c := by
        -- (2B/(m−1))·Qn ≤ c
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hm1pos]
        have h2B : 2 * B * Qn = c * (Q : ℝ) * Qn := by
          dsimp [B, c, Qn]
          ring
        rw [h2B]
        calc
          c * (Q : ℝ) * Qn = c * ((Q : ℝ) * Qn) := by ring
          _ = c * ((Q : ℝ) ^ (n + 1)) := by rw [← hQpow]
          _ ≤ c * ((m - 1 : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_left hmpow (le_of_lt hcpos)

end Commons.NumberTheory.DiophantineApproximation.Dirichlet