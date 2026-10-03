/-
**NOTE — the lemma `Work.A6HighLow.ennreal_mixed_minkowski` is FALSE as elaborated.**

In the sibling file `Submission/Work/A6HighLow/ennreal_mixed_minkowski.lean` the right hand side
ends in `^ (1 / 2)`.  The base of that power is an `ENNReal`, so the exponent is a metavariable,
and a numeral in a metavariable position defaults to `Nat`: Lean elaborates the exponent as
`(1 / 2 : ℕ) = 0`, i.e. the right hand side is `x ^ (0 : ℕ) = 1` for *every* input.  The requested
statement therefore asserts `LHS ≤ 1` for all data, which fails: with `R = 2`, `J = 1`, `Q = 1`
and `a i r = 2` one has `LHS = 4 ^ ((1:ℝ)/2) = 2 > 1 = RHS`.  The formal refutation of that
instance is `ennreal_mixed_minkowski_false` below (the exponent `(1 / 2 : ℕ)` is recorded there in
its elaborated form `((1 : ℕ) / 2)`).

With the missing ascription, i.e. with the exponent `(1 / 2 : ℝ)` (real power `ENNReal.rpow`), the
statement is the true *mixed Minkowski* (Minkowski integral) inequality

  `‖ ‖f‖_{L²(ν)} ‖_{L^R(μ)} ≤ ‖ ‖f‖_{L^R(μ)} ‖_{L²(ν)}`   for `R ≥ 2`,

proved here as `ennreal_mixed_minkowski_rpow`, with the finite-sum Hölder inequality
`ENNReal.inner_le_Lp_mul_Lq` at the conjugate exponents `R/(R-2)` and `R/2` as the only input.
-/
import Mathlib

namespace Work.A6HighLow

/-- The elementary rearrangement `∑ i, c * ∑ r, g i r = c * ∑ r, ∑ i, g i r`. -/
private lemma sum_mul_sum_comm' {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ENNReal) (g : ι → κ → ENNReal) :
    (∑ i, c * ∑ r, g i r) = c * ∑ r, ∑ i, g i r := by
  calc ∑ i, c * ∑ r, g i r
      = ∑ i, ∑ r, c * g i r := by simp only [Finset.mul_sum]
    _ = ∑ r, ∑ i, c * g i r := Finset.sum_comm
    _ = ∑ r, c * ∑ i, g i r := by simp only [Finset.mul_sum]
    _ = c * ∑ r, ∑ i, g i r := by simp only [Finset.mul_sum]

/-- **Mixed Minkowski inequality for finite sums of `ℝ≥0∞`**, in the normalised form needed by
`ennreal_mixed_minkowski`: for `R ≥ 2`, a constant `0 < c < ∞` and finite families
`f : ι → κ → ℝ≥0∞` with `f i r ≠ ∞`,

`(∑ i, (c * ∑ r, (f i r)^2)^(R/2))^(1/R) ≤ (c * ∑ r, (∑ i, (f i r)^R)^(2/R))^(1/2)`.

For `R = 2` both sides are equal; for `R > 2` the proof is the classical one: write
`(G i)^R = (G i)^(R-2) · (G i)^2` with `(G i)^2 = c · ∑ r, (f i r)^2`, exchange the two sums,
apply Hölder at the conjugate exponents `R/(R-2)`, `R/2` to the `i`-sum, factor out `S^((R-2)/R)`
and cancel (all quantities are finite, so cancellation is legitimate). -/
lemma minkowski_fin (R : ℝ) (hR : 2 ≤ R) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ENNReal) (hc : c < ⊤) (f : ι → κ → ENNReal) (hf : ∀ i r, f i r ≠ ⊤) :
    (∑ i, (c * ∑ r, (f i r) ^ (2:ℝ)) ^ (R/2)) ^ (1/R)
      ≤ (c * ∑ r, (∑ i, (f i r) ^ R) ^ (2/R)) ^ ((1:ℝ)/2) := by
  obtain hR2 | hR2 := hR.eq_or_lt
  · subst hR2
    have he : ∀ x : ENNReal, x ^ ((2:ℝ)/2) = x := by
      intro x; rw [show (2:ℝ)/2 = 1 by norm_num, ENNReal.rpow_one]
    simp only [he]
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    exact le_of_eq (sum_mul_sum_comm' c (fun i r => (f i r) ^ (2:ℝ)))
  · have hR2pos : (0:ℝ) < R := by linarith
    have hp : (R/(R-2)).HolderConjugate (R/2) := by
      rw [Real.holderConjugate_iff]
      refine ⟨by rw [one_lt_div (by linarith : (0:ℝ) < R - 2)]; linarith, ?_⟩
      rw [inv_eq_one_div, inv_eq_one_div, one_div_div, one_div_div,
          ← add_div, show R - 2 + 2 = R from by ring, div_self (by linarith : R ≠ 0)]
    set G : ι → ENNReal := fun i => (c * ∑ r, (f i r) ^ (2:ℝ)) ^ ((1:ℝ)/2) with hG
    set S : ENNReal := ∑ i, (G i) ^ R with hS
    set B : κ → ENNReal := fun r => (∑ i, (f i r) ^ R) ^ (2/R) with hB
    have hA_lt : ∀ i, c * ∑ r, (f i r) ^ (2:ℝ) < ⊤ := fun i =>
      ENNReal.mul_lt_top hc (ENNReal.sum_lt_top.mpr fun r _ =>
        ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 2) (hf i r))
    have hG_lt : ∀ i, G i < ⊤ := fun i => by
      simp only [hG]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2) (ne_of_lt (hA_lt i))
    have hS_lt : S < ⊤ := by
      rw [hS]
      exact ENNReal.sum_lt_top.mpr fun i _ =>
        ENNReal.rpow_lt_top_of_nonneg (le_of_lt hR2pos) (ne_of_lt (hG_lt i))
    have hG2 : ∀ i, (G i) ^ (2:ℝ) = c * ∑ r, (f i r) ^ (2:ℝ) := by
      intro i
      rw [hG]
      simp only []
      rw [← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have h1 : S = c * ∑ r, ∑ i, (G i) ^ (R-2) * (f i r) ^ (2:ℝ) := by
      rw [hS]
      calc ∑ i, (G i) ^ R
          = ∑ i, (G i) ^ (R-2) * (c * ∑ r, (f i r) ^ (2:ℝ)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            conv_lhs => rw [show R = R - 2 + 2 from by ring]
            rw [ENNReal.rpow_add_of_nonneg (R-2) 2 (by linarith) (by norm_num), hG2 i]
        _ = ∑ i, c * ((G i) ^ (R-2) * ∑ r, (f i r) ^ (2:ℝ)) := by
            refine Finset.sum_congr rfl fun i _ => ?_; ring
        _ = ∑ i, c * ∑ r, (G i) ^ (R-2) * (f i r) ^ (2:ℝ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            congr 1
            rw [Finset.mul_sum]
        _ = c * ∑ i, ∑ r, (G i) ^ (R-2) * (f i r) ^ (2:ℝ) := by
            rw [Finset.mul_sum]
        _ = c * ∑ r, ∑ i, (G i) ^ (R-2) * (f i r) ^ (2:ℝ) := by
            rw [Finset.sum_comm]
    have holder_r : ∀ r : κ, ∑ i, (G i) ^ (R-2) * (f i r) ^ (2:ℝ) ≤ S ^ ((R-2)/R) * B r := by
      intro r
      have h := ENNReal.inner_le_Lp_mul_Lq Finset.univ
        (fun i : ι => (G i) ^ (R-2)) (fun i : ι => (f i r) ^ (2:ℝ)) hp
      have hs1 : (∑ i, ((G i) ^ (R-2)) ^ (R/(R-2))) = S := by
        rw [hS]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ENNReal.rpow_mul,
            show (R-2) * (R/(R-2)) = R from by
              rw [mul_comm, div_mul_cancel₀ _ (by linarith : R - 2 ≠ 0)]]
      have hs2 : (∑ i, ((f i r) ^ (2:ℝ)) ^ (R/2)) = (∑ i, (f i r) ^ R) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ENNReal.rpow_mul, show (2:ℝ) * (R/2) = R from by ring]
      have he1 : 1 / (R/(R-2)) = (R-2)/R := one_div_div _ _
      have he2 : 1 / (R/2) = 2/R := one_div_div _ _
      rw [hs1, hs2, he1, he2] at h
      exact h
    have key : S ≤ S ^ ((R-2)/R) * (c * ∑ r, B r) := by
      conv_lhs => rw [h1]
      calc c * ∑ r, ∑ i, (G i) ^ (R-2) * (f i r) ^ (2:ℝ)
          ≤ ∑ r, c * (S ^ ((R-2)/R) * B r) := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun r _ => mul_le_mul_right (holder_r r) c
        _ = ∑ r, (S ^ ((R-2)/R) * c) * B r := by
            refine Finset.sum_congr rfl fun r _ => ?_; ring
        _ = (S ^ ((R-2)/R) * c) * ∑ r, B r := by
            rw [Finset.mul_sum]
        _ = S ^ ((R-2)/R) * (c * ∑ r, B r) := by ring
    have hSW : S ^ (2/R) ≤ c * ∑ r, B r := by
      rcases eq_or_ne S 0 with hS0 | hS0
      · rw [hS0, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 2/R)]
        exact bot_le
      · have hne0 : S ^ ((R-2)/R) ≠ 0 := by
          intro hz
          rw [ENNReal.rpow_eq_zero_iff] at hz
          rcases hz with ⟨h1', _⟩ | ⟨h1', _⟩
          · exact hS0 h1'
          · exact (ne_of_lt hS_lt) h1'
        have hsplit : S ^ ((R-2)/R) * S ^ (2/R) = S := by
          rw [← ENNReal.rpow_add_of_nonneg ((R-2)/R) (2/R) (by positivity) (by positivity)]
          rw [show (R-2)/R + 2/R = 1 from by
                rw [← add_div, show R - 2 + 2 = R from by ring,
                    div_self (by linarith : R ≠ 0)]]
          rw [ENNReal.rpow_one]
        have hk : S ^ ((R-2)/R) * S ^ (2/R) ≤ S ^ ((R-2)/R) * (c * ∑ r, B r) := by
          rw [hsplit]; exact key
        have hfin : S ^ ((R-2)/R) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_of_lt hS_lt)
        rw [ENNReal.mul_le_mul_iff_right hne0 hfin] at hk
        exact hk
    have hfinal : S ^ (1/R) ≤ (c * ∑ r, B r) ^ ((1:ℝ)/2) := by
      calc S ^ (1/R) = (S ^ (2/R)) ^ ((1:ℝ)/2) := by
            rw [← ENNReal.rpow_mul, show (2/R) * ((1:ℝ)/2) = 1/R from by
              rw [div_mul_eq_mul_div, show (2:ℝ) * (1/2) = 1 from by norm_num, one_div]]
        _ ≤ (c * ∑ r, B r) ^ ((1:ℝ)/2) := ENNReal.rpow_le_rpow hSW (by norm_num)
    have hS' : S = ∑ i, (c * ∑ r, (f i r) ^ (2:ℝ)) ^ (R/2) := by
      rw [hS]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hG]
      rw [← ENNReal.rpow_mul, show ((1:ℝ)/2) * R = R/2 from by ring]
    have hB' : c * ∑ r, B r = c * ∑ r, (∑ i, (f i r) ^ R) ^ (2/R) := by
      rw [hB]
    rw [hS', hB'] at hfinal
    exact hfinal

/-- **The intended (true) statement**: `ennreal_mixed_minkowski` with the right hand exponent
elaborated at `ℝ`, i.e. as the real power `x ^ ((1:ℝ)/2)`. -/
theorem ennreal_mixed_minkowski_rpow (R : ℝ) (hR : 2 ≤ R) {J Q : ℕ} (a : Fin J → ℕ → ENNReal) :
    (∑ i : Fin J, ((Q : ENNReal)⁻¹ * ∑ r ∈ Finset.range Q, (a i r) ^ (2 : ℝ)) ^ (R / 2)) ^ (1 / R)
      ≤ ((Q : ENNReal)⁻¹ * ∑ r ∈ Finset.range Q,
          (∑ i : Fin J, (a i r) ^ R) ^ (2 / R)) ^ ((1 : ℝ) / 2) := by
  have hRpos : (0:ℝ) < R := by linarith
  by_cases hQ : Q = 0
  · subst hQ
    have h1 : (0:ENNReal) ^ (R/2) = 0 := ENNReal.zero_rpow_of_pos (div_pos hRpos (by norm_num))
    have h2 : (0:ENNReal) ^ (1/R) = 0 := ENNReal.zero_rpow_of_pos (one_div_pos.mpr hRpos)
    have h3 : (0:ENNReal) ^ ((1:ℝ)/2) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, mul_zero,
      h1, h2, h3, le_refl]
  · have hcinv_lt : (Q : ENNReal)⁻¹ < ⊤ := by
      rw [ENNReal.inv_lt_top]
      exact_mod_cast Nat.pos_of_ne_zero hQ
    by_cases htop : ∃ i : Fin J, ∃ r ∈ Finset.range Q, a i r = ⊤
    · obtain ⟨i, r, hr, hir⟩ := htop
      have hB : (∑ r ∈ Finset.range Q, (∑ i : Fin J, (a i r) ^ R) ^ (2 / R)) = ⊤ := by
        rw [ENNReal.sum_eq_top]
        refine ⟨r, hr, ?_⟩
        rw [ENNReal.sum_eq_top.mpr
              ⟨i, Finset.mem_univ i, by rw [hir, ENNReal.top_rpow_of_pos hRpos]⟩,
            ENNReal.top_rpow_of_pos (div_pos (by norm_num) hRpos)]
      have hQinv : (Q : ENNReal)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top Q)
      have hRHS : ((Q : ENNReal)⁻¹ * ∑ r ∈ Finset.range Q,
          (∑ i : Fin J, (a i r) ^ R) ^ (2 / R)) ^ ((1:ℝ)/2) = ⊤ := by
        rw [hB, ENNReal.mul_top hQinv,
            ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < (1:ℝ)/2)]
      rw [hRHS]
      exact le_top
    · push Not at htop
      have hf : ∀ i (r : Fin Q), a i (r : ℕ) ≠ ⊤ :=
        fun i r => htop i (r:ℕ) (Finset.mem_range.mpr r.isLt)
      have key := minkowski_fin R hR (c := (Q:ENNReal)⁻¹) hcinv_lt
        (fun i (r : Fin Q) => a i (r:ℕ)) hf
      simp only [Finset.sum_range] at key ⊢
      exact key

/-- **The statement of `Work.A6HighLow.ennreal_mixed_minkowski` is false.**

In the requested statement the final exponent `(1 / 2)` is a numeral in a metavariable position
(the base is an `ENNReal` power), which Lean elaborates at `Nat`; the right hand side is therefore
`x ^ ((1 / 2 : ℕ)) = x ^ (0 : ℕ) = 1` for every `x`.  The instance below is `R = 2`, `J = 1`,
`Q = 1`, `a ≡ 2` of the requested statement (with that exponent rendered in its elaborated form
`((1 : ℕ) / 2)`); its left hand side is `4 ^ ((1:ℝ)/2) = 2`, so the statement claims `2 ≤ 1`. -/
theorem ennreal_mixed_minkowski_false :
    ¬ ((∑ _ : Fin 1, (((1:ℕ):ENNReal)⁻¹ * ∑ _ ∈ Finset.range 1, (2:ENNReal) ^ (2 : ℝ)) ^ ((2:ℝ) / 2)) ^ (1 / (2:ℝ))
      ≤ (((1:ℕ):ENNReal)⁻¹ * ∑ _ ∈ Finset.range 1,
          (∑ _ : Fin 1, (2:ENNReal) ^ (2:ℝ)) ^ ((2:ℝ) / 2)) ^ ((1:ℕ) / 2)) := by
  intro h
  have hbase : ((1:ℕ):ENNReal)⁻¹ * ∑ r ∈ Finset.range 1, (2:ENNReal) ^ (2:ℝ) = 4 := by
    rw [show ((1:ℕ):ENNReal)⁻¹ = 1 from by norm_num, one_mul]
    rw [Finset.sum_range_one, show ((2:ENNReal) ^ (2:ℝ)) = 4 from by norm_num]
  have hL : (∑ i : Fin 1, (((1:ℕ):ENNReal)⁻¹ * ∑ r ∈ Finset.range 1,
      (2:ENNReal) ^ (2 : ℝ)) ^ ((2:ℝ) / 2)) = 4 := by
    rw [Fin.sum_univ_one, hbase]
    rw [show (2:ℝ)/2 = 1 from by norm_num, ENNReal.rpow_one]
  have hR : ((((1:ℕ):ENNReal)⁻¹ * ∑ r ∈ Finset.range 1,
      (∑ i : Fin 1, (2:ENNReal) ^ (2:ℝ)) ^ ((2:ℝ) / 2)) ^ ((1:ℕ) / 2)) = 1 := by
    simp
  rw [hL, hR] at h
  have hlt : (1:ENNReal) < ((4:ENNReal) ^ ((1:ℝ) / 2)) :=
    ENNReal.one_lt_rpow (by norm_num) (by norm_num)
  exact absurd h (not_le.mpr hlt)

end Work.A6HighLow
