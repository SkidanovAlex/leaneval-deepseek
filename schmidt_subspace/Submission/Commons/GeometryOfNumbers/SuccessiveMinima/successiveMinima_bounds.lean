import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Submission.Commons.Analysis.Normed.intVec_norm_le_sum_forms
import Submission.Commons.Analysis.Normed.intVec_norm_ge_one
import Submission.Commons.Analysis.Asymptotics.const_mul_two_mul_rpow_le

/-!
# Two-sided bounds for the successive minima of the Schmidt box

For an invertible complex `N × N` matrix `L`, a base `Q ≥ 2`, exponents `c : Fin N → ℝ` and
`lam j` the smallest `t ≥ 0` for which the integer solutions of

  `∀ i, ‖∑ k, L i k * y k‖ ≤ t * Q ^ (c i)`

`ℚ`-span a space of dimension `≥ j + 1`, we show that all `lam j` (`j < N`) are trapped
between `Q ^ (-K)` and `Q ^ K` for a single constant `K > 0`.

* Upper bound: `T := 1 + ∑ i ∑ l ‖L i l‖ Q ^ (-c i)` is admissible at every level `j < N`,
  because each standard basis vector `e_l` satisfies the defining inequalities for `t = T`
  (its `i`-th form is `L i l` and `Q ^ (-c i) * Q ^ (c i) = 1`); hence the `ℚ`-span is all of
  `ℚ ^ N` and `lam j ≤ T`.
* Lower bound: if the span has dimension `≥ 1` it contains a nonzero vector, i.e. there is
  `0 ≠ y ∈ ℤ ^ N` satisfying the inequalities. By the norm equivalence
  `intVec_norm_le_sum_forms`, `1 ≤ ‖y‖ ≤ C ∑ i ‖∑ k, L i k y k‖ ≤ C t ∑ i Q ^ (c i)`, so
  `t ≥ (C ∑ i Q ^ (c i))⁻¹`. This is uniform in `j`, and the `Q ^ K` with
  `2 ^ K ≥ max T (C ∑ i Q ^ (c i))` (available for `Q ≥ 2`) gives the two-sided bound.

The two ingredients `intVec_norm_le_sum_forms` and `intVec_norm_ge_one` are the commons'
norm estimates for integer vectors.
-/

open scoped BigOperators

namespace Commons.GeometryOfNumbers.SuccessiveMinima

theorem successiveMinima_bounds {N : ℕ} (hN : 1 ≤ N)
    (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (Q : ℝ) (hQ : 2 ≤ Q) (c : Fin N → ℝ) (lam : ℕ → ℝ)
    (hlam : ∀ j : ℕ, j < N → lam j = sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
        {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))}) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ, j < N → Q ^ (-K) ≤ lam j ∧ lam j ≤ Q ^ K := by
  classical
  have hQpos : 0 < Q := by linarith
  obtain ⟨C, hCpos, hCnorm⟩ :=
    @Commons.Analysis.Normed.intVec_norm_le_sum_forms (Fin N) _ _ ⟨⟨0, by omega⟩⟩
      (Matrix.of L) hdet
  let Bd : ℝ → Set (Fin N → ℤ) :=
    fun t => {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}
  let g : (Fin N → ℤ) → (Fin N → ℚ) := fun y k => (y k : ℚ)
  let V : ℝ → Submodule ℚ (Fin N → ℚ) := fun t => Submodule.span ℚ (Set.image g (Bd t))
  let T : ℝ := 1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i))
  let Sc : ℝ := ∑ i : Fin N, Q ^ (c i)
  let D : ℝ := C * Sc
  have hTdef : T = 1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i)) := rfl
  have hScdef : Sc = ∑ i : Fin N, Q ^ (c i) := rfl
  have hDdef : D = C * Sc := rfl
  have hTpos : 0 < T := by
    rw [hTdef]
    have h : 0 ≤ ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i)) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun l _ =>
        mul_nonneg (norm_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hQpos _))))
    linarith
  have hScpos : 0 < Sc := by
    rw [hScdef]
    exact Finset.sum_pos (s := Finset.univ) (fun i _ => Real.rpow_pos_of_pos hQpos _)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hDpos : 0 < D := by rw [hDdef]; exact mul_pos hCpos hScpos
  have hsingle_sum : ∀ (l i : Fin N),
      (∑ k, L i k * (((Pi.single l (1 : ℤ) : Fin N → ℤ) k) : ℂ)) = L i l := by
    intro l i
    rw [Finset.sum_eq_single l
      (fun k _ hk => by rw [Pi.single_eq_of_ne hk]; simp)
      (fun hl => absurd (Finset.mem_univ l) hl)]
    simp
  have hTmem : ∀ l : Fin N, (Pi.single l (1 : ℤ) : Fin N → ℤ) ∈ Bd T := by
    intro l i
    rw [hsingle_sum l i]
    have hle : ‖L i l‖ * Q ^ (-(c i)) ≤ T := by
      rw [hTdef]
      have h1 : ‖L i l‖ * Q ^ (-(c i)) ≤ ∑ l' : Fin N, ‖L i l'‖ * Q ^ (-(c i)) :=
        Finset.single_le_sum (f := fun l' => ‖L i l'‖ * Q ^ (-(c i)))
          (s := Finset.univ) (a := l) (fun l' _ => mul_nonneg (norm_nonneg _)
          (le_of_lt (Real.rpow_pos_of_pos hQpos _))) (Finset.mem_univ l)
      have h2 : (∑ l' : Fin N, ‖L i l'‖ * Q ^ (-(c i)))
          ≤ ∑ i' : Fin N, ∑ l' : Fin N, ‖L i' l'‖ * Q ^ (-(c i')) :=
        Finset.single_le_sum (f := fun i' => ∑ l' : Fin N, ‖L i' l'‖ * Q ^ (-(c i')))
          (s := Finset.univ) (a := i) (fun i' _ => Finset.sum_nonneg (fun l' _ =>
            mul_nonneg (norm_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hQpos _))))
          (Finset.mem_univ i)
      linarith
    calc ‖L i l‖ = ‖L i l‖ * 1 := (mul_one _).symm
      _ = ‖L i l‖ * (Q ^ (-(c i)) * Q ^ (c i)) := by
            rw [show Q ^ (-(c i)) * Q ^ (c i) = 1 by
              rw [← Real.rpow_add hQpos, neg_add_cancel, Real.rpow_zero]]
      _ = (‖L i l‖ * Q ^ (-(c i))) * Q ^ (c i) := by ring
      _ ≤ T * Q ^ (c i) := mul_le_mul_of_nonneg_right hle (le_of_lt (Real.rpow_pos_of_pos hQpos _))
  have hbasis : Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin N))) = ⊤ :=
    (Pi.basisFun ℚ (Fin N)).span_eq
  have hVrankT : Module.finrank ℚ (V T) = N := by
    have hsub : Set.range (Pi.basisFun ℚ (Fin N)) ⊆ Set.image g (Bd T) := by
      rintro a ⟨l, rfl⟩
      refine ⟨(Pi.single l (1 : ℤ) : Fin N → ℤ), hTmem l, ?_⟩
      funext k
      rw [Pi.basisFun_apply]
      by_cases hk : k = l
      · subst hk; simp [g]
      · simp [g, Pi.single_eq_of_ne hk]
    have htop : V T = ⊤ := by
      have h := Submodule.span_mono (R := ℚ) hsub
      rw [hbasis] at h
      exact top_le_iff.mp h
    rw [htop]
    rw [finrank_top]
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hlower : ∀ t : ℝ, 1 ≤ Module.finrank ℚ (V t) → D⁻¹ ≤ t := by
    intro t hrank
    have hne : V t ≠ ⊥ := by
      intro hbot
      rw [hbot] at hrank
      simp at hrank
    have hex : ∃ y ∈ Bd t, y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hzero : ∀ a ∈ Set.image g (Bd t), a = 0 := by
        rintro _ ⟨y, hy, rfl⟩
        rw [hcon y hy]
        funext k
        simp [g]
      have hbot : V t = ⊥ := by
        change Submodule.span ℚ (Set.image g (Bd t)) = ⊥
        rw [Submodule.span_eq_bot]
        exact hzero
      exact hne hbot
    obtain ⟨y, hyB, hyne⟩ := hex
    have hynorm : (1 : ℝ) ≤ ‖y‖ := Commons.Analysis.Normed.intVec_norm_ge_one y hyne
    have hsumle : (∑ i : Fin N, ‖∑ k, L i k * (y k : ℂ)‖) ≤ t * Sc := by
      calc (∑ i : Fin N, ‖∑ k, L i k * (y k : ℂ)‖) ≤ ∑ i : Fin N, t * Q ^ (c i) :=
            Finset.sum_le_sum (fun i _ => hyB i)
        _ = t * Sc := by rw [hScdef, Finset.mul_sum]
    have h1 : ‖y‖ ≤ C * (∑ i : Fin N, ‖∑ k, L i k * (y k : ℂ)‖) := hCnorm y
    have h2 : C * (∑ i : Fin N, ‖∑ k, L i k * (y k : ℂ)‖) ≤ C * (t * Sc) :=
      mul_le_mul_of_nonneg_left hsumle (le_of_lt hCpos)
    have hkey : 1 ≤ t * (C * Sc) := by
      calc (1 : ℝ) ≤ C * (t * Sc) := le_trans hynorm (le_trans h1 h2)
        _ = t * (C * Sc) := by ring
    rw [hDdef, inv_le_iff_one_le_mul₀ (mul_pos hCpos hScpos)]
    exact hkey
  obtain ⟨K, hKpos, hKge⟩ : ∃ K : ℝ, 0 < K ∧ max T D ≤ Q ^ K := by
    obtain ⟨d, hdpos, hdle⟩ :=
      Commons.Analysis.Asymptotics.exists_two_rpow_ge_pos (max T D)
        (lt_of_lt_of_le hTpos (le_max_left T D))
    refine ⟨d, hdpos, ?_⟩
    calc max T D ≤ (2 : ℝ) ^ d := hdle
      _ ≤ Q ^ d := Real.rpow_le_rpow (by norm_num) hQ (le_of_lt hdpos)
  refine ⟨K, hKpos, fun j hj => ?_⟩
  have hmem : T ∈ {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} :=
    ⟨le_of_lt hTpos, by rw [hVrankT]; omega⟩
  have hlow : ∀ t ∈ {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)}, D⁻¹ ≤ t := by
    intro t ht
    exact hlower t (le_trans (by omega : 1 ≤ j + 1) ht.2)
  have hQK : Q ^ (-K) ≤ D⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hQpos), inv_le_inv₀ (Real.rpow_pos_of_pos hQpos K) hDpos]
    exact le_trans (le_max_right T D) hKge
  rw [hlam j hj]
  change Q ^ (-K) ≤ sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} ∧
    sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} ≤ Q ^ K
  constructor
  · exact le_trans hQK (le_csInf ⟨T, hmem⟩ hlow)
  · exact le_trans (csInf_le ⟨0, fun t ht => ht.1⟩ hmem) (le_trans (le_max_left T D) hKge)

end Commons.GeometryOfNumbers.SuccessiveMinima