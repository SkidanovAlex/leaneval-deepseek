import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Submission.Commons.Analysis.Normed.intVec_norm_le_sum_forms
import Submission.Commons.Analysis.Normed.intVec_norm_ge_one
import Submission.Commons.Analysis.Asymptotics.const_mul_two_mul_rpow_le

/-!
# Uniform-in-`Q` two-sided bounds for the successive minima of the Schmidt box

For an invertible complex `N × N` matrix `L`, exponents `c : Fin N → ℝ` and `lam j` the
smallest `t ≥ 0` for which the integer solutions of

  `∀ i, ‖∑ k, L i k * y k‖ ≤ t * Q ^ (c i)`

`ℚ`-span a space of dimension `≥ j + 1`, we show that there is a SINGLE constant `K ≥ 1`,
independent of `Q`, such that for every `Q ≥ 2`

  `Q ^ (-K) ≤ lam j ≤ Q ^ K`     (`j < N`).

The proof only keeps the `Q`-dependence where it genuinely happens: the upper bound is
governed by `Mm := ∑ i max 0 (-c i)` (the function `t = 1 + ∑ i ∑ l ‖L i l‖ Q ^ (-c i)`
is admissible when scaled by `Q ^ Mm`) and the lower bound by `Mp := ∑ i max 0 (c i)`
(the constant `D = C ∑ i Q ^ (c i)` of the norm-equivalence is at most a multiple of
`Q ^ Mp`).  Absorbing the `Q`-independent constant factors with `Q ≥ 2` gives the uniform
`K`.

This is the uniform-in-`Q` version of `successiveMinima_bounds`.
-/

open scoped BigOperators

namespace Commons.GeometryOfNumbers.SuccessiveMinima

theorem box_bounds_uniform {N : ℕ} (hN : 1 ≤ N)
    (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0) (c : Fin N → ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Q : ℝ, 2 ≤ Q → ∀ j : ℕ, j < N →
      Q ^ (-K) ≤ sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (Submodule.span ℚ
        (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
          {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))} ∧
      sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (Submodule.span ℚ
        (Set.image (fun y : Fin N → ℤ => fun k => (y k : ℚ))
          {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}))} ≤ Q ^ K := by
  classical
  obtain ⟨C, hCpos, hCnorm⟩ :=
    @Commons.Analysis.Normed.intVec_norm_le_sum_forms (Fin N) _ _ ⟨⟨0, by omega⟩⟩
      (Matrix.of L) hdet
  -- Q-independent constants.
  let B : ℝ := ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖
  let A : ℝ := 1 + B
  let Mm : ℝ := ∑ i : Fin N, max 0 (-(c i))
  let Mp : ℝ := ∑ i : Fin N, max 0 (c i)
  have hBnn : 0 ≤ B :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => norm_nonneg _
  have hApos : 0 < A := by simp only [A]; linarith
  have hMmnn : 0 ≤ Mm :=
    Finset.sum_nonneg fun i _ => le_max_left _ _
  have hMpnn : 0 ≤ Mp :=
    Finset.sum_nonneg fun i _ => le_max_left _ _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨d1, hd1pos, hd1⟩ :=
    Commons.Analysis.Asymptotics.exists_two_rpow_ge_pos A hApos
  obtain ⟨d2, hd2pos, hd2⟩ :=
    Commons.Analysis.Asymptotics.exists_two_rpow_ge_pos (C * (N : ℝ))
      (mul_pos hCpos hNpos)
  refine ⟨max 1 (max (Mm + d1) (Mp + d2)), le_max_left _ _, ?_⟩
  intro Q hQ j hj
  have hQpos : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let Bd : ℝ → Set (Fin N → ℤ) :=
    fun t => {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ t * Q ^ (c i)}
  let gg : (Fin N → ℤ) → (Fin N → ℚ) := fun y k => (y k : ℚ)
  let V : ℝ → Submodule ℚ (Fin N → ℚ) := fun t => Submodule.span ℚ (Set.image gg (Bd t))
  let T : ℝ := 1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i))
  let Sc : ℝ := ∑ i : Fin N, Q ^ (c i)
  let D : ℝ := C * Sc
  have hTdef : T = 1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i)) := rfl
  have hScdef : Sc = ∑ i : Fin N, Q ^ (c i) := rfl
  have hDdef : D = C * Sc := rfl
  have hScpos : 0 < Sc := by
    rw [hScdef]
    exact Finset.sum_pos (s := Finset.univ) (fun i _ => Real.rpow_pos_of_pos hQpos _)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hTpos : 0 < T := by
    rw [hTdef]
    have h : 0 ≤ ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i)) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun l _ =>
        mul_nonneg (norm_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hQpos _))))
    linarith
  have hDpos : 0 < D := by rw [hDdef]; exact mul_pos hCpos hScpos
  -- The standard basis vectors satisfy the box inequalities for `t = T`.
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
      _ ≤ T * Q ^ (c i) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt (Real.rpow_pos_of_pos hQpos _))
  -- Hence `V T = ⊤`, so `T` is admissible at every level `j < N`.
  have hbasis : Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin N))) = ⊤ :=
    (Pi.basisFun ℚ (Fin N)).span_eq
  have hVrankT : Module.finrank ℚ (V T) = N := by
    have hsub : Set.range (Pi.basisFun ℚ (Fin N)) ⊆ Set.image gg (Bd T) := by
      rintro a ⟨l, rfl⟩
      refine ⟨(Pi.single l (1 : ℤ) : Fin N → ℤ), hTmem l, ?_⟩
      funext k
      rw [Pi.basisFun_apply]
      by_cases hk : k = l
      · subst hk; simp [gg]
      · simp [gg, Pi.single_eq_of_ne hk]
    have htop : V T = ⊤ := by
      have h := Submodule.span_mono (R := ℚ) hsub
      rw [hbasis] at h
      exact top_le_iff.mp h
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hTmemSe : T ∈ {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} :=
    ⟨le_of_lt hTpos, by rw [hVrankT]; omega⟩
  -- `T ≤ Q ^ (Mm + d1)`.
  have hQi_le : ∀ i : Fin N, Q ^ (-(c i)) ≤ Q ^ Mm := by
    intro i
    refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
    have h1 : -(c i) ≤ max 0 (-(c i)) := le_max_right _ _
    have h2 : max 0 (-(c i)) ≤ Mm := by
      simp only [Mm]
      exact Finset.single_le_sum (f := fun i' => max 0 (-(c i'))) (s := Finset.univ)
        (a := i) (fun i' _ => le_max_left _ _) (Finset.mem_univ i)
    linarith
  have hT_le_A : T ≤ A * Q ^ Mm := by
    rw [hTdef]
    have hsum : ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i))
        ≤ (∑ i : Fin N, ∑ l : Fin N, ‖L i l‖) * Q ^ Mm := by
      calc ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i))
          ≤ ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ Mm :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ =>
              mul_le_mul_of_nonneg_left (hQi_le i) (norm_nonneg _)))
        _ = (∑ i : Fin N, ∑ l : Fin N, ‖L i l‖) * Q ^ Mm := by
            simp only [Finset.sum_mul]
    have h1le : (1 : ℝ) ≤ Q ^ Mm := Real.one_le_rpow hQ1 hMmnn
    calc 1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖ * Q ^ (-(c i))
        ≤ 1 + (∑ i : Fin N, ∑ l : Fin N, ‖L i l‖) * Q ^ Mm := by linarith
      _ ≤ Q ^ Mm + (∑ i : Fin N, ∑ l : Fin N, ‖L i l‖) * Q ^ Mm := by linarith
      _ = (1 + ∑ i : Fin N, ∑ l : Fin N, ‖L i l‖) * Q ^ Mm := by ring
      _ = A * Q ^ Mm := rfl
  have hT_le_K1 : T ≤ Q ^ (Mm + d1) := by
    have hA_le : A ≤ Q ^ d1 :=
      le_trans hd1 (Real.rpow_le_rpow (by norm_num) hQ (le_of_lt hd1pos))
    calc T ≤ A * Q ^ Mm := hT_le_A
      _ ≤ Q ^ d1 * Q ^ Mm :=
            mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = Q ^ (d1 + Mm) := (Real.rpow_add hQpos d1 Mm).symm
      _ = Q ^ (Mm + d1) := by rw [show d1 + Mm = Mm + d1 by ring]
  -- `D ≤ Q ^ (Mp + d2)`.
  have hci_le : ∀ i : Fin N, c i ≤ Mp := by
    intro i
    have h1 : c i ≤ max 0 (c i) := le_max_right _ _
    have h2 : max 0 (c i) ≤ Mp := by
      simp only [Mp]
      exact Finset.single_le_sum (f := fun i' => max 0 (c i')) (s := Finset.univ)
        (a := i) (fun i' _ => le_max_left _ _) (Finset.mem_univ i)
    linarith
  have hSc_le : Sc ≤ (N : ℝ) * Q ^ Mp := by
    rw [hScdef]
    calc ∑ i : Fin N, Q ^ (c i) ≤ ∑ i : Fin N, Q ^ Mp :=
          Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow_of_exponent_le hQ1 (hci_le i))
      _ = (N : ℝ) * Q ^ Mp := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD_le : D ≤ Q ^ (Mp + d2) := by
    rw [hDdef]
    calc C * Sc ≤ C * ((N : ℝ) * Q ^ Mp) :=
          mul_le_mul_of_nonneg_left hSc_le (le_of_lt hCpos)
      _ = (C * (N : ℝ)) * Q ^ Mp := by ring
      _ ≤ (2 : ℝ) ^ d2 * Q ^ Mp :=
            mul_le_mul_of_nonneg_right hd2 (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ ≤ Q ^ d2 * Q ^ Mp :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (by norm_num) hQ (le_of_lt hd2pos))
              (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = Q ^ (d2 + Mp) := (Real.rpow_add hQpos d2 Mp).symm
      _ = Q ^ (Mp + d2) := by rw [show d2 + Mp = Mp + d2 by ring]
  -- The `Q`-free lower bound on admissible `t`.
  have hlower : ∀ t : ℝ, 1 ≤ Module.finrank ℚ (V t) → D⁻¹ ≤ t := by
    intro t hrank
    have hne : V t ≠ ⊥ := by
      intro hbot
      rw [hbot] at hrank
      simp at hrank
    have hex : ∃ y ∈ Bd t, y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hzero : ∀ a ∈ Set.image gg (Bd t), a = 0 := by
        rintro _ ⟨y, hy, rfl⟩
        rw [hcon y hy]
        funext k
        simp [gg]
      have hbot : V t = ⊥ := by
        change Submodule.span ℚ (Set.image gg (Bd t)) = ⊥
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
  -- Assemble.
  set K := max 1 (max (Mm + d1) (Mp + d2)) with hK
  have hK1ge : Mm + d1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK2ge : Mp + d2 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hTK : T ≤ Q ^ K :=
    le_trans hT_le_K1 (Real.rpow_le_rpow_of_exponent_le hQ1 hK1ge)
  have hDK : D ≤ Q ^ K :=
    le_trans hD_le (Real.rpow_le_rpow_of_exponent_le hQ1 hK2ge)
  have hQnegK_le : Q ^ (-K) ≤ D⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hQpos)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hQpos K) hDpos).mpr hDK
  change Q ^ (-K) ≤ sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} ∧
    sInf {t : ℝ | 0 ≤ t ∧ (j + 1) ≤ Module.finrank ℚ (V t)} ≤ Q ^ K
  constructor
  · refine le_csInf ⟨T, hTmemSe⟩ (fun t ht => ?_)
    exact le_trans hQnegK_le (hlower t (le_trans (by omega : 1 ≤ j + 1) ht.2))
  · exact le_trans (csInf_le ⟨0, fun t ht => ht.1⟩ hTmemSe) hTK

end Commons.GeometryOfNumbers.SuccessiveMinima