import Mathlib
import Submission.Work.Diff.STE.flat.coeffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform ellipticity of the symmetrised inverse metric matrix

`Work.Diff.STE.flat.coeffA u t x` is the symmetrisation of the inverse of the real matrix
`reMat (u t x)`; it is the coefficient matrix of the principal part of the linearised flat DeTurck
operator (see `Work.Diff.STE.flat.coeffDefs`).  This file proves that the lower ellipticity bound
`reMat (u t x) ⪰ lam · 1` (`lam > 0`, uniformly on the strip `[0,T)`) propagates to
`coeffA u t x ⪰ lam' · 1` on the shorter strip `[0,tstar)`, `tstar < T`.

The point is that `reMat (u t x)` is *not* assumed symmetric: only its quadratic form is bounded
below.  Nevertheless the quadratic form of the inverse is bounded below, because *both* ends of the
matrix are controlled on the shorter strip:

* the entries of `reMat (u t x)` are bounded by a constant `C` on `[0,tstar] × ℝⁿ`
  (continuity on the compact `[0,tstar] × [0,1]ⁿ` together with `1`-periodicity in `x`), so that
  `‖B v‖ ≤ (n C) ‖v‖` for `B = reMat (u t x)`;
* `⟨B v, v⟩ ≥ lam ‖v‖²` by the hypothesis.

For `ξ : Fin n → ℝ` put `u := B⁻¹ ξ`.  Then `ξᵀ B⁻¹ ξ = uᵀ B u ≥ lam ‖u‖²` while
`‖ξ‖ = ‖B u‖ ≤ (n C) ‖u‖`; eliminating `‖u‖` gives the uniform constant
`lam' = lam / ((n:ℝ) * C + 1)²`.

The symmetrised matrix `coeffA u t x` has the same quadratic form as `(reMat (u t x))⁻¹`
(`Work.Diff.STE.flat.coeffA_quadForm_eq`), so the bound is the one required by Gårding's estimate.
-/

noncomputable section

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped Matrix BigOperators

/-- **Uniform bound for the entries of the metric matrix.**  A function `u` that is jointly smooth
on `Ico 0 T × univ` and `1`-periodic in `x` has entries of `reMat (u t x)` bounded by a single
constant on `[0,tstar] × ℝⁿ` for every `tstar < T`.

The bound is a compactness statement: on the compact set `[0,tstar] × [0,1]ⁿ` the (continuous) sum
of the norms of the entries of `u` is bounded, and `1`-periodicity in `x` transports the bound to
all of `ℝⁿ`. -/
lemma exists_reMat_entry_bound_aux {n : ℕ} {T tstar : ℝ} (htstarT : tstar < T)
    (u : ℝ → Torus n)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (huper : ∀ t ∈ Set.Ico (0:ℝ) T, Periodic1 (u t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ i j : Fin n,
      |reMat (u t x) i j| ≤ C := by
  have hKcompact : IsCompact ((Set.Icc (0:ℝ) tstar) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : (Set.Icc (0:ℝ) tstar) ×ˢ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))
      ⊆ Set.Ico (0:ℝ) T ×ˢ Set.univ :=
    fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 htstarT⟩, Set.mem_univ _⟩
  have hcont : ContinuousOn
      (fun p : ℝ × (Fin n → ℝ) => ∑ a : Fin n, ∑ b : Fin n, ‖u p.1 p.2 a b‖)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
    exact continuous_norm.comp_continuousOn (contDiffOn_entry_of_contDiffOn hu a b).continuousOn
  obtain ⟨C₀, hC₀⟩ := hKcompact.exists_bound_of_continuousOn (hcont.mono hKsub)
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro t ht x i j
  have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_trans ht.2 htstarT⟩
  have hperfun : Periodic1 (fun y : Fin n → ℝ => ∑ a : Fin n, ∑ b : Fin n, ‖u t y a b‖) := by
    intro k y
    show (∑ a : Fin n, ∑ b : Fin n, ‖u t (y + Pi.single k 1) a b‖)
      = ∑ a : Fin n, ∑ b : Fin n, ‖u t y a b‖
    rw [huper t htT k y]
  have hbig : ∑ a : Fin n, ∑ b : Fin n, ‖u t x a b‖ ≤ C₀ := by
    rw [← Periodic1.apply_periodicRep hperfun x]
    have h := hC₀ (t, periodicRep x) ⟨⟨ht.1, ht.2.le⟩, fun i _ => periodicRep_mem x i⟩
    have hnn : 0 ≤ ∑ a : Fin n, ∑ b : Fin n, ‖u t (periodicRep x) a b‖ :=
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))
    rwa [Real.norm_of_nonneg hnn] at h
  have h1 : |reMat (u t x) i j| ≤ ‖u t x i j‖ := Complex.abs_re_le_norm _
  have h2 : ‖u t x i j‖ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖u t x a b‖ := norm_entry_le_sum_matC _ i j
  exact le_trans (le_trans (le_trans h1 h2) hbig) (le_max_left _ _)

/-- **Lower bound for the quadratic form of the inverse of a matrix with bounded entries.**
If the quadratic form of `M` dominates `lam ‖·‖²` (`lam > 0`) and the entries of `M` are bounded by
`C ≥ 0`, then the quadratic form of `M⁻¹` dominates `lam / ((n:ℝ) * C + 1)² · ‖·‖²`.

Note that `M` need not be symmetric, and `M⁻¹` is Mathlib's matrix inverse (`adjugate / det`):
the hypothesis forces `det M ≠ 0`, so it is the honest inverse. -/
lemma inv_quadForm_lower_of_entry_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 0 ≤ C)
    (hlow : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, M i j * v i * v j)
    (hentry : ∀ i j : Fin n, |M i j| ≤ C) :
    ∀ ξ : Fin n → ℝ,
      lam / ((n : ℝ) * C + 1) ^ 2 * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, M⁻¹ i j * ξ i * ξ j := by
  intro ξ
  -- `M` is invertible, and `u := M⁻¹ ξ` satisfies `M u = ξ`
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_quadratic hlam hlow)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  set u : Fin n → ℝ := M⁻¹ *ᵥ ξ with hu
  have hMu : M *ᵥ u = ξ := by
    rw [hu, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  -- the normalisation constant is positive
  have hD : (0:ℝ) < (n:ℝ) * C + 1 := by
    have h1 : (0:ℝ) ≤ (n:ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
    linarith
  have hD2 : (0:ℝ) < ((n:ℝ) * C + 1) ^ 2 := pow_pos hD 2
  -- entrywise bound for `M u`
  have hmv : ∀ i : Fin n, ((M *ᵥ u) i) ^ 2 ≤ (C * ∑ j, |u j|) ^ 2 := by
    intro i
    have h1 : |(M *ᵥ u) i| ≤ C * ∑ j, |u j| := by
      rw [Matrix.mulVec_apply_eq_sum]
      calc |∑ j, M i j * u j| ≤ ∑ j, |M i j * u j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |M i j| * |u j| := by simp only [abs_mul]
        _ ≤ ∑ j, C * |u j| :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _))
        _ = C * ∑ j, |u j| := (Finset.mul_sum _ _ _).symm
    calc ((M *ᵥ u) i) ^ 2 = |(M *ᵥ u) i| ^ 2 := (sq_abs _).symm
      _ ≤ (C * ∑ j, |u j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- `∑ ξᵢ² ≤ ((n*C+1)²) * ∑ uᵢ²`
  have hup : ∑ i, (ξ i) ^ 2 ≤ ((n:ℝ) * C + 1) ^ 2 * ∑ i, (u i) ^ 2 := by
    have hsum1 : ∑ i, (ξ i) ^ 2 ≤ (n:ℝ) * (C * ∑ j, |u j|) ^ 2 := by
      rw [← hMu]
      calc ∑ i, ((M *ᵥ u) i) ^ 2 ≤ ∑ i, (C * ∑ j, |u j|) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hmv i)
        _ = (n:ℝ) * (C * ∑ j, |u j|) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hsq : (∑ j, |u j|) ^ 2 ≤ (n:ℝ) * ∑ j, (u j) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => |u j|)
      rw [Finset.sum_congr rfl (fun j _ => sq_abs (u j))] at h
      simpa [Finset.card_univ, Fintype.card_fin] using h
    have hcomb : (n:ℝ) * (C * ∑ j, |u j|) ^ 2
        ≤ ((n:ℝ) * C + 1) ^ 2 * ∑ i, (u i) ^ 2 := by
      have hnn : 0 ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have h1 : (C * ∑ j, |u j|) ^ 2 = C ^ 2 * (∑ j, |u j|) ^ 2 := by ring
      have h2 : (n:ℝ) * (C ^ 2 * (∑ j, |u j|) ^ 2)
          ≤ (n:ℝ) * (C ^ 2 * ((n:ℝ) * ∑ j, (u j) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
      have h3 : (n:ℝ) * (C ^ 2 * ((n:ℝ) * ∑ j, (u j) ^ 2))
          = ((n:ℝ) * C) ^ 2 * ∑ j, (u j) ^ 2 := by ring
      have h4 : ((n:ℝ) * C) ^ 2 ≤ ((n:ℝ) * C + 1) ^ 2 := by
        have h5 : (0:ℝ) ≤ (n:ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC
        nlinarith
      calc (n:ℝ) * (C * ∑ j, |u j|) ^ 2
          = (n:ℝ) * (C ^ 2 * (∑ j, |u j|) ^ 2) := by rw [h1]
        _ ≤ (n:ℝ) * (C ^ 2 * ((n:ℝ) * ∑ j, (u j) ^ 2)) := h2
        _ = ((n:ℝ) * C) ^ 2 * ∑ j, (u j) ^ 2 := h3
        _ ≤ ((n:ℝ) * C + 1) ^ 2 * ∑ j, (u j) ^ 2 :=
            mul_le_mul_of_nonneg_right h4 hnn
    linarith [hsum1, hcomb]
  -- the two quadratic-form identities
  have hkey : ∑ i, ∑ j, M⁻¹ i j * ξ i * ξ j = ∑ i, u i * ξ i := by
    have h1 : ∀ i, ∑ j, M⁻¹ i j * ξ i * ξ j = ξ i * u i := by
      intro i
      rw [hu, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hkey2 : ∑ i, u i * ξ i = ∑ i, ∑ j, M i j * u i * u j := by
    have h1 : ∀ i, u i * ξ i = ∑ j, M i j * u i * u j := by
      intro i
      rw [← hMu, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    exact Finset.sum_congr rfl (fun i _ => h1 i)
  -- multiply the comparison `∑ ξᵢ² ≤ (n*C+1)² ∑ uᵢ²` by `lam / (n*C+1)²`
  have hstep : lam / ((n:ℝ) * C + 1) ^ 2 * ∑ i, (ξ i) ^ 2 ≤ lam * ∑ i, (u i) ^ 2 := by
    have h1 : lam / ((n:ℝ) * C + 1) ^ 2 * ∑ i, (ξ i) ^ 2
        ≤ lam / ((n:ℝ) * C + 1) ^ 2
          * (((n:ℝ) * C + 1) ^ 2 * ∑ i, (u i) ^ 2) :=
      mul_le_mul_of_nonneg_left hup (le_of_lt (div_pos hlam hD2))
    have h2 : lam / ((n:ℝ) * C + 1) ^ 2 * (((n:ℝ) * C + 1) ^ 2 * ∑ i, (u i) ^ 2)
        = lam * ∑ i, (u i) ^ 2 := by
      have hne : ((n:ℝ) * C + 1) ^ 2 ≠ 0 := ne_of_gt hD2
      field_simp
    linarith [h1, h2.le]
  rw [hkey, hkey2]
  linarith [hstep, hlow u]

theorem coeffA_elliptic {n : ℕ} {T tstar : ℝ} (htstarT : tstar < T)
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (huper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (u t))
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j) :
    ∃ lam' : ℝ, 0 < lam' ∧ ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam' * ∑ i, (ξ i) ^ 2
        ≤ ∑ c, ∑ d, Work.Diff.STE.flat.coeffA u t x c d * ξ c * ξ d := by
  obtain ⟨C, hC0, hCb⟩ := exists_reMat_entry_bound_aux htstarT u hu huper
  have hD : (0:ℝ) < (n:ℝ) * C + 1 := by
    have h1 : (0:ℝ) ≤ (n:ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hC0
    linarith
  refine ⟨lam / ((n:ℝ) * C + 1) ^ 2, div_pos hlam (pow_pos hD 2), ?_⟩
  intro t ht x ξ
  rw [coeffA_quadForm_eq]
  exact inv_quadForm_lower_of_entry_aux (reMat (u t x)) hlam hC0
    (fun v => hell t ⟨ht.1, lt_trans ht.2 htstarT⟩ x v) (fun i j => hCb t ht x i j) ξ

end Work.Diff.STE.flat
