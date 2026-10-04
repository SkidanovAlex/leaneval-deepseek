import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.tail_tsum_box_tendsto_zero
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform convergence of the box partial Fourier sums on the flat torus

For a smooth `1`-periodic matrix-valued function `u` on the flat torus, the partial Fourier sums
over the frequency box `box n N = piFinset (i ↦ Icc (-N) N)`,
`seriesFunM (projBox N (fourierCoeffM u))`, converge to `u` **uniformly**.

The proof is entrywise and rests on the `ℓ¹` summability of the Fourier coefficients of a smooth
periodic function, `fourierCoeff_summable_norm`: since the coefficient family is absolutely
summable, the truncated (box) series differs from the full (absolutely convergent) series by
exactly the tail over the complement of the box, whose norm is bounded by the `ℓ¹` tail; the boxes
exhaust `ℤⁿ`, so the `ℓ¹` tails tend to `0`
(`Work.Diff.STE.flat.tail_tsum_box_tendsto_zero`).

The uniform statement is then obtained by applying the entrywise estimate to the (finitely many)
matrix entries and taking the maximum of the corresponding `N₀`.
-/

namespace Work.Diff.STE.flat

open Filter

/-- **`ℓ¹` summability of the Fourier coefficients of a smooth periodic function.**  For
`f : (Fin n → ℝ) → ℂ` of class `C^∞` and `1`-periodic in every coordinate, the coefficient family
`k ↦ fourierCoeff f k` is absolutely summable: rapid (faster than polynomial) decay of the Fourier
coefficients of a smooth function on the torus.

This is `summable_norm_of_CSq` applied to the weighted `ℓ²` summability
`summable_weighted_fourierCoeff_of_contDiff`, at a level `s` above the critical exponent `n/2`. -/
lemma fourierCoeff_summable_norm {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    Summable (fun k : Fin n → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖) :=
  Work.Diff.STE.summable_norm_of_CSq (n + 1)
    (by rw [Fintype.card_fin]; omega) _
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hper (n + 1))

/-- **Pointwise tail bound for the box truncation of a Fourier series.**  If `c` is absolutely
summable, the box-truncated series differs from the full series by at most the `ℓ¹` mass of the
frequencies outside the box:

  `‖seriesFun (projBox N c) x - seriesFun c x‖ ≤ ∑' k ∉ box n N, ‖c k‖`.

The two series are absolutely convergent (`tsum_sub`), the truncated one differs from the full one
only on the complement of the box, and `‖fourierExp k x‖ = 1`. -/
lemma seriesFun_projBox_sub_norm_le {n : ℕ} (c : (Fin n → ℤ) → ℂ)
    (hc : Summable (fun k : Fin n → ℤ => ‖c k‖)) (N : ℕ) (x : Fin n → ℝ) :
    ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N c) x
        - Work.Diff.STE.seriesFun c x‖
      ≤ ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, ‖c k.1‖ := by
  -- Summability of the truncated series (finitely supported) and of the full series.
  have h1 : Summable (fun k : Fin n → ℤ =>
      Work.Diff.STE.Flat.projBox N c k * Work.Diff.STE.fourierExp k x) := by
    refine Summable.of_norm_bounded (g := fun k => ‖c k‖) hc fun k => ?_
    rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    by_cases hk : k ∈ Work.Diff.STE.Flat.box n N
    · rw [Work.Diff.STE.Flat.projBox_apply_of_mem N c hk]
    · rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N c hk, norm_zero]
      exact norm_nonneg _
  have h2 : Summable (fun k : Fin n → ℤ => c k * Work.Diff.STE.fourierExp k x) := by
    refine Summable.of_norm_bounded (g := fun k => ‖c k‖) hc fun k => ?_
    rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
  -- Summability of the norms of the difference, dominated by `2 ‖c k‖`.
  have hnorm : Summable (fun k : Fin n → ℤ =>
      ‖(Work.Diff.STE.Flat.projBox N c k - c k) * Work.Diff.STE.fourierExp k x‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hc.mul_left 2)
    rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    by_cases hk : k ∈ Work.Diff.STE.Flat.box n N
    · rw [Work.Diff.STE.Flat.projBox_apply_of_mem N c hk, sub_self, norm_zero]
      positivity
    · rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N c hk, zero_sub, norm_neg]
      linarith [norm_nonneg (c k)]
  have hsplit : Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N c) x
      - Work.Diff.STE.seriesFun c x
      = ∑' k : Fin n → ℤ, (Work.Diff.STE.Flat.projBox N c k - c k)
          * Work.Diff.STE.fourierExp k x := by
    simp only [Work.Diff.STE.seriesFun]
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun k => by ring
  rw [hsplit]
  calc ‖∑' k : Fin n → ℤ, (Work.Diff.STE.Flat.projBox N c k - c k)
        * Work.Diff.STE.fourierExp k x‖
      ≤ ∑' k : Fin n → ℤ, ‖(Work.Diff.STE.Flat.projBox N c k - c k)
          * Work.Diff.STE.fourierExp k x‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' k : Fin n → ℤ, ‖Work.Diff.STE.Flat.projBox N c k - c k‖ :=
        tsum_congr fun k => by rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    _ = ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N}, ‖c k.1‖ := by
        rw [← tsum_subtype_eq_of_support_subset (s := {k : Fin n → ℤ |
              k ∉ Work.Diff.STE.Flat.box n N}) ?_]
        · refine tsum_congr fun k => ?_
          rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N c k.2, zero_sub, norm_neg]
        · intro k hk
          by_cases hkb : k ∈ Work.Diff.STE.Flat.box n N
          · have hz : ‖Work.Diff.STE.Flat.projBox N c k - c k‖ = 0 := by
              rw [Work.Diff.STE.Flat.projBox_apply_of_mem N c hkb, sub_self, norm_zero]
            exact absurd hz hk
          · exact hkb

/-- **Entrywise uniform convergence of the box partial sums.**  For a smooth `1`-periodic
`f : (Fin n → ℝ) → ℂ` the box partial Fourier sums converge uniformly to `f`. -/
theorem seriesFun_projBox_uniform {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : Fin n → ℝ,
      ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
        (Work.Diff.STE.fourierCoeff f)) x - f x‖ ≤ ε := by
  intro ε hε
  have hc := fourierCoeff_summable_norm f hf hper
  have htail := Work.Diff.STE.flat.tail_tsum_box_tendsto_zero
    (fun k : Fin n → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖)
  have hlt : ∀ᶠ N : ℕ in atTop,
      (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
        ‖Work.Diff.STE.fourierCoeff f k.1‖) < ε :=
    (tendsto_order.1 htail).2 ε hε
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
        ‖Work.Diff.STE.fourierCoeff f k.1‖) < ε := (eventually_atTop.1 hlt)
  refine ⟨N₀, fun N hN x => ?_⟩
  calc ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
        (Work.Diff.STE.fourierCoeff f)) x - f x‖
      = ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.fourierCoeff f)) x
          - Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff f) x‖ := by
        rw [seriesFun_fourierCoeff f hf hper x]
    _ ≤ ∑' k : {k : Fin n → ℤ // k ∉ Work.Diff.STE.Flat.box n N},
          ‖Work.Diff.STE.fourierCoeff f k.1‖ := seriesFun_projBox_sub_norm_le _ hc N x
    _ ≤ ε := le_of_lt (hN₀ N hN)

/-- The `(i,j)`-entry of `seriesFunM (projBox N (fourierCoeffM u))` is the box partial sum of the
`(i,j)`-entry of `u`. -/
lemma seriesFunM_projBox_fourierCoeffM_apply {n : ℕ} (u : Work.Diff.STE.Flat.Torus n) (N : ℕ)
    (x : Fin n → ℝ) (i j : Fin n) :
    Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N
        (Work.Diff.STE.Flat.fourierCoeffM u)) x i j
      = Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => u y i j))) x := by
  rw [Work.Diff.STE.Flat.seriesFunM_apply]
  congr 1
  funext k
  by_cases hk : k ∈ Work.Diff.STE.Flat.box n N
  · rw [Work.Diff.STE.Flat.projBox_apply_of_mem N _ hk,
      Work.Diff.STE.Flat.projBox_apply_of_mem N _ hk]
    rfl
  · rw [Work.Diff.STE.Flat.projBox_apply_of_not_mem N _ hk,
      Work.Diff.STE.Flat.projBox_apply_of_not_mem N _ hk]
    rfl

/-- **Uniform convergence of the box partial Fourier sums on the torus** (matrix-valued form).
For a smooth `1`-periodic `u : Torus n` and every `ε > 0` there is `N₀` such that for all `N ≥ N₀`
the box partial sum `seriesFunM (projBox N (fourierCoeffM u))` is within `ε` of `u` everywhere. -/
theorem fourier_projBox_uniform_tendsto {n : ℕ} (u : Work.Diff.STE.Flat.Torus n)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hper : Work.Diff.STE.Periodic1 u) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : Fin n → ℝ,
      ‖Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.Flat.fourierCoeffM u)) x - u x‖ ≤ ε := by
  intro ε hε
  -- Entrywise uniform convergence, with a bound `N₀ i j` for each entry.
  have hentry : ∀ i j : Fin n, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : Fin n → ℝ,
      ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => u y i j))) x - u x i j‖ ≤ ε := by
    intro i j
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u y i j) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u y i) := (contDiff_pi.mp hu) i
      exact (contDiff_pi.mp h1) j
    have hp : Work.Diff.STE.Periodic1 (fun y : Fin n → ℝ => u y i j) :=
      fun a y => congrArg (fun F : Work.Diff.STE.Flat.MatC n => F i j) (hper a y)
    exact seriesFun_projBox_uniform _ hcd hp ε hε
  choose N₀ hN₀ using hentry
  refine ⟨(Finset.univ : Finset (Fin n)).sup
    (fun i => (Finset.univ : Finset (Fin n)).sup (fun j => N₀ i j)), fun N hN x => ?_⟩
  have hM : ∀ i j : Fin n, N₀ i j ≤ (Finset.univ : Finset (Fin n)).sup
      (fun i => (Finset.univ : Finset (Fin n)).sup (fun j => N₀ i j)) := by
    intro i j
    refine le_trans (Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => N₀ i j) (Finset.mem_univ j)) ?_
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (Finset.univ : Finset (Fin n)).sup (fun j => N₀ i j)) (Finset.mem_univ i)
  rw [pi_norm_le_iff_of_nonneg (le_of_lt hε)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (le_of_lt hε)]
  intro j
  have hdiff : (Work.Diff.STE.Flat.seriesFunM (Work.Diff.STE.Flat.projBox N
        (Work.Diff.STE.Flat.fourierCoeffM u)) x - u x) i j
      = Work.Diff.STE.seriesFun (Work.Diff.STE.Flat.projBox N
          (Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => u y i j))) x - u x i j := by
    simp only [Pi.sub_apply, seriesFunM_projBox_fourierCoeffM_apply]
  rw [hdiff]
  exact hN₀ i j N (le_trans (hM i j) hN) x

end Work.Diff.STE.flat
