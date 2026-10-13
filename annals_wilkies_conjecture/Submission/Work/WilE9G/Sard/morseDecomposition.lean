import Mathlib
import Submission.Work.WilE9G.Sard.volume_image_eq_zero_of_flat_along_vec
import Submission.Work.WilE9G.Sard.morseCriticality
import Submission.Work.WilE9G.Sard.subFlatOfFderivFlat

/-!
# Morse's decomposition of the critical set

`morseDecomposition` is derived from the criticality theorem
`Work.WilE9G.Sard.morseCriticality`: applied with `s = q - 1` to the coefficient functions
`x ↦ (D f x) (Pi.single j 1) i` of the derivative of `f` (all vanishing on `A`), it produces a
countable chart cover of `A` on whose pieces every coefficient of `D f` is flat of order `q - 1`.
`opNorm_le_sum_coeff'` turns this into the vector flatness of `D f`, `subFlatOfFderivFlat`
upgrades it to the flatness of `f` of order `q`, and the expanding condition of the charts
converts the estimate in the chart parameter into the estimate on the piece.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.WilE9G.Sard

open Set Filter Metric Bornology
open scoped Topology

/-- A countable type admits a surjection from `ℕ` once it is nonempty. -/
theorem surj_of_countable {ι : Type} (h : Countable ι) (hne : Nonempty ι) :
    ∃ g : ℕ → ι, Function.Surjective g := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Function.invFun f, fun i => ⟨f i, ?_⟩⟩
  exact Function.leftInverse_invFun hf i

/-- The operator norm of a linear map `ℝ^d → ℝ^n` is bounded by the sum of the absolute values of
its matrix coefficients. -/
theorem opNorm_le_sum_coeff' {d n : ℕ} (A : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ‖A‖ ≤ ∑ p : Fin d × Fin n, ‖A (Pi.single p.1 1) p.2‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun p _ => norm_nonneg _))
    (fun x => ?_)
  have hx : x = ∑ j : Fin d, x j • Pi.single j (1 : ℝ) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro b _ hb; rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hAx : A x = ∑ j : Fin d, x j • A (Pi.single j (1 : ℝ)) := by
    conv_lhs => rw [hx]
    rw [map_sum]; simp [map_smul]
  rw [hAx]
  calc ‖∑ j : Fin d, x j • A (Pi.single j (1 : ℝ))‖
      ≤ ∑ j : Fin d, ‖x j • A (Pi.single j (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ j : Fin d, |x j| * ‖A (Pi.single j (1 : ℝ))‖ := by
        simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin d, ‖x‖ * ∑ i : Fin n, ‖A (Pi.single j (1 : ℝ)) i‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        calc |x j| * ‖A (Pi.single j (1 : ℝ))‖
            ≤ ‖x‖ * ‖A (Pi.single j (1 : ℝ))‖ :=
              mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _)
          _ ≤ ‖x‖ * ∑ i : Fin n, ‖A (Pi.single j (1 : ℝ)) i‖ :=
              mul_le_mul_of_nonneg_left
                ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
                  (fun i => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)))
                (norm_nonneg _)
    _ = ‖x‖ * ∑ j : Fin d, ∑ i : Fin n, ‖A (Pi.single j (1 : ℝ)) i‖ := by
        rw [Finset.mul_sum]
    _ = (∑ p : Fin d × Fin n, ‖A (Pi.single p.1 1) p.2‖) * ‖x‖ := by
        rw [Fintype.sum_prod_type]
        ring

theorem morseDecomposition {d n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (f : (Fin d → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ q f)
    (A : Set (Fin d → ℝ)) (hA : A ⊆ {x | fderiv ℝ f x = 0}) :
    ∃ A' : ℕ → Set (Fin d → ℝ),
      (∀ j, Bornology.IsBounded (A' j)) ∧
      A ⊆ ⋃ j, A' j ∧
      (∀ j x, x ∈ A' j → ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A' j,
        ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ q) := by
  classical
  rcases Nat.lt_or_ge q 2 with hq_lt | hq2
  · -- ## the case `q = 1`
    have hq1 : q = 1 := by omega
    subst hq1
    refine ⟨fun j => A ∩ closedBall 0 (j + 1),
      fun j => isBounded_closedBall.subset inter_subset_right, ?_, ?_⟩
    · intro y hy
      obtain ⟨j, hj⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨j, hy, by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        linarith [hj]⟩
    · intro j x hx ε hε
      obtain ⟨hxA, -⟩ := hx
      have hx0 : fderiv ℝ f x = 0 := hA hxA
      have hcont : ContinuousAt (fderiv ℝ f) x :=
        (hf.continuous_fderiv (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).continuousAt
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont ε hε
      refine ⟨min δ 1 / 2, by positivity, fun y hy hxy => ?_⟩
      have hyδ : ‖y - x‖ < δ := by
        have h2 : min δ 1 / 2 < δ := by
          have h3 := min_le_left δ 1
          linarith
        linarith
      have hconv : Convex ℝ (closedBall x ‖y - x‖) := convex_closedBall _ _
      have hdiff : ∀ z ∈ closedBall x ‖y - x‖, DifferentiableAt ℝ f z :=
        fun z _ => (hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      have hbd : ∀ z ∈ closedBall x ‖y - x‖, ‖fderiv ℝ f z‖ ≤ ε := by
        intro z hz
        have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz
        have hzδ : dist z x < δ := by
          rw [dist_eq_norm]; linarith
        have := le_of_lt (hδ' hzδ)
        rwa [dist_eq_norm, hx0, sub_zero] at this
      have hmvt := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbd
        (by rw [Metric.mem_closedBall, dist_self]; positivity)
        (by rw [Metric.mem_closedBall, dist_eq_norm])
      simpa [pow_one] using hmvt
  · -- ## the case `q ≥ 2`
    obtain ⟨ι, hcnt, c, P, hPA, hcov, hPsub, hflatG⟩ :=
      morseCriticality (q - 1) d (by omega) A
    -- ### flatness of the coefficient functions of `D f` along the pieces
    have hcoeff : ∀ (i : ι) (u : Fin (c i).t → ℝ), u ∈ ball (c i).base (c i).rad →
        (c i).γ u ∈ P i → ∀ p : Fin d × Fin n, ∀ ε > 0, ∃ ρ > 0, ∀ v, ‖v - u‖ ≤ ρ →
          ‖(fderiv ℝ f ((c i).γ v)) (Pi.single p.1 1) p.2‖ ≤ ε * ‖v - u‖ ^ (q - 1) := by
      intro i u hu huP p ε hε
      have hGdiff : ContDiff ℝ (q - 1)
          (fun x => (fderiv ℝ f x) (Pi.single p.1 1) p.2) := by
        have h1 : ContDiff ℝ (q - 1) (fun x => fderiv ℝ f x) := by
          rw [← contDiffOn_univ]
          refine hf.contDiffOn.fderiv_of_isOpen isOpen_univ ?_
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
          simp [Nat.succ_eq_add_one, add_comm]
        have h2 : ContDiff ℝ (q - 1) (fun x => (fderiv ℝ f x) (Pi.single p.1 1)) :=
          h1.clm_apply contDiff_const
        exact (ContinuousLinearMap.proj (R := ℝ) p.2).contDiff.comp h2
      have hG0 : ∀ x ∈ A, (fun x => (fderiv ℝ f x) (Pi.single p.1 1) p.2) x = 0 := by
        intro x hx
        show (fderiv ℝ f x) (Pi.single p.1 1) p.2 = 0
        rw [hA hx]; rfl
      exact hflatG _ hGdiff hG0 i u hu huP ε hε
    -- ### vector flatness of `D f` along the pieces
    have hDf : ∀ (i : ι) (u : Fin (c i).t → ℝ), u ∈ ball (c i).base (c i).rad →
        (c i).γ u ∈ P i → ∀ ε > 0, ∃ ρ > 0, ∀ v, ‖v - u‖ ≤ ρ →
          ‖fderiv ℝ f ((c i).γ v)‖ ≤ ε * ‖v - u‖ ^ (q - 1) := by
      intro i u hu huP ε hε
      by_cases hne : Nonempty (Fin d × Fin n)
      · have hN : (0 : ℝ) < ((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1 := by positivity
        have hε' : 0 < ε / (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1) :=
          div_pos hε hN
        have hchoose : ∀ p : Fin d × Fin n, ∃ ρ > 0, ∀ v, ‖v - u‖ ≤ ρ →
            ‖(fderiv ℝ f ((c i).γ v)) (Pi.single p.1 1) p.2‖
              ≤ ε / (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1) * ‖v - u‖ ^ (q - 1) :=
          fun p => hcoeff i u hu huP p _ hε'
        choose ρ hρpos hρ using hchoose
        obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image Finset.univ ρ Finset.univ_nonempty
        refine ⟨ρ p₀, hρpos p₀, fun v hv => ?_⟩
        have hvρ : ∀ p : Fin d × Fin n, ‖v - u‖ ≤ ρ p := fun p =>
          hv.trans (hp₀ p (Finset.mem_univ p))
        have hco : ((Fintype.card (Fin d × Fin n) : ℕ) : ℝ)
            / (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hN]; linarith
        calc ‖fderiv ℝ f ((c i).γ v)‖
            ≤ ∑ p : Fin d × Fin n,
                ‖(fderiv ℝ f ((c i).γ v)) (Pi.single p.1 1) p.2‖ :=
              opNorm_le_sum_coeff' _
          _ ≤ ∑ _p : Fin d × Fin n,
                (ε / (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1) * ‖v - u‖ ^ (q - 1)) :=
              Finset.sum_le_sum (fun p _ => hρ p v (hvρ p))
          _ = (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ)
                / (((Fintype.card (Fin d × Fin n) : ℕ) : ℝ) + 1)) * (ε * ‖v - u‖ ^ (q - 1)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
          _ ≤ 1 * (ε * ‖v - u‖ ^ (q - 1)) :=
              mul_le_mul_of_nonneg_right hco (by positivity)
          _ = ε * ‖v - u‖ ^ (q - 1) := one_mul _
      · -- the index type is empty: the operator norm is bounded by the empty sum, hence `0`
        rw [not_nonempty_iff] at hne
        refine ⟨1, one_pos, fun v _ => ?_⟩
        refine (opNorm_le_sum_coeff' (fderiv ℝ f ((c i).γ v))).trans ?_
        rw [Finset.univ_eq_empty, Finset.sum_empty]
        positivity
    -- ### integration: flatness of `f` along the pieces
    have hflat_f : ∀ (i : ι) (u : Fin (c i).t → ℝ), u ∈ ball (c i).base (c i).rad →
        (c i).γ u ∈ P i → ∀ ε > 0, ∃ ρ > 0, ∀ w, ‖w - u‖ ≤ ρ →
          ‖f ((c i).γ w) - f ((c i).γ u)‖ ≤ ε * ‖w - u‖ ^ q := by
      intro i u hu huP
      exact subFlatOfFderivFlat (by omega) (hf.of_le (Nat.cast_le.mpr (by omega : 1 ≤ q)))
        (c i) hu (hDf i u hu huP)
    -- ### assembly
    by_cases hne : Nonempty ι
    · obtain ⟨g, hg⟩ := surj_of_countable hcnt hne
      have hbd : ∀ j, Bornology.IsBounded (P (g j)) := by
        intro j
        refine IsBounded.subset ?_ ((hPsub (g j)).trans (image_mono ball_subset_closedBall))
        exact ((isCompact_closedBall (c (g j)).base (c (g j)).rad).image_of_continuousOn
          (c (g j)).contdiffOn.continuousOn).isBounded
      refine ⟨fun j => P (g j), hbd, ?_, ?_⟩
      · -- covering
        intro y hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
        obtain ⟨k, hk⟩ := hg i
        exact mem_iUnion.mpr ⟨k, by rwa [hk]⟩
      · -- flatness
        intro j x hxP ε hε
        obtain ⟨u, hu, hxu⟩ := hPsub (g j) hxP
        obtain ⟨ρ, hρ, hρ'⟩ := hflat_f (g j) u hu (hxu ▸ hxP) ε hε
        subst hxu
        refine ⟨ρ, hρ, fun y hy hxy => ?_⟩
        obtain ⟨w, hw, hwy⟩ := hPsub (g j) hy
        have hexp := (c (g j)).expanding w (ball_subset_closedBall hw)
          u (ball_subset_closedBall hu)
        have h2 : ‖w - u‖ ≤ ‖y - (c (g j)).γ u‖ := by
          calc ‖w - u‖ ≤ ‖(c (g j)).γ w - (c (g j)).γ u‖ := by
                simpa [dist_eq_norm] using hexp
            _ = ‖y - (c (g j)).γ u‖ := by rw [hwy]
        have hwu : ‖w - u‖ ≤ ρ := h2.trans hxy
        have h1 : ‖f y - f ((c (g j)).γ u)‖ ≤ ε * ‖w - u‖ ^ q := by
          rw [← hwy]; exact hρ' w hwu
        exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 q) hε.le)
    · -- empty index type: `A = ∅`
      refine ⟨fun _ => ∅, fun _ => isBounded_empty, ?_, ?_⟩
      · rw [iUnion_empty]
        by_contra hcon
        obtain ⟨y, hyA⟩ := not_subset.mp hcon
        obtain ⟨i, -⟩ := mem_iUnion.mp (hcov hyA.1)
        exact hne ⟨i⟩
      · intro j x hx; exact absurd hx (by simp)

end Work.WilE9G.Sard
