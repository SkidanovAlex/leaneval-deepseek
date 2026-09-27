import Mathlib
import Submission.Work.Whitney.CutPush.frame_glue
import Submission.Work.Whitney.CutPush.smooth_orthonormal_frame_of_projection_family

/-!
# The local frame field of a smooth family of projections

`NOTES_STATE_S56.md` §6 item 3 (the local half of brick G1-a).  Given a smooth family `Q t` of
orthogonal projections of constant rank `k`, at every point `t₀` there is a *neighbourhood* on which a
smooth orthonormal `k`-frame of `range (Q t)` exists.

The construction avoids any subset selection.  Take an orthonormal frame `b` of `range (Q t₀)`
(pointwise lemma `exists_orthonormal_frame_of_projection`) and put `v i t := Q t (b i)`.  Then
`v · t₀ = b`, so by continuity `v · t` is *close* to the orthonormal family `b` near `t₀`, and

> a family that is pointwise close to an orthonormal one, with `ε·k < 1`, is linearly independent

(`linearIndependent_of_near_orthonormal` below: if `∑ α i • v i = 0` then
`‖∑ α i • b i‖ ≤ ε·k·‖∑ α i • b i‖` because `|α i| ≤ ‖∑ α j • b j‖`, and the orthonormal norm formula
`‖∑ α i • b i‖² = ∑ α i²` kills it).  Gram–Schmidt (`contDiff_gramSchmidtNormed_fin`) then gives the
smooth orthonormal frame, whose span is `range (Q t)` by the dimension count `k = finrank (range Q t)`.
-/

open scoped BigOperators ContDiff Topology
open Set Filter

namespace Work.Whitney.CutPush

/-- **A family close to an orthonormal family is independent.** -/
theorem linearIndependent_of_near_orthonormal {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {b v : Fin k → E} (hb : Orthonormal ℝ b) {ε : ℝ}
    (hε : ε * (k : ℝ) < 1) (hclose : ∀ i, ‖v i - b i‖ ≤ ε) :
    LinearIndependent ℝ v := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact linearIndependent_empty_type
  · rw [Fintype.linearIndependent_iff]
    intro α hα
    -- the orthonormal norm formula
    have hnorm : ‖∑ i, α i • b i‖ ^ 2 = ∑ i, (α i) ^ 2 := sum_smul_norm_sq_orthonormal hb α
    -- each `|α i|` is bounded by the norm of the combination
    have hsingle : ∀ i : Fin k, |α i| ≤ ‖∑ j, α j • b j‖ := by
      intro i
      have h1 : (α i) ^ 2 ≤ ∑ j, (α j) ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin k => (α j) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      have h2 : |α i| = Real.sqrt ((α i) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h2]
      have h3 : Real.sqrt ((α i) ^ 2) ≤ Real.sqrt (∑ j, (α j) ^ 2) := Real.sqrt_le_sqrt h1
      have h4 : Real.sqrt (∑ j, (α j) ^ 2) = ‖∑ j, α j • b j‖ := by
        rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
      rw [h4] at h3
      exact h3
    have hsum : ∑ i, |α i| ≤ (k : ℝ) * ‖∑ j, α j • b j‖ := by
      refine le_trans (Finset.sum_le_sum fun i _ => hsingle i) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- the perturbation identity
    have hkey : ∑ i, α i • (b i - v i) = ∑ i, α i • b i := by
      rw [Finset.sum_congr rfl fun i _ => smul_sub (α i) (b i) (v i), Finset.sum_sub_distrib, hα,
        sub_zero]
    have hbound : ‖∑ i, α i • b i‖ ≤ ε * ∑ i, |α i| := by
      rw [← hkey]
      calc ‖∑ i, α i • (b i - v i)‖ ≤ ∑ i, ‖α i • (b i - v i)‖ := norm_sum_le _ _
        _ = ∑ i, |α i| * ‖v i - b i‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
        _ ≤ ∑ i, |α i| * ε :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hclose i) (abs_nonneg _)
        _ = ε * ∑ i, |α i| := by rw [mul_comm ε, Finset.sum_mul]
    have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hclose ⟨0, hk⟩)
    have hzero : ‖∑ i, α i • b i‖ = 0 := by
      have h2 : ‖∑ i, α i • b i‖ ≤ (ε * (k : ℝ)) * ‖∑ i, α i • b i‖ := by
        calc ‖∑ i, α i • b i‖ ≤ ε * ∑ i, |α i| := hbound
          _ ≤ ε * ((k : ℝ) * ‖∑ i, α i • b i‖) := mul_le_mul_of_nonneg_left hsum hε0
          _ = (ε * (k : ℝ)) * ‖∑ i, α i • b i‖ := by ring
      nlinarith [norm_nonneg (∑ i, α i • b i)]
    intro i
    have hs : ∑ j, (α j) ^ 2 = 0 := by
      rw [← hnorm, hzero]; norm_num
    have h0 : (α i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (α j))).mp hs i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp h0

/-- **Gram–Schmidt smoothness at a point.**  The `ContDiffAt` form of `contDiff_gramSchmidt_fin`: it
only needs independence *at* `t₀`, which is what makes it usable on the neighbourhood supplied by
`linearIndependent_of_near_orthonormal`. -/
theorem contDiffAt_gramSchmidt_fin {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (v : ℝ → Fin k → E) (t₀ : ℝ)
    (hv : ∀ i : Fin k, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i) t₀)
    (hli : LinearIndependent ℝ (v t₀)) (n : Fin k) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) n) t₀ := by
  have key : ∀ m : ℕ, ∀ hm : m < k,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩) t₀ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hstep : (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) ⟨m, hm⟩)
          = fun t : ℝ => v t ⟨m, hm⟩ - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin k),
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (v t) i) (v t ⟨m, hm⟩)
                / (‖InnerProductSpace.gramSchmidt ℝ (v t) i‖ : ℝ) ^ 2)
              • InnerProductSpace.gramSchmidt ℝ (v t) i := by
        funext t
        rw [eq_sub_iff_add_eq]
        exact (InnerProductSpace.gramSchmidt_def'' ℝ (v t) ⟨m, hm⟩).symm
      rw [hstep]
      refine (hv ⟨m, hm⟩).sub ?_
      refine ContDiffAt.sum fun i hi => ?_
      have hi' : (i : ℕ) < m := by
        have h : i < (⟨m, hm⟩ : Fin k) := Finset.mem_Iio.mp hi
        exact h
      have hig : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => InnerProductSpace.gramSchmidt ℝ (v t) i) t₀ :=
        ih (i : ℕ) hi' i.isLt
      have hne : InnerProductSpace.gramSchmidt ℝ (v t₀) i ≠ 0 :=
        InnerProductSpace.gramSchmidt_ne_zero i hli
      have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => (‖InnerProductSpace.gramSchmidt ℝ (v t) i‖ : ℝ) ^ 2) t₀ :=
        (ContDiffAt.norm ℝ hig hne).pow 2
      have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => inner ℝ (InnerProductSpace.gramSchmidt ℝ (v t) i) (v t ⟨m, hm⟩)) t₀ :=
        ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.contDiffAt).comp t₀
          (hig.prodMk (hv ⟨m, hm⟩))
      have hden_ne : (‖InnerProductSpace.gramSchmidt ℝ (v t₀) i‖ : ℝ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr hne)
      exact (hnum.div hden hden_ne).smul hig
  exact key n.val n.isLt

/-- **Normalised Gram–Schmidt smoothness at a point.** -/
theorem contDiffAt_gramSchmidtNormed_fin {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (v : ℝ → Fin k → E) (t₀ : ℝ)
    (hv : ∀ i : Fin k, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i) t₀)
    (hli : LinearIndependent ℝ (v t₀)) (n : Fin k) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) n) t₀ := by
  have hgs := contDiffAt_gramSchmidt_fin v t₀ hv hli n
  have hne : InnerProductSpace.gramSchmidt ℝ (v t₀) n ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero n hli
  have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ‖InnerProductSpace.gramSchmidt ℝ (v t) n‖) t₀ :=
    ContDiffAt.norm ℝ hgs hne
  have hinv := hnorm.inv (norm_ne_zero_iff.mpr hne)
  have hfun : (fun t : ℝ => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) n)
      = fun t : ℝ => (‖InnerProductSpace.gramSchmidt ℝ (v t) n‖)⁻¹
          • InnerProductSpace.gramSchmidt ℝ (v t) n := by
    funext t
    simp [InnerProductSpace.gramSchmidtNormed]
  rw [hfun]
  exact hinv.smul hgs

/-- **A local frame field of a smooth family of projections.**  At every `t₀` there is a neighbourhood
on which the family `range (Q t)` has a smooth orthonormal `k`-frame.

The frame is `gramSchmidtNormed` of the smooth family `t ↦ Q t (b i)`, where `b` is an orthonormal
frame of `range (Q t₀)`; that family equals `b` at `t₀`, hence is independent on a neighbourhood of
`t₀` by `linearIndependent_of_near_orthonormal`, and its span is `range (Q t)` by the dimension count.
The smoothness on the neighbourhood is `contDiffAt_gramSchmidtNormed_fin` at each point (smoothness is
a local property, so the *global* smoothness of the frame is a separate, later step). -/
theorem exists_local_frame_of_projection_family {m k : ℕ}
    (Q : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Q p.1 p.2))
    (hidem : ∀ t : ℝ, Q t * Q t = Q t)
    (hsymm : ∀ t : ℝ, ∀ x y : EuclideanSpace ℝ (Fin m),
      inner ℝ (Q t x) y = inner ℝ x (Q t y))
    (hrank : ∀ t : ℝ,
      Module.finrank ℝ (LinearMap.range (Q t : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin m))) = k)
    (t₀ : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : Fin k → ℝ → EuclideanSpace ℝ (Fin m),
      (∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i) (Metric.ball t₀ η)) ∧
      (∀ t ∈ Metric.ball t₀ η, Orthonormal ℝ (fun i => B i t)) ∧
      (∀ t ∈ Metric.ball t₀ η,
        Submodule.span ℝ (Set.range (fun i => B i t))
          = LinearMap.range (Q t : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin m))) := by
  classical
  -- a pointwise orthonormal frame of `range (Q t₀)`
  obtain ⟨b, hb, hbspan⟩ :=
    exists_orthonormal_frame_of_projection (Q t₀) (hidem t₀) (hsymm t₀) (hrank t₀)
  -- the smooth family `t ↦ Q t (b i)`
  set v : ℝ → Fin k → EuclideanSpace ℝ (Fin m) := fun t i => Q t (b i) with hv
  have hvsm : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => v t i) := by
    intro i
    rw [hv]
    exact hQ.comp (contDiff_id.prodMk contDiff_const)
  -- it equals `b` at `t₀`
  have hvt₀ : ∀ i : Fin k, v t₀ i = b i := by
    intro i
    have hmem : b i ∈ LinearMap.range (Q t₀ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin m)) := by
      rw [← hbspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    have hfix : Q t₀ (b i) = b i := by
      rw [← hy]
      show (Q t₀ * Q t₀) y = Q t₀ y
      rw [hidem t₀]
    simpa [hv] using hfix
  -- closeness to `b` near `t₀`
  set ε : ℝ := 1 / (2 * ((k : ℝ) + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; positivity
  have hεk : ε * (k : ℝ) < 1 := by
    rw [hεdef]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [div_mul_eq_mul_div, one_mul]
    rw [div_lt_one (by positivity)]
    linarith
  have hclose_ev : ∀ᶠ t in 𝓝 t₀, ∀ i : Fin k, ‖v t i - b i‖ < ε := by
    have h1 : ∀ i : Fin k, ∀ᶠ t in 𝓝 t₀, ‖v t i - b i‖ < ε := by
      intro i
      have hcont : ContinuousAt (fun t : ℝ => ‖v t i - b i‖) t₀ :=
        ((hvsm i).continuous.continuousAt.sub continuousAt_const).norm
      have hlt : ‖v t₀ i - b i‖ < ε := by rw [hvt₀ i, sub_self, norm_zero]; exact hεpos
      exact hcont.eventually_lt continuousAt_const hlt
    have h2 := (Finset.eventually_all (Finset.univ : Finset (Fin k))).mpr fun i _ => h1 i
    exact h2.mono fun t ht i => ht i (Finset.mem_univ i)
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hclose_ev
  have hmem_ball : ∀ t : ℝ, |t - t₀| < η → t ∈ Metric.ball t₀ η := by
    intro t ht
    rwa [Metric.mem_ball, Real.dist_eq]
  -- the family is independent on the ball
  have hindep : ∀ t ∈ Metric.ball t₀ η, LinearIndependent ℝ (v t) := by
    intro t ht
    exact linearIndependent_of_near_orthonormal hb hεk fun i => le_of_lt (hη ht i)
  refine ⟨η, hηpos, fun i t => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) i, ?_, ?_, ?_⟩
  · intro i t ht
    exact (contDiffWithinAt_iff_contDiffAt (Metric.isOpen_ball.mem_nhds ht)).mpr
      (contDiffAt_gramSchmidtNormed_fin v t (fun j => (hvsm j).contDiffAt)
        (hindep t ht) i)
  · intro t ht
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hindep t ht)
  · intro t ht
    have h1 : Submodule.span ℝ
          (Set.range (fun i => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v t) i))
        = Submodule.span ℝ (Set.range (v t)) := by
      have hA := InnerProductSpace.span_gramSchmidtNormed (𝕜 := ℝ) (v t) Set.univ
      have hB := InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (v t)
      simp only [Set.image_univ] at hA
      rw [hA, hB]
    rw [h1]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, by simp [hv]⟩
    · rw [finrank_span_eq_card (hindep t ht), hrank t, Fintype.card_fin]

end Work.Whitney.CutPush
