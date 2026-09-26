import Submission.Work.Smooth.JordanSeparation.ind_eq_zero_of_avoiding_extension
import Submission.Work.Smooth.JordanSeparation.Unconditional

/-!
# Schoenflies from an injective extension of the curve to the disc

For a `C¹` simple closed plane curve `c` with a `PlaneSeparation` datum `S`, **any** continuous
injective `F : 𝔻 → ℂ` agreeing with `c` on the boundary circle is automatically a
`PlaneSchoenflies` datum: its image is the closure of the bounded side `S.V`.

This is the (⟸) direction of the equivalence recorded in `SCHOENFLIES.md` §1, and it reduces the
whole of the Jordan–Schoenflies theorem in the plane to the single classical statement

> **(E)** every embedding `S¹ → ℂ` extends to an embedding `𝔻 → ℂ`.

The proof uses the argument principle of `ind_eq_zero_of_avoiding_extension`: if a point `z` of the
bounded side were missed by `F`, then `F` would avoid `z` altogether, so `γ` would be null-homotopic
in `ℂ ∖ {z}` and `ind c z = 0`, contradicting `|ind c z| = 1` on the bounded side.  Hence `F` even
maps the *closed* disc onto `closure S.V` — no hypothesis on the image of `F` is needed.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **Schoenflies from an injective extension.**  If `F : 𝔻 → ℂ` is continuous and injective and
agrees with the `C¹` simple closed curve `c` on the boundary circle, then `F` is a spanning disc for
`c`: `Set.range F = closure S.V` for the bounded side `S.V` of any separation of `c`. -/
theorem range_eq_closure_V_of_injective_extension (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) (S : PlaneSeparation c.toPlaneCurve)
    (F : C(Disc, ℂ)) (hinj : Function.Injective F)
    (hbd : ∀ θ : ℝ, F (circlePoint θ) = c.γ θ) :
    Set.range F = closure S.V := by
  classical
  -- the restriction of `F` to the open unit ball, as a map from the subtype
  set g : Metric.ball (0 : ℂ) 1 → ℂ :=
    fun z => F ⟨(z : ℂ), Metric.ball_subset_closedBall z.2⟩ with hg
  have hg_apply : ∀ z : Metric.ball (0 : ℂ) 1, g z = F ⟨(z : ℂ),
      Metric.ball_subset_closedBall z.2⟩ := fun _ => rfl
  haveI : PreconnectedSpace (Metric.ball (0 : ℂ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : ℂ) 1).isPreconnected
  have hgcont : Continuous g :=
    F.continuous.comp (continuous_subtype_val.subtype_mk
      (fun z => Metric.ball_subset_closedBall z.2))
  have hpre : IsPreconnected (Set.range g) := isPreconnected_range hgcont
  -- (i) `F` misses the trace on the open disc
  have hWsub : Set.range g ⊆ c.traceᶜ := by
    rintro y ⟨z, rfl⟩
    rw [Set.mem_compl_iff, PlaneCurve.mem_trace_iff]
    rintro ⟨θ, hθ⟩
    have hzeq : (⟨(z : ℂ), Metric.ball_subset_closedBall z.2⟩ : Disc) = circlePoint θ := by
      apply hinj
      rw [hg_apply z] at hθ
      exact hθ.symm.trans (hbd θ).symm
    have hnorm : ‖(z : ℂ)‖ = 1 := by
      have h1 := congrArg (fun w : Disc => ‖(w : ℂ)‖) hzeq
      rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at h1
      simpa using h1
    have hlt : ‖(z : ℂ)‖ < 1 := by
      have := Metric.mem_ball.mp z.2
      simpa [dist_eq_norm] using this
    rw [hnorm] at hlt
    exact lt_irrefl 1 hlt
  -- (ii) `F` cannot miss a point of the bounded side
  have hSVsub : S.V ⊆ Set.range g := by
    intro y hyV
    by_contra hyW
    have hynotrace : y ∉ c.trace := by
      have : y ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr hyV
      exact this
    have hne : ∀ z : Disc, F z ≠ y := by
      intro z hz
      have hzle : ‖(z : ℂ)‖ ≤ 1 := by
        have := Metric.mem_closedBall.mp z.2
        simpa [dist_eq_norm] using this
      rcases lt_or_eq_of_le hzle with hlt | heq
      · refine hyW ⟨⟨(z : ℂ), ?_⟩, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm] using hlt
        · rw [hg_apply]
          exact (congrArg F (Subtype.ext rfl)).trans hz
      · obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z heq
        exact hynotrace ⟨θ, by rw [← hbd θ, hθ, hz]⟩
    have hz0 : ind c y = 0 := ind_eq_zero_of_avoiding_extension c hynotrace F hne hbd
    have hz1 : |ind c y| = 1 := ind_abs_eq_one_of_mem_V_of_isSimple c hs hyV
    rw [hz0] at hz1
    norm_num at hz1
  -- (iii) and conversely
  have hWsubSV : Set.range g ⊆ S.V := by
    have hsub : Set.range g ⊆ S.U ∪ S.V := by
      rw [S.union_eq]
      exact hWsub
    rcases hpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hsub with h | h
    · exfalso
      obtain ⟨p, hpV⟩ := S.nonempty_V
      exact Set.disjoint_left.mp S.disjoint_UV (h (hSVsub hpV)) hpV
    · exact h
  have hWeq : Set.range g = S.V := Set.Subset.antisymm hWsubSV hSVsub
  -- (iv) the whole image
  have h1 : Set.range F = Set.range g ∪ c.trace := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hzle : ‖(z : ℂ)‖ ≤ 1 := by
        have := Metric.mem_closedBall.mp z.2
        simpa [dist_eq_norm] using this
      rcases lt_or_eq_of_le hzle with hlt | heq
      · refine Or.inl ⟨⟨(z : ℂ), ?_⟩, ?_⟩
        · simpa [Metric.mem_ball, dist_eq_norm] using hlt
        · rw [hg_apply]
      · obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z heq
        exact Or.inr ⟨θ, by rw [← hbd θ, hθ]⟩
    · rintro (⟨z, rfl⟩ | ⟨θ, rfl⟩)
      · exact ⟨⟨(z : ℂ), Metric.ball_subset_closedBall z.2⟩, rfl⟩
      · exact ⟨circlePoint θ, hbd θ⟩
  rw [h1, hWeq]
  exact (closure_V_eq_of_isSimple c hs).symm

/-- **Schoenflies from an injective extension.**  An injective continuous extension of a `C¹` simple
closed plane curve to the disc is a `PlaneSchoenflies` datum (`Work.Smooth.Jordan.PlaneSchoenflies`),
i.e. an embedded disc spanning the curve whose image is the closure of the bounded side. -/
theorem planeSchoenflies_of_injective_extension (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) (S : PlaneSeparation c.toPlaneCurve)
    (F : C(Disc, ℂ)) (hinj : Function.Injective F)
    (hbd : ∀ θ : ℝ, F (circlePoint θ) = c.γ θ) :
    Nonempty (PlaneSchoenflies c.toPlaneCurve) :=
  ⟨⟨S, F, hinj, hbd, range_eq_closure_V_of_injective_extension c hs S F hinj hbd⟩⟩

end

end Work.Smooth.JordanSeparation
