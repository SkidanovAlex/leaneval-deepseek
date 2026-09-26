import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.PCopy.Setup
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-!
# Two pccuts of an pcannulus along radial crosscuts: the two pieces are discs

Setup and reduction for `Work.Smooth.SphereJordan.radialTwoCutsPieces`.
-/

/-- `θ ↦ e^{iθ}` is continuous. -/
theorem pccontinuous_circlePoint_self :
    Continuous (Work.Smooth.Jordan.circlePoint : ℝ → Work.Smooth.Jordan.Disc) :=
  Continuous.subtype_mk (by fun_prop : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I))
    (fun θ => by rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I])

theorem pccirclePoint_add_two_pi_self (θ : ℝ) :
    Work.Smooth.Jordan.circlePoint (θ + 2 * Real.pi) = Work.Smooth.Jordan.circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (2 * (Real.pi : ℂ)) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The plane curve traced by the boundary circle of an injective disc map. -/
def pcradialBoundaryCurve (e : C(Work.Smooth.SphereJordan.Disc, ℂ)) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := fun θ => e (Work.Smooth.Jordan.circlePoint θ)
  cont := e.continuous.comp pccontinuous_circlePoint_self
  periodic := fun θ => by
    show e (Work.Smooth.Jordan.circlePoint (θ + 2 * Real.pi)) = e (Work.Smooth.Jordan.circlePoint θ)
    rw [pccirclePoint_add_two_pi_self]

@[simp] theorem pcradialBoundaryCurve_apply (e : C(Work.Smooth.SphereJordan.Disc, ℂ)) (θ : ℝ) :
    (pcradialBoundaryCurve e).γ θ = e (Work.Smooth.Jordan.circlePoint θ) := rfl

theorem pcradialBoundaryCurve_isSimple {e : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (he : Function.Injective e) : (pcradialBoundaryCurve e).IsSimple :=
  fun _ ha _ hb hab => injOn_circlePoint ha hb (he hab)

/-- The corestriction of an injective disc map into the closed unit ball. -/
def pccorestrictDisc {W : Set ℂ} (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (e : C(Work.Smooth.SphereJordan.Disc, ℂ)) (he : Set.range e = W) :
    C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) where
  toFun z := ⟨e z, Metric.ball_subset_closedBall (hWsub (by rw [← he]; exact ⟨z, rfl⟩))⟩
  continuous_toFun := Continuous.subtype_mk e.continuous (fun z =>
    Metric.ball_subset_closedBall (hWsub (by rw [← he]; exact ⟨z, rfl⟩)))

@[simp] theorem pccorestrictDisc_coe {W : Set ℂ} (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (e : C(Work.Smooth.SphereJordan.Disc, ℂ)) (he : Set.range e = W)
    (z : Work.Smooth.SphereJordan.Disc) :
    ((pccorestrictDisc hWsub e he z : Work.Smooth.SphereJordan.Disc) : ℂ) = e z := rfl

theorem pccorestrictDisc_injective {W : Set ℂ} (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (e : C(Work.Smooth.SphereJordan.Disc, ℂ)) (he : Set.range e = W)
    (hinj : Function.Injective e) : Function.Injective (pccorestrictDisc hWsub e he) :=
  fun a b hab => hinj (by
    have h := congrArg (fun z : Work.Smooth.SphereJordan.Disc => (z : ℂ)) hab
    simpa using h)

/-- The bounded side of a simple closed plane curve whose trace lies in the closed unit disc is
contained in the closed unit disc.  (The "ray to infinity" argument: the outward ray through a point
of the bounded side outside the disc is preconnected and avoids the trace, hence lies on the same
side of the curve as the point, which would make the bounded side unbounded.) -/
theorem pcplaneSeparation_V_subset_closedBall' {c : Work.Smooth.Jordan.PlaneCurve}
    (d : Work.Smooth.Jordan.PlaneSeparation c) (hc : c.trace ⊆ Metric.closedBall (0 : ℂ) 1) :
    d.V ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro x hxV
  by_contra hcon
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hcon
  have hx1 : 1 < ‖x‖ := not_le.mp hcon
  set R : Set ℂ := (fun s : ℝ => s • x) '' Set.Ici 1 with hR
  have hRpre : IsPreconnected R :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hxR : x ∈ R := ⟨1, Set.mem_Ici.mpr le_rfl, by simp⟩
  have hRsub : R ⊆ c.traceᶜ := by
    rintro y ⟨s, hs, rfl⟩ hy
    obtain ⟨θ, hθ⟩ := hy
    have hs1 : (1 : ℝ) ≤ s := Set.mem_Ici.mp hs
    have ht : ‖s • x‖ ≤ 1 := by
      have h1 := hc ⟨θ, hθ⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
      exact h1
    have hnorm : ‖s • x‖ = s * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1)]
    have hle : ‖x‖ ≤ ‖s • x‖ := by rw [hnorm]; nlinarith [norm_nonneg x]
    linarith
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset d hRpre hRsub with hU | hV
  · exact Set.disjoint_left.mp d.disjoint_UV (hU hxR) hxV
  · have hb := d.bounded_V.subset hV
    rw [isBounded_iff_forall_norm_le] at hb
    obtain ⟨C, hC⟩ := hb
    have hxn : 0 < ‖x‖ := lt_trans zero_lt_one hx1
    set s : ℝ := (C + 1) / ‖x‖ with hs
    have hs1 : (1 : ℝ) ≤ s := by
      rw [hs, le_div_iff₀ hxn]; linarith [hC x hxR]
    have hmem : s • x ∈ R := ⟨s, hs1, rfl⟩
    have hval : C + 1 ≤ C := by
      calc C + 1 = ‖s • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hs1), hs]
            field_simp
        _ ≤ C := hC _ hmem
    linarith

/-- **Setup.**  From a closed disc `W ⊆ ball 0 1` which is the image of the model disc and two
radial free crosscuts we produce the simple closed plane curve `γ` traced by the boundary of `W`
together with its Schoenflies datum `S` (with `closure S.V = W`), and we locate the inner endpoints
of the two crosscuts on the trace of `γ`.

The elementary point: a point `t • w` of `W` (with `‖w‖ = 1`) whose outward ray avoids `W` cannot be
in the open bounded side `S.V` (which is open, hence would contain a small ball, hence points
`r • w` with `r` slightly bigger than `t`), so it lies on the boundary curve. -/
theorem pcexists_curve_of_disc (h : Work.Smooth.SphereJordan.PlaneHypothesis) {W : Set ℂ}
    (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (hWdisc : ∃ e : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective e ∧ Set.range e = W)
    (w₁ w₂ : ℂ) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (ht₂ : 0 < t₂) (ht₂' : t₂ < 1)
    (hm₁ : t₁ • w₁ ∈ W) (hm₂ : t₂ • w₂ ∈ W)
    (hf₁ : ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ∉ W)
    (hf₂ : ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ∉ W) :
    ∃ (γ : Work.Smooth.Jordan.PlaneCurve) (S : Work.Smooth.Jordan.PlaneSchoenflies γ),
      γ.IsSimple ∧ (∀ θ : ℝ, ‖γ.γ θ‖ < 1) ∧ closure S.V = W ∧
        t₁ • w₁ ∈ γ.trace ∧ t₂ • w₂ ∈ γ.trace := by
  obtain ⟨e, he, hre⟩ := hWdisc
  have hball : ∀ θ : ℝ, ‖(pcradialBoundaryCurve e).γ θ‖ < 1 := by
    intro θ
    have h1 : (pcradialBoundaryCurve e).γ θ ∈ W := by
      rw [← hre]
      exact ⟨Work.Smooth.Jordan.circlePoint θ, rfl⟩
    have h2 := hWsub h1
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h2
  have hs : (pcradialBoundaryCurve e).IsSimple := pcradialBoundaryCurve_isSimple he
  obtain ⟨S⟩ := h (pcradialBoundaryCurve e) hs
  have hFbd : ∀ θ : ℝ,
      ((pccorestrictDisc hWsub e hre (Work.Smooth.Jordan.circlePoint θ) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = (pcradialBoundaryCurve e).γ θ := fun θ => rfl
  obtain ⟨hrange, -⟩ :=
    disc_spans_schoenflies_clean hball S (pccorestrictDisc_injective hWsub e hre he) hFbd
  have hcl : closure S.V = W := by
    rw [← hrange]
    exact hre
  have key : ∀ (t : ℝ) (w : ℂ), ‖w‖ = 1 → t < 1 → t • w ∈ W →
      (∀ r : ℝ, t < r → r < 1 → r • w ∉ W) → t • w ∈ (pcradialBoundaryCurve e).trace := by
    intro t w hw ht1 htw hfree
    have hmem : t • w ∈ closure S.V := by rw [hcl]; exact htw
    have hmem' : t • w ∈ S.V ∪ (pcradialBoundaryCurve e).trace := by
      have h4 : t • w ∈ Set.range S.e := by rw [S.range_e, hcl]; exact htw
      obtain ⟨z, hz⟩ := h4
      have hz1 : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      rcases lt_or_eq_of_le hz1 with hlt | heq
      · refine Or.inl ?_
        have h5 : S.e z ∈ S.V := by
          rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
          exact ⟨z, hlt, rfl⟩
        rwa [hz] at h5
      · refine Or.inr ?_
        obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z heq
        exact ⟨θ, by rw [← hz, ← hθ]; exact (S.boundary θ).symm⟩
    rcases hmem' with h | h
    · exfalso
      obtain ⟨ε₀, hε₀, hε₀'⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds h)
      set ε : ℝ := min ε₀ (1 - t) with hεdef
      have hε : 0 < ε := lt_min hε₀ (by linarith)
      have hεle : ε ≤ ε₀ := min_le_left _ _
      have hε' : Metric.ball (t • w) ε ⊆ S.V := fun z hz => hε₀' (Metric.ball_subset_ball hεle hz)
      have h1 : (t + ε / 2) • w ∈ Metric.ball (t • w) ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : (t + ε / 2) • w - t • w = (ε / 2) • w := by
          rw [add_smul t (ε / 2) w]; abel
        rw [hsub, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by linarith : (0 : ℝ) < ε / 2), hw, mul_one]
        linarith
      have hSW : (t + ε / 2) • w ∈ S.V := hε' h1
      have hεle1 : ε ≤ 1 - t := min_le_right _ _
      refine hfree (t + ε / 2) (by linarith) (by linarith) ?_
      rw [← hcl]
      exact subset_closure hSW
    · exact h
  exact ⟨pcradialBoundaryCurve e, S, hs, hball, hcl,
    key t₁ w₁ hw₁ ht₁' hm₁ hf₁, key t₂ w₂ hw₂ ht₂' hm₂ hf₂⟩
end

end Work.Smooth.SphereJordan
