import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.interior_closure_V_eq

/-!
# The annulus region between a Jordan curve and the boundary circle

Let `γ` be a simple closed plane curve and `S` a Schoenflies datum for it.  The **annulus region**

`annulusRegion S = Metric.closedBall 0 1 \ S.V`

is the closed region between the curve and the boundary circle.  The main result of this file is
that it is **preconnected**: the input which makes the "two cuts" construction work.

If `A ⊆ ℂ` is closed, preconnected and contains `{z | 1 ≤ ‖z‖}` (the complement of the open unit
disc), then `A ∩ 𝔻` is preconnected: given closed disjoint `u`, `v` covering `A ∩ 𝔻`, the circle
`∂𝔻 ⊆ A ∩ 𝔻` is connected and hence lies in one of them, say `u`.  Then `u ∪ {z | 1 ≤ ‖z‖}` and
`v ∩ 𝔻` are closed, disjoint (they meet only in `v ∩ ∂𝔻 = ∅`) and cover `A`, so preconnectedness of
`A` puts `A` in one of them; the second is impossible since `A` contains the point `2`, and the
first gives `A ∩ 𝔻 ⊆ u`.  The case `∂𝔻 ⊆ v` is symmetric.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **The closed region between a curve and the boundary circle**: the closed unit disc with the
bounded side of `γ` removed. -/
def annulusRegion (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 \ S.V

/-- The complement of the *open* unit disc: everything at distance at least one from the origin. -/
def bigUnit : Set ℂ := {z : ℂ | 1 ≤ ‖z‖}

theorem mem_bigUnit {z : ℂ} : z ∈ bigUnit ↔ 1 ≤ ‖z‖ := Iff.rfl

theorem two_mem_bigUnit : (2 : ℂ) ∈ bigUnit := by rw [mem_bigUnit]; norm_num

theorem two_notMem_closedBall : (2 : ℂ) ∉ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]; norm_num

theorem isClosed_bigUnit : IsClosed bigUnit := by
  have h : bigUnit = (Metric.ball (0 : ℂ) 1)ᶜ := by
    ext z
    rw [mem_bigUnit, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right]
    exact ⟨fun h => not_lt.mpr h, fun h => not_lt.mp h⟩
  rw [h]; exact Metric.isOpen_ball.isClosed_compl

theorem sphere_subset_bigUnit : Metric.sphere (0 : ℂ) 1 ⊆ bigUnit := by
  intro x hx
  rw [mem_bigUnit]
  exact (by simpa [Metric.mem_sphere, dist_eq_norm] using hx : ‖x‖ = 1).ge

/-- **A closed, preconnected set containing the complement of the open unit disc meets the closed
unit disc in a preconnected set.** -/
theorem isPreconnected_inter_closedBall_of_isClosed
    {A : Set ℂ} (hAcl : IsClosed A) (hApre : IsPreconnected A) (hout : bigUnit ⊆ A) :
    IsPreconnected (A ∩ Metric.closedBall (0 : ℂ) 1) := by
  have hcl : IsClosed (A ∩ Metric.closedBall (0 : ℂ) 1) :=
    hAcl.inter Metric.isClosed_closedBall
  have h2A : (2 : ℂ) ∈ A := hout two_mem_bigUnit
  have hsphere_in : Metric.sphere (0 : ℂ) 1 ⊆ A ∩ Metric.closedBall (0 : ℂ) 1 := fun x hx =>
    ⟨hout (sphere_subset_bigUnit hx), Metric.sphere_subset_closedBall hx⟩
  have hconn : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    (isConnected_sphere (E := ℂ) (by simp) (0 : ℂ) (by norm_num)).isPreconnected
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hcl]
  intro u v hu hv hcover huv
  have hsp_cov : Metric.sphere (0 : ℂ) 1 ⊆ u ∪ v := fun x hx => hcover (hsphere_in hx)
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed Metric.isClosed_sphere).mp hconn
      u v hu hv hsp_cov huv with hU | hV
  · -- ## `∂𝔻 ⊆ u`
    have hcl1 : IsClosed (u ∪ bigUnit) := hu.union isClosed_bigUnit
    have hcl2 : IsClosed (v ∩ Metric.closedBall (0 : ℂ) 1) :=
      hv.inter Metric.isClosed_closedBall
    have hdisj : Disjoint (u ∪ bigUnit) (v ∩ Metric.closedBall (0 : ℂ) 1) := by
      rw [Set.disjoint_left]
      rintro x (hxu | hx1) ⟨hxv, hxd⟩
      · exact Set.disjoint_left.mp huv hxu hxv
      · have hxsp : x ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [Metric.mem_sphere, dist_eq_norm]
          exact le_antisymm (by simpa using hxd) (by simpa using mem_bigUnit.mp hx1)
        exact Set.disjoint_left.mp huv (hU hxsp) hxv
    have hcovA : A ⊆ (u ∪ bigUnit) ∪ (v ∩ Metric.closedBall (0 : ℂ) 1) := by
      intro x hx
      by_cases hd : x ∈ Metric.closedBall (0 : ℂ) 1
      · rcases hcover ⟨hx, hd⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hd⟩
      · refine Or.inl (Or.inr (mem_bigUnit.mpr ?_))
        rw [Metric.mem_closedBall, dist_zero_right] at hd
        exact le_of_lt (not_le.mp hd)
    rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hAcl).mp hApre _ _ hcl1 hcl2
        hcovA hdisj with h | h
    · refine Or.inl fun x hx => ?_
      rcases h hx.1 with h' | h'
      · exact h'
      · exact hU (by
          rw [Metric.mem_sphere, dist_eq_norm]
          exact le_antisymm (by simpa using hx.2) (by simpa using mem_bigUnit.mp h'))
    · exact absurd (h h2A).2 two_notMem_closedBall
  · -- ## `∂𝔻 ⊆ v`
    have hcl1 : IsClosed (u ∩ Metric.closedBall (0 : ℂ) 1) :=
      hu.inter Metric.isClosed_closedBall
    have hcl2 : IsClosed (v ∪ bigUnit) := hv.union isClosed_bigUnit
    have hdisj : Disjoint (u ∩ Metric.closedBall (0 : ℂ) 1) (v ∪ bigUnit) := by
      rw [Set.disjoint_left]
      rintro x ⟨hxu, hxd⟩ (hxv | hx1)
      · exact Set.disjoint_left.mp huv hxu hxv
      · have hxsp : x ∈ Metric.sphere (0 : ℂ) 1 := by
          rw [Metric.mem_sphere, dist_eq_norm]
          exact le_antisymm (by simpa using hxd) (by simpa using mem_bigUnit.mp hx1)
        exact Set.disjoint_left.mp huv hxu (hV hxsp)
    have hcovA : A ⊆ (u ∩ Metric.closedBall (0 : ℂ) 1) ∪ (v ∪ bigUnit) := by
      intro x hx
      by_cases hd : x ∈ Metric.closedBall (0 : ℂ) 1
      · rcases hcover ⟨hx, hd⟩ with h | h
        · exact Or.inl ⟨h, hd⟩
        · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr (mem_bigUnit.mpr ?_))
        rw [Metric.mem_closedBall, dist_zero_right] at hd
        exact le_of_lt (not_le.mp hd)
    rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hAcl).mp hApre _ _ hcl1 hcl2
        hcovA hdisj with h | h
    · exact absurd (h h2A).2 two_notMem_closedBall
    · refine Or.inr fun x hx => ?_
      rcases h hx.1 with h' | h'
      · exact h'
      · exact hV (by
          rw [Metric.mem_sphere, dist_eq_norm]
          exact le_antisymm (by simpa using hx.2) (by simpa using mem_bigUnit.mp h'))

end


/-! ## The annulus region of a curve in the open unit disc -/

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The trace of a curve in the open unit disc lies in the closed unit disc. -/
theorem trace_subset_closedBall {γ : Work.Smooth.Jordan.PlaneCurve}
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    γ.trace ⊆ Metric.closedBall (0 : ℂ) 1 := by
  rintro z ⟨θ, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hball θ).le

/-- The bounded side of a curve in the open unit disc lies in the open unit disc. -/
theorem V_subset_ball (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : S.V ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  have hbdd : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      planeSeparation_V_subset_closedBall S.toPlaneSeparation hball z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  rw [not_lt] at hcon
  have hnorm : ‖z‖ = 1 := le_antisymm hbdd hcon
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp S.toPlaneSeparation.isOpen_V z hz
  set w : ℂ := ((1 + ε / 2 : ℝ)) • z with hw
  have hwball : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w - z = ((ε / 2 : ℝ)) • z := by
      rw [hw, add_smul, one_smul, add_sub_cancel_left]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε / 2), hnorm,
      mul_one]
    linarith
  have hwV : w ∈ S.V := hε hwball
  have hwbdd : ‖w‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      planeSeparation_V_subset_closedBall S.toPlaneSeparation hball w hwV
  have hwnorm : ‖w‖ = 1 + ε / 2 := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 + ε / 2), hnorm,
      mul_one]
  rw [hwnorm] at hwbdd
  linarith

/-- The boundary circle lies in the unbounded side of a curve in the open unit disc. -/
theorem sphere_subset_unboundedSide (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Metric.sphere (0 : ℂ) 1 ⊆ S.U := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hx
  have hxnotV : x ∉ S.V := by
    intro hxV
    have := V_subset_ball S hball hxV
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith
  have hxnotT : x ∉ γ.trace := by
    rintro ⟨θ, hθ⟩
    have h := hball θ
    rw [hθ] at h
    linarith
  have : x ∈ S.U ∪ S.V := by
    rw [S.toPlaneSeparation.union_eq]; exact hxnotT
  exact this.resolve_right hxnotV

/-- The complement of the open unit disc lies in the closure of the unbounded side. -/
theorem bigUnit_subset_closure_U (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : bigUnit ⊆ closure S.U := by
  intro z hz
  rcases lt_or_eq_of_le (mem_bigUnit.mp hz) with hlt | heq
  · -- the exterior: a ray from `z` to infinity avoids the trace
    refine subset_closure ?_
    have hnotT : z ∉ γ.trace := by
      rintro ⟨θ, hθ⟩
      have h := hball θ
      rw [hθ] at h
      linarith
    have hnotV : z ∉ S.V := by
      intro hV
      have := V_subset_ball S hball hV
      rw [Metric.mem_ball, dist_zero_right] at this
      linarith
    have : z ∈ S.U ∪ S.V := by
      rw [S.toPlaneSeparation.union_eq]; exact hnotT
    exact this.resolve_right hnotV
  · refine subset_closure ?_
    exact sphere_subset_unboundedSide S hball (by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact heq.symm)

/-- **The trace lies in the closure of the unbounded side.**  Indeed `S.U = (closure S.V)ᶜ` (the
sides are separated by the closed disc `closure S.V`), and every point of the trace is a boundary
point of `closure S.V`: it lies in `closure S.V` (the trace is inside the image of `S.e`) but not
in its interior, which is `S.V` by `interior_closure_V_eq`. -/
theorem trace_subset_closure_U (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    γ.trace ⊆ closure S.U := by
  have hU : S.U = (closure S.V)ᶜ := by
    ext z
    constructor
    · intro hzU hzcl
      obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp hzcl S.U
        S.toPlaneSeparation.isOpen_U hzU
      exact Set.disjoint_left.mp S.toPlaneSeparation.disjoint_UV hyU hyV
    · intro hzcl
      have hzV : z ∉ S.V := fun hV => hzcl (subset_closure hV)
      have hzT : z ∉ γ.trace := by
        rintro ⟨θ, hθ⟩
        exact hzcl (by
          rw [← S.range_e]
          exact ⟨circlePoint θ, (S.boundary θ).trans hθ⟩)
      have hall : z ∈ S.U ∪ S.V := by
        rw [S.toPlaneSeparation.union_eq]; exact hzT
      exact hall.resolve_right hzV
  intro x hx
  have hxV : x ∉ S.V := by
    intro hV
    have : x ∈ S.U ∪ S.V := Or.inr hV
    rw [S.toPlaneSeparation.union_eq] at this
    exact this hx
  rw [hU]
  refine mem_closure_iff.mpr ?_
  intro t htopen hxt
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have ht : t ⊆ closure S.V := by
    intro y hyt
    by_contra hy
    have hmem : y ∈ t ∩ (closure S.V)ᶜ := ⟨hyt, hy⟩
    rw [hcon] at hmem
    exact hmem
  have hint : x ∈ interior (closure S.V) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (htopen.mem_nhds hxt) ht)
  rw [interior_closure_V_eq S] at hint
  exact hxV hint

/-- **The annulus region of a curve in the open unit disc is preconnected.** -/
theorem isPreconnected_annulusRegion (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    IsPreconnected (annulusRegion S) := by
  have htrace : γ.trace ⊆ closure S.U := trace_subset_closure_U S
  have heq : annulusRegion S = closure S.U ∩ Metric.closedBall (0 : ℂ) 1 := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzD, hzV⟩
      have hmem : z ∈ S.U ∪ γ.trace := by
        have hall : z ∈ S.U ∪ S.V ∪ γ.trace := by
          have hun : (S.U ∪ S.V ∪ γ.trace) = Set.univ := by
            rw [S.toPlaneSeparation.union_eq, Set.compl_union_self]
          rw [hun]; trivial
        rcases hall with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact absurd h hzV
        · exact Or.inr h
      refine ⟨?_, hzD⟩
      rcases hmem with h | h
      · exact subset_closure h
      · exact htrace h
    · rintro z ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      intro hV
      have hcl : z ∉ closure S.U := by
        intro hzcl
        obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hzcl S.V
          S.toPlaneSeparation.isOpen_V hV
        exact Set.disjoint_left.mp S.toPlaneSeparation.disjoint_UV hyU hyV
      exact hcl h1
  rw [heq]
  exact isPreconnected_inter_closedBall_of_isClosed isClosed_closure
    S.toPlaneSeparation.preconn_U.closure (bigUnit_subset_closure_U S hball)

end Work.Smooth.SphereJordan
