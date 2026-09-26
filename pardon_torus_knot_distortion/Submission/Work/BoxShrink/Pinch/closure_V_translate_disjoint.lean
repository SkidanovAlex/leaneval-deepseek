import Mathlib
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.Jordan.plane_separation_preconnected_subset
import Submission.Work.Smooth.Jordan.plane_separation_unbounded
import Submission.Work.Smooth.Jordan.plane_separation_component_V
import Submission.Work.Smooth.Jordan.plane_separation_component_U
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

/-!
# The closed bounded side of a simple closed plane curve is disjoint from its translate

For a simple closed plane curve `γ` with a Jordan separation `S` (two open preconnected pieces
`S.U`, `S.V` covering `γ.traceᶜ`, `S.V` bounded), and a nonzero vector `z` such that the trace of
`γ` is disjoint from its translate by `z`, the closed bounded side `closure S.V` is disjoint from
its translate by `z`.

## Route

The frontier of either side of a Jordan separation is the whole trace
(`frontier_V_eq_trace`, `frontier_U_eq_trace`), proved from Maehara's Lemma 1
(`Work.Topology.PlaneCurve.frontier_component_eq_range`) and the identification of the sides with
connected components of the complement.  Hence `closure S.V = S.V ∪ γ.trace` and
`closure (S.V + z) = (S.V + z) ∪ (γ.trace + z)`; it remains to see that the four pairwise
intersections `V ∩ (V+z)`, `V ∩ (c+z)`, `c ∩ (V+z)`, `c ∩ (c+z)` are empty.

The key geometric input is `inside_subset_of_trace_subset`: for two disjoint simple closed curves
with Jordan separations, if the trace of one is contained in the bounded side of the other, then
the bounded side of the first is contained in the bounded side of the second.  Applied to the
curve and its translate (both ways), it shows that neither trace can lie in the other's bounded
side — that would force `S.V ⊆ S.V + z` or `S.V + z ⊆ S.V`, and hence (by iterating the
translation) an unbounded `S.V`.  So each trace lies in the other's *unbounded* side, and the four
intersections are then immediate from the partition of the plane.
-/

open Set
open Classical

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## Frontier and closure of the two sides -/

/-- The complement of the trace of a simple closed curve with a Jordan separation is not
preconnected: it is the union of the two disjoint non-empty open pieces `S.U`, `S.V`. -/
theorem not_isPreconnected_compl_trace {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : ¬ IsPreconnected c.traceᶜ := by
  intro h
  rcases h.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
      (by rw [S.union_eq]) with hU | hV
  · obtain ⟨v, hv⟩ := S.nonempty_V
    exact Set.disjoint_left.mp S.disjoint_UV
      (hU (by rw [← S.union_eq]; exact Or.inr hv)) hv
  · obtain ⟨u, hu⟩ := S.nonempty_U
    exact Set.disjoint_left.mp S.disjoint_UV hu
      (hV (by rw [← S.union_eq]; exact Or.inl hu))

/-- **The frontier of the bounded side of a Jordan separation is the trace of the curve.** -/
theorem frontier_V_eq_trace {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : frontier S.V = c.trace := by
  obtain ⟨x, hxV⟩ := S.nonempty_V
  have hxt : x ∉ c.trace := by
    intro h
    have : x ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr hxV
    exact this h
  have h := Work.Topology.PlaneCurve.frontier_component_eq_range c.cont c.periodic S.simple
    (not_isPreconnected_compl_trace S) x hxt
  have h2 : connectedComponentIn (Set.range c.γ)ᶜ x = S.V :=
    Work.Smooth.Jordan.plane_separation_component_V S hxV
  rw [h2] at h
  exact h

/-- **The frontier of the unbounded side of a Jordan separation is the trace of the curve.** -/
theorem frontier_U_eq_trace {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : frontier S.U = c.trace := by
  obtain ⟨x, hxU⟩ := S.nonempty_U
  have hxt : x ∉ c.trace := by
    intro h
    have : x ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inl hxU
    exact this h
  have h := Work.Topology.PlaneCurve.frontier_component_eq_range c.cont c.periodic S.simple
    (not_isPreconnected_compl_trace S) x hxt
  have h2 : connectedComponentIn (Set.range c.γ)ᶜ x = S.U :=
    Work.Smooth.Jordan.plane_separation_component_U S hxU
  rw [h2] at h
  exact h

/-- **The closure of the bounded side is the bounded side together with the curve.** -/
theorem closure_V_eq {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : closure S.V = S.V ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_V_eq_trace S]

/-- **The closure of the unbounded side is the unbounded side together with the curve.** -/
theorem closure_U_eq {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : closure S.U = S.U ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_U_eq_trace S]

/-! ## The translate of a curve and of its separation -/

/-- The **translate** of a plane curve by a vector `z`. -/
def translateCurve (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := fun t => c.γ t + z
  cont := c.cont.add continuous_const
  periodic := fun t => by
    show c.γ (t + 2 * Real.pi) + z = c.γ t + z
    rw [c.periodic t]

@[simp] theorem translateCurve_apply (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) (t : ℝ) :
    (translateCurve c z).γ t = c.γ t + z := rfl

/-- The trace of a translate is the translate of the trace. -/
theorem translateCurve_trace (c : Work.Smooth.Jordan.PlaneCurve) (z : ℂ) :
    (translateCurve c z).trace = (fun w : ℂ => w + z) '' c.trace := by
  show Set.range (fun t => c.γ t + z) = (fun w : ℂ => w + z) '' Set.range c.γ
  rw [← Set.range_comp]
  rfl

/-- The **translate** of a Jordan separation: the same datum pushed forward by `w ↦ w + z`. -/
def translateSeparation {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) (z : ℂ) :
    Work.Smooth.Jordan.PlaneSeparation (translateCurve c z) where
  simple := by
    intro a ha b hb hab
    exact S.simple ha hb (add_right_cancel hab)
  U := (fun w : ℂ => w + z) '' S.U
  V := (fun w : ℂ => w + z) '' S.V
  isOpen_U := (Homeomorph.addRight z).isOpenMap S.U S.isOpen_U
  isOpen_V := (Homeomorph.addRight z).isOpenMap S.V S.isOpen_V
  preconn_U := S.preconn_U.image _ (continuous_add_const z).continuousOn
  preconn_V := S.preconn_V.image _ (continuous_add_const z).continuousOn
  nonempty_U := S.nonempty_U.image _
  nonempty_V := S.nonempty_V.image _
  disjoint_UV := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := add_right_cancel (hax.trans hbx.symm)
    exact Set.disjoint_left.mp S.disjoint_UV ha (hab ▸ hb)
  union_eq := by
    have hbij : Function.Bijective (fun w : ℂ => w + z) :=
      ⟨fun a b h => add_right_cancel h, fun b => ⟨b - z, by ring⟩⟩
    rw [← Set.image_union, S.union_eq, Set.image_compl_eq hbij, ← translateCurve_trace]
  bounded_V := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp S.bounded_V
    rw [Metric.isBounded_iff]
    refine ⟨C, ?_⟩
    rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hbx⟩
    rw [← hax, ← hbx, dist_eq_norm, show a + z - (b + z) = a - b by ring, ← dist_eq_norm]
    exact hC ha hb

/-- A set whose translates have points of arbitrarily large norm is unbounded; the translate of an
unbounded set is unbounded. -/
theorem unbounded_image_add (A : Set ℂ) (z : ℂ)
    (h : ∀ R : ℝ, ∃ x ∈ A, R ≤ ‖x‖) :
    ∀ R : ℝ, ∃ x ∈ (fun w : ℂ => w + z) '' A, R ≤ ‖x‖ := by
  intro R
  obtain ⟨x, hx, hRx⟩ := h (R + ‖z‖)
  refine ⟨x + z, ⟨x, hx, rfl⟩, ?_⟩
  have h1 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by
    have h2 := norm_add_le (x + z) (-z)
    rw [add_neg_cancel_right] at h2
    simpa using h2
  linarith

/-! ## The key geometric input -/

/-- **A curve inside a Jordan domain has its own Jordan domain inside.**  If two simple closed
curves have disjoint traces and the trace of `σ` lies in the bounded side `Sρ.V` of a Jordan
separation of `ρ`, then the bounded side `Sσ.V` of `σ` lies in `Sρ.V` as well. -/
theorem inside_subset_of_trace_subset {ρ σ : Work.Smooth.Jordan.PlaneCurve}
    (Sρ : Work.Smooth.Jordan.PlaneSeparation ρ) (Sσ : Work.Smooth.Jordan.PlaneSeparation σ)
    (hdisj : Disjoint ρ.trace σ.trace) (hsub : σ.trace ⊆ Sρ.V) :
    Sσ.V ⊆ Sρ.V := by
  classical
  have hρpre : IsPreconnected ρ.trace := isPreconnected_range ρ.cont
  have hσpre : IsPreconnected σ.trace := isPreconnected_range σ.cont
  -- `Sρ.U ⊆ Sσ.U`
  have hUρUσ : Sρ.U ⊆ Sσ.U := by
    have hsub1 : Sρ.U ⊆ Sσ.U ∪ Sσ.V := by
      intro x hx
      have hxσ : x ∉ σ.trace := fun h => Set.disjoint_left.mp Sρ.disjoint_UV hx (hsub h)
      rw [Sσ.union_eq]
      exact hxσ
    rcases Sρ.preconn_U.subset_or_subset Sσ.isOpen_U Sσ.isOpen_V Sσ.disjoint_UV hsub1 with h | h
    · exact h
    · exfalso
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp Sσ.bounded_V
      obtain ⟨y, hy⟩ := Sσ.nonempty_V
      obtain ⟨x, hxU, hxR⟩ := Work.Smooth.Jordan.plane_separation_unbounded Sρ (C + ‖y‖ + 1)
      have hxV : x ∈ Sσ.V := h hxU
      have h1 : dist x y ≤ C := hC hxV hy
      rw [dist_eq_norm] at h1
      have h2 : ‖x‖ ≤ C + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by ring_nf
          _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ C + ‖y‖ := by linarith
      linarith
  -- `ρ.trace` lies in one of the two sides of `σ`
  have hρsplit : ρ.trace ⊆ Sσ.U ∨ ρ.trace ⊆ Sσ.V :=
    hρpre.subset_or_subset Sσ.isOpen_U Sσ.isOpen_V Sσ.disjoint_UV
      (by intro x hx; rw [Sσ.union_eq]; exact Set.disjoint_left.mp hdisj hx)
  rcases hρsplit with hA | hB
  · -- the easy case: `ρ.trace ⊆ Sσ.U`; then `Sσ.V ⊆ Sρ.V`
    intro x hx
    have hxρ : x ∉ ρ.trace := fun hh => Set.disjoint_left.mp Sσ.disjoint_UV (hA hh) hx
    have hxUρ : x ∉ Sρ.U := fun hh => Set.disjoint_left.mp Sσ.disjoint_UV (hUρUσ hh) hx
    have hxmem : x ∈ ρ.traceᶜ := hxρ
    rw [← Sρ.union_eq] at hxmem
    exact hxmem.resolve_left hxUρ
  · -- the hard case: `ρ.trace ⊆ Sσ.V`; then also `Sσ.U ⊆ Sρ.U`, and the two frontiers meet
    exfalso
    have hUσUρ : Sσ.U ⊆ Sρ.U := by
      have hsub2 : Sσ.U ⊆ Sρ.U ∪ Sρ.V := by
        intro x hx
        have hxρ : x ∉ ρ.trace := fun hh => Set.disjoint_left.mp Sσ.disjoint_UV hx (hB hh)
        rw [Sρ.union_eq]
        exact hxρ
      rcases Sσ.preconn_U.subset_or_subset Sρ.isOpen_U Sρ.isOpen_V Sρ.disjoint_UV hsub2 with h | h
      · exact h
      · exfalso
        obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp Sρ.bounded_V
        obtain ⟨y, hy⟩ := Sρ.nonempty_V
        obtain ⟨x, hxU, hxR⟩ := Work.Smooth.Jordan.plane_separation_unbounded Sσ (C + ‖y‖ + 1)
        have hxV : x ∈ Sρ.V := h hxU
        have h1 : dist x y ≤ C := hC hxV hy
        rw [dist_eq_norm] at h1
        have h2 : ‖x‖ ≤ C + ‖y‖ := by
          calc ‖x‖ = ‖(x - y) + y‖ := by ring_nf
            _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
            _ ≤ C + ‖y‖ := by linarith
        linarith
    have hUeq : Sσ.U = Sρ.U := Subset.antisymm hUσUρ hUρUσ
    -- `Sσ.V = σ.traceᶜ \ Sρ.U`
    have hVeq : Sσ.V = σ.traceᶜ \ Sρ.U := by
      ext x; constructor
      · intro hx
        refine ⟨by rw [← Sσ.union_eq]; exact Or.inr hx, ?_⟩
        intro hxU
        exact Set.disjoint_left.mp Sσ.disjoint_UV (by rw [hUeq]; exact hxU) hx
      · rintro ⟨hxσc, hxU⟩
        rw [← Sσ.union_eq] at hxσc
        exact hxσc.resolve_left (fun hxUσ => hxU (hUeq ▸ hxUσ))
    -- `closure Sσ.V = Sρ.Uᶜ`
    have hclosure : closure Sσ.V = Sρ.Uᶜ := by
      apply Subset.antisymm
      · calc closure Sσ.V = closure (σ.traceᶜ \ Sρ.U) := by rw [hVeq]
          _ ⊆ closure (Sρ.Uᶜ) := closure_mono (fun x hx => hx.2)
          _ = Sρ.Uᶜ := Sρ.isOpen_U.isClosed_compl.closure_eq
      · rw [closure_V_eq Sσ]
        intro x hx
        by_cases hxσ : x ∈ σ.trace
        · exact Or.inr hxσ
        · exact Or.inl (by rw [hVeq]; exact ⟨hxσ, hx⟩)
    -- `ρ.trace ⊆ closure Sσ.V ∩ closure (Sσ.V)ᶜ = frontier Sσ.V = σ.trace`
    have hρcl : ρ.trace ⊆ closure Sσ.V := by
      rw [hclosure, ← frontier_U_eq_trace Sρ, Sρ.isOpen_U.frontier_eq]
      intro x hx
      exact hx.2
    have hρcl2 : ρ.trace ⊆ closure ((Sσ.V)ᶜ) := by
      have h1 : ρ.trace ⊆ closure Sρ.U := by
        rw [← frontier_U_eq_trace Sρ, Sρ.isOpen_U.frontier_eq]
        intro x hx
        exact hx.1
      refine h1.trans (closure_mono ?_)
      intro x hx hxV
      rw [hVeq] at hxV
      exact hxV.2 hx
    have hsubρσ : ρ.trace ⊆ σ.trace := by
      calc ρ.trace ⊆ closure Sσ.V ∩ closure ((Sσ.V)ᶜ) := fun x hx => ⟨hρcl hx, hρcl2 hx⟩
        _ = frontier Sσ.V := (frontier_eq_closure_inter_closure (s := Sσ.V)).symm
        _ = σ.trace := frontier_V_eq_trace Sσ
    obtain ⟨x0, hx0⟩ : ρ.trace.Nonempty := ⟨ρ.γ 0, Set.mem_range_self 0⟩
    exact Set.disjoint_left.mp hdisj hx0 (hsubρσ hx0)

/-! ## The main theorem -/

theorem closure_V_translate_disjoint {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {z : ℂ} (hz : z ≠ 0)
    (hdisj : Disjoint (Set.range γ.γ) ((fun w : ℂ => w + z) '' Set.range γ.γ)) :
    Disjoint (closure S.V) ((fun w : ℂ => w + z) '' closure S.V) := by
  classical
  set γz := translateCurve γ z with hγz
  have htrace : γz.trace = (fun w : ℂ => w + z) '' γ.trace := translateCurve_trace γ z
  have hdisj' : Disjoint γ.trace γz.trace := by rw [htrace]; exact hdisj
  have hdisj'' : Disjoint γz.trace γ.trace := hdisj'.symm
  set S' := translateSeparation S z with hS'
  have hV' : S'.V = (fun w : ℂ => w + z) '' S.V := rfl
  have hσpre : IsPreconnected γz.trace := isPreconnected_range γz.cont
  have hρpre : IsPreconnected γ.trace := isPreconnected_range γ.cont
  -- `S'.V ⊄ S.V`, since `S.V` is bounded and translation by `z ≠ 0` is unbounded
  have hnotV'V : ¬ S'.V ⊆ S.V := by
    intro hcont
    obtain ⟨x, hxV⟩ := S.nonempty_V
    have hstep : ∀ n : ℕ, x + (n : ℂ) * z ∈ S.V := by
      intro n
      induction n with
      | zero => simpa using hxV
      | succ m ih =>
        have hmem' : x + (m : ℂ) * z + z ∈ S'.V := ⟨x + (m : ℂ) * z, ih, rfl⟩
        have hmem := hcont hmem'
        rw [Nat.cast_succ, show x + ((m : ℂ) + 1) * z = x + (m : ℂ) * z + z by ring]
        exact hmem
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp S.bounded_V
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖z‖)
    have h1 : dist x (x + (n : ℂ) * z) ≤ C := hC hxV (hstep n)
    rw [dist_eq_norm, show x - (x + (n : ℂ) * z) = -((n : ℂ) * z) by ring, norm_neg, norm_mul,
      Complex.norm_natCast] at h1
    have h2 : C < (n : ℝ) * ‖z‖ := (div_lt_iff₀ hzpos).mp hn
    linarith
  -- `S.V ⊄ S'.V`, symmetrically
  have hnotVV' : ¬ S.V ⊆ S'.V := by
    intro hcont
    obtain ⟨x, hxV⟩ := S.nonempty_V
    have hstep : ∀ n : ℕ, x - (n : ℂ) * z ∈ S.V := by
      intro n
      induction n with
      | zero => simpa using hxV
      | succ m ih =>
        obtain ⟨a, ha, hay⟩ := hcont ih
        have hrepr : x - (↑m + 1) * z = a := by
          have h2 : a = x - (m : ℂ) * z - z := by
            rw [eq_sub_iff_add_eq]
            exact hay
          rw [h2]; ring
        rw [Nat.cast_succ, hrepr]
        exact ha
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp S.bounded_V
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖z‖)
    have h1 : dist x (x - (n : ℂ) * z) ≤ C := hC hxV (hstep n)
    rw [dist_eq_norm, show x - (x - (n : ℂ) * z) = (n : ℂ) * z by ring, norm_mul,
      Complex.norm_natCast] at h1
    have h2 : C < (n : ℝ) * ‖z‖ := (div_lt_iff₀ hzpos).mp hn
    linarith
  -- neither trace lies in the other's bounded side
  have hσV : ¬ γz.trace ⊆ S.V := fun h => hnotV'V (inside_subset_of_trace_subset S S' hdisj' h)
  have hρV : ¬ γ.trace ⊆ S'.V := fun h => hnotVV' (inside_subset_of_trace_subset S' S hdisj'' h)
  -- so each trace lies in the other's unbounded side
  have hc'SU : γz.trace ⊆ S.U := by
    rcases hσpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
      (by intro x hx; rw [S.union_eq]; exact Set.disjoint_left.mp hdisj'.symm hx) with h | h
    · exact h
    · exact absurd h hσV
  have hcS'U : γ.trace ⊆ S'.U := by
    rcases hρpre.subset_or_subset S'.isOpen_U S'.isOpen_V S'.disjoint_UV
      (by intro x hx; rw [S'.union_eq]; exact Set.disjoint_left.mp hdisj' hx) with h | h
    · exact h
    · exact absurd h hρV
  -- hence the translate of the bounded side is in the unbounded side
  have hV'SU : S'.V ⊆ S.U := by
    rcases S'.preconn_V.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
      (by intro x hx; rw [S.union_eq]
          exact fun hc => Set.disjoint_left.mp S'.disjoint_UV (hcS'U hc) hx) with h | h
    · exact h
    · exact absurd h hnotV'V
  -- conclude
  have hRHS : (fun w : ℂ => w + z) '' closure S.V = closure S'.V := by
    rw [closure_V_eq S, Set.image_union, ← hV', ← htrace, ← closure_V_eq S']
  rw [hRHS, closure_V_eq S, closure_V_eq S', Set.disjoint_left]
  rintro x (hxV | hxc) (hxV' | hxc')
  · exact Set.disjoint_left.mp S.disjoint_UV (hV'SU hxV') hxV
  · exact Set.disjoint_left.mp S.disjoint_UV (hc'SU hxc') hxV
  · exact Set.disjoint_left.mp S'.disjoint_UV (hcS'U hxc) hxV'
  · exact Set.disjoint_left.mp hdisj' hxc hxc'

end

end Work.BoxShrink.Pinch
