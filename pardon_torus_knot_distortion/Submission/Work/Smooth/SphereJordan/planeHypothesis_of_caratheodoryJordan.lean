import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.SphereJordan.planeDomain_homeo_unitBall
import Submission.Work.Smooth.JordanSeparation.alexander_cone_extension
import Submission.Work.Smooth.JordanSeparation.isSimplyConnected_of_isPreconnected_compl
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo

/-!
# Carathéodory's theorem implies the planar Jordan–Schoenflies theorem

The hypothesis `H` of the target statement is Carathéodory's boundary-correspondence theorem for
Jordan domains in the (weak) form "the closure of a Jordan domain is homeomorphic to the closed
unit disc".  This file derives from it the chapter's classical input
`Work.Smooth.SphereJordan.PlaneHypothesis`: for every simple closed plane curve `c` there is an
embedded disc spanning `c` (in the given parametrisation) whose image is the closure of the bounded
side.

The content beyond `H` is the *boundary correspondence*: `H` supplies a homeomorphism
`Ψ : closure V ≃ₜ 𝔻` of the closure of the bounded side `V` of `c`, but says nothing about which
point of the frontier goes to which point of the circle.  Two ingredients recover it:

* **`image_trace_eq_sphere`**: `Ψ` carries the frontier `trace = range c.γ` onto the unit circle.
  This is a genuine point-set fact — a homeomorphism of a Jordan domain closure preserves its
  frontier.  The proof is self-contained: if `A := Ψ '' trace` missed the circle, then
  `𝔻 ∖ A = Ψ '' V` would have to be disconnected while `V` is preconnected (refuted with the
  unconditional Jordan separation theorem `exists_jsep` and the winding number
  `windNumber_eq_zero_of_norm_gt`), and if `A` met the interior of the disc then the unbounded side
  of the (simple closed) image curve `A` — an open set containing everything outside the closed
  disc — and the bounded side of `A` would disconnect the open ball;
* the **Alexander trick** (`discHomeo`): the homeomorphism of the circle `exp (iθ) ↦ Ψ (c γ θ)`
  (well defined precisely because of the first point) extends to a homeomorphism `Φ` of `𝔻`, and
  `Ψ⁻¹ ∘ Φ` is the required spanning disc.

## Main results

* `Work.Smooth.SphereJordan.simplyConnectedSpace_boundedSide` — the bounded side of a Jordan
  separation datum is simply connected;
* `Work.Smooth.SphereJordan.image_trace_eq_sphere` — a homeomorphism of a Jordan domain closure
  carries the frontier curve onto the unit circle;
* `Work.Smooth.SphereJordan.exists_circleHomeo_of_periodic` — a continuous `2π`-periodic map
  `ℝ → S¹` that is injective on one period and surjective induces a homeomorphism of the circle
  with the prescribed boundary values;
* `Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan` — the target.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The period `2π` is positive, as a `Fact`, so that the `AddCircle` API applies. -/
instance fact_two_pi_pos' : Fact (0 < 2 * (Real.pi : ℝ)) := ⟨by positivity⟩

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The trace of a closed plane curve lies in the closure of the bounded side of any Jordan
separation datum for it. -/
theorem carathTrace_subset_closure_V (S : JSep γ) : γ.trace ⊆ closure S.V := by
  intro x hx
  rw [closure_eq_self_union_frontier, S.frontier_V]
  exact Or.inr hx

/-- **The bounded side of a Jordan separation datum is simply connected.**

Its complement `Vᶜ = U ∪ trace = closure U` is preconnected, so `V` is a complementary domain of
the continuum `closure U` in the plane; the classical statement is proved on the Riemann sphere
(`Work.Smooth.JordanSeparation.isSimplyConnected_of_isPreconnected_compl`), to which `ℂ` transfers
along the open embedding `ℂ ↪ ℂ ∪ {∞}` — the point `∞` lies in the closure of the (unbounded)
complement of the bounded side. -/
theorem simplyConnectedSpace_boundedSide (S : JSep γ) : SimplyConnectedSpace ↥S.V := by
  classical
  -- the complement of the bounded side is the closure of the unbounded side
  have hcompl : S.Vᶜ = closure S.U := by
    have h1 : S.Vᶜ = S.U ∪ γ.trace := by
      ext x
      constructor
      · intro hx
        by_cases hxt : x ∈ γ.trace
        · exact Or.inr hxt
        · refine Or.inl ?_
          have h2 : x ∈ γ.traceᶜ := hxt
          rw [← S.union_eq] at h2
          rcases h2 with h | h
          · exact h
          · exact absurd h hx
      · rintro (hx | hx)
        · intro hV
          exact (Set.disjoint_left.mp S.disjoint_UV hx) hV
        · intro hV
          have h2 : x ∈ γ.traceᶜ := by rw [← S.union_eq]; exact Or.inr hV
          exact h2 hx
    rw [h1, ← S.frontier_U, closure_eq_self_union_frontier]
  -- the complement of the bounded side is unbounded
  have hunb : ∀ R : ℝ, ∃ x ∈ S.Vᶜ, R ≤ ‖x‖ := by
    intro R
    obtain ⟨C, hC⟩ := S.bounded_V.subset_closedBall (0 : ℂ)
    have hpos : (0 : ℝ) < max R (max C 0) + 1 := by
      linarith [le_max_right R (max C 0), le_max_right C 0]
    refine ⟨(((max R (max C 0) + 1 : ℝ)) : ℂ), ?_, ?_⟩
    · intro hmem
      have h1 := hC hmem
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpos] at h1
      linarith [le_max_right R (max C 0), le_max_left C 0]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      linarith [le_max_left R (max C 0)]
  -- `∞` lies in the closure of the image of the complement
  have hinfty : (OnePoint.infty : OnePoint ℂ) ∈
      closure ((fun z : ℂ => (z : OnePoint ℂ)) '' S.Vᶜ) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨K, ⟨-, hKcomp⟩, hKV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
    obtain ⟨R, hR⟩ := hKcomp.isBounded.exists_norm_le
    obtain ⟨x, hx, hxR⟩ := hunb (R + 1)
    refine ⟨(x : OnePoint ℂ), hKV (Or.inl ⟨x, ?_, rfl⟩), ⟨x, hx, rfl⟩⟩
    intro hxK
    have h1 := hR x hxK
    linarith
  -- the complement of the image on the sphere is preconnected
  have hDpre : IsPreconnected ((fun z : ℂ => (z : OnePoint ℂ)) '' S.V) :=
    S.preconn_V.image _ OnePoint.continuous_coe.continuousOn
  have hDpre_c : IsPreconnected ((fun z : ℂ => (z : OnePoint ℂ)) '' S.V)ᶜ := by
    rw [OnePoint.compl_image_coe]
    exact IsPreconnected.subset_closure
      (by
        rw [hcompl]
        exact (S.preconn_U.closure).image _ OnePoint.continuous_coe.continuousOn)
      Set.subset_union_left
      (fun x hx => by
        rcases hx with hx | hx
        · exact subset_closure hx
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hinfty)
  -- transfer the sphere statement back along the open embedding
  have hsc : IsSimplyConnected ((fun z : ℂ => (z : OnePoint ℂ)) '' S.V : Set (OnePoint ℂ)) :=
    Work.Smooth.JordanSeparation.isSimplyConnected_of_isPreconnected_compl
      (OnePoint.isOpen_image_coe.mpr S.isOpen_V) (S.nonempty_V.image _) hDpre hDpre_c
  exact (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image (s := S.V)).mp hsc

/-- **A homeomorphism of a Jordan domain closure preserves its frontier.**
For the bounded side `S.V` of a simple closed plane curve `γ` and a homeomorphism
`Ψ : closure S.V ≃ₜ 𝔻`, the image of the trace `range γ` under `Ψ` is exactly the unit circle. -/
theorem image_trace_eq_sphere (hγ : γ.IsSimple) (S : JSep γ)
    (Ψ : closure S.V ≃ₜ Metric.closedBall (0 : ℂ) 1) :
    Set.range (fun θ : ℝ => ((Ψ ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ :
      Metric.closedBall (0 : ℂ) 1) : ℂ)) = Metric.sphere (0 : ℂ) 1 := by
  classical
  set δ : ℝ → ℂ := fun θ =>
    ((Ψ ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ :
      Metric.closedBall (0 : ℂ) 1) : ℂ) with hδdef
  have hδcont : Continuous δ := by
    rw [hδdef]
    exact continuous_subtype_val.comp (Ψ.continuous.comp (γ.cont.subtype_mk _))
  have hδper : Function.Periodic δ (2 * Real.pi) := by
    intro θ
    have hpt : (⟨γ (θ + 2 * Real.pi),
          carathTrace_subset_closure_V S (γ.mem_trace (θ + 2 * Real.pi))⟩ : ↥(closure S.V)) =
        ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ := Subtype.ext (γ.periodic θ)
    simp only [hδdef]
    rw [hpt]
  have hδinj : Set.InjOn δ (Set.Ico 0 (2 * Real.pi)) := by
    intro θ hθ θ' hθ' h
    apply hγ hθ hθ'
    simp only [hδdef] at h
    have h' : (⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ : ↥(closure S.V)) =
        ⟨γ θ', carathTrace_subset_closure_V S (γ.mem_trace θ')⟩ := Ψ.injective (Subtype.ext h)
    exact congrArg (fun w : ↥(closure S.V) => (w : ℂ)) h'
  -- the image curve, and its unconditional Jordan separation
  set cδ : Work.Smooth.Jordan.PlaneCurve := ⟨δ, hδcont, hδper⟩ with hcδ
  have hδsimp : cδ.IsSimple := hδinj
  obtain ⟨T⟩ := exists_jsep cδ hδsimp
  have htrace : cδ.trace = Set.range δ := rfl
  have hA_sub : Set.range δ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rintro u ⟨θ, rfl⟩
    exact (Ψ ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ : Metric.closedBall (0 : ℂ) 1).2
  -- points far from the origin lie in the unbounded side of the image curve
  have hfar : ∀ z : ℂ, 1 < ‖z‖ → z ∈ T.U := by
    intro z hz
    have hnotA : z ∉ Set.range δ := by
      rintro ⟨θ, hθ⟩
      have h := hA_sub ⟨θ, rfl⟩
      rw [hθ] at h
      rw [Metric.mem_closedBall, dist_zero_right] at h
      linarith
    have hz' : z ∉ cδ.trace := by rw [htrace]; exact hnotA
    rw [← (T.wind_zero_iff_U z hz')]
    refine windNumber_eq_zero_of_norm_gt hδcont hδper (fun t => ?_) hz
    have h := hA_sub ⟨t, rfl⟩
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  -- the bounded side of the image curve lies in the closed disc
  have hTV_closedBall : T.V ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push_neg at h
    exact (Set.disjoint_left.mp T.disjoint_UV (hfar z h)) hz
  -- the image of the bounded side of `γ` under `Ψ` is the complement of the image curve
  set g : ↥S.V → ℂ := fun v =>
    ((Ψ ⟨(v : ℂ), subset_closure v.2⟩ : Metric.closedBall (0 : ℂ) 1) : ℂ) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    exact continuous_subtype_val.comp (Ψ.continuous.comp
      (continuous_subtype_val.subtype_mk (fun v => subset_closure v.2)))
  haveI hPCSV : PreconnectedSpace ↥S.V := isPreconnected_iff_preconnectedSpace.mp S.preconn_V
  have hrange_g : Set.range g = Metric.closedBall (0 : ℂ) 1 \ Set.range δ := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨(Ψ ⟨(v : ℂ), subset_closure v.2⟩ : Metric.closedBall (0 : ℂ) 1).2, ?_⟩
      rintro ⟨θ, hθ⟩
      have heq : (⟨(v : ℂ), subset_closure v.2⟩ : ↥(closure S.V)) =
          ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ := by
        apply Ψ.injective
        exact Subtype.ext hθ.symm
      have hv : (v : ℂ) = γ θ := congrArg (fun w : ↥(closure S.V) => (w : ℂ)) heq
      have : γ θ ∈ γ.traceᶜ := by
        rw [← S.union_eq]
        exact Or.inr (hv ▸ v.2)
      exact this (γ.mem_trace θ)
    · rintro ⟨huD, huA⟩
      obtain ⟨y, hy⟩ := Ψ.surjective (⟨u, huD⟩ : Metric.closedBall (0 : ℂ) 1)
      have hyV : (y : ℂ) ∈ S.V := by
        by_contra h
        have hcl : closure S.V = S.V ∪ γ.trace := by
          rw [closure_eq_self_union_frontier, S.frontier_V]
        have h1 : (y : ℂ) ∈ S.V ∪ γ.trace := hcl ▸ y.2
        rcases h1 with h1 | h1
        · exact h h1
        · obtain ⟨θ, hθ⟩ := h1
          have hyθ : y = ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ := Subtype.ext hθ.symm
          refine huA ⟨θ, ?_⟩
          show ((Ψ ⟨γ θ, carathTrace_subset_closure_V S (γ.mem_trace θ)⟩ :
            Metric.closedBall (0 : ℂ) 1) : ℂ) = u
          rw [← hyθ]
          exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) hy
      refine ⟨⟨(y : ℂ), hyV⟩, ?_⟩
      show ((Ψ ⟨((⟨(y : ℂ), hyV⟩ : ↥S.V) : ℂ), subset_closure hyV⟩ :
        Metric.closedBall (0 : ℂ) 1) : ℂ) = u
      rw [show (⟨((⟨(y : ℂ), hyV⟩ : ↥S.V) : ℂ), subset_closure hyV⟩ : ↥(closure S.V)) = y from
        Subtype.ext rfl]
      exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) hy
  have hpre : IsPreconnected (Metric.closedBall (0 : ℂ) 1 \ Set.range δ) := by
    rw [← hrange_g]
    exact isPreconnected_range hgcont
  -- the unbounded side of the image curve does not meet the closed disc
  have hTU_disj : T.U ∩ Metric.closedBall (0 : ℂ) 1 = ∅ := by
    by_contra hne
    obtain ⟨z, hzU, hzD⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hTVsubA : T.V ⊆ (Set.range δ)ᶜ := by
      intro w hw hwA
      have : w ∈ cδ.traceᶜ := by rw [← T.union_eq]; exact Or.inr hw
      rw [htrace] at this
      exact this hwA
    have hnotA : z ∉ Set.range δ := by
      intro hzA
      have : z ∈ cδ.traceᶜ := by rw [← T.union_eq]; exact Or.inl hzU
      rw [htrace] at this
      exact this hzA
    have hzB : z ∈ Metric.closedBall (0 : ℂ) 1 \ Set.range δ := ⟨hzD, hnotA⟩
    have hsub : Metric.closedBall (0 : ℂ) 1 \ Set.range δ ⊆ T.U ∪ T.V := by
      intro w hw
      have : w ∈ cδ.traceᶜ := by rw [htrace]; exact hw.2
      rwa [← T.union_eq] at this
    rcases hpre.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV hsub with h | h
    · obtain ⟨w, hw⟩ := T.nonempty_V
      exact (Set.disjoint_left.mp T.disjoint_UV (h ⟨hTV_closedBall hw, hTVsubA hw⟩)) hw
    · exact (Set.disjoint_left.mp T.disjoint_UV hzU) (h hzB)
  -- hence the unbounded side of the image curve is the exterior of the closed disc
  have hTU_eq : T.U = {z : ℂ | 1 < ‖z‖} := by
    refine Set.Subset.antisymm ?_ hfar
    intro z hz
    by_contra h
    have hle : ‖z‖ ≤ 1 := le_of_not_gt (fun hlt => h hlt)
    have hzD : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hle
    have : z ∈ T.U ∩ Metric.closedBall (0 : ℂ) 1 := ⟨hz, hzD⟩
    rw [hTU_disj] at this
    exact this
  have hset : {z : ℂ | 1 < ‖z‖} = (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  have hAfin : Set.range δ = Metric.sphere (0 : ℂ) 1 := by
    rw [← htrace, ← T.frontier_U, hTU_eq, hset, frontier_compl,
      frontier_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  exact hAfin

/-- **A continuous `2π`-periodic map of the circle that is injective on a period and surjective
induces a homeomorphism of the circle with the prescribed boundary values.** -/
theorem exists_circleHomeo_of_periodic {F : ℝ → Metric.sphere (0 : ℂ) 1}
    (hcont : Continuous F) (hper : Function.Periodic F (2 * Real.pi))
    (hinj : Set.InjOn F (Set.Ico 0 (2 * Real.pi))) (hsurj : Function.Surjective F) :
    ∃ ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1,
      ∀ θ : ℝ, ρ (Circle.exp θ) = F θ := by
  classical
  let G : AddCircle (2 * Real.pi) → Metric.sphere (0 : ℂ) 1 := Function.Periodic.lift hper
  have hGval : ∀ θ : ℝ, G (θ : AddCircle (2 * Real.pi)) = F θ :=
    fun θ => Function.Periodic.lift_coe hper θ
  have hGcont : Continuous G := by
    have hcomp : Continuous (G ∘ fun x : ℝ => (x : AddCircle (2 * Real.pi))) := by
      rw [show (G ∘ fun x : ℝ => (x : AddCircle (2 * Real.pi))) = F from
        funext (fun x => hGval x)]
      exact hcont
    exact (continuous_coinduced_dom
      (f := fun x : ℝ => (x : AddCircle (2 * Real.pi))) (g := G)).mpr hcomp
  have hGbij : Function.Bijective G := by
    constructor
    · intro x y hxy
      set s : ℝ := ((AddCircle.equivIco (2 * Real.pi) (0 : ℝ) x :
        Set.Ico (0 : ℝ) (0 + 2 * Real.pi)) : ℝ) with hs
      set t : ℝ := ((AddCircle.equivIco (2 * Real.pi) (0 : ℝ) y :
        Set.Ico (0 : ℝ) (0 + 2 * Real.pi)) : ℝ) with ht
      have hxs : (s : AddCircle (2 * Real.pi)) = x := by
        rw [hs]; exact AddCircle.coe_equivIco
      have hyt : (t : AddCircle (2 * Real.pi)) = y := by
        rw [ht]; exact AddCircle.coe_equivIco
      have hsI : s ∈ Set.Ico 0 (2 * Real.pi) := by
        have := (AddCircle.equivIco (2 * Real.pi) (0 : ℝ) x).2
        simpa only [zero_add] using this
      have htI : t ∈ Set.Ico 0 (2 * Real.pi) := by
        have := (AddCircle.equivIco (2 * Real.pi) (0 : ℝ) y).2
        simpa only [zero_add] using this
      have hst : F s = F t := by
        rw [← hGval s, ← hGval t, hxs, hyt, hxy]
      have := hinj hsI htI hst
      rw [← hxs, ← hyt, this]
    · intro y
      obtain ⟨θ, hθ⟩ := hsurj y
      exact ⟨(θ : AddCircle (2 * Real.pi)), (hGval θ).trans hθ⟩
  let ρ₁ : AddCircle (2 * Real.pi) ≃ₜ Metric.sphere (0 : ℂ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGbij) hGcont
  have hρ₁ : ∀ θ : ℝ, ρ₁ (θ : AddCircle (2 * Real.pi)) = F θ := fun θ => hGval θ
  refine ⟨(AddCircle.homeomorphCircle').symm.trans ρ₁, ?_⟩
  intro θ
  have hsymm : AddCircle.homeomorphCircle'.symm (Circle.exp θ) = (θ : AddCircle (2 * Real.pi)) := by
    rw [← AddCircle.homeomorphCircle'_apply_mk θ]
    exact Homeomorph.symm_apply_apply _ _
  show ρ₁ (AddCircle.homeomorphCircle'.symm (Circle.exp θ)) = F θ
  rw [hsymm]
  exact hρ₁ θ

/-- The Alexander disc homeomorphism, evaluated on a boundary point. -/
theorem discHomeo_coe_of_norm_eq_one (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1)
    {z : Metric.closedBall (0 : ℂ) 1} (hz : ‖(z : ℂ)‖ = 1) :
    ((discHomeo ρ z : Metric.closedBall (0 : ℂ) 1) : ℂ) =
      ((ρ (⟨(z : ℂ), by rw [Metric.mem_sphere, dist_zero_right]; exact hz⟩ :
        Metric.sphere (0 : ℂ) 1) : Metric.sphere (0 : ℂ) 1) : ℂ) := by
  show radialMap ρ (z : ℂ) = _
  rw [radialMap_coe_sphere ρ
    (⟨(z : ℂ), by rw [Metric.mem_sphere, dist_zero_right]; exact hz⟩ : Metric.sphere (0 : ℂ) 1)]

theorem planeHypothesis_of_caratheodoryJordan
    (H : ∀ {Ω : Set ℂ}, IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω → SimplyConnectedSpace Ω →
      ∀ {γ : ℝ → ℂ}, Continuous γ → Function.Periodic γ (2 * Real.pi) →
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) → frontier Ω = Set.range γ →
      Nonempty (closure Ω ≃ₜ Metric.closedBall (0 : ℂ) 1)) :
    Work.Smooth.SphereJordan.PlaneHypothesis := by
  intro c hc
  classical
  obtain ⟨S⟩ := exists_jsep c hc
  haveI : SimplyConnectedSpace ↥S.V := simplyConnectedSpace_boundedSide S
  -- Carathéodory's theorem for the bounded side of `c`
  obtain ⟨Ψ⟩ := H (Ω := S.V) S.isOpen_V S.nonempty_V S.bounded_V ‹SimplyConnectedSpace ↥S.V›
    c.cont c.periodic hc (by rw [S.frontier_V]; rfl)
  -- the boundary correspondence
  have hA := image_trace_eq_sphere hc S Ψ
  set δ : ℝ → ℂ := fun θ =>
    ((Ψ ⟨c.γ θ, carathTrace_subset_closure_V S (c.mem_trace θ)⟩ :
      Metric.closedBall (0 : ℂ) 1) : ℂ) with hδdef
  have hmem : ∀ θ : ℝ, δ θ ∈ Metric.sphere (0 : ℂ) 1 := by
    intro θ
    rw [← hA]
    exact ⟨θ, rfl⟩
  set F : ℝ → Metric.sphere (0 : ℂ) 1 := fun θ => ⟨δ θ, hmem θ⟩ with hFdef
  have hδcont : Continuous δ := by
    rw [hδdef]
    exact continuous_subtype_val.comp (Ψ.continuous.comp (c.cont.subtype_mk _))
  have hδper : Function.Periodic δ (2 * Real.pi) := by
    intro θ
    have hpt : (⟨c.γ (θ + 2 * Real.pi),
          carathTrace_subset_closure_V S (c.mem_trace (θ + 2 * Real.pi))⟩ : ↥(closure S.V)) =
        ⟨c.γ θ, carathTrace_subset_closure_V S (c.mem_trace θ)⟩ := Subtype.ext (c.periodic θ)
    simp only [hδdef]
    rw [hpt]
  have hδinj : Set.InjOn δ (Set.Ico 0 (2 * Real.pi)) := by
    intro θ hθ θ' hθ' h
    apply hc hθ hθ'
    simp only [hδdef] at h
    have h' : (⟨c.γ θ, carathTrace_subset_closure_V S (c.mem_trace θ)⟩ : ↥(closure S.V)) =
        ⟨c.γ θ', carathTrace_subset_closure_V S (c.mem_trace θ')⟩ := Ψ.injective (Subtype.ext h)
    exact congrArg (fun w : ↥(closure S.V) => (w : ℂ)) h'
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Continuous.subtype_mk hδcont hmem
  have hFper : Function.Periodic F (2 * Real.pi) := by
    intro θ
    apply Subtype.ext
    exact hδper θ
  have hFinj : Set.InjOn F (Set.Ico 0 (2 * Real.pi)) := by
    intro θ hθ θ' hθ' h
    exact hδinj hθ hθ' (congrArg (fun x : Metric.sphere (0 : ℂ) 1 => (x : ℂ)) h)
  have hFsurj : Function.Surjective F := by
    intro x
    have hx : (x : ℂ) ∈ Set.range (fun θ : ℝ =>
        ((Ψ ⟨c.γ θ, carathTrace_subset_closure_V S (c.mem_trace θ)⟩ :
          Metric.closedBall (0 : ℂ) 1) : ℂ)) := by
      rw [hA]
      exact x.2
    obtain ⟨θ, hθ⟩ := hx
    exact ⟨θ, Subtype.ext hθ⟩
  obtain ⟨ρ, hρ⟩ := exists_circleHomeo_of_periodic hFcont hFper hFinj hFsurj
  -- the Alexander trick
  have hΦcircle : ∀ θ : ℝ,
      ((discHomeo ρ (circlePoint θ) : Metric.closedBall (0 : ℂ) 1) : ℂ) = δ θ := by
    intro θ
    have hz : ‖((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
      rw [Work.Smooth.Jordan.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I (θ : ℝ)
    rw [discHomeo_coe_of_norm_eq_one ρ hz]
    have hx : (⟨((circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ),
        by rw [Metric.mem_sphere, dist_zero_right]; exact hz⟩ : Metric.sphere (0 : ℂ) 1) =
        Circle.exp θ := by
      apply Subtype.ext
      rw [Work.Smooth.Jordan.circlePoint_coe, Circle.coe_exp]
    rw [hx, hρ θ]
  refine ⟨Work.Smooth.Jordan.PlaneSchoenflies.mk (S.toPlaneSeparation hc)
    ⟨fun z => ((Ψ.symm (discHomeo ρ z) : ↥(closure S.V)) : ℂ), ?_⟩ ?_ ?_ ?_⟩
  · exact continuous_subtype_val.comp (Ψ.symm.continuous.comp (discHomeo ρ).continuous)
  · intro z w hzw
    exact (discHomeo ρ).injective (Ψ.symm.injective (Subtype.ext hzw))
  · intro θ
    have hstep : discHomeo ρ (circlePoint θ) =
        Ψ ⟨c.γ θ, carathTrace_subset_closure_V S (c.mem_trace θ)⟩ := by
      apply Subtype.ext
      rw [hΦcircle θ]
    show ((Ψ.symm (discHomeo ρ (circlePoint θ)) : ↥(closure S.V)) : ℂ) = c.γ θ
    rw [hstep, Homeomorph.symm_apply_apply]
  · ext u
    constructor
    · rintro ⟨z, rfl⟩
      exact (Ψ.symm (discHomeo ρ z)).2
    · intro hu
      refine ⟨(discHomeo ρ).symm (Ψ ⟨u, hu⟩), ?_⟩
      show ((Ψ.symm (discHomeo ρ ((discHomeo ρ).symm (Ψ ⟨u, hu⟩))) : ↥(closure S.V)) : ℂ) = u
      rw [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

end

end Work.Smooth.SphereJordan
