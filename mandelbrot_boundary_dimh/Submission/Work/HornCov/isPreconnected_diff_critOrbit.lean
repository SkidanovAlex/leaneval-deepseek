import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornCov.exists_mem_ball_notMem_of_countable
import Submission.Work.Horn.basin_facts
import Submission.Work.HornVarphi.exists_ball_subset_diff_critOrbit

/-!
# `B ∖ critOrbit` is preconnected (HORN-VARPHI, auxiliary topology)

Let `f₀ ∈ 𝓕₀` with immediate basin `B` and (unique) critical point `c ∈ B`.  The forward critical
orbit `P⁺ = critOrbit f₀ c = {f₀^k c | k ≥ 1}` is a *countable* subset of the *open, connected*
domain `B`.  This file proves the topological fact that removing `P⁺` does not disconnect `B`:

  `IsPreconnected (B \ critOrbit f₀ c)`.

The mathematics is the classical statement that a countable set does not disconnect a domain in
`ℂ ≅ ℝ²` (dimension `> 1`):

* `isPreconnected_ball_diff_countable` : a ball of positive radius minus a countable set is
  preconnected (the complement of a countable set in a real vector space of dimension `> 1` is
  path connected, and a ball is homeomorphic to the ambient space);
* `exists_mem_ball_notMem_of_countable` : a countable set misses every positive-radius ball;
* `isPreconnected_diff_countable` : if `U` is open and preconnected and `C` is countable then
  `U ∖ C` is preconnected.  Fixing `x ∈ U ∖ C`, let `A` be its connected component in `U ∖ C` and
  `D = (U ∖ C) ∖ A`.  Since a ball minus a countable set is preconnected, both `A` and `D` are
  "locally whole balls", hence `closure A ∩ (U ∖ C) = A` and `closure D ∩ (U ∖ C) = D`; as
  `U ∖ C` is dense in `U`, this makes `U ⊆ closure A ∪ closure D` with
  `U ∩ closure A ∩ closure D = ∅`, and `isPreconnected_subset_or_subset_of_isClosed` (which
  merely unwinds the definition of `IsPreconnected`) forces `U ⊆ closure A` or `U ⊆ closure D`.
  Both alternatives contradict `D ≠ ∅` (in the first case `D ⊆ A`, in the second `x ∈ D`).
-/

namespace Work.HornCov

open Set Metric
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- A ball of positive radius minus a countable set is preconnected.  (`ℂ` is a real vector
space of dimension `2 > 1`, so the complement of a countable set is (path) connected, and any ball
is homeomorphic to `ℂ`.) -/
private theorem isPreconnected_ball_diff_countable {C : Set ℂ} (hC : C.Countable) {c : ℂ}
    {r : ℝ} (hr : 0 < r) : IsPreconnected (Metric.ball c r \ C) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    have h : Module.rank ℝ ℂ = 2 := by
      rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
      simp
    rw [h]; norm_num
  -- a homeomorphism from `ℂ` onto the ball
  let e : ℂ ≃ₜ ↥(Metric.ball c r) :=
    (Homeomorph.unitBall (E := ℂ)).trans
      ((OpenPartialHomeomorph.unitBallBall (c : ℂ) r hr).toHomeomorphSourceTarget)
  let Φ : ℂ → ℂ := fun z => ((e z : ↥(Metric.ball c r)) : ℂ)
  have hinj : Function.Injective Φ := fun a b hab => e.injective (Subtype.ext hab)
  have hpre : e ⁻¹' ((Subtype.val ⁻¹' (Cᶜ) : Set ↥(Metric.ball c r))) = (Φ ⁻¹' C)ᶜ := by
    ext z
    exact Iff.rfl
  have hconn : IsConnected (e ⁻¹' ((Subtype.val ⁻¹' (Cᶜ) : Set ↥(Metric.ball c r)))) := by
    rw [hpre]
    exact Set.Countable.isConnected_compl_of_one_lt_rank hrank (hC.preimage hinj)
  have hpc : IsPreconnected ((Subtype.val ⁻¹' (Cᶜ) : Set ↥(Metric.ball c r))) :=
    (Homeomorph.isPreconnected_preimage e).mp hconn.isPreconnected
  have h1 : IsPreconnected (Subtype.val '' (Subtype.val ⁻¹' (Cᶜ) : Set ↥(Metric.ball c r))) :=
    hpc.image Subtype.val continuous_subtype_val.continuousOn
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_comm] at h1
  exact h1

/-! ## Preconnectedness from two closed sets -/

/-- A preconnected set covered by two closed sets whose intersection meets the set only trivially
is contained in one of them. -/
theorem isPreconnected_subset_or_subset_of_isClosed {s F₁ F₂ : Set ℂ} (hpre : IsPreconnected s)
    (h₁ : IsClosed F₁) (h₂ : IsClosed F₂) (hsub : s ⊆ F₁ ∪ F₂)
    (hdisj : s ∩ F₁ ∩ F₂ = ∅) : s ⊆ F₁ ∨ s ⊆ F₂ := by
  by_contra h
  rw [not_or, not_subset, not_subset] at h
  obtain ⟨⟨x, hxs, hx₁⟩, ⟨y, hys, hy₂⟩⟩ := h
  have hdisj' : ∀ z, z ∈ s → z ∈ F₁ → z ∈ F₂ → False := by
    intro z hz h1 h2
    have hmem : z ∈ s ∩ F₁ ∩ F₂ := ⟨⟨hz, h1⟩, h2⟩
    rwa [hdisj] at hmem
  have hsub' : s ⊆ F₁ᶜ ∪ F₂ᶜ := by
    intro z hz
    rcases hsub hz with h1 | h2
    · by_cases h2' : z ∈ F₂
      · exact absurd (hdisj' z hz h1 h2') not_false
      · exact Or.inr h2'
    · by_cases h1' : z ∈ F₁
      · exact absurd (hdisj' z hz h1' h2) not_false
      · exact Or.inl h1'
  have hne := hpre F₁ᶜ F₂ᶜ h₁.isOpen_compl h₂.isOpen_compl hsub'
    ⟨x, hxs, hx₁⟩ ⟨y, hys, hy₂⟩
  obtain ⟨z, hz⟩ := hne
  rcases hsub hz.1 with h | h
  · exact hz.2.1 h
  · exact hz.2.2 h

/-! ## The general topological statement -/

/-- **A countable set does not disconnect an open preconnected set of `ℂ`.** -/
theorem isPreconnected_diff_countable {U C : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hC : C.Countable) : IsPreconnected (U \ C) := by
  classical
  -- a radius function: every point of `U` has a ball inside `U`
  have hρ : ∀ z ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ U := fun z hz => by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨ρ, hρpos, hρsub⟩
  let R : ℂ → ℝ := fun z => if hz : z ∈ U then Classical.choose (hρ z hz) else 1
  have hRpos : ∀ z ∈ U, 0 < R z := fun z hz => by
    simp only [R, dite_eq_left hz]
    exact (Classical.choose_spec (hρ z hz)).1
  have hRsub : ∀ z ∈ U, Metric.ball z (R z) ⊆ U := fun z hz => by
    simp only [R, dite_eq_left hz]
    exact (Classical.choose_spec (hρ z hz)).2
  have hballpre : ∀ z ∈ U, IsPreconnected (Metric.ball z (R z) \ C) := fun z hz =>
    isPreconnected_ball_diff_countable hC (hRpos z hz)
  rcases (U \ C).eq_empty_or_nonempty with hemp | ⟨x, hx⟩
  · rw [hemp]; exact isPreconnected_empty
  · have hWsub : U \ C ⊆ connectedComponentIn (U \ C) x := by
      intro y hy
      by_contra hyA
      set A : Set ℂ := connectedComponentIn (U \ C) x with hA
      set D : Set ℂ := (U \ C) \ A with hD
      have hxA : x ∈ A := by rw [hA]; exact mem_connectedComponentIn hx
      have hyD : y ∈ D := by rw [hD]; exact ⟨hy, hyA⟩
      -- maximality of the connected component
      have hmemA : ∀ {t : Set ℂ}, IsPreconnected t → t ⊆ U \ C → ∀ a ∈ t, a ∈ A → t ⊆ A := by
        intro t ht hts a hat haA
        have h1 : t ⊆ connectedComponentIn (U \ C) a := ht.subset_connectedComponentIn hat hts
        have h2 : connectedComponentIn (U \ C) a = A := by
          have haA' : a ∈ connectedComponentIn (U \ C) x := by rw [hA] at haA; exact haA
          rw [hA]; exact (connectedComponentIn_eq haA').symm
        exact h1.trans h2.le
      have hmemD : ∀ {t : Set ℂ}, IsPreconnected t → t ⊆ U \ C → ∀ d ∈ t, d ∈ D → t ⊆ D := by
        intro t ht hts d hdt hdD
        have h1 : t ⊆ connectedComponentIn (U \ C) d := ht.subset_connectedComponentIn hdt hts
        have h2 : connectedComponentIn (U \ C) d ⊆ D := by
          intro w hw
          have hwW : w ∈ U \ C := connectedComponentIn_subset _ _ hw
          have hdw : connectedComponentIn (U \ C) d = connectedComponentIn (U \ C) w :=
            connectedComponentIn_eq hw
          rw [hD]
          refine ⟨hwW, ?_⟩
          intro hwA
          have hwA' : w ∈ connectedComponentIn (U \ C) x := by rw [hA] at hwA; exact hwA
          have hddx : connectedComponentIn (U \ C) d = connectedComponentIn (U \ C) x :=
            hdw.trans (connectedComponentIn_eq hwA').symm
          have hdD' : d ∈ (U \ C) \ A := by rw [hD] at hdD; exact hdD
          exact hdD'.2 (by rw [hA, ← hddx]; exact mem_connectedComponentIn (hts hdt))
        exact h1.trans h2
      -- closedness of `A`, `D` inside `U ∖ C`
      have hclA : ∀ z ∈ U \ C, z ∈ closure A → z ∈ A := by
        intro z hzW hzcl
        obtain ⟨a, haA, haz⟩ := Metric.mem_closure_iff.mp hzcl (R z) (hRpos z hzW.1)
        have haB : a ∈ Metric.ball z (R z) := Metric.mem_ball.mpr (by rw [dist_comm]; exact haz)
        have haC : a ∉ C :=
          fun h => (connectedComponentIn_subset (U \ C) x (by rw [hA] at haA; exact haA)).2 h
        exact hmemA (hballpre z hzW.1) (fun w hw => ⟨hRsub z hzW.1 hw.1, hw.2⟩)
          a ⟨haB, haC⟩ haA ⟨Metric.mem_ball_self (hRpos z hzW.1), hzW.2⟩
      have hclD : ∀ z ∈ U \ C, z ∈ closure D → z ∈ D := by
        intro z hzW hzcl
        obtain ⟨d, hdD, hdz⟩ := Metric.mem_closure_iff.mp hzcl (R z) (hRpos z hzW.1)
        have hdB : d ∈ Metric.ball z (R z) := Metric.mem_ball.mpr (by rw [dist_comm]; exact hdz)
        have hdD' : d ∈ (U \ C) \ A := by rw [hD] at hdD; exact hdD
        exact hmemD (hballpre z hzW.1) (fun w hw => ⟨hRsub z hzW.1 hw.1, hw.2⟩)
          d ⟨hdB, hdD'.1.2⟩ hdD ⟨Metric.mem_ball_self (hRpos z hzW.1), hzW.2⟩
      -- `U ∖ C` is dense in `U`
      have hdense : U ⊆ closure (U \ C) := by
        intro z hzU
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨w, hwball, hwC⟩ :=
          exists_mem_ball_notMem_of_countable hC (lt_min hε (hRpos z hzU))
        have hwdist : dist z w < min ε (R z) := by
          rw [dist_comm]; exact Metric.mem_ball.mp hwball
        have hwB : w ∈ Metric.ball z (R z) :=
          Metric.mem_ball.mpr (by rw [dist_comm]; exact lt_of_lt_of_le hwdist (min_le_right _ _))
        exact ⟨w, ⟨hRsub z hzU hwB, hwC⟩, lt_of_lt_of_le hwdist (min_le_left _ _)⟩
      have hunion : U \ C = A ∪ D := by
        rw [hD]
        ext z
        constructor
        · intro hz
          by_cases hzA : z ∈ A
          · exact Or.inl hzA
          · exact Or.inr ⟨hz, hzA⟩
        · rintro (hz | hz)
          · exact connectedComponentIn_subset (U \ C) x (by rw [hA] at hz; exact hz)
          · exact hz.1
      have hcover : U ⊆ closure A ∪ closure D := by
        intro z hzU
        have h := hdense hzU
        rwa [hunion, closure_union] at h
      have hdisjA : U ∩ closure A ∩ closure D = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro z hz
        obtain ⟨⟨hzU, hzA⟩, hzD⟩ := hz
        obtain ⟨a, haA, haz⟩ := Metric.mem_closure_iff.mp hzA (R z) (hRpos z hzU)
        obtain ⟨d, hdD, hdz⟩ := Metric.mem_closure_iff.mp hzD (R z) (hRpos z hzU)
        have haB : a ∈ Metric.ball z (R z) := Metric.mem_ball.mpr (by rw [dist_comm]; exact haz)
        have hdB : d ∈ Metric.ball z (R z) := Metric.mem_ball.mpr (by rw [dist_comm]; exact hdz)
        have haC : a ∉ C :=
          fun h => (connectedComponentIn_subset (U \ C) x (by rw [hA] at haA; exact haA)).2 h
        have hdD' : d ∈ (U \ C) \ A := by rw [hD] at hdD; exact hdD
        exact hdD'.2 (hmemA (hballpre z hzU) (fun w hw => ⟨hRsub z hzU hw.1, hw.2⟩)
          a ⟨haB, haC⟩ haA ⟨hdB, hdD'.1.2⟩)
      rcases isPreconnected_subset_or_subset_of_isClosed hUc isClosed_closure isClosed_closure
        hcover hdisjA with hUA | hUD
      · have hyD' : y ∈ (U \ C) \ A := by rw [hD] at hyD; exact hyD
        exact hyD'.2 (hclA y hyD'.1 (hUA hyD'.1.1))
      · have hxA' : x ∈ U \ C := connectedComponentIn_subset (U \ C) x hxA
        have hxD' : x ∈ (U \ C) \ A := by
          rw [← hD]
          exact hclD x hxA' (hUD hxA'.1)
        exact hxD'.2 hxA
    have hEq : U \ C = connectedComponentIn (U \ C) x :=
      Subset.antisymm hWsub (connectedComponentIn_subset (U \ C) x)
    rw [hEq]
    exact isPreconnected_connectedComponentIn

/-! ## Countability of the critical orbit -/

/-- The forward critical orbit `{f₀^k c | k ≥ 1}` is countable. -/
theorem countable_critOrbit (f₀ : ℂ → ℂ) (c : ℂ) : (MandelDim.critOrbit f₀ c).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range (fun k : ℕ => f₀^[k] c))
  rintro z ⟨k, hk, rfl⟩
  exact ⟨k, rfl⟩

/-! ## The target -/

theorem isPreconnected_diff_critOrbit (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    IsPreconnected (B \ MandelDim.critOrbit f₀ c) :=
  isPreconnected_diff_countable hsetup.2.1.1 hsetup.2.1.2.1.isPreconnected
    (countable_critOrbit f₀ c)

end

end Work.HornCov
