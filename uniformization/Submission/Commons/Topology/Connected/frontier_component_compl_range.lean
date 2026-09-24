import Mathlib
import Submission.Commons.Topology.Connected.isPreconnected_compl_closedBall
import Submission.Commons.Topology.Brouwer.brouwer_fixed_point_closedBall

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Set Metric
open scoped Topology

namespace Commons.Topology.Connected

noncomputable section

/-- The closed unit interval as a type. -/
abbrev UI : Type := Set.Icc (0 : ℝ) 1

/-- A compact subset of the circle avoiding a point is contained in a closed arc
which also avoids that point (the arc being the image of `[0,1]` under an
injective continuous map into `Circle`). -/
lemma exists_closedArc_circle {S : Set Circle} (hS : IsCompact S) {t0 : Circle} (ht0 : t0 ∉ S) :
    ∃ α : C(UI, Circle), Function.Injective α ∧ S ⊆ Set.range α ∧ t0 ∉ Set.range α := by
  obtain ⟨θ0, hθ0⟩ := Circle.exp_surjective t0
  let T : Set ℝ := {θ | θ ∈ Set.Icc θ0 (θ0 + 2 * Real.pi) ∧ Circle.exp θ ∈ S}
  have hTsub : T ⊆ Set.Icc θ0 (θ0 + 2 * Real.pi) := fun θ h => h.1
  have hTclosed : IsClosed T :=
    isClosed_Icc.inter (hS.isClosed.preimage Circle.exp.continuous)
  have hTcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have hTmem : ∀ s ∈ S, ∃ θ ∈ T, Circle.exp θ = s := by
    intro s hs
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective s
    obtain ⟨k, hk⟩ : ∃ k : ℤ, θ + k * (2 * Real.pi) ∈ Set.Icc θ0 (θ0 + 2 * Real.pi) := by
      refine ⟨⌈(θ0 - θ) / (2 * Real.pi)⌉, ?_, ?_⟩
      · have h : (θ0 - θ) / (2 * Real.pi) ≤ ((⌈(θ0 - θ) / (2 * Real.pi)⌉ : ℤ) : ℝ) :=
          Int.le_ceil _
        have hp : (0:ℝ) < 2 * Real.pi := by positivity
        have hmul := mul_le_mul_of_nonneg_right h hp.le
        rw [div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
        linarith
      · have h : ((⌈(θ0 - θ) / (2 * Real.pi)⌉ : ℤ) : ℝ) < (θ0 - θ) / (2 * Real.pi) + 1 :=
          Int.ceil_lt_add_one _
        have hp : (0:ℝ) < 2 * Real.pi := by positivity
        have hmul := mul_lt_mul_of_pos_right h hp
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
        linarith
    refine ⟨θ + k * (2 * Real.pi), ⟨hk, ?_⟩, ?_⟩
    · rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one, hθ]; exact hs
    · rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]; exact hθ
  have hθ0T : θ0 ∉ T := fun h => ht0 (by rw [← hθ0]; exact h.2)
  have hθ1T : θ0 + 2 * Real.pi ∉ T := by
    intro h
    have h2 : Circle.exp (θ0 + 2 * Real.pi) ∈ S := h.2
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one, hθ0] at h2
    exact ht0 h2
  have hab : ∃ a b : ℝ,
      0 < b - a ∧ b - a < 2 * Real.pi ∧ T ⊆ Set.Icc a b ∧
        Set.Icc a b ⊆ Set.Ioo θ0 (θ0 + 2 * Real.pi) := by
    by_cases hTne : T.Nonempty
    · have hmT : sInf T ∈ T := hTcompact.sInf_mem hTne
      have hMT : sSup T ∈ T := hTcompact.sSup_mem hTne
      have hm_gt : θ0 < sInf T := lt_of_le_of_ne hmT.1.1 (fun h => hθ0T (h ▸ hmT))
      have hM_lt : sSup T < θ0 + 2 * Real.pi :=
        lt_of_le_of_ne hMT.1.2 (fun h => hθ1T (h ▸ hMT))
      have hbdd_below : BddBelow T := ⟨θ0, fun θ hθ => hθ.1.1⟩
      have hbdd_above : BddAbove T := ⟨θ0 + 2 * Real.pi, fun θ hθ => hθ.1.2⟩
      refine ⟨(θ0 + sInf T) / 2, (sSup T + θ0 + 2 * Real.pi) / 2, ?_, ?_, ?_, ?_⟩
      · have hle : sInf T ≤ sSup T := le_csSup hbdd_above hmT
        linarith [Real.pi_pos]
      · have hle : sInf T ≤ sSup T := le_csSup hbdd_above hmT
        have : sSup T - sInf T < 2 * Real.pi := by linarith
        linarith
      · intro θ hθ
        have h1 : sInf T ≤ θ := csInf_le hbdd_below hθ
        have h2 : θ ≤ sSup T := le_csSup hbdd_above hθ
        constructor <;> linarith
      · intro θ hθ
        exact ⟨by linarith [hθ.1, hm_gt], by linarith [hθ.2, hM_lt]⟩
    · have hTeq : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hTne
      refine ⟨θ0 + Real.pi / 2, θ0 + 3 * Real.pi / 2, ?_, ?_, ?_, ?_⟩
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · rw [hTeq]; exact Set.empty_subset _
      · intro θ hθ
        exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  obtain ⟨a, b, hbda, hab_lt, hTab, hab_θ⟩ := hab
  refine ⟨⟨fun t : UI => Circle.exp (a + (t:ℝ) * (b - a)), by fun_prop⟩, ?_, ?_, ?_⟩
  · intro t t' htt
    simp only [ContinuousMap.coe_mk] at htt
    have ht : a + (t:ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [t.2.1, t.2.2, hbda], by nlinarith [t.2.1, t.2.2, hbda]⟩
    have ht' : a + (t':ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [t'.2.1, t'.2.2, hbda], by nlinarith [t'.2.1, t'.2.2, hbda]⟩
    have h := Circle.exp_injOn_Icc hab_lt ht ht' htt
    have h2 : ((t:ℝ) - (t':ℝ)) * (b - a) = 0 := by linarith [h]
    have : (t:ℝ) = t' := by
      have := mul_eq_zero.mp h2
      rcases this with h3 | h3
      · linarith
      · exact absurd h3 (ne_of_gt hbda)
    exact Subtype.ext this
  · intro s hs
    obtain ⟨θ, hθT, hθ⟩ := hTmem s hs
    have hmem : θ ∈ Set.Icc a b := hTab hθT
    refine ⟨⟨(θ - a) / (b - a), ⟨?_, ?_⟩⟩, ?_⟩
    · rw [le_div_iff₀ hbda]; linarith [hmem.1]
    · rw [div_le_one hbda]; linarith [hmem.2]
    · simp only [ContinuousMap.coe_mk]
      rw [show a + ((θ - a) / (b - a)) * (b - a) = θ from by field_simp; ring]
      exact hθ
  · rintro ⟨t, ht⟩
    simp only [ContinuousMap.coe_mk] at ht
    rw [← hθ0, Circle.exp_eq_exp] at ht
    obtain ⟨m, hm⟩ := ht
    have htmem : a + (t:ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [t.2.1, t.2.2, hbda], by nlinarith [t.2.1, t.2.2, hbda]⟩
    have hIoo := hab_θ htmem
    have hval : a + (t:ℝ) * (b - a) - θ0 = m * (2 * Real.pi) := by linarith [hm]
    have hpos : (0:ℝ) < m * (2 * Real.pi) := by rw [← hval]; linarith [hIoo.1]
    have hlt : m * (2 * Real.pi) < 2 * Real.pi := by rw [← hval]; linarith [hIoo.2]
    have hm0 : m = 0 := by
      have hp : (0:ℝ) < 2 * Real.pi := by positivity
      have h1 : (0:ℝ) < m := by nlinarith
      have h2 : (m:ℝ) < 1 := by nlinarith
      have h1z : (0:ℤ) < m := by exact_mod_cast h1
      have h2z : m < 1 := by exact_mod_cast h2
      omega
    rw [hm0, Int.cast_zero, zero_mul] at hpos
    exact lt_irrefl _ hpos

/-- Given an injective continuous parametrisation `β` of an arc in `ℂ`, there is a
continuous retraction `r : ℂ → ℂ` of the plane onto the image of `β` which fixes
that image pointwise. -/
lemma exists_retraction_of_arc {β : C(UI, ℂ)} (hβ : Function.Injective β) :
    ∃ r : C(ℂ, ℂ), (∀ t : UI, r (β t) = β t) ∧ Set.range r ⊆ Set.range β := by
  haveI : CompactSpace UI := isCompact_iff_compactSpace.mp isCompact_Icc
  let A : Set ℂ := Set.range β
  let e0 : UI → A := fun t => ⟨β t, t, rfl⟩
  have he0cont : Continuous e0 := β.continuous.subtype_mk _
  have he0inj : Function.Injective e0 := fun a b hb => hβ (Subtype.ext_iff.mp hb)
  have he0surj : Function.Surjective e0 := fun a => by
    obtain ⟨t, ht⟩ := a.2
    exact ⟨t, Subtype.ext ht⟩
  let e : UI ≃ A := Equiv.ofBijective e0 ⟨he0inj, he0surj⟩
  have hecont : Continuous e := he0cont
  let β' : UI ≃ₜ A := Continuous.homeoOfEquivCompactToT2 hecont
  have hβ'key : ∀ t : UI, ((β' t : A) : ℂ) = β t := fun t => rfl
  have hβ'symm : ∀ t : UI, β'.symm ⟨β t, t, rfl⟩ = t := by
    intro t
    apply β'.injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  let f : C(A, ℝ) := ⟨fun a => ((β'.symm a : UI) : ℝ), by fun_prop⟩
  obtain ⟨g, hg⟩ := f.exists_restrict_eq (isCompact_range β.continuous).isClosed
  have hgapply : ∀ t : UI, g (⟨β t, t, rfl⟩ : A) = (t : ℝ) := by
    intro t
    have h := congrArg (fun (m : C(A, ℝ)) => m ⟨β t, t, rfl⟩) hg
    simpa [f, hβ'symm t] using h
  let g' : C(ℂ, UI) :=
    ⟨fun x => ⟨max 0 (min (g x) 1), ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩⟩,
      Continuous.subtype_mk (by fun_prop) _⟩
  refine ⟨⟨fun x => ((β' (g' x) : A) : ℂ), ?_⟩, ?_, ?_⟩
  · exact continuous_subtype_val.comp (β'.continuous.comp g'.continuous)
  · intro t
    have hgt : g' (β t) = t := by
      apply Subtype.ext
      show max 0 (min (g (β t)) 1) = (t : ℝ)
      rw [hgapply t, min_eq_left t.2.2, max_eq_right t.2.1]
    show ((β' (g' (β t)) : A) : ℂ) = β t
    rw [hgt, hβ'key t]
  · rintro _ ⟨x, rfl⟩
    exact ⟨g' x, (hβ'key (g' x)).symm⟩


/-- Auxiliary: the final numerical contradiction in the Maehara argument. -/
lemma smul_sub_eq_neg_false {c0 z : ℂ} {R : ℝ} (hR : 0 < R) (hz : ‖z - c0‖ = R)
    (h : (R / ‖z - c0‖) • (z - c0) = -(z - c0)) : False := by
  rw [hz, div_self (ne_of_gt hR), one_smul] at h
  have h2 : (z - c0) + (z - c0) = 0 := by
    have hh := congrArg (fun w => (z - c0) + w) h
    simpa using hh
  have h3 : (2:ℂ) * (z - c0) = 0 := by rw [two_mul]; exact h2
  have h4 : z - c0 = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num)
  rw [h4] at hz
  simp only [norm_zero] at hz
  linarith

theorem frontier_component_compl_range (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (h : ¬ IsPreconnected (Set.range γ)ᶜ) (x : ℂ) (hx : x ∈ (Set.range γ)ᶜ) :
    frontier (connectedComponentIn (Set.range γ)ᶜ x) = Set.range γ := by
  classical
  set K : Set ℂ := Set.range γ with hKdef
  have hKcompact : IsCompact K := isCompact_range γ.continuous
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKcopen : IsOpen Kᶜ := hKclosed.isOpen_compl
  set C : Set ℂ := connectedComponentIn Kᶜ x with hCdef
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCsub : C ⊆ Kᶜ := connectedComponentIn_subset Kᶜ x
  have hCop : IsOpen C := hKcopen.connectedComponentIn
  have hClosKc : closure C ∩ Kᶜ = C := by
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨subset_closure hz, hCsub hz⟩)
    rintro z ⟨hzcl, hzKc⟩
    have hmem : connectedComponentIn Kᶜ z ∈ 𝓝 z :=
      connectedComponentIn_mem_nhds (hKcopen.mem_nhds hzKc)
    obtain ⟨U, hUsub, hUopen, hzU⟩ := _root_.mem_nhds_iff.mp hmem
    obtain ⟨w, hw⟩ := _root_.mem_closure_iff.mp hzcl U hUopen hzU
    rw [Set.mem_inter_iff] at hw
    obtain ⟨hwU, hwC⟩ := hw
    have hwD : w ∈ connectedComponentIn Kᶜ z := hUsub hwU
    have hzeq : z ∈ connectedComponentIn Kᶜ z := mem_connectedComponentIn hzKc
    have h1 : connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ w := connectedComponentIn_eq hwD
    have h2 : connectedComponentIn Kᶜ w = connectedComponentIn Kᶜ x :=
      (connectedComponentIn_eq (hCdef ▸ hwC)).symm
    have hzw : z ∈ connectedComponentIn Kᶜ w := h1 ▸ hzeq
    have hzx : z ∈ connectedComponentIn Kᶜ x := h2 ▸ hzw
    exact hCdef.symm ▸ hzx
  have hfront_eq : frontier C = closure C \ C := hCop.frontier_eq
  have hfront_sub : frontier C ⊆ K := by
    intro z hz
    rw [hfront_eq] at hz
    by_contra hzK
    have hzc : z ∈ C := by
      rw [← hClosKc]
      exact ⟨hz.1, hzK⟩
    exact hz.2 hzc
  have hfinal : frontier C = K := by
    by_contra hne
    have hz0 : ∃ z0 ∈ K, z0 ∉ frontier C := by
      by_contra hc
      push Not at hc
      exact hne (Set.Subset.antisymm hfront_sub fun z hz => hc z hz)
    obtain ⟨z0, hz0K, hz0front⟩ := hz0
    -- Build a closed arc inside K containing frontier C
    obtain ⟨β, hβinj, hβsub, hβfront⟩ : ∃ β : C(UI, ℂ), Function.Injective β ∧
        Set.range β ⊆ K ∧ frontier C ⊆ Set.range β := by
      have hScompact : IsCompact (γ ⁻¹' frontier C) :=
        (isClosed_frontier.preimage γ.continuous).isCompact
      obtain ⟨t0, ht0⟩ := Set.mem_range.mp (hKdef ▸ hz0K)
      have ht0not : t0 ∉ γ ⁻¹' frontier C := fun hh => hz0front (ht0 ▸ hh)
      obtain ⟨α, hαinj, hαsub, hαnot⟩ := exists_closedArc_circle hScompact ht0not
      refine ⟨γ.comp α, hγ.comp hαinj, ?_, ?_⟩
      · rintro _ ⟨t, rfl⟩
        exact hKdef.symm ▸ ⟨α t, rfl⟩
      · intro z hz
        obtain ⟨s, hs⟩ := Set.mem_range.mp (hKdef ▸ hfront_sub hz)
        have hsS : s ∈ γ ⁻¹' frontier C := by rw [Set.mem_preimage, hs]; exact hz
        obtain ⟨t, ht⟩ := hαsub hsS
        exact ⟨t, by simp [ContinuousMap.comp_apply, ht, hs]⟩
    obtain ⟨r, hrβ, hrrange⟩ := exists_retraction_of_arc hβinj
    have hr_on : ∀ a ∈ Set.range β, r a = a := by
      rintro a ⟨t, rfl⟩
      exact hrβ t
    -- a radius bounding K
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ z ∈ K, ‖z‖ ≤ ρ := by
      obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hKcompact.isBounded
      exact ⟨ρ, fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hρ hz⟩
    by_cases hbdd : Bornology.IsBounded C
    · -- ===== bounded case: centre c0 = x =====
      have hclbdd : Bornology.IsBounded (closure C) := hbdd.closure
      obtain ⟨R1, hR1⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hclbdd
      obtain ⟨R2, hR2⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hKcompact.isBounded
      have hR1nonneg : 0 ≤ R1 := by
        have h1 := hR1 (subset_closure hxC)
        rw [Metric.mem_closedBall, dist_self] at h1
        exact h1
      set R : ℝ := max R1 R2 + 1 with hRdef
      have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_left R1 R2]
      have hcl_ball : closure C ⊆ Metric.ball x R := by
        intro z hz
        have h1 := hR1 hz
        rw [Metric.mem_closedBall] at h1
        rw [Metric.mem_ball]
        calc dist z x ≤ R1 := h1
          _ < R := by rw [hRdef]; linarith [le_max_left R1 R2]
      have hK_ball : K ⊆ Metric.closedBall x R := by
        intro z hz
        have h1 := hR2 hz
        rw [Metric.mem_closedBall] at h1
        rw [Metric.mem_closedBall]
        calc dist z x ≤ R2 := h1
          _ ≤ R := by rw [hRdef]; linarith [le_max_right R1 R2]
      set D : Set ℂ := Metric.closedBall x R with hDdef
      have hcontpiece : Continuous (fun z : ℂ => if z ∈ closure C then r z else z) := by
        apply continuous_if
        · intro a ha
          exact hr_on a (hβfront (frontier_closure_subset ha))
        · exact r.continuous.continuousOn
        · exact continuous_id.continuousOn
      set fp : C(ℂ, ℂ) := ⟨fun z => if z ∈ closure C then r z else z, hcontpiece⟩ with hfpdef
      set fD : C(D, ℂ) := fp.restrict D with hfDdef
      have hneD : ∀ z : D, fD z ≠ x := by
        intro z
        have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval]
        by_cases hzC : z.1 ∈ closure C
        · rw [if_pos hzC]
          intro heq
          have : r z.1 ∈ Set.range β := hrrange ⟨z.1, rfl⟩
          rw [heq] at this
          exact hCsub hxC (hKdef.symm ▸ hβsub this)
        · rw [if_neg hzC]
          intro heq
          exact hzC (heq ▸ subset_closure hxC)
      have hinD : ∀ z : D, fD z ∈ D := by
        intro z
        have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval]
        by_cases hzC : z.1 ∈ closure C
        · rw [if_pos hzC]
          exact hK_ball (hβsub (hrrange ⟨z.1, rfl⟩))
        · rw [if_neg hzC]
          exact z.2
      have hnormne : ∀ z : D, ‖fD z - x‖ ≠ 0 := fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hneD z))
      set w : D → ℂ := fun z => x + (R / ‖fD z - x‖) • (fD z - x) with hwdef
      have hwcont : Continuous w := by
        have hnorm : Continuous fun z : D => ‖fD z - x‖ := (fD.continuous.sub continuous_const).norm
        exact continuous_const.add ((continuous_const.div hnorm hnormne).smul
          (fD.continuous.sub continuous_const))
      have hw_sphere : ∀ z : D, ‖w z - x‖ = R := by
        intro z
        have heq : w z - x = (R / ‖fD z - x‖) • (fD z - x) := by rw [hwdef]; ring
        rw [heq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hRpos.le (norm_nonneg _))]
        rw [div_mul_cancel₀ _ (hnormne z)]
      have hGmem : ∀ z : D, (2 * x - w z) ∈ D := fun z => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h2 : (2 * x - w z) - x = -(w z - x) := by ring
        rw [h2, norm_neg, hw_sphere z]
      set G : C(D, D) := ⟨fun z => ⟨2 * x - w z, hGmem z⟩,
        Continuous.subtype_mk (continuous_const.sub hwcont) hGmem⟩ with hGdef
      obtain ⟨z, hzfix⟩ := Commons.Topology.Brouwer.brouwer_fixed_point_closedBall x hRpos G
      have hz1 : 2 * x - w z = z.1 := Subtype.ext_iff.mp hzfix
      have hwz : w z = 2 * x - z.1 := by rw [← hz1]; ring
      have hspz : ‖z.1 - x‖ = R := by
        have := hw_sphere z
        rw [hwz] at this
        rw [show (2 * x - z.1) - x = -(z.1 - x) from by ring, norm_neg] at this
        exact this
      have hz1notC : z.1 ∉ closure C := by
        intro hzc
        have h1 := hcl_ball hzc
        rw [Metric.mem_ball, dist_eq_norm, hspz] at h1
        linarith
      have hz_fd : fD z = z.1 := by
        have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval, if_neg hz1notC]
      have hdir : (R / ‖z.1 - x‖) • (z.1 - x) = -(z.1 - x) := by
        have hwdef' : w z = x + (R / ‖fD z - x‖) • (fD z - x) := rfl
        have hone : (R / ‖fD z - x‖) • (fD z - x) = -(z.1 - x) := by
          have h1 : x + (R / ‖fD z - x‖) • (fD z - x) = 2 * x - z.1 := by rw [← hwdef']; exact hwz
          have h2 : (R / ‖fD z - x‖) • (fD z - x) = (2 * x - z.1) - x := by
            linear_combination h1
          rw [h2]; ring
        rw [hz_fd, hspz, div_self (ne_of_gt hRpos), one_smul] at hone
        rw [hspz, div_self (ne_of_gt hRpos), one_smul]
        exact hone
      exact smul_sub_eq_neg_false hRpos hspz hdir
    · -- ===== unbounded case: centre c0 = p ∈ another (bounded) component =====
      have hOconn : IsPreconnected {z : ℂ | ρ < ‖z - 0‖} := isPreconnected_compl_closedBall 0 ρ
      have hOsub : {z : ℂ | ρ < ‖z - 0‖} ⊆ Kᶜ := by
        intro z hz hzK
        exact absurd (hρ z hzK) (not_le.mpr (by simpa using hz))
      have hz1 : ∃ z ∈ C, ρ < ‖z‖ := by
        by_contra hc
        push Not at hc
        apply hbdd
        rw [Metric.isBounded_iff_subset_closedBall (0:ℂ)]
        exact ⟨ρ, fun z hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hc z hz⟩
      obtain ⟨z1, hz1C, hz1ρ⟩ := hz1
      have hOsubC : {z : ℂ | ρ < ‖z - 0‖} ⊆ C := by
        have h1 : {z : ℂ | ρ < ‖z - 0‖} ⊆ connectedComponentIn Kᶜ z1 :=
          hOconn.subset_connectedComponentIn (by simpa using hz1ρ) hOsub
        have h2 : connectedComponentIn Kᶜ z1 = C := by
          rw [hCdef]
          exact (connectedComponentIn_eq (hCdef ▸ hz1C)).symm
        rw [h2] at h1; exact h1
      have hy : ∃ y ∈ Kᶜ, connectedComponentIn Kᶜ y ≠ C := by
        by_contra hc
        push Not at hc
        apply (hKdef.symm ▸ h)
        have hEq : Kᶜ = C := Set.Subset.antisymm
          (fun y hy => (hc y hy) ▸ mem_connectedComponentIn hy) hCsub
        exact hEq ▸ (show IsPreconnected C from hCdef ▸ isPreconnected_connectedComponentIn)
      obtain ⟨p, hpKc, hpne⟩ := hy
      have hpbdd : Bornology.IsBounded (connectedComponentIn Kᶜ p) := by
        by_contra hnb
        have hmeet : ∃ z ∈ connectedComponentIn Kᶜ p, ρ < ‖z‖ := by
          by_contra hc; push Not at hc
          apply hnb
          rw [Metric.isBounded_iff_subset_closedBall (0:ℂ)]
          exact ⟨ρ, fun z hz => by rw [Metric.mem_closedBall, dist_zero_right]; exact hc z hz⟩
        obtain ⟨z, hzp, hzρ⟩ := hmeet
        have hzC : z ∈ C := hOsubC (by simpa using hzρ)
        exact hpne ((connectedComponentIn_eq hzp).trans
          ((connectedComponentIn_eq (hCdef ▸ hzC)).symm.trans hCdef.symm))
      have hpnotC : p ∉ closure C := by
        intro hpcl
        have hpC : p ∈ C := by rw [← hClosKc]; exact ⟨hpcl, hpKc⟩
        exact hpne ((connectedComponentIn_eq (hCdef ▸ hpC)).symm.trans hCdef.symm)
      have hρnonneg : 0 ≤ ρ := by
        have h1 : ‖γ 1‖ ≤ ρ := hρ (γ 1) (hKdef.symm ▸ ⟨(1 : Circle), rfl⟩)
        linarith [norm_nonneg (γ 1)]
      set R : ℝ := ρ + ‖p‖ + 1 with hRdef
      have hRpos : 0 < R := by rw [hRdef]; positivity
      have hK_ball : K ⊆ Metric.closedBall p R := by
        intro z hz
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖z‖ ≤ ρ := hρ z hz
        calc ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le z p
          _ ≤ ρ + ‖p‖ := by linarith
          _ ≤ R := by rw [hRdef]; linarith
      have hsphereC : Metric.sphere p R ⊆ C := by
        intro z hz
        rw [Metric.mem_sphere, dist_eq_norm, hRdef] at hz
        apply hOsubC
        have hle : ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le z p
        have hxz : ρ < ‖z‖ := by
          have h2 : ρ + ‖p‖ + 1 ≤ ‖z‖ + ‖p‖ := by rw [← hz]; exact hle
          linarith
        simpa [sub_zero] using hxz
      set D : Set ℂ := Metric.closedBall p R with hDdef
      have hcontpiece : Continuous (fun z : ℂ => if z ∈ closure C then z else r z) := by
        apply continuous_if
        · intro a ha
          exact (hr_on a (hβfront (frontier_closure_subset ha))).symm
        · exact continuous_id.continuousOn
        · exact r.continuous.continuousOn
      set fp : C(ℂ, ℂ) := ⟨fun z => if z ∈ closure C then z else r z, hcontpiece⟩ with hfpdef
      set fD : C(D, ℂ) := fp.restrict D with hfDdef
      have hneD' : ∀ z : D, fD z ≠ p := by
        intro z
        have hzval : fD z = (if z.1 ∈ closure C then z.1 else r z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval]
        by_cases hzC : z.1 ∈ closure C
        · rw [if_pos hzC]
          intro heq
          exact hpnotC (heq ▸ hzC)
        · rw [if_neg hzC]
          intro heq
          have : r z.1 ∈ Set.range β := hrrange ⟨z.1, rfl⟩
          rw [heq] at this
          exact hpKc (hKdef.symm ▸ hβsub this)
      have hinD' : ∀ z : D, fD z ∈ D := by
        intro z
        have hzval : fD z = (if z.1 ∈ closure C then z.1 else r z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval]
        by_cases hzC : z.1 ∈ closure C
        · rw [if_pos hzC]; exact z.2
        · rw [if_neg hzC]
          exact hK_ball (hβsub (hrrange ⟨z.1, rfl⟩))
      have hnormne : ∀ z : D, ‖fD z - p‖ ≠ 0 := fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hneD' z))
      set w : D → ℂ := fun z => p + (R / ‖fD z - p‖) • (fD z - p) with hwdef
      have hwcont : Continuous w := by
        have hnorm : Continuous fun z : D => ‖fD z - p‖ := (fD.continuous.sub continuous_const).norm
        exact continuous_const.add ((continuous_const.div hnorm hnormne).smul
          (fD.continuous.sub continuous_const))
      have hw_sphere : ∀ z : D, ‖w z - p‖ = R := by
        intro z
        have heq : w z - p = (R / ‖fD z - p‖) • (fD z - p) := by rw [hwdef]; ring
        rw [heq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hRpos.le (norm_nonneg _))]
        rw [div_mul_cancel₀ _ (hnormne z)]
      have hGmem : ∀ z : D, (2 * p - w z) ∈ D := fun z => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h2 : (2 * p - w z) - p = -(w z - p) := by ring
        rw [h2, norm_neg, hw_sphere z]
      set G : C(D, D) := ⟨fun z => ⟨2 * p - w z, hGmem z⟩,
        Continuous.subtype_mk (continuous_const.sub hwcont) hGmem⟩ with hGdef
      obtain ⟨z, hzfix⟩ := Commons.Topology.Brouwer.brouwer_fixed_point_closedBall p hRpos G
      have hz1 : 2 * p - w z = z.1 := Subtype.ext_iff.mp hzfix
      have hwz : w z = 2 * p - z.1 := by rw [← hz1]; ring
      have hspz : ‖z.1 - p‖ = R := by
        have := hw_sphere z
        rw [hwz] at this
        rw [show (2 * p - z.1) - p = -(z.1 - p) from by ring, norm_neg] at this
        exact this
      have hz1C : z.1 ∈ closure C := by
        have : z.1 ∈ Metric.sphere p R := by rw [Metric.mem_sphere, dist_eq_norm]; exact hspz
        exact subset_closure (hsphereC this)
      have hz_fd : fD z = z.1 := by
        have hzval : fD z = (if z.1 ∈ closure C then z.1 else r z.1) := by
          rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
        rw [hzval, if_pos hz1C]
      have hdir : (R / ‖z.1 - p‖) • (z.1 - p) = -(z.1 - p) := by
        have hwdef' : w z = p + (R / ‖fD z - p‖) • (fD z - p) := rfl
        have hone : (R / ‖fD z - p‖) • (fD z - p) = -(z.1 - p) := by
          have h1 : p + (R / ‖fD z - p‖) • (fD z - p) = 2 * p - z.1 := by rw [← hwdef']; exact hwz
          have h2 : (R / ‖fD z - p‖) • (fD z - p) = (2 * p - z.1) - p := by
            linear_combination h1
          rw [h2]; ring
        rw [hz_fd, hspz, div_self (ne_of_gt hRpos), one_smul] at hone
        rw [hspz, div_self (ne_of_gt hRpos), one_smul]
        exact hone
      exact smul_sub_eq_neg_false hRpos hspz hdir
  exact hfinal


end

end Commons.Topology.Connected
