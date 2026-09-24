import Mathlib
import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two
import Submission.Commons.Topology.Jordan.arc_complement_no_bounded_component
import Submission.Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs
import Submission.Commons.Topology.Connected.frontier_component_compl_range

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

/-! ## Generic helpers -/

/-- Inserting a point of the closure of a preconnected set keeps it preconnected. -/
private lemma isPreconnected_insert_of_mem_closure {s : Set ℂ} (hs : IsPreconnected s) {y : ℂ}
    (hy : y ∈ closure s) : IsPreconnected (insert y s) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hs ⊢
  intro u v hu hv hsub huv
  have hsuv : s ⊆ u ∪ v := fun z hz => hsub (Set.mem_insert_iff.mpr (Or.inr hz))
  have hsuv' : s ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at huv ⊢
    rintro z ⟨hz1, hz2⟩
    exact huv z (by simp [hz1, hz2])
  rcases hs u v hu hv hsuv hsuv' with hsu | hsv
  · left
    have hyu : y ∈ u := by
      by_contra hyu
      have hyv : y ∈ v := (hsub (Set.mem_insert_iff.mpr (Or.inl rfl))).resolve_left hyu
      obtain ⟨w, hwv, hws⟩ := _root_.mem_closure_iff.mp hy v hv hyv
      exact (Set.eq_empty_iff_forall_notMem.mp huv) w
        ⟨Set.mem_insert_iff.mpr (Or.inr hws), hsu hws, hwv⟩
    intro z hz
    rcases (Set.mem_insert_iff.mp hz : z = y ∨ z ∈ s) with hzy | hzs
    · rw [hzy]; exact hyu
    · exact hsu hzs
  · right
    have hyv : y ∈ v := by
      by_contra hyv
      have hyu : y ∈ u := (hsub (Set.mem_insert_iff.mpr (Or.inl rfl))).resolve_right hyv
      obtain ⟨w, hwu, hws⟩ := _root_.mem_closure_iff.mp hy u hu hyu
      exact (Set.eq_empty_iff_forall_notMem.mp huv) w
        ⟨Set.mem_insert_iff.mpr (Or.inr hws), hwu, hsv hws⟩
    intro z hz
    rcases (Set.mem_insert_iff.mp hz : z = y ∨ z ∈ s) with hzy | hzs
    · rw [hzy]; exact hyv
    · exact hsv hzs

/-- A preconnected set contained in `S` and meeting a component of `S` lies in it. -/
private lemma preconnected_subset_component_of_meets {S H : Set ℂ} {x : ℂ}
    (hHpre : IsPreconnected H) (hHsub : H ⊆ S)
    (hmeet : (H ∩ connectedComponentIn S x).Nonempty) : H ⊆ connectedComponentIn S x := by
  obtain ⟨h, hhH, hhU⟩ := hmeet
  have h1 : H ⊆ connectedComponentIn S h := hHpre.subset_connectedComponentIn hhH hHsub
  have h2 : connectedComponentIn S h = connectedComponentIn S x :=
    (connectedComponentIn_eq hhU).symm
  rwa [h2] at h1

/-- The parametrisation `u ↦ c + r*u` of the round sphere `Metric.sphere c r`. -/
private def sphC (c : ℂ) (r : ℝ) : C(Circle, ℂ) := ⟨fun u => c + r * (u : ℂ), by fun_prop⟩

private lemma sphC_apply (c : ℂ) (r : ℝ) (u : Circle) : sphC c r u = c + r * (u : ℂ) := rfl

private lemma sphC_mem_sphere (c : ℂ) (r : ℝ) (hr : 0 < r) (u : Circle) :
    sphC c r u ∈ Metric.sphere c r := by
  rw [Metric.mem_sphere, dist_eq_norm, sphC_apply, add_sub_cancel_left, norm_mul,
    Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private lemma sphC_range (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Set.range (sphC c r) = Metric.sphere c r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩; exact sphC_mem_sphere c r hr u
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    refine ⟨⟨(z - c) / (r : ℂ), ?_⟩, ?_⟩
    · refine mem_sphere_zero_iff_norm.mpr ?_
      rw [norm_div, Complex.norm_real, hz, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    · show c + r * ((z - c) / (r : ℂ)) = z
      rw [← mul_div_assoc, mul_div_cancel_left₀ (z - c) hr0]
      ring

private lemma sphC_injective (c : ℂ) (r : ℝ) (hr : 0 < r) : Function.Injective (sphC c r) := by
  intro u v huv
  rw [sphC_apply, sphC_apply] at huv
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h : ((u:ℂ)) = (v:ℂ) := mul_left_cancel₀ hr0 (add_left_cancel huv)
  exact Subtype.ext h



/-! ## A circle does not embed in the real line -/

/-- There is no injective continuous map from the circle to `ℝ`. -/
private lemma no_injective_continuous_circle_real (f : C(Circle, ℝ)) :
    ¬ Function.Injective f := by
  intro hf
  have hne01 : Circle.exp 0 ≠ Circle.exp Real.pi := by
    intro h
    exact Circle.exp_pi_ne_one (by rw [← Circle.exp_zero]; exact h.symm)
  set K : Set ℝ := Set.range ⇑f with hK
  have hKne : K.Nonempty := ⟨f 1, Set.mem_range_self 1⟩
  have hKpre : IsPreconnected K := by
    rw [hK]; exact isPreconnected_range f.continuous
  have hKcomp : IsCompact K := by rw [hK]; exact isCompact_range f.continuous
  have hKord : K.OrdConnected := hKpre.ordConnected
  set a : ℝ := sInf K with hadef
  set b : ℝ := sSup K with hbdef
  have haK : a ∈ K := by rw [hadef]; exact hKcomp.sInf_mem hKne
  have hbK : b ∈ K := by rw [hbdef]; exact hKcomp.sSup_mem hKne
  have hle : a ≤ b := by
    obtain ⟨x, hx⟩ := hKne
    exact le_trans (csInf_le hKcomp.bddBelow hx) (le_csSup hKcomp.bddAbove hx)
  have hIK1 : Set.Icc a b ⊆ K := hKord.out haK hbK
  have hIK2 : K ⊆ Set.Icc a b := by
    intro x hx
    refine ⟨csInf_le hKcomp.bddBelow hx, le_csSup hKcomp.bddAbove hx⟩
  have hIK : Set.Icc a b = K := Set.Subset.antisymm hIK1 hIK2
  have hab : a < b := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hKsing : K = {a} := by rw [← hIK, h, Set.Icc_self]
      have hconst : ∀ u : Circle, f u = a := fun u => by
        have : f u ∈ K := Set.mem_range_self u
        rw [hKsing] at this; exact Set.mem_singleton_iff.mp this
      exact (hne01 (hf (by rw [hconst (Circle.exp 0), hconst (Circle.exp Real.pi)])))
  set m : ℝ := (a + b) / 2 with hmdef
  have ham : a < m := by rw [hmdef]; linarith
  have hmb : m < b := by rw [hmdef]; linarith
  have hmK : m ∈ K := hIK1 ⟨le_of_lt ham, le_of_lt hmb⟩
  obtain ⟨um, hum⟩ : ∃ u : Circle, f u = m := hmK
  obtain ⟨ua, hua⟩ : ∃ u : Circle, f u = a := haK
  obtain ⟨ub, hub⟩ : ∃ u : Circle, f u = b := hbK
  have huam : ua ≠ um := by intro h; rw [h] at hua; linarith [hua, hum]
  have hubm : ub ≠ um := by intro h; rw [h] at hub; linarith [hub, hum]
  have hpre : IsPreconnected ({um}ᶜ : Set Circle) :=
    (Circle.isPathConnected_compl_singleton um).isConnected.isPreconnected
  have himg : IsPreconnected (f '' ({um}ᶜ : Set Circle)) := hpre.image f f.continuous.continuousOn
  have hamem : a ∈ f '' ({um}ᶜ : Set Circle) := ⟨ua, by simpa using huam, hua⟩
  have hbmem : b ∈ f '' ({um}ᶜ : Set Circle) := ⟨ub, by simpa using hubm, hub⟩
  have hsub : Set.Icc a b ⊆ f '' ({um}ᶜ : Set Circle) := himg.ordConnected.out hamem hbmem
  obtain ⟨u, hu_ne, hu⟩ := hsub ⟨le_of_lt ham, le_of_lt hmb⟩
  have : u = um := hf (by rw [hu, hum])
  exact hu_ne (by simpa using this)



/-- No ball is contained in the image of an injective arc of `ℂ`. -/
private lemma range_arc_not_ball {β : C(Set.Icc (0:ℝ) 1, ℂ)} (hβ : Function.Injective β)
    {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) : ¬ (Metric.ball z ρ ⊆ Set.range β) := by
  intro hsub
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  set A : Set ℂ := Set.range β with hA
  let e0 : Set.Icc (0:ℝ) 1 → A := fun t => ⟨β t, t, rfl⟩
  have he0cont : Continuous e0 := β.continuous.subtype_mk _
  have he0inj : Function.Injective e0 := fun a b hb => hβ (Subtype.ext_iff.mp hb)
  have he0surj : Function.Surjective e0 := fun a => by
    obtain ⟨t, ht⟩ := a.2
    exact ⟨t, Subtype.ext ht⟩
  let e : Set.Icc (0:ℝ) 1 ≃ A := Equiv.ofBijective e0 ⟨he0inj, he0surj⟩
  have hecont : Continuous e := he0cont
  let β' : Set.Icc (0:ℝ) 1 ≃ₜ A := Continuous.homeoOfEquivCompactToT2 hecont
  have hc : (0:ℝ) < ρ / 2 := by linarith
  have hmem : ∀ u : Circle, z + (ρ / 2) * (u : ℂ) ∈ A := by
    intro u
    have hb : z + (ρ / 2) * (u : ℂ) ∈ Metric.ball z ρ := by
      rw [Metric.mem_ball, dist_eq_norm,
        show z + (ρ / 2) * (u : ℂ) - z = (ρ / 2 : ℂ) * (u : ℂ) by ring,
        norm_mul, Circle.norm_coe, mul_one,
        show (ρ / 2 : ℂ) = ((ρ / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      linarith
    exact hsub hb
  let φ : C(Circle, A) := ⟨fun u => ⟨z + (ρ / 2) * (u : ℂ), hmem u⟩,
      Continuous.subtype_mk (by fun_prop) _⟩
  let g : C(Circle, ℝ) :=
    ⟨fun u => ((β'.symm (φ u) : Set.Icc (0:ℝ) 1) : ℝ),
      (continuous_subtype_val.comp β'.symm.continuous).comp φ.continuous⟩
  have hginj : Function.Injective g := by
    intro u v huv
    have h1 : β'.symm (φ u) = β'.symm (φ v) := Subtype.ext huv
    have h2 : φ u = φ v := β'.symm.injective h1
    have h3 : z + (ρ / 2) * (u : ℂ) = z + (ρ / 2) * (v : ℂ) := Subtype.ext_iff.mp h2
    have h4 : (ρ / 2) * (u : ℂ) = (ρ / 2) * (v : ℂ) := add_left_cancel h3
    have hhalf : ((ρ : ℂ) / 2) ≠ 0 := by
      have : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      exact div_ne_zero this (by norm_num)
    have h5 : (u : ℂ) = (v : ℂ) := mul_left_cancel₀ hhalf h4
    exact Subtype.ext h5
  exact no_injective_continuous_circle_real g hginj



/-! ## Basic facts about the crosscut arc -/

private lemma range_beta_subset_closedBall {c : ℂ} {r : ℝ} (β : C(Set.Icc (0:ℝ) 1, ℂ))
    (hβ : Function.Injective β) (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r) :
    Set.range β ⊆ Metric.closedBall c r := by
  rintro z ⟨t, rfl⟩
  rcases eq_or_ne t 0 with rfl | ht0
  · exact Metric.sphere_subset_closedBall h0
  · rcases eq_or_ne t 1 with rfl | ht1
    · exact Metric.sphere_subset_closedBall h1
    · exact Metric.ball_subset_closedBall
        (hint t (fun h => ht0 (hβ h)) (fun h => ht1 (hβ h)))

private lemma range_beta_inter_sphere {c : ℂ} {r : ℝ} (β : C(Set.Icc (0:ℝ) 1, ℂ))
    (hβ : Function.Injective β) (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r) :
    Set.range β ∩ Metric.sphere c r = {β 0, β 1} := by
  ext w; constructor
  · rintro ⟨⟨t, rfl⟩, hwS⟩
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · rcases eq_or_ne t 1 with rfl | ht1
      · simp
      · exfalso
        have hb := hint t (fun h => ht0 (hβ h)) (fun h => ht1 (hβ h))
        rw [Metric.mem_sphere] at hwS
        rw [Metric.mem_ball] at hb
        linarith
  · rintro (h | h)
    · exact ⟨⟨0, h.symm⟩, h.symm ▸ h0⟩
    · exact ⟨⟨1, h.symm⟩, h.symm ▸ h1⟩

private lemma beta_mem_ball {c : ℂ} {r : ℝ} (β : C(Set.Icc (0:ℝ) 1, ℂ))
    (hβ : Function.Injective β)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r)
    {t : Set.Icc (0:ℝ) 1} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : β t ∈ Metric.ball c r :=
  hint t (fun h => ht0 (hβ h)) (fun h => ht1 (hβ h))

/-- **If a component of the complement of a crosscut accumulates, near the whole sphere,
at a spherical arc joining the two endpoints of the crosscut, then it accumulates at every
interior point of the crosscut.** -/
private lemma beta_mem_closure_of_arc_touch
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (β : C(Set.Icc (0:ℝ) 1, ℂ)) (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r)
    (α : C(Set.Icc (0:ℝ) 1, ℂ)) (hα : Function.Injective α)
    (hαS : ∀ u : Set.Icc (0:ℝ) 1, α u ∈ Metric.sphere c r)
    (hα0 : α 0 = β 0) (hα1 : α 1 = β 1)
    (hαdisj : ∀ s t : Set.Icc (0:ℝ) 1, β s = α t → s = 0 ∨ s = 1)
    {U : Set ℂ} (hUpre : IsPreconnected U) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hUsub : U ⊆ Metric.ball c r \ Set.range β)
    (hUcl : closure U ∩ (Metric.ball c r \ Set.range β) = U)
    (hS : closure U ∩ Metric.sphere c r ⊆ Set.range α) :
    ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 → β t ∈ closure U := by
  classical
  have hβ0ne : β 0 ≠ β 1 := by
    intro h
    have hc : (0 : Set.Icc (0:ℝ) 1) = 1 := hβ h
    exact absurd (congrArg (Subtype.val) hc) (by norm_num)
  obtain ⟨γ, hγ, hγrange⟩ :=
    exists_injective_circle_map_of_two_arcs β α hβ hα hα0.symm hα1.symm hβ0ne hαdisj
  have hrange : Set.range γ = Set.range β ∪ Set.range α := hγrange
  -- U avoids range γ
  have hUsubγ : U ⊆ (Set.range γ)ᶜ := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hUsub hz
    rw [Set.mem_compl_iff, hrange, Set.mem_union]
    push Not
    refine ⟨hz2, ?_⟩
    rintro ⟨u, rfl⟩
    have hb : dist (α u) c < r := Metric.mem_ball.mp hz1
    have hs : dist (α u) c = r := Metric.mem_sphere.mp (hαS u)
    linarith
  -- closure U ∩ (range γ)ᶜ = U
  have hclosγ : closure U ∩ (Set.range γ)ᶜ = U := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzcl, hzγ⟩
      have hzD : z ∈ Metric.closedBall c r := by
        have h1 : z ∈ closure (Metric.ball c r) :=
          closure_mono (fun y hy => (hUsub hy).1) hzcl
        rwa [closure_ball c hr.ne'] at h1
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzD) with hlt | heq
      · rw [← hUcl]
        refine ⟨hzcl, ?_, ?_⟩
        · exact hlt
        · exact fun h => hzγ (by rw [hrange]; exact Or.inl h)
      · exfalso
        apply hzγ
        rw [hrange]
        exact Or.inr (hS ⟨hzcl, Metric.mem_sphere.mpr heq⟩)
    · intro z hz
      exact ⟨subset_closure hz, hUsubγ hz⟩
  -- U is a proper subset of the complement
  have hUbdd : U ⊆ Metric.closedBall (0:ℂ) (‖c‖ + r) := by
    intro z hz
    have h1 : dist z c < r := Metric.mem_ball.mp (hUsub hz).1
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ = dist z 0 := by rw [dist_zero_right]
      _ ≤ dist z c + dist c 0 := dist_triangle _ _ _
      _ = dist z c + ‖c‖ := by rw [dist_zero_right]
      _ ≤ r + ‖c‖ := by linarith
      _ = ‖c‖ + r := by ring
  have hγbdd : Set.range γ ⊆ Metric.closedBall (0:ℂ) (‖c‖ + r) := by
    intro z hz
    rw [hrange, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨u, rfl⟩ := hz
      have hcl : dist (β u) c ≤ r := Metric.mem_closedBall.mp
        (range_beta_subset_closedBall β hβ h0 h1 hint ⟨u, rfl⟩)
      rw [Metric.mem_closedBall]
      have htri : dist (β u) 0 ≤ dist (β u) c + ‖c‖ := by
        have hh := dist_triangle (β u) c 0
        rwa [dist_zero_right c] at hh
      linarith
    · obtain ⟨u, rfl⟩ := hz
      have hcl : dist (α u) c ≤ r := Metric.mem_closedBall.mp
        (Metric.sphere_subset_closedBall (hαS u))
      rw [Metric.mem_closedBall]
      have htri : dist (α u) 0 ≤ dist (α u) c + ‖c‖ := by
        have hh := dist_triangle (α u) c 0
        rwa [dist_zero_right c] at hh
      linarith
  have hUneγ : U ≠ (Set.range γ)ᶜ := by
    intro heq
    obtain ⟨z, hz⟩ : ∃ z : ℂ, ‖c‖ + r < ‖z‖ :=
      ⟨((‖c‖ + r + 1 : ℝ) : ℂ), by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖c‖ + r + 1)]
        linarith⟩
    have hzγ : z ∈ (Set.range γ)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hzz
      have h1 : dist z 0 ≤ ‖c‖ + r := Metric.mem_closedBall.mp (hγbdd hzz)
      rw [dist_zero_right] at h1
      linarith
    rw [← heq] at hzγ
    have h2 : dist z 0 ≤ ‖c‖ + r := Metric.mem_closedBall.mp (hUbdd hzγ)
    rw [dist_zero_right] at h2
    linarith
  -- the complement of range γ is disconnected
  have hnotpre : ¬ IsPreconnected ((Set.range γ)ᶜ) := by
    intro hpre
    have hsub : (Set.range γ)ᶜ ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure U
      · left; rw [← hclosγ]; exact ⟨hzc, hz⟩
      · right; exact hzc
    have hinter : (Set.range γ)ᶜ ∩ (U ∩ (closure U)ᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨_, hzU, hzc⟩
      exact hzc (subset_closure hzU)
    rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) U ((closure U)ᶜ) hUopen
      isClosed_closure.isOpen_compl hsub hinter with h1 | h2
    · exact hUneγ (Set.Subset.antisymm hUsubγ h1)
    · obtain ⟨x, hxU⟩ := hUne
      exact h2 (hUsubγ hxU) (subset_closure hxU)
  -- apply the Jordan separation statement
  obtain ⟨x, hxU⟩ := hUne
  have hx : x ∈ (Set.range γ)ᶜ := hUsubγ hxU
  have hcomp : connectedComponentIn ((Set.range γ)ᶜ) x = U := by
    refine Set.Subset.antisymm ?_ ?_
    · have hsub : connectedComponentIn ((Set.range γ)ᶜ) x ⊆ U ∪ (closure U)ᶜ := by
        intro z hz
        have hzγ : z ∈ (Set.range γ)ᶜ := connectedComponentIn_subset _ _ hz
        by_cases hzc : z ∈ closure U
        · left; rw [← hclosγ]; exact ⟨hzc, hzγ⟩
        · right; exact hzc
      have hinter : connectedComponentIn ((Set.range γ)ᶜ) x ∩ (U ∩ (closure U)ᶜ) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨_, hzU, hzc⟩
        exact hzc (subset_closure hzU)
      rcases (isPreconnected_iff_subset_of_disjoint.mp
        (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := x))) U ((closure U)ᶜ)
        hUopen isClosed_closure.isOpen_compl hsub hinter with h1 | h2
      · exact h1
      · exact absurd (h2 (mem_connectedComponentIn hx)) (by simp [subset_closure hxU])
    · exact hUpre.subset_connectedComponentIn hxU hUsubγ
  have hfront := Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre x hx
  rw [hcomp] at hfront
  intro t ht0 ht1
  have hβt : β t ∈ Set.range γ := by rw [hrange]; exact Or.inl ⟨t, rfl⟩
  rw [← hfront] at hβt
  exact frontier_subset_closure hβt



/-! ## Boundary arcs of the sphere joining the two endpoints -/

private def bdryArc (c : ℂ) (r : ℝ) (u v : Circle) : C(Set.Icc (0:ℝ) 1, ℂ) :=
  ⟨fun t => sphC c r (Circle.path u v t), (sphC c r).continuous.comp (Circle.path u v).continuous⟩

private def bdryArcRev (c : ℂ) (r : ℝ) (u v : Circle) : C(Set.Icc (0:ℝ) 1, ℂ) :=
  ⟨fun t => sphC c r ((Circle.path u v).symm t),
    (sphC c r).continuous.comp (Circle.path u v).symm.continuous⟩

private lemma bdryArc_zero (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArc c r u v 0 = sphC c r u := by
  show sphC c r (Circle.path u v 0) = sphC c r u
  rw [(Circle.path u v).source]

private lemma bdryArc_one (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArc c r u v 1 = sphC c r v := by
  show sphC c r (Circle.path u v 1) = sphC c r v
  rw [(Circle.path u v).target]

private lemma bdryArcRev_zero (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArcRev c r u v 0 = sphC c r v := by
  show sphC c r ((Circle.path u v).symm 0) = sphC c r v
  rw [show (Circle.path u v).symm 0 = Circle.path u v 1 from by simp]
  rw [(Circle.path u v).target]

private lemma bdryArcRev_one (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArcRev c r u v 1 = sphC c r u := by
  show sphC c r ((Circle.path u v).symm 1) = sphC c r u
  rw [show (Circle.path u v).symm 1 = Circle.path u v 0 from by simp]
  rw [(Circle.path u v).source]

private lemma bdryArc_inj {c : ℂ} {r : ℝ} (hr : 0 < r) {u v : Circle} (huv : u ≠ v) :
    Function.Injective (bdryArc c r u v) := by
  intro a b hab
  exact Circle.path_injective_of_ne huv (sphC_injective c r hr hab)

private lemma bdryArcRev_inj {c : ℂ} {r : ℝ} (hr : 0 < r) {u v : Circle} (huv : u ≠ v) :
    Function.Injective (bdryArcRev c r u v) := by
  intro a b hab
  have h1 : (Circle.path u v).symm a = (Circle.path u v).symm b := sphC_injective c r hr hab
  have h2 : (Circle.path u v) (unitInterval.symm a) = (Circle.path u v) (unitInterval.symm b) := by
    rwa [Path.symm_apply, Path.symm_apply] at h1
  exact unitInterval.symm_bijective.injective (Circle.path_injective_of_ne huv h2)



/-! ## Decomposition of the sphere minus the crosscut into two open arcs -/

private lemma range_diff_path (u v : Circle) (huv : u ≠ v) :
    Set.range (Circle.path u v) \ {u, v} = Circle.path u v '' Set.Ioo (0:unitInterval) 1 := by
  have hinj : Function.Injective (Circle.path u v) := Circle.path_injective_of_ne huv
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t, rfl⟩, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    rw [Set.mem_image]
    have ht0 : (0 : unitInterval) ≠ t := by
      intro h
      exact hx.1 (by rw [← h, (Circle.path u v).source])
    have ht1 : t ≠ 1 := by
      intro h
      exact hx.2 (by rw [h, (Circle.path u v).target])
    exact ⟨t, ⟨lt_of_le_of_ne t.2.1 ht0, lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    push Not
    exact ⟨fun h => ht.1.ne' (hinj (by rw [h, (Circle.path u v).source])),
      fun h => ht.2.ne (hinj (by rw [h, (Circle.path u v).target]))⟩

private lemma path_Ioo_preconnected (u v : Circle) :
    IsPreconnected (Circle.path u v '' Set.Ioo (0:unitInterval) 1) :=
  IsPreconnected.image isPreconnected_Ioo _ (by fun_prop)

private lemma range_path_eq_Ioo_union (u v : Circle) (huv : u ≠ v) :
    Set.range (Circle.path u v) =
      Circle.path u v '' Set.Ioo (0:unitInterval) 1 ∪ {u, v} := by
  have hsub : ({u, v} : Set Circle) ⊆ Set.range (Circle.path u v) := by
    rintro x (h | h)
    · rw [h]; exact ⟨0, (Circle.path u v).source⟩
    · rw [h]; exact ⟨1, (Circle.path u v).target⟩
  ext x; constructor
  · intro hx
    by_cases hxt : x ∈ ({u, v} : Set Circle)
    · exact Or.inr hxt
    · left
      rw [← range_diff_path u v huv]
      exact ⟨hx, hxt⟩
  · rintro (h | h)
    · obtain ⟨t, -, ht⟩ := h
      exact ⟨t, ht⟩
    · exact hsub h



/-- A preconnected set contained in `V` and meeting a set `Z` that is clopen in `V` is contained
in `Z`. -/
private lemma preconnected_subset_of_clopen_sub {s V Z : Set ℂ} (hs : IsPreconnected s)
    (hsub : s ⊆ V)
    (hZo : ∃ O : Set ℂ, IsOpen O ∧ ∀ x ∈ V, (x ∈ Z ↔ x ∈ O))
    (hZc : ∃ C : Set ℂ, IsClosed C ∧ ∀ x ∈ V, (x ∈ Z ↔ x ∈ C))
    (hne : (s ∩ Z).Nonempty) : s ⊆ Z := by
  obtain ⟨O, hOo, hO⟩ := hZo
  obtain ⟨C, hCc, hC⟩ := hZc
  have hcov : s ⊆ O ∪ Cᶜ := by
    intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · refine Or.inr ?_
      intro hxC
      exact hxO ((hO x (hsub hx)).mp ((hC x (hsub hx)).mpr hxC))
  have hdisj : s ∩ (O ∩ Cᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxO, hxC⟩
    exact hxC ((hC x (hsub hx)).mp ((hO x (hsub hx)).mpr hxO))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hs) O Cᶜ hOo hCc.isOpen_compl hcov hdisj
    with h1 | h2
  · intro x hx
    exact (hO x (hsub hx)).mpr (h1 hx)
  · obtain ⟨x, hx, hxZ⟩ := hne
    exact absurd ((hC x (hsub hx)).mp hxZ) (by simpa using (h2 hx : x ∉ C))

/-- A component `V` of the crosscut complement contains a whole "cap" of the ball around any
sphere point outside the crosscut that lies in its closure. -/
private lemma subset_component_of_convex {c : ℂ} {r : ℝ} (β : C(Set.Icc (0:ℝ) 1, ℂ))
    (hAcl : IsClosed (Set.range β)) {V : Set ℂ}
    (hVsub : V ⊆ Metric.ball c r \ Set.range β)
    (hcomp : ∀ x ∈ V, connectedComponentIn (Metric.ball c r \ Set.range β) x = V)
    {z : ℂ} (hzA : z ∉ Set.range β) (hzcl : z ∈ closure V) :
    ∃ ε > 0, Metric.ball z ε ∩ Metric.ball c r ⊆ V := by
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hAcl.isOpen_compl z hzA
  refine ⟨ε, hεpos, ?_⟩
  have hHpre : IsPreconnected (Metric.ball z ε ∩ Metric.ball c r) :=
    ((convex_ball z ε).inter (convex_ball c r)).isPreconnected
  have hHsub : Metric.ball z ε ∩ Metric.ball c r ⊆ Metric.ball c r \ Set.range β :=
    fun y hy => ⟨hy.2, hεsub hy.1⟩
  obtain ⟨x, hxV, hxd⟩ := Metric.mem_closure_iff.mp hzcl ε hεpos
  have hxH : x ∈ Metric.ball z ε ∩ Metric.ball c r :=
    ⟨by rw [Metric.mem_ball, dist_comm]; exact hxd, (hVsub hxV).1⟩
  have h1 : Metric.ball z ε ∩ Metric.ball c r ⊆
      connectedComponentIn (Metric.ball c r \ Set.range β) x :=
    hHpre.subset_connectedComponentIn hxH hHsub
  rwa [hcomp x hxV] at h1


/-- **Crosscut components accumulate along the crosscut.**  Let `β` be an injective arc in `ℂ`
whose two endpoints lie on the sphere `sphere c r` of a round ball and whose interior lies in
the open ball (`β t ∈ ball c r` for `t ≠ 0, 1`).  Then every connected component of the
complement of the arc in the ball accumulates at every interior point of the arc: for every
`w ∈ ball c r \ range β` and every interior `t`, `β t` lies in the closure of the component
of `w`. -/
theorem crosscut_component_closure
    {c : ℂ} {r : ℝ} (hr : 0 < r) (β : C(Set.Icc (0:ℝ) 1, ℂ)) (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hint : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r)
    {w : ℂ} (hw : w ∈ Metric.ball c r \ Set.range β) :
    ∀ t : Set.Icc (0:ℝ) 1, t ≠ 0 → t ≠ 1 →
      β t ∈ closure (connectedComponentIn (Metric.ball c r \ Set.range β) w) := by
  classical
  set U : Set ℂ := connectedComponentIn (Metric.ball c r \ Set.range β) w with hUdef
  have hAclosed : IsClosed (Set.range β) := (isCompact_range β.continuous).isClosed
  have hWopen : IsOpen (Metric.ball c r \ Set.range β) := Metric.isOpen_ball.sdiff hAclosed
  have hUopen : IsOpen U := by rw [hUdef]; exact hWopen.connectedComponentIn
  have hUpre : IsPreconnected U := by rw [hUdef]; exact isPreconnected_connectedComponentIn
  have hUsubW : U ⊆ Metric.ball c r \ Set.range β := by
    rw [hUdef]; exact connectedComponentIn_subset _ _
  have hwU : w ∈ U := by rw [hUdef]; exact mem_connectedComponentIn hw
  have hUcomp : ∀ x ∈ U,
      connectedComponentIn (Metric.ball c r \ Set.range β) x = U := by
    intro x hx
    have hx' : x ∈ connectedComponentIn (Metric.ball c r \ Set.range β) w := hUdef ▸ hx
    rw [hUdef]; exact (connectedComponentIn_eq hx').symm
  have hUcl : closure U ∩ (Metric.ball c r \ Set.range β) = U := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzcl, hzW⟩
      have hins : IsPreconnected (insert z U) := isPreconnected_insert_of_mem_closure hUpre hzcl
      have hsub : insert z U ⊆ Metric.ball c r \ Set.range β := by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with h | h
        · rw [h]; exact hzW
        · exact hUsubW h
      have hmain := hins.subset_connectedComponentIn (Set.mem_insert_iff.mpr (Or.inr hwU)) hsub
      rw [← hUdef] at hmain
      exact hmain (Set.mem_insert_iff.mpr (Or.inl rfl))
    · intro z hz; exact ⟨subset_closure hz, hUsubW hz⟩
  by_cases hWpre : IsPreconnected (Metric.ball c r \ Set.range β)
  · have hUW : U = Metric.ball c r \ Set.range β := by
      rw [hUdef]; exact hWpre.connectedComponentIn hw
    intro t ht0 ht1
    rw [hUW, Metric.mem_closure_iff]
    intro ε hε
    have hβtD : β t ∈ Metric.ball c r := beta_mem_ball β hβ hint ht0 ht1
    have hdc : dist (β t) c < r := Metric.mem_ball.mp hβtD
    set δ : ℝ := min (ε / 2) ((r - dist (β t) c) / 2) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ ε / 2 := by rw [hδdef]; exact min_le_left _ _
    have hδ2 : δ ≤ (r - dist (β t) c) / 2 := by rw [hδdef]; exact min_le_right _ _
    have hballD : Metric.ball (β t) δ ⊆ Metric.ball c r := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y c ≤ dist y (β t) + dist (β t) c := dist_triangle _ _ _
        _ < δ + dist (β t) c := by linarith
        _ ≤ (r - dist (β t) c) / 2 + dist (β t) c := by linarith
        _ < r := by linarith
    obtain ⟨y, hyb, hyA⟩ : ∃ y, y ∈ Metric.ball (β t) δ ∧ y ∉ Set.range β := by
      by_contra hc
      push Not at hc
      exact range_arc_not_ball hβ hδpos hc
    refine ⟨y, ⟨hballD hyb, hyA⟩, ?_⟩
    rw [dist_comm]
    calc dist y (β t) < δ := Metric.mem_ball.mp hyb
      _ ≤ ε / 2 := hδ1
      _ < ε := by linarith
  · -- the complement of the crosscut has exactly two components
    have hfrontD : frontier U ∩ Metric.ball c r ⊆ Set.range β := by
      rintro z ⟨hzf, hzD⟩
      by_contra hzA
      rw [hUopen.frontier_eq] at hzf
      have hzW : z ∈ Metric.ball c r \ Set.range β := ⟨hzD, hzA⟩
      have hzU : z ∈ U := by rw [← hUcl]; exact ⟨hzf.1, hzW⟩
      exact hzf.2 hzU
    have hfront_sub : frontier U ⊆ Set.range β ∪ Metric.sphere c r := by
      intro z hz
      have hzcl : z ∈ closure U := frontier_subset_closure hz
      have hbdd : closure U ⊆ Metric.closedBall c r := by
        have h1 : closure U ⊆ closure (Metric.ball c r) :=
          closure_mono (hUsubW.trans Set.sdiff_subset)
        rwa [closure_ball c hr.ne'] at h1
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp (hbdd hzcl)) with hlt | heq
      · exact Or.inl (hfrontD ⟨hz, Metric.mem_ball.mpr hlt⟩)
      · exact Or.inr (Metric.mem_sphere.mpr heq)
    have hβ0ne : β 0 ≠ β 1 := by
      intro hh
      have : (0 : Set.Icc (0:ℝ) 1) = 1 := hβ hh
      exact absurd (congrArg Subtype.val this) (by norm_num)
    have hSopen : ∀ z : ℂ, z ∉ Set.range β → ∃ ε > 0, Metric.ball z ε ⊆ (Set.range β)ᶜ := by
      intro z hzA
      rcases Metric.isOpen_iff.mp hAclosed.isOpen_compl z hzA with ⟨ε, hε, hsub⟩
      exact ⟨ε, hε, hsub⟩
    have hcap : ∀ z : ℂ, z ∉ Set.range β → z ∈ closure U →
        ∃ ε > 0, Metric.ball z ε ∩ Metric.ball c r ⊆ U :=
      fun z hzA hzcl => subset_component_of_convex β hAclosed hUsubW hUcomp hzA hzcl
    have hZopen : ∀ z ∈ closure U ∩ (Metric.sphere c r \ Set.range β),
        ∃ ε > 0, Metric.ball z ε ∩ (Metric.sphere c r \ Set.range β)
          ⊆ closure U ∩ (Metric.sphere c r \ Set.range β) := by
      rintro z ⟨hzcl, hzS, hzA⟩
      obtain ⟨ε, hεpos, hεsub⟩ := hcap z hzA hzcl
      refine ⟨ε, hεpos, ?_⟩
      rintro z' ⟨hz'1, hz'S, hz'A⟩
      refine ⟨?_, hz'S, hz'A⟩
      have hz'cl2 : z' ∈ closure (Metric.ball z ε ∩ Metric.ball c r) := by
        rw [Metric.mem_closure_iff]
        intro η hη
        obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z' hz'1
        have hηδ : 0 < min η δ := lt_min hη hδpos
        have hz'cb : z' ∈ closure (Metric.ball c r) := by
          rw [closure_ball c hr.ne']
          exact Metric.sphere_subset_closedBall hz'S
        obtain ⟨y, hy⟩ := Metric.mem_closure_iff.mp hz'cb (min η δ) hηδ
        exact ⟨y, ⟨hδsub (Metric.mem_ball.mpr
          (by rw [dist_comm]; exact lt_of_lt_of_le hy.2 (min_le_right _ _))), hy.1⟩,
          lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
      exact closure_mono hεsub hz'cl2
    have hZne : (closure U ∩ (Metric.sphere c r \ Set.range β)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hfrontA : frontier U ⊆ Set.range β := by
        intro z hz
        rcases hfront_sub hz with h | h
        · exact h
        · by_contra hzA
          exact Set.notMem_empty z (hemp ▸ (⟨frontier_subset_closure hz, h, hzA⟩ :
            z ∈ closure U ∩ (Metric.sphere c r \ Set.range β)))
      exact arc_complement_no_bounded_component β hβ hUopen ⟨w, hwU⟩
        (Metric.isBounded_ball.subset (hUsubW.trans Set.sdiff_subset)) hUpre hfrontA
        (Set.disjoint_left.mpr (fun z hzU hzA => (hUsubW hzU).2 hzA))
    -- the second component
    obtain ⟨w', hw'W, hw'U⟩ : ∃ w', w' ∈ Metric.ball c r \ Set.range β ∧ w' ∉ U := by
      by_contra hc
      push Not at hc
      have hUW : U = Metric.ball c r \ Set.range β := Set.Subset.antisymm hUsubW hc
      exact hWpre (hUW ▸ hUpre)
    have hw'W' : w' ∈ Metric.ball c r \ Set.range β := hw'W
    set U' : Set ℂ := connectedComponentIn (Metric.ball c r \ Set.range β) w' with hU'def
    have hU'open : IsOpen U' := by rw [hU'def]; exact hWopen.connectedComponentIn
    have hU'pre : IsPreconnected U' := by rw [hU'def]; exact isPreconnected_connectedComponentIn
    have hU'subW : U' ⊆ Metric.ball c r \ Set.range β := by
      rw [hU'def]; exact connectedComponentIn_subset _ _
    have hw'U' : w' ∈ U' := by rw [hU'def]; exact mem_connectedComponentIn hw'W'
    have hU'comp : ∀ x ∈ U',
        connectedComponentIn (Metric.ball c r \ Set.range β) x = U' := by
      intro x hx
      have hx' : x ∈ connectedComponentIn (Metric.ball c r \ Set.range β) w' := hU'def ▸ hx
      rw [hU'def]; exact (connectedComponentIn_eq hx').symm
    have hU'cl : closure U' ∩ (Metric.ball c r \ Set.range β) = U' := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro z ⟨hzcl, hzW⟩
        have hins : IsPreconnected (insert z U') := isPreconnected_insert_of_mem_closure hU'pre hzcl
        have hsub : insert z U' ⊆ Metric.ball c r \ Set.range β := by
          intro y hy
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hzW
          · exact hU'subW h
        have hmain := hins.subset_connectedComponentIn (Set.mem_insert_iff.mpr (Or.inr hw'U')) hsub
        rw [← hU'def] at hmain
        exact hmain (Set.mem_insert_iff.mpr (Or.inl rfl))
      · intro z hz; exact ⟨subset_closure hz, hU'subW hz⟩
    have hUdisjU' : Disjoint U U' := by
      rw [Set.disjoint_left]
      intro z hzU hzU'
      have h1 : U = U' := by
        rw [hUdef, hU'def]
        exact (connectedComponentIn_eq (hUdef ▸ hzU)).trans
          (connectedComponentIn_eq (hU'def ▸ hzU')).symm
      rw [h1] at hw'U
      exact hw'U hw'U'
    have hfrontD' : frontier U' ∩ Metric.ball c r ⊆ Set.range β := by
      rintro z ⟨hzf, hzD⟩
      by_contra hzA
      rw [hU'open.frontier_eq] at hzf
      have hzW : z ∈ Metric.ball c r \ Set.range β := ⟨hzD, hzA⟩
      have hzU : z ∈ U' := by rw [← hU'cl]; exact ⟨hzf.1, hzW⟩
      exact hzf.2 hzU
    have hfront_sub' : frontier U' ⊆ Set.range β ∪ Metric.sphere c r := by
      intro z hz
      have hzcl : z ∈ closure U' := frontier_subset_closure hz
      have hbdd : closure U' ⊆ Metric.closedBall c r := by
        have h1 : closure U' ⊆ closure (Metric.ball c r) :=
          closure_mono (hU'subW.trans Set.sdiff_subset)
        rwa [closure_ball c hr.ne'] at h1
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp (hbdd hzcl)) with hlt | heq
      · exact Or.inl (hfrontD' ⟨hz, Metric.mem_ball.mpr hlt⟩)
      · exact Or.inr (Metric.mem_sphere.mpr heq)
    have hZne' : (closure U' ∩ (Metric.sphere c r \ Set.range β)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hfrontA : frontier U' ⊆ Set.range β := by
        intro z hz
        rcases hfront_sub' hz with h | h
        · exact h
        · by_contra hzA
          exact Set.notMem_empty z (hemp ▸ (⟨frontier_subset_closure hz, h, hzA⟩ :
            z ∈ closure U' ∩ (Metric.sphere c r \ Set.range β)))
      exact arc_complement_no_bounded_component β hβ hU'open ⟨w', hw'U'⟩
        (Metric.isBounded_ball.subset (hU'subW.trans Set.sdiff_subset)) hU'pre hfrontA
        (Set.disjoint_left.mpr (fun z hzU hzA => (hU'subW hzU).2 hzA))
    have hZdisj : Disjoint (closure U ∩ (Metric.sphere c r \ Set.range β))
        (closure U' ∩ (Metric.sphere c r \ Set.range β)) := by
      rw [Set.disjoint_left]
      rintro z ⟨hzUcl, hzS, hzA⟩ ⟨hzU'cl, _, _⟩
      obtain ⟨ε, hεpos, hεsub⟩ := hSopen z hzA
      obtain ⟨x, hxU, hxd⟩ := Metric.mem_closure_iff.mp hzUcl ε hεpos
      obtain ⟨x', hx'U', hx'd⟩ := Metric.mem_closure_iff.mp hzU'cl ε hεpos
      have hHpre : IsPreconnected (Metric.ball z ε ∩ Metric.ball c r) :=
        ((convex_ball z ε).inter (convex_ball c r)).isPreconnected
      have hHsub : Metric.ball z ε ∩ Metric.ball c r ⊆ Metric.ball c r \ Set.range β :=
        fun y hy => ⟨hy.2, hεsub hy.1⟩
      have hxH : x ∈ Metric.ball z ε ∩ Metric.ball c r :=
        ⟨by rw [Metric.mem_ball, dist_comm]; exact hxd, (hUsubW hxU).1⟩
      have hxH' : x' ∈ Metric.ball z ε ∩ Metric.ball c r :=
        ⟨by rw [Metric.mem_ball, dist_comm]; exact hx'd, (hU'subW hx'U').1⟩
      have h1 : Metric.ball z ε ∩ Metric.ball c r ⊆
          connectedComponentIn (Metric.ball c r \ Set.range β) x :=
        hHpre.subset_connectedComponentIn hxH hHsub
      have hx'U : x' ∈ U := by
        have h2 := h1 hxH'
        rwa [hUcomp x hxU] at h2
      exact Set.notMem_empty x' (hUdisjU'.le_bot ⟨hx'U, hx'U'⟩)
    have hZlt : closure U ∩ (Metric.sphere c r \ Set.range β)
        ≠ Metric.sphere c r \ Set.range β := by
      intro heq
      obtain ⟨z, hz⟩ := hZne'
      have hzZ : z ∈ closure U ∩ (Metric.sphere c r \ Set.range β) := by
        rw [heq]; exact hz.2
      exact (Set.disjoint_left.mp hZdisj hzZ) ⟨hz.1, hz.2⟩
    -- the two boundary arcs
    obtain ⟨u0, hu0⟩ : ∃ u : Circle, sphC c r u = β 0 := by
      have : β 0 ∈ Set.range (sphC c r) := by rw [sphC_range c r hr]; exact h0
      exact this
    obtain ⟨u1, hu1⟩ : ∃ u : Circle, sphC c r u = β 1 := by
      have : β 1 ∈ Set.range (sphC c r) := by rw [sphC_range c r hr]; exact h1
      exact this
    have hu01 : u0 ≠ u1 := by
      intro h
      exact hβ0ne (by rw [← hu0, ← hu1, h])
    set arcA : C(Set.Icc (0:ℝ) 1, ℂ) := bdryArc c r u0 u1 with harcA
    set arcB : C(Set.Icc (0:ℝ) 1, ℂ) := bdryArcRev c r u1 u0 with harcB
    set RAo : Set ℂ := sphC c r '' (Circle.path u0 u1 '' Set.Ioo (0:unitInterval) 1) with hRAo
    set RBo : Set ℂ := sphC c r '' (Circle.path u1 u0 '' Set.Ioo (0:unitInterval) 1) with hRBo
    have harcA0 : arcA 0 = β 0 := by rw [harcA, bdryArc_zero, hu0]
    have harcA1 : arcA 1 = β 1 := by rw [harcA, bdryArc_one, hu1]
    have harcB0 : arcB 0 = β 0 := by rw [harcB, bdryArcRev_zero, hu0]
    have harcB1 : arcB 1 = β 1 := by rw [harcB, bdryArcRev_one, hu1]
    have harcAinj : Function.Injective arcA := by rw [harcA]; exact bdryArc_inj hr hu01
    have harcBinj : Function.Injective arcB := by rw [harcB]; exact bdryArcRev_inj hr hu01.symm
    have harcAS : ∀ t : Set.Icc (0:ℝ) 1, arcA t ∈ Metric.sphere c r := by
      intro t; rw [harcA]; exact sphC_mem_sphere c r hr _
    have harcBS : ∀ t : Set.Icc (0:ℝ) 1, arcB t ∈ Metric.sphere c r := by
      intro t; rw [harcB]; exact sphC_mem_sphere c r hr _
    have hRAopre : IsPreconnected RAo := by
      rw [hRAo]
      exact IsPreconnected.image (path_Ioo_preconnected u0 u1) _
        (sphC c r).continuous.continuousOn
    have hRBopre : IsPreconnected RBo := by
      rw [hRBo]
      exact IsPreconnected.image (path_Ioo_preconnected u1 u0) _
        (sphC c r).continuous.continuousOn
    -- the sphere minus the crosscut is the union of the two open arcs
    have hSat : Metric.sphere c r = sphC c r '' (Set.univ : Set Circle) := by
      rw [Set.image_univ]; exact (sphC_range c r hr).symm
    have hpair : ({β 0, β 1} : Set ℂ) = sphC c r '' ({u0, u1} : Set Circle) := by
      rw [Set.image_pair, hu0, hu1]
    have hsquare : Metric.sphere c r \ Set.range β = RAo ∪ RBo := by
      have hAb : Set.range β ∩ Metric.sphere c r = {β 0, β 1} :=
        range_beta_inter_sphere β hβ h0 h1 hint
      have hdiff : Metric.sphere c r \ Set.range β = Metric.sphere c r \ {β 0, β 1} := by
        ext z; constructor
        · rintro ⟨hzS, hzA⟩
          refine ⟨hzS, ?_⟩
          rintro hz2
          rw [← hAb] at hz2
          exact hzA hz2.1
        · rintro ⟨hzS, hz2⟩
          refine ⟨hzS, ?_⟩
          rintro hzA
          exact hz2 (by rw [← hAb]; exact ⟨hzA, hzS⟩)
      rw [hdiff, hSat, hpair, ← Set.image_sdiff (sphC_injective c r hr)]
      rw [show (Set.univ : Set Circle) \ {u0, u1} =
          (Set.range (Circle.path u0 u1) ∪ Set.range (Circle.path u1 u0)) \ {u0, u1} from by
        rw [Circle.range_path_union_range_path hu01]]
      rw [Set.union_diff_distrib, range_diff_path u0 u1 hu01]
      rw [show (Set.range (Circle.path u1 u0) \ {u0, u1}) =
          Circle.path u1 u0 '' Set.Ioo (0:unitInterval) 1 from by
        rw [Set.pair_comm u0 u1]; exact range_diff_path u1 u0 hu01.symm]
      rw [Set.image_union, hRAo, hRBo]
    have hRAo_diff : RAo ⊆ Metric.sphere c r \ Set.range β := by
      rw [hsquare]; exact Set.subset_union_left
    have hRBo_diff : RBo ⊆ Metric.sphere c r \ Set.range β := by
      rw [hsquare]; exact Set.subset_union_right
    have hRAorange : RAo ∪ {β 0, β 1} = Set.range arcA := by
      have hfun : (arcA : Set.Icc (0:ℝ) 1 → ℂ) = (sphC c r) ∘ (Circle.path u0 u1) := by
        rw [harcA]; rfl
      have h1 : Set.range arcA = sphC c r '' Set.range (Circle.path u0 u1) := by
        rw [hfun, Set.range_comp]
      rw [h1, hpair, hRAo, range_path_eq_Ioo_union u0 u1 hu01, Set.image_union]
    have hRBorange : RBo ∪ {β 0, β 1} = Set.range arcB := by
      have hfun : (arcB : Set.Icc (0:ℝ) 1 → ℂ) = (sphC c r) ∘ (Circle.path u1 u0).symm := by
        rw [harcB]; rfl
      have h1 : Set.range arcB = sphC c r '' Set.range (Circle.path u1 u0) := by
        rw [hfun, Set.range_comp, Path.symm_range]
      rw [h1, hpair, hRBo, range_path_eq_Ioo_union u1 u0 hu01.symm, Set.image_union,
        Set.pair_comm u1 u0]
    -- Z is clopen in the two-arc union
    have hZclosed : ∃ C : Set ℂ, IsClosed C ∧
        ∀ x ∈ Metric.sphere c r \ Set.range β,
          (x ∈ closure U ∩ (Metric.sphere c r \ Set.range β) ↔ x ∈ C) :=
      ⟨closure U, isClosed_closure, fun x hx => by
        constructor
        · intro h; exact h.1
        · intro h; exact ⟨h, hx⟩⟩
    have hZopene : ∃ O : Set ℂ, IsOpen O ∧
        ∀ x ∈ Metric.sphere c r \ Set.range β,
          (x ∈ closure U ∩ (Metric.sphere c r \ Set.range β) ↔ x ∈ O) := by
      let Z : Set ℂ := closure U ∩ (Metric.sphere c r \ Set.range β)
      have hsub : ∀ z ∈ Z, ∃ ε > 0,
          Metric.ball z ε ∩ (Metric.sphere c r \ Set.range β) ⊆ Z :=
        fun z hz => hZopen z hz
      let eps : ℂ → ℝ := fun z => if hz : z ∈ Z then Classical.choose (hsub z hz) else 1
      have hepspos : ∀ z (hz : z ∈ Z), 0 < eps z := by
        intro z hz; simp only [eps]; rw [dif_pos hz]
        exact (Classical.choose_spec (hsub z hz)).1
      have hepssub : ∀ z (hz : z ∈ Z),
          Metric.ball z (eps z) ∩ (Metric.sphere c r \ Set.range β) ⊆ Z := by
        intro z hz; simp only [eps]; rw [dif_pos hz]
        exact (Classical.choose_spec (hsub z hz)).2
      refine ⟨⋃ z ∈ Z, Metric.ball z (eps z),
        isOpen_iUnion (fun z => isOpen_iUnion (fun _ => Metric.isOpen_ball)), ?_⟩
      intro x hx
      constructor
      · intro hxZ
        exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxZ, mem_ball_self (hepspos x hxZ)⟩⟩
      · intro hxO
        obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hxO
        obtain ⟨hzZ, hxz⟩ := Set.mem_iUnion.mp hz
        exact hepssub z hzZ ⟨hxz, hx⟩
    have hZun : closure U ∩ (Metric.sphere c r \ Set.range β) ⊆ RAo ∪ RBo := by
      rw [hsquare]; exact Set.inter_subset_right
    -- dichotomy for each arc
    have hRAodich : RAo ⊆ closure U ∩ (Metric.sphere c r \ Set.range β) ∨
        RAo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β)) = ∅ := by
      by_cases hne : (RAo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β))).Nonempty
      · left
        exact preconnected_subset_of_clopen_sub hRAopre hRAo_diff hZopene hZclosed hne
      · right; exact Set.not_nonempty_iff_eq_empty.mp hne
    have hRBodich : RBo ⊆ closure U ∩ (Metric.sphere c r \ Set.range β) ∨
        RBo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β)) = ∅ := by
      by_cases hne : (RBo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β))).Nonempty
      · left
        exact preconnected_subset_of_clopen_sub hRBopre hRBo_diff hZopene hZclosed hne
      · right; exact Set.not_nonempty_iff_eq_empty.mp hne
    have hdisjA : ∀ s u : Set.Icc (0:ℝ) 1, β s = arcA u → s = 0 ∨ s = 1 := by
      intro s u hsu
      have hmem : β s ∈ Set.range β ∩ Metric.sphere c r := ⟨⟨s, rfl⟩, by rw [hsu]; exact harcAS u⟩
      rw [range_beta_inter_sphere β hβ h0 h1 hint] at hmem
      rcases (by simpa using hmem : β s = β 0 ∨ β s = β 1) with hh | hh
      · exact Or.inl (hβ hh)
      · exact Or.inr (hβ hh)
    have hdisjB : ∀ s u : Set.Icc (0:ℝ) 1, β s = arcB u → s = 0 ∨ s = 1 := by
      intro s u hsu
      have hmem : β s ∈ Set.range β ∩ Metric.sphere c r := ⟨⟨s, rfl⟩, by rw [hsu]; exact harcBS u⟩
      rw [range_beta_inter_sphere β hβ h0 h1 hint] at hmem
      rcases (by simpa using hmem : β s = β 0 ∨ β s = β 1) with hh | hh
      · exact Or.inl (hβ hh)
      · exact Or.inr (hβ hh)
    -- final case analysis
    intro t ht0 ht1
    by_cases hRA : RAo ⊆ closure U ∩ (Metric.sphere c r \ Set.range β)
    · have hZleA : closure U ∩ (Metric.sphere c r \ Set.range β) ⊆ RAo := by
        rcases hRBodich with hRB | hRB
        · exfalso
          have hSsub : Metric.sphere c r \ Set.range β
              ⊆ closure U ∩ (Metric.sphere c r \ Set.range β) := by
            intro z hz
            refine ⟨?_, hz⟩
            rw [hsquare] at hz
            rcases hz with hz | hz
            · exact (hRA hz).1
            · exact (hRB hz).1
          exact hZlt (Set.Subset.antisymm Set.inter_subset_right hSsub)
        · intro z hz
          rcases hZun hz with h | h
          · exact h
          · exact absurd ⟨h, hz⟩ (Set.eq_empty_iff_forall_notMem.mp hRB z)
      have hSsubA : closure U ∩ Metric.sphere c r ⊆ Set.range arcA := by
        calc closure U ∩ Metric.sphere c r
            ⊆ (closure U ∩ (Metric.sphere c r \ Set.range β)) ∪ {β 0, β 1} := by
              rintro z ⟨hzcl, hzS⟩
              by_cases hzA : z ∈ Set.range β
              · right
                have hz2 : z ∈ Set.range β ∩ Metric.sphere c r := ⟨hzA, hzS⟩
                rwa [range_beta_inter_sphere β hβ h0 h1 hint] at hz2
              · exact Or.inl ⟨hzcl, hzS, hzA⟩
          _ ⊆ RAo ∪ {β 0, β 1} := Set.union_subset (hZleA.trans Set.subset_union_left) Set.subset_union_right
          _ = Set.range arcA := hRAorange
      exact beta_mem_closure_of_arc_touch hr β hβ h0 h1 hint arcA harcAinj harcAS harcA0
        harcA1 hdisjA hUpre hUopen ⟨w, hwU⟩ hUsubW hUcl hSsubA t ht0 ht1
    · have hZleB : closure U ∩ (Metric.sphere c r \ Set.range β) ⊆ RBo := by
        have hRAodich' : RAo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β)) = ∅ := by
          by_cases hne : (RAo ∩ (closure U ∩ (Metric.sphere c r \ Set.range β))).Nonempty
          · exact absurd (preconnected_subset_of_clopen_sub hRAopre hRAo_diff hZopene hZclosed hne) hRA
          · exact Set.not_nonempty_iff_eq_empty.mp hne
        intro z hz
        rcases hZun hz with h | h
        · exact absurd ⟨h, hz⟩ (Set.eq_empty_iff_forall_notMem.mp hRAodich' z)
        · exact h
      have hSsubB : closure U ∩ Metric.sphere c r ⊆ Set.range arcB := by
        calc closure U ∩ Metric.sphere c r
            ⊆ (closure U ∩ (Metric.sphere c r \ Set.range β)) ∪ {β 0, β 1} := by
              rintro z ⟨hzcl, hzS⟩
              by_cases hzA : z ∈ Set.range β
              · right
                have hz2 : z ∈ Set.range β ∩ Metric.sphere c r := ⟨hzA, hzS⟩
                rwa [range_beta_inter_sphere β hβ h0 h1 hint] at hz2
              · exact Or.inl ⟨hzcl, hzS, hzA⟩
          _ ⊆ RBo ∪ {β 0, β 1} := Set.union_subset (hZleB.trans Set.subset_union_left) Set.subset_union_right
          _ = Set.range arcB := hRBorange
      exact beta_mem_closure_of_arc_touch hr β hβ h0 h1 hint arcB harcBinj harcBS harcB0
        harcB1 hdisjB hUpre hUopen ⟨w, hwU⟩ hUsubW hUcl hSsubB t ht0 ht1

end

end Commons.Topology.Jordan
