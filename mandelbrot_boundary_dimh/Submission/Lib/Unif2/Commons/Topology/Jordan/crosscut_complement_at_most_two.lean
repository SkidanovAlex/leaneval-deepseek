import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Jordan.arc_complement_no_bounded_component

open Set Metric
open scoped Topology

set_option linter.style.haveILetI false

namespace Commons.Topology.Jordan

noncomputable section

private def sph (c : ℂ) (r : ℝ) : C(Circle, ℂ) := ⟨fun u => c + r * (u : ℂ), by fun_prop⟩

private lemma sph_apply (c : ℂ) (r : ℝ) (u : Circle) : sph c r u = c + r * (u : ℂ) := rfl

private lemma sph_mem_sphere (c : ℂ) (r : ℝ) (hr : 0 < r) (u : Circle) :
    sph c r u ∈ Metric.sphere c r := by
  rw [Metric.mem_sphere, dist_eq_norm, sph_apply, add_sub_cancel_left, norm_mul,
    Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private lemma sph_range (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Set.range (sph c r) = Metric.sphere c r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩; exact sph_mem_sphere c r hr u
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    refine ⟨⟨(z - c) / (r : ℂ), ?_⟩, ?_⟩
    · refine mem_sphere_zero_iff_norm.mpr ?_
      rw [norm_div, Complex.norm_real, hz, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    · show c + r * ((z - c) / (r : ℂ)) = z
      rw [← mul_div_assoc, mul_div_cancel_left₀ (z - c) hr0]
      ring

private lemma sph_injective (c : ℂ) (r : ℝ) (hr : 0 < r) : Function.Injective (sph c r) := by
  intro u v huv
  rw [sph_apply, sph_apply] at huv
  have h : ((u:ℂ)) = (v:ℂ) := by
    have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact mul_left_cancel₀ hr0 (by simpa using huv)
  exact Subtype.ext h

private def Arc (c : ℂ) (r : ℝ) (u v : Circle) : Set ℂ :=
  sph c r '' ((Circle.path u v) '' Set.Ioo (0:unitInterval) 1)

private lemma arc_preconnected (c : ℂ) (r : ℝ) (u v : Circle) : IsPreconnected (Arc c r u v) := by
  have h1 : IsPreconnected (((Circle.path u v) '' Set.Ioo (0:unitInterval) 1 : Set Circle)) :=
    IsPreconnected.image isPreconnected_Ioo _ (by fun_prop)
  exact IsPreconnected.image h1 _ (by fun_prop)

private lemma arc_nonempty (c : ℂ) (r : ℝ) (u v : Circle) : (Arc c r u v).Nonempty := by
  have ht : (⟨(1/2:ℝ), by norm_num⟩ : unitInterval) ∈ Set.Ioo (0:unitInterval) 1 := by
    rw [Set.mem_Ioo, ← Subtype.coe_lt_coe, ← Subtype.coe_lt_coe]
    exact ⟨by norm_num, by norm_num⟩
  exact ⟨sph c r (Circle.path u v ⟨(1/2:ℝ), by norm_num⟩),
    ⟨Circle.path u v ⟨(1/2:ℝ), by norm_num⟩,
      ⟨⟨(1/2:ℝ), by norm_num⟩, ht, rfl⟩, rfl⟩⟩

private lemma circle_arcs_union {u v : Circle} (h : u ≠ v) :
    ((Circle.path u v) '' Set.Ioo (0:unitInterval) 1) ∪
      ((Circle.path v u) '' Set.Ioo (0:unitInterval) 1) = ({u, v} : Set Circle)ᶜ := by
  rw [← Circle.compl_range_path h.symm, ← Circle.compl_range_path h, ← Set.compl_inter]
  rw [Set.inter_comm (Set.range (v.path u)) (Set.range (u.path v)),
    Circle.range_path_inter_range_path h]

private lemma circle_arcs_disjoint {u v : Circle} (h : u ≠ v) :
    Disjoint ((Circle.path u v) '' Set.Ioo (0:unitInterval) 1)
      ((Circle.path v u) '' Set.Ioo (0:unitInterval) 1) :=
  (Circle.disjoint_path_image_Ioc h).mono (Set.image_mono Set.Ioo_subset_Ioc_self)
    (Set.image_mono Set.Ioo_subset_Ioc_self)

private lemma arc_union (c : ℂ) (r : ℝ) (hr : 0 < r) {u v : Circle} (huv : u ≠ v) :
    Arc c r u v ∪ Arc c r v u = Metric.sphere c r \ {sph c r u, sph c r v} := by
  have h1 : Arc c r u v ∪ Arc c r v u = sph c r '' (({u, v} : Set Circle)ᶜ) := by
    rw [Arc, Arc, ← Set.image_union, circle_arcs_union huv]
  rw [h1, Set.compl_eq_univ_sdiff, Set.image_sdiff (sph_injective c r hr), Set.image_univ,
    sph_range c r hr, Set.image_pair]

private lemma arc_disjoint (c : ℂ) (r : ℝ) (hr : 0 < r) {u v : Circle} (huv : u ≠ v) :
    Disjoint (Arc c r u v) (Arc c r v u) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hab : a = b := sph_injective c r hr hba.symm
  exact Set.disjoint_left.mp (circle_arcs_disjoint huv) ha (hab ▸ hb)

/-! ## Main theorem -/

theorem crosscut_complement_at_most_two (c : ℂ) {r : ℝ} (hr : 0 < r)
    (β : C(Set.Icc (0:ℝ) 1, ℂ)) (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hinterior : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r)
    {x y z : ℂ} (hx : x ∈ Metric.ball c r) (hy : y ∈ Metric.ball c r) (hz : z ∈ Metric.ball c r)
    (hxA : x ∉ Set.range β) (hyA : y ∉ Set.range β) (hzA : z ∉ Set.range β) :
    connectedComponentIn (Metric.ball c r \ Set.range β) x
        = connectedComponentIn (Metric.ball c r \ Set.range β) y ∨
      connectedComponentIn (Metric.ball c r \ Set.range β) y
        = connectedComponentIn (Metric.ball c r \ Set.range β) z ∨
      connectedComponentIn (Metric.ball c r \ Set.range β) x
        = connectedComponentIn (Metric.ball c r \ Set.range β) z := by
  classical
  haveI : CompactSpace (Set.Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  let D : Set ℂ := Metric.ball c r
  let S : Set ℂ := Metric.sphere c r
  let A : Set ℂ := Set.range β
  have hDdef : D = Metric.ball c r := rfl
  have hSdef : S = Metric.sphere c r := rfl
  have hAdef : A = Set.range β := rfl
  have hDopen : IsOpen D := Metric.isOpen_ball
  have hAclosed : IsClosed A := (isCompact_range β.continuous).isClosed
  have hAcompact : IsCompact A := isCompact_range β.continuous
  have hWopen : IsOpen (D \ A) := hDopen.sdiff hAclosed
  have hDcl : closure D = Metric.closedBall c r := closure_ball c hr.ne'
  -- A ∩ S = {β 0, β 1}
  have hpnq : β 0 ≠ β 1 := by
    intro h
    have : (0 : Set.Icc (0:ℝ) 1) = 1 := hβ h
    exact absurd (congrArg Subtype.val this) (by norm_num)
  have hinS : ∀ t : Set.Icc (0:ℝ) 1, β t ∈ Metric.sphere c r → β t = β 0 ∨ β t = β 1 := by
    intro t ht
    by_cases h0t : t = 0
    · exact Or.inl (by rw [h0t])
    · by_cases h1t : t = 1
      · exact Or.inr (by rw [h1t])
      · exfalso
        have hb := hinterior t (fun hh => h0t (hβ hh)) (fun hh => h1t (hβ hh))
        rw [Metric.mem_sphere, dist_eq_norm] at ht
        rw [Metric.mem_ball, dist_eq_norm] at hb
        linarith
  have hAinterS : Set.range β ∩ Metric.sphere c r = {β 0, β 1} := by
    ext w; constructor
    · rintro ⟨⟨t, rfl⟩, hwS⟩
      rcases hinS t hwS with hh | hh <;> simp [hh]
    · rintro (hh | hh)
      · exact ⟨⟨0, hh.symm⟩, hh.symm ▸ h0⟩
      · exact ⟨⟨1, hh.symm⟩, hh.symm ▸ h1⟩
  -- arcs
  obtain ⟨up, hup⟩ : ∃ u : Circle, sph c r u = β 0 := by
    have : β 0 ∈ Set.range (sph c r) := by rw [sph_range c r hr]; exact h0
    exact this
  obtain ⟨uq, huq⟩ : ∃ u : Circle, sph c r u = β 1 := by
    have : β 1 ∈ Set.range (sph c r) := by rw [sph_range c r hr]; exact h1
    exact this
  have hupq : up ≠ uq := by
    intro h
    exact hpnq (by rw [← hup, ← huq, h])
  set Arc1 : Set ℂ := Arc c r up uq with hArc1def
  set Arc2 : Set ℂ := Arc c r uq up with hArc2def
  have hArc1pc : IsPreconnected Arc1 := arc_preconnected c r up uq
  have hArc2pc : IsPreconnected Arc2 := arc_preconnected c r uq up
  have hArc1ne : Arc1.Nonempty := arc_nonempty c r up uq
  have hArc2ne : Arc2.Nonempty := arc_nonempty c r uq up
  have hArc_union : Arc1 ∪ Arc2 = Metric.sphere c r \ {β 0, β 1} := by
    rw [hArc1def, hArc2def, arc_union c r hr hupq, hup, huq]
  have hArc1sub : Arc1 ⊆ S \ {β 0, β 1} := by
    rw [hSdef, ← hArc_union]; exact Set.subset_union_left
  have hArc2sub : Arc2 ⊆ S \ {β 0, β 1} := by
    rw [hSdef, ← hArc_union]; exact Set.subset_union_right
  -- components
  let U : ℂ → Set ℂ := fun w => connectedComponentIn (D \ A) w
  let T : ℂ → Set ℂ := fun w => closure (U w) ∩ (S \ {β 0, β 1})
  have hUopen : ∀ w : ℂ, IsOpen (U w) := fun w => hWopen.connectedComponentIn
  have hcomp_open : ∀ w : ℂ, IsOpen ((D \ A) \ U w) := by
    intro w
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨hbW, hbU⟩ := hb
    have hVopen : IsOpen (U b) := hUopen b
    refine Filter.mem_of_superset (hVopen.mem_nhds (mem_connectedComponentIn hbW)) ?_
    intro d hd
    refine ⟨connectedComponentIn_subset _ _ hd, ?_⟩
    intro hdUw
    have e1 : U b = U d := connectedComponentIn_eq hd
    have e2 : U w = U d := connectedComponentIn_eq hdUw
    have hEq : U b = U w := e1.trans e2.symm
    exact hbU (hEq ▸ mem_connectedComponentIn hbW)
  have hfrontW : ∀ w : ℂ, frontier (U w) ∩ (D \ A) = ∅ := by
    intro w
    rw [Set.eq_empty_iff_forall_notMem]
    intro a ha
    obtain ⟨hfa, haW⟩ := ha
    rw [(hUopen w).frontier_eq] at hfa
    obtain ⟨hcl, hnotU⟩ := hfa
    by_cases haU : a ∈ U w
    · exact hnotU haU
    · have hopen := hcomp_open w
      have hmem : ((D \ A) \ U w) ∈ 𝓝 a := hopen.mem_nhds ⟨haW, haU⟩
      have hnotcl : a ∉ closure (U w) := by
        intro hcl'
        obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.mp hcl' ((D \ A) \ U w) hopen ⟨haW, haU⟩
        exact hx1.2 hx2
      exact hnotcl hcl
  have hz0_notA : ∀ z0 : ℂ, z0 ∈ S \ {β 0, β 1} → z0 ∉ A := by
    intro z0 hz0 hA
    have hmem : z0 ∈ Set.range β ∩ Metric.sphere c r := ⟨hA, hz0.1⟩
    rw [hAinterS] at hmem
    rcases (by simpa using hmem : z0 = β 0 ∨ z0 = β 1) with hh | hh
    · exact hz0.2 (by simp [hh])
    · exact hz0.2 (by simp [hh])
  have hsphere_open : ∀ z0 : ℂ, z0 ∉ A → ∃ ε > 0, Metric.ball z0 ε ⊆ Aᶜ := by
    intro z0 hz0
    rcases Metric.isOpen_iff.mp hAclosed.isOpen_compl z0 hz0 with ⟨ε, hε, hsub⟩
    exact ⟨ε, hε, hsub⟩
  -- nonemptiness of T
  have hT_nonempty : ∀ w : ℂ, w ∈ D \ A → (T w).Nonempty := by
    intro w hw
    by_contra hne
    have hdisj : closure (U w) ∩ (S \ {β 0, β 1}) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hfront : frontier (U w) ⊆ A := by
      intro a ha
      have hcl : a ∈ closure (U w) := frontier_subset_closure ha
      have hclsub : closure (U w) ⊆ D ∪ S := by
        have h1 : closure (U w) ⊆ closure D :=
          closure_mono ((connectedComponentIn_subset (D \ A) w).trans Set.sdiff_subset)
        rw [hDcl, ← ball_union_sphere] at h1
        intro z hz
        exact h1 hz
      rcases hclsub hcl with haD | haS
      · by_contra haA
        exact (Set.eq_empty_iff_forall_notMem.mp (hfrontW w)) a ⟨ha, haD, haA⟩
      · have hcases : a = β 0 ∨ a = β 1 := by
          by_contra hc
          rw [not_or] at hc
          exact (Set.eq_empty_iff_forall_notMem.mp hdisj) a
            ⟨hcl, haS, by simp [hc.1, hc.2]⟩
        rcases hcases with hh | hh
        · exact ⟨0, hh.symm⟩
        · exact ⟨1, hh.symm⟩
    refine arc_complement_no_bounded_component β hβ (hUopen w)
      ⟨w, mem_connectedComponentIn hw⟩ (Metric.isBounded_ball.subset ((connectedComponentIn_subset (D \ A) w).trans Set.sdiff_subset))
      isPreconnected_connectedComponentIn hfront ?_
    rw [Set.disjoint_left]
    intro a ha haA
    exact (connectedComponentIn_subset (D \ A) w ha).2 haA
  -- T is relatively clopen
  have hT_closed : ∀ w : ℂ, ∃ C : Set ℂ, IsClosed C ∧ T w = (S \ {β 0, β 1}) ∩ C :=
    fun w => ⟨closure (U w), isClosed_closure, (Set.inter_comm _ _).symm⟩
  have hT_open : ∀ w : ℂ, w ∈ D \ A →
      ∀ a ∈ T w, ∃ ε > 0, Metric.ball a ε ∩ (S \ {β 0, β 1}) ⊆ T w := by
    intro w hw a ha
    obtain ⟨hacl, haS'⟩ := ha
    have haA : a ∉ A := hz0_notA a haS'
    obtain ⟨ε, hεpos, hεsub⟩ := hsphere_open a haA
    refine ⟨ε, hεpos, ?_⟩
    have hHsub : Metric.ball a ε ∩ D ⊆ U w := by
      obtain ⟨z, hzU, hzdist⟩ := Metric.mem_closure_iff.mp hacl ε hεpos
      have hzH : z ∈ Metric.ball a ε ∩ D :=
        ⟨by rw [Metric.mem_ball, dist_comm]; exact hzdist,
          (connectedComponentIn_subset (D \ A) w hzU).1⟩
      have hHpre : IsPreconnected (Metric.ball a ε ∩ D) :=
        ((convex_ball a ε).inter (convex_ball c r)).isPreconnected
      have hHDA : Metric.ball a ε ∩ D ⊆ D \ A := by
        rintro y ⟨hy1, hy2⟩
        exact ⟨hy2, fun hyA => hεsub hy1 hyA⟩
      have hsub := hHpre.subset_connectedComponentIn hzH hHDA
      rwa [← connectedComponentIn_eq hzU] at hsub
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    refine ⟨?_, hu2⟩
    have huclD : u ∈ closure D := by rw [hDcl]; exact sphere_subset_closedBall hu2.1
    have h1 : u ∈ closure (D ∩ Metric.ball a ε) := (IsOpen.closure_inter (s := D)
      Metric.isOpen_ball) ⟨huclD, hu1⟩
    exact (closure_mono (by rw [Set.inter_comm]; exact hHsub)) h1
  -- peeling
  have peel : ∀ (Ar : Set ℂ), IsPreconnected Ar → Ar ⊆ S \ {β 0, β 1} → Ar.Nonempty →
      ∀ w : ℂ, w ∈ D \ A → (T w ∩ Ar).Nonempty → Ar ⊆ T w := by
    intro Ar hArpc hArsub hArne w hw hzAr
    obtain ⟨z0, hz0T, hz0Ar⟩ := hzAr
    obtain ⟨C, hCclosed, hCeq⟩ := hT_closed w
    by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨a0, ha0Ar, ha0T⟩ := hcon
    have hex : ∀ a, a ∈ T w → ∃ ε > 0, Metric.ball a ε ∩ (S \ {β 0, β 1}) ⊆ T w :=
      fun a ha => hT_open w hw a ha
    let ε0 : ℂ → ℝ := fun a => if ha : a ∈ T w then Classical.choose (hex a ha) else 1
    have hε0pos : ∀ a (ha : a ∈ T w), 0 < ε0 a := by
      intro a ha; simp only [ε0]; rw [dif_pos ha]; exact (Classical.choose_spec (hex a ha)).1
    have hε0sub : ∀ a (ha : a ∈ T w),
        Metric.ball a (ε0 a) ∩ (S \ {β 0, β 1}) ⊆ T w := by
      intro a ha; simp only [ε0]; rw [dif_pos ha]; exact (Classical.choose_spec (hex a ha)).2
    let u : Set ℂ := ⋃ a ∈ T w, Metric.ball a (ε0 a)
    let v : Set ℂ := Cᶜ
    have hu : IsOpen u := isOpen_iUnion (fun a => isOpen_iUnion (fun _ => Metric.isOpen_ball))
    have hv : IsOpen v := hCclosed.isOpen_compl
    have hsub : Ar ⊆ u ∪ v := by
      intro a ha
      have haS : a ∈ S \ {β 0, β 1} := hArsub ha
      by_cases haT : a ∈ T w
      · exact Or.inl (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haT, mem_ball_self (hε0pos a haT)⟩⟩)
      · refine Or.inr ?_
        intro haC
        exact haT (by rw [hCeq]; exact ⟨haS, haC⟩)
    have hne1 : (Ar ∩ u).Nonempty :=
      ⟨z0, hz0Ar, Set.mem_iUnion.mpr ⟨z0, Set.mem_iUnion.mpr ⟨hz0T, mem_ball_self (hε0pos z0 hz0T)⟩⟩⟩
    have hne2 : (Ar ∩ v).Nonempty := ⟨a0, ha0Ar, fun haC => ha0T (by rw [hCeq]; exact ⟨hArsub ha0Ar, haC⟩)⟩
    have hemp : Ar ∩ (u ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro a ⟨haAr, hau, hav⟩
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hau
      obtain ⟨hbT, hab⟩ := Set.mem_iUnion.mp hb
      have haS : a ∈ S \ {β 0, β 1} := hArsub haAr
      have haT : a ∈ T w := hε0sub b hbT ⟨hab, haS⟩
      have haC : a ∈ C := (hCeq ▸ haT).2
      exact hav haC
    have hne3 := hArpc u v hu hv hsub hne1 hne2
    rw [hemp] at hne3
    exact hne3.elim (fun x hx => hx)
  have hT_peel : ∀ w : ℂ, w ∈ D \ A → Arc1 ⊆ T w ∨ Arc2 ⊆ T w := by
    intro w hw
    obtain ⟨z0, hz0⟩ := hT_nonempty w hw
    have hz0mem : z0 ∈ Arc1 ∪ Arc2 := by rw [hArc_union]; exact hz0.2
    rcases hz0mem with hz1 | hz2
    · exact Or.inl (peel Arc1 hArc1pc hArc1sub hArc1ne w hw ⟨z0, hz0, hz1⟩)
    · exact Or.inr (peel Arc2 hArc2pc hArc2sub hArc2ne w hw ⟨z0, hz0, hz2⟩)
  -- same component from a common point on the circle
  have half_disk_same : ∀ (z0 a b : ℂ), z0 ∈ S \ {β 0, β 1} →
      a ∈ D \ A → b ∈ D \ A → z0 ∈ closure (U a) → z0 ∈ closure (U b) → U a = U b := by
    intro z0 a b hz0S ha hb hza hzb
    have hz0A : z0 ∉ A := hz0_notA z0 hz0S
    obtain ⟨ε, hεpos, hεsub⟩ := hsphere_open z0 hz0A
    let H : Set ℂ := Metric.ball z0 ε ∩ D
    have hHpre : IsPreconnected H := ((convex_ball z0 ε).inter (convex_ball c r)).isPreconnected
    have hHDA : H ⊆ D \ A := fun z hz => ⟨hz.2, fun hzA => hεsub hz.1 hzA⟩
    have hHa : H ⊆ U a := by
      obtain ⟨z, hzU, hzdist⟩ := Metric.mem_closure_iff.mp hza ε hεpos
      have hzH : z ∈ H := ⟨by rw [Metric.mem_ball, dist_comm]; exact hzdist,
        (connectedComponentIn_subset (D \ A) a hzU).1⟩
      have := hHpre.subset_connectedComponentIn hzH hHDA
      rwa [← connectedComponentIn_eq hzU] at this
    have hHb : H ⊆ U b := by
      obtain ⟨z, hzU, hzdist⟩ := Metric.mem_closure_iff.mp hzb ε hεpos
      have hzH : z ∈ H := ⟨by rw [Metric.mem_ball, dist_comm]; exact hzdist,
        (connectedComponentIn_subset (D \ A) b hzU).1⟩
      have := hHpre.subset_connectedComponentIn hzH hHDA
      rwa [← connectedComponentIn_eq hzU] at this
    have hHne : H.Nonempty := by
      obtain ⟨z, hzU, hzdist⟩ := Metric.mem_closure_iff.mp hza ε hεpos
      exact ⟨z, by rw [Metric.mem_ball, dist_comm]; exact hzdist,
        (connectedComponentIn_subset (D \ A) a hzU).1⟩
    obtain ⟨z, hzH⟩ := hHne
    exact (connectedComponentIn_eq (hHa hzH)).trans (connectedComponentIn_eq (hHb hzH)).symm
  have sameA : ∀ a b : ℂ, a ∈ D \ A → b ∈ D \ A → Arc1 ⊆ T a → Arc1 ⊆ T b → U a = U b := by
    intro a b ha hb hTa hTb
    obtain ⟨z0, hz0⟩ := hArc1ne
    exact half_disk_same z0 a b (hArc1sub hz0) ha hb (hTa hz0).1 (hTb hz0).1
  have sameB : ∀ a b : ℂ, a ∈ D \ A → b ∈ D \ A → Arc2 ⊆ T a → Arc2 ⊆ T b → U a = U b := by
    intro a b ha hb hTa hTb
    obtain ⟨z0, hz0⟩ := hArc2ne
    exact half_disk_same z0 a b (hArc2sub hz0) ha hb (hTa hz0).1 (hTb hz0).1
  have hxDA : x ∈ D \ A := ⟨hx, hxA⟩
  have hyDA : y ∈ D \ A := ⟨hy, hyA⟩
  have hzDA : z ∈ D \ A := ⟨hz, hzA⟩
  have hpx := hT_peel x hxDA
  have hpy := hT_peel y hyDA
  have hpz := hT_peel z hzDA
  by_cases hlex : Arc1 ⊆ T x
  · by_cases hley : Arc1 ⊆ T y
    · exact Or.inl (sameA x y hxDA hyDA hlex hley)
    · by_cases hlez : Arc1 ⊆ T z
      · exact Or.inr (Or.inr (sameA x z hxDA hzDA hlex hlez))
      · have hy2 : Arc2 ⊆ T y := hpy.resolve_left hley
        have hz2 : Arc2 ⊆ T z := hpz.resolve_left hlez
        exact Or.inr (Or.inl (sameB y z hyDA hzDA hy2 hz2))
  · by_cases hley : Arc1 ⊆ T y
    · by_cases hlez : Arc1 ⊆ T z
      · exact Or.inr (Or.inl (sameA y z hyDA hzDA hley hlez))
      · have hx2 : Arc2 ⊆ T x := hpx.resolve_left hlex
        have hz2 : Arc2 ⊆ T z := hpz.resolve_left hlez
        exact Or.inr (Or.inr (sameB x z hxDA hzDA hx2 hz2))
    · have hx2 : Arc2 ⊆ T x := hpx.resolve_left hlex
      have hy2 : Arc2 ⊆ T y := hpy.resolve_left hley
      exact Or.inl (sameB x y hxDA hyDA hx2 hy2)

end

end Commons.Topology.Jordan
