import Mathlib
import Submission.Work.Smooth.Schoenflies.All
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.disc_image_open_of_injective
import Submission.Work.Smooth.SphereJordan.exists_outerDisc
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.outerDiscAux
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.Jordan.All

namespace Work.Peel

open Set Metric

noncomputable section

/-- A continuous map into `ℂ ∪ {∞}` avoiding `∞` has a continuous lift to `ℂ`. -/
theorem exists_lift_coe {X : Type*} [TopologicalSpace X] (g : C(X, OnePoint ℂ))
    (hg : ∀ x, g x ≠ OnePoint.infty) :
    ∃ g' : C(X, ℂ), ∀ x, OnePoint.some (g' x) = g x := by
  refine ⟨⟨fun x => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg x)), ?_⟩, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    have hx : OnePoint.some (Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg x))) = g x :=
      Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hg x))
    show Filter.Tendsto (fun y : X => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg y)))
      (nhds x) (nhds (Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg x))))
    rw [← OnePoint.comap_coe_nhds (Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg x))),
      Filter.tendsto_comap_iff]
    have hcoe : (OnePoint.some ∘ fun y => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg y)))
        = ⇑g := funext (fun y => Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hg y)))
    rw [hcoe, hx]
    exact g.continuous.continuousAt
  · intro x
    exact Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hg x))

/-- The radial retraction of the unit disc onto the closed disc of radius `c` (`0 < c ≤ 1`),
as a continuous self-map of the disc. -/
theorem exists_radialScale (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ sc : C(Work.Smooth.Jordan.Disc, Work.Smooth.Jordan.Disc),
      (∀ z : Work.Smooth.Jordan.Disc, ‖(z:ℂ)‖ ≤ c → (sc z : ℂ) = (z:ℂ)/((c:ℝ):ℂ)) ∧
      (∀ z : Work.Smooth.Jordan.Disc, ‖(sc z : ℂ)‖ ≤ 1) := by
  have hcon : Continuous (fun z : Work.Smooth.Jordan.Disc =>
      if ‖(z:ℂ)‖ ≤ c then (z:ℂ)/((c:ℝ):ℂ) else (z:ℂ)/((‖(z:ℂ)‖:ℝ):ℂ)) := by
    apply continuous_if
    · intro z hz
      have hfr : frontier {x : Work.Smooth.Jordan.Disc | ‖(x:ℂ)‖ ≤ c} ⊆
          {x : Work.Smooth.Jordan.Disc | ‖(x:ℂ)‖ = c} :=
        frontier_le_subset_eq (continuous_norm.comp continuous_subtype_val) continuous_const
      have hzc : ‖(z:ℂ)‖ = c := hfr hz
      rw [hzc]
    · exact (continuous_subtype_val.div_const _).continuousOn
    · have hsub : closure {z : Work.Smooth.Jordan.Disc | ¬ ‖(z:ℂ)‖ ≤ c} ⊆
          {z : Work.Smooth.Jordan.Disc | c ≤ ‖(z:ℂ)‖} := by
        apply closure_minimal _ (isClosed_le continuous_const
          (continuous_norm.comp continuous_subtype_val))
        intro z hz
        exact le_of_lt (not_le.mp hz)
      refine ContinuousOn.div (f := fun z : Work.Smooth.Jordan.Disc => (z:ℂ))
        (g := fun z : Work.Smooth.Jordan.Disc => ((‖(z:ℂ)‖:ℝ):ℂ))
        continuous_subtype_val.continuousOn
        (Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)).continuousOn ?_
      intro z hz
      have h1 : c ≤ ‖(z:ℂ)‖ := hsub hz
      have h2 : (0:ℝ) < ‖(z:ℂ)‖ := lt_of_lt_of_le hc0 h1
      exact_mod_cast h2.ne'
  have hnorm : ∀ z : Work.Smooth.Jordan.Disc,
      (if ‖(z:ℂ)‖ ≤ c then (z:ℂ)/((c:ℝ):ℂ) else (z:ℂ)/((‖(z:ℂ)‖:ℝ):ℂ)) ∈
        Metric.closedBall (0:ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : ‖(z:ℂ)‖ ≤ c
    · rw [if_pos h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      have : ‖(z:ℂ)‖ ≤ 1 := le_trans h hc1
      rwa [div_le_one hc0]
    · have hlt : c < ‖(z:ℂ)‖ := not_le.mp h
      have hpos : (0:ℝ) < ‖(z:ℂ)‖ := lt_trans hc0 hlt
      rw [if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
        div_self (ne_of_gt hpos)]
  refine ⟨⟨fun z => ⟨_, hnorm z⟩, hcon.subtype_mk hnorm⟩, ?_, fun z => by
    have := hnorm z
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this⟩
  · intro z hz
    exact if_pos hz

/-- The enlarged disc produced from an injective disc map: the given proof. -/
theorem exists_enlarged_disc
    (f : C(Metric.closedBall (0 : ℂ) 1, ℂ)) (hf : Function.Injective f)
    (U : Set ℂ) (hU : IsOpen U)
    (hbd : ⇑f '' (Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1) ⊆ U)
    {η : ℝ} (hη : 0 < η) :
    ∃ G : C(Metric.closedBall (0 : ℂ) 1, ℂ), Function.Injective G ∧
      ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1) ⊆
        ⇑G '' (Subtype.val ⁻¹' Metric.ball (0 : ℂ) 1) ∧
      ⇑G '' (Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1) ⊆ U ∧
      (∀ z, z ∈ Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1 →
        G z ∉ ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0 : ℂ) 1)) ∧
      (∀ z, ∃ w, dist (G z) (⇑f w) < η) := by
  classical
  obtain ⟨e, w, he_inj, he_bd, hw_lt, hw_inf, he_range⟩ :=
    Work.Smooth.SphereJordan.exists_outerDisc f hf
  -- ## the boundary circle as a subset of the disc
  have hcp_mem : ∀ θ : ℝ, Work.Smooth.Jordan.circlePoint θ ∈
      Subtype.val ⁻¹' Metric.sphere (0 : ℂ) 1 := fun θ => by
    rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right, Work.Smooth.Jordan.circlePoint_coe,
      Complex.norm_exp_ofReal_mul_I]
  have hnorm_le_one : ∀ z : Work.Smooth.Jordan.Disc, ‖(z:ℂ)‖ ≤ 1 := fun z => by
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have himg_closed : ⇑f '' (Subtype.val ⁻¹' Metric.closedBall (0:ℂ) 1) = Set.range ⇑f := by
    rw [show Subtype.val ⁻¹' Metric.closedBall (0:ℂ) 1 = (Set.univ : Set Work.Smooth.Jordan.Disc)
      from Set.eq_univ_of_forall (fun z => by
        rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
        exact hnorm_le_one z),
      Set.image_univ]
  -- ## key characterisation of the outer disc
  have hKey : ∀ z : Work.Smooth.Jordan.Disc,
      e z ∈ OnePoint.some '' (Set.range ⇑f) ↔ ‖(z:ℂ)‖ = 1 := by
    intro z
    constructor
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨w', hw'⟩ := hy
      have hye : OnePoint.some y ∈ Set.range ⇑e := ⟨z, hyz.symm⟩
      rw [he_range] at hye
      rw [Set.mem_union, Set.mem_union] at hye
      rcases hye with (hinf | hxB) | hxC
      · exact absurd hinf (OnePoint.coe_ne_infty y)
      · obtain ⟨x, hx, hxy⟩ := hxB
        exact absurd (OnePoint.coe_injective hxy ▸ (hw' ▸ ⟨w', rfl⟩)) hx
      · obtain ⟨u, ⟨θ, hθ⟩, hueq⟩ := hxC
        have h1 : f (Work.Smooth.Jordan.circlePoint θ) = y := by
          rw [← OnePoint.coe_injective hueq, ← hθ]
        have h2 : w' = Work.Smooth.Jordan.circlePoint θ := hf (by rw [hw', h1])
        have h3 : z = Work.Smooth.Jordan.circlePoint θ := by
          apply he_inj
          rw [← hyz, ← h1, ← he_bd θ]
        rw [h3, Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    · intro hz
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
      exact ⟨f (Work.Smooth.Jordan.circlePoint θ), ⟨_, rfl⟩, by rw [← hθ, he_bd θ]⟩
  -- ## the boundary curve
  set Gam : Set ℂ := Set.range (fun θ : ℝ => f (Work.Smooth.Jordan.circlePoint θ)) with hGamdef
  have hGamU : Gam ⊆ U := by
    rw [hGamdef]
    rintro y ⟨θ, rfl⟩
    exact hbd ⟨Work.Smooth.Jordan.circlePoint θ, hcp_mem θ, rfl⟩
  have hSph : Subtype.val ⁻¹' Metric.sphere (0:ℂ) 1 =
      {z : Work.Smooth.Jordan.Disc | ‖(z:ℂ)‖ = 1} := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_sphere, dist_zero_right, Set.mem_setOf_eq]
  have hGamC : IsCompact Gam := by
    rw [hGamdef]
    have hset : Set.range (fun θ : ℝ => f (Work.Smooth.Jordan.circlePoint θ))
        = ⇑f '' (Subtype.val ⁻¹' Metric.sphere (0:ℂ) 1) := by
      ext y; constructor
      · rintro ⟨θ, rfl⟩
        exact ⟨Work.Smooth.Jordan.circlePoint θ, hcp_mem θ, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right] at hz
        obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
        exact ⟨θ, by change f (Work.Smooth.Jordan.circlePoint θ) = f z; rw [hθ]⟩
    rw [hset]
    have hc : IsCompact (Subtype.val ⁻¹' Metric.sphere (0:ℂ) 1 : Set Work.Smooth.Jordan.Disc) := by
      rw [hSph]
      exact (isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const).isCompact
    exact hc.image f.continuous
  obtain ⟨d0, hd0pos, hd0⟩ := hGamC.exists_cthickening_subset_open hU hGamU
  -- ## the collar parameters
  set ρ : ℝ := 1 - ‖(w:ℂ)‖ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  set ε0 : ℝ := min (ρ/2) (1/2) with hε0def
  have hε0pos : 0 < ε0 := lt_min (by linarith) (by norm_num)
  have hε0ρ : ε0 < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε0half : ε0 ≤ 1/2 := min_le_right _ _
  -- ## the fixed compact collar on which the outer disc avoids `∞`
  set KS : Set Work.Smooth.Jordan.Disc := {z | 1 - ε0 ≤ ‖(z:ℂ)‖} with hKSdef
  haveI : CompactSpace Work.Smooth.Jordan.Disc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  have hKScl : IsClosed KS :=
    isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)
  have hKSc : IsCompact KS := hKScl.isCompact
  haveI : CompactSpace ↥KS := isCompact_iff_compactSpace.mp hKSc
  have heK : ∀ z : ↥KS, e (z : Work.Smooth.Jordan.Disc) ≠ OnePoint.infty := by
    intro z hz
    have h1 : (z : Work.Smooth.Jordan.Disc) = w := he_inj (hz.trans hw_inf.symm)
    have h2 : (1:ℝ) - ε0 ≤ ‖(w:ℂ)‖ := by
      have h3 : (1:ℝ) - ε0 ≤ ‖((z : Work.Smooth.Jordan.Disc) : ℂ)‖ := z.2
      rwa [h1] at h3
    rw [show ‖(w:ℂ)‖ = 1 - ρ from by rw [hρdef]; ring] at h2
    linarith [hε0ρ]
  obtain ⟨φ, hφ⟩ := exists_lift_coe
    (⟨fun z : ↥KS => e (z : Work.Smooth.Jordan.Disc),
      e.continuous.comp continuous_subtype_val⟩ : C(↥KS, OnePoint ℂ)) heK
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply he_inj
    have h := congrArg OnePoint.some hab
    rwa [hφ a, hφ b] at h
  have huc : UniformContinuousOn (fun z : ↥KS => φ z) Set.univ :=
    isCompact_univ.uniformContinuousOn_of_continuous φ.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δu, hδupos, hδu⟩ := huc (min d0 η) (lt_min hd0pos hη)
  -- ## the size of the enlargement
  set ε : ℝ := min ε0 (δu/2) with hεdef
  have hεpos : 0 < ε := lt_min hε0pos (by linarith)
  have hεle0 : ε ≤ ε0 := min_le_left _ _
  have hεltu : ε < δu := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hεlt1 : ε < 1 := lt_of_le_of_lt hεle0 (lt_of_le_of_lt hε0half (by norm_num))
  have hε1pos : (0:ℝ) < 1 - ε := by linarith
  have hεne1 : ((1 - ε : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  -- ## the inner piece
  obtain ⟨sc, hsc, hscn⟩ := exists_radialScale (1 - ε) hε1pos (by linarith)
  let gInner : C(Work.Smooth.Jordan.Disc, ℂ) := f.comp sc
  have hsc_inj : ∀ z1 z2 : Work.Smooth.Jordan.Disc, ‖(z1:ℂ)‖ ≤ 1 - ε → ‖(z2:ℂ)‖ ≤ 1 - ε →
      sc z1 = sc z2 → z1 = z2 := by
    intro z1 z2 h1 h2 h
    have h3 : (z1:ℂ)/(((1-ε:ℝ):ℂ)) = (z2:ℂ)/(((1-ε:ℝ):ℂ)) := by
      rw [← hsc z1 h1, ← hsc z2 h2, h]
    have h4 : (z1:ℂ) = (z2:ℂ) := by
      have := congrArg (fun x : ℂ => x * ((1-ε:ℝ):ℂ)) h3
      rwa [div_mul_cancel₀ _ hεne1, div_mul_cancel₀ _ hεne1] at this
    exact Subtype.ext h4
  -- ## the outer piece
  set A : Set Work.Smooth.Jordan.Disc := {z | 1 - ε ≤ ‖(z:ℂ)‖} with hAdef
  have hvalA_cont : Continuous (fun a : ↥A => (((a : Work.Smooth.Jordan.Disc)) : ℂ)) :=
    (continuous_subtype_val : Continuous
        (Subtype.val : Work.Smooth.Jordan.Disc → ℂ)).comp
      (continuous_subtype_val : Continuous (Subtype.val : ↥A → Work.Smooth.Jordan.Disc))
  have hnormA_cont : Continuous (fun a : ↥A => ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖) :=
    continuous_norm.comp hvalA_cont
  have hnormA_ge : ∀ a : ↥A, (0:ℝ) < ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ :=
    fun a => lt_of_lt_of_le hε1pos a.2
  have hdenA_cont : Continuous
      (fun a : ↥A => ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hnormA_cont
  have hdenA_ne : ∀ a : ↥A,
      ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ) ≠ 0 :=
    fun a => by exact_mod_cast (ne_of_gt (hnormA_ge a))
  let v : ↥A → ℂ := fun a => (((2 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ)) : ℂ) *
      ((((a : Work.Smooth.Jordan.Disc)) : ℂ) / ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ))
  have hv1_cont : Continuous (fun a : ↥A =>
      (((2 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ)) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub hnormA_cont)
  have hv_cont : Continuous v := hv1_cont.mul (hvalA_cont.div hdenA_cont hdenA_ne)
  have hv_norm : ∀ a : ↥A,
      ‖v a‖ = 2 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ := by
    intro a
    have h2 : (0:ℝ) < 2 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ := by
      have := hnorm_le_one a.1; linarith
    simp only [v]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hnormA_ge a), div_self (ne_of_gt (hnormA_ge a)), mul_one]
  have hv_le1 : ∀ a : ↥A, ‖v a‖ ≤ 1 := by
    intro a
    have ha2 : 1 - ε ≤ ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ := a.2
    rw [hv_norm a]
    have := hnorm_le_one a.1
    linarith
  have hv_ge : ∀ a : ↥A, 1 - ε0 ≤ ‖v a‖ := by
    intro a
    have ha2 : 1 - ε ≤ ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ := a.2
    rw [hv_norm a]
    have := hnorm_le_one a.1
    linarith
  let ηc : ↥A → ↥KS := fun a => ⟨⟨v a, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv_le1 a⟩, hv_ge a⟩
  have hηc_fst : ∀ a : ↥A, ((ηc a : ↥KS) : ℂ) = v a := fun a => rfl
  have hηc_cont : Continuous ηc :=
    (hv_cont.subtype_mk (fun a => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hv_le1 a)).subtype_mk (fun a => hv_ge a)
  have hup_norm : ∀ a : ↥A,
      ‖((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
        ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ))‖ = 1 := by
    intro a
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hnormA_ge a),
      div_self (ne_of_gt (hnormA_ge a))]
  let up : ↥A → Work.Smooth.Jordan.Disc := fun a => ⟨
      ((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
        ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)), by
      rw [Metric.mem_closedBall, dist_zero_right]; rw [hup_norm a]⟩
  let upK : ↥A → ↥KS := fun a => ⟨up a, by
      show 1 - ε0 ≤ ‖((up a : Work.Smooth.Jordan.Disc) : ℂ)‖
      rw [show ((up a : Work.Smooth.Jordan.Disc) : ℂ) =
        ((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
          ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)) from rfl, hup_norm a]
      linarith⟩
  have hηc_up_near : ∀ a : ↥A, dist (ηc a) (upK a) ≤ ε := by
    intro a
    show dist (v a) ((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
      ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)) ≤ ε
    rw [dist_eq_norm]
    have h2 : v a - ((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
        ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ))
        = (((1 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ)) : ℂ) *
          ((((a : Work.Smooth.Jordan.Disc)) : ℂ) /
            ((‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)) := by
      simp only [v]; push_cast; ring
    rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [show (1:ℝ) - ε ≤
        ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖ from a.2] :
        (1 - ε - ‖(((a : Work.Smooth.Jordan.Disc)) : ℂ)‖) ≤ 0),
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hnormA_ge a),
      div_self (ne_of_gt (hnormA_ge a)), mul_one]
    have := hnorm_le_one a.1
    linarith
  have hup_val : ∀ a : ↥A, φ (upK a) = f (up a) := by
    intro a
    have h3 : ‖((up a : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 := hup_norm a
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (up a) h3
    have hval : OnePoint.some (φ (upK a)) = OnePoint.some (f (up a)) := by
      rw [hφ (upK a)]
      show e (up a) = OnePoint.some (f (up a))
      rw [← hθ, he_bd θ]
    exact OnePoint.coe_injective hval
  have hOut_notmem : ∀ a : ↥A, ‖v a‖ < 1 → φ (ηc a) ∉ Set.range ⇑f := by
    intro a ha hy
    obtain ⟨y, hy'⟩ := hy
    have h1 : e ((ηc a : ↥KS) : Work.Smooth.Jordan.Disc) = OnePoint.some (φ (ηc a)) :=
      (hφ (ηc a)).symm
    have h2 : e ((ηc a : ↥KS) : Work.Smooth.Jordan.Disc) ∈ OnePoint.some '' Set.range ⇑f :=
      ⟨f y, ⟨y, rfl⟩, by rw [hy', ← h1]⟩
    have h3 : ‖v a‖ = 1 := (hKey _).mp h2
    linarith
  -- ## gluing the two pieces
  let gOut : Work.Smooth.Jordan.Disc → ℂ := fun z =>
    if h : 1 - ε ≤ ‖(z:ℂ)‖ then φ (ηc ⟨z, h⟩) else 0
  have hgOut_eq : ∀ (z : Work.Smooth.Jordan.Disc) (h : 1 - ε ≤ ‖(z:ℂ)‖),
      gOut z = φ (ηc ⟨z, h⟩) := fun z h => dif_pos h
  have hOut_cont : ContinuousOn gOut A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : A.domRestrict gOut = fun a : ↥A => φ (ηc a) := by
      funext a
      simp only [Set.domRestrict]
      rw [hgOut_eq a a.2]
    rw [h1]
    exact φ.continuous.comp hηc_cont
  have hOut_inner : ∀ (z : Work.Smooth.Jordan.Disc) (h : 1 - ε ≤ ‖(z:ℂ)‖),
      ‖(z:ℂ)‖ = 1 - ε → gOut z = gInner z := by
    intro z h hzeq
    have hzle : ‖(z:ℂ)‖ ≤ 1 - ε := le_of_eq hzeq
    have hval : v ⟨z, h⟩ = (z:ℂ)/(((1-ε:ℝ):ℂ)) := by
      have hfac : (2 - ε - ‖(z:ℂ)‖ : ℝ) = 1 := by rw [hzeq]; ring
      have hvz : v ⟨z, h⟩ = (((2 - ε - ‖(z:ℂ)‖ : ℝ)) : ℂ) *
          ((z:ℂ)/(((‖(z:ℂ)‖:ℝ):ℂ))) := rfl
      rw [hvz, hfac, hzeq]
      simp
    have hφval : φ (ηc ⟨z, h⟩) = f (sc z) := by
      have h2 : ((ηc ⟨z, h⟩ : ↥KS) : Work.Smooth.Jordan.Disc) = sc z :=
        Subtype.ext (hval.trans (hsc z hzle).symm)
      have h3 : ‖((sc z : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 := by
        rw [hsc z hzle, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε1pos,
          div_eq_one_iff_eq (by linarith : (1 - ε : ℝ) ≠ 0)]
        exact hzeq
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (sc z) h3
      have hval2 : OnePoint.some (φ (ηc ⟨z, h⟩)) = OnePoint.some (f (sc z)) := by
        rw [hφ (ηc ⟨z, h⟩)]
        show e ((ηc ⟨z, h⟩ : ↥KS) : Work.Smooth.Jordan.Disc) = OnePoint.some (f (sc z))
        rw [h2, ← hθ, he_bd θ]
      exact OnePoint.coe_injective hval2
    rw [hgOut_eq z h, hφval]
    rfl
  let Gf : Work.Smooth.Jordan.Disc → ℂ := fun z =>
    if 1 - ε ≤ ‖(z:ℂ)‖ then gOut z else gInner z
  have hGf_cont : Continuous Gf := by
    have hfr : frontier {x : Work.Smooth.Jordan.Disc | 1 - ε ≤ ‖(x:ℂ)‖} ⊆
        {x : Work.Smooth.Jordan.Disc | 1 - ε = ‖(x:ℂ)‖} :=
      frontier_le_subset_eq continuous_const (continuous_norm.comp continuous_subtype_val)
    have hclA : closure {x : Work.Smooth.Jordan.Disc | 1 - ε ≤ ‖(x:ℂ)‖} = A :=
      IsClosed.closure_eq (isClosed_le continuous_const
        (continuous_norm.comp continuous_subtype_val))
    apply continuous_if
    · intro z hz
      exact hOut_inner z (le_of_eq (hfr hz)) (hfr hz).symm
    · rw [hclA]
      exact hOut_cont
    · exact gInner.continuous.continuousOn
  have hGf_outer : ∀ (z : Work.Smooth.Jordan.Disc) (h : 1 - ε ≤ ‖(z:ℂ)‖),
      Gf z = φ (ηc ⟨z, h⟩) := by
    intro z h
    simp only [Gf, if_pos h]
    exact hgOut_eq z h
  have hGf_inner : ∀ z : Work.Smooth.Jordan.Disc, ‖(z:ℂ)‖ ≤ 1 - ε → Gf z = f (sc z) := by
    intro z hz
    rcases lt_or_eq_of_le hz with hlt | heq
    · simp only [Gf, if_neg (not_le.mpr hlt)]
      rfl
    · simp only [Gf, if_pos (le_of_eq heq.symm)]
      exact hOut_inner z (le_of_eq heq.symm) heq
  have hGf_inner_range : ∀ z : Work.Smooth.Jordan.Disc, ‖(z:ℂ)‖ ≤ 1 - ε →
      Gf z ∈ Set.range ⇑f := fun z hz => by rw [hGf_inner z hz]; exact ⟨sc z, rfl⟩
  have hGf_outer_notmem : ∀ z : Work.Smooth.Jordan.Disc, 1 - ε < ‖(z:ℂ)‖ →
      Gf z ∉ Set.range ⇑f := by
    intro z hz hmem
    have hA : 1 - ε ≤ ‖(z:ℂ)‖ := le_of_lt hz
    rw [hGf_outer z hA] at hmem
    exact hOut_notmem ⟨z, hA⟩ (by rw [hv_norm]; linarith) hmem
  have hclose : ∀ a : ↥A, dist (Gf (a : Work.Smooth.Jordan.Disc)) (f (up a)) < min d0 η := by
    intro a
    have h1 : Gf (a : Work.Smooth.Jordan.Disc) = φ (ηc a) :=
      hGf_outer (a : Work.Smooth.Jordan.Disc) a.2
    rw [h1, ← hup_val a]
    exact hδu (ηc a) trivial (upK a) trivial (lt_of_le_of_lt (hηc_up_near a) hεltu)
  -- ## injectivity
  have hinj : Function.Injective Gf := by
    intro z1 z2 hz
    by_cases h1 : ‖(z1:ℂ)‖ ≤ 1 - ε
    · by_cases h2 : ‖(z2:ℂ)‖ ≤ 1 - ε
      · have hx1 : Gf z1 = f (sc z1) := hGf_inner z1 h1
        have hx2 : Gf z2 = f (sc z2) := hGf_inner z2 h2
        exact hsc_inj z1 z2 h1 h2 (hf (by rw [← hx1, ← hx2]; exact hz))
      · have h2' : 1 - ε < ‖(z2:ℂ)‖ := lt_of_not_ge h2
        exact absurd (by rw [← hz]; exact hGf_inner_range z1 h1) (hGf_outer_notmem z2 h2')
    · have h1' : 1 - ε < ‖(z1:ℂ)‖ := lt_of_not_ge h1
      by_cases h2 : ‖(z2:ℂ)‖ ≤ 1 - ε
      · exact absurd (by rw [hz]; exact hGf_inner_range z2 h2) (hGf_outer_notmem z1 h1')
      · have h2' : 1 - ε < ‖(z2:ℂ)‖ := lt_of_not_ge h2
        set a1 : ↥A := ⟨z1, le_of_lt h1'⟩ with ha1
        set a2 : ↥A := ⟨z2, le_of_lt h2'⟩ with ha2
        have hae : ηc a1 = ηc a2 := by
          apply hφinj
          rw [← hGf_outer z1 (le_of_lt h1'), ← hGf_outer z2 (le_of_lt h2')]
          exact hz
        have h5 : v a1 = v a2 := by
          have h5' := congrArg (fun x : ↥KS => ((x : Work.Smooth.Jordan.Disc) : ℂ)) hae
          rwa [hηc_fst a1, hηc_fst a2] at h5'
        have h6 : ‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖
            = ‖(((a2 : Work.Smooth.Jordan.Disc)) : ℂ)‖ := by
          have e1 := hv_norm a1
          have e2 := hv_norm a2
          have e3 : ‖v a1‖ = ‖v a2‖ := by rw [h5]
          linarith
        have h7 : (((a1 : Work.Smooth.Jordan.Disc)) : ℂ)
            = (((a2 : Work.Smooth.Jordan.Disc)) : ℂ) := by
          have hfac : (((2 - ε - ‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ)) : ℂ) ≠ 0 := by
            have := hnorm_le_one a1.1
            have hpos : (0:ℝ) < 2 - ε - ‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ := by linarith
            exact_mod_cast (ne_of_gt hpos)
          have h9 : (((a1 : Work.Smooth.Jordan.Disc)) : ℂ) /
                ((‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)
              = (((a2 : Work.Smooth.Jordan.Disc)) : ℂ) /
                ((‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ) := by
            have h := h5
            simp only [v] at h
            rw [← h6] at h
            exact mul_left_cancel₀ hfac h
          have hden : ((‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := hdenA_ne a1
          have h10 := congrArg (fun x : ℂ =>
            x * ((‖(((a1 : Work.Smooth.Jordan.Disc)) : ℂ)‖ : ℝ) : ℂ)) h9
          rwa [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at h10
        have hfin : ((a1 : Work.Smooth.Jordan.Disc)) = ((a2 : Work.Smooth.Jordan.Disc)) :=
          Subtype.ext h7
        exact hfin
  refine ⟨⟨Gf, hGf_cont⟩, hinj, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩
    have hx1 : ‖(x:ℂ)‖ ≤ 1 := hnorm_le_one x
    have hmem0 : ‖(((1 - ε : ℝ) : ℂ) * (x:ℂ))‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε1pos]
      nlinarith [hεpos, hε1pos, hx1, norm_nonneg (x:ℂ)]
    let z0 : Work.Smooth.Jordan.Disc := ⟨((1 - ε : ℝ) : ℂ) * (x:ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hmem0⟩
    have hz0le : ‖(z0:ℂ)‖ ≤ 1 - ε := by
      show ‖(((1 - ε : ℝ) : ℂ) * (x:ℂ))‖ ≤ 1 - ε
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε1pos]
      nlinarith [hεpos, hε1pos, hx1, norm_nonneg (x:ℂ)]
    refine ⟨z0, ?_, ?_⟩
    · rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hz0le (by linarith)
    · change Gf z0 = f x
      rw [hGf_inner z0 hz0le]
      congr 1
      apply Subtype.ext
      rw [hsc z0 hz0le]
      show ((((1 - ε : ℝ) : ℂ)) * (x:ℂ)) / ((1-ε:ℝ):ℂ) = (x:ℂ)
      rw [mul_div_cancel_left₀ _ hεne1]
  · rintro y ⟨z, hz, rfl⟩
    have hzn : ‖(z:ℂ)‖ = 1 := by
      rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right] at hz; exact hz
    have hA : 1 - ε ≤ ‖(z:ℂ)‖ := by rw [hzn]; linarith
    change Gf z ∈ U
    have hcl := hclose ⟨z, hA⟩
    have hgm : f (up ⟨z, hA⟩) ∈ Gam := by
      rw [hGamdef]
      have h3 : ‖((up ⟨z, hA⟩ : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 := hup_norm ⟨z, hA⟩
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (up ⟨z, hA⟩) h3
      exact ⟨θ, by change f (Work.Smooth.Jordan.circlePoint θ) = f (up ⟨z, hA⟩); rw [hθ]⟩
    refine hd0 (Metric.closedBall_subset_cthickening hgm d0 ?_)
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le hcl (min_le_left _ _))
  · intro z hz
    have hzn : ‖(z:ℂ)‖ = 1 := by
      rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right] at hz; exact hz
    have hA : 1 - ε ≤ ‖(z:ℂ)‖ := by rw [hzn]; linarith
    rw [himg_closed]
    change Gf z ∉ Set.range ⇑f
    rw [hGf_outer z hA]
    refine hOut_notmem ⟨z, hA⟩ ?_
    rw [hv_norm, hzn]
    linarith
  · intro z
    change ∃ w, dist (Gf z) (⇑f w) < η
    by_cases hz : 1 - ε ≤ ‖(z:ℂ)‖
    · exact ⟨up ⟨z, hz⟩, lt_of_lt_of_le (hclose ⟨z, hz⟩) (min_le_right _ _)⟩
    · have hz' : ‖(z:ℂ)‖ < 1 - ε := lt_of_not_ge hz
      exact ⟨sc z, by rw [hGf_inner z (le_of_lt hz'), dist_self]; exact hη⟩

end

end Work.Peel
