import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.Drive.N2.roundConfigPicture
import Submission.Work.Drive.N2.extremumCollapse
import Submission.Work.Drive.N2.exists_extremumProfile
import Submission.Work.Drive.N2.pictureOfConfig
import Submission.Work.Drive.N2.extremumLanding
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.N2C.extremumWindowCertAux
import Submission.Work.N2C.certWindowLevel

/-!
# The certified window at an extremum (compact `n = 2`)

This is lemma **D1** of the coherent-window architecture
(`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md` §4): at a critical point `p` whose two
Morse signs agree (a local extremum) there is a value window `(f p - 2η, f p + 2η)` carrying a good
drawing `W` which is *certified* at the two levels `f p ∓ 3η/2`, i.e. at each of those levels the
picture of `W` is isotopic through pictures of that level to a disjoint round configuration read
through a parametrisation of the level.

The drawing is the hybrid of `Work.N2C.Ext.extremumWindowExposed_picture`: the radial collapse of a
Morse chart on the model ball and the transport `A₀ ∘ foot` of a round picture of the anchor level
`f p + s·2η` outside it.  The certificates are then read off the two pieces: at each certificate level
every component of the level is either the small model circle around `p` (drawn round by the collapse)
or lies outside the model ball (drawn round by the anchor picture), and
`Work.N2C.isCertifiedAt_of_roundImage` turns that into the certificate.

The two analytic facts used are `Work.Drive.N2.extremumLanding` (the transport off the model ball
lands on the anchor level) and `Work.N2C.isCertifiedAt_of_roundImage`.
-/

namespace Work.N2C

open scoped Manifold ContDiff Topology
open Set

theorem exists_certifiedWindow_extremum {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) {p : M}
    (D : Work.Drive.N2.WindowDatum f p) (hext : D.s₁ D.j = D.s₂ D.j) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ →
      ∃ W : M → EuclideanSpace ℝ (Fin 3),
        Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η)) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) W ∧
        Work.Drive.N2C.IsCertifiedAt f (f p + 3 * η / 2) W := by
  classical

  have hfm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f := hf.1
  set s : ℝ := D.s₁ D.j with hsdef
  have hs : s = 1 ∨ s = -1 := (D.hsgn D.j).1
  have hs₂ : D.s₂ D.j = s := hext.symm
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  -- a ball in the chart target around the origin
  have h0tgt : (0 : EuclideanSpace ℝ (Fin 2)) ∈ (D.φ D.j).target := by
    have h1 := (D.φ D.j).map_source (D.hsrc D.j)
    rwa [D.hcen D.j] at h1
  obtain ⟨r, hrpos, hrsub⟩ :=
    Metric.mem_nhds_iff.mp ((D.φ D.j).open_target.mem_nhds h0tgt)
  refine ⟨min (min (D.ηd / 2) ((D.ρ D.j) ^ 2 / 8)) (r ^ 2 / 8), ?_, ?_⟩
  · exact lt_min (lt_min (div_pos D.hηd (by norm_num))
      (div_pos (pow_pos hρpos 2) (by norm_num)))
      (div_pos (pow_pos hrpos 2) (by norm_num))
  · intro η hηpos hηle
    set ηw : ℝ := 2 * η with hηwdef
    have hηw : 0 < ηw := by rw [hηwdef]; linarith
    have hη1a : η ≤ D.ηd / 2 :=
      le_trans hηle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hη1b : η ≤ (D.ρ D.j) ^ 2 / 8 :=
      le_trans hηle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hη1c : η ≤ r ^ 2 / 8 := le_trans hηle (min_le_right _ _)
    have hηw_ηd : ηw ≤ D.ηd := by rw [hηwdef]; linarith [D.hηd]
    have hρηw : 4 * ηw ≤ (D.ρ D.j) ^ 2 := by rw [hηwdef]; linarith
    have hηw_r : 2 * ηw < r ^ 2 := by rw [hηwdef]; linarith
    set c : ℝ := f p with hcdef
    set a : ℝ := c + s * ηw with hadef
    have hfc : f (D.x D.j) = c := by rw [D.hxj, hcdef]
    have hmodel : ∀ y ∈ (D.φ D.j).source,
        f y = c + s * ((D.φ D.j y) 0 ^ 2 + (D.φ D.j y) 1 ^ 2) := by
      intro y hy
      have h := D.hval D.j y hy
      rw [Work.Drive.N2.chartQ] at h
      rw [h, hfc, hext, hs₂]
      ring
    -- the anchor level is attained
    have hanc : ∃ y : M, f y = a := by
      obtain ⟨v₀, hv₀⟩ : ∃ v₀ : EuclideanSpace ℝ (Fin 2), v₀ ≠ 0 :=
        ⟨WithLp.toLp 2 (Pi.single (0 : Fin 2) (1 : ℝ)), by
          intro h
          have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
          simp [Pi.single_eq_same] at this⟩
      set v : EuclideanSpace ℝ (Fin 2) := (Real.sqrt (2 * ηw) / ‖v₀‖) • v₀ with hvdef
      have hvnorm : ‖v‖ = Real.sqrt (2 * ηw) := by
        rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        field_simp
      have hvmem : v ∈ (D.φ D.j).target := by
        have h1 : ‖v‖ < r := by
          rw [hvnorm]
          calc Real.sqrt (2 * ηw) < Real.sqrt (r ^ 2) :=
                Real.sqrt_lt_sqrt (by linarith) hηw_r
            _ = r := Real.sqrt_sq hrpos.le
        exact hrsub (by simpa [Metric.mem_ball, dist_eq_norm] using h1)
      have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • v ∈ (D.φ D.j).target := by
        intro t ht
        refine hrsub ?_
        simp only [Metric.mem_ball, dist_zero_right]
        calc ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          _ ≤ 1 * ‖v‖ := by exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ = ‖v‖ := one_mul _
          _ < r := by
            rw [hvnorm]
            calc Real.sqrt (2 * ηw) < Real.sqrt (r ^ 2) :=
                  Real.sqrt_lt_sqrt (by linarith) hηw_r
              _ = r := Real.sqrt_sq hrpos.le
      set γ : ℝ → M := fun t => (D.φ D.j).symm (t • v) with hγdef
      have hγsrc : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (D.φ D.j).source :=
        fun t ht => (D.φ D.j).symm.map_source (hseg t ht)
      have hφγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, D.φ D.j (γ t) = t • v :=
        fun t ht => (D.φ D.j).right_inv (hseg t ht)
      have hγval : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (γ t) = c + s * (t ^ 2 * ‖v‖ ^ 2) := by
        intro t ht
        have hv := D.hval D.j (γ t) (hγsrc t ht)
        have hq : Work.Drive.N2.chartQ (D.φ D.j) (D.s₁ D.j) (D.s₂ D.j) (γ t)
            = D.s₁ D.j * ((t • v) 0) ^ 2 + D.s₂ D.j * ((t • v) 1) ^ 2 := by
          rw [Work.Drive.N2.chartQ, hφγ t ht]
        rw [hv, hfc, hq, hext, hs₂]
        have h2 : ((t • v) 0) ^ 2 + ((t • v) 1) ^ 2 = ‖t • v‖ ^ 2 :=
          Work.Drive.N2.coord_sq_eq_norm_sq (t • v)
        rw [← mul_add, h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_pow]
      have hγ1 : f (γ 1) = c + s * (2 * ηw) := by
        rw [hγval 1 ⟨by norm_num, le_rfl⟩, hvnorm, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * ηw)]
        ring
      have hγ0 : f (γ 0) = c := by
        rw [hγval 0 ⟨le_rfl, by norm_num⟩]
        ring
      have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) :=
        ContinuousOn.comp ((D.hφ' D.j).continuousOn) (by fun_prop) hseg
      have hfoc : ContinuousOn f Set.univ := hfm.continuous.continuousOn
      have hcont : ContinuousOn (fun t : ℝ => f (γ t)) (Set.Icc (0 : ℝ) 1) :=
        hfoc.comp hγcont (fun t _ => Set.mem_univ t)
      rcases hs with h1 | h1
      · have hy1 : f (γ 0) ≤ a := by rw [hγ0, hadef, h1]; simp; linarith [hηw]
        have hy2 : a ≤ f (γ 1) := by rw [hγ1, hadef, h1]; simp; linarith [hηw]
        obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont ⟨hy1, hy2⟩
        exact ⟨γ t, hft⟩
      · have hy1 : f (γ 1) ≤ a := by rw [hγ1, hadef, h1]; simp; linarith [hηw]
        have hy2 : a ≤ f (γ 0) := by rw [hγ0, hadef, h1]; simp; linarith [hηw]
        obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hcont ⟨hy1, hy2⟩
        exact ⟨γ t, hft⟩
    -- the anchor level is regular
    have hreg_a : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x := by
      intro x hx hxc
      obtain ⟨i, hi⟩ := D.hcover x hxc
      have hne : i ≠ D.j := by
        intro hij
        have h1 : f x = c := by rw [← hi, hij, D.hxj, hcdef]
        rw [hx, hadef] at h1
        have h2 : s * ηw = 0 := by linarith
        rcases hs with h | h <;> rw [h] at h2 <;> linarith
      have h1 := D.hsep i D.j hne
      rw [hi, hfc] at h1
      have h2 : |f x - c| = ηw := by
        rw [hx, hadef]
        have h3 : c + s * ηw - c = s * ηw := by ring
        rw [h3]
        rcases hs with h | h <;> rw [h] <;> simp [abs_of_pos hηw]
      rw [h2] at h1
      linarith [h1, hηw_ηd, D.hηd]
    -- the anchor level curves
    obtain ⟨na, γa, hγasm, hγaper, hγainj, hγaval, hγaderiv, hγaker, hγacovU, hγadisj, hγaclosed,
      hγamod⟩ := Work.Drive.N2.exists_levelComponentCurves f hfm a hreg_a hanc
    have hγacov : ∀ y : M, f y = a → ∃ (i : Fin na) (t : ℝ), y = γa i t := by
      intro y hy
      have h : y ∈ ⋃ i, Set.range (γa i) := by rw [hγacovU]; exact hy
      simp only [Set.mem_iUnion, Set.mem_range] at h
      obtain ⟨i, t, ht⟩ := h
      exact ⟨i, t, ht.symm⟩
    -- the anchor round configuration and the picture of the anchor level
    let Da : Work.Drive.N2.RoundConfig na := Ext.stackConfig na
    have hDaD : Da.Disjoint := Ext.stackConfig_disjoint na
    obtain ⟨A, hAsm, hAcirc, hAinjL, hAimmL⟩ :=
      Work.Drive.N2.exists_picture_of_config (f := f) (b := a) γa hfm hreg_a hγasm hγaval
        hγaper hγainj hγacov hγadisj hγaker Da hDaD
    -- shift the picture so that all third coordinates are positive
    have hAcont : Continuous (fun y : M => -(A y) 2) :=
      (by fun_prop : Continuous fun v : E3 => -(v 2)).comp hAsm.continuous
    obtain ⟨C₀, hC₀⟩ := (isCompact_univ.image hAcont).bddAbove
    have hC₀' : ∀ y : M, -(A y) 2 ≤ C₀ := fun y =>
      hC₀ (Set.mem_image_of_mem (fun y : M => -(A y) 2) (Set.mem_univ y))
    set u₃ : E3 := WithLp.toLp 2 (Pi.single (2 : Fin 3) (1 : ℝ)) with hu₃def
    have hu₃ : u₃ 2 = 1 := by simp [hu₃def, Pi.single_eq_same]
    set A₀ : M → E3 := fun y => A y + (C₀ + 1) • u₃ with hA₀def
    have hA₀sm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A₀ y := fun y =>
      (hAsm y).add contMDiffAt_const
    have hA₀third : ∀ y : M, 0 < (A₀ y) 2 := by
      intro y
      have h : (A₀ y) 2 = (A y) 2 + (C₀ + 1) := by simp [hA₀def, hu₃]
      rw [h]; linarith [hC₀' y]
    have hA₀deriv : ∀ (x : M) (v : TangentSpace (𝓡 2) x),
        mfderiv (𝓡 2) (𝓡 3) A₀ x v = mfderiv (𝓡 2) (𝓡 3) A x v := by
      intro x v
      have hmd : MDifferentiableAt (𝓡 3) (𝓡 3)
          (fun z : E3 => z + (C₀ + 1) • u₃) (A x) :=
        (mdifferentiableAt_iff_differentiableAt).mpr (by fun_prop)
      have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3)
        (f := A) (g := fun z : E3 => z + (C₀ + 1) • u₃) (x := x)
        hmd (hAsm.mdifferentiableAt (by simp)) v
      have h1 : A₀ = (fun z : E3 => z + (C₀ + 1) • u₃) ∘ A := rfl
      rw [h1, hcomp]
      have h2 : mfderiv (𝓡 3) (𝓡 3) (fun z : E3 => z + (C₀ + 1) • u₃) (A x)
          = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) (A x)) := by
        rw [mfderiv_eq_fderiv, fderiv_add_const]
        exact fderiv_id
      rw [h2]
      rfl
    have hA₀inj : ∀ x y : M, f x = a → f y = a → A₀ x = A₀ y → x = y := by
      intro x y hx hy h
      have h1 : A x = A y := by rw [hA₀def] at h; exact add_right_cancel h
      obtain ⟨i, t, rfl⟩ := hγacov x hx
      obtain ⟨j, u, rfl⟩ := hγacov y hy
      exact hAinjL _ _ ⟨i, t, rfl⟩ ⟨j, u, rfl⟩ h1
    have hA₀imm : ∀ x : M, f x = a → ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) A₀ x v = 0 → v = 0 := by
      intro x hx v hv hv'
      obtain ⟨i, t, rfl⟩ := hγacov x hx
      exact hAimmL _ ⟨i, t, rfl⟩ v hv (by rw [← hA₀deriv]; exact hv')
    -- the configuration carried by the shifted picture
    let Da₀ : Work.Drive.N2.RoundConfig na :=
      { pos := fun i => Da.pos i + (C₀ + 1) • u₃, rad := Da.rad, hrad := Da.hrad,
        phase := Da.phase }
    have hDa₀circle : ∀ (i : Fin na) (x : ℝ),
        Da₀.circle i x = Da.circle i x + (C₀ + 1) • u₃ := by
      intro i x
      simp only [Da₀, Work.Drive.N2.RoundConfig.circle]
      abel
    have hDa₀D : Da₀.Disjoint := by
      intro i j hij s t h
      have h1 : Da.circle i s = Da.circle j t := by
        have h2 := hDa₀circle i s
        have h3 := hDa₀circle j t
        rw [h2, h3] at h
        exact add_right_cancel h
      exact hDaD i j hij s t h1
    have hAcirc₀ : ∀ (i : Fin na) (x : ℝ), A₀ (γa i x) = Da₀.circle i x := by
      intro i x
      show A (γa i x) + (C₀ + 1) • u₃ = Da₀.circle i x
      rw [hAcirc i x, hDa₀circle i x]
    -- the landing row of the transport
    have hb_ge_ρ : D.ρ D.j / 8 ≤ max (D.ρ D.j / 8) (2 * Real.sqrt ηw) := le_max_left _ _
    have hland : ∀ x : M,
        x ∉ Work.Drive.N2.modelBall (D.φ D.j) (max (D.ρ D.j / 8) (2 * Real.sqrt ηw)) →
        f x ∈ Set.Ioo (c - ηw) (c + ηw) →
        f (Work.Drive.N2.footMap D.Φ f a x) = a := by
      intro x hxD hx
      have hx8 : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j / 8) :=
        fun h => hxD ⟨h.1, lt_of_lt_of_le h.2 hb_ge_ρ⟩
      have h := Work.Drive.N2.extremumLanding (f := f) D hext hηw hηw_ηd hx8 hx
      simpa [Work.Drive.N2.footMap, hadef, hsdef] using h
    -- the hybrid drawing
    obtain ⟨b, μ, hb, hμsm, hμpos, hμone, hμinv, hGD⟩ :=
      Ext.extremumWindowExposed_picture (f := f) (p := p) D hfm hext hηw hηw_ηd hρηw
        hA₀sm hA₀inj hA₀imm hA₀third hland
    have hb_ge : D.ρ D.j / 8 ≤ b := by rw [hb]; exact le_max_left _ _
    have hb_pos : 0 < b := by rw [hb]; positivity
    have hb_le_ρ : b ≤ D.ρ D.j := by
      rw [hb]
      refine max_le (by linarith [hρpos]) ?_
      have h5 : ηw ≤ (D.ρ D.j / 2) ^ 2 := by nlinarith
      have h6 : Real.sqrt ηw ≤ D.ρ D.j / 2 := (Real.sqrt_le_iff).mpr ⟨by linarith, h5⟩
      linarith
    set foot : M → M := Work.Drive.N2.footMap D.Φ f a with hfootdef
    obtain ⟨hfoot_sm, -, -⟩ :=
      Work.Drive.N2.footMap_rows_noLaw (M := M) (f := f) hfm (D.hΦsm) (D.hΦ0) (D.hΦcomp) a
    have hfootsm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot y :=
      fun y => hfoot_sm.contMDiffAt
    set W : M → E3 := Ext.hybridW (D.φ D.j) μ b A₀ foot with hWdef
    -- the certificates
    have hcert : ∀ u : ℝ, u ≠ c → |u - c| < ηw → Work.Drive.N2C.IsCertifiedAt f u W := by
      intro u hu_ne hu
      have hu_band : u ∈ Set.Ioo (c - ηw) (c + ηw) := by
        rw [Set.mem_Ioo]
        have h := abs_lt.mp hu
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      have hreg_u : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x := by
        intro x hx hxc
        obtain ⟨i, hi⟩ := D.hcover x hxc
        have hne : i ≠ D.j := by
          intro hij
          have h1 : f x = c := by rw [← hi, hij, D.hxj, hcdef]
          rw [hx] at h1
          exact hu_ne h1
        have h1 := D.hsep i D.j hne
        rw [hi, hfc] at h1
        have h2 : |f x - c| < ηw := by rw [hx]; exact hu
        linarith [h1, hηw_ηd, D.hηd]
      have hDmclosed : IsClosed (Work.Drive.N2.modelBall (D.φ D.j) b ∩ {x : M | f x = u}) := by
        rw [hb]
        refine Ext.isClosed_modelBall_inter_level (f := f) (φ := D.φ D.j) (c := c) (s := s)
          (b := max (D.ρ D.j / 8) (2 * Real.sqrt ηw)) (u := u) hs (by positivity) hmodel
          (fun x => hfm.contMDiffAt) (D.hCclosed D.j)
          (fun y hy => (D.hCcl D.j).2 (subset_closure hy))
          (fun y hy => D.hCop D.j ⟨hy.1, lt_of_lt_of_le hy.2
            (by rw [← hb]; exact hb_le_ρ)⟩) ?_
        have hA' : |u - c| < 4 * ηw := by linarith
        have hB : (2 * Real.sqrt ηw) ^ 2 = 4 * ηw := by
          rw [mul_pow, Real.sq_sqrt hηw.le]; ring
        have hC : 4 * ηw ≤ max (D.ρ D.j / 8) (2 * Real.sqrt ηw) ^ 2 := by
          rw [← hB]
          exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2
        linarith
      have hWrows : (∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y) ∧
          (∀ x y : M, f x = u → f y = u → W x = W y → x = y) ∧
          (∀ x : M, f x = u → ∀ v : TangentSpace (𝓡 2) x,
            mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) W x v = 0 → v = 0) := by
        have hmem : u ∈ Set.Ioo (f p - ηw) (f p + ηw) := by
          rw [← hcdef]; exact hu_band
        exact ⟨fun y hy => hGD.1 y (by rw [hy]; exact hmem),
          fun x y hx hy hxy => hGD.2.2 x y (by rw [hx]; exact hmem) (by rw [hy]; exact hmem)
            (hx.trans hy.symm) hxy,
          fun x hx v hv hv' => hGD.2.1 x (by rw [hx]; exact hmem) v hv hv'⟩
      have hland' : ∀ x : M, x ∉ Work.Drive.N2.modelBall (D.φ D.j) b →
          f x = u → f (foot x) = a := by
        intro x hx hxu
        refine hland x ?_ ?_
        · rw [hb] at hx; exact hx
        · rw [hxu]; exact hu_band
      exact Ext.isCertifiedAt_of_hybrid (f := f) hfm (u := u) (a := a) (c := c) (s := s)
        (b := b) hu_ne hs hmodel (Ext.isOpen_modelBall' _ _) hDmclosed hμpos hA₀sm hfootsm
        (fun y _ => rfl) hγacov (Da := Da₀) hAcirc₀ hDa₀D hland' hreg_u hWrows.1 hWrows.2.1
        hWrows.2.2
    refine ⟨W, ?_, hcert (c - 3 * η / 2) ?_ ?_, hcert (c + 3 * η / 2) ?_ ?_⟩
    · have hband : Set.Ioo (f p - 2 * η) (f p + 2 * η) = Set.Ioo (f p - ηw) (f p + ηw) := by
        rw [hηwdef]
      rw [hband, hWdef]
      exact hGD
    · rw [hcdef]; intro h; linarith
    · rw [hcdef, abs_lt]; constructor <;> rw [hηwdef] <;> linarith
    · rw [hcdef]; intro h; linarith
    · rw [hcdef, abs_lt]; constructor <;> rw [hηwdef] <;> linarith

end Work.N2C
