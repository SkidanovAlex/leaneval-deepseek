
import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulusLP_local
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.branchOfUnitGreen
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.coveringAux
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.isCoveringMap_branchProj
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.conjBridgeMap
import Submission.Lib.Unif2.Work.Modulus.greenPeriodHom_two_pi_zmultiples

/-!
# The branch bundle and the period homomorphism, without decay

Port of the covering-theoretic half of `Work.Modulus` to the decay-free hypotheses (harmonicity off
the pole, logarithmic pole bound).  Every statement is the corresponding statement of
`Work.Modulus` with `(hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)` replaced by
`(hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))` and
`(hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option warn.classDefReducibility false

noncomputable section

open Filter Set
open Classical

namespace Work.ModulusLP

open Work.Modulus Work.Modulus.BranchCovering Work.Modulus.BranchCovering.Aux

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The period homomorphism of the conjugate -/

/-- The Green function restricted to the punctured surface is harmonic (decay-free form). -/
theorem greenPunctured_harmonic {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) :
    Submission.HarmonicOnX (greenPunctured z₀ E) Set.univ :=
  puncturedHarmonic (X := X) (z₀ := z₀) (E := E) hEharm

/-- The first projection of the conjugate étale space of `E` over the punctured surface is a
covering map (decay-free form). -/
theorem green_isCoveringMap {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) :
    @IsCoveringMap ((puncturedOpens z₀) × ℝ) (puncturedOpens z₀)
      (greenConjTopology z₀ E) inferInstance Prod.fst :=
  @Submission.isCoveringMap_fst_conjTopology (puncturedOpens z₀) _ _ _
    (greenPunctured z₀ E) (greenPunctured_harmonic hEharm)

/-- **The period homomorphism of the conjugate** (decay-free form). -/
noncomputable def greenPeriodHom {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) (u₀ : puncturedOpens z₀) :
    Additive (FundamentalGroup (puncturedOpens z₀) u₀) →+ ℝ :=
  Submission.conjPeriodHom (X := puncturedOpens z₀) (htop := greenConjTopology z₀ E) u₀
    (Submission.conjFiberPt u₀ 0) (green_isCoveringMap hEharm)
    (fun c => green_continuous_conjShift (z₀ := z₀) (E := E) c)

theorem greenPeriodHom_apply {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) (u₀ : puncturedOpens z₀)
    (γ : FundamentalGroup (puncturedOpens z₀) u₀) :
    greenPeriodHom hEharm u₀ (Additive.ofMul γ) =
      Submission.conjPeriod (X := puncturedOpens z₀) (htop := greenConjTopology z₀ E) u₀
        (Submission.conjFiberPt u₀ 0) (green_isCoveringMap hEharm) γ := rfl

/-! ## The model branches of the modulus -/

/-- **A local branch of the modulus at a point different from the pole** (decay-free form). -/
theorem exists_isModulusBranch_of_ne_of_unitGreen {z₀ x : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) (hx : x ≠ z₀) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds x ∧ Φ x ≠ 0 := by
  have hharm : Submission.HarmonicOnXAt E x := hEharm x ⟨mem_univ x, hx⟩
  obtain ⟨U, Φ, hUopen, hxU, hΦhol, hΦne, hΦnorm⟩ :=
    Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt (X := X) hharm
  exact ⟨U, Φ, ⟨hUopen, hΦhol, fun y hy _ => hΦne y hy, fun y hy _ => hΦnorm y hy⟩,
    hUopen.mem_nhds hxU, hΦne x hxU⟩

/-- **A model branch of the modulus at the pole** (decay-free form). -/
theorem exists_isModulusBranch_at_pole_of_unitGreen {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    ∃ (U : Set X) (Φ : X → ℂ), Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ nhds z₀ ∧
      Submission.HasLogPoleAt z₀ Φ := by
  obtain ⟨ρ, Φ, hρ, hhol, hp, hmod⟩ :=
    localHolomorphicModulus_of_unitGreen (z₀ := z₀) (E := E) hEharm hpole
  refine ⟨Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, Φ, ?_, ?_, hp⟩
  · refine ⟨Submission.chartBall_isOpen _ _ _, hhol, ?_, hmod⟩
    intro x hx hxne hzero
    have h := hmod x hx hxne
    rw [hzero, norm_zero] at h
    exact (Real.exp_ne_zero _) h.symm
  · refine (Submission.chartBall_isOpen _ _ _).mem_nhds ?_
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ z₀, Metric.mem_ball_self hρ⟩

/-- **A model branch on a chart ball around the pole** (decay-free form). -/
theorem exists_isModulusBranch_chartBall_at_pole {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  obtain ⟨U, Φ, hbr, hU, hp⟩ :=
    exists_isModulusBranch_at_pole_of_unitGreen (z₀ := z₀) hEharm hpole
  obtain ⟨ρ, hρ, hρsub⟩ := Aux.exists_chartBall_subset_of_mem_nhds hU
  refine ⟨ρ, Φ, hρ, hbr.mono (Submission.chartBall_isOpen _ _ _) hρsub, ?_⟩
  intro y hy
  by_cases hy0 : y = z₀
  · right
    subst hy0
    exact Submission.phi_deriv_ne_zero_of_logPole hp
  · exact Or.inl (hbr.ne_zero y (hρsub hy) hy0)

/-- **A model branch on a chart ball around a point different from the pole** (decay-free form). -/
theorem exists_isModulusBranch_chartBall_off_pole {z₀ x : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) (hxne : x ≠ z₀) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  obtain ⟨U, Φ, hbr, hU, -⟩ :=
    exists_isModulusBranch_of_ne_of_unitGreen (z₀ := z₀) hEharm hxne
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Aux.exists_chartBall_subset_of_mem_nhds hU
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Aux.exists_chartBall_avoiding (x := x) (z₀ := z₀) hxne
  refine ⟨min ρ₁ ρ₂, Φ, lt_min hρ₁ hρ₂, ?_, ?_⟩
  · refine hbr.mono (Submission.chartBall_isOpen _ _ _) ?_
    intro y hy
    exact hρ₁sub (Aux.chartBall_subset_of_le (min_le_left _ _) hy)
  · intro y hy
    exact Or.inl (hbr.ne_zero y
      (hρ₁sub (Aux.chartBall_subset_of_le (min_le_left _ _) hy))
      (hρ₂sub y (Aux.chartBall_subset_of_le (min_le_right _ _) hy)))

/-- **A model branch on a chart ball around any point** (decay-free form). -/
theorem exists_isModulusBranch_chartBall {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) (x : X) :
    ∃ (ρ : ℝ) (Φ : X → ℂ), 0 < ρ ∧
      Work.SC.IsModulusBranch z₀ E (Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ) Φ ∧
      (∀ y ∈ Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ,
        Φ y ≠ 0 ∨ Work.SC.chartDeriv Φ y ≠ 0) := by
  rcases eq_or_ne x z₀ with rfl | hxne
  · exact exists_isModulusBranch_chartBall_at_pole hEharm hpole
  · exact exists_isModulusBranch_chartBall_off_pole hEharm hxne

/-- The projection of the modulus bundle is a covering map (decay-free form). -/
theorem isCoveringMap_branchProj {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E) :
    @IsCoveringMap (Work.SC.ModulusBundle z₀ E) X (Work.SC.modulusBundleTopology z₀ E) _
      (Work.SC.branchProj z₀ E) := by
  classical
  letI : TopologicalSpace (X × ℂ × ℂ) := Work.SC.branchTopology z₀ E
  intro x
  obtain ⟨ρ, Φ₀, hρ, hbr, hnd⟩ := exists_isModulusBranch_chartBall hEharm hpole x
  let B : Set X := Submission.chartBall (chartAt ℂ x) ((chartAt ℂ x) x) ρ
  have hBopen : IsOpen B := Submission.chartBall_isOpen (chartAt ℂ x) ((chartAt ℂ x) x) ρ
  have hxmem : x ∈ B := ⟨mem_chart_source ℂ x, Metric.mem_ball_self hρ⟩
  have hbrB : Work.SC.IsModulusBranch z₀ E B Φ₀ := hbr
  have hndB : ∀ y ∈ B, Φ₀ y ≠ 0 ∨ Work.SC.chartDeriv Φ₀ y ≠ 0 := hnd
  have hdisc : DiscreteTopology ↥(Work.SC.branchProj z₀ E ⁻¹' {x}) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro p
    obtain ⟨V, Ψ, hbrΨ, hyV, hval, hder⟩ := (p : Work.SC.ModulusBundle z₀ E).2
    have hset : ({p} : Set ↥(Work.SC.branchProj z₀ E ⁻¹' {x})) =
        (Subtype.val : ↥(Work.SC.branchProj z₀ E ⁻¹' {x}) → Work.SC.ModulusBundle z₀ E) ⁻¹'
          ((Subtype.val : Work.SC.ModulusBundle z₀ E → X × ℂ × ℂ) ⁻¹'
            Work.SC.branchGraph V Ψ) := by
      ext q
      constructor
      · intro hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨hyV, hval, hder⟩
      · intro hq
        rw [Set.mem_singleton_iff]
        have hqmem : (q : Work.SC.ModulusBundle z₀ E).1.1 = x := Set.mem_singleton_iff.mp q.2
        have hpmem : (p : Work.SC.ModulusBundle z₀ E).1.1 = x := Set.mem_singleton_iff.mp p.2
        apply Subtype.ext
        apply Subtype.ext
        refine Prod.ext (hqmem.trans hpmem.symm) (Prod.ext ?_ ?_)
        · rw [hq.2.1, hval, hqmem, hpmem]
        · rw [hq.2.2, hder, hqmem, hpmem]
    rw [hset]
    exact ((TopologicalSpace.isOpen_generateFrom_of_mem (g := Work.SC.branchFamily z₀ E)
      ⟨V, Ψ, hbrΨ, rfl⟩).preimage continuous_subtype_val).preimage continuous_subtype_val
  have hπcont : Continuous (Work.SC.branchProj z₀ E) := by
    rw [continuous_def]
    intro W hW
    rw [isOpen_iff_mem_nhds]
    intro p hp
    rw [show 𝓝 p = Filter.comap (Subtype.val : Work.SC.ModulusBundle z₀ E → X × ℂ × ℂ)
        (𝓝 ((p : Work.SC.ModulusBundle z₀ E) : X × ℂ × ℂ)) from nhds_induced _ _]
    rw [Filter.mem_comap]
    obtain ⟨V, Ψ, hbrΨ, hyV, hval, hder⟩ := (p : Work.SC.ModulusBundle z₀ E).2
    refine ⟨Work.SC.branchGraph (V ∩ W) Ψ, ?_, ?_⟩
    · exact (TopologicalSpace.isOpen_generateFrom_of_mem (g := Work.SC.branchFamily z₀ E)
        ⟨V ∩ W, Ψ, hbrΨ.mono (hbrΨ.1.inter hW) inter_subset_left, rfl⟩).mem_nhds
        ⟨⟨hyV, hp⟩, hval, hder⟩
    · intro q hq
      exact hq.1.2
  let K : ↥B × Aux.DiscCircle → ↥(Work.SC.branchProj z₀ E ⁻¹' B) := fun q =>
    ⟨⟨Aux.canonPt Φ₀ q.1.1 q.2.val, Aux.canonPt_mem hbrB q.1.2 q.2.norm_val⟩, q.1.2⟩
  let H : ↥(Work.SC.branchProj z₀ E ⁻¹' B) → ↥B × Aux.DiscCircle := fun p =>
    (⟨p.1.1.1, p.2⟩, ⟨Aux.pointLabel Φ₀ p.1, Aux.norm_pointLabel hbrB hndB p.2⟩)
  have hleft : Function.LeftInverse K H := by
    intro p
    have h := Aux.canonPt_eq_pointLabel hbrB hndB (p := p.1) p.2
    apply Subtype.ext
    apply Subtype.ext
    show Aux.canonPt Φ₀ p.1.1.1 (Aux.pointLabel Φ₀ p.1) = p.1.1
    exact h.symm
  have hright : Function.RightInverse K H := by
    rintro ⟨y, c⟩
    refine Prod.ext ?_ ?_
    · exact Subtype.ext rfl
    · refine Aux.DiscCircle.ext_iff ?_
      show Aux.pointLabel Φ₀ (⟨Aux.canonPt Φ₀ y.1 c.val,
        Aux.canonPt_mem hbrB y.2 c.norm_val⟩ : Work.SC.ModulusBundle z₀ E) = c.val
      exact Aux.pointLabel_canonPt hbrB y.2 (hndB y.1 y.2) c.norm_val
  have hHcont : Continuous H := by
    refine Continuous.prodMk ?_ ?_
    · exact (hπcont.comp continuous_subtype_val).subtype_mk (fun p => p.2)
    · have hlc : IsLocallyConstant (fun p : ↥(Work.SC.branchProj z₀ E ⁻¹' B) =>
          (⟨Aux.pointLabel Φ₀ p.1, Aux.norm_pointLabel hbrB hndB p.2⟩ : Aux.DiscCircle)) := by
        intro s
        rw [isOpen_iff_mem_nhds]
        intro p hp
        have hnbd : (Subtype.val ⁻¹' Aux.sheet (z₀ := z₀) (E := E) Φ₀ B
            (Aux.pointLabel Φ₀ p.1)) ∈ 𝓝 p :=
          ((Aux.sheet_isOpen hbrB (Aux.norm_pointLabel hbrB hndB p.2)).preimage
            continuous_subtype_val).mem_nhds (Aux.mem_sheet_pointLabel hbrB hndB p.2)
        refine Filter.mem_of_superset hnbd ?_
        intro q hq
        have hq' : (⟨Aux.pointLabel Φ₀ q.1, Aux.norm_pointLabel hbrB hndB q.2⟩ : Aux.DiscCircle) =
            ⟨Aux.pointLabel Φ₀ p.1, Aux.norm_pointLabel hbrB hndB p.2⟩ :=
          Aux.DiscCircle.ext_iff (Aux.pointLabel_eq_of_mem_sheet hbrB hndB hq)
        rw [Set.mem_preimage] at hp
        rw [Set.mem_preimage, hq']
        exact hp
      exact hlc.continuous
  have hKcont : Continuous K := by
    refine Aux.continuous_prod_of_forall_snd (f := fun (y : ↥B) (c : Aux.DiscCircle) =>
      (⟨⟨Aux.canonPt Φ₀ y.1 c.val, Aux.canonPt_mem hbrB y.2 c.norm_val⟩,
        (by exact y.2 : Work.SC.branchProj z₀ E _ ∈ B)⟩ :
        ↥(Work.SC.branchProj z₀ E ⁻¹' B))) ?_
    intro c
    exact (Aux.continuous_canonPt hbrB hndB c.norm_val).subtype_mk (fun y => y.2)
  have hcov : IsEvenlyCovered (Work.SC.branchProj z₀ E) x Aux.DiscCircle := by
    refine ⟨inferInstance, B, hxmem, hBopen, hπcont.isOpen_preimage B hBopen, ?_, ?_⟩
    · exact ({ toFun := H, invFun := K, left_inv := hleft, right_inv := hright,
               continuous_toFun := hHcont, continuous_invFun := hKcont } :
        ↥(Work.SC.branchProj z₀ E ⁻¹' B) ≃ₜ ↥B × Aux.DiscCircle)
    · intro p
      rfl
  exact hcov.to_isEvenlyCovered_preimage

/-- **The bridge from the conjugate étale space to the modulus bundle** (decay-free form). -/
theorem conjBridgeMap {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀})) :
    ∃ φ : (puncturedOpens z₀ × ℝ) → Work.SC.ModulusBundle z₀ E,
      @Continuous (puncturedOpens z₀ × ℝ) (Work.SC.ModulusBundle z₀ E)
          (greenConjTopology z₀ E) (Work.SC.modulusBundleTopology z₀ E) φ ∧
        (∀ p : puncturedOpens z₀ × ℝ, Work.SC.branchProj z₀ E (φ p) = p.1.1) ∧
        (∀ (x : puncturedOpens z₀) (t : ℝ),
          (φ (x, t)).1.2.1 = Complex.exp (-((E x.1 : ℂ) + (t : ℂ) * Complex.I))) := by
  classical
  letI topBranch : TopologicalSpace (X × ℂ × ℂ) := Work.SC.branchTopology z₀ E
  letI topConj : TopologicalSpace ((puncturedOpens z₀) × ℝ) := greenConjTopology z₀ E
  have hmodel : ∀ u : puncturedOpens z₀,
      ∃ (U : Set X) (Φ : X → ℂ),
        Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ 𝓝 u.1 ∧ Φ u.1 ≠ 0 :=
    fun u => exists_isModulusBranch_of_ne_of_unitGreen (z₀ := z₀) (E := E) hEharm u.2
  choose Um Φm hUm_br hUm_nhds hUm_ne using hmodel
  have hUm_mem : ∀ u : puncturedOpens z₀, u.1 ∈ Um u :=
    fun u => mem_of_mem_nhds (hUm_nhds u)
  let gv : puncturedOpens z₀ × ℝ → ℂ :=
    fun p => Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I))
  have hgv_norm : ∀ p, ‖gv p‖ = Real.exp (-(E p.1.1)) := by
    intro p
    show ‖Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ = Real.exp (-(E p.1.1))
    rw [Complex.norm_exp]
    congr 1
    simp
  let cc : puncturedOpens z₀ × ℝ → ℂ := fun p => gv p / Φm p.1 p.1.1
  have hcc_norm : ∀ p, ‖cc p‖ = 1 := by
    intro p
    show ‖gv p / Φm p.1 p.1.1‖ = 1
    rw [norm_div, hgv_norm p,
      (hUm_br p.1).norm_eq p.1.1 (hUm_mem p.1) p.1.2, div_self (Real.exp_ne_zero _)]
  have hcc_mul : ∀ p, cc p * Φm p.1 p.1.1 = gv p := by
    intro p
    show gv p / Φm p.1 p.1.1 * Φm p.1 p.1.1 = gv p
    rw [div_mul_cancel₀ _ (hUm_ne p.1)]
  let F : puncturedOpens z₀ × ℝ → X × ℂ × ℂ :=
    fun p => (p.1.1, gv p, cc p * Work.SC.chartDeriv (Φm p.1) p.1.1)
  have hFmem : ∀ p, F p ∈ Work.SC.branchSet z₀ E := by
    intro p
    refine ⟨Um p.1, fun y => cc p * Φm p.1 y,
      Aux.isModulusBranch_const_mul (hUm_br p.1) (hcc_norm p), hUm_mem p.1, ?_, ?_⟩
    · show gv p = cc p * Φm p.1 p.1.1
      exact (hcc_mul p).symm
    · show cc p * Work.SC.chartDeriv (Φm p.1) p.1.1
          = Work.SC.chartDeriv (fun y => cc p * Φm p.1 y) p.1.1
      exact (Aux.chartDeriv_const_mul ((hUm_br p.1).holomorphic p.1.1 (hUm_mem p.1)) (cc p)).symm
  have hFcont : @Continuous (puncturedOpens z₀ × ℝ) (X × ℂ × ℂ)
      (greenConjTopology z₀ E) (Work.SC.branchTopology z₀ E) F := by
    rw [Work.SC.branchTopology, continuous_generateFrom_iff]
    intro S hS
    obtain ⟨U₀, Φ₀, hbr₀, rfl⟩ := hS
    rw [isOpen_iff_mem_nhds]
    intro p₀ hp₀
    rw [Set.mem_preimage, Work.SC.mem_branchGraph_iff] at hp₀
    obtain ⟨hp₀U₀, hp₀val, hp₀der⟩ := hp₀
    have hΨ₀br : Work.SC.IsModulusBranch z₀ E (Um p₀.1) (fun y => cc p₀ * Φm p₀.1 y) :=
      Aux.isModulusBranch_const_mul (hUm_br p₀.1) (hcc_norm p₀)
    have hΨ₀val : (fun y => cc p₀ * Φm p₀.1 y) p₀.1.1 = Φ₀ p₀.1.1 := by
      show cc p₀ * Φm p₀.1 p₀.1.1 = Φ₀ p₀.1.1
      rw [hcc_mul p₀]
      exact hp₀val
    have hΨ₀_Φ₀ : (fun y => cc p₀ * Φm p₀.1 y) =ᶠ[𝓝 p₀.1.1] Φ₀ :=
      eventually_eq_of_value_eq_of_isModulusBranch_of_ne hbr₀ hΨ₀br
        ⟨hp₀U₀, hUm_mem p₀.1⟩ p₀.1.2 hΨ₀val
    obtain ⟨W₁, hW₁sub, hW₁open, hp₀W₁⟩ := mem_nhds_iff.mp hΨ₀_Φ₀
    set W : Set X := W₁ ∩ U₀ with hWdef
    have hWopen : IsOpen W := hW₁open.inter hbr₀.1
    have hp₀W : p₀.1.1 ∈ W := ⟨hp₀W₁, hp₀U₀⟩
    have hWval : ∀ y ∈ W, Φ₀ y = cc p₀ * Φm p₀.1 y := fun y hy => (hW₁sub hy.1).symm
    obtain ⟨B₁, F₁, hB₁open, hp₀B₁, hF₁hol, hF₁re⟩ :=
      Submission.exists_conjData (X := puncturedOpens z₀)
        (greenPunctured_harmonic (z₀ := z₀) (E := E) hEharm) p₀.1
    let F₂ : puncturedOpens z₀ → ℂ :=
      fun v => F₁ v + (((p₀.2 - (F₁ p₀.1).im : ℝ)) : ℂ) * Complex.I
    have hF₂hol : Submission.HolomorphicOnX F₂ B₁ :=
      hF₁hol.add (Submission.holomorphicOnX_const _)
    have hF₂re : ∀ v ∈ B₁, (F₂ v).re = E v.1 := by
      intro v hv
      have h1 : (F₂ v).re = (F₁ v).re := add_pureImag_re (F₁ v) _
      rw [h1]
      exact hF₁re v hv
    have hF₂im : (F₂ p₀.1).im = p₀.2 := by
      rw [show (F₂ p₀.1).im = (F₁ p₀.1).im + (p₀.2 - (F₁ p₀.1).im)
        from add_pureImag_im (F₁ p₀.1) _]
      ring
    let Ψ₂ : X → ℂ := punctLift (fun v => Complex.exp (-(F₂ v)))
    have hΨ₂br : Work.SC.IsModulusBranch z₀ E (punctImage B₁) Ψ₂ :=
      isModulusBranch_punctLift hB₁open hF₂hol hF₂re
    have hΨ₂val : Ψ₂ p₀.1.1 = Complex.exp (-(F₂ p₀.1)) := punctLift_apply p₀.1.2
    have hΨ₂_Ψ₀ : Ψ₂ =ᶠ[𝓝 p₀.1.1] (fun y => cc p₀ * Φm p₀.1 y) := by
      refine eventually_eq_of_value_eq_of_isModulusBranch_of_ne hΨ₀br hΨ₂br
        ⟨hUm_mem p₀.1, ⟨p₀.1, hp₀B₁, rfl⟩⟩ p₀.1.2 ?_
      show Ψ₂ p₀.1.1 = cc p₀ * Φm p₀.1 p₀.1.1
      rw [hΨ₂val, hcc_mul p₀]
      show Complex.exp (-(F₂ p₀.1))
        = Complex.exp (-((E p₀.1.1 : ℂ) + (p₀.2 : ℂ) * Complex.I))
      rw [exp_neg_eq_of_re (hF₂re p₀.1 hp₀B₁), hF₂im]
    obtain ⟨W₂, hW₂sub, hW₂open, hp₀W₂⟩ := mem_nhds_iff.mp hΨ₂_Ψ₀
    set N₀ : Set (puncturedOpens z₀) := B₁ ∩ (Subtype.val ⁻¹' (W ∩ W₂)) with hN₀def
    have hN₀open : IsOpen N₀ :=
      hB₁open.inter ((hWopen.inter hW₂open).preimage continuous_subtype_val)
    have hp₀N₀ : p₀.1 ∈ N₀ := ⟨hp₀B₁, ⟨hp₀W, hp₀W₂⟩⟩
    have hNopen : IsOpen (Submission.conjGraph N₀ F₂) :=
      Submission.isOpen_conjGraph hN₀open (hF₂hol.mono Set.inter_subset_left)
        (fun v hv => hF₂re v hv.1)
    have hp₀N : p₀ ∈ Submission.conjGraph N₀ F₂ := ⟨hp₀N₀, hF₂im.symm⟩
    refine Filter.mem_of_superset (hNopen.mem_nhds hp₀N) ?_
    rintro p ⟨hpN₀, hpval⟩
    obtain ⟨hpB₁, hpW⟩ := hpN₀
    have hpu : p.1.1 ∈ W ∩ W₂ := hpW
    have h1 : gv p = Ψ₂ p.1.1 := by
      show Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I)) = Ψ₂ p.1.1
      rw [show Ψ₂ p.1.1 = Complex.exp (-(F₂ p.1)) from punctLift_apply p.1.2, hpval]
      exact (exp_neg_eq_of_re (hF₂re p.1 hpB₁)).symm
    have hval : gv p = Φ₀ p.1.1 := by
      rw [h1, show Ψ₂ p.1.1 = cc p₀ * Φm p₀.1 p.1.1 from hW₂sub hpu.2,
        ← hWval p.1.1 hpu.1]
    have hder : cc p * Work.SC.chartDeriv (Φm p.1) p.1.1 = Work.SC.chartDeriv Φ₀ p.1.1 := by
      have hΨpbr : Work.SC.IsModulusBranch z₀ E (Um p.1) (fun y => cc p * Φm p.1 y) :=
        Aux.isModulusBranch_const_mul (hUm_br p.1) (hcc_norm p)
      have hevp : (fun y => cc p * Φm p.1 y) =ᶠ[𝓝 p.1.1] Ψ₂ := by
        refine eventually_eq_of_value_eq_of_isModulusBranch_of_ne hΨ₂br hΨpbr
          ⟨⟨p.1, hpB₁, rfl⟩, hUm_mem p.1⟩ p.1.2 ?_
        show cc p * Φm p.1 p.1.1 = Ψ₂ p.1.1
        rw [hcc_mul p]
        exact h1
      have hev₂ : Ψ₂ =ᶠ[𝓝 p.1.1] (fun y => cc p₀ * Φm p₀.1 y) :=
        Filter.eventually_of_mem (hW₂open.mem_nhds hpu.2) (fun y hy => hW₂sub hy)
      have hev₁ : (fun y => cc p₀ * Φm p₀.1 y) =ᶠ[𝓝 p.1.1] Φ₀ :=
        Filter.eventually_of_mem (hW₁open.mem_nhds hpu.1.1) (fun y hy => hW₁sub hy)
      calc cc p * Work.SC.chartDeriv (Φm p.1) p.1.1
          = Work.SC.chartDeriv (fun y => cc p * Φm p.1 y) p.1.1 :=
            (Aux.chartDeriv_const_mul ((hUm_br p.1).holomorphic p.1.1 (hUm_mem p.1)) (cc p)).symm
        _ = Work.SC.chartDeriv Ψ₂ p.1.1 := Aux.chartDeriv_congr_of_eventuallyEq hevp
        _ = Work.SC.chartDeriv (fun y => cc p₀ * Φm p₀.1 y) p.1.1 :=
            Aux.chartDeriv_congr_of_eventuallyEq hev₂
        _ = Work.SC.chartDeriv Φ₀ p.1.1 := Aux.chartDeriv_congr_of_eventuallyEq hev₁
    exact ⟨hpu.1.2, hval, hder⟩
  refine ⟨fun p => ⟨F p, hFmem p⟩, ?_, ?_, ?_⟩
  · exact hFcont.subtype_mk hFmem
  · intro p
    rfl
  · intro x t
    rfl

/-! ## The periods of a loop null-homotopic in `X` are multiples of `2π` -/

/-- **The main period computation** (decay-free form), with its two covering-theoretic inputs
isolated as hypotheses. -/
theorem greenPeriodHom_two_pi_zmultiples_of_inputs {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀)
    (hγ : FundamentalGroup.map (ContinuousMap.mk (Subtype.val : puncturedOpens z₀ → X)
      continuous_subtype_val) u₀ γ = 1)
    (hcovX : @IsCoveringMap (Work.SC.ModulusBundle z₀ E) X (Work.SC.modulusBundleTopology z₀ E) _
      (Work.SC.branchProj z₀ E))
    (hbridge : ∃ φ : ((puncturedOpens z₀) × ℝ) → Work.SC.ModulusBundle z₀ E,
      @Continuous ((puncturedOpens z₀) × ℝ) (Work.SC.ModulusBundle z₀ E)
          (greenConjTopology z₀ E) (Work.SC.modulusBundleTopology z₀ E) φ ∧
        (∀ p : (puncturedOpens z₀) × ℝ, Work.SC.branchProj z₀ E (φ p) = p.1.1) ∧
        (∀ (x : puncturedOpens z₀) (t : ℝ),
          (φ (x, t)).1.2.1 = Complex.exp (-((E x.1 : ℂ) + (t : ℂ) * Complex.I)))) :
    ∃ k : ℤ, greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi) := by
  classical
  letI : TopologicalSpace ((puncturedOpens z₀) × ℝ) := greenConjTopology z₀ E
  letI : TopologicalSpace (Work.SC.ModulusBundle z₀ E) := Work.SC.modulusBundleTopology z₀ E
  have hcovU : IsCoveringMap (Prod.fst : (puncturedOpens z₀) × ℝ → puncturedOpens z₀) :=
    green_isCoveringMap hEharm
  obtain ⟨φ, hφcont, hφproj, hφval⟩ := hbridge
  obtain ⟨γp⟩ := γ
  let e₀ : (puncturedOpens z₀) × ℝ := (u₀, 0)
  let Γ : C(unitInterval, (puncturedOpens z₀) × ℝ) :=
    hcovU.liftPath γp e₀ (γp.source.trans (rfl : Prod.fst e₀ = u₀).symm)
  have hΓlifts : Prod.fst ∘ (Γ : unitInterval → (puncturedOpens z₀) × ℝ) =
      (γp : unitInterval → ↥(puncturedOpens z₀)) := hcovU.liftPath_lifts _ _ _
  have hΓ0 : Γ 0 = e₀ := hcovU.liftPath_zero _ _ _
  have hper : greenPeriodHom hEharm u₀ (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) =
      (Γ 1).2 := by
    rw [greenPeriodHom_apply]
    have h1 : (hcovU.monodromy (Path.Homotopic.Quotient.mk γp)
        (Submission.conjFiberPt u₀ 0)).1 = Γ 1 := rfl
    have h2 : (Submission.conjFiberPt u₀ 0).1.2 = 0 := rfl
    have h3 : (hcovU.monodromy (Path.Homotopic.Quotient.mk γp)
        (Submission.conjFiberPt u₀ 0)).1.2 = (Γ 1).2 := congrArg Prod.snd h1
    simp only [Submission.conjPeriod, h3, h2, sub_zero]
  set incl : C(puncturedOpens z₀, X) := ⟨Subtype.val, continuous_subtype_val⟩ with hincl
  set γX : Path u₀.1 u₀.1 :=
    γp.map (f := (Subtype.val : puncturedOpens z₀ → X)) continuous_subtype_val with hγX
  have hmap : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp) =
      Path.Homotopic.Quotient.mk γX := by
    rw [show (FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp))
        = (Path.Homotopic.Quotient.mk γp).map incl from rfl]
    exact (Path.Homotopic.Quotient.mk_map γp incl).symm
  have hγ' : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp) = 1 := hγ
  have hγX1 : Path.Homotopic.Quotient.mk γX = Path.Homotopic.Quotient.mk (Path.refl u₀.1) := by
    rw [← hmap, hγ']
    exact FundamentalGroup.one_def
  have hhom : (γX : C(unitInterval, X)).HomotopicRel (ContinuousMap.const unitInterval u₀.1)
      {0,1} := by
    have h3 : γX.Homotopic (Path.refl u₀.1) := Path.Homotopic.Quotient.eq.mp hγX1
    exact ⟨h3.some⟩
  set ΓX : C(unitInterval, Work.SC.ModulusBundle z₀ E) :=
    ⟨fun s => φ (Γ s), hφcont.comp Γ.continuous⟩ with hΓX
  have hΓXlifts : Work.SC.branchProj z₀ E ∘ (ΓX : unitInterval → Work.SC.ModulusBundle z₀ E) =
      (γX : unitInterval → X) := by
    funext s
    have hs : (Γ s).1 = γp s := congrFun hΓlifts s
    show Work.SC.branchProj z₀ E (φ (Γ s)) = γX s
    rw [hφproj, hs]
    rfl
  have hΓX0 : (ΓX : unitInterval → Work.SC.ModulusBundle z₀ E) 0 = φ e₀ := by
    show φ (Γ 0) = φ e₀
    rw [hΓ0]
  have huniq : ΓX = hcovX.liftPath γX (φ e₀) ((γX.source).trans (hφproj e₀).symm) :=
    (hcovX.eq_liftPath_iff' (γ := γX) (e := φ e₀)
      (γ_0 := (γX.source).trans (hφproj e₀).symm)).mpr ⟨hΓXlifts, hΓX0⟩
  have hfinal : φ (Γ 1) = φ e₀ := by
    have h1 : φ (Γ 1) = (hcovX.liftPath γX (φ e₀)
        ((γX.source).trans (hφproj e₀).symm)) 1 := by
      rw [← huniq]
      rfl
    rw [h1]
    have h2 := hcovX.liftPath_apply_one_eq_of_homotopicRel hhom (φ e₀)
      ((γX.source).trans (hφproj e₀).symm) (hφproj e₀).symm
    rw [h2, hcovX.liftPath_const (x := u₀.1) (hpe := (hφproj e₀).symm)]
    rfl
  have hbase1 : (Γ 1).1 = u₀ := by
    have := congrFun hΓlifts 1
    simpa using this
  have hval1 : (φ (Γ 1)).1.2.1 =
      Complex.exp (-((E u₀.1 : ℂ) + ((Γ 1).2 : ℂ) * Complex.I)) := by
    have hsplit : Γ 1 = (u₀, (Γ 1).2) := Prod.ext hbase1 rfl
    rw [hsplit]
    exact hφval u₀ (Γ 1).2
  have hval0 : (φ e₀).1.2.1 = Complex.exp (-((E u₀.1 : ℂ) + (0 : ℂ) * Complex.I)) := by
    show (φ (u₀, 0)).1.2.1 = _
    exact hφval u₀ 0
  have heqexp : Complex.exp (-((E u₀.1 : ℂ) + ((Γ 1).2 : ℂ) * Complex.I)) =
      Complex.exp (-((E u₀.1 : ℂ) + (0 : ℂ) * Complex.I)) := by
    rw [← hval1, ← hval0, hfinal]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heqexp
  have him : -(((Γ 1).2 : ℝ)) = (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  refine ⟨-n, ?_⟩
  show greenPeriodHom hEharm u₀ (Additive.ofMul (Path.Homotopic.Quotient.mk γp))
    = ↑(-n) * (2 * Real.pi)
  rw [hper]
  push_cast
  linarith

/-- **The periods of the conjugate around loops null-homotopic in `X` are multiples of `2π`**
(decay-free form). -/
theorem greenPeriodHom_two_pi_zmultiples {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀)
    (hγ : FundamentalGroup.map (ContinuousMap.mk (Subtype.val : puncturedOpens z₀ → X)
      continuous_subtype_val) u₀ γ = 1) :
    ∃ k : ℤ, greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi) :=
  greenPeriodHom_two_pi_zmultiples_of_inputs hEharm u₀ γ hγ
    (isCoveringMap_branchProj hEharm hpole)
    (conjBridgeMap hEharm)

end Work.ModulusLP
