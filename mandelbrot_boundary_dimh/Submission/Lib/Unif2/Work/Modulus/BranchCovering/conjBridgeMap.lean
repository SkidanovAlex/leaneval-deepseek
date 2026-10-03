import Mathlib
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_isModulusBranch_of_ne
import Submission.Lib.Unif2.Work.SimplyConnected.Modulus.exists_ratio_eq_of_isModulusBranch
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.conjBridgeSetup
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.branchOfUnitGreen

/-!
# The bridge map from the conjugate étale space to the modulus bundle

Let `X` be a connected complex one-manifold, `z₀ : X` and `E : X → ℝ` a Green function with pole
`z₀` (`Work.UnitGreen.IsUnitGreenFunctionAt`).  The multivalued modulus `Φ = exp (-(E + iE*))` is organised,
in `Work.SC.ModulusDefs`, as the *modulus bundle* `Work.SC.branchProj : ModulusBundle z₀ E → X`
whose fibre over `x` consists of the pairs `(Φ x, Φ'(x))` coming from the local branches of the
modulus; and, in `Submission.Conjugate`, as the *conjugate étale space*
`((X ∖ {z₀}) × ℝ, greenConjTopology z₀ E)`, whose point over `u` is the value of a local harmonic
conjugate of `E` at `u`.

This module constructs the canonical map between the two: the point `(u, t)` of the étale space is
sent to the branch whose value at `u` is `exp (-(E u + i t))`.  The map is continuous, covers the
punctured surface and realises `exp (-(E + iE*))` on the nose.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus.BranchCovering

theorem conjBridgeMap {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∃ φ : (Work.Modulus.puncturedOpens z₀ × ℝ) → Work.SC.ModulusBundle z₀ E,
      @Continuous (Work.Modulus.puncturedOpens z₀ × ℝ) (Work.SC.ModulusBundle z₀ E)
          (Work.Modulus.greenConjTopology z₀ E) (Work.SC.modulusBundleTopology z₀ E) φ ∧
        (∀ p : Work.Modulus.puncturedOpens z₀ × ℝ,
          Work.SC.branchProj z₀ E (φ p) = p.1.1) ∧
        (∀ (x : Work.Modulus.puncturedOpens z₀) (t : ℝ),
          (φ (x, t)).1.2.1 = Complex.exp (-((E x.1 : ℂ) + (t : ℂ) * Complex.I))) := by
  classical
  letI topBranch : TopologicalSpace (X × ℂ × ℂ) := Work.SC.branchTopology z₀ E
  letI topConj : TopologicalSpace ((Work.Modulus.puncturedOpens z₀) × ℝ) :=
    Work.Modulus.greenConjTopology z₀ E
  -- a model branch of the modulus near every point of the punctured surface
  have hmodel : ∀ u : Work.Modulus.puncturedOpens z₀,
      ∃ (U : Set X) (Φ : X → ℂ),
        Work.SC.IsModulusBranch z₀ E U Φ ∧ U ∈ 𝓝 u.1 ∧ Φ u.1 ≠ 0 :=
    fun u => Aux.exists_isModulusBranch_of_ne_of_unitGreen (z₀ := z₀) (E := E) hE u.2
  choose Um Φm hUm_br hUm_nhds hUm_ne using hmodel
  have hUm_mem : ∀ u : Work.Modulus.puncturedOpens z₀, u.1 ∈ Um u :=
    fun u => mem_of_mem_nhds (hUm_nhds u)
  -- the value of the multivalued modulus at a point of the étale space
  let gv : (Work.Modulus.puncturedOpens z₀) × ℝ → ℂ :=
    fun p => Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I))
  have hgv_norm : ∀ p, ‖gv p‖ = Real.exp (-(E p.1.1)) := by
    intro p
    show ‖Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ = Real.exp (-(E p.1.1))
    rw [Complex.norm_exp]
    congr 1
    simp
  -- the unit by which the model branch at `p.1` is scaled to have value `gv p`
  let cc : (Work.Modulus.puncturedOpens z₀) × ℝ → ℂ := fun p => gv p / Φm p.1 p.1.1
  have hcc_norm : ∀ p, ‖cc p‖ = 1 := by
    intro p
    show ‖gv p / Φm p.1 p.1.1‖ = 1
    rw [norm_div, hgv_norm p,
      (hUm_br p.1).norm_eq p.1.1 (hUm_mem p.1) p.1.2, div_self (Real.exp_ne_zero _)]
  have hcc_mul : ∀ p, cc p * Φm p.1 p.1.1 = gv p := by
    intro p
    show gv p / Φm p.1 p.1.1 * Φm p.1 p.1.1 = gv p
    rw [div_mul_cancel₀ _ (hUm_ne p.1)]
  -- the bridge, on the level of `X × ℂ × ℂ`
  let F : (Work.Modulus.puncturedOpens z₀) × ℝ → X × ℂ × ℂ :=
    fun p => (p.1.1, gv p, cc p * Work.SC.chartDeriv (Φm p.1) p.1.1)
  have hFmem : ∀ p, F p ∈ Work.SC.branchSet z₀ E := by
    intro p
    refine ⟨Um p.1, fun y => cc p * Φm p.1 y,
      isModulusBranch_const_mul (hUm_br p.1) (hcc_norm p), hUm_mem p.1, ?_, ?_⟩
    · show gv p = cc p * Φm p.1 p.1.1
      exact (hcc_mul p).symm
    · show cc p * Work.SC.chartDeriv (Φm p.1) p.1.1
          = Work.SC.chartDeriv (fun y => cc p * Φm p.1 y) p.1.1
      exact (chartDeriv_const_mul ((hUm_br p.1).holomorphic p.1.1 (hUm_mem p.1)) (cc p)).symm
  -- continuity of the bridge into the topology of the branch bundle
  have hFcont : @Continuous ((Work.Modulus.puncturedOpens z₀) × ℝ) (X × ℂ × ℂ)
      (Work.Modulus.greenConjTopology z₀ E) (Work.SC.branchTopology z₀ E) F := by
    rw [Work.SC.branchTopology, continuous_generateFrom_iff]
    intro S hS
    obtain ⟨U₀, Φ₀, hbr₀, rfl⟩ := hS
    rw [isOpen_iff_mem_nhds]
    intro p₀ hp₀
    rw [Set.mem_preimage, Work.SC.mem_branchGraph_iff] at hp₀
    obtain ⟨hp₀U₀, hp₀val, hp₀der⟩ := hp₀
    -- the scaled model branch at `p₀` agrees with `Φ₀` near `p₀.1.1`
    have hΨ₀br : Work.SC.IsModulusBranch z₀ E (Um p₀.1) (fun y => cc p₀ * Φm p₀.1 y) :=
      isModulusBranch_const_mul (hUm_br p₀.1) (hcc_norm p₀)
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
    -- a local conjugate of `E` on the punctured surface, matched to the fibre coordinate `p₀.2`
    obtain ⟨B₁, F₁, hB₁open, hp₀B₁, hF₁hol, hF₁re⟩ :=
      Submission.exists_conjData (X := Work.Modulus.puncturedOpens z₀)
        (Work.Modulus.greenPunctured_harmonic (z₀ := z₀) (E := E) hE) p₀.1
    let F₂ : Work.Modulus.puncturedOpens z₀ → ℂ :=
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
    -- the branch of the modulus attached to `F₂`, and its agreement with the scaled model branch
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
    -- the neighbourhood in the étale space
    set N₀ : Set (Work.Modulus.puncturedOpens z₀) :=
      B₁ ∩ (Subtype.val ⁻¹' (W ∩ W₂)) with hN₀def
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
    -- the value coordinate
    have h1 : gv p = Ψ₂ p.1.1 := by
      show Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I)) = Ψ₂ p.1.1
      rw [show Ψ₂ p.1.1 = Complex.exp (-(F₂ p.1)) from punctLift_apply p.1.2, hpval]
      exact (exp_neg_eq_of_re (hF₂re p.1 hpB₁)).symm
    have hval : gv p = Φ₀ p.1.1 := by
      rw [h1, show Ψ₂ p.1.1 = cc p₀ * Φm p₀.1 p.1.1 from hW₂sub hpu.2,
        ← hWval p.1.1 hpu.1]
    -- the derivative coordinate
    have hder : cc p * Work.SC.chartDeriv (Φm p.1) p.1.1 = Work.SC.chartDeriv Φ₀ p.1.1 := by
      have hΨpbr : Work.SC.IsModulusBranch z₀ E (Um p.1) (fun y => cc p * Φm p.1 y) :=
        isModulusBranch_const_mul (hUm_br p.1) (hcc_norm p)
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
            (chartDeriv_const_mul ((hUm_br p.1).holomorphic p.1.1 (hUm_mem p.1)) (cc p)).symm
        _ = Work.SC.chartDeriv Ψ₂ p.1.1 := chartDeriv_congr_of_eventuallyEq hevp
        _ = Work.SC.chartDeriv (fun y => cc p₀ * Φm p₀.1 y) p.1.1 :=
            chartDeriv_congr_of_eventuallyEq hev₂
        _ = Work.SC.chartDeriv Φ₀ p.1.1 := chartDeriv_congr_of_eventuallyEq hev₁
    exact ⟨hpu.1.2, hval, hder⟩
  refine ⟨fun p => ⟨F p, hFmem p⟩, ?_, ?_, ?_⟩
  · exact hFcont.subtype_mk hFmem
  · intro p
    rfl
  · intro x t
    rfl

end Work.Modulus.BranchCovering
