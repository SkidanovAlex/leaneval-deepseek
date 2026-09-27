import Mathlib
import Submission.Work.Drive.N2C.arcImmersion
import Submission.Work.Drive.N2C.arcLiftOfLevelCurves
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The arc lift of the saddle (§1.3/§1.4 of the D2 design)

`Work.Drive.N2C.arcLiftOfLevelCurves` lifts a **globally** smooth immersed curve `α : ℝ → M` whose
image on an open preconnected `J` lies in the range of a component curve to the component's
parameter.  The model arcs of the saddle's anchor level are smooth and immersive only on
`Ioo (-3) 3` (the chart-inverse row `D.hφ'` is available only while the chart vector stays in the
chart's ball), so this file proves the **localised** form of the lift — its hypotheses
`∀ w ∈ J, ContMDiffAt ... α w` and `∀ w ∈ J, mfderiv ... α w 1 ≠ 0` — from which the two arc lifts
`τU` (upper arc) and `τL` (lower arc) of the design's §1.4 follow at once.

The localisation is verbatim: the three helpers of `N2Lead/exists_arcLift.lean` use the global
smoothness of `α` only through `hα.continuous` (at the points of the open set `α ⁻¹' (W ∩ U) ∩ J`),
`hα.contMDiffAt` (at a point of `J`) and `hαimm` (at a point of `J`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]

open Work.Drive.N2Lead (arcZ arcUpPt arcDnPt)

section Localised

/-- `Work.Drive.N2Lead.exists_local_piece_of` with the smoothness of `α` required only on `J`. -/
lemma exists_local_piece_of_on {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n)
    (i : Fin n) {α : ℝ → M} {J : Set ℝ}
    (hα : ∀ w ∈ J, ContMDiffAt 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) α w)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0)
    (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) (w : ℝ) (hw : w ∈ J) (t : ℝ)
    (ht : L.γ i t = α w) :
    ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
      ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t := by
  obtain ⟨U, φ, hUopen, htU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve (L.γ i) (L.sm i) himm t
  obtain ⟨W, hWopen, htW, hW⟩ :=
    Work.Drive.N2Lead.exists_local_rightInverse (L.sm i).continuous (L.per i) (L.modOne i) t hδpos hφ
  have hWUopen : IsOpen (W ∩ U) := hWopen.inter hUopen
  have htWU : L.γ i t ∈ W ∩ U := ⟨htW, htU⟩
  have hV₀open : IsOpen (α ⁻¹' (W ∩ U) ∩ J) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.inter_mem
      (((hα x hx.2).continuousAt).preimage_mem_nhds (hWUopen.mem_nhds hx.1))
      (hJ.mem_nhds hx.2)
  have hwV₀ : w ∈ α ⁻¹' (W ∩ U) ∩ J := ⟨by change α w ∈ W ∩ U; rw [← ht]; exact htWU, hw⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hV₀open w hwV₀
  refine ⟨J ∩ Ioo (w - ε) (w + ε), fun u => φ (α u), inter_subset_left, hJ.inter isOpen_Ioo,
    ?_, ⟨hw, by rw [mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩, ?_, ?_, ?_⟩
  · exact (convex_iff_ordConnected.mpr hJc.ordConnected).ordConnected.inter
      (convex_Ioo _ _).ordConnected
  · refine ContinuousOn.comp (t := W ∩ U) (hφsm.continuousOn.mono inter_subset_right) ?_
      (fun u hu => ?_)
    · intro u hu
      exact ((hα u hu.1).continuousAt).continuousWithinAt
    · have hu' : u ∈ Metric.ball w ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
      exact Set.mem_preimage.mp (hεsub hu').1
  · intro u hu
    have hu' : u ∈ Metric.ball w ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    have huW : α u ∈ W := (Set.mem_preimage.mp (hεsub hu').1).1
    exact hW (α u) huW (hJα u hu.1)
  · change φ (α w) = t
    rw [← ht]
    exact hφ t ⟨by linarith [hδpos], by linarith [hδpos]⟩

/-- `Work.Drive.N2Lead.contDiffOn_of_lift` with the smoothness of `α` required only on `J`. -/
lemma contDiffOn_of_lift_on {γ α : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0) {J : Set ℝ} (hJ : IsOpen J)
    (hα : ∀ w ∈ J, ContMDiffAt 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) α w)
    {τ : ℝ → ℝ} (hτc : ContinuousOn τ J) (hcast : ∀ w ∈ J, γ (τ w) = α w) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J := by
  rw [IsOpen.contDiffOn_iff hJ]
  intro w hw
  obtain ⟨U, φ, hUopen, hγtU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve γ hγsm himm (τ w)
  have hαwU : α w ∈ U := by rw [← hcast w hw]; exact hγtU
  have hτat : ContinuousAt τ w := hτc.continuousAt (hJ.mem_nhds hw)
  have hV1 : {w' : ℝ | α w' ∈ U} ∈ 𝓝 w :=
    ((hα w hw).continuousAt).preimage_mem_nhds (hUopen.mem_nhds hαwU)
  have hV2 : {w' : ℝ | τ w' ∈ Ioo (τ w - δ) (τ w + δ)} ∈ 𝓝 w :=
    hτat.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => φ (α w')) w :=
    contMDiffAt_iff_contDiffAt.mp ((hφsm.contMDiffAt (hUopen.mem_nhds hαwU)).comp w (hα w hw))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hV1, hV2, hJ.mem_nhds hw] with w' h1 h2 h3
  have := hφ (τ w') h2
  rw [hcast w' h3] at this
  exact this.symm

/-- `Work.Drive.N2Lead.deriv_ne_zero_of_lift` with the immersion of `α` required only on `J`. -/
lemma deriv_ne_zero_of_lift_on {γ α : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {J : Set ℝ} (hJ : IsOpen J)
    (hαimm : ∀ w ∈ J, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w 1 ≠ 0)
    {τ : ℝ → ℝ} (hτsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J)
    (hcast : ∀ w ∈ J, γ (τ w) = α w) :
    ∀ w ∈ J, deriv τ w ≠ 0 := by
  intro w hw
  have hτat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ w := (IsOpen.contDiffOn_iff hJ).mp hτsm hw
  have hτmd : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w :=
    (contMDiffAt_iff_contDiffAt.mpr hτat).mdifferentiableAt (by simp)
  have hγmd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w) :=
    (hγsm.contMDiffAt (x := τ w)).mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ ∘ τ) w
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) :=
    mfderiv_comp w hγmd hτmd
  have hev : (γ ∘ τ) =ᶠ[𝓝 w] α := by
    filter_upwards [hJ.mem_nhds hw] with x hx
    exact hcast x hx
  have hchain' : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) := by
    rw [← Filter.EventuallyEq.mfderiv_eq_v433 hev]
    exact hchain
  have h1 : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) 1 = deriv τ w := by
    rw [mfderiv_eq_fderiv]
    rfl
  have happ : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w 1
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) (deriv τ w) := by
    rw [hchain']
    change (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) τ w) 1)
      = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ (τ w)) (deriv τ w)
    exact congrArg _ h1
  intro h0
  have h0' : (deriv τ w : TangentSpace 𝓘(ℝ,ℝ) (τ w)) = 0 := h0
  rw [h0', map_zero] at happ
  exact hαimm w hw happ

/-- **The arc lift with localised rows**: the §1.4 statement of the design. -/
theorem arcLiftOfLevelCurvesOn {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n) (i : Fin n)
    {α : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hα : ∀ w ∈ J, ContMDiffAt 𝓘(ℝ,ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) α w)
    (hαimm : ∀ w ∈ J, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) α w 1 ≠ 0)
    (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J ∧
      (∀ w ∈ J, L.γ i (τ w) = α w) ∧ (∀ w ∈ J, deriv τ w ≠ 0) ∧
      (StrictMonoOn τ J ∨ StrictAntiOn τ J) := by
  have himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0 :=
    fun t => Work.Drive.N2Lead.mfderiv_γ_ne_zero L i t
  have hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), L.γ i t = α w →
      ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
        ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t :=
    fun w hw t ht => exists_local_piece_of_on L i hα himm hJ hJc hJα w hw t ht
  obtain ⟨τ, hτc, hτγ⟩ :=
    Work.Drive.N2Lead.exists_continuous_lift hJ hJc hJα (L.modOne i) (L.per i) hpiece
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ J :=
    contDiffOn_of_lift_on (L.sm i) himm hJ hα hτc hτγ
  have hderiv : ∀ w ∈ J, deriv τ w ≠ 0 :=
    deriv_ne_zero_of_lift_on (L.sm i) hJ hαimm hsm hτγ
  exact ⟨τ, hsm, hτγ, hderiv,
    Work.Drive.N2Lead.strictMonoOn_or_strictAntiOn_of_deriv_ne_zero hJ hJc hsm hderiv⟩

end Localised

section Arcs

/-- **The arc lift of the upper model arc** (the `τU` of the design's §1.4). -/
theorem exists_arcReparam_up {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ,ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    {a : ℝ} {n : ℕ} (L : LevelCurves f a n) (i : Fin n)
    (hJα : ∀ w ∈ Ioo (-3) 3, arcUpPt D lam0 η w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ (Ioo (-3) 3) ∧
      (∀ w ∈ Ioo (-3) 3, L.γ i (τ w) = arcUpPt D lam0 η w) ∧
      (∀ w ∈ Ioo (-3) 3, deriv τ w ≠ 0) ∧
      (StrictMonoOn τ (Ioo (-3) 3) ∨ StrictAntiOn τ (Ioo (-3) 3)) := by
  refine arcLiftOfLevelCurvesOn L i isOpen_Ioo isPreconnected_Ioo ?_ ?_ hJα
  · intro w hw
    exact (contMDiffOn_arcUpPt D hη hη1 hlam0pos hlam0).contMDiffAt
      (Ioo_mem_nhds hw.1 hw.2)
  · intro w hw
    exact mfderiv_arcUpPt_ne_zero D hη hη1 hlam0pos hlam0 hZrel hZsm hw

/-- **The arc lift of the lower model arc** (the `τL` of the design's §1.4). -/
theorem exists_arcReparam_dn {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {Z : M → ℂ}
    {lam0 η : ℝ} (hη : 0 < η) (hη1 : |η| ≤ 1) (hlam0pos : 0 < lam0)
    (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ x : M, Work.Drive.N2Lead.chartCplx D x = (lam0 : ℂ) * Z x)
    (hZsm : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ,ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x)
    {a : ℝ} {n : ℕ} (L : LevelCurves f a n) (i : Fin n)
    (hJα : ∀ w ∈ Ioo (-3) 3, arcDnPt D lam0 η w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ (Ioo (-3) 3) ∧
      (∀ w ∈ Ioo (-3) 3, L.γ i (τ w) = arcDnPt D lam0 η w) ∧
      (∀ w ∈ Ioo (-3) 3, deriv τ w ≠ 0) ∧
      (StrictMonoOn τ (Ioo (-3) 3) ∨ StrictAntiOn τ (Ioo (-3) 3)) := by
  refine arcLiftOfLevelCurvesOn L i isOpen_Ioo isPreconnected_Ioo ?_ ?_ hJα
  · intro w hw
    exact (contMDiffOn_arcDnPt D hη hη1 hlam0pos hlam0).contMDiffAt
      (Ioo_mem_nhds hw.1 hw.2)
  · intro w hw
    exact mfderiv_arcDnPt_ne_zero D hη hη1 hlam0pos hlam0 hZrel hZsm hw

end Arcs

end Work.Drive.N2C
