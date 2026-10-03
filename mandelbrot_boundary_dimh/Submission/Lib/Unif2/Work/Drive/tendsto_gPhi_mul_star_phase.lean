import Mathlib
import Submission.Lib.Unif2.Work.Drive.phaseChainDefs
import Submission.Lib.Unif2.Work.Drive.continuousAt_gadget
import Submission.Lib.Unif2.Work.Drive.tendsto_gPhi_at_pivot

/-!
# The normalized limit of the telescoping product at the base point

`Work.Drive.gPhi a ρ = ∏ᶠ i, gadget a ρ i` is the locally finite product of the transfer gadgets
of the pivot chain `a` with radii `ρ` (see `Submission/Work/Drive/phaseChainDefs.lean`).  At the
first pivot `z₀ = a 0` the gadget `gadget a ρ 0` is *singular*: in the chart at `z₀` it equals
`phase (d x / (d x - q))` with `d x = (chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀ → 0` and `q ≠ 0` fixed, so
that its phase has no limit (all directions occur).

Multiplying it by the conjugate of the phase of `d x` repairs this:  for `z`, `w ≠ 0`

  `phase (z / w) * conj (phase z) = conj (phase w)`,

so that in the chart at `z₀`

  `gadget a ρ 0 x * conj (phase (d x)) = conj (phase ((chartAt ℂ z₀) x - (chartAt ℂ z₀) (a 1)))`,

which tends to `conj (phase ((chartAt ℂ z₀) z₀ - (chartAt ℂ z₀) (a 1)))`, a non-zero unit complex
number.  Since all the other gadgets are continuous and non-zero at `z₀` (local finiteness makes
the product finite near `z₀`, and no other pivot equals `z₀` by injectivity of `a`), the whole
normalized product `gPhi a ρ · conj (phase d)` has a non-zero limit at `z₀` along the punctured
neighbourhood.  This is exactly the "`Θ / d` has a non-zero continuous extension at `z₀`" step of
the degree-one phase construction (`Submission/Work/Drive/exists_continuous_singleZero_phase.lean`).
-/

open Filter Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.Drive

/-- For non-zero `z` and `w`, `phase (z / w) * conj (phase z) = conj (phase w)`. -/
lemma phase_div_mul_star_phase {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    phase (z / w) * star (phase z) = star (phase w) := by
  have h1 : phase (z / w) * star (phase z) = phase ((z / w) / z) :=
    (phase_div_of_ne_zero (div_ne_zero hz hw) hz).symm
  rw [h1]
  have h2 : (z / w) / z = w⁻¹ := by field_simp
  rw [h2, phase_inv_eq_conj hw]
  simp

theorem tendsto_gPhi_mul_star_phase {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : ℕ → X} {ρ : ℕ → ℝ} {z₀ : X}
    (ha0 : a 0 = z₀)
    (hρ : ∀ i, 0 < ρ i)
    (hinj : Function.Injective a)
    (hstep : ∀ i, a (i + 1) ∈ Work.Drive.gB a ρ i)
    (hwell : ∀ i, closure (Work.Drive.gU a ρ i) ⊆ (chartAt ℂ (a i)).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ Work.Drive.gU a ρ i).Nonempty}.Finite) :
    ∃ u₀ : ℂ, u₀ ≠ 0 ∧ Filter.Tendsto (fun x : X =>
        Work.Drive.gPhi a ρ x * star (Work.Drive.phase ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀)))
      (nhdsWithin z₀ {z₀}ᶜ) (nhds u₀) := by
  classical
  rw [← ha0]
  -- ### 1. Only finitely many gadgets are non-trivial near the base point
  obtain ⟨F₀, hF₀⟩ := exists_finset_eventually_gadget_ne_one hρ hlf (a 0)
  set F : Finset ℕ := insert 0 F₀ with hF
  have h0F : (0 : ℕ) ∈ F := by rw [hF]; exact Finset.mem_insert_self 0 F₀
  have hFev : ∀ᶠ y in 𝓝 (a 0), ∀ i : ℕ, gadget a ρ i y ≠ 1 → i ∈ F :=
    hF₀.mono fun y hy i hi => by
      rw [hF]; exact Finset.mem_insert_of_mem (hy i hi)
  -- the product splits off the singular gadget `0`
  have hsplit : ∀ᶠ y in 𝓝 (a 0),
      gPhi a ρ y = gadget a ρ 0 y * ∏ i ∈ F.erase 0, gadget a ρ i y := by
    filter_upwards [hFev] with y hy
    rw [gPhi_eq_prod_of hy]
    conv_lhs => rw [← Finset.insert_erase h0F]
    rw [Finset.prod_insert (Finset.notMem_erase 0 F)]
  -- ### 2. The complement product is continuous and non-zero at the base point
  have hrest_tend : Filter.Tendsto (fun y : X => ∏ i ∈ F.erase 0, gadget a ρ i y) (𝓝 (a 0))
      (𝓝 (∏ i ∈ F.erase 0, gadget a ρ i (a 0))) := by
    refine tendsto_finsetProd _ (fun i hi => ?_)
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hne1 : a 0 ≠ a i := fun h => hi0 (hinj h).symm
    have hne2 : a 0 ≠ a (i + 1) := fun h => Nat.succ_ne_zero i (hinj h).symm
    exact (continuousAt_gadget (hρ i) (norm_gQ_sub_gP_lt hρ hstep i) (step_src hstep i)
      (hwell i) hne1 hne2).tendsto
  have hrest_ne : (∏ i ∈ F.erase 0, gadget a ρ i (a 0)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    exact gadget_ne_zero_of_ne_pivots (step_src hstep i)
      (fun h => hi0 (hinj h).symm) (fun h => Nat.succ_ne_zero i (hinj h).symm)
  -- ### 3. The normalized singular gadget has a non-zero limit
  have hpq : (chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1) ≠ 0 :=
    sub_ne_zero.mpr fun h => Nat.succ_ne_zero 0 (hinj ((chartAt ℂ (a 0)).injOn
      (step_src hstep 0) (mem_chart_source ℂ (a 0)) h.symm))
  have hsrc_ev : ∀ᶠ y in 𝓝 (a 0), y ∈ (chartAt ℂ (a 0)).source :=
    (chartAt ℂ (a 0)).open_source.mem_nhds (mem_chart_source ℂ (a 0))
  have hne_ev : ∀ᶠ y in 𝓝 (a 0), y ≠ a 1 :=
    eventually_ne_nhds fun h => Nat.succ_ne_zero 0 (hinj h.symm)
  have hball_ev : ∀ᶠ y in 𝓝 (a 0),
      ‖(chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0)‖ < 2 * ρ 0 := by
    have hcont : ContinuousAt (fun y : X =>
        ‖(chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0)‖) (a 0) :=
      (((chartAt ℂ (a 0)).continuousAt (mem_chart_source ℂ (a 0))).sub continuousAt_const).norm
    have hlt : ‖(chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 0)‖ < 2 * ρ 0 := by
      rw [sub_self, norm_zero]; linarith [hρ 0]
    exact hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
  -- on the punctured neighbourhood the normalized gadget *is* a nice phase
  have hev_pair : (fun y : X => gadget a ρ 0 y *
        star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0))))
      =ᶠ[𝓝[≠] (a 0)]
      (fun y : X => star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 1)))) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hsrc_ev,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hne_ev,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hball_ev] with y hy hy1 hy2 hy3
    have hA : (chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0) ≠ 0 :=
      sub_ne_zero.mpr fun h =>
        hy ((chartAt ℂ (a 0)).injOn hy1 (mem_chart_source ℂ (a 0)) h)
    have hB : (chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 1) ≠ 0 :=
      sub_ne_zero.mpr fun h =>
        hy2 ((chartAt ℂ (a 0)).injOn hy1 (step_src hstep 0) h)
    rw [gadget_eq_phase (a := a) (ρ := ρ) (i := 0) ⟨hy1, le_of_lt hy3⟩]
    exact phase_div_mul_star_phase hA hB
  have hpair_lim : Filter.Tendsto (fun y : X =>
        star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 1))))
      (𝓝[≠] (a 0))
      (𝓝 (star (phase ((chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1))))) := by
    have hc : Filter.Tendsto (fun y : X => (chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 1))
        (𝓝 (a 0)) (𝓝 ((chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1))) :=
      (((chartAt ℂ (a 0)).continuousAt (mem_chart_source ℂ (a 0))).sub
        continuousAt_const).tendsto
    exact (tendsto_phase_of_tendsto (hc.mono_left nhdsWithin_le_nhds) hpq).star
  have hpair : Filter.Tendsto (fun y : X => gadget a ρ 0 y *
        star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0))))
      (𝓝[≠] (a 0))
      (𝓝 (star (phase ((chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1))))) :=
    hpair_lim.congr' hev_pair.symm
  -- ### 4. Assembly
  refine ⟨(∏ i ∈ F.erase 0, gadget a ρ i (a 0)) *
      star (phase ((chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1))),
    mul_ne_zero hrest_ne (star_ne_zero.mpr (phase_ne_zero hpq)), ?_⟩
  have hmain : Filter.Tendsto (fun y : X => (∏ i ∈ F.erase 0, gadget a ρ i y) *
      (gadget a ρ 0 y * star (phase ((chartAt ℂ (a 0)) y - (chartAt ℂ (a 0)) (a 0)))))
      (𝓝[≠] (a 0)) (𝓝 ((∏ i ∈ F.erase 0, gadget a ρ i (a 0)) *
        star (phase ((chartAt ℂ (a 0)) (a 0) - (chartAt ℂ (a 0)) (a 1))))) :=
    (hrest_tend.mono_left nhdsWithin_le_nhds).mul hpair
  refine hmain.congr' ?_
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hsplit] with y hy
  rw [hy]; ring

end Work.Drive
