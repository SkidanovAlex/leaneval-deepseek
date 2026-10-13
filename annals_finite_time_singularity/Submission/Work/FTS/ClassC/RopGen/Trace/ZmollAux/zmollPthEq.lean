/-
# `zmollPthEq` — the angular derivative of the log-radial mollification

The double mollification `Φ_{δ,ε} = zmoll G δ ε` of `PkgK5.K5c.MollDefs` is the iterated
integral

  `Φ z θ = ∫_t sKer δ (log z - t) · thMoll G ε (exp t) θ`

of the angular mollification of the datum against the log-radial kernel `sKer δ`.  This file
computes its *angular* derivative: for `z > 0` and `θ ∈ Iθ`,

  `∂_θ Φ z θ = ∫_t sKer δ (log z - t) · (∫_s sKerd ε (θ - s) · Qext G (exp t) s)`,

i.e. the derivative may be moved inside the `t`-integral (dominated convergence: the
`θ`-derivative of the angular mollification is dominated, in `t`, by
`3 Mε · ∫_{Iθ} |Hxyc G t s|`, by `kernelSliceBound`, and that function is locally integrable by
`hdom`), and the inner `θ`-derivative is the angular convolution with the derivative kernel
(`thMoll_hasDerivAt`).

Together with `logConvDeriv` (the chain rule for the log-radial variable) this gives the
identification of the mixed derivative `D_z∂_θ Φ` used by the Fatou step of the mollification
transfer.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.kernelSliceBound
import Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.hxycSliceAESM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext thMoll zmoll sKer)
open Work.FTS.EllSol.EllPkgAux (sKerd Hxyc)

/-! ## A bound for compactly supported continuous kernels -/

/-- A continuous kernel vanishing outside `[-ε, ε]` with `ε > 0` is bounded on all of `ℝ`. -/
theorem exists_kernel_bound {k : ℝ → ℝ} (hk : Continuous k) {ε : ℝ} (hε0 : 0 < ε)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x : ℝ, |k x| ≤ M) ∧ (∀ x : ℝ, ε < |x| → k x = 0) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -ε) (b := ε)).exists_bound_of_continuousOn
    hk.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, hvan⟩
  intro x
  by_cases hx : x ∈ Set.Icc (-ε) ε
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · have hz : k x = 0 := by
      refine hvan x ?_
      rw [Set.mem_Icc, not_and_or] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    rw [hz, abs_zero]
    exact le_max_right _ _

/-! ## The packaged slice bound -/

/-- `kernelSliceBound` packaged along the parameter `t ↦ exp t`. -/
theorem kernel_slice_le (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, |k x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → k x = 0) :
    ∀ (t θ' : ℝ), θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) →
      |∫ s : ℝ, k (θ' - s) * Qext G (Real.exp t) s|
        ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Hxyc G t s| := by
  intro t θ' hθ'
  have h := kernelSliceBound G (Real.exp t)
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
    hk hε0 hε1 hM0 hM hvan hθ'
  simpa only [Hxyc] using h

/-! ## The angular derivative of `zmoll` -/

/-- **The angular derivative of the log-radial mollification.** -/
theorem zmollPthEq (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Hxyc G t s|) MeasureTheory.volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pth (zmoll G δ ε) z θ
      = ∫ t : ℝ, sKer δ (Real.log z - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- bounds for the kernels
  obtain ⟨Mδ, hMδ0, hMδb, hMδv⟩ := exists_kernel_bound
    ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous) hδ0
    (fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 (le_of_lt hx))
  obtain ⟨M₁, hM₁0, hM₁b, hM₁v⟩ := exists_kernel_bound
    ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous) hε0
    (fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 (le_of_lt hx))
  obtain ⟨M₂, hM₂0, hM₂b, hM₂v⟩ := exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  -- a common bound `Mε` for both angular kernels
  set Mε : ℝ := max M₁ M₂ with hMεdef
  have hMε0 : 0 ≤ Mε := by rw [hMεdef]; exact le_max_of_le_left hM₁0
  have hMεKer : ∀ x : ℝ, |sKer ε x| ≤ Mε := fun x => by
    rw [hMεdef]; exact le_trans (hM₁b x) (le_max_left _ _)
  have hMεKerd : ∀ x : ℝ, |sKerd ε x| ≤ Mε := fun x => by
    rw [hMεdef]; exact le_trans (hM₂b x) (le_max_right _ _)
  have hkε : Continuous (sKer ε) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
  have hvanε : ∀ x : ℝ, ε < |x| → sKer ε x = 0 :=
    fun x hx => Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 (le_of_lt hx)
  have hkεd : Continuous (sKerd ε) :=
    Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε
  have hvanεd : ∀ x : ℝ, ε < |x| → sKerd ε x = 0 :=
    fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx
  -- `θ` lies in the wider window on which `thMoll_hasDerivAt` is available
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the auxiliary objects
  let Gfn : ℝ → ℝ := fun u : ℝ => ∫ s in Work.Spaces.Iθ, |Hxyc G u s|
  let K : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ)
  let bound : ℝ → ℝ := fun t : ℝ => Mδ * (3 * Mε) * K.indicator Gfn t
  let F : ℝ → ℝ → ℝ := fun θ' t : ℝ => sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ'
  let F' : ℝ → ℝ → ℝ := fun θ' t : ℝ => sKer δ (Real.log z - t)
    * (∫ s : ℝ, sKerd ε (θ' - s) * Qext G (Real.exp t) s)
  have hKc : IsCompact K := isCompact_Icc
  have hKmeas : MeasurableSet K := measurableSet_Icc
  have hbound_int : Integrable bound MeasureTheory.volume := by
    have h : Integrable (K.indicator Gfn) MeasureTheory.volume :=
      (integrable_indicator_iff hKmeas).mpr (hdom.integrableOn_isCompact hKc)
    exact h.const_mul (Mδ * (3 * Mε))
  -- ## measurability of the sliced convolutions
  have hmeas_k : ∀ (k : ℝ → ℝ), Continuous k → (∀ x : ℝ, ε < |x| → k x = 0) →
      ∀ θ' : ℝ, θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) →
      AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)
        * (∫ s : ℝ, k (θ' - s) * Hxyc G t s))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro k hk hvan θ' hθ'
    have hsm : AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ' - s) * Hxyc G t s)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      hxycSliceAESM G hS hk hε0 hε1 hvan hθ'
    have hcont : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
      ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
        (continuous_const.sub continuous_id)
    exact hcont.aestronglyMeasurable.mul hsm
  -- ## the small-window helper
  have hsmall : ∀ θ' : ℝ, θ' ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8) →
      θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    intro θ' hθ'
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ'
    obtain ⟨h3, h4⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- ## the seven hypotheses of the parametric integral theorem
  have hs : Set.Ioo (θ - 1 / 8) (θ + 1 / 8) ∈ 𝓝 θ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable (F θ')
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine Filter.Eventually.mono (Ioo_mem_nhds (show θ - 1 / 4 < θ by linarith)
      (show θ < θ + 1 / 4 by linarith)) ?_
    intro θ' hθ'
    have hθ'w : θ' ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
      obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ'
      obtain ⟨h3, h4⟩ := Set.mem_Icc.mp hθ
      exact ⟨by linarith, by linarith⟩
    exact hmeas_k (sKer ε) hkε hvanε θ' hθ'w
  have hF_int : Integrable (F θ) MeasureTheory.volume := by
    refine Integrable.mono' hbound_int (hF_meas.self_of_nhds) (Filter.Eventually.of_forall ?_)
    intro t
    show ‖sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ‖
      ≤ Mδ * (3 * Mε) * K.indicator Gfn t
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have h1 : |∫ s : ℝ, sKer ε (θ - s) * Qext G (Real.exp t) s| ≤ 3 * Mε * Gfn t :=
        kernel_slice_le G hT hkε hε0 hε1 hMε0 hMεKer hvanε t θ hθw
      have h1' : |thMoll G ε (Real.exp t) θ| ≤ 3 * Mε * Gfn t := h1
      rw [Real.norm_eq_abs, abs_mul]
      calc |sKer δ (Real.log z - t)| * |thMoll G ε (Real.exp t) θ|
          ≤ Mδ * (3 * Mε * Gfn t) := mul_le_mul (hMδb _) h1' (abs_nonneg _) hMδ0
        _ = Mδ * (3 * Mε) * Gfn t := by ring
    · rw [Set.indicator_of_notMem ht]
      have hzK : δ ≤ |Real.log z - t| := by
        have hmem : t ∉ Set.Icc (Real.log z - δ) (Real.log z + δ) := ht
        rw [Set.mem_Icc, not_and_or] at hmem
        rcases hmem with h | h
        · rw [abs_of_pos (by linarith)]
          linarith
        · rw [abs_of_neg (by linarith)]
          linarith
      rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 hzK, zero_mul, norm_zero]
      simp
  have hF'_meas : AEStronglyMeasurable (F' θ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    hmeas_k (sKerd ε) hkεd hvanεd θ hθw
  have h_bound : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8), ‖F' x t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t x hx => ?_)
    show ‖sKer δ (Real.log z - t)
        * (∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s)‖
      ≤ Mδ * (3 * Mε) * K.indicator Gfn t
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have h1 : |∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s| ≤ 3 * Mε * Gfn t :=
        kernel_slice_le G hT hkεd hε0 hε1 hMε0 hMεKerd hvanεd t x (hsmall x hx)
      rw [Real.norm_eq_abs, abs_mul]
      calc |sKer δ (Real.log z - t)| * |∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s|
          ≤ Mδ * (3 * Mε * Gfn t) := mul_le_mul (hMδb _) h1 (abs_nonneg _) hMδ0
        _ = Mδ * (3 * Mε) * Gfn t := by ring
    · rw [Set.indicator_of_notMem ht]
      have hzK : δ ≤ |Real.log z - t| := by
        have hmem : t ∉ Set.Icc (Real.log z - δ) (Real.log z + δ) := ht
        rw [Set.mem_Icc, not_and_or] at hmem
        rcases hmem with h | h
        · rw [abs_of_pos (by linarith)]
          linarith
        · rw [abs_of_neg (by linarith)]
          linarith
      rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0 hzK, zero_mul, norm_zero]
      simp
  have h_diff : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ x ∈ Set.Ioo (θ - 1 / 8) (θ + 1 / 8), HasDerivAt (F · t) (F' x t) x := by
    refine Filter.Eventually.of_forall (fun t x hx => ?_)
    have hxw : x ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := hsmall x hx
    have hd := Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
      (Q := fun s : ℝ => Qext G (Real.exp t) s)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hε0 hε1 hMεKerd hxw
    have h2 := hd.const_mul (sKer δ (Real.log z - t))
    show HasDerivAt (fun θ' : ℝ => sKer δ (Real.log z - t) * thMoll G ε (Real.exp t) θ')
      (sKer δ (Real.log z - t)
        * (∫ s : ℝ, sKerd ε (x - s) * Qext G (Real.exp t) s)) x
    exact h2
  -- ## the parametric integral theorem
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (F := F) (F' := F') (x₀ := θ) (s := Set.Ioo (θ - 1 / 8) (θ + 1 / 8))
    (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hderiv := hmain.2
  show deriv (fun θ' : ℝ => ∫ a, F θ' a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) θ
    = ∫ t : ℝ, sKer δ (Real.log z - t) * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)
  rw [hderiv.deriv]
  rfl

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
