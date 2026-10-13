/-
# `Assembly/RegQAux.lean` — the `RegQ`-algebra needed by the `Assembly` layer, self-contained

The `Assembly` layer uses exactly four `RegQ`-closure rules

* `regQ_mono` (`RegQ α k f → l ≤ k → RegQ α l f`),
* `regQ_smul` (`RegQ α k f → RegQ α k (c · f)`),
* `regQ_add` (`RegQ α k f → RegQ α k g → RegQ α k (f + g)`),
* `regQ_sub` (the last two combined).

In the tree these are provided by `Work.FTS.Apriori.RegQApi`, which imports the
`EllipticEst` certificate cone; that cone is much larger than the coercivity development needs
(and is currently in flux).  This module re-states the four rules in the `Assembly` namespace
with *small* imports, so that `Assembly.All` builds from `Spaces`/`LocData` alone:

* `regQ_mono` is the `Work.FTS.GalerkinFix.RegQ.regQ_mono` of the clean
  `GalerkinFix`-cone;
* `HkMem_add_open` is the `α`-generic version from
  `Work.FTS.EllipticEst.RPFresh.straight_transfers`;
* everything else (`mixed_const_mul`, `mixed_add_quad`, the `BdryTraces` algebra) is proved
  here from `SmoothQuad` data, exactly as in `RegQApi`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Nonlin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Monotonicity in the order -/

/-- **`RegQ` descends in the order**: `RegQ α k f → l ≤ k → RegQ α l f`. -/
theorem regQ_mono {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (hf : RegQ α k f) : RegQ α l f :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono hf hkl

/-! ## Scalar homogeneity of the iterated operators (unconditional) -/

private theorem deriv_const_mul' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul']

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul']

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- **The mixed operators are scalar homogeneous** (unconditionally). -/
theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Additivity of the iterated operators on the open quadrant (`SmoothQuad` data) -/

private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter j a z θ + Work.Spaces.DzIter j b z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **The mixed operators `D_z^jD_θ^i` are additive on the open quadrant** for `SmoothQuad`
data. -/
theorem mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## `RegQ` is closed under multiplication by a constant -/

private theorem bdryTraces_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (htr : BdryTraces α k f) : BdryTraces α k (fun z θ => c * f z θ) := by
  intro a b hab
  have hfab := htr a b hab
  have hfun : ∀ z θ, Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed b a f z θ := by
    intro z θ
    rw [mixed_const_mul]
  have hz : ∀ θ, (fun z => z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
        * Work.Spaces.w z) ^ 2)
      = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) := by
    intro θ
    funext z
    show z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ * Work.Spaces.w z) ^ 2
      = c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
    rw [hfun z θ]; ring
  have ht : ∀ z, (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2)
      = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    intro z
    funext θ
    show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2
      = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2)
    rw [hfun z θ]; ring
  constructor
  · intro θ hθ
    have h := hfab.1 θ hθ
    constructor
    · rw [hz θ]
      simpa using h.1.const_mul (c ^ 2)
    · rw [hz θ]
      simpa using h.2.const_mul (c ^ 2)
  · intro z hzmem
    have h := hfab.2 z hzmem
    constructor
    · rw [ht z]
      simpa using h.1.const_mul (c ^ 2)
    · rw [ht z]
      simpa using h.2.const_mul (c ^ 2)

/-- **`RegQ` is closed under multiplication by a constant.** -/
theorem regQ_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) : RegQ α k (fun z θ => c * f z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α k c hf.2.1, bdryTraces_smul c hf.2.2⟩

/-! ## `RegQ` is closed under addition -/

/-- `SmoothQuad` data is `SmoothOpen` (the open quadrant is contained in the half-strip of
`SmoothQuad`). -/
private theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data (the `α`-generic version, with the
domination of `HkIntegrand_add_le_open`). -/
theorem HkMem_add_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hfg.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have htarget : MeasureTheory.IntegrableOn
        (fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
        Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine MeasureTheory.Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ

/-- Additivity of `BdryTraces`: by `mixed_add_quad` the boundary limits of the sum are those
of the sum of the limits, and `z ≥ 0` resp. `sin(2θ)^{1-γ} ≥ 0` let the squeeze theorem
conclude. -/
theorem bdryTraces_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (htf : BdryTraces α k f) (htg : BdryTraces α k g) :
    BdryTraces α k (fun z θ => f z θ + g z θ) := by
  intro a b hab
  have hfab := htf a b hab
  have hgab := htg a b hab
  have hpt : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ :=
    fun z θ hz h1 h2 => mixed_add_quad hsmf hsmg b a z θ (by linarith) h1 h2
  have hwsq : ∀ z θ, (Work.Spaces.w z
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ)) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2 := by
    intro z θ
    nlinarith [sq_nonneg (Work.Spaces.w z * Work.Spaces.mixed b a f z θ
        - Work.Spaces.w z * Work.Spaces.mixed b a g z θ)]
  have hssq : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) ^ 2
      ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2)
        + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z θ hθ
    have h1 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ), h1]
  constructor
  · intro θ hθ
    have hA := hfab.1 θ hθ
    have hB := hgab.1 θ hθ
    have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimT : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) atTop (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hsq : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt (Set.mem_Ioi.mp hzmem)) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt (Set.mem_Ioi.mp hzmem)]
    have hsqT : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimT ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt hzmem) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt hzmem]
    exact ⟨hsq, hsqT⟩
  · intro z hzmem
    have hA := hfab.2 z hzmem
    have hB := hgab.2 z hzmem
    have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimL : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hmemGT : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hmemLT : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hsq : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [hmemGT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemGT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    have hsqL : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimL ?_ ?_
      · filter_upwards [hmemLT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemLT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    exact ⟨hsq, hsqL⟩

/-- **`RegQ` is closed under addition.** -/
theorem regQ_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_add hf.1 hg.1,
    HkMem_add_open α k
      (smoothOpen_of_smoothQuad hf.1)
      (smoothOpen_of_smoothQuad hg.1) hf.2.1 hg.2.1,
    bdryTraces_add hf.1 hg.1 hf.2.2 hg.2.2⟩

/-! ## Derived closure properties -/

/-- `RegQ` contains the zero profile. -/
theorem regQ_zero (α : ℝ) (k : ℕ) : RegQ α k (fun _ _ : ℝ => (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  refine ⟨hsm, Work.FTS.EllipticEst.HkMem_zero α k, ?_⟩
  intro a b _
  have hmix : Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
    have h := mixed_const_mul (0 : ℝ) (fun _ _ : ℝ => (1 : ℝ)) b a
    simpa using h
  have hmix_pt : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
    fun z θ => congrFun (congrFun hmix z) θ
  constructor
  · intro θ _
    have hz : (fun z => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
        * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
      funext z
      show z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.w z) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [hz]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · intro z _
    have ht : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [ht]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-- `RegQ` is closed under negation. -/
theorem regQ_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hf : RegQ α k f) :
    RegQ α k (fun z θ => -f z θ) := by
  have h := regQ_smul (α := α) (k := k) (-1) hf
  simpa using h

/-- `RegQ` is closed under subtraction. -/
theorem regQ_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ - g z θ) := by
  have h := regQ_add hf (regQ_neg hg)
  simpa [sub_eq_add_neg] using h

/-- `RegQ` is closed under finite linear combinations. -/
theorem regQ_finset_sum {α : ℝ} {k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ → ℝ) (hF : ∀ i ∈ s, RegQ α k (F i)) :
    RegQ α k (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      exact regQ_zero α k
  | insert a s' ha ih =>
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]; rfl
      rw [hsum]
      refine regQ_add (regQ_smul (c a) (hF a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end Work.FTS.CoercivityFix.Assembly
