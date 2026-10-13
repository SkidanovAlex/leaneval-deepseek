import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR1.SliceDiffAux
import Submission.Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXR1.pthIter_le_of_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.slice_diff_weighted`

The mixed slots of order `≤ 1` of the difference of two slices `slice g τ - slice g τ'` of a
`LimApprox` family decay like the weight `z^{3/2}/(1+z)²`, uniformly on every horizon `[0,T]`,
with a Lipschitz factor `|τ - τ'|` in the fake time.

The proof has three ingredients.

* The approximating families `gn` of the `LimApprox` clause are class-`C` on every slice, and
  `ClassC` is a subspace, so the *difference* `H_n := slice (gn n) τ - slice (gn n) τ'` is again
  class-`C`; `classC_sub_hyp` then supplies `SmoothOpen`, `HkMem β 4` and `BdryTraces β 4` for it,
  so the weighted slot bound `hw` applies at every order `a + b ≤ 2`:
  `|mixed b a H_n| ≤ Cw · SliceW z · |H_n|_{ℋ⁴}`, and `|H_n|_{ℋ⁴} ≤ L|τ - τ'|` is the Lipschitz
  clause of `LimApprox`.
* The `Qd`-jet convergence clause identifies the pointwise limits of `mixed b a H_n` with the
  *difference of the limit slots* `mixed b a (slice g τ) - mixed b a (slice g τ')`: the identity
  `mixed b a (F - G) = mixed b a F - mixed b a G` holds on the open quadrant for the smooth
  approximants (`TTSlot11Aux.mixed_sub_open`).
* At order `≤ 1` the slot of the *limit difference* `mixed b a (slice g τ - slice g τ')` equals the
  difference of the limit slots: for `(b,a) = (0,0)` this is definitional; for `(1,0)` and
  `(0,1)` it is the "derivative of a pointwise limit" statement, which holds because the
  first-order approximant slots are equi-Lipschitz on compacts (`hw` at orders `1` and `2` supply
  the uniform bounds `pzIter_bound_weighted` / `pthIter_le_of_weighted`), so the limit is
  differentiable with the pointwise limit of the derivatives as derivative
  (`hasDerivAt_of_tendsto_deriv`).
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `θ`-derivative of the `θ`-slice** of a function `C^∞` on the open quadrant (companion of
`EllipticEst.SmoothOpen.hasDerivAt_slice`). -/
theorem smoothOpen_hasDerivAt_thslice {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' : ℝ => f z θ') (Work.Spaces.pthIter 1 f z θ) θ :=
  (((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

theorem slice_diff_weighted {β C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hA : Work.FTS.FinalV2.LimApprox β C₀ Φs E g)
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem β 4 f →
      Work.FTS.Nonlin.BdryTraces β 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm β 4 f)
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
  obtain ⟨Cw, hCw0, hwraw⟩ := hw
  have hwB : HwBnd β Cw := fun f h1 h2 h3 b a hab z θ hz hθ hθ2 => hwraw f h1 h2 h3 b a hab z θ hz hθ hθ2
  obtain ⟨Kz, hKz0, hzbd⟩ := pzIter_bound_weighted hCw0 hwB
  obtain ⟨Kt, hKt0, htbd⟩ := pthIter_le_of_weighted hCw0 hwB
  obtain ⟨gn, B, L₀, hC, hLip, hjet, hmu⟩ := hA T hT
  refine ⟨Cw * max L₀ 0, mul_nonneg hCw0 (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hL0 : (0 : ℝ) ≤ max L₀ 0 := le_max_right _ _
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  -- ## step 1: the approximant differences are honest class-`C⁴` data
  have hsmH : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).1
  have hmemH : ∀ n : ℕ, Work.Spaces.HkMem β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).2.1
  have htrH : ∀ n : ℕ, Work.FTS.Nonlin.BdryTraces β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) :=
    fun n => (classC_sub_hyp (hC n τ hτ).1 (hC n τ' hτ').1).2.2
  have hHk : ∀ n : ℕ, Work.Spaces.HkNorm β 4
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
      ≤ max L₀ 0 * |τ - τ'| := by
    intro n
    exact (hLip n τ hτ τ' hτ').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  -- ## step 2: the uniform weighted bound on the approximant differences, all orders `≤ 2`
  have hmain : ∀ n : ℕ, ∀ b a : ℕ, a + b ≤ 2 →
      |Work.Spaces.mixed b a
        (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
        z θ| ≤ Cw * SliceW z * (max L₀ 0 * |τ - τ'|) := by
    intro n b a hab2
    exact (hwB _ (hsmH n) (hmemH n) (htrH n) b a hab2 z θ hz hθ0 hθ1).trans
      (mul_le_mul_of_nonneg_left (hHk n) (mul_nonneg hCw0 (SliceW_nonneg hz.le)))
  -- ## step 3: the pointwise limit slot
  have hsub : ∀ n : ℕ, Work.Spaces.mixed b a
      (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ
      = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ :=
    fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
      (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
  set Lam : ℝ := Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
    - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ with hLam
  have hLamBd : |Lam| ≤ Cw * SliceW z * (max L₀ 0 * |τ - τ'|) := by
    have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed b a
        (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
        z θ) atTop (𝓝 Lam) := by
      rw [show (fun n : ℕ => Work.Spaces.mixed b a
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z θ)
        = fun n : ℕ => (Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ) from
        funext (fun n => hsub n)]
      rw [hLam]
      exact (hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)
    exact le_of_tendsto hconv.abs (Eventually.of_forall (fun n => hmain n b a (by omega)))
  -- ## step 4: the case analysis
  rcases (by omega : b = 0 ∧ a = 0 ∨ b = 1 ∧ a = 0 ∨ b = 0 ∧ a = 1)
    with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `(b,a) = (0,0)`: the slot is the value itself
    have heq : |Work.Spaces.mixed 0 0
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| = |Lam| := by
      rw [hLam]
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Pi.sub_apply]
    rw [heq]
    exact hLamBd.trans (le_of_eq (by ring))
  · -- `(b,a) = (1,0)`
    have hzint : z ∈ Set.Ioo (z / 2) (2 * z + 1) := ⟨by linarith, by linarith⟩
    have hder : ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        HasDerivAt (fun z'' : ℝ => Work.FTS.Galerkin.slice (gn n) τ z'' θ
            - Work.FTS.Galerkin.slice (gn n) τ' z'' θ)
          (Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) z' :=
      fun n z' hz' => (hsmH n).hasDerivAt_slice hθ (by linarith [hz'.1, hz])
    have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ
        (fun z' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) (Set.Ioo (z / 2) (2 * z + 1)) :=
      fun n z' hz' => ((hsmH n).hasDerivAt_slice_pzIter 1 hθ (by linarith [hz'.1, hz]))
        |>.differentiableAt.differentiableWithinAt
    have hMd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        |Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ| ≤ M := by
      refine ⟨Kz * Real.sqrt (2 * z + 1) * (max L₀ 0 * |τ - τ'|), by positivity, ?_⟩
      intro n z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      refine ((hzbd _ (hsmH n) (hmemH n) (htrH n) z' θ hz'0 hθ0 hθ1).1).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left
        (SliceW_div_le_sqrt hz hz'.1.le hz'.2.le) hKz0)
        (hHk n) (Work.Spaces.HkNorm_nonneg β 4 _) (by positivity)
    have hLd : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        |deriv (fun z'' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ) z'| ≤ L := by
      refine ⟨Kz * (z / 2) ^ (-(1 : ℝ) / 2) * (max L₀ 0 * |τ - τ'|), by positivity, ?_⟩
      intro n z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have hderiv : deriv (fun z'' : ℝ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ) z'
          = Work.Spaces.pzIter 2 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ :=
        ((hsmH n).hasDerivAt_slice_pzIter 1 hθ hz'0).deriv
      rw [hderiv]
      refine ((hzbd _ (hsmH n) (hmemH n) (htrH n) z' θ hz'0 hθ0 hθ1).2).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left
        (SliceW_div_sq_le hz hz'.1.le) hKz0)
        (hHk n) (Work.Spaces.HkNorm_nonneg β 4 _) (by positivity)
    have hu : ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        Tendsto (fun n : ℕ => Work.FTS.Galerkin.slice (gn n) τ z' θ
            - Work.FTS.Galerkin.slice (gn n) τ' z' θ) atTop
          (𝓝 (Work.FTS.Galerkin.slice g τ z' θ - Work.FTS.Galerkin.slice g τ' z' θ)) := by
      intro z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have h1 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ) z' θ)
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z' θ)) :=
        hjet τ hτ 0 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩
      have h2 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ') z' θ)
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z' θ)) :=
        hjet τ' hτ' 0 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h1.sub h2
    have hv : ∀ z' ∈ Set.Ioo (z / 2) (2 * z + 1),
        Tendsto (fun n : ℕ => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z' θ) atTop
          (𝓝 ((Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z' θ
            - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z' θ) / z')) := by
      intro z' hz'
      have hz'0 : 0 < z' := by linarith [hz'.1, hz]
      have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed 1 0
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z' θ) atTop
          (𝓝 (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z' θ
            - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z' θ)) := by
        rw [show (fun n : ℕ => Work.Spaces.mixed 1 0
            (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
            z' θ)
          = fun n : ℕ => (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice (gn n) τ) z' θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice (gn n) τ') z' θ) from
          funext (fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
            (hC n τ' hτ').1.reg 1 0 z' θ hz'0 hθ0 hθ1)]
        exact (hjet τ hτ 1 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩).sub
          (hjet τ' hτ' 1 0 (by omega) z' θ ⟨hz'0, hθ0, hθ1⟩)
      exact Filter.Tendsto.congr (fun n => by
        rw [Work.FTS_RegExport.RXR1.mixed_one_zero_eq]
        field_simp) (hconv.div_const z')
    have hlim := hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z + 1) (by linarith)
      (u := fun n z'' => Work.FTS.Galerkin.slice (gn n) τ z'' θ
        - Work.FTS.Galerkin.slice (gn n) τ' z'' θ)
      (v := fun n z'' => Work.Spaces.pzIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
        - Work.FTS.Galerkin.slice (gn n) τ' z θ) z'' θ)
      (φ := fun z'' => Work.FTS.Galerkin.slice g τ z'' θ - Work.FTS.Galerkin.slice g τ' z'' θ)
      (γ := fun z'' => (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z'' θ
        - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z'' θ) / z'')
      hder hvdiff hMd hLd hu hv z hzint
    have hident : Work.Spaces.mixed 1 0
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ = Lam := by
      have hfun : (fun z' : ℝ => (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ)
          = fun z' : ℝ => Work.FTS.Galerkin.slice g τ z' θ - Work.FTS.Galerkin.slice g τ' z' θ := by
        funext z'; rfl
      have hd : deriv (fun z' : ℝ =>
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ) z
          = (Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ') z θ) / z := by
        rw [hfun]; exact hlim.deriv
      rw [hLam]
      rw [show Work.Spaces.mixed 1 0
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ
          = z * deriv (fun z' : ℝ =>
              (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z' θ) z from rfl]
      rw [hd]
      field_simp
    rw [hident]
    exact hLamBd.trans (le_of_eq (by ring))
  · -- `(b,a) = (0,1)`
    -- the neighbourhood of `θ` on which `sin (2θ')` stays above `m := min (sin θ) (cos θ)`
    set m : ℝ := min (Real.sin θ) (Real.cos θ) with hmdef
    have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    have hcosθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    have hm : 0 < m := by rw [hmdef]; exact lt_min hsinθ hcosθ
    have hθin : θ ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) := ⟨by linarith, by linarith⟩
    have h2π : (θ + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
    have hsenv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        m ≤ Real.sin (2 * θ') := by
      intro θ' hθ'
      have h1 : θ < 2 * θ' := by linarith [hθ'.1]
      have h2 : 2 * θ' < θ + Real.pi / 2 := by linarith [hθ'.2]
      by_cases hle : 2 * θ' ≤ Real.pi / 2
      · refine le_trans (min_le_left _ _) ?_
        exact Real.monotoneOn_sin
          (by constructor <;> linarith [Real.pi_pos])
          (by constructor <;> linarith [Real.pi_pos]) h1.le
      · have hlt : Real.pi / 2 < 2 * θ' := not_le.mp hle
        rw [← Real.sin_pi_sub (2 * θ')]
        refine le_trans (min_le_right _ _) ?_
        have h5 : Real.pi / 2 - θ ≤ Real.pi - 2 * θ' := by linarith
        have h6 : Real.pi - 2 * θ' ≤ Real.pi / 2 := by linarith
        have h7 := Real.monotoneOn_sin
          (by constructor <;> linarith [Real.pi_pos])
          (by constructor <;> linarith [Real.pi_pos]) h5
        rwa [Real.sin_pi_div_two_sub] at h7
    have hθ'pos : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2), 0 < θ' :=
      fun θ' hθ' => by linarith [hθ'.1, hθ0]
    have hθ'lt : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2), θ' < Real.pi / 2 :=
      fun θ' hθ' => by linarith [hθ'.2, hθ1]
    have hdiv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        SliceW z / Real.sin (2 * θ') ≤ SliceW z / m := by
      intro θ' hθ'
      exact div_le_div_of_nonneg_left (SliceW_nonneg hz.le) hm (hsenv θ' hθ')
    have hdivsq : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        SliceW z / (Real.sin (2 * θ') * Real.sin (2 * θ')) ≤ SliceW z / (m * m) := by
      intro θ' hθ'
      refine div_le_div_of_nonneg_left (SliceW_nonneg hz.le) (by positivity) ?_
      exact mul_le_mul (hsenv θ' hθ') (hsenv θ' hθ') hm.le
        (le_trans hm.le (hsenv θ' hθ'))
    have hder : ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        HasDerivAt (fun θ'' : ℝ => Work.FTS.Galerkin.slice (gn n) τ z θ''
            - Work.FTS.Galerkin.slice (gn n) τ' z θ'')
          (Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') θ' :=
      fun n θ' hθ' => smoothOpen_hasDerivAt_thslice (hsmH n) hz
        ⟨hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
    have h2deriv : ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        HasDerivAt (fun θ'' : ℝ => Work.Spaces.pthIter 1 (fun z θ =>
            Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'')
          (Work.Spaces.pthIter 2 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') θ' :=
      fun n θ' hθ' => smoothOpen_hasDerivAt_thslice ((hsmH n).pth) hz
        ⟨hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
    have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ
        (fun θ' : ℝ => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ')
        (Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2)) :=
      fun n θ' hθ' => (h2deriv n θ' hθ').differentiableAt.differentiableWithinAt
    have hMd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        |Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'| ≤ M := by
      refine ⟨Kt * (SliceW z / m) * (max L₀ 0 * |τ - τ'|),
        mul_nonneg (mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) hm.le)) (by positivity), ?_⟩
      intro n θ' hθ'
      refine ((htbd _ (hsmH n) (hmemH n) (htrH n) z θ' hz (hθ'pos θ' hθ')
        (hθ'lt θ' hθ')).1).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hdiv θ' hθ') hKt0) (hHk n)
        (Work.Spaces.HkNorm_nonneg β 4 _) ?_
      exact mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) hm.le)
    have hLd : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        |deriv (fun θ'' : ℝ => Work.Spaces.pthIter 1 (fun z θ =>
            Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'') θ'|
          ≤ L := by
      refine ⟨Kt * (SliceW z / (m * m)) * (max L₀ 0 * |τ - τ'|),
        mul_nonneg (mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) (by positivity))) (by positivity), ?_⟩
      intro n θ' hθ'
      rw [(h2deriv n θ' hθ').deriv]
      refine ((htbd _ (hsmH n) (hmemH n) (htrH n) z θ' hz (hθ'pos θ' hθ')
        (hθ'lt θ' hθ')).2).trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hdivsq θ' hθ') hKt0) (hHk n)
        (Work.Spaces.HkNorm_nonneg β 4 _) ?_
      exact mul_nonneg hKt0 (div_nonneg (SliceW_nonneg hz.le) (by positivity))
    have hu : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        Tendsto (fun n : ℕ => Work.FTS.Galerkin.slice (gn n) τ z θ'
            - Work.FTS.Galerkin.slice (gn n) τ' z θ') atTop
          (𝓝 (Work.FTS.Galerkin.slice g τ z θ' - Work.FTS.Galerkin.slice g τ' z θ')) := by
      intro θ' hθ'
      have hmem : (z, θ') ∈ Work.Construction.Qd := ⟨hz, hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
      have h1 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ) z θ')
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ')) :=
        hjet τ hτ 0 0 (by omega) z θ' hmem
      have h2 : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ') z θ')
          atTop (𝓝 (Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z θ')) :=
        hjet τ' hτ' 0 0 (by omega) z θ' hmem
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
        Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h1.sub h2
    have hv : ∀ θ' ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2),
        Tendsto (fun n : ℕ => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
            - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ') atTop
          (𝓝 ((Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ'
            - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ') / Real.sin (2 * θ'))) := by
      intro θ' hθ'
      have hmem : (z, θ') ∈ Work.Construction.Qd := ⟨hz, hθ'pos θ' hθ', hθ'lt θ' hθ'⟩
      have hsp : Real.sin (2 * θ') ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hsenv θ' hθ'))
      have hconv : Tendsto (fun n : ℕ => Work.Spaces.mixed 0 1
          (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
          z θ') atTop
          (𝓝 (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ'
            - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ')) := by
        rw [show (fun n : ℕ => Work.Spaces.mixed 0 1
            (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ - Work.FTS.Galerkin.slice (gn n) τ' z θ)
            z θ')
          = fun n : ℕ => (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice (gn n) τ) z θ'
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice (gn n) τ') z θ') from
          funext (fun n => Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open (hC n τ hτ).1.reg
            (hC n τ' hτ').1.reg 0 1 z θ' hz (hθ'pos θ' hθ') (hθ'lt θ' hθ'))]
        exact (hjet τ hτ 0 1 (by omega) z θ' hmem).sub (hjet τ' hτ' 0 1 (by omega) z θ' hmem)
      exact Filter.Tendsto.congr (fun n => by
        rw [Work.FTS_RegExport.RXR1.mixed_zero_one_eq]
        field_simp) (hconv.div_const (Real.sin (2 * θ')))
    have hlim := hasDerivAt_of_tendsto_deriv (a := θ / 2) (b := (θ + Real.pi / 2) / 2)
      (by linarith)
      (u := fun n θ'' => Work.FTS.Galerkin.slice (gn n) τ z θ''
        - Work.FTS.Galerkin.slice (gn n) τ' z θ'')
      (v := fun n θ'' => Work.Spaces.pthIter 1 (fun z θ => Work.FTS.Galerkin.slice (gn n) τ z θ
        - Work.FTS.Galerkin.slice (gn n) τ' z θ) z θ'')
      (φ := fun θ'' => Work.FTS.Galerkin.slice g τ z θ'' - Work.FTS.Galerkin.slice g τ' z θ'')
      (γ := fun θ'' => (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ''
        - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ'') / Real.sin (2 * θ''))
      hder hvdiff hMd hLd hu hv θ hθin
    have hsin2 : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hident : Work.Spaces.mixed 0 1
        (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ = Lam := by
      have hfun : (fun θ' : ℝ => (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ')
          = fun θ' : ℝ => Work.FTS.Galerkin.slice g τ z θ' - Work.FTS.Galerkin.slice g τ' z θ' := by
        funext θ'; rfl
      have hd : deriv (fun θ' : ℝ =>
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ') θ
          = (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ) / Real.sin (2 * θ) := by
        rw [hfun]; exact hlim.deriv
      rw [hLam]
      rw [show Work.Spaces.mixed 0 1
          (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ
          = Real.sin (2 * θ) * deriv (fun θ' : ℝ =>
              (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ') θ from rfl]
      rw [hd]
      field_simp
    rw [hident]
    exact hLamBd.trans (le_of_eq (by ring))

end Work.FTS_RegExport.RXR1
