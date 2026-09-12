import Mathlib.Analysis.Calculus.TaylorIntegral
import Submission.Work.NoFlatStop
import Submission.PaperBand.KernelMaximal
import Submission.Commons.Analysis.Calculus.Deriv.ode_contradiction_one_sided

open OptimalMoebius Topology ContDiff
open scoped BigOperators
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat stops are impossible — part 2: the one-variable ODE (GREEN, zero sorry)

The complete proof of `flat_stop_impossible` (see `NoFlatStop.lean` for
part 1, the rotated shape-operator frame).  **A straight kernel segment
through `U = {dN ≠ 0}` cannot end at an interior flat point.**  This
eliminates the S4 ε-contraction machinery (connectors, Lemma 0.4,
Gauss contraction — Bricks D/E) from the global-rigidity argument and is
the local input that closes `no_flat_endpoint_global` /
`bends_reach_boundary_test` (assembly documented in `session_status26`).

## Contents (all green, 0 sorry)
* pullback calculus along affine rays: `deriv_ray`
  (`deriv (fun s => g(x+s•W)) u = fderiv g (x+u•W) W` via Mathlib's
  `DifferentiableAt.deriv_comp_add_smul`), `deriv_eq_zero_of_eventually_zero`;
* constancy of the rotated entries along the arc:
  `fderiv_nfsA_along_arc_zero`, `fderiv_nfsB_along_arc_zero`
  (`A_W = B_W = 0` at arc points);
* `differentiableAt_fderiv_dir` (+ `differentiableAt_dir_nfsA/B/C`) and the
  product-rule `fderiv_mul_apply`;
* `fderiv_iter_zero_of_eq_zero` (iterated derivative of a function
  identically zero on the strip);
* **`ode_arc_point`** — the core computation: at an arc point
  `x = p+u•W`, differentiating `AC − B² ≡ 0` twice in the transverse
  direction `U = perp W` (with `A = B = 0`, `A_U = 0` on the arc) gives
  `A₂·C(x) = 2·(B_U x)²`;
* `A2_eq_CWW` — `A₂ = (C_W)_W` at the arc point (rotated Codazzi + Clairaut
  `secondDirectional_commute_two`);
* **`ode_gamma`** — the ODE `γ·γ'' = 2γ'²` in directional-derivative form;
* the γ-bridges `deriv_gamma_first`, `deriv_gamma_second` (γ(s) := C(p+s•W))
  and `contDiffOn_gamma` (C² on an interval whose image stays interior);
* **`flat_stop_impossible`** — assemble with the commons lemma
  `Commons.Analysis.Calculus.Deriv.ode_contradiction_one_sided` (no smooth
  γ with γ(0)=0, γ≠0 on one side satisfies the ODE).

## Remark on the interval hypotheses
The ODE lemmas take the arc interval `(0, η)` explicitly (`u ∈ Ioo 0 η`,
conditions on `Ioo 0 η`), so they apply at any `u` of an arc even when
`u` is close to `η` (no `(0,u+1)` trick).
-/


noncomputable section
namespace Submission.PaperBand

/-- Pullback derivative along an affine ray: for `g : ℝ² → ℝ` smooth at
`x + u • W`, `deriv (fun s => g (x + s • W)) u = fderiv g (x + u • W) W`. -/
lemma deriv_ray {g : ℝ² → ℝ} {x : ℝ²} (W : ℝ²) {u : ℝ}
    (hd : DifferentiableAt ℝ g (x + u • W)) :
    deriv (fun s : ℝ => g (x + s • W)) u = fderiv ℝ g (x + u • W) W := by
  simpa using DifferentiableAt.deriv_comp_add_smul (x := x) (y := W) (t := u) hd

/-- If `g` is eventually zero near `u` then `deriv g u = 0`. -/
lemma deriv_eq_zero_of_eventually_zero {g : ℝ → ℝ} {u : ℝ}
    (hg : ∀ᶠ s : ℝ in 𝓝 u, g s = 0) : deriv g u = 0 := by
  have heq : g =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hg] with s hs
    rw [hs]
  rw [heq.deriv_eq]
  simp

/-- The rotated `A`-entry is constant (zero) along the arc: its derivative
in the arc direction `W` vanishes at an arc point. -/
lemma fderiv_nfsA_along_arc_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {η u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) η)
    (harc : ∀ u' ∈ Set.Ioo (0 : ℝ) η,
      p + u' • W ∈ stripInterior ∧ dN f (p + u' • W) ≠ 0 ∧ dN f (p + u' • W) W = 0) :
    fderiv ℝ (nfsA f W) (p + u • W) W = 0 := by
  let g : ℝ → ℝ := fun s => nfsA f W (p + s • W)
  have hg0 : ∀ᶠ s : ℝ in 𝓝 u, g s = 0 := by
    rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds isOpen_Ioo hu) with ⟨δ, hδ0, hδ⟩
    filter_upwards [Metric.ball_mem_nhds u hδ0] with s hs
    have hsi : s ∈ Set.Ioo (0 : ℝ) η := by
      exact hδ (by simpa [Metric.mem_ball, Real.dist_eq] using hs)
    rcases harc s hsi with ⟨_, _, hk⟩
    exact nfsA_zero_of_kernel hf (harc s hsi).1 W hk
  have hder : deriv g u = 0 := deriv_eq_zero_of_eventually_zero hg0
  -- and the pullback identity
  have hdg : DifferentiableAt ℝ (nfsA f W) (p + u • W) :=
    differentiableAt_nfsA hf W (p + u • W) (harc u hu).1
  have hpull := deriv_ray (x := p) W (g := nfsA f W) (u := u) hdg
  -- hpull : deriv (fun s => nfsA f W (p + s•W)) u = fderiv nfsA (p+uW) W
  have hpull' : deriv g u = fderiv ℝ (nfsA f W) (p + u • W) W := by
    simpa [g] using hpull
  exact hpull'.symm.trans hder

/-- The rotated `B`-entry is constant (zero) along the arc: its derivative
in the arc direction `W` vanishes at an arc point. -/
lemma fderiv_nfsB_along_arc_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {η u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) η)
    (harc : ∀ u' ∈ Set.Ioo (0 : ℝ) η,
      p + u' • W ∈ stripInterior ∧ dN f (p + u' • W) ≠ 0 ∧ dN f (p + u' • W) W = 0) :
    fderiv ℝ (nfsB f W) (p + u • W) W = 0 := by
  let g : ℝ → ℝ := fun s => nfsB f W (p + s • W)
  have hg0 : ∀ᶠ s : ℝ in 𝓝 u, g s = 0 := by
    rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds isOpen_Ioo hu) with ⟨δ, hδ0, hδ⟩
    filter_upwards [Metric.ball_mem_nhds u hδ0] with s hs
    have hsi : s ∈ Set.Ioo (0 : ℝ) η := by
      exact hδ (by simpa [Metric.mem_ball, Real.dist_eq] using hs)
    rcases harc s hsi with ⟨_, _, hk⟩
    exact nfsB_zero_of_kernel hf (harc s hsi).1 W hk
  have hder : deriv g u = 0 := deriv_eq_zero_of_eventually_zero hg0
  have hdg : DifferentiableAt ℝ (nfsB f W) (p + u • W) :=
    differentiableAt_nfsB hf W (p + u • W) (harc u hu).1
  have hpull := deriv_ray (x := p) W (g := nfsB f W) (u := u) hdg
  have hpull' : deriv g u = fderiv ℝ (nfsB f W) (p + u • W) W := by
    simpa [g] using hpull
  exact hpull'.symm.trans hder


/-- Second directional derivative of a function that vanishes identically on
the strip interior: zero at interior points. -/
lemma fderiv_iter_zero_of_eq_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (G : ℝ² → ℝ) {x : ℝ²} (hx : x ∈ stripInterior)
    (hG : ∀ y ∈ stripInterior, G y = 0) (U : ℝ²) :
    fderiv ℝ (fun y : ℝ² => fderiv ℝ G y U) x U = 0 := by
  have heq : (fun y : ℝ² => fderiv ℝ G y U) =ᶠ[𝓝 x] (fun _ : ℝ² => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    have hG0 : G =ᶠ[𝓝 y] (fun _ : ℝ² => (0 : ℝ)) := by
      filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hy] with z hz
      exact hG z hz
    rw [hG0.fderiv_eq]
    simp
  rw [heq.fderiv_eq]
  simp


/-- Differentiability of the directional fderiv-map from `C²`-smoothness. -/
lemma differentiableAt_fderiv_dir {G : ℝ² → ℝ} (U : ℝ²) {x : ℝ²}
    (hG : ContDiffOn ℝ 2 G stripInterior) (hx : x ∈ stripInterior) :
    DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ G y U) x := by
  have hcont : ContDiffAt ℝ 2 G x := hG.contDiffAt (IsOpen.mem_nhds stripInterior_isOpen hx)
  have hfd : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ G y) x :=
    (hcont.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hfd.clm_apply (differentiableAt_const (c := U) (𝕜 := ℝ))

/-- `C∞`-smoothness of the directional fderiv-map of the rotated entries
(`C²` suffices, stated with `∞` inputs and `.of_le`). -/
lemma differentiableAt_dir_nfsC {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (W U : ℝ²) :
    DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y U) x :=
  differentiableAt_fderiv_dir U ((contDiffOn_nfsC hf W).of_le (by decide : (2 : ℕ∞) ≤ ∞)) hx

lemma differentiableAt_dir_nfsA {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (W U : ℝ²) :
    DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x :=
  differentiableAt_fderiv_dir U ((contDiffOn_nfsA hf W).of_le (by decide : (2 : ℕ∞) ≤ ∞)) hx

lemma differentiableAt_dir_nfsB {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (W U : ℝ²) :
    DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y U) x :=
  differentiableAt_fderiv_dir U ((contDiffOn_nfsB hf W).of_le (by decide : (2 : ℕ∞) ≤ ∞)) hx

/-- The derivative of a product of scalar functions, applied to a direction. -/
lemma fderiv_mul_apply {φ ψ : ℝ² → ℝ} {x : ℝ²} (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) (U : ℝ²) :
    fderiv ℝ (fun y : ℝ² => φ y * ψ y) x U =
      φ x * fderiv ℝ ψ x U + ψ x * fderiv ℝ φ x U := by
  have hm := fderiv_mul hφ hψ
  have h' : fderiv ℝ (fun y : ℝ² => φ y * ψ y) x U = (fderiv ℝ (φ * ψ) x) U := by rfl
  rw [h', hm]
  simp [smul_eq_mul]


/-- **Core ODE at an arc point** (fderiv form).  At an arc point
`x = p + u•W` of a kernel segment in `U`, the second transverse derivative
of `AC − B² ≡ 0` gives `A₂·C(x) = 2·(B₁)²`, where
`A₂ = ∂ᵤ∂ᵤ A (x)` and `B₁ = ∂ᵤ B (x)` along the transverse direction
`U = perp W`; equivalently (Codazzi₁) `B₁ = C_W(x)`, so
`A₂·C(x) = 2·(C_W x)²`. -/
lemma ode_arc_point {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {η u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) η)
    (harc : ∀ u' ∈ Set.Ioo (0 : ℝ) η,
      p + u' • W ∈ stripInterior ∧ dN f (p + u' • W) ≠ 0 ∧ dN f (p + u' • W) W = 0) :
    fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y (perp W)) (p + u • W) (perp W)
      * nfsC f W (p + u • W)
      = 2 * (fderiv ℝ (nfsC f W) (p + u • W) W)^2 := by
  let x : ℝ² := p + u • W
  let U : ℝ² := perp W
  have hx : x ∈ stripInterior := by
    dsimp [x]
    exact (harc u hu).1
  have hk : dN f x W = 0 := by
    dsimp [x]
    exact (harc u hu).2.2
  have hA0 : nfsA f W x = 0 := nfsA_zero_of_kernel hf hx W hk
  have hB0 : nfsB f W x = 0 := nfsB_zero_of_kernel hf hx W hk
  have hc0 : fderiv ℝ (nfsA f W) x U = 0 := by
    have hcod := nfs_codazzi₀ hf W x hx
    rw [hcod]
    dsimp [x, U]
    exact fderiv_nfsB_along_arc_zero hf hu harc
  have hdA : DifferentiableAt ℝ (nfsA f W) x := differentiableAt_nfsA hf W x hx
  have hdB : DifferentiableAt ℝ (nfsB f W) x := differentiableAt_nfsB hf W x hx
  have hdC : DifferentiableAt ℝ (nfsC f W) x := differentiableAt_nfsC hf W x hx
  have hdhA : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x :=
    differentiableAt_dir_nfsA hf hx W U
  have hdhB : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y U) x :=
    differentiableAt_dir_nfsB hf hx W U
  have hdhC : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y U) x :=
    differentiableAt_dir_nfsC hf hx W U
  let H : ℝ² → ℝ := fun z => nfsA f W z * nfsC f W z - (nfsB f W z)^2
  have hzero : fderiv ℝ (fun y : ℝ² => fderiv ℝ H y U) x U = 0 := by
    have hg : ∀ y ∈ stripInterior, H y = 0 := by
      intro y hy
      dsimp [H]
      exact nfs_det_zero hf W y hy
    exact fderiv_iter_zero_of_eq_zero hf H hx hg U
  have hH2form : (fun y : ℝ² => fderiv ℝ H y U) =ᶠ[𝓝 x]
      (fun y : ℝ² => nfsA f W y * fderiv ℝ (nfsC f W) y U
        + nfsC f W y * fderiv ℝ (nfsA f W) y U
        - 2 * (nfsB f W y * fderiv ℝ (nfsB f W) y U)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    have hdAy : DifferentiableAt ℝ (nfsA f W) y := differentiableAt_nfsA hf W y hy
    have hdBy : DifferentiableAt ℝ (nfsB f W) y := differentiableAt_nfsB hf W y hy
    have hdCy : DifferentiableAt ℝ (nfsC f W) y := differentiableAt_nfsC hf W y hy
    have hsub' : fderiv ℝ (fun z : ℝ² => nfsA f W z * nfsC f W z - (nfsB f W z)^2) y =
        fderiv ℝ (fun z : ℝ² => nfsA f W z * nfsC f W z) y -
          fderiv ℝ (fun z : ℝ² => (nfsB f W z)^2) y := by
      exact fderiv_sub (hdAy.mul hdCy) (hdBy.pow 2)
    have hAC := fderiv_mul_apply hdAy hdCy U
    calc
      fderiv ℝ H y U = fderiv ℝ H y U := rfl
      _ = fderiv ℝ (fun z : ℝ² => nfsA f W z * nfsC f W z - (nfsB f W z)^2) y U := rfl
      _ = (fderiv ℝ (fun z : ℝ² => nfsA f W z * nfsC f W z) y
          - fderiv ℝ (fun z : ℝ² => (nfsB f W z)^2) y) U := by
              rw [hsub']
      _ = fderiv ℝ (fun z : ℝ² => nfsA f W z * nfsC f W z) y U
          - fderiv ℝ (fun z : ℝ² => (nfsB f W z)^2) y U := by
              simp
      _ = (nfsA f W y * fderiv ℝ (nfsC f W) y U + nfsC f W y * fderiv ℝ (nfsA f W) y U)
          - (nfsB f W y * fderiv ℝ (nfsB f W) y U + nfsB f W y * fderiv ℝ (nfsB f W) y U) := by
              rw [hAC]
              have hpow : (fun z : ℝ² => (nfsB f W z)^2) = fun z : ℝ² => nfsB f W z * nfsB f W z := by
                funext z
                rw [pow_two]
              rw [hpow]
              simpa using (fderiv_mul_apply hdBy hdBy U : fderiv ℝ (fun z : ℝ² => nfsB f W z * nfsB f W z) y U =
                nfsB f W y * fderiv ℝ (nfsB f W) y U + nfsB f W y * fderiv ℝ (nfsB f W) y U)
      _ = nfsA f W y * fderiv ℝ (nfsC f W) y U + nfsC f W y * fderiv ℝ (nfsA f W) y U
          - 2 * (nfsB f W y * fderiv ℝ (nfsB f W) y U) := by
              ring
  let S : ℝ² → ℝ := fun y => nfsA f W y * fderiv ℝ (nfsC f W) y U
      + nfsC f W y * fderiv ℝ (nfsA f W) y U
      - 2 * (nfsB f W y * fderiv ℝ (nfsB f W) y U)
  let T1 : ℝ² → ℝ := fun y => nfsA f W y * fderiv ℝ (nfsC f W) y U
  let T2 : ℝ² → ℝ := fun y => nfsC f W y * fderiv ℝ (nfsA f W) y U
  let T3 : ℝ² → ℝ := fun y => nfsB f W y * fderiv ℝ (nfsB f W) y U
  have hdT1 : DifferentiableAt ℝ T1 x := by
    dsimp [T1]
    exact hdA.mul hdhC
  have hdT2 : DifferentiableAt ℝ T2 x := by
    dsimp [T2]
    exact hdC.mul hdhA
  have hdT3 : DifferentiableAt ℝ T3 x := by
    dsimp [T3]
    exact hdB.mul hdhB
  have hfT1 : fderiv ℝ T1 x U = 0 := by
    have hm := fderiv_mul_apply hdA hdhC U
    calc
      fderiv ℝ T1 x U = nfsA f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y U) x U
          + fderiv ℝ (nfsC f W) x U * fderiv ℝ (nfsA f W) x U := by
            simpa [T1] using hm
      _ = 0 := by
            rw [hA0, hc0]
            ring
  have hfT2 : fderiv ℝ T2 x U = nfsC f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U := by
    have hm := fderiv_mul_apply hdC hdhA U
    calc
      fderiv ℝ T2 x U = nfsC f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U
          + fderiv ℝ (nfsA f W) x U * fderiv ℝ (nfsC f W) x U := by
            simpa [T2] using hm
      _ = nfsC f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U := by
            rw [hc0]
            ring
  have hfT3 : fderiv ℝ T3 x U = (fderiv ℝ (nfsB f W) x U)^2 := by
    have hm := fderiv_mul_apply hdB hdhB U
    calc
      fderiv ℝ T3 x U = nfsB f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y U) x U
          + fderiv ℝ (nfsB f W) x U * fderiv ℝ (nfsB f W) x U := by
            simpa [T3] using hm
      _ = (fderiv ℝ (nfsB f W) x U)^2 := by
            rw [hB0]
            ring
  have hfSsum : fderiv ℝ S x U = fderiv ℝ T1 x U + fderiv ℝ T2 x U - 2 * fderiv ℝ T3 x U := by
    have hS2 : S = (T1 + T2) - fun y : ℝ² => (2 : ℝ) * T3 y := by
      funext y
      dsimp [S, T1, T2, T3]
    have hd12 : DifferentiableAt ℝ (T1 + T2) x := hdT1.add hdT2
    have hd23 : DifferentiableAt ℝ (fun y : ℝ² => (2 : ℝ) * T3 y) x := hdT3.const_mul 2
    have hc2 : fderiv ℝ (fun y : ℝ² => (2 : ℝ) * T3 y) x = (2 : ℝ) • fderiv ℝ T3 x := by
      have hc2' : (fun y : ℝ² => (2 : ℝ) * T3 y) = (2 : ℝ) • T3 := by
        funext y
        rfl
      rw [hc2', fderiv_const_smul (c := (2 : ℝ)) hdT3]
    calc
      fderiv ℝ S x U = fderiv ℝ ((T1 + T2) - fun y : ℝ² => (2 : ℝ) * T3 y) x U := by
          rw [hS2]
      _ = (fderiv ℝ (T1 + T2) x - fderiv ℝ (fun y : ℝ² => (2 : ℝ) * T3 y) x) U := by
          rw [fderiv_sub hd12 hd23]
      _ = (fderiv ℝ T1 x + fderiv ℝ T2 x - (2 : ℝ) • fderiv ℝ T3 x) U := by
          rw [fderiv_add hdT1 hdT2, hc2]
      _ = fderiv ℝ T1 x U + fderiv ℝ T2 x U - 2 * fderiv ℝ T3 x U := by
          simp [smul_eq_mul]
  have hSexp : fderiv ℝ S x U =
      (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U) * nfsC f W x
        - 2 * (fderiv ℝ (nfsB f W) x U)^2 := by
    calc
      fderiv ℝ S x U = fderiv ℝ T1 x U + fderiv ℝ T2 x U - 2 * fderiv ℝ T3 x U := hfSsum
      _ = 0 + (nfsC f W x * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U)
          - 2 * (fderiv ℝ (nfsB f W) x U)^2 := by
            rw [hfT1, hfT2, hfT3]
      _ = (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U) * nfsC f W x
          - 2 * (fderiv ℝ (nfsB f W) x U)^2 := by ring
  have hz : fderiv ℝ S x U = 0 := by
    have heqF : fderiv ℝ (fun y : ℝ² => fderiv ℝ H y U) x = fderiv ℝ S x := by
      exact hH2form.fderiv_eq
    calc
      fderiv ℝ S x U = fderiv ℝ (fun y : ℝ² => fderiv ℝ H y U) x U := by
          rw [heqF]
      _ = 0 := hzero
  have hmain0 : (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U) * nfsC f W x
      - 2 * (fderiv ℝ (nfsB f W) x U)^2 = 0 := by
    have hz' := hz
    rw [hSexp] at hz'
    exact hz'
  have hmain : (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y U) x U) * nfsC f W x
      = 2 * (fderiv ℝ (nfsB f W) x U)^2 := by
    have hz'' := hmain0
    nlinarith
  have hcod := nfs_codazzi₁ hf W x hx
  rw [hcod] at hmain
  simpa [x, U] using hmain


/-- The iterated transverse derivative of `A` equals the iterated arc
derivative of `C` (via rotated Codazzi + Clairaut):
`A₂ = C_WW` at an arc point. -/
lemma A2_eq_CWW {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x : ℝ²}
    (hx : x ∈ stripInterior) (W : ℝ²) :
    fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y (perp W)) x (perp W)
      = fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) x W := by
  -- step 1: A_U = B_W pointwise (codazzi₀) on the interior
  have h1 : fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y (perp W)) x =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y W) x := by
    have heq : (fun y : ℝ² => fderiv ℝ (nfsA f W) y (perp W)) =ᶠ[𝓝 x]
        (fun y : ℝ² => fderiv ℝ (nfsB f W) y W) := by
      filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
      exact nfs_codazzi₀ hf W y hy
    exact heq.fderiv_eq
  -- step 2: Clairaut (B mixed partials commute)
  have h2 : fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y W) x (perp W) =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y (perp W)) x W := by
    exact Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
      (s := stripInterior) (f := nfsB f W) (x := x) stripInterior_isOpen hx
      ((contDiffOn_nfsB hf W).of_le (by decide : (2 : ℕ∞) ≤ ∞)) W (perp W)
  -- step 3: B_U = C_W pointwise (codazzi₁)
  have h3 : fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y (perp W)) x =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) x := by
    have heq : (fun y : ℝ² => fderiv ℝ (nfsB f W) y (perp W)) =ᶠ[𝓝 x]
        (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) := by
      filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
      exact nfs_codazzi₁ hf W y hy
    exact heq.fderiv_eq
  calc
    fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsA f W) y (perp W)) x (perp W)
        = (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y W) x) (perp W) := by
            rw [h1]
    _ = fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsB f W) y (perp W)) x W := h2
    _ = (fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) x) W := by
            rw [h3]

/-- **ODE in γ terms** along the arc: for `γ(u) = C(p + u•W)`,
`γ(u)·γ''(u) = 2·γ'(u)²` at each arc point (directional-derivative form). -/
lemma ode_gamma {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {η u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) η)
    (harc : ∀ u' ∈ Set.Ioo (0 : ℝ) η,
      p + u' • W ∈ stripInterior ∧ dN f (p + u' • W) ≠ 0 ∧ dN f (p + u' • W) W = 0) :
    nfsC f W (p + u • W) * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) W
      = 2 * (fderiv ℝ (nfsC f W) (p + u • W) W)^2 := by
  have h1 := ode_arc_point hf hu harc
  have hx : p + u • W ∈ stripInterior := (harc u hu).1
  have hA := A2_eq_CWW hf hx W
  rw [hA] at h1
  rw [mul_comm] at h1
  exact h1


/-- First derivative of `γ(s) = C(p + s•W)` via the pullback. -/
lemma deriv_gamma_first {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {u : ℝ} (huI : p + u • W ∈ stripInterior) :
    deriv (fun s : ℝ => nfsC f W (p + s • W)) u = fderiv ℝ (nfsC f W) (p + u • W) W := by
  have hd : DifferentiableAt ℝ (nfsC f W) (p + u • W) := differentiableAt_nfsC hf W (p + u • W) huI
  exact deriv_ray (x := p) W (g := nfsC f W) (u := u) hd

/-- Second derivative of `γ(s) = C(p + s•W)` via the second pullback. -/
lemma deriv_gamma_second {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {u : ℝ} (huI : p + u • W ∈ stripInterior) :
    deriv (deriv (fun s : ℝ => nfsC f W (p + s • W))) u
      = fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) W := by
  have hpre : {s : ℝ | p + s • W ∈ stripInterior} ∈ 𝓝 u := by
    have hcont : ContinuousAt (fun s : ℝ => p + s • W) u := by fun_prop
    exact hcont.preimage_mem_nhds (IsOpen.mem_nhds stripInterior_isOpen huI)
  have hγ' : (fun s : ℝ => deriv (fun t : ℝ => nfsC f W (p + t • W)) s) =ᶠ[𝓝 u]
      (fun s : ℝ => fderiv ℝ (nfsC f W) (p + s • W) W) := by
    filter_upwards [hpre] with s hs
    have hd : DifferentiableAt ℝ (nfsC f W) (p + s • W) := differentiableAt_nfsC hf W (p + s • W) hs
    exact deriv_ray (x := p) W (g := nfsC f W) (u := s) hd
  have hmain : deriv (deriv (fun s : ℝ => nfsC f W (p + s • W))) u =
      deriv (fun s : ℝ => fderiv ℝ (nfsC f W) (p + s • W) W) u := by
    have hd' : deriv (fun s : ℝ => deriv (fun t : ℝ => nfsC f W (p + t • W)) s) u =
        deriv (fun s : ℝ => fderiv ℝ (nfsC f W) (p + s • W) W) u := by
      exact hγ'.deriv_eq
    simpa using hd'
  have hdF : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) :=
    differentiableAt_dir_nfsC hf huI W W
  have hpull := deriv_ray (x := p) W (g := fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (u := u) hdF
  calc
    deriv (deriv (fun s : ℝ => nfsC f W (p + s • W))) u
        = deriv (fun s : ℝ => fderiv ℝ (nfsC f W) (p + s • W) W) u := hmain
    _ = fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) W := by
          simpa using hpull


/-- `γ(s) = C(p + s•W)` is `C²` on an interval whose image lies in the
strip interior. -/
lemma contDiffOn_gamma {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} {W : ℝ²} {ε : ℝ} (hε0 : 0 < ε)
    (hstrip : ∀ u ∈ Set.Ioo (-ε) ε, p + u • W ∈ stripInterior) :
    ContDiffOn ℝ 2 (fun s : ℝ => nfsC f W (p + s • W)) (Set.Ioo (-ε) ε) := by
  have haff : ContDiffOn ℝ 2 (fun u : ℝ => p + u • W) (Set.univ : Set ℝ) := by
    have hc : ContDiff ℝ 2 (fun u : ℝ => p + u • W) := by fun_prop
    exact hc.contDiffOn
  have haffI : ContDiffOn ℝ 2 (fun u : ℝ => p + u • W) (Set.Ioo (-ε) ε) :=
    haff.mono (by simp)
  have hgN : ContDiffOn ℝ 2 (nfsC f W) stripInterior :=
    (contDiffOn_nfsC hf W).of_le (by decide : (2 : ℕ∞) ≤ ∞)
  have hmap : Set.MapsTo (fun u : ℝ => p + u • W) (Set.Ioo (-ε) ε) stripInterior := by
    intro u hu
    exact hstrip u hu
  have hcomp := ContDiffOn.comp hgN haffI hmap
  simpa [Function.comp_def] using hcomp

/-- **Flat stops are impossible**: a straight kernel segment through
`U = {dN ≠ 0}` (points `p + u•W`, `u > 0`, with `dN ≠ 0` and `dN·W = 0`)
cannot end at an interior flat point `p` (`dN f p = 0`). -/
theorem flat_stop_impossible {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} (hp : p ∈ stripInterior) {W : ℝ²} (hW : W ≠ 0)
    (hflat : dN f p = 0)
    (harc : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Ioo (0 : ℝ) η,
      p + u • W ∈ stripInterior ∧ dN f (p + u • W) ≠ 0 ∧ dN f (p + u • W) W = 0) :
    False := by
  rcases harc with ⟨η, hη0, harc⟩
  -- near p (in all directions) the points are in the strip interior
  have hpre0 : {s : ℝ | p + s • W ∈ stripInterior} ∈ 𝓝 0 := by
    have hp0 : p + (0 : ℝ) • W ∈ stripInterior := by simpa using hp
    have hcont : ContinuousAt (fun s : ℝ => p + s • W) 0 := by fun_prop
    exact hcont.preimage_mem_nhds (IsOpen.mem_nhds stripInterior_isOpen hp0)
  rcases Metric.mem_nhds_iff.mp hpre0 with ⟨δ, hδ0, hδ⟩
  let ε : ℝ := min (η / 2) δ
  have hε0 : 0 < ε := by
    dsimp [ε]
    positivity
  have hεη : ε ≤ η / 2 := by dsimp [ε]; exact min_le_left _ _
  have hεδ : ε ≤ δ := by dsimp [ε]; exact min_le_right _ _
  -- the interval (−ε, ε) maps into the strip interior and (0,ε) into the arc
  have hstrip : ∀ u ∈ Set.Ioo (-ε) ε, p + u • W ∈ stripInterior := by
    intro u hu
    have huδ : |u| < δ := by
      rw [Set.mem_Ioo] at hu
      exact lt_of_lt_of_le (abs_lt.mpr ⟨hu.1, hu.2⟩) hεδ
    have huin : u ∈ Metric.ball (0 : ℝ) δ := by
      simpa [Real.dist_eq] using huδ
    exact hδ huin
  have harcI : ∀ u ∈ Set.Ioo (0 : ℝ) η, p + u • W ∈ stripInterior ∧
      dN f (p + u • W) ≠ 0 ∧ dN f (p + u • W) W = 0 := harc
  have harcE : ∀ u ∈ Set.Ioo (0 : ℝ) ε,
      p + u • W ∈ stripInterior ∧ dN f (p + u • W) ≠ 0 ∧ dN f (p + u • W) W = 0 := by
    intro u hu
    have huη : u ∈ Set.Ioo (0 : ℝ) η := by
      rw [Set.mem_Ioo] at hu ⊢
      exact ⟨hu.1, lt_trans (lt_of_lt_of_le hu.2 hεη) (half_lt_self hη0)⟩
    exact harcI u huη
  let γ : ℝ → ℝ := fun s => nfsC f W (p + s • W)
  have hg0 : γ 0 = 0 := by
    have hn : nfsC f W p = 0 := by
      rw [nfsC_eq_inner hf hp W, hflat]
      simp
    change nfsC f W (p + (0 : ℝ) • W) = 0
    simpa using hn
  have hgne : ∀ u ∈ Set.Ioo (0 : ℝ) ε, γ u ≠ 0 := by
    intro u hu
    dsimp [γ]
    exact nfsC_ne_zero hf (harcE u hu).1 W hW (harcE u hu).2.1 (harcE u hu).2.2
  have hgs : ContDiffOn ℝ 2 γ (Set.Ioo (-ε) ε) := by
    dsimp [γ]
    exact contDiffOn_gamma hf (ε := ε) hε0 hstrip
  have hode : ∀ u ∈ Set.Ioo (0 : ℝ) ε, γ u * deriv (deriv γ) u = 2 * (deriv γ u)^2 := by
    intro u hu
    have hx : p + u • W ∈ stripInterior := (harcE u hu).1
    have h1 := ode_gamma hf hu harcE
    -- rewrite via the γ-bridges
    have hd1 := deriv_gamma_first hf (W := W) (u := u) hx
    have hd2 := deriv_gamma_second hf (W := W) (u := u) hx
    -- h1 : C(x) * CWW = 2 (CW)² ; target γu * γ''u = 2(γ'u)²
    have hgoal : γ u * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) W
        = 2 * (fderiv ℝ (nfsC f W) (p + u • W) W)^2 := by
      simpa [γ] using h1
    calc
      γ u * deriv (deriv γ) u = γ u * fderiv ℝ (fun y : ℝ² => fderiv ℝ (nfsC f W) y W) (p + u • W) W := by
            rw [hd2]
      _ = 2 * (fderiv ℝ (nfsC f W) (p + u • W) W)^2 := hgoal
      _ = 2 * (deriv γ u)^2 := by
            rw [hd1]
  exact Commons.Analysis.Calculus.Deriv.ode_contradiction_one_sided
    (g := γ) (ε := ε) hε0 hgs hg0 hgne hode

/-- **The U-component sup-argument (right side)**: along an affine ray
`s -> x0 + s*w`, if the strip-interior membership and the kernel condition
`dN(x0+s*w) w = 0` hold on the whole open segment `(0, B)` and the start
point is in `U`, then the whole segment is in `U` (`dN ≠ 0`): a flat point
in `(0,B)` would be a flat stop, contradicting `flat_stop_impossible`. -/
lemma right_all_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw : w ≠ 0) {B : ℝ} (hB : 0 < B)
    (hU0 : dN f x₀ ≠ 0)
    (hseg : ∀ s ∈ Set.Ioo (0 : ℝ) B,
      x₀ + s • w ∈ stripInterior ∧ dN f (x₀ + s • w) w = 0) :
    ∀ s ∈ Set.Ioo (0 : ℝ) B, dN f (x₀ + s • w) ≠ 0 := by
  let E : Set ℝ := {s : ℝ | 0 ≤ s ∧ s < B ∧ ∀ r ∈ Set.Icc 0 s, dN f (x₀ + r • w) ≠ 0}
  have hopen_at (r : ℝ) (hV : dN f (x₀ + r • w) ≠ 0) (hrI : x₀ + r • w ∈ stripInterior) :
      {s : ℝ | dN f (x₀ + s • w) ≠ 0} ∈ 𝓝 r := by
    have hcont : ContinuousAt (fun s : ℝ => dN f (x₀ + s • w)) r := by
      have hdif : DifferentiableAt ℝ (fun z : ℝ² => dN f z) (x₀ + r • w) := by
        have h1 : DifferentiableOn ℝ (fun z : ℝ² => dN f z) stripInterior := by
          exact ContDiffOn.differentiableOn (contDiffOn_dN hf) (by decide)
        exact h1.differentiableAt (IsOpen.mem_nhds stripInterior_isOpen hrI)
      have haffD : DifferentiableAt ℝ (fun s : ℝ => x₀ + s • w) r := by fun_prop
      have hcomp : DifferentiableAt ℝ (fun s : ℝ => dN f (x₀ + s • w)) r := by
        fun_prop
      exact hcomp.continuousAt
    have htend : Filter.Tendsto (fun s : ℝ => dN f (x₀ + s • w)) (𝓝 r)
        (𝓝 (dN f (x₀ + r • w))) := hcont.tendsto
    have hnorm : 0 < ‖dN f (x₀ + r • w)‖ := norm_pos_iff.mpr hV
    filter_upwards [Metric.tendsto_nhds.mp htend ‖dN f (x₀ + r • w)‖ hnorm] with s hs
    intro hz0
    have hdist : ‖(dN f (x₀ + s • w)) - dN f (x₀ + r • w)‖ < ‖dN f (x₀ + r • w)‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hs
    have : ‖dN f (x₀ + r • w)‖ < ‖dN f (x₀ + r • w)‖ := by
      rw [hz0] at hdist
      simpa using hdist
    linarith
  have hE0 : (0 : ℝ) ∈ E := by
    refine ⟨le_rfl, hB, ?_⟩
    intro r hr
    have hr0 : r = 0 := by
      rw [Set.mem_Icc] at hr
      linarith
    simpa [hr0, zero_smul] using hU0
  have hEne : E.Nonempty := ⟨0, hE0⟩
  have hbdd : ∀ e : ℝ, e ∈ E → e ≤ B := by
    intro e he
    exact le_of_lt he.2.1
  have hbddE : BddAbove E := ⟨B, hbdd⟩
  let β₀ : ℝ := sSup E
  have hβ₀ge0 : 0 ≤ β₀ := by
    dsimp [β₀]
    exact le_csSup hbddE hE0
  have hβ₀leB : β₀ ≤ B := by
    dsimp [β₀]
    exact csSup_le hEne hbdd
  have hrestrict : ∀ e s : ℝ, e ∈ E → 0 ≤ s → s ≤ e → s ∈ E := by
    intro e s he hs0 hse
    refine ⟨hs0, ?_⟩
    constructor
    · exact lt_of_le_of_lt hse he.2.1
    · intro r hr
      rcases Set.mem_Icc.mp hr with ⟨hr0, hrs⟩
      have hri : r ∈ Set.Icc 0 e := by
        rw [Set.mem_Icc]
        constructor <;> linarith
      exact he.2.2 r hri
  have hdensity : ∀ s : ℝ, 0 ≤ s → s < β₀ → s ∈ E := by
    intro s hs0 hsβ
    have hsup' : ∃ s' : ℝ, s' ∈ E ∧ s < s' := by
      by_contra h
      have hupper : sSup E ≤ s := csSup_le hEne (by
        intro s' hs'
        by_contra hle
        exact h ⟨s', hs', lt_of_not_ge hle⟩)
      dsimp [β₀] at hsβ
      exact (not_lt_of_ge hupper) hsβ
    rcases hsup' with ⟨s', hs', hss'⟩
    exact hrestrict s' s hs' hs0 (le_of_lt hss')
  have hU : ∀ s ∈ Set.Ioo (0 : ℝ) β₀, dN f (x₀ + s • w) ≠ 0 := by
    intro s hs
    have hsE : s ∈ E := hdensity s (le_of_lt hs.1) hs.2
    exact hsE.2.2 s (by rw [Set.mem_Icc]; exact ⟨le_of_lt hs.1, le_rfl⟩)
  have hβ₀pos : 0 < β₀ := by
    by_cases hz : β₀ = 0
    · exfalso
      have hU0' : dN f (x₀ + (0 : ℝ) • w) ≠ 0 := by simpa using hU0
      have hx₀' : x₀ + (0 : ℝ) • w ∈ stripInterior := by simpa using hx₀
      rcases Metric.mem_nhds_iff.mp (hopen_at 0 hU0' hx₀') with ⟨δ0, hδ0, hδ0'⟩
      let s₁ : ℝ := min (δ0 / 2) (B / 2)
      have hs₁0 : 0 < s₁ := by
        dsimp [s₁]
        positivity
      have hs₁E : s₁ ∈ E := by
        refine ⟨le_of_lt hs₁0, ?_⟩
        constructor
        · have h₁ : min (δ0 / 2) (B / 2) ≤ B / 2 := min_le_right _ _
          exact lt_of_le_of_lt h₁ (half_lt_self hB)
        · intro r hr
          rw [Set.mem_Icc] at hr
          have hrs₁ : r ≤ s₁ := hr.2
          have h₁ : s₁ ≤ δ0 / 2 := min_le_left _ _
          have hrs : r ≤ δ0 / 2 := le_trans hrs₁ h₁
          have hr0 : 0 ≤ r := hr.1
          have hrδ : |r| < δ0 := by
            rw [abs_of_nonneg hr0]
            exact lt_of_le_of_lt hrs (half_lt_self hδ0)
          have hb : r ∈ Metric.ball (0 : ℝ) δ0 := by
            simpa [Real.dist_eq] using hrδ
          exact hδ0' hb
      have hle : s₁ ≤ sSup E := le_csSup hbddE hs₁E
      dsimp [β₀] at hz
      linarith
    · exact lt_of_le_of_ne hβ₀ge0 (by intro h; exact hz h.symm)
  by_cases hβlt : β₀ < B
  · -- β₀ < B: rule out by a flat stop at p = x₀ + β₀•w
    exfalso
    let p : ℝ² := x₀ + β₀ • w
    have hpI : p ∈ stripInterior := (hseg β₀ ⟨hβ₀pos, hβlt⟩).1
    have hdNp0 : dN f p = 0 := by
      by_contra hdNp
      rcases Metric.mem_nhds_iff.mp (hopen_at β₀ hdNp hpI) with ⟨δ0, hδ0, hδ0'⟩
      let s₂ : ℝ := β₀ + min (δ0 / 2) ((B - β₀) / 2)
      have hs₂b : s₂ < B := by
        dsimp [s₂]
        have h₁ : min (δ0 / 2) ((B - β₀) / 2) < B - β₀ := by
          have h₁' : min (δ0 / 2) ((B - β₀) / 2) ≤ (B - β₀) / 2 := min_le_right _ _
          exact lt_of_le_of_lt h₁' (by linarith : (B - β₀) / 2 < B - β₀)
        nlinarith [hβlt]
      have hs₂E : s₂ ∈ E := by
        refine ⟨by dsimp [s₂]; positivity, ?_⟩
        constructor
        · exact hs₂b
        · intro r hr
          rw [Set.mem_Icc] at hr
          have hr0 : 0 ≤ r := hr.1
          have hrs₂ : r ≤ s₂ := hr.2
          by_cases hrlt : r < β₀
          · by_cases hr0z : r = 0
            · simpa [hr0z, zero_smul] using hU0
            · have hrr : r ∈ Set.Ioo (0 : ℝ) β₀ := by
                rw [Set.mem_Ioo]
                exact ⟨lt_of_le_of_ne hr0 (by intro hz; exact hr0z hz.symm), hrlt⟩
              exact hU r hrr
          · have hβr : β₀ ≤ r := le_of_not_gt hrlt
            by_cases hreq : r = β₀
            · simpa [p, hreq] using hdNp
            · have hrgt : β₀ < r := lt_of_le_of_ne hβr (by intro hz; exact hreq hz.symm)
              have h₁ : r - β₀ ≤ min (δ0 / 2) ((B - β₀) / 2) := by
                dsimp [s₂] at hrs₂
                linarith
              have h₂ : r - β₀ ≤ δ0 / 2 := le_trans h₁ (min_le_left _ _)
              have h₃ : 0 ≤ r - β₀ := by linarith
              have hrδ : |r - β₀| < δ0 := by
                rw [abs_of_nonneg h₃]
                exact lt_of_le_of_lt h₂ (half_lt_self hδ0)
              have hb : r ∈ Metric.ball β₀ δ0 := by
                rw [Metric.mem_ball, Real.dist_eq]
                exact hrδ
              exact hδ0' hb
      have hle : s₂ ≤ sSup E := le_csSup hbddE hs₂E
      have hs₂gt : sSup E < s₂ := by
        have hm : 0 < min (δ0 / 2) ((B - β₀) / 2) := by
          have h1 : 0 < δ0 / 2 := by positivity
          have h2 : 0 < (B - β₀) / 2 := by positivity
          exact lt_min h1 h2
        have hgt : β₀ < s₂ := by
          dsimp [s₂]
          nlinarith
        have hβ : sSup E = β₀ := rfl
        rwa [← hβ] at hgt
      linarith
    have hW' : -w ≠ 0 := by
      intro hz
      exact hw (neg_eq_zero.mp hz)
    have harc : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Ioo (0 : ℝ) η,
        p + u • (-w) ∈ stripInterior ∧ dN f (p + u • (-w)) ≠ 0 ∧ dN f (p + u • (-w)) (-w) = 0 := by
      refine ⟨β₀ / 2, half_pos hβ₀pos, ?_⟩
      intro u hu
      let s' : ℝ := β₀ - u
      have hs'0 : 0 < s' := by dsimp [s']; linarith [hu.2, hβ₀pos]
      have hs'β : s' < β₀ := by dsimp [s']; linarith [hu.1]
      have hs'I : s' ∈ Set.Ioo (0 : ℝ) β₀ := by rw [Set.mem_Ioo]; exact ⟨hs'0, hs'β⟩
      have hs'B : s' ∈ Set.Ioo (0 : ℝ) B := by
        rw [Set.mem_Ioo]
        exact ⟨hs'0, lt_trans hs'β hβlt⟩
      have hpt : p + u • (-w) = x₀ + s' • w := by
        dsimp [p, s']
        rw [sub_smul, smul_neg]
        abel
      have hmem : p + u • (-w) ∈ stripInterior := by
        rw [hpt]
        exact (hseg s' hs'B).1
      have hker : dN f (p + u • (-w)) (-w) = 0 := by
        rw [hpt]
        have hk := (hseg s' hs'B).2
        rw [map_neg, hk]
        simp
      have hnz : dN f (p + u • (-w)) ≠ 0 := by
        rw [hpt]
        exact hU s' hs'I
      exact ⟨hmem, hnz, hker⟩
    exact flat_stop_impossible hf hpI hW' hdNp0 harc
  · -- β₀ = B
    have hβeq : β₀ = B := le_antisymm hβ₀leB (le_of_not_gt hβlt)
    rw [← hβeq]
    exact hU


/-- The `0`-coordinate of an affine ray point is continuous. -/
lemma g_coord_continuous (x₀ w₀ : ℝ²) : Continuous (fun s : ℝ => (x₀ + s • w₀) 0) := by
  fun_prop

/-- Along the maximal kernel segment the `0`-coordinate stays in `[0,1]`
at the right endpoint (affine function whose values on `(0,β)` lie in
`(0,1)`). -/
lemma coord_mem_Icc {x₀ w₀ : ℝ²} {β : ℝ} (hβ : 0 < β)
    (h : ∀ s ∈ Set.Ioo (0 : ℝ) β, (x₀ + s • w₀) 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (x₀ + β • w₀) 0 ∈ Set.Icc (0 : ℝ) 1 := by
  let g : ℝ → ℝ := fun s => (x₀ + s • w₀) 0
  have hct : ContinuousAt g β := (g_coord_continuous x₀ w₀).continuousAt
  rw [Set.mem_Icc]
  constructor
  · by_contra hz
    have hlt : g β < 0 := by
      dsimp [g] at hz
      exact lt_of_not_ge hz
    have hpre : {s : ℝ | g s < 0} ∈ 𝓝 β := hct.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hlt)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hη, hη'⟩
    have hm0 : 0 < min (η / 2) (β / 2) := lt_min (by positivity) (by positivity)
    have hmB : min (η / 2) (β / 2) < β := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hβ)
    let s : ℝ := β - min (η / 2) (β / 2)
    have hs0 : 0 < s := by
      dsimp [s]
      linarith
    have hsβ : s < β := by
      dsimp [s]
      linarith
    have hb : s ∈ Metric.ball β η := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hm1 : min (η / 2) (β / 2) < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
      have hdiff : β - s = min (η / 2) (β / 2) := by dsimp [s]; ring
      rw [abs_sub_comm, hdiff, abs_of_nonneg (le_of_lt hm0)]
      exact hm1
    have hgs : g s < 0 := hη' hb
    have hin := h s ⟨hs0, hsβ⟩
    dsimp [g] at hgs hin
    exact (not_lt_of_ge (le_of_lt hin.1)) hgs
  · by_contra hz
    have hgt : 1 < g β := by
      dsimp [g] at hz
      exact lt_of_not_ge hz
    have hpre : {s : ℝ | 1 < g s} ∈ 𝓝 β := hct.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi hgt)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hη, hη'⟩
    have hm0 : 0 < min (η / 2) (β / 2) := lt_min (by positivity) (by positivity)
    have hmB : min (η / 2) (β / 2) < β := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hβ)
    let s : ℝ := β - min (η / 2) (β / 2)
    have hs0 : 0 < s := by
      dsimp [s]
      linarith
    have hsβ : s < β := by
      dsimp [s]
      linarith
    have hb : s ∈ Metric.ball β η := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hm1 : min (η / 2) (β / 2) < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
      have hdiff : β - s = min (η / 2) (β / 2) := by dsimp [s]; ring
      rw [abs_sub_comm, hdiff, abs_of_nonneg (le_of_lt hm0)]
      exact hm1
    have hgs : 1 < g s := hη' hb
    have hin := h s ⟨hs0, hsβ⟩
    dsimp [g] at hgs hin
    exact (not_lt_of_ge (le_of_lt hgs)) hin.2

/-- **The maximal kernel segment through a `U`-point reaches the strip
boundary at both ends, staying in `U`**: no flat stops.  This is the content
of `main0_test.bends_reach_boundary_test` and
`GlobalRigidity.no_flat_endpoint_global`, proved via
`right_all_U` + `flat_stop_impossible` + `coord_mem_Icc`. -/
theorem maximal_kernel_interval_in_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN₀ : dN f x₀ ≠ 0)
    (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0) (hw0 : w₀ 0 ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      (∀ s ∈ Set.Ioo α β, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) ≠ 0) ∧
      ((x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1) ∧
      ((x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1) := by
  rcases kernel_segment_two_sided hf hx₀ hdN₀ hker₀ hw₀ hw0 with ⟨α, β, hα, hβ, hseg, hstopL, hstopR⟩
  have hw₀n : -w₀ ≠ 0 := by
    intro hz
    exact hw₀ (neg_eq_zero.mp hz)
  have hα0 : 0 < -α := by linarith
  -- restrict the kernel segment to the right side (0,β) and mirror on the left (0,−α)
  have hsegR : ∀ s ∈ Set.Ioo (0 : ℝ) β,
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
    intro s hs
    have hsI : s ∈ Set.Ioo α β := by
      rw [Set.mem_Ioo]
      exact ⟨lt_trans hα hs.1, hs.2⟩
    exact hseg s hsI
  have hUR : ∀ s ∈ Set.Ioo (0 : ℝ) β, dN f (x₀ + s • w₀) ≠ 0 :=
    right_all_U hf hx₀ hw₀ hβ hdN₀ hsegR
  have hsegL : ∀ s ∈ Set.Ioo (0 : ℝ) (-α),
      x₀ + s • (-w₀) ∈ stripInterior ∧ dN f (x₀ + s • (-w₀)) (-w₀) = 0 := by
    intro s hs
    have hs0 : 0 < s := (Set.mem_Ioo.mp hs).1
    have hsα : s < -α := (Set.mem_Ioo.mp hs).2
    have hsI : -s ∈ Set.Ioo α β := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    rcases hseg (-s) hsI with ⟨hint, hk⟩
    have hpt : x₀ + s • (-w₀) = x₀ + (-s) • w₀ := by
      rw [smul_neg]
      simp
    constructor
    · rw [hpt]
      exact hint
    · rw [hpt]
      rw [map_neg, hk]
      simp
  have hUL : ∀ s ∈ Set.Ioo (0 : ℝ) (-α), dN f (x₀ + s • (-w₀)) ≠ 0 :=
    right_all_U hf hx₀ hw₀n hα0 hdN₀ hsegL
  -- the whole open maximal kernel interval is in U
  have hUall : ∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) ≠ 0 := by
    intro s hs
    rw [Set.mem_Ioo] at hs
    by_cases hs0 : s ≤ 0
    · by_cases hz : s = 0
      · simpa [hz] using hdN₀
      · have hsneg : s < 0 := lt_of_le_of_ne hs0 hz
        let s' : ℝ := -s
        have hs' : s' ∈ Set.Ioo (0 : ℝ) (-α) := by
          rw [Set.mem_Ioo]
          dsimp [s']
          constructor <;> linarith
        have hnz := hUL s' hs'
        have hpt : x₀ + s' • (-w₀) = x₀ + s • w₀ := by
          dsimp [s']
          rw [smul_neg_neg]
        rw [← hpt]
        exact hnz
    · have hsgt : 0 < s := lt_of_not_ge hs0
      have hsI : s ∈ Set.Ioo (0 : ℝ) β := by
        rw [Set.mem_Ioo]
        exact ⟨hsgt, hs.2⟩
      exact hUR s hsI
  -- endpoint at β is on the boundary (flat stops are impossible)
  have hβbound : (x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1 := by
    rcases hstopR with h | h | hflat
    · exact Or.inl h
    · exact Or.inr h
    · by_cases hb : (x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1
      · exact hb
      · exfalso
        let p : ℝ² := x₀ + β • w₀
        have hcoord01 : ∀ s ∈ Set.Ioo (0 : ℝ) β, (x₀ + s • w₀) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
          intro s hs
          simpa [stripInterior] using (hsegR s hs).1
        have hcoord := coord_mem_Icc hβ hcoord01
        rw [Set.mem_Icc] at hcoord
        have hn0 : (x₀ + β • w₀) 0 ≠ 0 := by
          intro hz
          exact hb (Or.inl hz)
        have hn1 : (x₀ + β • w₀) 0 ≠ 1 := by
          intro hz
          exact hb (Or.inr hz)
        have hp0 : 0 < (x₀ + β • w₀) 0 := lt_of_le_of_ne hcoord.1 (by intro hz; exact hn0 hz.symm)
        have hp1 : (x₀ + β • w₀) 0 < 1 := lt_of_le_of_ne hcoord.2 hn1
        have hpI : p ∈ stripInterior := by
          dsimp [p]
          simpa [stripInterior] using ⟨hp0, hp1⟩
        have hflat0 : dN f p = 0 := by
          dsimp [p]
          exact hflat.1
        have hW' : -w₀ ≠ 0 := hw₀n
        have harc : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Ioo (0 : ℝ) η,
            p + u • (-w₀) ∈ stripInterior ∧ dN f (p + u • (-w₀)) ≠ 0 ∧
              dN f (p + u • (-w₀)) (-w₀) = 0 := by
          have hbma : 0 < β - α := by linarith
          have h₂ : 0 < (β - α) / 2 := by positivity
          refine ⟨min (β / 2) ((β - α) / 2), lt_min (by positivity) h₂, ?_⟩
          intro u hu
          have hu0 : 0 < u := hu.1
          have huη : u < min (β / 2) ((β - α) / 2) := hu.2
          have huβ : u < β / 2 := lt_of_lt_of_le huη (min_le_left _ _)
          have huβα : u < (β - α) / 2 := lt_of_lt_of_le huη (min_le_right _ _)
          let s' : ℝ := β - u
          have hs'αβ : s' ∈ Set.Ioo α β := by
            rw [Set.mem_Ioo]
            dsimp [s']
            constructor <;> linarith
          have hpt : p + u • (-w₀) = x₀ + s' • w₀ := by
            dsimp [p, s']
            rw [sub_smul, smul_neg]
            abel
          have hmem : p + u • (-w₀) ∈ stripInterior := by
            rw [hpt]
            exact (hseg s' hs'αβ).1
          have hker : dN f (p + u • (-w₀)) (-w₀) = 0 := by
            rw [hpt]
            rw [map_neg, (hseg s' hs'αβ).2]
            simp
          have hnz : dN f (p + u • (-w₀)) ≠ 0 := by
            rw [hpt]
            exact hUall s' hs'αβ
          exact ⟨hmem, hnz, hker⟩
        exact flat_stop_impossible hf hpI hW' hflat0 harc
  -- endpoint at α is on the boundary (mirror via the −w₀ direction)
  have hαbound : (x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1 := by
    rcases hstopL with h | h | hflat
    · exact Or.inl h
    · exact Or.inr h
    · by_cases hb : (x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1
      · exact hb
      · exfalso
        let p : ℝ² := x₀ + α • w₀
        -- coordinate from the mirrored ray on (0,−α)
        have hcoord01 : ∀ s ∈ Set.Ioo (0 : ℝ) (-α),
            (x₀ + s • (-w₀)) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
          intro s hs
          simpa [stripInterior] using (hsegL s hs).1
        have hcoord := coord_mem_Icc hα0 hcoord01
        rw [Set.mem_Icc] at hcoord
        have hc : (x₀ + (-α) • (-w₀)) 0 ∈ Set.Icc (0 : ℝ) 1 := hcoord
        have hceq : (x₀ + (-α) • (-w₀)) 0 = (x₀ + α • w₀) 0 := by
          rw [smul_neg_neg]
        rw [hceq] at hc
        have hn0 : (x₀ + α • w₀) 0 ≠ 0 := by
          intro hz
          exact hb (Or.inl hz)
        have hn1 : (x₀ + α • w₀) 0 ≠ 1 := by
          intro hz
          exact hb (Or.inr hz)
        have hp0 : 0 < (x₀ + α • w₀) 0 := lt_of_le_of_ne hc.1 (by intro hz; exact hn0 hz.symm)
        have hp1 : (x₀ + α • w₀) 0 < 1 := lt_of_le_of_ne hc.2 hn1
        have hpI : p ∈ stripInterior := by
          dsimp [p]
          simpa [stripInterior] using ⟨hp0, hp1⟩
        have hflat0 : dN f p = 0 := by
          dsimp [p]
          exact hflat.1
        have harc : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Ioo (0 : ℝ) η,
            p + u • w₀ ∈ stripInterior ∧ dN f (p + u • w₀) ≠ 0 ∧
              dN f (p + u • w₀) w₀ = 0 := by
          refine ⟨(-α) / 2, by positivity, ?_⟩
          intro u hu
          have hu0 : 0 < u := hu.1
          have huα : u < -α / 2 := hu.2
          let s' : ℝ := α + u
          have hs'αβ : s' ∈ Set.Ioo α β := by
            rw [Set.mem_Ioo]
            dsimp [s']
            constructor <;> linarith
          have hpt : p + u • w₀ = x₀ + s' • w₀ := by
            dsimp [p, s']
            rw [add_smul]
            abel
          have hmem : p + u • w₀ ∈ stripInterior := by
            rw [hpt]
            exact (hseg s' hs'αβ).1
          have hker : dN f (p + u • w₀) w₀ = 0 := by
            rw [hpt]
            exact (hseg s' hs'αβ).2
          have hnz : dN f (p + u • w₀) ≠ 0 := by
            rw [hpt]
            exact hUall s' hs'αβ
          exact ⟨hmem, hnz, hker⟩
        exact flat_stop_impossible hf hpI hw₀ hflat0 harc
  exact ⟨α, β, hα, hβ, hseg, hUall, hβbound, hαbound⟩


end Submission.PaperBand
