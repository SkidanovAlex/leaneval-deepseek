/-
# `Work.FTS.Top.Rescale.Basic` — the time rescaling on the class of `theorem_1`

This file collects the two halves of the time rescaling that are *not* about a single operator:

* the `C¹` reparametrisation of the spacetime field: `ContDiffOn ℝ 1` is preserved by
  `uncurry ↦ uncurry ∘ timeCLM c` (plus a constant on the values);
* the preservation of the three *datum* classes of `BlowupAt` under the value scaling
  `v ↦ (fun x => c • v x)`: oddness (`IsOdd`), the `C^{1,α}` class (`IsContDiffHolder`) and — in
  `Rescale/Blowup.lean` — the vorticity decay;
* the invariance of the Euler equation itself (`euler_eq_timeScale`), obtained by combining the
  operator scaling laws of `Rescale/Defs.lean` with the generic derivative laws of
  `Rescale/spaceGrad_timeScaleP`.

The `IsContDiffHolderOn`-version of the reparametrisation (the strip clause) is in
`Rescale/isContDiffHolderOn_uncurry_timeScale`.
-/
import Submission.Work.FTS.Top.Rescale.Defs
import Submission.Work.FTS.Top.Rescale.spaceGrad_timeScaleP
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-! ## The `C¹` reparametrisation -/

/-- **`ContDiffOn` is preserved by the time rescaling** (a reparametrisation: the field
`(timeScale c u).uncurry` is `smulCLM c ∘ u.uncurry ∘ timeCLM c`). -/
theorem contDiffOn_uncurry_timeScale {c : ℝ} {s t : Set (R3 × ℝ)} {u : R3 → ℝ → R3}
    (hΦ : Set.MapsTo (timeCLM c) s t) (h : ContDiffOn ℝ 1 u.uncurry t) :
    ContDiffOn ℝ 1 (timeScale c u).uncurry s := by
  have hlin : ContDiffOn ℝ 1 (fun z : R3 × ℝ => timeCLM c z) s := (timeCLM c).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun z => u.uncurry (timeCLM c z)) s := h.comp hlin hΦ
  have h2 : ContDiffOn ℝ 1 (fun z => c • u.uncurry (timeCLM c z)) s := h1.const_smul c
  have hEq : (timeScale c u).uncurry = fun z : R3 × ℝ => c • u.uncurry (timeCLM c z) := rfl
  rw [hEq]
  exact h2

/-- **`ContDiffOn` is preserved by the time rescaling of the pressure** (the scalar version). -/
theorem contDiffOn_uncurry_timeScaleP {c : ℝ} {s t : Set (R3 × ℝ)} {p : R3 → ℝ → ℝ}
    (hΦ : Set.MapsTo (timeCLM c) s t) (h : ContDiffOn ℝ 1 p.uncurry t) :
    ContDiffOn ℝ 1 (timeScaleP c p).uncurry s := by
  have hlin : ContDiffOn ℝ 1 (fun z : R3 × ℝ => timeCLM c z) s := (timeCLM c).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun z => p.uncurry (timeCLM c z)) s := h.comp hlin hΦ
  have h2 : ContDiffOn ℝ 1 (fun z => c ^ 2 • p.uncurry (timeCLM c z)) s := h1.const_smul (c ^ 2)
  have hEq : (timeScaleP c p).uncurry = fun z : R3 × ℝ => c ^ 2 • p.uncurry (timeCLM c z) := rfl
  rw [hEq]
  exact h2

/-! ## Slices of a jointly `C¹` field at interior times -/

/-- If `u.uncurry` is `C¹` on the slab `ℝ³ × V` with `V` open, then at every time
`t ∈ V` both slices through `(x,t)` are differentiable: `t' ↦ u x t'` at `t` and `x' ↦ u x' t` at
`x`.  (Openness is only used to upgrade `ContDiffWithinAt` to `ContDiffAt`.)  This is what makes
the `deriv`-based `timeDeriv` and the `fderiv`-based `directionalDeriv` comparable with the
derivatives of the rescaled field. -/
theorem differentiableAt_slice_of_contDiffOn {u : R3 → ℝ → R3} {V : Set ℝ} (hV : IsOpen V)
    {t : ℝ} {x : R3} (h : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ V)) (ht : t ∈ V) :
    DifferentiableAt ℝ (u x) t ∧ DifferentiableAt ℝ (u · t) x := by
  have hmem : (x, t) ∈ Set.univ ×ˢ V := ⟨trivial, ht⟩
  have hopen : IsOpen (Set.univ ×ˢ V : Set (R3 × ℝ)) := isOpen_univ.prod hV
  have hca : ContDiffAt ℝ 1 u.uncurry (x, t) :=
    (h.contDiffWithinAt hmem).contDiffAt (hopen.mem_nhds hmem)
  have hd : DifferentiableAt ℝ u.uncurry (x, t) := hca.differentiableAt (by norm_num)
  have hleft : DifferentiableAt ℝ (fun s : ℝ => (x, s)) t :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := R3) (F := ℝ) x t).differentiableAt
  have hright : DifferentiableAt ℝ (fun y : R3 => (y, t)) x :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := R3) (F := ℝ) x t).differentiableAt
  refine ⟨?_, ?_⟩
  · show DifferentiableAt ℝ (fun s : ℝ => u.uncurry (x, s)) t
    exact hd.comp t hleft
  · show DifferentiableAt ℝ (fun y : R3 => u.uncurry (y, t)) x
    exact hd.comp x hright

/-! ## The Euler equation is invariant under the time rescaling -/

/-- **The Euler equation is preserved by the time rescaling.**  If `(p,u)` solves
`∂ₜu + (u·∇)u + ∇p = 0` at every `(x,t')` with `t' ∈ Ioo 0 T`, then the rescaled pair
`(timeScaleP c p, timeScale c u)` solves it at every `(x,t)` with `t ∈ Ioo 0 1`, provided
`0 < c` and `c ≤ T` (so that `c·t < T`).

All three terms of the equation are multiplied by the *same* factor `c²`, and the equation at
`(x, c·t)` is the given one. -/
theorem euler_eq_timeScale {c T : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    {p : R3 → ℝ → ℝ} {u : R3 → ℝ → R3}
    (hcu : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo 0 T))
    (heq : ∀ x, ∀ t ∈ Set.Ioo 0 T,
      timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0) :
    ∀ x, ∀ t ∈ Set.Ioo 0 1,
      timeDeriv (timeScale c u) x t + directionalDeriv (timeScale c u) (timeScale c u) x t
        + spaceGrad (timeScaleP c p) x t = 0 := by
  intro x t ht
  have hct : c * t ∈ Set.Ioo 0 T :=
    ⟨mul_pos hc ht.1, by nlinarith [ht.2, hc, hcT]⟩
  have hd1 : DifferentiableAt ℝ (u x) (c * t) :=
    (differentiableAt_slice_of_contDiffOn isOpen_Ioo hcu hct).1
  have hsum : timeDeriv u x (c * t) + directionalDeriv u u x (c * t) + spaceGrad p x (c * t) = 0 :=
    heq x (c * t) hct
  rw [timeDeriv_timeScale c u x t hd1, directionalDeriv_timeScale,
    Work.FTS.Top.Rescale.spaceGrad_timeScaleP,
    ← smul_add, ← smul_add, hsum, smul_zero]

/-! ## The datum classes are preserved by the value scaling -/

/-- The `edist`/`dist` bridge for `HolderWith`. -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- **Oddness is preserved by the value scaling** `v ↦ (fun x => c • v x)`: multiplying each
component by the same constant preserves the parity profile of `IsOdd`. -/
theorem isOdd_const_smul {c : ℝ} {v : R3 → R3} (h : IsOdd v) :
    IsOdd (fun x => c • v x) := by
  have hsmul : ∀ (i : Fin 3) (y : R3),
      (((fun x : R3 => c • v x) y).ofLp i) = c * ((v y).ofLp i) := by
    intro i y
    simp only [PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x₁ x₂
    obtain ⟨ha, hb, hc⟩ := h1 x₁ x₂
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c
  · intro x₀ x₂
    obtain ⟨ha, hb, hc⟩ := h2 x₀ x₂
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c
  · intro x₀ x₁
    obtain ⟨ha, hb, hc⟩ := h3 x₀ x₁
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c

/-- **The `C^{1,α}` class is preserved by the value scaling** `v ↦ (fun x => c • v x)`:
`fderiv (c • v) = c • fderiv v` (`fderiv_const_smul_field`), scaled boundedness and scaled
Holder continuity. -/
theorem isContDiffHolder_const_smul {α : ℝ≥0} {c : ℝ} {v : R3 → R3}
    (h : IsContDiffHolder ℝ α v) : IsContDiffHolder ℝ α (fun x => c • v x) := by
  obtain ⟨hcd, hbdd, hholder⟩ := h
  refine ⟨hcd.const_smul c, ?_, ?_⟩
  · rw [IsBoundedFun, IsBoundedFunOn, Set.image_univ] at hbdd ⊢
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖c‖ * C, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hy
    rw [fderiv_const_smul_apply c v x, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (fderiv ℝ v x) (Set.mem_range_self x)) (norm_nonneg c)
  · obtain ⟨C, hC⟩ := hholder
    refine ⟨‖c‖₊ * C, holderWith_of_dist_le fun x y => ?_⟩
    rw [fderiv_const_smul_apply c v x, fderiv_const_smul_apply c v y]
    calc dist (c • fderiv ℝ v x) (c • fderiv ℝ v y)
        = ‖c‖ * dist (fderiv ℝ v x) (fderiv ℝ v y) := dist_smul₀ c (fderiv ℝ v x) (fderiv ℝ v y)
      _ ≤ ‖c‖ * ((C : ℝ) * dist x y ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC.dist_le x y) (norm_nonneg c)
      _ = ((‖c‖₊ * C : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
          rw [NNReal.coe_mul, coe_nnnorm]
          ring

end Work.FTS.Top
