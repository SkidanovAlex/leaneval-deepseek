/-
Copyright: work module for the Elgindi finite-time singularity project.

# `BoxRegAux/Defs` — auxiliary objects for `FTS_EllLimOK.BoxReg_of_uniform`

This module holds the small objects used by the proof that the pointwise limit of a sequence
of `C^∞` (on a neighbourhood of the closed quadrant) functions, with uniform box bounds on the
jets of order `≤ 3`, is `C²` on every closed box `[a,b] × [0,π/2]` (`0 < a ≤ b`):

* `ellCop x y` — the continuous linear functional `(u,v) ↦ u * x + v * y` on `ℝ × ℝ`, i.e. the
  Fréchet derivative of a function with partials `x`, `y` (`cop` of `LimTower_c2`, under a fresh
  name so that this file does not import that module);
* `copBilin` — the (continuous, linear) map `(x,y) ↦ ellCop x y`, used to assemble the *second*
  Fréchet derivative from the four second partials;
* `clampθ`, `boxClamp` — the `1`-Lipschitz retraction of the angle onto `[0,π/2]`, and the
  induced retraction of `ℝ × ℝ`; it is the identity on the closed quadrant, and is what makes the
  Arzelà–Ascoli extraction of `Submission.Work.FTS.StrongEps.LocUnif` applicable on an open set
  containing the closed box;
* `jetVec f p` — the six components (value-free) of the order-`≤ 2` jet of `f` at `p`:
  `∂_z f`, `∂_θ f`, `∂_z∂_z f`, `∂_θ∂_z f`, `∂_z∂_θ f`, `∂_θ∂_θ f`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.BoxReg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The linear functional with two given slopes -/

/-- The continuous linear functional `(u,v) ↦ u * x + v * y` on `ℝ × ℝ`: the Fréchet derivative
of a function whose two partial derivatives are `x` and `y`. -/
def ellCop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

theorem ellCop_apply (x y : ℝ) (v : ℝ × ℝ) : ellCop x y v = v.1 * x + v.2 * y := by
  simp only [ellCop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply]
  ring

@[simp] theorem ellCop_zero_zero : ellCop 0 0 = 0 :=
  ContinuousLinearMap.ext fun v => by simp [ellCop_apply]

/-! ## The `(x,y) ↦ ellCop x y` continuous linear map -/

/-- The continuous linear map `(x,y) ↦ ellCop x y`, from `ℝ × ℝ` to the space of continuous
linear functionals on `ℝ × ℝ`.  It is the "curried" version of the second derivative: composing
it with `(dA, dB)` (the two partials of the two first partials of a function) produces the second
Fréchet derivative. -/
def copBilin : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem copBilin_apply (a b : ℝ) : copBilin (a, b) = ellCop a b := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show ellCop a b v = v.1 * a + v.2 * b from by
    simp only [ellCop, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    ring]
  simp only [copBilin, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  have h1 : (ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) = a := rfl
  have h2 : (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) = b := rfl
  have h3 : (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 := rfl
  have h4 : (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 := rfl
  rw [h1, h2, h3, h4]
  ring

/-- The derivative of `y ↦ ellCop (A y) (B y)` computed from the within-derivatives of `A` and
`B`: the chain rule for the composition of the pair `(A, B)` with the continuous linear map
`copBilin`. -/
theorem hasFDerivWithinAt_ellCop {A B : (ℝ × ℝ) → ℝ} {a₁ a₂ b₁ b₂ : ℝ} {s : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} (hA : HasFDerivWithinAt A (ellCop a₁ a₂) s p)
    (hB : HasFDerivWithinAt B (ellCop b₁ b₂) s p) :
    HasFDerivWithinAt (fun y => ellCop (A y) (B y))
      (copBilin.comp ((ellCop a₁ a₂).prod (ellCop b₁ b₂))) s p := by
  have hpair : HasFDerivWithinAt (fun y => (A y, B y))
      ((ellCop a₁ a₂).prod (ellCop b₁ b₂)) s p := hA.prodMk hB
  have hcomp := (ContinuousLinearMap.hasFDerivWithinAt copBilin).comp p hpair
    (fun y _ => Set.mem_univ _)
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with y
    simp only [Function.comp_apply, copBilin_apply]
  · simp only [Function.comp_apply, copBilin_apply]

/-- Continuity of `y ↦ ellCop (A y) (B y)` from continuity of `A` and `B`. -/
theorem continuousWithinAt_ellCop {A B : (ℝ × ℝ) → ℝ} {s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hA : ContinuousWithinAt A s p) (hB : ContinuousWithinAt B s p) :
    ContinuousWithinAt (fun y => ellCop (A y) (B y)) s p := by
  have h1 : ContinuousWithinAt (fun y => copBilin (A y, B y)) s p :=
    (ContinuousLinearMap.continuous copBilin).continuousAt.comp_continuousWithinAt
      (hA.prodMk hB)
  exact h1.congr (fun y _ => (copBilin_apply (A y) (B y)).symm)
    (copBilin_apply (A p) (B p)).symm

/-! ## The clamping of the angle -/

/-- The `1`-Lipschitz retraction of the angle onto `[0,π/2]`: the identity on the closed
quadrant. -/
def clampθ (θ : ℝ) : ℝ := max 0 (min θ (Real.pi / 2))

theorem clampθ_nonneg (θ : ℝ) : 0 ≤ clampθ θ := le_max_left _ _

theorem clampθ_le (θ : ℝ) : clampθ θ ≤ Real.pi / 2 :=
  max_le (by linarith [Real.pi_pos]) (min_le_right _ _)

theorem clampθ_eq_of_mem {θ : ℝ} (h : θ ∈ Set.Icc 0 (Real.pi / 2)) : clampθ θ = θ := by
  rw [clampθ, min_eq_left h.2, max_eq_right h.1]

theorem abs_clampθ_sub_clampθ_le (x y : ℝ) : |clampθ x - clampθ y| ≤ |x - y| := by
  have h1 : |min x (Real.pi / 2) - min y (Real.pi / 2)| ≤ |x - y| := by
    refine le_trans (abs_min_sub_min_le_max x (Real.pi / 2) y (Real.pi / 2)) ?_
    rw [max_le_iff]
    exact ⟨le_rfl, by simp⟩
  have h2 : |max 0 (min x (Real.pi / 2)) - max 0 (min y (Real.pi / 2))| ≤
      |min x (Real.pi / 2) - min y (Real.pi / 2)| := by
    refine le_trans (abs_max_sub_max_le_max 0 (min x (Real.pi / 2)) 0 (min y (Real.pi / 2))) ?_
    rw [max_le_iff]
    exact ⟨by simp, le_rfl⟩
  calc |clampθ x - clampθ y| = |max 0 (min x (Real.pi / 2)) - max 0 (min y (Real.pi / 2))| := rfl
    _ ≤ |min x (Real.pi / 2) - min y (Real.pi / 2)| := h2
    _ ≤ |x - y| := h1

/-- The retraction of `ℝ × ℝ` onto the closed right half plane in the second variable, fixing
the closed quadrant `[0,∞) × [0,π/2]` (and in particular every box `cbox a b`). -/
def boxClamp (p : ℝ × ℝ) : ℝ × ℝ := (p.1, clampθ p.2)

@[simp] theorem boxClamp_fst (p : ℝ × ℝ) : (boxClamp p).1 = p.1 := rfl

@[simp] theorem boxClamp_snd (p : ℝ × ℝ) : (boxClamp p).2 = clampθ p.2 := rfl

theorem boxClamp_eq_of_mem {p : ℝ × ℝ} (hp : p.2 ∈ Set.Icc 0 (Real.pi / 2)) :
    boxClamp p = p := by
  obtain ⟨x, y⟩ := p
  have hp' : y ∈ Set.Icc 0 (Real.pi / 2) := hp
  simp only [boxClamp, clampθ_eq_of_mem hp']

theorem dist_boxClamp_le (p q : ℝ × ℝ) : dist (boxClamp p) (boxClamp q) ≤ dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq, sup_le_iff]
  constructor
  · simp only [boxClamp_fst]; exact le_sup_left
  · simp only [boxClamp_snd]
    refine le_trans ?_ le_sup_right
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clampθ_sub_clampθ_le _ _

/-- The clamped point of the box `[a,b] × [0,π/2]` lies in that box. -/
theorem boxClamp_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ cbox a b) :
    boxClamp p ∈ cbox a b := by
  rw [mem_cbox] at hp ⊢
  exact ⟨hp.1, clampθ_nonneg _, clampθ_le _⟩

/-- `boxClamp` fixes the points of the box `[a,b] × [0,π/2]`. -/
theorem boxClamp_eq_of_mem_cbox {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ cbox a b) :
    boxClamp p = p := by
  rw [mem_cbox] at hp
  exact boxClamp_eq_of_mem hp.2

/-! ## The order-`≤ 2` jet vector -/

/-- The six components of the order-`≤ 2` jet of `f`, in the order
`∂_z`, `∂_θ`, `∂_z∂_z`, `∂_θ∂_z`, `∂_z∂_θ`, `∂_θ∂_θ`. -/
def jetVec (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  ![Work.Spaces.pz f p.1 p.2, Work.Spaces.pth f p.1 p.2,
    Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2, Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2,
    Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2, Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2]

theorem jetVec_zero (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 0 = Work.Spaces.pz f p.1 p.2 := by simp [jetVec]

theorem jetVec_one (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 1 = Work.Spaces.pth f p.1 p.2 := by simp [jetVec]

theorem jetVec_two (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 2 = Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 := by simp [jetVec]

theorem jetVec_three (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 3 = Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 := by simp [jetVec]

theorem jetVec_four (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 4 = Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2 := by simp [jetVec]

theorem jetVec_five (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    jetVec f p 5 = Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2 := by simp [jetVec]

/-- Componentwise extraction of uniform convergence from uniform convergence of the jet family. -/
theorem tendstoUniformlyOn_jetVec_component {F : ℕ → ℝ × ℝ → (Fin 6 → ℝ)}
    {g : ℝ × ℝ → (Fin 6 → ℝ)} {s : Set (ℝ × ℝ)}
    (h : TendstoUniformlyOn F g Filter.atTop s) (m : Fin 6) :
    TendstoUniformlyOn (fun n p => F n p m) (fun p => g p m) Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn p hp
  exact lt_of_le_of_lt (dist_le_pi_dist (g p) (F n p) m) (hn p hp)

/-- **Componentwise bound of the jet vector**: the six components of `jetVec f p` are bounded by
`C` as soon as the six partials are. -/
theorem abs_jetVec_le {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} {C : ℝ}
    (h : |Work.Spaces.pz f p.1 p.2| ≤ C ∧ |Work.Spaces.pth f p.1 p.2| ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2| ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2| ≤ C) :
    ∀ m : Fin 6, |jetVec f p m| ≤ C := by
  intro m
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  fin_cases m
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- **Componentwise Lipschitz bound of the jet vector**: the six components of `jetVec f` are
`C`-Lipschitz on a set as soon as the six partials are. -/
theorem abs_jetVec_sub_le {f : ℝ → ℝ → ℝ} {p q : ℝ × ℝ} {C : ℝ}
    (h : |Work.Spaces.pz f p.1 p.2 - Work.Spaces.pz f q.1 q.2| ≤ C ∧
      |Work.Spaces.pth f p.1 p.2 - Work.Spaces.pth f q.1 q.2| ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - Work.Spaces.pz (Work.Spaces.pz f) q.1 q.2|
        ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - Work.Spaces.pth (Work.Spaces.pz f) q.1 q.2|
        ≤ C ∧
      |Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2 - Work.Spaces.pz (Work.Spaces.pth f) q.1 q.2|
        ≤ C ∧
      |Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2 - Work.Spaces.pth (Work.Spaces.pth f) q.1 q.2|
        ≤ C) :
    ∀ m : Fin 6, |jetVec f p m - jetVec f q m| ≤ C := by
  intro m
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  fin_cases m
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end Work.FTS_EllLimOK
