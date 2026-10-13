/-
# `Work.FTS.GalLimit.GalWeak.bslOp_galPsi`

**The elliptic law survives the Galerkin superposition.**  Let `EllSol` be an elliptic solution
operator for the Galerkin basis `φ` (each `EllSol (φ k)` solves `bslOp α Ψ = φ k` in the strong
sense `IsBslSol`, each is `C^∞` on the open quadrant, and `EllSol` is additive on the Galerkin
span), and let `Φs` solve the elliptic problem with the self-similar source `F_* α`, `C^∞` on the
open quadrant.  Then `Φs + EllSol (galFun φ c)` solves the elliptic problem with source
`F_* α + galFun φ c`:

  `bslOp α (Φs + EllSol (galFun φ c)) = F_* α + galFun φ c` on the open quadrant `Qd`.

This is the "`hGalWeak'` at a single coefficient vector" node of the passage to the limit
(`Submission/Work/FTS/GalLimit/Defs.lean`, `hGalWeak'`): the Galerkin elliptic identities
`bslOp α (EllSol g_n(τ)) = g_n(τ)` have to pass to the tested limit
`IsBslSolPos α (F_* + g(τ)) (Φ(τ))`, and the first thing needed is that the *linear* solution
operator produces solutions of the summed source.

## The mathematical content

`bslOp` is a linear second-order differential operator, and `EllSol` is linear on the Galerkin
span by `hEllLin`.  Hence

  `bslOp α (Φs + EllSol (galFun φ c)) = bslOp α Φs + bslOp α (EllSol (galFun φ c))`   (additivity)
  `= F_* α + bslOp α (∑_k c k · EllSol (φ k))`                                        (hypotheses)
  `= F_* α + ∑_k c k · bslOp α (EllSol (φ k)) = F_* α + ∑_k c k · φ k = F_* α + galFun φ c`.

## What has to be built, and why

Additivity for **two** summands is `Work.Elliptic.bslOp_add`, and it demands joint `C²` of both
summands at the point — `deriv` in Mathlib is *totalised* (it returns the junk value `0` at a
non-differentiable point), so neither additivity *nor* homogeneity is free.  We therefore record,
in this file:

* `pz_const_mul`, `pth_const_mul`, `pzIter_const_mul`, `pthIter_const_mul`, `Lzero_const_mul`,
  `bslOp_const_mul` — homogeneity of the individual slots of `bslOp` in a *constant*
  (`deriv_const_mul_field` is unconditional, unlike `deriv_const_mul`);
* `bslOp_zero` — `bslOp α 0 = 0` (needs no differentiability: every slot is a derivative of `0`);
* `contDiffAt_uncurry_const_mul`, `contDiffAt_uncurry_finset_sum` — the `C²` bookkeeping for
  constant multiples and finite sums of the summands;
* `bslOp_finset_sum` — additivity of `bslOp` over an arbitrary finite sum, by induction from
  `bslOp_add`, the differentiability of the partial sums being supplied by the previous lemma.

The `C²` hypotheses of the main theorem come from `SmoothOpen`, which is `C^∞` on the open
quadrant `Q0 = Qd`; a point of `Qd` is an interior point of `Q0`, so `SmoothOpen.forall` followed
by `ContDiffOn.contDiffAt` supplies them.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalLimit.Defs
import Submission.Work.Elliptic.bslOp_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit.GalWeak

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Homogeneity of the slots of `bslOp` in a constant -/

/-- `∂_z` commutes with multiplication by a constant. -/
lemma pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pz f z θ := by
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- Function-level form of `pz_const_mul`. -/
lemma pz_const_mul_fun (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ; exact pz_const_mul c f z θ

/-- `∂_θ` commutes with multiplication by a constant. -/
lemma pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pth f z θ := by
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- Function-level form of `pth_const_mul`. -/
lemma pth_const_mul_fun (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ; exact pth_const_mul c f z θ

/-- `∂_z^k` commutes with multiplication by a constant. -/
lemma pzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter n f z θ := by
  induction n with
  | zero => funext z θ; simp [Work.Spaces.pzIter]
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ, pz_const_mul_fun]

/-- `∂_θ^k` commutes with multiplication by a constant. -/
lemma pthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter n f z θ := by
  induction n with
  | zero => funext z θ; simp [Work.Spaces.pthIter]
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ, pth_const_mul_fun]

/-- `L₀` is homogeneous in a constant: `L₀ (c · f) = c · L₀ f`. -/
lemma Lzero_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun z θ => c * f z θ) z θ = c * Work.Elliptic.Lzero f z θ := by
  have h2 : Work.Spaces.pthIter 2 (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.pthIter 2 f z θ := congrFun (congrFun (pthIter_const_mul c f 2) z) θ
  have htan : (fun z' θ' => Real.tan θ' * (c * f z' θ'))
      = (fun z' θ' => c * (Real.tan θ' * f z' θ')) := by funext z' θ'; ring
  have h3 : Work.Spaces.pth (fun z' θ' => c * (Real.tan θ' * f z' θ')) z θ
      = c * Work.Spaces.pth (fun z' θ' => Real.tan θ' * f z' θ') z θ :=
    congrFun (congrFun (pth_const_mul_fun c (fun z' θ' => Real.tan θ' * f z' θ')) z) θ
  simp only [Work.Elliptic.Lzero]
  rw [h2, htan, h3]
  ring

/-- `bslOp` is homogeneous in a constant.  Unlike additivity this needs **no** differentiability
hypothesis: `deriv_const_mul_field` is unconditional (at a non-differentiable point both sides
vanish). -/
lemma bslOp_const_mul (α c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α (fun z θ => c * f z θ) z θ
      = c * Work.Elliptic.bslOp α f z θ := by
  have h2 := congrFun (congrFun (pzIter_const_mul c f 2) z) θ
  have h1 := pz_const_mul c f z θ
  have hL := Lzero_const_mul c f z θ
  simp only [Work.Elliptic.bslOp_apply]
  rw [h2, h1, hL]
  ring

/-- `bslOp` kills the zero function. -/
lemma bslOp_zero (α z θ : ℝ) :
    Work.Elliptic.bslOp α (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, Work.Spaces.pzIter,
    Work.Spaces.pz, Work.Spaces.pthIter, Work.Spaces.pth]

/-! ## `C²` bookkeeping for constant multiples and finite sums -/

/-- A constant multiple of a jointly `C²` function is jointly `C²`. -/
lemma contDiffAt_uncurry_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z' θ' => c * f z' θ')) (z, θ) := by
  have key : Function.uncurry (fun z' θ' => c * f z' θ')
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; simp only [Function.uncurry]
  rw [key]
  exact contDiffAt_const.mul hf

/-- A finite linear combination of jointly `C²` functions is jointly `C²`. -/
lemma contDiffAt_uncurry_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (Function.uncurry (f i)) (z, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z' θ' => ∑ i ∈ s, c i * f i z' θ')) (z, θ) := by
  have key : Function.uncurry (fun z' θ' => ∑ i ∈ s, c i * f i z' θ')
      = fun p : ℝ × ℝ => ∑ i ∈ s, c i * Function.uncurry (f i) p := by
    funext p; simp only [Function.uncurry]
  rw [key]
  exact ContDiffAt.sum (fun i hi => contDiffAt_const.mul (hf i hi))

/-! ## Additivity of `bslOp` over a finite sum -/

/-- **Additivity of `bslOp` over an arbitrary finite sum.**  The partial sums are `C²` at the
point because every summand is (`contDiffAt_uncurry_finset_sum`, `contDiffAt_uncurry_const_mul`),
which is all that `bslOp_add` asks for. -/
lemma bslOp_finset_sum {ι : Type*} (α : ℝ) (c : ι → ℝ) (f : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0)
    (hf : ∀ i : ι, ContDiffAt ℝ 2 (Function.uncurry (f i)) (z, θ)) (s : Finset ι) :
    Work.Elliptic.bslOp α (fun z' θ' => ∑ i ∈ s, c i * f i z' θ') z θ
      = ∑ i ∈ s, c i * Work.Elliptic.bslOp α (f i) z θ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (fun z' θ' => ∑ i ∈ (∅ : Finset ι), c i * f i z' θ')
        = (fun _ _ => (0 : ℝ)) from by funext z' θ'; simp]
    rw [bslOp_zero]
    simp
  | insert i s hi ih =>
    have hfun : (fun z' θ' => ∑ j ∈ insert i s, c j * f j z' θ')
        = fun z' θ' => c i * f i z' θ' + (∑ j ∈ s, c j * f j z' θ') := by
      funext z' θ'; rw [Finset.sum_insert hi]
    rw [hfun]
    rw [Work.Elliptic.bslOp_add α (fun z' θ' => c i * f i z' θ')
        (fun z' θ' => ∑ j ∈ s, c j * f j z' θ') z θ hcos
        (contDiffAt_uncurry_const_mul (c i) (hf i))
        (contDiffAt_uncurry_finset_sum s c f z θ (fun j _ => hf j))]
    rw [bslOp_const_mul, ih, Finset.sum_insert hi]

/-! ## The Galerkin superposition solves the summed equation -/

theorem bslOp_galPsi {α : ℝ} {φ : ℕ → Work.FTS.Galerkin.Fn} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hStar : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φs)
    (hsmΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hEllLin : ∀ (n : ℕ) (c : Fin n → ℝ),
      EllSol (Work.FTS.Galerkin.galFun φ c)
        = fun z θ => ∑ k : Fin n, c k * EllSol (φ k) z θ)
    (hEll : ∀ k : ℕ, Work.Elliptic.IsBslSol α (φ k) (EllSol (φ k)))
    (hsmE : ∀ k : ℕ, Work.FTS.EllipticEst.SmoothOpen (EllSol (φ k)))
    (n : ℕ) (c : Fin n → ℝ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp α (fun z θ => Φs z θ + EllSol (Work.FTS.Galerkin.galFun φ c) z θ) z θ
        = Work.Construction.Fstar α z θ + Work.FTS.Galerkin.galFun φ c z θ := by
  intro z θ hmem
  -- the open quadrant `Qd` of `Work.Construction` is `Q0` of the elliptic estimates
  have hmemQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hmem
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hmemQ
  have hcos : Real.cos θ ≠ 0 := by
    intro h
    have hpos := Real.cos_pos_of_mem_Ioo (x := θ) ⟨by linarith [Real.pi_pos], hθ2⟩
    linarith
  -- `C²` of the two summands at the point, from `SmoothOpen` (smoothness on the open quadrant)
  have hC2_Φ : ContDiffAt ℝ 2 (Function.uncurry Φs) (z, θ) :=
    (Work.FTS.EllipticEst.SmoothOpen.forall hsmΦs 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmemQ)
  have hC2_k : ∀ k : ℕ, ContDiffAt ℝ 2 (Function.uncurry (EllSol (φ k))) (z, θ) := fun k =>
    (Work.FTS.EllipticEst.SmoothOpen.forall (hsmE k) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmemQ)
  have hC2_E : ContDiffAt ℝ 2
      (Function.uncurry (EllSol (Work.FTS.Galerkin.galFun φ c))) (z, θ) := by
    rw [hEllLin n c]
    exact contDiffAt_uncurry_finset_sum Finset.univ c (fun k : Fin n => EllSol (φ (k : ℕ))) z θ
      (fun k _ => hC2_k (k : ℕ))
  -- the linearity of `EllSol` on the Galerkin span turns the Galerkin combination into a solution
  have hE : Work.Elliptic.bslOp α (EllSol (Work.FTS.Galerkin.galFun φ c)) z θ
      = Work.FTS.Galerkin.galFun φ c z θ := by
    rw [hEllLin n c]
    rw [bslOp_finset_sum α c (fun k : Fin n => EllSol (φ (k : ℕ))) z θ hcos
      (fun k => hC2_k (k : ℕ)) Finset.univ]
    have hk : ∀ k : Fin n, Work.Elliptic.bslOp α (EllSol (φ (k : ℕ))) z θ = φ (k : ℕ) z θ :=
      fun k => (hEll (k : ℕ)).1 z hz θ hθ hθ2
    simp only [hk]
    rfl
  rw [Work.Elliptic.bslOp_add α Φs (EllSol (Work.FTS.Galerkin.galFun φ c)) z θ hcos hC2_Φ hC2_E,
    hStar.1 z hz θ hθ hθ2, hE]

end Work.FTS.GalLimit.GalWeak
