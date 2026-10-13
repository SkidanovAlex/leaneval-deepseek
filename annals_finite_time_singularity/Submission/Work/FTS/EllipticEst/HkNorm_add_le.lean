/-
# Subadditivity of the weighted `ℋ^k`-norm

`Work.Spaces.HkNorm α k` is the norm of the paper's weighted space `ℋ^k` (Elgindi,
*Finite-time singularity formation for `C^{1,α}` solutions to the incompressible Euler
equations on `ℝ³`*, Annals of Math. **194** (2021), §Notation and §H2).  Its square is the
iterated integral of a sum of squares of weighted derivatives,

`HkSq α k f = ∫_{z∈[0,∞)} ∫_{θ∈[0,π/2]} HkIntegrand α k f z θ dθ dz`,

so the triangle inequality is `(a+b)² ≤ 2a² + 2b²` summand by summand and then monotonicity of
the integral:

`|f+g|²_{ℋ^k} ≤ 2|f|²_{ℋ^k} + 2|g|²_{ℋ^k}`,

which by `√(2x+2y) ≤ √2(√x+√y)` gives

`|f+g|_{ℋ^k} ≤ √2 (|f|_{ℋ^k} + |g|_{ℋ^k})`.

The smoothness hypothesis of the statement is `C^n` on the *open* quadrant
`Q = (0,∞) × (0,π/2)` for every `n : ℕ`.  In this Mathlib that is exactly the genuine smooth
order `∞ = Work.Stability.smoothOrder` (the order `⊤ : ℕ∞ω` is analyticity, so the analytic
`SmoothNbhd` route of `Submission/Work/Elliptic/HkSq_add_le.lean` does not apply).  Since
`deriv_add` needs differentiability *at the point*, additivity of the iterated operators
`D_z^i`, `D_z^j D_θ^i` is only obtained on the open quadrant `Q`; on the two boundary lines
`z = 0` and `sin(2θ) = 0` the integrand vanishes identically (the weight `w 0 = 0` kills every
term at `z = 0`, and at `sin(2θ) = 0` the first sum is killed by `1/0 = 0` while every
surviving summand of the second sum carries a factor `D_θ^i` with `i ≥ 1`, hence a factor
`sin(2θ) = 0`).  Both boundary cases therefore contribute the trivial inequality `0 ≤ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The open quadrant and the smoothness order -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the smoothness hypothesis of
`HkNorm_add_le` is imposed. -/
private abbrev quadV : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private theorem isOpen_quadV : IsOpen quadV := isOpen_Ioi.prod isOpen_Ioo

private theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- `C^n` for every natural number `n` is the genuine smooth order `∞`. -/
private theorem contDiffOn_smoothOrder_of_forall_nat {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (h : ∀ n : ℕ, ContDiffOn ℝ n f s) : ContDiffOn ℝ Work.Stability.smoothOrder f s := by
  intro x hx m _
  exact h m x hx m le_rfl

/-- Slices of a function smooth on the open quadrant are differentiable in `z`. -/
private theorem slice_diffAt_fst {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h) quadV)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z :=
  ((Work.FTS.LocData.contDiffOn_slice_z (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
      hh hθ).differentiableOn smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- Slices of a function smooth on the open quadrant are differentiable in `θ`. -/
private theorem slice_diffAt_snd {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h) quadV)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ :=
  ((Work.FTS.LocData.contDiffOn_slice_θ (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
      hh hz).differentiableOn smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-! ## Additivity of the iterated operators on the open quadrant -/

/-- Two functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
private theorem DzIter_congr_of_quad {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) quadV) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) quadV := by
  induction j with
  | zero => exact h
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      show z * deriv (fun z' => Work.Spaces.DzIter n F z' θ) z
          = z * deriv (fun z' => Work.Spaces.DzIter n G z' θ) z
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih (show (z', θ) ∈ quadV from ⟨hz', hθ⟩)

/-- The iterated operators `D_z^j` are additive on the open quadrant. -/
private theorem DzIter_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter j f z θ
        + Work.Spaces.DzIter j g z θ)) quadV := by
  induction j with
  | zero => rintro ⟨z, θ⟩ -; rfl
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (show (z', θ) ∈ quadV from ⟨hz', hθ⟩)
      have h1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        slice_diffAt_fst (Work.FTS.LocData.contDiffOn_DzIter isOpen_quadV hf n) hz hθ
      have h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        slice_diffAt_fst (Work.FTS.LocData.contDiffOn_DzIter isOpen_quadV hg n) hz hθ
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add h1 h2
      show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ) z
          = z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + z * deriv (fun z' => Work.Spaces.DzIter n g z' θ) z
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated operators `D_θ^i` are additive on the open quadrant. -/
private theorem DthIter_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DthIter i f z θ
        + Work.Spaces.DthIter i g z θ)) quadV := by
  induction i with
  | zero => rintro ⟨z, θ⟩ -; rfl
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih (show (z, θ') ∈ quadV from ⟨hz, hθ'⟩)
      have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        slice_diffAt_snd (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hf n) hz hθ
      have h2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        slice_diffAt_snd (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hg n) hz hθ
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add h1 h2
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ') θ
          = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant. -/
private theorem mixed_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i f z θ
        + Work.Spaces.mixed j i g z θ)) quadV := by
  have hDth := DthIter_add_of_contDiffOn hf hg i
  have hcongr := DzIter_congr_of_quad hDth j
  have hadd := DzIter_add_of_contDiffOn
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hf i)
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hg i) j
  rintro ⟨z, θ⟩ hzθ
  exact (hcongr hzθ).trans (hadd hzθ)

/-! ## Vanishing of the integrand on the two boundary lines -/

/-- At `sin(2θ) = 0` every `D_θ`-iterate of positive order vanishes at that same `θ` (the
outermost `D_θ` carries the factor `sin(2θ)`). -/
private theorem DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

/-- A function whose `θ`-slice vanishes identically has vanishing `D_z`-iterates there. -/
private theorem DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]
      simp

/-- At `sin(2θ) = 0` every mixed derivative `D_z^j D_θ^i` with `i ≥ 1` vanishes at `(z,θ)`. -/
private theorem mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- On the angular boundary `sin(2θ) = 0` the `ℋ^k`-integrand vanishes: the first sum is killed
by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its summands. -/
private theorem HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- On the radial boundary `z = 0` the `ℋ^k`-integrand vanishes, because the weight
`w 0 = (1+0)²/0² = 0` kills both sums. -/
private theorem HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The algebraic core: sums of squares of sums -/

private theorem sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z,θ)`. -/
private theorem HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hm p.1 p.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The pointwise inequality on the closed quadrant -/

/-- **The pointwise inequality for the `ℋ^k`-integrand** on the whole closed quadrant: for
`(z,θ) ∈ [0,∞) × [0,π/2]`,

`HkIntegrand (f+g) ≤ 2·HkIntegrand f + 2·HkIntegrand g`.

On the interior this is additivity of the operators plus `(a+b)² ≤ 2a² + 2b²`; on the two
boundary lines both sides vanish, the left-hand side by the vanishing lemmas above and the
right-hand side because each summand does. -/
theorem HkIntegrand_add_le_of_contDiffOn (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k (fun z θ => f z θ + g z θ) hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k f g z θ
      (fun i => DzIter_add_of_contDiffOn hf hg i (show (z, θ) ∈ quadV from ⟨hzpos, hθ1, hθ2⟩))
      (fun i j => mixed_add_of_contDiffOn hf hg j i
        (show (z, θ) ∈ quadV from ⟨hzpos, hθ1, hθ2⟩))

/-! ## Lifting the pointwise inequality to `HkSq`, and then to the norm -/

/-- **Subadditivity of `HkSq`.**  Given the pointwise inequality for the integrands and the
honest integrability certificates (`HkMem`) for `f` and `g`, integrating over `θ` and then over
`z` gives

`HkSq α k (f+g) ≤ 2·HkSq α k f + 2·HkSq α k g`.

No integrability of `HkIntegrand (f+g)` is needed: `integral_mono_of_nonneg` asks only for the
*upper* function to be integrable, and the upper function is `2·HkIntegrand f + 2·HkIntegrand g`,
integrable by `hmf` and `hmg`. -/
theorem HkSq_add_le_of_pointwise (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => hpt z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2)
          ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k _ z θ)
    ((hmf.2.const_mul 2).add (hmg.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_add (hmf.2.const_mul 2) (hmg.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- Subadditivity of the square root: `√(x+y) ≤ √x + √y` for `x,y ≥ 0`. -/
private theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- The `√2`-form used to pass from the squared estimate to the norm. -/
theorem sqrt_two_mul_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (2 * x + 2 * y) ≤ Real.sqrt 2 * (Real.sqrt x + Real.sqrt y) := by
  have hsum : Real.sqrt (2 * x + 2 * y) = Real.sqrt 2 * Real.sqrt (x + y) := by
    rw [show 2 * x + 2 * y = 2 * (x + y) by ring, Real.sqrt_mul (by norm_num)]
  rw [hsum]
  exact mul_le_mul_of_nonneg_left (sqrt_add_le hx hy) (Real.sqrt_nonneg 2)

/-! ## The statement -/

theorem HkNorm_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  have hf' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV :=
    contDiffOn_smoothOrder_of_forall_nat hf
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV :=
    contDiffOn_smoothOrder_of_forall_nat hg
  have hpt := HkIntegrand_add_le_of_contDiffOn α k hf' hg'
  have hsq := HkSq_add_le_of_pointwise α k hmf hmg hpt
  have hx : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hy : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  have hroot : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g) :=
    Real.sqrt_le_sqrt hsq
  refine le_trans hroot ?_
  have hsqrt : Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g)
      = Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) := by
    rw [show 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
        = 2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) by ring,
      Real.sqrt_mul (by norm_num)]
  rw [hsqrt, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  exact mul_le_mul_of_nonneg_left (sqrt_add_le hx hy) (Real.sqrt_nonneg 2)

end Work.FTS.EllipticEst
