/-
# `Work.FTS.PressureOn.MollAux.exists_const_Dpair_aux` — the weak Weyl lemma

**Statement.**  Let `q : ℝ³ → ℝ` and `Φ : ℝ³ → ℝ³` be continuous and vanish at infinity, and let
the pairing `Dpair q Φ ψ = ∫ ⟪Φ, ψ⟫ + ∫ q · div ψ` of the distribution `D := Φ − ∇q` annihilate
every gradient and every curl of a smooth compactly supported test object:

* `⟨D, ∇φ⟩ = 0` for every test function `φ` (`hdiv`), i.e. `Δq = div Φ` weakly;
* `⟨D, curl ψ⟩ = 0` for every test field `ψ` (`hcurl`), i.e. `curl Φ = 0` weakly.

Then `⟨D, ψ⟩` depends on the test field only through its total integral: there is `c ∈ ℝ³` with
`Dpair q Φ ψ = ⟪c, ∫ψ⟫` for every smooth compactly supported `ψ`.

## Route

1. **Mollify.**  With `qₙ := moll n q`, `Φₙ := mollV n Φ` (`MollDefs`) the difference field
   `Vₙ := Φₙ − ∇qₙ` is `C^∞`, bounded and *weakly harmonic*:
   `∫ ⟪Vₙ, ΔW⟫ = 0` for every test field `W` (this is
   `MollAux.weak_harmonic_mollified_diff`, proved from `Dpair_convolution`,
   `convolution_laplaceTraceVec_comm` and the M2 identity for the pair `(q, Φ)`).
   By `MollAux.eq_const_of_weak_harmonic_smooth` (weak harmonicity + boundedness + smoothness
   gives constancy, via Green's second identity `integral_inner_laplaceTraceVec_comm`, the
   du-Bois-Reymond lemma `BSSwirl.eq_zero_of_forall_inner_test` and the heat-kernel Liouville
   theorem `Auxiliary.bounded_harmonic_const`), `Vₙ = cₙ` is a constant vector; the bound comes
   from `cocompact_bound_vec`, `tendsto_cocompact_bound_scalar` and the mollifier estimates of
   `MollAux.moll_smooth_bounded`.

2. **The pairing of a mollified test field.**  For every test field `ψ` and every `n`,
   `Dpair q Φ (mollV n ψ) = Dpair qₙ Φₙ ψ = ∫ ⟪Vₙ, ψ⟫ = ⟪cₙ, ∫ψ⟫`
   (`Dpair_convolution`, `Dpair_eq_integral_sub_gradient_of_smooth`,
   `Auxiliary.integral_inner_eq_inner_integral`).

3. **Mean-zero test fields.**  If `∫ψ = 0` then `Dpair q Φ (mollV n ψ) = 0` for every `n`, and
   `Dpair q Φ (mollV n ψ) → Dpair q Φ ψ` as `n → ∞` (`MollAux.moll_tendsto`); hence
   `Dpair q Φ ψ = 0`.

4. **The constant.**  Take the test function `θ := rho 0` with `∫θ = 1` and put
   `c := ∫ x, θ x • Φ x + ∫ x, q x • ∇θ x`.  For an arbitrary test field `ψ`,
   `Θ := θ • ∫ψ` is a test field with `∫Θ = ∫ψ`, so `ψ − Θ` is mean-zero and
   `Dpair q Φ ψ = Dpair q Φ Θ` (linearity of `Dpair` in the test field, `Dpair_sub`).
   Computing `Dpair q Φ Θ` with the divergence of `Θ` (`Green.div_smul_eq`) and the commutation
   of the inner product with the Bochner integral gives `Dpair q Φ Θ = ⟪c, ∫ψ⟫`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.MollAux.Dpair_convolution
import Submission.Work.FTS.PressureOn.MollAux.moll_smooth_bounded
import Submission.Work.FTS.PressureOn.MollAux.moll_tendsto
import Submission.Work.FTS.PressureOn.MollAux.rho_props
import Submission.Work.FTS.PressureOn.MollAux.laplaceTraceVec_smooth_compact
import Submission.Work.FTS.PressureOn.MollAux.eq_const_of_weak_harmonic_smooth
import Submission.Work.FTS.PressureOn.MollAux.weak_harmonic_mollified_diff
import Submission.Work.FTS.PressureOn.MollAux.Dpair_eq_integral_sub_gradient_of_smooth
import Submission.Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const
import Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_laplaceTraceVec_comm
import Submission.Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec
import Submission.Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity
import Submission.Work.FTS.PressureOn.Auxiliary.gradient_smooth_norm
import Submission.Work.FTS.PressureOn.Auxiliary.cocompact_bound_vec
import Submission.Work.FTS.PressureOn.Auxiliary.tendsto_cocompact_bound_scalar
import Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_eq_inner_integral
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter FiniteTimeSingularity
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.MollAux

/-! ## Small helpers -/

/-- The pairing `x ↦ ⟪Φ x, f x⟫` has compact support as soon as `f` does. -/
lemma hasCompactSupport_inner_right {Φ f : R3 → R3} (hfc : HasCompactSupport f) :
    HasCompactSupport (fun x => inner ℝ (Φ x) (f x)) :=
  HasCompactSupport.intro hfc (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right])

/-- The inner product against a *fixed* vector in the **second** slot commutes with the Bochner
integral (mirror of `Auxiliary.integral_inner_eq_inner_integral`, where the fixed vector sits in
the first slot). -/
lemma integral_inner_eq_inner_integral_right (g : R3) (ψ : R3 → R3) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, inner ℝ (ψ x) g = inner ℝ (∫ x, ψ x) g := by
  have h := Auxiliary.integral_inner_eq_inner_integral g ψ hψ hψc
  rw [show (∫ x : R3, inner ℝ (ψ x) g) = ∫ x : R3, inner ℝ g (ψ x) from
        integral_congr_ae (Eventually.of_forall fun x => (real_inner_comm (ψ x) g).symm),
      show inner ℝ (∫ x : R3, ψ x) g = inner ℝ g (∫ x : R3, ψ x) from
        (real_inner_comm (∫ x : R3, ψ x) g).symm]
  exact h

/-- Linearity of the pairing `Dpair` in the test field, in the form needed for the argument:
for two smooth compactly supported fields `f`, `h`,
`Dpair q Φ (f - h) = Dpair q Φ f - Dpair q Φ h`. -/
lemma Dpair_sub (q : R3 → ℝ) (Φ : R3 → R3) (hq : Continuous q) (hΦ : Continuous Φ)
    (f h : R3 → R3) (hf : ∀ n : ℕ, ContDiff ℝ n f) (hfc : HasCompactSupport f)
    (hg : ∀ n : ℕ, ContDiff ℝ n h) (hgc : HasCompactSupport h) :
    Dpair q Φ (f - h) = Dpair q Φ f - Dpair q Φ h := by
  have hfcont : Continuous f := (hf 0).continuous
  have hgcont : Continuous h := (hg 0).continuous
  have hfdiv : Continuous (fun x => FiniteTimeSingularity.div f x) :=
    (Auxiliary.contDiff_div f hf 0).continuous
  have hgdiv : Continuous (fun x => FiniteTimeSingularity.div h x) :=
    (Auxiliary.contDiff_div h hg 0).continuous
  have hfcdiv : HasCompactSupport (fun x => FiniteTimeSingularity.div f x) :=
    hasCompactSupport_div f hfc
  have hgcdiv : HasCompactSupport (fun x => FiniteTimeSingularity.div h x) :=
    hasCompactSupport_div h hgc
  have hI1 : Integrable (fun x => inner ℝ (Φ x) (f x)) :=
    (hΦ.inner hfcont).integrable_of_hasCompactSupport (hasCompactSupport_inner_right hfc)
  have hI2 : Integrable (fun x => inner ℝ (Φ x) (h x)) :=
    (hΦ.inner hgcont).integrable_of_hasCompactSupport (hasCompactSupport_inner_right hgc)
  have hJ1 : Integrable (fun x => q x * FiniteTimeSingularity.div f x) :=
    (hq.mul hfdiv).integrable_of_hasCompactSupport hfcdiv.mul_left
  have hJ2 : Integrable (fun x => q x * FiniteTimeSingularity.div h x) :=
    (hq.mul hgdiv).integrable_of_hasCompactSupport hgcdiv.mul_left
  have hdiv : ∀ x, FiniteTimeSingularity.div (f - h) x
      = FiniteTimeSingularity.div f x - FiniteTimeSingularity.div h x := fun x =>
    Green.div_sub_eq f h x
      ((hf 1).differentiable (by norm_num) x)
      ((hg 1).differentiable (by norm_num) x)
  rw [Dpair_apply, Dpair_apply, Dpair_apply]
  have e1 : (fun x => inner ℝ (Φ x) ((f - h) x))
      = fun x => inner ℝ (Φ x) (f x) - inner ℝ (Φ x) (h x) := by
    funext x
    rw [Pi.sub_apply, inner_sub_right]
  have e2 : (fun x => q x * FiniteTimeSingularity.div (f - h) x)
      = fun x => q x * FiniteTimeSingularity.div f x - q x * FiniteTimeSingularity.div h x := by
    funext x
    rw [hdiv x]
    ring
  rw [e1, e2, integral_sub hI1 hI2, integral_sub hJ1 hJ2]
  ring

/-! ## The main theorem -/

theorem exists_const_Dpair_aux (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0))
    (hdiv : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) →
      HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
        Work.FTS.PressureOn.Dpair q Φ ψ = inner ℝ c (∫ x, ψ x) := by
  -- boundedness of `Φ` and `q`, from the decay at infinity
  obtain ⟨DΦ, hDΦ⟩ := Auxiliary.cocompact_bound_vec hΦ hΦ0
  obtain ⟨Dq, hDq⟩ := (Auxiliary.tendsto_cocompact_bound_scalar hq hq0).1
  -- ## Step 1: the mollified difference field `Vₙ = mollV n Φ - ∇(moll n q)` is constant
  have hVconst : ∀ n : ℕ, ∃ c : R3, ∀ x, mollV n Φ x - gradient (moll n q) x = c := by
    intro n
    refine eq_const_of_weak_harmonic_smooth _ ?_ ?_ ?_
    · intro m
      exact (MollSB.contDiff_mollV n Φ hΦ m).sub
        ((Auxiliary.gradient_smooth_norm (moll n q) (MollSB.contDiff_moll n q hq)).1 m)
    · refine ⟨DΦ + Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖, fun x => ?_⟩
      have h1 : ‖mollV n Φ x‖ ≤ DΦ := MollSB.norm_mollV_le n Φ DΦ hDΦ x
      have h2 : ‖gradient (moll n q) x‖ ≤ Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖ := by
        rw [(Auxiliary.gradient_smooth_norm (moll n q) (MollSB.contDiff_moll n q hq)).2 x]
        exact MollSB.norm_fderiv_moll_le n q hq Dq hDq x
      calc ‖mollV n Φ x - gradient (moll n q) x‖
          ≤ ‖mollV n Φ x‖ + ‖gradient (moll n q) x‖ := norm_sub_le _ _
        _ ≤ DΦ + Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖ := add_le_add h1 h2
    · intro W hW hWc
      exact weak_harmonic_mollified_diff q Φ hq hΦ hdiv hcurl n W hW hWc
  choose c hc using hVconst
  -- ## Step 2: the pairing against a mollified test field only sees `∫ψ`
  have hstep2 : ∀ (n : ℕ) (ψ : R3 → R3), (∀ m : ℕ, ContDiff ℝ m ψ) → HasCompactSupport ψ →
      Dpair q Φ (mollV n ψ) = inner ℝ (c n) (∫ x, ψ x) := by
    intro n ψ hψ hψc
    have hrp := rho_props n
    have hA : Dpair q Φ (mollV n ψ) = Dpair (moll n q) (mollV n Φ) ψ := by
      show Dpair q Φ (MeasureTheory.convolution (rho n) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          = Dpair (MeasureTheory.convolution (rho n) q (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (MeasureTheory.convolution (rho n) Φ (ContinuousLinearMap.lsmul ℝ ℝ) volume) ψ
      exact Dpair_convolution q Φ (rho n) ψ hrp.1 hrp.2.1 hrp.2.2.2.2.1 hψ hψc hq hΦ
    have hB : Dpair (moll n q) (mollV n Φ) ψ
        = ∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x) :=
      Dpair_eq_integral_sub_gradient_of_smooth (moll n q) (mollV n Φ)
        (MollSB.contDiff_moll n q hq) (MollSB.contDiff_mollV n Φ hΦ 0).continuous ψ hψ hψc
    have hC : (∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x))
        = ∫ x, inner ℝ (c n) (ψ x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x) = inner ℝ (c n) (ψ x)
      rw [hc n x]
    have hD : (∫ x, inner ℝ (c n) (ψ x)) = inner ℝ (c n) (∫ x, ψ x) :=
      Auxiliary.integral_inner_eq_inner_integral (c n) ψ (hψ 0).continuous hψc
    rw [hA, hB, hC, hD]
  -- ## Step 3: the pairing annihilates mean-zero test fields
  have hmean : ∀ ψ : R3 → R3, (∀ m : ℕ, ContDiff ℝ m ψ) → HasCompactSupport ψ →
      (∫ x, ψ x) = 0 → Dpair q Φ ψ = 0 := by
    intro ψ hψ hψc h0
    have hlim := moll_tendsto q Φ hq hΦ ψ hψ hψc
    have hconst : (fun n : ℕ => Dpair q Φ (mollV n ψ)) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [hstep2 n ψ hψ hψc, h0, inner_zero_right]
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- ## Step 4: the value of the constant, and the general test field
  have hθsm : ∀ m : ℕ, ContDiff ℝ m (rho 0) := (rho_props 0).1
  have hθc : HasCompactSupport (rho 0) := (rho_props 0).2.1
  have hθint : ∫ x : R3, rho 0 x = 1 := (rho_props 0).2.2.1
  have hθcont : Continuous (rho 0) := (hθsm 0).continuous
  have hgradθcont : Continuous (fun x => gradient (rho 0) x) :=
    (Green.contDiff_gradient (rho 0) (hθsm 2)).continuous
  have hgradθc : HasCompactSupport (fun x => gradient (rho 0) x) :=
    HasCompactSupport.intro hθc (fun x hx => Green.gradient_eq_zero_of_notMem_tsupport hx)
  refine ⟨(∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x, fun ψ hψ hψc => ?_⟩
  set g : R3 := ∫ y : R3, ψ y with hg
  -- the divergence of `x ↦ rho 0 x • g`
  have hΘdiv : ∀ x : R3,
      FiniteTimeSingularity.div (fun y : R3 => rho 0 y • g) x = (fderiv ℝ (rho 0) x) g := by
    intro x
    have h0 : FiniteTimeSingularity.div (fun _ : R3 => g) x = 0 := by
      rw [FiniteTimeSingularity.div, fderiv_const_apply]
      simp
    rw [Green.div_smul_eq (rho 0) (fun _ : R3 => g) x
      ((hθsm 1).differentiable (by norm_num) x)
      (differentiableAt_const g), h0, mul_zero, zero_add]
  -- the mean-zero field `ψ - ρg`
  have hzero_int : (∫ x : R3, (ψ x - rho 0 x • g)) = 0 := by
    have h1 : Integrable ψ := (hψ 0).continuous.integrable_of_hasCompactSupport hψc
    have h2 : Integrable (fun x : R3 => rho 0 x • g) := (MollSB.integrable_rho 0).smul_const g
    rw [integral_sub h1 h2, integral_smul_const, hθint, one_smul, hg, sub_self]
  have hmz : Dpair q Φ (fun x : R3 => ψ x - rho 0 x • g) = 0 :=
    hmean _ (fun m => (hψ m).sub ((hθsm m).smul_const g)) (hψc.sub hθc.smul_right) hzero_int
  have hsplit : Dpair q Φ (fun x : R3 => ψ x - rho 0 x • g)
      = Dpair q Φ ψ - Dpair q Φ (fun x : R3 => rho 0 x • g) :=
    Dpair_sub q Φ hq hΦ ψ (fun x : R3 => rho 0 x • g) hψ hψc
      (fun m => (hθsm m).smul_const g) hθc.smul_right
  -- the two pairings that make up `Dpair q Φ (ρ • g)`
  have hI1 : (∫ x : R3, rho 0 x * inner ℝ (Φ x) g)
      = inner ℝ (∫ x : R3, rho 0 x • Φ x) g := by
    rw [show (fun x : R3 => rho 0 x * inner ℝ (Φ x) g)
        = fun x : R3 => inner ℝ (rho 0 x • Φ x) g from
      funext (fun x => by rw [real_inner_smul_left])]
    exact integral_inner_eq_inner_integral_right g (fun x : R3 => rho 0 x • Φ x)
      (hθcont.smul hΦ) hθc.smul_right
  have hI2 : (∫ x : R3, q x * (fderiv ℝ (rho 0) x) g)
      = inner ℝ (∫ x : R3, q x • gradient (rho 0) x) g := by
    rw [show (fun x : R3 => q x * (fderiv ℝ (rho 0) x) g)
        = fun x : R3 => inner ℝ (q x • gradient (rho 0) x) g from
      funext (fun x => by rw [real_inner_smul_left, inner_gradient_left])]
    exact integral_inner_eq_inner_integral_right g (fun x : R3 => q x • gradient (rho 0) x)
      (hq.smul hgradθcont)
      (HasCompactSupport.intro hgradθc
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]))
  have hmain : Dpair q Φ (fun x : R3 => rho 0 x • g)
      = inner ℝ ((∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x) g := by
    rw [Dpair_apply]
    have hp1 : (fun x : R3 => inner ℝ (Φ x) (rho 0 x • g))
        = fun x : R3 => rho 0 x * inner ℝ (Φ x) g := by
      funext x
      rw [real_inner_smul_right]
    have hp2 : (fun x : R3 => q x * FiniteTimeSingularity.div (fun y : R3 => rho 0 y • g) x)
        = fun x : R3 => q x * (fderiv ℝ (rho 0) x) g := by
      funext x
      rw [hΘdiv x]
    rw [hp1, hp2, hI1, hI2, inner_add_left]
  have : Dpair q Φ ψ
      = inner ℝ ((∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x) g := by
    linarith [hmz, hsplit, hmain]
  rwa [hg] at this

end Work.FTS.PressureOn.MollAux
