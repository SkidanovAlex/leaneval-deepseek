import Mathlib
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
import Submission.Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving
import Submission.Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc
import Submission.Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution
import Submission.Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small
import Submission.Commons.Geometry.Ulam.volterra_unperturbed_det_ne_zero
import Submission.Commons.Geometry.Ulam.dist_image_sub_le_of_norm_fderiv_le
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_upper_piece_of_continuous
import Submission.Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint
import Submission.Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
import Submission.Commons.Geometry.Ulam.returns_to_semicircle_of_moment_eqs
import Submission.Commons.Geometry.Ulam.moment_eqs_below_of_relations
import Submission.Commons.Analysis.Calculus.envelope_smooth_of_strictAntiOn
import Submission.Commons.Geometry.Ulam.moment_solution_profile_continuous
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution_not_even
set_option synthInstance.maxHeartbeats 1000000


-- ===== FILE _finpar.lean =====

noncomputable section
open Filter Set
open scoped Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Commons.Analysis.Calculus

/-!
# Finite-order parametric iterated derivatives

Finite-order version of `Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv`
(which requires `(⊤ : ℕ∞)` = smoothness on the whole space).  Each `iteratedDeriv` in the
`v`-variable costs exactly one order:

`ContDiffOn ℝ (k + m) (fun p => F p.1 p.2) U → ContDiffOn ℝ m (fun p => iteratedDeriv k
(fun v => F p.1 v) p.2) U`.
-/

/-- The `v`-derivative of a parameter-dependent function loses one order of smoothness. -/
lemma contDiffOn_deriv_snd_fin {K : ℕ} {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ (K + 1) (fun p : ℝ × ℝ => G p.1 p.2) U) :
    ContDiffOn ℝ K (fun p : ℝ × ℝ => deriv (fun v : ℝ => G p.1 v) p.2) U := by
  let H : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => G p.1 p.2
  have hH : ContDiffOn ℝ (K + 1) H U := hG
  have hmn : ((K : ℕ) : ℕ∞ω) + 1 ≤ ((K + 1 : ℕ) : ℕ∞ω) := by
    exact_mod_cast Nat.le_refl (K + 1)
  have hfderiv : ContDiffOn ℝ K (fderiv ℝ H) U := hH.fderiv_of_isOpen hU hmn
  have hconst : ContDiffOn ℝ K (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) U := contDiffOn_const
  have hmain : ContDiffOn ℝ K (fun p : ℝ × ℝ => (fderiv ℝ H p) ((0, 1) : ℝ × ℝ)) U :=
    hfderiv.clm_apply hconst
  refine hmain.congr ?_
  intro p hp
  have hdiff : DifferentiableAt ℝ H p :=
    ((hH.of_le (by exact_mod_cast (by omega : 1 ≤ K + 1))).differentiableOn
      (by norm_num : ((1 : ℕ) : ℕ∞ω) ≠ 0)).differentiableAt (hU.mem_nhds hp)
  have hdiffH_at : DifferentiableAt ℝ H (p.1, p.2) := by simpa using hdiff
  have hφdiff : DifferentiableAt ℝ (fun v : ℝ => (p.1, v)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hφfderiv : fderiv ℝ (fun v : ℝ => (p.1, v)) p.2 =
      ContinuousLinearMap.inr ℝ ℝ ℝ :=
    (hasFDerivAt_prodMk_right p.1 p.2).fderiv
  have hfd : fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2 =
      (fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    rw [fderiv_fun_comp p.2 hdiffH_at hφdiff, hφfderiv]
  change deriv (fun v : ℝ => H (p.1, v)) p.2 = (fderiv ℝ H p) ((0, 1) : ℝ × ℝ)
  calc deriv (fun v : ℝ => H (p.1, v)) p.2
      = (fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2) 1 := by
        rw [fderiv_apply_one_eq_deriv]
    _ = ((fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 1 := by rw [hfd]
    _ = (fderiv ℝ H p) ((0, 1) : ℝ × ℝ) := by simp

/-- **Finite-order parametric iterated derivatives.** -/
theorem contDiffOn_parametric_iteratedDeriv_fin :
    ∀ (k m : ℕ) {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}, IsOpen U →
      ContDiffOn ℝ (k + m) (fun p : ℝ × ℝ => F p.1 p.2) U →
      ContDiffOn ℝ m (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U
  | 0, m, F, U, hU, hF => by
      simpa [iteratedDeriv_zero] using hF
  | k + 1, m, F, U, hU, hF => by
      have hord : ((k : ℕ∞ω) + ((m : ℕ∞ω) + 1)) = ((k + 1 : ℕ) : ℕ∞ω) + (m : ℕ∞ω) := by
        push_cast
        ring
      have hF' : ContDiffOn ℝ ((k : ℕ∞ω) + ((m : ℕ∞ω) + 1))
          (fun p : ℝ × ℝ => F p.1 p.2) U := by
        simpa only [hord] using hF
      have hprev : ContDiffOn ℝ (m + 1)
          (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U :=
        contDiffOn_parametric_iteratedDeriv_fin k (m + 1) hU hF'
      let G : ℝ → ℝ → ℝ := fun x v => iteratedDeriv k (fun t : ℝ => F x t) v
      have hprevG : ContDiffOn ℝ (m + 1) (fun p : ℝ × ℝ => G p.1 p.2) U := by
        simpa [G] using hprev
      have hstep : ContDiffOn ℝ m
          (fun p : ℝ × ℝ =>
            deriv (fun v : ℝ => iteratedDeriv k (fun t : ℝ => F p.1 t) v) p.2) U := by
        simpa [G] using contDiffOn_deriv_snd_fin hU hprevG
      refine hstep.congr ?_
      intro p hp
      rw [iteratedDeriv_succ]

/-- Continuity of a parametrised `k`-th iterated derivative from finite smoothness of the
parameter-dependent function. -/
lemma continuous_iteratedDeriv_param_fin {k K : ℕ} {A : ℝ → ℝ → ℝ} (hKk : k ≤ K)
    (hA : ContDiff ℝ K (fun p : ℝ × ℝ => A p.1 p.2)) (s : ℝ) :
    Continuous (fun t : ℝ => iteratedDeriv k (fun u : ℝ => A t u) s) := by
  have hord : ((k : ℕ∞ω) + ((K - k : ℕ) : ℕ∞ω)) = ((K : ℕ) : ℕ∞ω) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hKk]
  have hA' : ContDiffOn ℝ ((k : ℕ∞ω) + ((K - k : ℕ) : ℕ∞ω))
      (fun p : ℝ × ℝ => A p.1 p.2) Set.univ := by
    simpa only [hord] using hA.contDiffOn
  have hparOn := contDiffOn_parametric_iteratedDeriv_fin k (K - k) isOpen_univ hA'
  have hpar : ContDiff ℝ (K - k)
      (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => A p.1 v) p.2) :=
    contDiffOn_univ.mp hparOn
  have h2 : ContDiff ℝ (K - k) (fun t : ℝ => (t, s)) := by fun_prop
  have hcomp := hpar.comp h2
  have hfun : (fun t : ℝ => iteratedDeriv k (fun u : ℝ => A t u) s) =
      (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => A p.1 v) p.2) ∘
        (fun t : ℝ => (t, s)) := by
    funext t; rfl
  rw [hfun]
  exact hcomp.continuous

end Commons.Analysis.Calculus
end

-- ===== FILE _tau_base.lean =====

/-!
# The `_small` even profile existence lemma

This file records the reduction of the requested `_small` statement to the
smooth local perturbation lemma of Ryabogin (Ann. of Math. 195 (2022)), whose
formalisation uses the Nazarov--Ryabogin--Zvavitch implicit-function/Volterra
machinery (`Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small`).

## What is proved here

* the moving-interval Leibniz formula
  `Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints`
  and the auxiliary vanishing lemma
  `Commons.Analysis.Calculus.iteratedDeriv_eq_zero_of_eq_zero_on_subinterval`
  are inlined (they are needed by the statement, which must import only
  Mathlib and `Submission.Commons.*`);

* the four-by-four Volterra data `G, Theta, Xi, Xi1, Xi2, stateOf, baseState`
  of Ryabogin's reduction (in the sub-namespace `RyaboginVolterra`), together
  with the (previously proved) boundary-term lemmas
  `boundaryTerm_{momentIntegrand,centroidIntegrand}_eq_G_row{2,3}`;

* **`integral_moving_split_subst`**: the general "split the moving interval at
  the base point and substitute `t = -x σ`, `t = y σ`" lemma;

* **`integral_iteratedDeriv_momentF_eq` / `..._momentH_eq`**: the two
  identities `∫ (∂/∂s)^{n+1}(f²-L²)^n = Ξ₁ - ∫ Θ₂` and
  `∫ (∂/∂s)^n((f²-L²)^{n-1}∂L/∂s) = Ξ₂ - ∫ Θ₃`, which are the paper's
  equations (feq)/(seq) after the change of variables;

* **`iteratedDeriv_momentF_eq_volterra_row` / `..._momentH_eq_volterra_row`**:
  the differentiated moment identities, i.e. the statement that the
  `(n+1)`-st derivative of the first moment error and the `n`-th derivative of
  the centroid moment are exactly the corresponding rows of
  `G - (∫ Θ + Ξ)`.

These are precisely the "Step 2" identities of the paper.

## What remains

The statement `honest_perturbation` below is the paper's local perturbation
theorem.  Its proof requires (a) transferring the data `G, Theta, Xi` to
`EuclideanSpace ℝ (Fin 4)` (the type expected by the abstract Volterra theorem
`Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small`), (b) verifying
the base-solution identity for `h = 0`, `x = y = profileX`, `f = semicircle`
(this follows from the two row identities above together with the definitions
of `momentRHS` and the oddness of the centroid integrand), (c) the bounds and
Lipschitz estimates, (d) applying the abstract theorem, (e) the paper's Steps
3 and 4 (return to the semicircle, and the extension of the moment equations
to small `s`), and (f) constructing `f` as the envelope of the family of
lines `s ↦ s·t + h s`.
-/

/-!
# High-order Leibniz formula for moving interval integrals

Let `I(u) = ∫ t in a u..b u, F u t`.  This file develops the recursive
formula for the `k`-th iterated derivative of `I`.

The formula has the shape

`iteratedDeriv k I s = ∫ t in a s..b s, iteratedDeriv k (fun u => F u t) s
    + boundaryTerm k F a b s`,

where `boundaryTerm` is generated recursively: at each differentiation the
new endpoint contribution is the current partial derivative of `F` evaluated
at the two moving endpoints, multiplied by the endpoint derivatives.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Commons.Analysis.Calculus

/-- The `k`-th partial derivative of `F` in its first variable. -/
def partialDerivIter (F : ℝ → ℝ → ℝ) (k : ℕ) (u t : ℝ) : ℝ :=
  iteratedDeriv k (fun v : ℝ => F v t) u

/-- The boundary part of the `k`-th derivative of a moving interval integral. -/
def boundaryTerm (F : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | (k + 1) => fun s =>
      partialDerivIter F k s (b s) * deriv b s -
        partialDerivIter F k s (a s) * deriv a s +
        deriv (boundaryTerm F a b k) s

lemma iteratedFDeriv_slice_apply {G : ℝ × ℝ → ℝ} {k : ℕ} {u t : ℝ}
    (hG : ContDiff ℝ k G) :
    (iteratedFDeriv ℝ k (fun v : ℝ => G (v, t)) u) (fun _ : Fin k => (1 : ℝ)) =
      (iteratedFDeriv ℝ k G (u, t)) (fun _ : Fin k => ((1 : ℝ), (0 : ℝ))) := by
  let ι0 : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inl ℝ ℝ ℝ
  have hshift : ContDiff ℝ k (fun z : ℝ × ℝ => G ((0, t) + z)) := by
    have hcomp : (fun z : ℝ × ℝ => G ((0, t) + z)) =
        G ∘ (fun z : ℝ × ℝ => (0, t) + z) := rfl
    rw [hcomp]
    exact hG.comp (contDiff_const.add contDiff_id)
  have hcomp_right := ContinuousLinearMap.iteratedFDeriv_comp_right ι0
    (f := fun z : ℝ × ℝ => G ((0, t) + z))
    (hf := hshift) (x := u) (i := k) (hi := le_rfl)
  have hfun : (fun v : ℝ => G (v, t)) =
      (fun z : ℝ × ℝ => G ((0, t) + z)) ∘ (fun v : ℝ => ι0 v) := by
    ext v
    simp [ι0]
  rw [hfun]
  have happly := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ) ℝ =>
      L (fun _ : Fin k => (1 : ℝ))) hcomp_right
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at happly
  rw [happly]
  rw [iteratedFDeriv_comp_add_left]
  have hpoint : (0, t) + ι0 u = (u, t) := by simp [ι0]
  rw [hpoint]
  exact congrArg (iteratedFDeriv ℝ k G (u, t)) (by ext i <;> rfl)

/-- The bridge between `partialDerivIter` and iterated Fréchet derivatives of the
uncurried function. -/
lemma partialDerivIter_eq_iteratedFDeriv_apply
    {F : ℝ → ℝ → ℝ} {k : ℕ} (p : ℝ × ℝ)
    (hF : ContDiff ℝ k (fun q : ℝ × ℝ => F q.1 q.2)) :
    partialDerivIter F k p.1 p.2 =
      (iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) p)
        (fun _ : Fin k => ((1 : ℝ), (0 : ℝ))) := by
  unfold partialDerivIter
  rw [iteratedDeriv_eq_iteratedFDeriv]
  let G : ℝ × ℝ → ℝ := fun q => F q.1 q.2
  have hG : ContDiff ℝ k G := by simpa [G] using hF
  have hslice := iteratedFDeriv_slice_apply (G := G) (k := k) (u := p.1) (t := p.2) hG
  simpa [G] using hslice

/-- The derivative data for `partialDerivIter F k` as a `C¹` function of the
pair `(u,t)`.  This is the main regularity input for the induction step. -/
lemma contDiff_partialDerivIter {F : ℝ → ℝ → ℝ} {n k : ℕ}
    (hF : ContDiff ℝ (n + k) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ (n + k) G := by simpa [G] using hF
  have hiter : ContDiff ℝ n (iteratedFDeriv ℝ k G) := by
    simpa [G] using hG.iteratedFDeriv_right' (m := n) (i := k)
  have hfun : (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) =
      fun p : ℝ × ℝ => (iteratedFDeriv ℝ k G p) (fun _ : Fin k => ((1 : ℝ), (0 : ℝ))) := by
    ext p
    have hGk : ContDiff ℝ k G := by
      have hle : ((k : ℕ∞ω) ≤ (n + k : ℕ∞ω)) := by
        simpa [Nat.cast_add] using
          (WithTop.coe_le_coe.mpr (show ((k : ℕ∞) ≤ (n + k : ℕ∞)) by omega))
      exact hG.of_le hle
    have hb := partialDerivIter_eq_iteratedFDeriv_apply (F := F) (k := k) p (by simpa [G] using hGk)
    simpa [G] using hb
  rw [hfun]
  let E : Fin k → Type := fun _ => ℝ × ℝ
  let v : (i : Fin k) → E i := fun _ => ((1 : ℝ), (0 : ℝ))
  let applyCLM : ContinuousMultilinearMap ℝ E ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ E ℝ v
  have hcomp : ContDiff ℝ n (fun p : ℝ × ℝ => applyCLM (iteratedFDeriv ℝ k G p)) :=
    (applyCLM.contDiff (n := n)).comp hiter
  simpa [applyCLM, E, v] using hcomp

lemma contDiff_partialDerivIter_one {F : ℝ → ℝ → ℝ} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ (k + 1) G := by simpa [G] using hF
  have hG' : ContDiff ℝ (1 + k) G := by
    simpa [add_comm] using hG
  have hiter : ContDiff ℝ 1 (iteratedFDeriv ℝ k G) := by
    simpa [G] using hG'.iteratedFDeriv_right' (m := 1) (i := k)
  have hfun : (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) =
      fun p : ℝ × ℝ => (iteratedFDeriv ℝ k G p) (fun _ : Fin k => ((1 : ℝ), (0 : ℝ))) := by
    ext p
    have hGk : ContDiff ℝ k G := by
      have hle : ((k : ℕ∞ω) ≤ (k + 1 : ℕ∞ω)) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (WithTop.coe_le_coe.mpr (show ((k : ℕ∞) ≤ (k + 1 : ℕ∞)) by exact_mod_cast (Nat.le_succ k)))
      exact hG.of_le hle
    have hb := partialDerivIter_eq_iteratedFDeriv_apply (F := F) (k := k) p (by simpa [G] using hGk)
    simpa [G] using hb
  rw [hfun]
  let E : Fin k → Type := fun _ => ℝ × ℝ
  let v : (i : Fin k) → E i := fun _ => ((1 : ℝ), (0 : ℝ))
  let applyCLM : ContinuousMultilinearMap ℝ E ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ E ℝ v
  have hcomp : ContDiff ℝ 1 (fun p : ℝ × ℝ => applyCLM (iteratedFDeriv ℝ k G p)) :=
    applyCLM.contDiff.comp hiter
  simpa [applyCLM, E, v] using hcomp

lemma continuous_partialDerivIter_succ {F : ℝ → ℝ → ℝ} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => partialDerivIter F (k + 1) p.1 p.2) := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ (k + 1) G := by simpa [G] using hF
  have hG' : ContDiff ℝ (0 + (k + 1)) G := by
    simpa [add_comm, add_left_comm, add_assoc] using hG
  have hiter : Continuous (iteratedFDeriv ℝ (k + 1) G) := by
    have h := hG'.iteratedFDeriv_right' (m := 0) (i := k + 1)
    exact h.continuous
  have hfun : (fun p : ℝ × ℝ => partialDerivIter F (k + 1) p.1 p.2) =
      fun p : ℝ × ℝ => (iteratedFDeriv ℝ (k + 1) G p) (fun _ : Fin (k + 1) => ((1 : ℝ), (0 : ℝ))) := by
    ext p
    have hb := partialDerivIter_eq_iteratedFDeriv_apply (F := F) (k := k + 1) p (by simpa [G] using hG)
    simpa [G] using hb
  rw [hfun]
  let E : Fin (k + 1) → Type := fun _ => ℝ × ℝ
  let v : (i : Fin (k + 1)) → E i := fun _ => ((1 : ℝ), (0 : ℝ))
  let applyCLM : ContinuousMultilinearMap ℝ E ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ E ℝ v
  have hcomp : Continuous (fun p : ℝ × ℝ => applyCLM (iteratedFDeriv ℝ (k + 1) G p)) :=
    applyCLM.continuous.comp hiter
  simpa [applyCLM, E, v] using hcomp

lemma partialDerivIter_one_eq_fderiv {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) (p : ℝ × ℝ) :
    partialDerivIter F 1 p.1 p.2 =
      fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) p (1, 0) := by
  unfold partialDerivIter
  rw [iteratedDeriv_one]
  let G : ℝ × ℝ → ℝ := fun q => F q.1 q.2
  have hGfun : (fun v : ℝ => F v p.2) = G ∘ (fun v : ℝ => (v, p.2)) := by
    ext v; rfl
  have hγ : HasDerivAt (fun v : ℝ => (v, p.2)) (1, 0) p.1 := by
    exact (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hGdiff : DifferentiableAt ℝ G (p.1, p.2) := by
    have hG : ContDiff ℝ 1 G := by simpa [G] using hF
    exact (hG.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hcomp := hGdiff.hasFDerivAt.comp_hasDerivAt p.1 hγ
  simpa [hGfun] using hcomp.deriv

lemma continuous_partialDerivIter_one {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => partialDerivIter F 1 p.1 p.2) := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ 1 G := by simpa [G] using hF
  have hfderiv_cont : Continuous (fderiv ℝ G) :=
    hG.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hfun : (fun p : ℝ × ℝ => partialDerivIter F 1 p.1 p.2) =
      fun p : ℝ × ℝ => fderiv ℝ G p (1, 0) := by
    ext p
    exact partialDerivIter_one_eq_fderiv hF p
  rw [hfun]
  exact hfderiv_cont.clm_apply continuous_const

/-- Base case of the combined pair-smoothness induction for `partialDerivIter`. -/
lemma partialDerivIter_smooth_data_zero {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => partialDerivIter F 0 p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => partialDerivIter F 1 p.1 p.2) := by
  constructor
  · simpa [partialDerivIter, iteratedDeriv_zero] using hF
  · exact continuous_partialDerivIter_one hF

lemma hasDerivAt_iteratedDeriv_succ {f : ℝ → ℝ} {k : ℕ} {u : ℝ}
    (hf : ContDiff ℝ (k + 1) f) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f u) u := by
  have hdiff : Differentiable ℝ (iteratedDeriv k f) := by
    exact hf.differentiable_iteratedDeriv' k
  have hder := (hdiff.differentiableAt (x := u)).hasDerivAt
  have hsucc : deriv (iteratedDeriv k f) u = iteratedDeriv (k + 1) f u := by
    rw [iteratedDeriv_succ]
  simpa [hsucc] using hder

lemma hasDerivAt_partialDerivIter_succ {F : ℝ → ℝ → ℝ} {k : ℕ} {u t : ℝ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    HasDerivAt (fun v : ℝ => partialDerivIter F k v t)
      (partialDerivIter F (k + 1) u t) u := by
  have hslice : ContDiff ℝ (k + 1) (fun v : ℝ => F v t) := by
    have hcomp : (fun v : ℝ => F v t) =
        (fun p : ℝ × ℝ => F p.1 p.2) ∘ (fun v : ℝ => (v, t)) := by
      ext v; rfl
    rw [hcomp]
    exact hF.comp (contDiff_id.prodMk contDiff_const)
  have h := hasDerivAt_iteratedDeriv_succ (f := fun v : ℝ => F v t) (k := k) (u := u) hslice
  simpa [partialDerivIter] using h

lemma partialDerivIter_one_data
    {F : ℝ → ℝ → ℝ} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => partialDerivIter F (k + 1) p.1 p.2) ∧
      (∀ u t : ℝ, HasDerivAt (fun v : ℝ => partialDerivIter F k v t)
        (partialDerivIter F (k + 1) u t) u) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiff_partialDerivIter_one hF
  · exact continuous_partialDerivIter_succ hF
  · intro u t
    exact hasDerivAt_partialDerivIter_succ hF

/-- Base case `k = 0` of the moving-interval Leibniz formula. -/
lemma iteratedDeriv_intervalIntegral_moving_endpoints_zero
    {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {s : ℝ} :
    iteratedDeriv 0 (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s =
      (∫ t in (a s)..(b s), iteratedDeriv 0 (fun u : ℝ => F u t) s) +
        boundaryTerm F a b 0 s := by
  simp [iteratedDeriv_zero, boundaryTerm]

/-- Case `k = 1` of the moving-interval Leibniz formula, with the derivative
data for `F` supplied explicitly.  The smoothness version follows by taking
`F' = partialDerivIter F 1`. -/
lemma iteratedDeriv_intervalIntegral_moving_endpoints_one
    {F F' : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {s : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u)
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    iteratedDeriv 1 (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s =
      (∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s) +
        boundaryTerm F a b 1 s := by
  have ha_deriv : HasDerivAt a (deriv a s) s := by
    exact (ha.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt.hasDerivAt
  have hb_deriv : HasDerivAt b (deriv b s) s := by
    exact (hb.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt.hasDerivAt
  have ha_cont : ContinuousAt a s := ha.continuous.continuousAt
  have hb_cont : ContinuousAt b s := hb.continuous.continuousAt
  have hx_deriv : HasDerivAt (fun u : ℝ => -a u) (-deriv a s) s := ha_deriv.neg
  have hx_cont : ContinuousAt (fun u : ℝ => -a u) s := ha_cont.neg
  have hder := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := F) (F' := F') (x := fun u : ℝ => -a u) (y := b)
    (x' := -deriv a s) (y' := deriv b s)
    (s := s) hF_cont hF'_cont hF'_isDeriv hx_deriv hb_deriv hx_cont hb_cont
  have hder_clean : HasDerivAt (fun u : ℝ => ∫ t in (a u)..(b u), F u t)
      (F s (b s) * deriv b s - F s (a s) * deriv a s +
        ∫ t in (a s)..(b s), F' s t) s := by
    simpa [neg_neg] using hder
  have hder' := hder_clean.deriv
  have hfun : iteratedDeriv 1 (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s =
      deriv (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s := by
    rw [iteratedDeriv_one]
  rw [hfun, hder']
  have hpt : ∀ t : ℝ, iteratedDeriv 1 (fun u : ℝ => F u t) s = F' s t := by
    intro t
    rw [iteratedDeriv_one]
    exact (hF'_isDeriv s t).deriv
  have hint_eq :
      (∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s) =
        ∫ t in (a s)..(b s), F' s t := by
    exact intervalIntegral.integral_congr (fun t _ => hpt t)
  have hb0 : boundaryTerm F a b 1 s =
      F s (b s) * deriv b s - F s (a s) * deriv a s + 0 := by
    rw [show boundaryTerm F a b 1 s =
      partialDerivIter F 0 s (b s) * deriv b s -
        partialDerivIter F 0 s (a s) * deriv a s +
        deriv (boundaryTerm F a b 0) s by rfl]
    simp [partialDerivIter, boundaryTerm]
  let endpoint : ℝ := F s (b s) * deriv b s - F s (a s) * deriv a s
  have hmain :
      endpoint + ∫ t in (a s)..(b s), F' s t =
        (∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s) +
          boundaryTerm F a b 1 s := by
    rw [hb0]
    calc
      endpoint + ∫ t in (a s)..(b s), F' s t
          = endpoint + ∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s := by
              exact congrArg (fun X : ℝ => endpoint + X) hint_eq.symm
      _ = (∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s) + endpoint := by
              ring
      _ = (∫ t in (a s)..(b s), iteratedDeriv 1 (fun u : ℝ => F u t) s) +
            (endpoint + 0) := by ring
  simpa [endpoint] using hmain

lemma boundaryTerm_succ_eq {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {k : ℕ} {s : ℝ} :
    boundaryTerm F a b (k + 1) s =
      boundaryTerm (partialDerivIter F k) a b 1 s + deriv (boundaryTerm F a b k) s := by
  simp [boundaryTerm, partialDerivIter]

lemma contDiff_boundaryTerm_one_gen {G : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {n : ℕ}
    (hG : ContDiff ℝ (n + 1) (fun p : ℝ × ℝ => G p.1 p.2))
    (ha : ContDiff ℝ (n + 1) a) (hb : ContDiff ℝ (n + 1) b) :
    ContDiff ℝ n (boundaryTerm G a b 1) := by
  have hb' : ContDiff ℝ n (deriv b) := by
    exact hb.deriv'
  have ha' : ContDiff ℝ n (deriv a) := by
    exact ha.deriv'
  have hle_n : ((n : ℕ∞ω) ≤ (n + 1 : ℕ∞ω)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (WithTop.coe_le_coe.mpr (show ((n : ℕ∞) ≤ (n + 1 : ℕ∞)) by exact_mod_cast (Nat.le_succ n)))
  have hG_b : ContDiff ℝ n (fun s : ℝ => G s (b s)) := by
    have hcurve : ContDiff ℝ n (fun s : ℝ => (s, b s)) := by
      exact contDiff_id.prodMk (hb.of_le hle_n)
    exact (hG.of_le hle_n).comp hcurve
  have hG_a : ContDiff ℝ n (fun s : ℝ => G s (a s)) := by
    have hcurve : ContDiff ℝ n (fun s : ℝ => (s, a s)) := by
      exact contDiff_id.prodMk (ha.of_le hle_n)
    exact (hG.of_le hle_n).comp hcurve
  have hmain : ContDiff ℝ n (fun s : ℝ =>
      G s (b s) * deriv b s - G s (a s) * deriv a s) := by
    exact (hG_b.mul hb').sub (hG_a.mul ha')
  simpa [boundaryTerm, partialDerivIter] using hmain

/-- The strong two-parameter regularity lemma for the recursive boundary terms. -/
lemma contDiff_boundaryTerm
    {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} (m k : ℕ)
    (hF : ContDiff ℝ (m + k + 1) (fun p : ℝ × ℝ => F p.1 p.2))
    (ha : ContDiff ℝ (m + k + 1) a) (hb : ContDiff ℝ (m + k + 1) b) :
    ContDiff ℝ (m + 1) (boundaryTerm F a b k) := by
  induction k generalizing m F a b with
  | zero =>
      simp [boundaryTerm]
      exact contDiff_const
  | succ k ih =>
      have hF' : ContDiff ℝ ((m + 1) + k + 1) (fun p : ℝ × ℝ => F p.1 p.2) := by
        convert hF using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have ha' : ContDiff ℝ ((m + 1) + k + 1) a := by
        convert ha using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hb' : ContDiff ℝ ((m + 1) + k + 1) b := by
        convert hb using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hBk : ContDiff ℝ ((m + 1) + 1) (boundaryTerm F a b k) := by
        exact ih (m := m + 1) hF' ha' hb'
      have hBk_deriv : ContDiff ℝ (m + 1) (deriv (boundaryTerm F a b k)) := by
        have h := hBk.deriv'
        convert h using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hF1 : ContDiff ℝ ((m + 2) + k) (fun p : ℝ × ℝ => F p.1 p.2) := by
        convert hF using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hG : ContDiff ℝ (m + 2) (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) := by
        have h := contDiff_partialDerivIter (n := m + 2) (k := k) hF1
        convert h using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hG' : ContDiff ℝ ((m + 1) + 1) (fun p : ℝ × ℝ => partialDerivIter F k p.1 p.2) := by
        convert hG using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have ha2 : ContDiff ℝ (m + 2) a := by
        have hleNat : m + 2 ≤ m + k + 2 := by omega
        have hle : ((m + 2 : ℕ∞ω) ≤ (m + k + 2 : ℕ∞ω)) := by
          exact_mod_cast hleNat
        exact ha.of_le hle
      have hb2 : ContDiff ℝ (m + 2) b := by
        have hleNat : m + 2 ≤ m + k + 2 := by omega
        have hle : ((m + 2 : ℕ∞ω) ≤ (m + k + 2 : ℕ∞ω)) := by
          exact_mod_cast hleNat
        exact hb.of_le hle
      have hB1 : ContDiff ℝ (m + 1) (boundaryTerm (partialDerivIter F k) a b 1) := by
        apply contDiff_boundaryTerm_one_gen (n := m + 1)
        · exact hG'
        · convert ha2 using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
        · convert hb2 using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_assoc, add_comm, add_left_comm]
      have hsum : ContDiff ℝ (m + 1) (fun s : ℝ =>
          boundaryTerm (partialDerivIter F k) a b 1 s + deriv (boundaryTerm F a b k) s) :=
        hB1.add hBk_deriv
      convert hsum using 1
      ext s
      rw [boundaryTerm_succ_eq]

/-- The missing differentiability input for the successor proof. -/
lemma contDiff_boundaryTerm_one
    {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2))
    (ha : ContDiff ℝ (k + 1) a) (hb : ContDiff ℝ (k + 1) b) :
    ContDiff ℝ 1 (boundaryTerm F a b k) := by
  have h := contDiff_boundaryTerm (m := 0) (k := k) (F := F) (a := a) (b := b)
    (by simpa using hF) (by simpa using ha) (by simpa using hb)
  simpa using h

/--
Successor proof skeleton:
1. Write `I u = ∫ t in a u..b u, F u t`.
2. Use `iteratedDeriv_succ` to reduce the `k+1` derivative of `I` to the
   derivative of `iteratedDeriv k I`.
3. Use `ih_fun` to replace `iteratedDeriv k I u` by
   `(∫ t in a u..b u, partialDerivIter F k u t) + boundaryTerm F a b k u`.
4. Differentiate this sum at `s`:
   - the derivative of the integral is given by
     `iteratedDeriv_intervalIntegral_moving_endpoints_one` applied to
     `partialDerivIter F k`;
   - the derivative of `boundaryTerm F a b k` is exactly the remaining term
     in the recursive definition of `boundaryTerm F a b (k+1)`.
-/
lemma iteratedDeriv_intervalIntegral_moving_endpoints_succ
    {k : ℕ} {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {s : ℝ}
    (hF : ContDiff ℝ (k + 1) (fun p : ℝ × ℝ => F p.1 p.2))
    (ha : ContDiff ℝ (k + 1) a) (hb : ContDiff ℝ (k + 1) b)
    (ih : ∀ u : ℝ,
      iteratedDeriv k (fun v : ℝ => ∫ t in (a v)..(b v), F v t) u =
        (∫ t in (a u)..(b u), partialDerivIter F k u t) + boundaryTerm F a b k u) :
    iteratedDeriv (k + 1) (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s =
      (∫ t in (a s)..(b s), iteratedDeriv (k + 1) (fun u : ℝ => F u t) s) +
        boundaryTerm F a b (k + 1) s := by
  let I : ℝ → ℝ := fun u => ∫ t in (a u)..(b u), F u t
  have hI_succ : iteratedDeriv (k + 1) I s = deriv (iteratedDeriv k I) s := by
    rw [iteratedDeriv_succ]
  rw [hI_succ]
  let G : ℝ → ℝ → ℝ := partialDerivIter F k
  let G' : ℝ → ℝ → ℝ := partialDerivIter F (k + 1)
  have hdata := partialDerivIter_one_data hF
  rcases hdata with ⟨hG_one, hG'_cont, hG'_isDeriv⟩
  have hG_cont : Continuous (fun p : ℝ × ℝ => G p.1 p.2) := hG_one.continuous
  have hle1 : ((1 : ℕ∞ω) ≤ (k + 1 : ℕ∞ω)) := by
    have hleNat : 1 ≤ k + 1 := by omega
    exact_mod_cast hleNat
  have ha_deriv : HasDerivAt a (deriv a s) s := by
    exact (ha.of_le hle1).differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0) |>.differentiableAt.hasDerivAt
  have hb_deriv : HasDerivAt b (deriv b s) s := by
    exact (hb.of_le hle1).differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0) |>.differentiableAt.hasDerivAt
  have ha_cont : ContinuousAt a s := (ha.of_le hle1).continuous.continuousAt
  have hb_cont : ContinuousAt b s := (hb.of_le hle1).continuous.continuousAt
  have hx_deriv : HasDerivAt (fun u : ℝ => -a u) (-deriv a s) s := ha_deriv.neg
  have hx_cont : ContinuousAt (fun u : ℝ => -a u) s := ha_cont.neg
  have hJ_deriv_raw := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := G) (F' := G') (x := fun u : ℝ => -a u) (y := b)
    (x' := -deriv a s) (y' := deriv b s) (s := s)
    hG_cont hG'_cont hG'_isDeriv hx_deriv hb_deriv hx_cont hb_cont
  have hJ_deriv : HasDerivAt (fun u : ℝ => ∫ t in (a u)..(b u), G u t)
      (G s (b s) * deriv b s - G s (a s) * deriv a s +
        ∫ t in (a s)..(b s), G' s t) s := by
    simpa [neg_neg] using hJ_deriv_raw
  have hB : ContDiff ℝ 1 (boundaryTerm F a b k) := by
    exact contDiff_boundaryTerm_one hF ha hb
  have hB_diff : Differentiable ℝ (boundaryTerm F a b k) := by
    exact hB.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hB_deriv : HasDerivAt (boundaryTerm F a b k) (deriv (boundaryTerm F a b k) s) s := by
    exact (hB_diff.differentiableAt (x := s)).hasDerivAt
  have hsum_deriv : HasDerivAt (fun u : ℝ =>
      (∫ t in (a u)..(b u), G u t) + boundaryTerm F a b k u)
      ((G s (b s) * deriv b s - G s (a s) * deriv a s +
        ∫ t in (a s)..(b s), G' s t) + deriv (boundaryTerm F a b k) s) s := by
    exact hJ_deriv.add hB_deriv
  have hEqFun : (fun u : ℝ => iteratedDeriv k I u) =
      fun u : ℝ => (∫ t in (a u)..(b u), G u t) + boundaryTerm F a b k u := by
    ext u
    simpa [I, G] using ih u
  have hderiv_eq : deriv (iteratedDeriv k I) s =
      deriv (fun u : ℝ => (∫ t in (a u)..(b u), G u t) + boundaryTerm F a b k u) s := by
    exact congrFun (congrArg deriv hEqFun) s
  have hderiv_rhs := hsum_deriv.deriv
  have hmain : deriv (iteratedDeriv k I) s =
      (G s (b s) * deriv b s - G s (a s) * deriv a s +
        ∫ t in (a s)..(b s), G' s t) + deriv (boundaryTerm F a b k) s := by
    rw [hderiv_eq, hderiv_rhs]
  have hG'_eq : (∫ t in (a s)..(b s), G' s t) =
      ∫ t in (a s)..(b s), iteratedDeriv (k + 1) (fun u : ℝ => F u t) s := by
    apply intervalIntegral.integral_congr
    intro t ht
    simpa [G', partialDerivIter] using rfl
  rw [hmain, hG'_eq]
  rw [boundaryTerm_succ_eq]
  simp [G, partialDerivIter, boundaryTerm]
  ring

/-- The full high-order moving-boundary Leibniz formula. -/
lemma iteratedDeriv_intervalIntegral_moving_endpoints
    {k : ℕ} {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {s : ℝ}
    (hF : ContDiff ℝ k (fun p : ℝ × ℝ => F p.1 p.2))
    (ha : ContDiff ℝ k a) (hb : ContDiff ℝ k b) :
    iteratedDeriv k (fun u : ℝ => ∫ t in (a u)..(b u), F u t) s =
      (∫ t in (a s)..(b s), iteratedDeriv k (fun u : ℝ => F u t) s) +
        boundaryTerm F a b k s := by
  revert s
  induction k with
  | zero =>
      intro s
      exact iteratedDeriv_intervalIntegral_moving_endpoints_zero
  | succ k ih =>
      intro s
      have hFk : ContDiff ℝ k (fun p : ℝ × ℝ => F p.1 p.2) := by
        have hle : ((k : ℕ∞ω) ≤ (k + 1 : ℕ∞ω)) := by
          simpa [Nat.cast_add, Nat.cast_one] using
            (WithTop.coe_le_coe.mpr (show ((k : ℕ∞) ≤ (k + 1 : ℕ∞)) by exact_mod_cast (Nat.le_succ k)))
        exact hF.of_le hle
      have hak : ContDiff ℝ k a := by
        have hle : ((k : ℕ∞ω) ≤ (k + 1 : ℕ∞ω)) := by
          simpa [Nat.cast_add, Nat.cast_one] using
            (WithTop.coe_le_coe.mpr (show ((k : ℕ∞) ≤ (k + 1 : ℕ∞)) by exact_mod_cast (Nat.le_succ k)))
        exact ha.of_le hle
      have hbk : ContDiff ℝ k b := by
        have hle : ((k : ℕ∞ω) ≤ (k + 1 : ℕ∞ω)) := by
          simpa [Nat.cast_add, Nat.cast_one] using
            (WithTop.coe_le_coe.mpr (show ((k : ℕ∞) ≤ (k + 1 : ℕ∞)) by exact_mod_cast (Nat.le_succ k)))
        exact hb.of_le hle
      have ih_fun : ∀ u : ℝ,
          iteratedDeriv k (fun v : ℝ => ∫ t in (a v)..(b v), F v t) u =
            (∫ t in (a u)..(b u), partialDerivIter F k u t) + boundaryTerm F a b k u := by
        intro u
        have hku := ih hFk hak hbk (s := u)
        simpa [partialDerivIter] using hku
      exact iteratedDeriv_intervalIntegral_moving_endpoints_succ (k := k) (s := s)
        hF ha hb ih_fun

end Commons.Analysis.Calculus

end

namespace Commons.Analysis.Calculus

open Set Filter
open scoped Topology ContDiff

/-- If the `k`-th iterated derivative of a smooth function vanishes on an
interval and the function vanishes on a terminal subinterval with nonempty
interior, then it vanishes on the whole interval.  The assumption `c < b` is
needed: when `c = b`, the terminal condition is only a pointwise value and
does not determine the function. -/
lemma iteratedDeriv_zero_of_zero_nhds {k : ℕ} {f : ℝ → ℝ} {x : ℝ}
    (h : f =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ))) : iteratedDeriv k f x = 0 := by
  have hiter := Filter.EventuallyEq.iteratedDeriv_eq (𝕜 := ℝ) (n := k) (f := f)
    (g := fun _ : ℝ => (0 : ℝ)) (x := x) h
  simpa using hiter

lemma iteratedDeriv_eq_zero_of_eq_zero_on_subinterval {k : ℕ} {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hcb : c < b) (hac : a ≤ c)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Set.univ)
    (hderiv : ∀ s ∈ Set.Icc a b, iteratedDeriv k f s = 0)
    (hzero : ∀ s ∈ Set.Icc c b, f s = 0) :
    ∀ s ∈ Set.Icc a b, f s = 0 := by
  induction k with
  | zero =>
      intro s hs
      simpa [iteratedDeriv_zero] using hderiv s hs
  | succ k ih =>
      have hf_global : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hf
      let g : ℝ → ℝ := iteratedDeriv k f
      have hg_diff : ∀ x ∈ Set.Icc a b, HasDerivAt g 0 x := by
        intro x hx
        have hx_deriv : deriv g x = 0 := by
          have h := hderiv x hx
          simpa [g, iteratedDeriv_succ] using h
        have hd : HasDerivAt g (deriv g x) x := by
          have hdiff : Differentiable ℝ g := by
            exact (hf_global.differentiable_iteratedDeriv k (by
              exact_mod_cast (ENat.natCast_lt_top (n := k))))
          exact hdiff.differentiableAt.hasDerivAt
        simpa [hx_deriv] using hd
      have hconst : ∀ x ∈ Set.Icc a b, g x = g a :=
        eqOn_of_hasDerivAt_eq_zero_Icc (f := g) hab hg_diff
      have hg_a : g a = 0 := by
        let d : ℝ := (c + b) / 2
        have hcd : c < d := by dsimp [d]; linarith
        have hdb : d < b := by dsimp [d]; linarith
        have had : a ≤ d := le_trans hac (le_of_lt hcd)
        have hd_in : d ∈ Set.Icc a b := ⟨had, le_of_lt hdb⟩
        have h_eventually : f =ᶠ[𝓝 d] (fun _ : ℝ => (0 : ℝ)) := by
          have hIoo : Set.Ioo c b ∈ 𝓝 d := Ioo_mem_nhds hcd hdb
          filter_upwards [hIoo] with t ht
          exact hzero t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hd_deriv : g d = 0 := by
          have := iteratedDeriv_zero_of_zero_nhds (k := k) (f := f) (x := d) h_eventually
          simpa [g] using this
        have hconst_d := hconst d hd_in
        rw [← hconst_d]
        exact hd_deriv
      have hg_all : ∀ x ∈ Set.Icc a b, g x = 0 := by
        intro x hx
        rw [hconst x hx, hg_a]
      exact ih hg_all

end Commons.Analysis.Calculus


noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace Interval

namespace Commons.Geometry.Ulam.RyaboginVolterra

abbrev State : Type := EuclideanSpace ℝ (Fin 4)

/-- The four coordinates of a state, packaged as an element of `EuclideanSpace ℝ (Fin 4)`. -/
noncomputable def mk4 (a b c d : ℝ) : State :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![a, b, c, d]

@[simp] lemma mk4_apply (a b c d : ℝ) (i : Fin 4) : mk4 a b c d i = ![a, b, c, d] i := by
  simp [mk4]

/-- The affine line `L(s,t) = s t + h s`. -/
def line (h : ℝ → ℝ) (s t : ℝ) : ℝ := s * t + h s

/-- The derivative of `L` in the slope parameter: `t + h' s`. -/
def lineSlope (h : ℝ → ℝ) (s t : ℝ) : ℝ := t + deriv h s

/-- The first moment integrand `(f t² - L(s,t)²) ^ n`. -/
def momentIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (f t ^ 2 - line h s t ^ 2) ^ n

/-- The second moment integrand
`(f t² - L(s,t)²) ^ (n-1) * (t + h' s)`. -/
def centroidIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (f t ^ 2 - line h s t ^ 2) ^ (n - 1) * lineSlope h s t

/-- The first moment integral. -/
def momentF (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), momentIntegrand n h f s t

/-- The second moment integral. -/
def momentH (n : ℕ) (h x y f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-x s)..(y s), centroidIntegrand n h f s t

/-- The right-hand side of the first moment equation for the unit semicircle. -/
def momentRHS (n : ℕ) (s : ℝ) : ℝ :=
  ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
    ((1 - t ^ 2) - (s * t) ^ 2) ^ n

/-- The pointwise `s`-derivative of `momentIntegrand`. -/
def momentFDerivIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (n : ℝ) * (f t ^ 2 - line h s t ^ 2) ^ (n - 1) *
    (-2 * line h s t * lineSlope h s t)

/-- The second `s`-derivative of `h`, used when differentiating `lineSlope`. -/
def lineSlopeDeriv (h : ℝ → ℝ) (s : ℝ) : ℝ := iteratedDeriv 2 h s

/-- The pointwise `s`-derivative of `centroidIntegrand`. -/
def centroidDerivIntegrand (n : ℕ) (h f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * (f t ^ 2 - line h s t ^ 2) ^ (n - 1 - 1) *
    (-2 * line h s t * lineSlope h s t) * lineSlope h s t +
  (f t ^ 2 - line h s t ^ 2) ^ (n - 1) * lineSlopeDeriv h s

lemma hasDerivAt_line {h : ℝ → ℝ} {s t h' : ℝ} (hh : HasDerivAt h h' s) :
    HasDerivAt (fun u : ℝ => line h u t) (t + h') s := by
  unfold line
  have h1 : HasDerivAt (fun u : ℝ => u * t) t s := by
    simpa using (hasDerivAt_id s).mul_const t
  exact h1.add hh

lemma hasDerivAt_lineSlope {h : ℝ → ℝ} {s t h'' : ℝ}
    (hh : HasDerivAt (deriv h) h'' s) :
    HasDerivAt (fun u : ℝ => lineSlope h u t) h'' s := by
  unfold lineSlope
  simpa using hh.const_add t

lemma hasDerivAt_momentIntegrand {h f : ℝ → ℝ} {s t h' : ℝ} (n : ℕ)
    (hh : HasDerivAt h h' s) :
    HasDerivAt (fun u : ℝ => momentIntegrand n h f u t)
      ((n : ℝ) * (f t ^ 2 - line h s t ^ 2) ^ (n - 1) *
        (-2 * line h s t * (t + h'))) s := by
  have hL := hasDerivAt_line (h := h) (s := s) (t := t) (h' := h') hh
  have hsq := hL.pow 2
  have hconst : HasDerivAt (fun _ : ℝ => f t ^ 2) 0 s := hasDerivAt_const s (f t ^ 2)
  have hsub := hconst.sub hsq
  have hderiv : 0 - 2 * line h s t ^ (2 - 1) * (t + h') =
      -2 * line h s t * (t + h') := by
    have hpow : line h s t ^ (2 - 1) = line h s t := by norm_num
    rw [hpow]
    ring
  have hsub2 := hsub.congr_deriv hderiv
  have hpow2 := hsub2.pow n
  have hfun : (fun u : ℝ => (f t ^ 2 - line h u t ^ 2) ^ n) =
      (fun u : ℝ => momentIntegrand n h f u t) := by
    ext u; rfl
  have hpow3 := hpow2.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
    intro u
    exact (congr_fun hfun u).symm))
  exact hpow3

lemma hasDerivAt_centroidIntegrand {h f : ℝ → ℝ} {s t h' h'' : ℝ} (n : ℕ)
    (hh : HasDerivAt h h' s) (hh2 : HasDerivAt (deriv h) h'' s) :
    HasDerivAt (fun u : ℝ => centroidIntegrand n h f u t)
      (((n - 1 : ℕ) : ℝ) * (f t ^ 2 - line h s t ^ 2) ^ (n - 1 - 1) *
        (-2 * line h s t * (t + h')) * lineSlope h s t +
        (f t ^ 2 - line h s t ^ 2) ^ (n - 1) * h'') s := by
  have hL := hasDerivAt_line (h := h) (s := s) (t := t) (h' := h') hh
  have hsq := hL.pow 2
  have hconst : HasDerivAt (fun _ : ℝ => f t ^ 2) 0 s := hasDerivAt_const s (f t ^ 2)
  have hsub := hconst.sub hsq
  have hderiv : 0 - 2 * line h s t ^ (2 - 1) * (t + h') =
      -2 * line h s t * (t + h') := by
    have hpow : line h s t ^ (2 - 1) = line h s t := by norm_num
    rw [hpow]
    ring
  have hsub2 := hsub.congr_deriv hderiv
  have hA := hsub2.pow (n - 1)
  have hB := hasDerivAt_lineSlope (h := h) (s := s) (t := t) (h'' := h'') hh2
  have hmul := hA.mul hB
  have hfun : (fun u : ℝ => (f t ^ 2 - line h u t ^ 2) ^ (n - 1) * lineSlope h u t) =
      (fun u : ℝ => centroidIntegrand n h f u t) := by
    ext u; rfl
  have hmul2 := hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
    intro u
    exact (congr_fun hfun u).symm))
  have hsub_eval : ((fun x : ℝ => f t ^ 2) - (fun u : ℝ => line h u t) ^ 2) s =
      f t ^ 2 - line h s t ^ 2 := by simp
  have hderiv_expr :
      (↑(n - 1) * ((fun x : ℝ => f t ^ 2) - (fun u : ℝ => line h u t) ^ 2) s ^ (n - 1 - 1) *
        (-2 * line h s t * (t + h')) * lineSlope h s t +
        (((fun x : ℝ => f t ^ 2) - (fun u : ℝ => line h u t) ^ 2) ^ (n - 1)) s * h'')
      = (((n - 1 : ℕ) : ℝ) * (f t ^ 2 - line h s t ^ 2) ^ (n - 1 - 1) *
        (-2 * line h s t * (t + h')) * lineSlope h s t +
        (f t ^ 2 - line h s t ^ 2) ^ (n - 1) * h'') := by
    simp [hsub_eval]
  exact hmul2.congr_deriv hderiv_expr

lemma hasDerivAt_momentF
    {n : ℕ} {h x y f : ℝ → ℝ} {x' y' : ℝ} {s : ℝ}
    (hh : ∀ u : ℝ, HasDerivAt h (deriv h u) u)
    (hF_cont : Continuous (fun p : ℝ × ℝ => momentIntegrand n h f p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => momentFDerivIntegrand n h f p.1 p.2))
    (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s)
    (hx_cont : ContinuousAt x s) (hy_cont : ContinuousAt y s) :
    HasDerivAt (fun u : ℝ => momentF n h x y f u)
      (momentIntegrand n h f s (y s) * y' -
        momentIntegrand n h f s (-x s) * (-x') +
        ∫ t in (-x s)..(y s), momentFDerivIntegrand n h f s t) s := by
  unfold momentF
  refine Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := momentIntegrand n h f) (F' := momentFDerivIntegrand n h f)
    (x := x) (y := y) (x' := x') (y' := y') (s := s)
    hF_cont hF'_cont ?_ hx hy hx_cont hy_cont
  intro u t
  simpa [momentFDerivIntegrand, lineSlope] using
    hasDerivAt_momentIntegrand n (s := u) (t := t) (h' := deriv h u) (hh u)

lemma hasDerivAt_momentH
    {n : ℕ} {h x y f : ℝ → ℝ} {x' y' : ℝ} {s : ℝ}
    (hh : ∀ u : ℝ, HasDerivAt h (deriv h u) u)
    (hh2 : ∀ u : ℝ, HasDerivAt (deriv h) (lineSlopeDeriv h u) u)
    (hH_cont : Continuous (fun p : ℝ × ℝ => centroidIntegrand n h f p.1 p.2))
    (hH'_cont : Continuous (fun p : ℝ × ℝ => centroidDerivIntegrand n h f p.1 p.2))
    (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s)
    (hx_cont : ContinuousAt x s) (hy_cont : ContinuousAt y s) :
    HasDerivAt (fun u : ℝ => momentH n h x y f u)
      (centroidIntegrand n h f s (y s) * y' -
        centroidIntegrand n h f s (-x s) * (-x') +
        ∫ t in (-x s)..(y s), centroidDerivIntegrand n h f s t) s := by
  unfold momentH
  refine Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := centroidIntegrand n h f) (F' := centroidDerivIntegrand n h f)
    (x := x) (y := y) (x' := x') (y' := y') (s := s)
    hH_cont hH'_cont ?_ hx hy hx_cont hy_cont
  intro u t
  simpa [centroidDerivIntegrand, lineSlope, lineSlopeDeriv] using
    hasDerivAt_centroidIntegrand n (s := u) (t := t) (h' := deriv h u)
      (h'' := lineSlopeDeriv h u) (hh u) (hh2 u)

/-- The unperturbed base state `(x₀, y₀, x₀', y₀')`. -/
def baseState (s : ℝ) : State :=
  mk4 (profileX s) (profileX s) (deriv profileX s) (deriv profileX s)

/-- The endpoint coefficient in the third row of `G`. -/
def endpointC (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (-2 : ℝ) ^ n * (n.factorial : ℝ) * (line h s t * lineSlope h s t) ^ n

/-- The endpoint coefficient in the fourth row of `G`. -/
def endpointD (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) *
    (line h s t * lineSlope h s t) ^ (n - 1) * lineSlope h s t

/-- The left-hand side `G` of the four-by-four Volterra system. -/
def G (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (Z : State) : State :=
  mk4 (Z 0) (Z 1)
    (endpointC n h s (-Z 0) * Z 2 + endpointC n h s (Z 1) * Z 3)
    (endpointD n h s (-Z 0) * Z 2 + endpointD n h s (Z 1) * Z 3)

/-- The integral kernel `Θ` of the four-by-four Volterra system. -/
def Theta (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (Z : State) : State :=
  let x : ℝ := Z 0
  let y : ℝ := Z 1
  let x' : ℝ := Z 2
  let y' : ℝ := Z 3
  mk4 (-x') (-y')
    ((iteratedDeriv (n + 1)
        (fun u : ℝ => (line h σ (-x) ^ 2 - line h u (-x) ^ 2) ^ n) s) * x'
      + (iteratedDeriv (n + 1)
        (fun u : ℝ => (line h σ y ^ 2 - line h u y ^ 2) ^ n) s) * y')
    ((iteratedDeriv n
        (fun u : ℝ => (line h σ (-x) ^ 2 - line h u (-x) ^ 2) ^ (n - 1) *
          lineSlope h u (-x)) s) * x'
      + (iteratedDeriv n
        (fun u : ℝ => (line h σ y ^ 2 - line h u y ^ 2) ^ (n - 1) *
          lineSlope h u y) s) * y')

/-- The first auxiliary integral in `Ξ`. -/
def Xi1 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-profileX 1)..(profileX 1),
    iteratedDeriv (n + 1)
      (fun u : ℝ => (1 - t ^ 2 - (line h u t) ^ 2) ^ n) s

/-- The second auxiliary integral in `Ξ`. -/
def Xi2 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-profileX 1)..(profileX 1),
    iteratedDeriv n
      (fun u : ℝ => (1 - t ^ 2 - (line h u t) ^ 2) ^ (n - 1) *
        lineSlope h u t) s

/-- The inhomogeneous term `Ξ` of the four-by-four Volterra system. -/
def Xi (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : State :=
  mk4 (profileX 1) (profileX 1)
    (- Xi1 n h s + iteratedDeriv (n + 1) (momentRHS n) s)
    (- Xi2 n h s)

/-- The state built from two profile endpoint functions and their derivatives. -/
def stateOf (x y : ℝ → ℝ) (s : ℝ) : State :=
  mk4 (x s) (y s) (deriv x s) (deriv y s)

/-- The pointwise identity behind the base-solution computation:
`1 - profileX σ ^ 2 = (σ * profileX σ) ^ 2`. -/
lemma one_sub_profileX_sq (σ : ℝ) : 1 - profileX σ ^ 2 = (σ * profileX σ) ^ 2 := by
  simp only [mul_pow, profileX_sq]
  have h : (1 : ℝ) + σ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `boundaryTerm` depends only on the values of `F` on the strip `|t| ≤ 1`,
provided the endpoint functions take their values there. -/
lemma boundaryTerm_congr {F G : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {k : ℕ}
    (h : ∀ u t : ℝ, |t| ≤ 1 → F u t = G u t)
    (ha : ∀ σ : ℝ, |a σ| ≤ 1) (hb : ∀ σ : ℝ, |b σ| ≤ 1) :
    ∀ s : ℝ,
      Commons.Analysis.Calculus.boundaryTerm F a b k s =
        Commons.Analysis.Calculus.boundaryTerm G a b k s := by
  induction k with
  | zero => intro s; simp [Commons.Analysis.Calculus.boundaryTerm]
  | succ k ih =>
      intro s
      have hpb : Commons.Analysis.Calculus.partialDerivIter F k s (b s)
          = Commons.Analysis.Calculus.partialDerivIter G k s (b s) := by
        simp only [Commons.Analysis.Calculus.partialDerivIter]
        rw [show (fun u : ℝ => F u (b s)) = (fun u : ℝ => G u (b s)) from
          funext (fun u => h u (b s) (hb s))]
      have hpa : Commons.Analysis.Calculus.partialDerivIter F k s (a s)
          = Commons.Analysis.Calculus.partialDerivIter G k s (a s) := by
        simp only [Commons.Analysis.Calculus.partialDerivIter]
        rw [show (fun u : ℝ => F u (a s)) = (fun u : ℝ => G u (a s)) from
          funext (fun u => h u (a s) (ha s))]
      have hterm : Commons.Analysis.Calculus.boundaryTerm F a b k
          = Commons.Analysis.Calculus.boundaryTerm G a b k := funext ih
      simp only [Commons.Analysis.Calculus.boundaryTerm, hpb, hpa, hterm]

/-- The root hypothesis of the boundary-term lemmas, instantiated at
`f = semicircle`, `y = profileX`, `h = 0`.  It holds because both sides are
really `1 - profileX u ^ 2 = (u * profileX u) ^ 2`. -/
lemma hxy_semicircle (u : ℝ) :
    semicircle (profileX u) ^ 2 = (u * profileX u + 0) ^ 2 ∧
      semicircle (-profileX u) ^ 2 = (u * (-profileX u) + 0) ^ 2 := by
  have hmem : profileX u ∈ Set.Icc (-1 : ℝ) 1 := profileX_mem_Icc u
  have hmem' : -profileX u ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  constructor
  · rw [semicircle_sq_of_mem_Icc hmem, add_zero, one_sub_profileX_sq]
  · rw [semicircle_sq_of_mem_Icc hmem', add_zero, neg_sq, one_sub_profileX_sq]
    ring

lemma contDiff_profileX : ContDiff ℝ (⊤ : ℕ∞) profileX := by
  unfold profileX
  exact contDiff_const.div (by
      apply ContDiff.sqrt
      · fun_prop
      · intro r; positivity) (fun r => by positivity)

lemma deriv_profileX_nonpos {s : ℝ} (hs : 0 ≤ s) : deriv profileX s ≤ 0 := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    have h := ((hasDerivAt_id (x := s)).pow 2).const_add 1
    simpa using h
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s :=
    hinner.sqrt (by positivity)
  have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
  have hfun : profileX = (fun t : ℝ => Real.sqrt (1 + t ^ 2))⁻¹ := by
    funext t
    simp [profileX, one_div]
  have hd : HasDerivAt profileX
      (-((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) / (Real.sqrt (1 + s ^ 2)) ^ 2) s := by
    rw [hfun]
    exact hsqrt.inv hne
  rw [hd.deriv]
  have h1 : (0:ℝ) < (Real.sqrt (1 + s ^ 2)) ^ 2 := by positivity
  have h2 : (0:ℝ) ≤ (2 * s) / (2 * Real.sqrt (1 + s ^ 2)) := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h2) (le_of_lt h1)

lemma contDiff_momentIntegrand (n : ℕ) {h f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => momentIntegrand n h f p.1 p.2) := by
  unfold momentIntegrand line
  fun_prop

lemma contDiff_centroidIntegrand (n : ℕ) {h f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => centroidIntegrand n h f p.1 p.2) := by
  unfold centroidIntegrand line lineSlope
  fun_prop

lemma contDiff_momentF (n : ℕ) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun s : ℝ => momentF n h x y f s) := by
  unfold momentF
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving
    (F := momentIntegrand n h f) (a := fun u : ℝ => -x u) (b := y)
    (contDiff_momentIntegrand n hh hf) ?_ hy
  simpa using hx.neg

lemma contDiff_momentH (n : ℕ) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun s : ℝ => momentH n h x y f s) := by
  unfold momentH
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving
    (F := centroidIntegrand n h f) (a := fun u : ℝ => -x u) (b := y)
    (contDiff_centroidIntegrand n hh hf) ?_ hy
  simpa using hx.neg

lemma iteratedDeriv_pow_zero_of_zero {g : ℝ → ℝ} {n k : ℕ} {s : ℝ}
    (hg : ContDiff ℝ n g) (hzero : g s = 0) (hk : k < n) :
    iteratedDeriv k (fun u : ℝ => (g u) ^ n) s = 0 := by
  have hgAt : ContDiffAt ℝ n g s := hg.contDiffAt
  have hpAt : ContDiffAt ℝ n (fun x : ℝ => x ^ n) (g s) := by
    exact (contDiff_id.pow n).contDiffAt
  have hcomp := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (n := n) (i := k) (g := fun x : ℝ => x ^ n) (f := g) (x := s)
    hpAt hgAt (by exact_mod_cast hk.le)
  change iteratedDeriv k ((fun x : ℝ => x ^ n) ∘ g) s = 0
  rw [hcomp]
  apply Finset.sum_eq_zero
  intro c hc
  have hlen : c.length < n := lt_of_le_of_lt c.length_le hk
  have hpzero : iteratedDeriv c.length (fun x : ℝ => x ^ n) (g s) = 0 := by
    rw [hzero]
    rw [iteratedDeriv_fun_pow_zero]
    simp [hlen.ne]
  rw [hpzero]
  simp


lemma iteratedDeriv_pow_eq_factorial_deriv {g : ℝ → ℝ} {n : ℕ} {s : ℝ}
    (hg : ContDiff ℝ n g) (hzero : g s = 0) :
    iteratedDeriv n (fun u : ℝ => (g u)^n) s = (n.factorial : ℝ) * (deriv g s)^n := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have hg_succ : ContDiff ℝ (n+1) g := hg
      have hg_n : ContDiff ℝ n g := hg.of_le (by exact_mod_cast (Nat.le_succ n))
      have hpow_cont : ContDiff ℝ (n+1) (fun u : ℝ => (g u)^n) := by
        exact hg_succ.pow n
      have hgAt : ContDiffAt ℝ (↑(n+1)) g s := hg_succ.contDiffAt
      have hpAt : ContDiffAt ℝ (↑(n+1)) (fun u : ℝ => (g u)^n) s := hpow_cont.contDiffAt
      change iteratedDeriv (n+1) ((fun u : ℝ => (g u)^n) * g) s = ((n+1).factorial : ℝ) * (deriv g s)^(n+1)
      have hsum := iteratedDeriv_mul (n := n+1) (x := s) (f := fun u : ℝ => (g u)^n) (g := g) hpAt hgAt
      rw [hsum]
      have hzero_lt : ∀ i ∈ Finset.range (n+2), i < n → iteratedDeriv i (fun u : ℝ => (g u)^n) s = 0 := by
        intro i hi hil
        exact iteratedDeriv_pow_zero_of_zero (n := n) (k := i) (g := g) hg_n (by simpa using hzero) hil
      have hsingle : (∑ i ∈ Finset.range (n+2), ↑((n+1).choose i) * iteratedDeriv i (fun u : ℝ => (g u)^n) s * iteratedDeriv ((n+1) - i) g s) =
          ↑((n+1).choose n) * iteratedDeriv n (fun u : ℝ => (g u)^n) s * iteratedDeriv ((n+1)-n) g s := by
        refine Finset.sum_eq_single (s := Finset.range (n+2)) (a := n)
          (f := fun i : ℕ => ↑((n+1).choose i) * iteratedDeriv i (fun u : ℝ => (g u)^n) s * iteratedDeriv ((n+1) - i) g s) ?_ ?_
        · intro b hb hbn
          by_cases hb_lt : b < n
          · have hb0 := hzero_lt b hb hb_lt
            simp [hb0]
          · have hb_ge : n ≤ b := le_of_not_gt hb_lt
            have hb_le : b ≤ n+1 := by
              have := Finset.mem_range.mp hb
              exact Nat.le_of_lt_succ this
            have hb_eq : b = n ∨ b = n+1 := by omega
            rcases hb_eq with rfl | rfl
            · exact False.elim (hbn rfl)
            · simp [hzero]
        · intro hnmem
          have hnmem' : n ∈ Finset.range (n+2) := by simp
          exact False.elim (hnmem hnmem')
      rw [hsingle]
      rw [ih hg_n]
      have hsub : n+1-n = 1 := by omega
      rw [hsub]
      have hderiv1 : iteratedDeriv 1 g s = deriv g s := by
        rw [iteratedDeriv_one]
      rw [hderiv1]
      have hchoose_nat : (n+1).choose n = n+1 := by
        rw [Nat.choose_symm_of_eq_add (n := n+1) (a := n) (b := 1) (by omega)]
        exact Nat.choose_one_right (n+1)
      have hchoose : ((n+1).choose n : ℝ) = (n+1 : ℝ) := by exact_mod_cast hchoose_nat
      have hfact : ((n+1).factorial : ℝ) = (n.factorial : ℝ) * (n+1 : ℝ) := by
        rw [Nat.factorial_succ]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [hchoose]
      rw [hfact]
      ring_nf

lemma iteratedDeriv_pow_mul_eq_factorial_deriv {g b : ℝ → ℝ} {m : ℕ} {s : ℝ}
    (hg : ContDiff ℝ m g) (hb : ContDiff ℝ m b) (hzero : g s = 0) :
    iteratedDeriv m (fun u : ℝ => (g u)^m * b u) s =
      (m.factorial : ℝ) * (deriv g s)^m * b s := by
  induction m with
  | zero => simp [iteratedDeriv_zero]
  | succ m ih =>
      have hg_succ : ContDiff ℝ (m+1) g := hg
      have hb_succ : ContDiff ℝ (m+1) b := hb
      have hpow_cont : ContDiff ℝ (m+1) (fun u : ℝ => (g u)^(m+1)) := by
        exact hg_succ.pow (m+1)
      have hgAt : ContDiffAt ℝ (↑(m+1)) (fun u : ℝ => (g u)^(m+1)) s := hpow_cont.contDiffAt
      have hbAt : ContDiffAt ℝ (↑(m+1)) b s := hb_succ.contDiffAt
      change iteratedDeriv (m+1) ((fun u : ℝ => (g u)^(m+1)) * b) s =
        ((m+1).factorial : ℝ) * (deriv g s)^(m+1) * b s
      have hsum := iteratedDeriv_mul (n := m+1) (x := s) (f := fun u : ℝ => (g u)^(m+1)) (g := b) hgAt hbAt
      rw [hsum]
      have hzero_lt : ∀ i ∈ Finset.range (m+2), i < m+1 → iteratedDeriv i (fun u : ℝ => (g u)^(m+1)) s = 0 := by
        intro i hi hil
        exact iteratedDeriv_pow_zero_of_zero (n := m+1) (k := i) (g := g) hg_succ (by simpa using hzero) hil
      have hsingle : (∑ i ∈ Finset.range (m+2), ↑((m+1).choose i) * iteratedDeriv i (fun u : ℝ => (g u)^(m+1)) s * iteratedDeriv ((m+1) - i) b s) =
          ↑((m+1).choose (m+1)) * iteratedDeriv (m+1) (fun u : ℝ => (g u)^(m+1)) s * iteratedDeriv ((m+1)-(m+1)) b s := by
        refine Finset.sum_eq_single (s := Finset.range (m+2)) (a := m+1)
          (f := fun i : ℕ => ↑((m+1).choose i) * iteratedDeriv i (fun u : ℝ => (g u)^(m+1)) s * iteratedDeriv ((m+1) - i) b s) ?_ ?_
        · intro j hj hjn
          have hj_le : j ≤ m+1 := by
            have := Finset.mem_range.mp hj
            exact Nat.le_of_lt_succ this
          have hj_lt : j < m+1 := lt_of_le_of_ne hj_le hjn
          have hj0 := hzero_lt j hj hj_lt
          simp [hj0]
        · intro hnmem
          have hnmem' : (m+1) ∈ Finset.range (m+2) := by simp
          exact False.elim (hnmem hnmem')
      rw [hsingle]
      have hchoose : ((m+1).choose (m+1) : ℝ) = 1 := by exact_mod_cast (Nat.choose_self (m+1))
      rw [hchoose]
      have hsub : m+1-(m+1) = 0 := by omega
      rw [hsub]
      rw [iteratedDeriv_zero]
      have hpow := iteratedDeriv_pow_eq_factorial_deriv (n := m+1) (g := g) (s := s) hg_succ (by simpa using hzero)
      rw [hpow]
      have hfact : ((m+1).factorial : ℝ) = (m.factorial : ℝ) * (m+1 : ℝ) := by
        rw [Nat.factorial_succ]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [hfact]
      ring_nf


/--
Lower boundary terms vanish before the top order.

The successor case reduces to the fact that, for `k < n`,
`partialDerivIter (momentIntegrand n h f) k s t = 0` whenever
`f t² = line h s t²`; this is the zero-of-order-`n` vanishing of the
`k`-th derivative of `u ↦ (f t² - line h u t²)^n`.  The base case is `k=0`.
-/
lemma boundaryTerm_momentIntegrand_eq_zero_of_le
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) {h x y f : ℝ → ℝ} {s : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x Set.univ)
    (hy : ContDiffOn ℝ (⊤ : ℕ∞) y Set.univ)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    Commons.Analysis.Calculus.boundaryTerm (momentIntegrand n h f) (fun u : ℝ => -x u) y k s = 0 := by
  revert s
  induction k with
  | zero => simp [Commons.Analysis.Calculus.boundaryTerm]
  | succ k ih =>
      intro s
      have hk_lt : k < n := Nat.lt_of_succ_le hk
      have hh_glob : ContDiff ℝ (⊤ : ℕ∞) h := contDiffOn_univ.mp hh
      have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
      have hpartial_zero (t : ℝ) (ht : f t ^ 2 = (s * t + h s) ^ 2) :
          Commons.Analysis.Calculus.partialDerivIter (momentIntegrand n h f) k s t = 0 := by
        let g : ℝ → ℝ := fun u : ℝ => f t ^ 2 - line h u t ^ 2
        let gpow : ℝ → ℝ := fun u : ℝ => (g u) ^ n
        have hg_cont : ContDiff ℝ n g := by
          dsimp [g, line]
          fun_prop
        have hzero_g : g s = 0 := by
          dsimp [g, line]
          rw [ht]
          ring
        have hpow := iteratedDeriv_pow_zero_of_zero (n := n) (k := k) (s := s)
          (g := g) hg_cont hzero_g hk_lt
        have hgpow : iteratedDeriv k gpow s = 0 := by
          simpa [gpow] using hpow
        have hpart : Commons.Analysis.Calculus.partialDerivIter (momentIntegrand n h f) k s t =
            iteratedDeriv k gpow s := by
          simp [Commons.Analysis.Calculus.partialDerivIter, momentIntegrand, gpow, g, line]
        rw [hpart]
        exact hgpow
      have hB_zero : (Commons.Analysis.Calculus.boundaryTerm (momentIntegrand n h f)
          (fun u : ℝ => -x u) y k) = fun _ : ℝ => (0 : ℝ) := by
        funext u
        exact ih (Nat.le_of_lt hk_lt) (s := u)
      rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
      have hyzero := hpartial_zero (y s) (hxy s).1
      have hxzero := hpartial_zero (-x s) (hxy s).2
      simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter, iteratedDeriv_zero]
      have hyzero' : iteratedDeriv k (fun v : ℝ => momentIntegrand n h f v (y s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hyzero
      have hxzero' : iteratedDeriv k (fun v : ℝ => momentIntegrand n h f v (-x s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hxzero
      rw [hyzero', hxzero']
      rw [hB_zero]
      simp



lemma iteratedDeriv_pow_mul_zero_of_lt {g b : ℝ → ℝ} {m k : ℕ} {s : ℝ}
    (hg : ContDiff ℝ m g) (hb : ContDiff ℝ m b) (hzero : g s = 0) (hk : k < m) :
    iteratedDeriv k (fun u : ℝ => (g u)^m * b u) s = 0 := by
  have hg_k : ContDiff ℝ k g := by
    have hle : k ≤ m := Nat.le_of_lt hk
    exact hg.of_le (by exact_mod_cast hle)
  have hb_k : ContDiff ℝ k b := by
    have hle : k ≤ m := Nat.le_of_lt hk
    exact hb.of_le (by exact_mod_cast hle)
  have hgAt : ContDiffAt ℝ (↑k) (fun u : ℝ => (g u)^m) s := by
    have hp : ContDiff ℝ k (fun u : ℝ => (g u)^m) := by
      exact hg_k.pow m
    exact hp.contDiffAt
  have hbAt : ContDiffAt ℝ (↑k) b s := hb_k.contDiffAt
  have hsum := iteratedDeriv_mul (n := k) (x := s) (f := fun u : ℝ => (g u)^m) (g := b) hgAt hbAt
  change iteratedDeriv k ((fun u : ℝ => (g u)^m) * b) s = 0
  rw [hsum]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i < k + 1 := Finset.mem_range.mp hi
  have hile : i ≤ k := Nat.le_of_lt_succ hik
  have him : i < m := lt_of_le_of_lt hile hk
  have hzero_i := iteratedDeriv_pow_zero_of_zero (n := m) (k := i) (g := g) hg hzero him
  simp [hzero_i]

lemma partialDerivIter_momentIntegrand_eq_endpointC
    {n : ℕ} (hn : 2 ≤ n) {h f : ℝ → ℝ} {s t : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (ht : f t ^ 2 = (s * t + h s) ^ 2) :
    Commons.Analysis.Calculus.partialDerivIter (momentIntegrand n h f) n s t = endpointC n h s t := by
  have hh_glob : ContDiff ℝ (⊤ : ℕ∞) h := contDiffOn_univ.mp hh
  have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
  let g : ℝ → ℝ := fun u : ℝ => line h s t ^ 2 - line h u t ^ 2
  have hg_cont : ContDiff ℝ n g := by
    dsimp [g, line]
    fun_prop
  have hg_zero : g s = 0 := by
    dsimp [g, line]
    ring
  have hder_g : deriv g s = -2 * line h s t * lineSlope h s t := by
    have hhder : HasDerivAt h (deriv h s) s := by
      exact (hh_n.differentiable (by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_two hn)))).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun u : ℝ => line h u t) (t + deriv h s) s := by
      unfold line
      have h1 : HasDerivAt (fun u : ℝ => u * t) t s := by
        simpa using (hasDerivAt_id s).mul_const t
      exact h1.add hhder
    have hsq : HasDerivAt ((fun u : ℝ => line h u t) * (fun u : ℝ => line h u t))
        (2 * line h s t * (t + deriv h s)) s := by
      have hmul := hline.mul hline
      have hder : (t + deriv h s) * line h s t + line h s t * (t + deriv h s) =
          2 * line h s t * (t + deriv h s) := by ring
      exact hmul.congr_deriv hder
    have hconst : HasDerivAt (fun _ : ℝ => line h s t ^ 2) 0 s := hasDerivAt_const s (line h s t ^ 2)
    have hsub := hconst.sub hsq
    have hder_expr : 0 - 2 * line h s t * (t + deriv h s) =
        -2 * line h s t * lineSlope h s t := by
      simp [lineSlope]
    have hsub' := hsub.congr_deriv hder_expr
    have hfun_g : g = (fun _ : ℝ => line h s t ^ 2) -
        ((fun u : ℝ => line h u t) * (fun u : ℝ => line h u t)) := by
      funext u
      simp [g, line, Pi.sub_apply, Pi.mul_apply, pow_two]
    rw [hfun_g]
    simpa using hsub'.deriv
  have hfun : (fun u : ℝ => momentIntegrand n h f u t) = fun u : ℝ => (g u) ^ n := by
    funext u
    simp [momentIntegrand, g, line, ht]
  have hmain : Commons.Analysis.Calculus.partialDerivIter (momentIntegrand n h f) n s t =
      iteratedDeriv n (fun u : ℝ => (g u) ^ n) s := by
    simp [Commons.Analysis.Calculus.partialDerivIter, hfun]
  rw [hmain]
  have hpow := iteratedDeriv_pow_eq_factorial_deriv (n := n) (g := g) (s := s) hg_cont hg_zero
  rw [hpow, hder_g]
  unfold endpointC
  ring_nf

lemma partialDerivIter_centroidIntegrand_eq_endpointD
    {n : ℕ} (hn : 2 ≤ n) {h f : ℝ → ℝ} {s t : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (ht : f t ^ 2 = (s * t + h s) ^ 2) :
    Commons.Analysis.Calculus.partialDerivIter (centroidIntegrand n h f) (n - 1) s t = endpointD n h s t := by
  have hh_glob : ContDiff ℝ (⊤ : ℕ∞) h := contDiffOn_univ.mp hh
  have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
  let m : ℕ := n - 1
  have hmn : n = m + 1 := by
    dsimp [m]
    omega
  let g : ℝ → ℝ := fun u : ℝ => line h s t ^ 2 - line h u t ^ 2
  let b : ℝ → ℝ := fun u : ℝ => lineSlope h u t
  have hh_m : ContDiff ℝ m h := by
    have hle : m ≤ n := by dsimp [m]; omega
    exact hh_n.of_le (by exact_mod_cast hle)
  have hg_cont : ContDiff ℝ m g := by
    dsimp [g, line]
    fun_prop
  have hder_cont : ContDiff ℝ m (deriv h) := by
    have hd : ContDiff ℝ (m + 1) h := by simpa [hmn] using hh_n
    exact hd.deriv'
  have hb_cont : ContDiff ℝ m b := by
    dsimp [b, lineSlope]
    simpa [add_comm] using (contDiff_const.add hder_cont)
  have hg_zero : g s = 0 := by
    dsimp [g, line]
    ring
  have hder_g : deriv g s = -2 * line h s t * lineSlope h s t := by
    have hhder : HasDerivAt h (deriv h s) s := by
      exact (hh_n.differentiable (by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_two hn)))).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun u : ℝ => line h u t) (t + deriv h s) s := by
      unfold line
      have h1 : HasDerivAt (fun u : ℝ => u * t) t s := by
        simpa using (hasDerivAt_id s).mul_const t
      exact h1.add hhder
    have hsq : HasDerivAt ((fun u : ℝ => line h u t) * (fun u : ℝ => line h u t))
        (2 * line h s t * (t + deriv h s)) s := by
      have hmul := hline.mul hline
      have hder : (t + deriv h s) * line h s t + line h s t * (t + deriv h s) =
          2 * line h s t * (t + deriv h s) := by ring
      exact hmul.congr_deriv hder
    have hconst : HasDerivAt (fun _ : ℝ => line h s t ^ 2) 0 s := hasDerivAt_const s (line h s t ^ 2)
    have hsub := hconst.sub hsq
    have hder_expr : 0 - 2 * line h s t * (t + deriv h s) =
        -2 * line h s t * lineSlope h s t := by
      simp [lineSlope]
    have hsub' := hsub.congr_deriv hder_expr
    have hfun_g : g = (fun _ : ℝ => line h s t ^ 2) -
        ((fun u : ℝ => line h u t) * (fun u : ℝ => line h u t)) := by
      funext u
      simp [g, line, Pi.sub_apply, Pi.mul_apply, pow_two]
    rw [hfun_g]
    simpa using hsub'.deriv
  have hfun : (fun u : ℝ => centroidIntegrand n h f u t) = fun u : ℝ => (g u) ^ m * b u := by
    funext u
    dsimp [centroidIntegrand, momentIntegrand, g, b]
    rw [hmn]
    simp [line, ht]
  have hmain : Commons.Analysis.Calculus.partialDerivIter (centroidIntegrand n h f) (n - 1) s t =
      iteratedDeriv m (fun u : ℝ => (g u) ^ m * b u) s := by
    simp [Commons.Analysis.Calculus.partialDerivIter, hfun, m]
  rw [hmain]
  have hpow := iteratedDeriv_pow_mul_eq_factorial_deriv (m := m) (g := g) (b := b) (s := s) hg_cont hb_cont hg_zero
  rw [hpow, hder_g]
  dsimp [b, m]
  unfold endpointD
  ring_nf


/--
The boundary term for the first moment integrand collapses to row 2 of `G`.

Proof plan: prove by induction on `k ≤ n` that
`boundaryTerm (momentIntegrand n h f) (fun u => -x u) y k s = 0`.
At the final step `k = n + 1`, the only surviving term is
`partialDerivIter (momentIntegrand n h f) n` evaluated at the two endpoints,
which by the envelope equations is exactly `endpointC`.
-/
lemma boundaryTerm_momentIntegrand_eq_G_row2
    {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {s : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x Set.univ)
    (hy : ContDiffOn ℝ (⊤ : ℕ∞) y Set.univ)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    Commons.Analysis.Calculus.boundaryTerm (momentIntegrand n h f) (fun u : ℝ => -x u) y (n + 1) s =
      (G n h s (stateOf x y s)) 2 := by
  have hBzero : (Commons.Analysis.Calculus.boundaryTerm (momentIntegrand n h f)
      (fun u : ℝ => -x u) y n) = fun _ : ℝ => (0 : ℝ) := by
    funext u
    exact boundaryTerm_momentIntegrand_eq_zero_of_le (n := n) (k := n) hn le_rfl hh hx hy hxy (s := u)
  rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
  have hyC := partialDerivIter_momentIntegrand_eq_endpointC (n := n) hn hh (hxy s).1
  have hxC := partialDerivIter_momentIntegrand_eq_endpointC (n := n) hn hh (hxy s).2
  have hyC' : iteratedDeriv n (fun v : ℝ => momentIntegrand n h f v (y s)) s = endpointC n h s (y s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hyC
  have hxC' : iteratedDeriv n (fun v : ℝ => momentIntegrand n h f v (-x s)) s = endpointC n h s (-x s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hxC
  simp [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
    iteratedDeriv_zero, hBzero, hyC', hxC']
  simp [mk4, G, stateOf, endpointC]
  ring


lemma boundaryTerm_centroidIntegrand_eq_zero_of_le
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n - 1) {h x y f : ℝ → ℝ} {s : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x Set.univ)
    (hy : ContDiffOn ℝ (⊤ : ℕ∞) y Set.univ)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f) (fun u : ℝ => -x u) y k s = 0 := by
  revert s
  induction k with
  | zero => simp [Commons.Analysis.Calculus.boundaryTerm]
  | succ k ih =>
      intro s
      have hk_lt : k < n - 1 := Nat.lt_of_succ_le hk
      have hh_glob : ContDiff ℝ (⊤ : ℕ∞) h := contDiffOn_univ.mp hh
      have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
      have hpartial_zero (t : ℝ) (ht : f t ^ 2 = (s * t + h s) ^ 2) :
          Commons.Analysis.Calculus.partialDerivIter (centroidIntegrand n h f) k s t = 0 := by
        let m : ℕ := n - 1
        let g : ℝ → ℝ := fun u : ℝ => f t ^ 2 - line h u t ^ 2
        let b : ℝ → ℝ := fun u : ℝ => lineSlope h u t
        have hmk : k < m := by dsimp [m]; exact hk_lt
        have hh_m : ContDiff ℝ m h := by
          have hle : m ≤ n := by dsimp [m]; omega
          exact hh_n.of_le (by exact_mod_cast hle)
        have hg_cont : ContDiff ℝ m g := by
          dsimp [g, line]
          fun_prop
        have hder_cont : ContDiff ℝ m (deriv h) := by
          have hmn : n = m + 1 := by dsimp [m]; omega
          have hd : ContDiff ℝ (m + 1) h := by simpa [hmn] using hh_n
          exact hd.deriv'
        have hb_cont : ContDiff ℝ m b := by
          dsimp [b, lineSlope]
          simpa [add_comm] using (contDiff_const.add hder_cont)
        have hzero_g : g s = 0 := by
          dsimp [g, line]
          rw [ht]
          ring
        have hpow := iteratedDeriv_pow_mul_zero_of_lt (m := m) (k := k) (g := g) (b := b)
          (s := s) hg_cont hb_cont hzero_g hmk
        have hfun : (fun u : ℝ => centroidIntegrand n h f u t) = fun u : ℝ => (g u) ^ m * b u := by
          funext u
          dsimp [centroidIntegrand, momentIntegrand, g, b, m]
        have hmain : Commons.Analysis.Calculus.partialDerivIter (centroidIntegrand n h f) k s t =
            iteratedDeriv k (fun u : ℝ => (g u) ^ m * b u) s := by
          simp [Commons.Analysis.Calculus.partialDerivIter, hfun]
        rw [hmain]
        exact hpow
      have hB_zero : (Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f)
          (fun u : ℝ => -x u) y k) = fun _ : ℝ => (0 : ℝ) := by
        funext u
        exact ih (Nat.le_of_lt hk_lt) (s := u)
      rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
      have hyzero := hpartial_zero (y s) (hxy s).1
      have hxzero := hpartial_zero (-x s) (hxy s).2
      simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter, iteratedDeriv_zero]
      have hyzero' : iteratedDeriv k (fun v : ℝ => centroidIntegrand n h f v (y s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hyzero
      have hxzero' : iteratedDeriv k (fun v : ℝ => centroidIntegrand n h f v (-x s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hxzero
      rw [hyzero', hxzero']
      rw [hB_zero]
      simp

/-- The boundary term for the second moment integrand collapses to row 3 of `G`. -/
lemma boundaryTerm_centroidIntegrand_eq_G_row3
    {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {s : ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x Set.univ)
    (hy : ContDiffOn ℝ (⊤ : ℕ∞) y Set.univ)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f) (fun u : ℝ => -x u) y n s =
      (G n h s (stateOf x y s)) 3 := by
  have hBzero_lower : ∀ k : ℕ, k ≤ n - 1 →
      (Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f)
        (fun u : ℝ => -x u) y k) = fun _ : ℝ => (0 : ℝ) := by
    intro k hk
    funext u
    exact boundaryTerm_centroidIntegrand_eq_zero_of_le (n := n) (k := k) hn hk hh hx hy hxy (s := u)
  have hBzero : (Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f)
      (fun u : ℝ => -x u) y (n - 1)) = fun _ : ℝ => (0 : ℝ) := by
    exact hBzero_lower (n - 1) le_rfl
  have hstep := Commons.Analysis.Calculus.boundaryTerm_succ_eq
    (F := centroidIntegrand n h f) (a := fun u : ℝ => -x u) (b := y) (k := n - 1) (s := s)
  have hstep' : Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f)
      (fun u : ℝ => -x u) y n s =
      Commons.Analysis.Calculus.boundaryTerm
        (Commons.Analysis.Calculus.partialDerivIter (centroidIntegrand n h f) (n - 1))
        (fun u : ℝ => -x u) y 1 s +
        deriv (Commons.Analysis.Calculus.boundaryTerm (centroidIntegrand n h f)
          (fun u : ℝ => -x u) y (n - 1)) s := by
    simpa [show (n - 1) + 1 = n by omega] using hstep
  rw [hstep']
  have hyD := partialDerivIter_centroidIntegrand_eq_endpointD (n := n) hn hh (hxy s).1
  have hxD := partialDerivIter_centroidIntegrand_eq_endpointD (n := n) hn hh (hxy s).2
  have hyD' : iteratedDeriv (n - 1) (fun v : ℝ => centroidIntegrand n h f v (y s)) s = endpointD n h s (y s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hyD
  have hxD' : iteratedDeriv (n - 1) (fun v : ℝ => centroidIntegrand n h f v (-x s)) s = endpointD n h s (-x s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hxD
  simp [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
    iteratedDeriv_zero, hBzero, hyD', hxD']
  simp [mk4, G, stateOf, endpointD]
  ring

/--
The integration bridge.

If the high derivatives of the two moment-error functions vanish on an
interval and the errors vanish on a terminal subinterval `[c,b]`, then they
vanish on the whole interval.  This is the paper's polynomial argument.
-/
lemma moment_eq_of_deriv_errors_zero
    (n : ℕ) (hn : 2 ≤ n) {a b c : ℝ} (hab : a ≤ b) (hcb : c < b) (hac : a ≤ c)
    {h x y f : ℝ → ℝ}
    (hF_cont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => momentF n h x y f u - momentRHS n u) Set.univ)
    (hH_cont : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => momentH n h x y f u) Set.univ)
    (hF_deriv : ∀ s ∈ Set.Icc a b,
      iteratedDeriv (n + 1)
        (fun u : ℝ => momentF n h x y f u - momentRHS n u) s = 0)
    (hH_deriv : ∀ s ∈ Set.Icc a b,
      iteratedDeriv n (fun u : ℝ => momentH n h x y f u) s = 0)
    (hbase : ∀ s ∈ Set.Icc c b,
      momentF n h x y f s = momentRHS n s ∧ momentH n h x y f s = 0) :
    ∀ s ∈ Set.Icc a b,
      momentF n h x y f s = momentRHS n s ∧ momentH n h x y f s = 0 := by
  have hF_zero : ∀ s ∈ Set.Icc a b,
      momentF n h x y f s - momentRHS n s = 0 := by
    apply Commons.Analysis.Calculus.iteratedDeriv_eq_zero_of_eq_zero_on_subinterval
      (k := n + 1) (a := a) (b := b) (c := c)
      (f := fun u : ℝ => momentF n h x y f u - momentRHS n u)
    · exact hab
    · exact hcb
    · exact hac
    · exact hF_cont
    · exact hF_deriv
    · intro s hs
      have hb := (hbase s hs).1
      linarith
  have hH_zero : ∀ s ∈ Set.Icc a b, momentH n h x y f s = 0 := by
    apply Commons.Analysis.Calculus.iteratedDeriv_eq_zero_of_eq_zero_on_subinterval
      (k := n) (a := a) (b := b) (c := c)
      (f := fun u : ℝ => momentH n h x y f u)
    · exact hab
    · exact hcb
    · exact hac
    · exact hH_cont
    · exact hH_deriv
    · intro s hs
      exact (hbase s hs).2
  intro s hs
  constructor
  · have hsub := hF_zero s hs
    linarith
  · exact hH_zero s hs

end Commons.Geometry.Ulam.RyaboginVolterra
end


namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval

set_option autoImplicit false

/-! ## The differentiated moment identities

The following general lemma performs the "split the moving interval at the
base point and substitute `t = -x σ`, `t = y σ`" step of Ryabogin's
computation.  It is the analytic heart of the reduction of the differentiated
moment equations to the four-by-four Volterra system.
-/

lemma integral_moving_split_subst
    {a b : ℝ} (hab : a ≤ b) {x y : ℝ → ℝ}
    (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    {P Q : ℝ → ℝ} (hP : Continuous P)
    (hQeq : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0)
    (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s)
    (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s), P t) =
      (∫ t in (-profileX 1)..(profileX 1), Q t) -
        ∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ) := by
  have hxd : ∀ σ : ℝ, HasDerivAt x (deriv x σ) σ := fun σ =>
    (hx.differentiable (by simp)).differentiableAt.hasDerivAt
  have hyd : ∀ σ : ℝ, HasDerivAt y (deriv y σ) σ := fun σ =>
    (hy.differentiable (by simp)).differentiableAt.hasDerivAt
  have hxcd : Continuous (deriv x) := hx.continuous_deriv (by simp)
  have hycd : Continuous (deriv y) := hy.continuous_deriv (by simp)
  have hsle : s ≤ b := hs.2
  have hPint : ∀ u v : ℝ, IntervalIntegrable P volume u v := fun u v => hP.intervalIntegrable u v
  have hsplit : (∫ t in (-x s)..(y s), P t)
      = (∫ t in (-x s)..(-x b), P t) + (∫ t in (-x b)..(y b), P t)
        + (∫ t in (y b)..(y s), P t) := by
    have hA := intervalIntegral.integral_add_adjacent_intervals (f := P)
      (a := -x s) (b := -x b) (c := y b) (hPint _ _) (hPint _ _)
    have hB := intervalIntegral.integral_add_adjacent_intervals (f := P)
      (a := -x s) (b := y b) (c := y s) (hPint _ _) (hPint _ _)
    rw [← hB, ← hA]
  have hleft : (∫ t in (-x s)..(-x b), P t) = -∫ σ in s..b, deriv x σ * P (-x σ) := by
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun σ : ℝ => -x σ) (f' := fun σ : ℝ => -deriv x σ) (g := P) (a := s) (b := b)
      (hx.continuous.neg.continuousOn)
      (fun σ hσ => (hxd σ).neg)
      (fun σ hσ => by
        have h1 : s < σ := by
          have := hσ.1; rwa [min_eq_left hsle] at this
        have h2 : σ < b := by
          have := hσ.2; rwa [max_eq_right hsle] at this
        have hmem : σ ∈ Set.Ioo a b := ⟨lt_of_le_of_lt hs.1 h1, h2⟩
        have := hxdec σ hmem
        simp only [neg_nonneg]
        linarith)
    simp only [Function.comp_apply] at hsub
    rw [← hsub]
    have hfun : (fun σ : ℝ => P (-x σ) * (-deriv x σ))
        = (fun σ : ℝ => -(P (-x σ) * deriv x σ)) := by
      funext σ; ring
    rw [hfun, intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro σ _
    ring
  have hright : (∫ t in (y b)..(y s), P t) = -∫ σ in s..b, deriv y σ * P (y σ) := by
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
      (f := y) (f' := fun σ : ℝ => deriv y σ) (g := P) (a := s) (b := b)
      hy.continuous.continuousOn
      (fun σ hσ => hyd σ)
      (fun σ hσ => by
        have h1 : s < σ := by
          have := hσ.1; rwa [min_eq_left hsle] at this
        have h2 : σ < b := by
          have := hσ.2; rwa [max_eq_right hsle] at this
        exact hydec σ ⟨lt_of_le_of_lt hs.1 h1, h2⟩)
    simp only [Function.comp_apply] at hsub
    rw [intervalIntegral.integral_symm (y s) (y b), ← hsub]
    congr 1
    apply intervalIntegral.integral_congr
    intro σ _
    ring
  have hmid : (∫ t in (-x b)..(y b), P t) = ∫ t in (-profileX 1)..(profileX 1), Q t := by
    rw [hxb, hyb]
    apply intervalIntegral.integral_congr
    intro t ht
    have hp : (0:ℝ) < profileX 1 := profileX_pos 1 (by norm_num)
    rw [Set.uIcc_of_le (by linarith : -profileX 1 ≤ profileX 1)] at ht
    exact hQeq t ht
  have hint1 : IntervalIntegrable (fun σ : ℝ => P (-x σ) * deriv x σ) volume s b :=
    ((hP.comp (hx.continuous.neg)).mul hxcd).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun σ : ℝ => P (y σ) * deriv y σ) volume s b :=
    ((hP.comp hy.continuous).mul hycd).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun σ : ℝ => P (-x σ) * deriv x σ + P (y σ) * deriv y σ)
      volume s b := hint1.add hint2
  have e1 : (∫ σ in s..b, P (-x σ) * deriv x σ) = ∫ σ in s..b, deriv x σ * P (-x σ) := by
    apply intervalIntegral.integral_congr
    intro σ _
    ring
  have e2 : (∫ σ in s..b, P (y σ) * deriv y σ) = ∫ σ in s..b, deriv y σ * P (y σ) := by
    apply intervalIntegral.integral_congr
    intro σ _
    ring
  rw [hsplit, hleft, hright, hmid]
  rw [← e1, ← e2, intervalIntegral.integral_add hint1 hint2]
  ring

section RowIdentities

open RyaboginVolterra

lemma continuous_iteratedDeriv_param (k : ℕ) {A : ℝ → ℝ → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => A p.1 p.2))
    (s : ℝ) : Continuous (fun t : ℝ => iteratedDeriv k (fun u : ℝ => A t u) s) := by
  have hpar : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => iteratedDeriv k (fun v : ℝ => A p.1 v) p.2) Set.univ :=
    Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv (k := k) isOpen_univ hA.contDiffOn
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t, s)) := by fun_prop
  exact ((contDiffOn_univ.mp hpar).comp h2).continuous

end RowIdentities

lemma integral_iteratedDeriv_momentF_eq (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧ f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv (n + 1) (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s)
      = RyaboginVolterra.Xi1 n h s
        - (∫ σ in s..b,
            (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv (n + 1) (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s
    with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv (n + 1) (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ n) s
    with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    exact continuous_iteratedDeriv_param (n + 1) (by fun_prop) s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi1 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi1, RyaboginVolterra.line]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
    apply intervalIntegral.integral_congr
    intro σ _
    have hy1 := (hxy σ).1
    have hx1 := (hxy σ).2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf, RyaboginVolterra.line, hx1, hy1]
  rw [hmain, hQeq, hSum]

lemma integral_iteratedDeriv_momentH_eq (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧ f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv n
          (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s)
      = RyaboginVolterra.Xi2 n h s
        - (∫ σ in s..b,
            (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    exact continuous_iteratedDeriv_param n (by fun_prop) s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi2 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi2, RyaboginVolterra.line, RyaboginVolterra.lineSlope]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
    apply intervalIntegral.integral_congr
    intro σ _
    have hy1 := (hxy σ).1
    have hx1 := (hxy σ).2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf, RyaboginVolterra.line,
      RyaboginVolterra.lineSlope, hx1, hy1]
  rw [hmain, hQeq, hSum]


lemma contDiff_momentRHS (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (RyaboginVolterra.momentRHS n) := by
  unfold RyaboginVolterra.momentRHS
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving
    (F := fun r t : ℝ => ((1 - t ^ 2) - (r * t) ^ 2) ^ n)
    (a := fun r : ℝ => -(1 / Real.sqrt (1 + r ^ 2)))
    (b := fun r : ℝ => 1 / Real.sqrt (1 + r ^ 2)) ?_ ?_ ?_
  · fun_prop
  · exact (contDiff_const.div (by
      apply ContDiff.sqrt
      · fun_prop
      · intro r; positivity) (fun r => by positivity)).neg
  · exact contDiff_const.div (by
      apply ContDiff.sqrt
      · fun_prop
      · intro r; positivity) (fun r => by positivity)

lemma intervalIntegral_apply_fin {F : ℝ → EuclideanSpace ℝ (Fin 4)} (hF : Continuous F)
    {a b : ℝ} (i : Fin 4) :
    (∫ x in a..b, F x) i = ∫ x in a..b, F x i := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (μ := volume)
    (EuclideanSpace.proj i) (hF.intervalIntegrable a b)
  simpa using h.symm

lemma continuous_Theta_integrand (n : ℕ) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (s : ℝ) :
    Continuous (fun σ : ℝ => RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) := by
  have hcoe : Continuous (fun σ : ℝ =>
      ((RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) : Fin 4 → ℝ)) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · show Continuous (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 0)
      have hfun : (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 0)
          = fun σ : ℝ => -deriv x σ := by
        funext σ; simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf]
      rw [hfun]
      exact (hx.continuous_deriv (by simp)).neg
    · show Continuous (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 1)
      have hfun : (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 1)
          = fun σ : ℝ => -deriv y σ := by
        funext σ; simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf]
      rw [hfun]
      exact (hy.continuous_deriv (by simp)).neg
    · show Continuous (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2)
      have hfun : (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2)
          = fun σ : ℝ =>
              (iteratedDeriv (n + 1) (fun u : ℝ => (RyaboginVolterra.line h σ (-(x σ)) ^ 2 - RyaboginVolterra.line h u (-(x σ)) ^ 2) ^ n) s) * deriv x σ
              + (iteratedDeriv (n + 1) (fun u : ℝ => (RyaboginVolterra.line h σ (y σ) ^ 2 - RyaboginVolterra.line h u (y σ) ^ 2) ^ n) s) * deriv y σ := by
        funext σ; simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf]
      rw [hfun]
      refine Continuous.add (Continuous.mul ?_ ?_) (Continuous.mul ?_ ?_)
      · refine continuous_iteratedDeriv_param (n + 1) (A := fun σ u : ℝ =>
          (RyaboginVolterra.line h σ (-(x σ)) ^ 2 - RyaboginVolterra.line h u (-(x σ)) ^ 2) ^ n) ?_ s
        unfold RyaboginVolterra.line
        fun_prop
      · exact hx.continuous_deriv (by simp)
      · refine continuous_iteratedDeriv_param (n + 1) (A := fun σ u : ℝ =>
          (RyaboginVolterra.line h σ (y σ) ^ 2 - RyaboginVolterra.line h u (y σ) ^ 2) ^ n) ?_ s
        unfold RyaboginVolterra.line
        fun_prop
      · exact hy.continuous_deriv (by simp)
    · show Continuous (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3)
      have hfun : (fun σ : ℝ => (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3)
          = fun σ : ℝ =>
              (iteratedDeriv n (fun u : ℝ => (RyaboginVolterra.line h σ (-(x σ)) ^ 2 - RyaboginVolterra.line h u (-(x σ)) ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope h u (-(x σ))) s) * deriv x σ
              + (iteratedDeriv n (fun u : ℝ => (RyaboginVolterra.line h σ (y σ) ^ 2 - RyaboginVolterra.line h u (y σ) ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope h u (y σ)) s) * deriv y σ := by
        funext σ; simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf]
      rw [hfun]
      refine Continuous.add (Continuous.mul ?_ ?_) (Continuous.mul ?_ ?_)
      · refine continuous_iteratedDeriv_param n (A := fun σ u : ℝ =>
          (RyaboginVolterra.line h σ (-(x σ)) ^ 2 - RyaboginVolterra.line h u (-(x σ)) ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope h u (-(x σ))) ?_ s
        unfold RyaboginVolterra.line RyaboginVolterra.lineSlope
        fun_prop
      · exact hx.continuous_deriv (by simp)
      · refine continuous_iteratedDeriv_param n (A := fun σ u : ℝ =>
          (RyaboginVolterra.line h σ (y σ) ^ 2 - RyaboginVolterra.line h u (y σ) ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope h u (y σ)) ?_ s
        unfold RyaboginVolterra.line RyaboginVolterra.lineSlope
        fun_prop
      · exact hy.continuous_deriv (by simp)
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp hcoe

lemma iteratedDeriv_momentF_eq_volterra_row (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (hab : a ≤ b)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧ f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    iteratedDeriv (n + 1)
        (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s =
      (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 2
        - ((∫ σ in s..b,
              RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
            + RyaboginVolterra.Xi n h s) 2 := by
  have hF : ContDiff ℝ (n + 1) (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
      unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
      fun_prop
    exact h1.of_le (by exact_mod_cast le_top)
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n + 1) (F := fun u t : ℝ => RyaboginVolterra.momentIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le (by exact_mod_cast le_top)) (hy.of_le (by exact_mod_cast le_top)) (s := s)
  have hbt := RyaboginVolterra.boundaryTerm_momentIntegrand_eq_G_row2 (n := n) hn hh.contDiffOn
    hx.contDiffOn hy.contDiffOn hxy (s := s)
  have hrow := integral_iteratedDeriv_momentF_eq n hab hh hx hy hf hxy hxdec hydec hxb hyb hfb
    hxle hyle hord hs
  have hsplit : iteratedDeriv (n + 1)
        (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s
      = iteratedDeriv (n + 1) (fun u : ℝ => RyaboginVolterra.momentF n h x y f u) s
        - iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    change iteratedDeriv (n + 1)
      (RyaboginVolterra.momentF n h x y f - RyaboginVolterra.momentRHS n) s = _
    rw [iteratedDeriv_sub]
    · exact ((RyaboginVolterra.contDiff_momentF n hh hx hy hf).of_le (by exact_mod_cast le_top)).contDiffAt
    · exact ((contDiff_momentRHS n).of_le (by exact_mod_cast le_top)).contDiffAt
  have hXi : (RyaboginVolterra.Xi n h s) 2
      = -(RyaboginVolterra.Xi1 n h s)
        + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  rw [hsplit]
  unfold RyaboginVolterra.momentF
  rw [hleib, hbt]
  unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi, intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 2]
  ring

lemma iteratedDeriv_momentH_eq_volterra_row (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (hab : a ≤ b)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hxy : ∀ u : ℝ, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧ f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n h x y f u) s =
      (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 3
        - ((∫ σ in s..b,
              RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
            + RyaboginVolterra.Xi n h s) 3 := by
  have hF : ContDiff ℝ n (fun p : ℝ × ℝ => RyaboginVolterra.centroidIntegrand n h f p.1 p.2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => RyaboginVolterra.centroidIntegrand n h f p.1 p.2) := by
      unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
      fun_prop
    exact h1.of_le (by exact_mod_cast le_top)
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n) (F := fun u t : ℝ => RyaboginVolterra.centroidIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le (by exact_mod_cast le_top)) (hy.of_le (by exact_mod_cast le_top)) (s := s)
  have hbt := RyaboginVolterra.boundaryTerm_centroidIntegrand_eq_G_row3 (n := n) hn hh.contDiffOn
    hx.contDiffOn hy.contDiffOn hxy (s := s)
  have hrow := integral_iteratedDeriv_momentH_eq n hab hh hx hy hf hxy hxdec hydec hxb hyb hfb
    hxle hyle hord hs
  have hXi : (RyaboginVolterra.Xi n h s) 3 = -(RyaboginVolterra.Xi2 n h s) := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  unfold RyaboginVolterra.momentH
  rw [hleib, hbt]
  unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi, intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 3]
  ring


/-- A globally smooth function which agrees with the semicircle `√(1-t²)` in
square on the interval `[-ρ, ρ]`, for any `0 < ρ < 1`. -/
lemma exists_smooth_semicircle_agrees {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ F : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ t ∈ Set.Icc (-ρ) ρ, F t ^ 2 = 1 - t ^ 2 := by
  let ρ' : ℝ := (1 + ρ) / 2
  have hρ'0 : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨ρ, ρ', hρ0, hρ'0⟩
  refine ⟨fun t => b t * Real.sqrt (1 - t ^ 2), ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : |t| < 1
    · have hpos : (1 : ℝ) - t ^ 2 ≠ 0 := by
        have := abs_lt.mp ht
        nlinarith [this.1, this.2]
      have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 - s ^ 2)) t :=
        (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt hpos
      exact (b.contDiff.contDiffAt).mul hs
    · have hgt : 1 ≤ |t| := le_of_not_gt ht
      have hnear : Metric.ball t (|t| - ρ') ∈ 𝓝 t := Metric.ball_mem_nhds t (by linarith)
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
      filter_upwards [hnear] with s hs
      have h1 : |s - t| < |t| - ρ' := by
        simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hs
      have h2 : ρ' < |s| := by
        have h3 : |t| - |s| ≤ |s - t| := by
          have := abs_sub_abs_le_abs_sub t s
          rwa [abs_sub_comm] at this
        linarith
      have hbs : b s = 0 := by
        rw [← Function.notMem_support, b.support_eq, Metric.mem_ball, dist_zero_right, not_lt]
        simpa [Real.norm_eq_abs] using h2.le
      simp [hbs]
  · intro t ht
    have hbt : b t = 1 := b.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa [Real.norm_eq_abs] using abs_le.mpr ht)
    have hs : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := by
      rw [Real.sq_sqrt]
      have hle : |t| ≤ ρ := abs_le.mpr ht
      nlinarith [hle, hρ1, abs_nonneg t, sq_abs t]
    show (b t * Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2
    rw [hbt, one_mul, hs]

/-- **Base case of the (feq) change of variables.**  With `h = 0` and
`x = y = profileX`, the identity `∫ (∂/∂s)^{n+1}(f²-L²)^n = Ξ₁ - ∫ Θ₂` of
`integral_iteratedDeriv_momentF_eq` specialises to the explicit integrand
`((1 - t^2) - (u t)^2)^n` (the square of the semicircle). -/
lemma integral_iteratedDeriv_momentRHS_eq (n : ℕ) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    (∫ t in (-profileX s)..(profileX s),
        iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s)
      = RyaboginVolterra.Xi1 n (fun _ => 0) s
        - (∫ σ in s..1,
            (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) 2) := by
  have hsa : a ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hab : a ≤ 1 := le_trans hsa hs1
  have hP : Continuous (fun t : ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s) :=
    continuous_iteratedDeriv_param (n + 1)
      (A := fun t u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) (by fun_prop) s
  have hprof_le : ∀ σ ∈ Set.Icc (a:ℝ) 1, profileX 1 ≤ profileX σ := by
    intro σ hσ
    have h1 : (1:ℝ) + σ ^ 2 ≤ 1 + 1 ^ 2 := by nlinarith [hσ.1, hσ.2]
    have h2 : Real.sqrt (1 + σ ^ 2) ≤ Real.sqrt (1 + 1 ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : (0:ℝ) < Real.sqrt (1 + σ ^ 2) := Real.sqrt_pos.2 (by positivity)
    unfold profileX
    exact one_div_le_one_div_of_le h3 h2
  have hprof_pos : -profileX 1 ≤ profileX 1 := by
    have := profileX_pos 1 (by norm_num); linarith
  have hsplit := integral_moving_split_subst (a := a) (b := 1) hab
    (x := profileX) (y := profileX) RyaboginVolterra.contDiff_profileX RyaboginVolterra.contDiff_profileX
    (P := fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s)
    (Q := fun t : ℝ => iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s)
    hP (fun _ _ => rfl)
    (fun σ hσ => RyaboginVolterra.deriv_profileX_nonpos (le_of_lt (lt_trans ha hσ.1)))
    (fun σ hσ => RyaboginVolterra.deriv_profileX_nonpos (le_of_lt (lt_trans ha hσ.1)))
    rfl rfl hprof_le hprof_le hprof_pos hs
  rw [hsplit]
  have hXi1 : (∫ t in (-profileX 1)..(profileX 1),
        iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s)
      = RyaboginVolterra.Xi1 n (fun _ => 0) s := by
    simp only [RyaboginVolterra.Xi1, RyaboginVolterra.line, Pi.zero_apply, mul_zero, add_zero]
  rw [hXi1]
  congr 1
  apply intervalIntegral.integral_congr
  intro σ _
  simp only [RyaboginVolterra.Theta, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply,
    RyaboginVolterra.line, RyaboginVolterra.one_sub_profileX_sq, neg_sq, Pi.zero_apply,
    mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring_nf

/-- **Row 2 of the base-solution identity**: the Leibniz formula applied to
`momentRHS`, whose boundary term is row 2 of `G` at the base state, together
with the base-case change of variables `integral_iteratedDeriv_momentRHS_eq`
and the oddness-free identification of `Ξ`'s second component. -/
lemma volterra_base_row2 (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) 2
      = ((∫ σ in s..1,
            RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
          + RyaboginVolterra.Xi n (fun _ => 0) s) 2 := by
  have hprofX : ContDiff ℝ (⊤ : ℕ∞) profileX := RyaboginVolterra.contDiff_profileX
  -- Leibniz for the explicit integrand
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n + 1) (F := fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n)
    (a := fun u : ℝ => -profileX u) (b := profileX)
    ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => ((1 - p.2 ^ 2) - (p.1 * p.2) ^ 2) ^ n)).of_le
      (by exact_mod_cast le_top))
    (hprofX.neg.of_le (by exact_mod_cast le_top))
    (hprofX.of_le (by exact_mod_cast le_top)) (s := s)
  -- identify the left-hand side with the derivative of `momentRHS`
  have hmr : iteratedDeriv (n + 1)
        (fun u : ℝ => ∫ t in (-profileX u)..(profileX u), ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s
      = iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := rfl
  have hleib' : iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s
      = (∫ t in (-profileX s)..(profileX s),
          iteratedDeriv (n + 1) (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n) s)
        + Commons.Analysis.Calculus.boundaryTerm
            (fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n)
            (fun u : ℝ => -profileX u) profileX (n + 1) s := by
    rw [← hmr]
    exact hleib
  -- the boundary term is `(G 0 s (baseState s)) 2`
  have hcongr := RyaboginVolterra.boundaryTerm_congr
    (F := fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n)
    (G := RyaboginVolterra.momentIntegrand n (fun _ => 0) semicircle)
    (a := fun u : ℝ => -profileX u) (b := profileX)
    (k := n + 1)
    (by
      intro u t ht
      have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp ht
      simp only [RyaboginVolterra.momentIntegrand, RyaboginVolterra.line, Pi.zero_apply,
        mul_zero, add_zero, semicircle_sq_of_mem_Icc hmem])
    (by intro σ; rw [abs_neg]; exact abs_le.mpr (profileX_mem_Icc σ))
    (by intro σ; exact abs_le.mpr (profileX_mem_Icc σ))
  have hrow2 := RyaboginVolterra.boundaryTerm_momentIntegrand_eq_G_row2 (n := n) hn
    (contDiff_const.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0:ℝ)) Set.univ)
    hprofX.contDiffOn hprofX.contDiffOn (RyaboginVolterra.hxy_semicircle) (s := s)
  have hbt : Commons.Analysis.Calculus.boundaryTerm
        (fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ n)
        (fun u : ℝ => -profileX u) profileX (n + 1) s
      = (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) 2 := by
    rw [hcongr, ← show RyaboginVolterra.stateOf profileX profileX s
        = RyaboginVolterra.baseState s from rfl]
    exact hrow2
  -- the base-case change of variables
  have hbase := integral_iteratedDeriv_momentRHS_eq n ha hs
  -- `Ξ`'s second component
  have hXi : (RyaboginVolterra.Xi n (fun _ => 0) s) 2
      = -(RyaboginVolterra.Xi1 n (fun _ => 0) s)
        + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  have hcont : Continuous (fun σ : ℝ =>
      RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) :=
    continuous_Theta_integrand n (by fun_prop) hprofX hprofX s
  have hint : ((∫ σ in s..1,
          RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
        + RyaboginVolterra.Xi n (fun _ => 0) s) 2
      = (∫ σ in s..1,
          (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) 2)
        + (RyaboginVolterra.Xi n (fun _ => 0) s) 2 := by
    rw [WithLp.ofLp_add, Pi.add_apply, intervalIntegral_apply_fin hcont]
  rw [hint, hXi, ← hbt]
  linarith [hleib', hbase]

/-- An odd function integrates to zero over a symmetric interval. -/
lemma integral_odd_eq_zero {g : ℝ → ℝ} {c : ℝ} (hg : ∀ t : ℝ, g (-t) = -g t) :
    (∫ t in (-c)..c, g t) = 0 := by
  have h1 : (∫ t in (-c)..c, g t) = ∫ t in (-c)..c, g (-t) := by
    rw [intervalIntegral.integral_comp_neg (f := g) (a := -c) (b := c)]
    simp
  have h2 : (∫ t in (-c)..c, g (-t)) = -(∫ t in (-c)..c, g t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    exact hg t
  linarith

/-- The centroid integrand at `h = 0`, `x = y = profileX`, `f = semicircle` is
odd in `t`, so `momentH` vanishes identically for the base solution. -/
lemma momentH_base_eq_zero (n : ℕ) (u : ℝ) :
    RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle u = 0 := by
  set F : ℝ → ℝ := fun t => (semicircle t ^ 2 - (u * t + 0) ^ 2) ^ (n - 1) *
      (t + deriv (fun _ : ℝ => 0) u) with hF
  have hmoment : RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle u
      = ∫ t in (-profileX u)..(profileX u), F t := by
    simp only [RyaboginVolterra.momentH, RyaboginVolterra.centroidIntegrand,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope, hF]
  rw [hmoment]
  exact integral_odd_eq_zero (c := profileX u) (by
    intro t
    have hd : deriv (fun _ : ℝ => (0:ℝ)) u = 0 := (hasDerivAt_const u (0:ℝ)).deriv
    simp only [hF]
    rw [semicircle_even, hd]
    ring)

/-- The centroid moment of the base solution, written with the explicit
semicircle-square integrand (the form on which Leibniz applies). -/
lemma momentH_explicit_eq (n : ℕ) :
    (fun u : ℝ => ∫ t in (-profileX u)..(profileX u),
        ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
      = RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle := by
  funext u
  simp only [RyaboginVolterra.momentH, RyaboginVolterra.centroidIntegrand,
    RyaboginVolterra.line, RyaboginVolterra.lineSlope, Pi.zero_apply, mul_zero, add_zero]
  apply intervalIntegral.integral_congr
  intro t ht
  have hle : -profileX u ≤ profileX u := by
    have hpos : 0 < profileX u := by
      unfold profileX
      positivity
    linarith
  rw [Set.uIcc_of_le hle] at ht
  have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := profileX_mem_Icc u
    exact ⟨le_trans (neg_le_neg h.2) ht.1, le_trans ht.2 h.2⟩
  have hd : deriv (fun _ : ℝ => (0:ℝ)) u = 0 := (hasDerivAt_const u (0:ℝ)).deriv
  beta_reduce
  rw [← semicircle_sq_of_mem_Icc hmem, hd]
  ring

/-- **Base case of the (seq) change of variables**: the centroid analogue of
`integral_iteratedDeriv_momentRHS_eq`. -/
lemma integral_iteratedDeriv_momentH_base_eq (n : ℕ) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    (∫ t in (-profileX s)..(profileX s),
        iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s)
      = RyaboginVolterra.Xi2 n (fun _ => 0) s
        - (∫ σ in s..1,
            (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) 3) := by
  have hsa : a ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hab : a ≤ 1 := le_trans hsa hs1
  have hP : Continuous (fun t : ℝ =>
      iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s) :=
    continuous_iteratedDeriv_param n
      (A := fun t u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) (by fun_prop) s
  have hprof_le : ∀ σ ∈ Set.Icc (a:ℝ) 1, profileX 1 ≤ profileX σ := by
    intro σ hσ
    have h1 : (1:ℝ) + σ ^ 2 ≤ 1 + 1 ^ 2 := by nlinarith [hσ.1, hσ.2]
    have h2 : Real.sqrt (1 + σ ^ 2) ≤ Real.sqrt (1 + 1 ^ 2) := Real.sqrt_le_sqrt h1
    have h3 : (0:ℝ) < Real.sqrt (1 + σ ^ 2) := Real.sqrt_pos.2 (by positivity)
    unfold profileX
    exact one_div_le_one_div_of_le h3 h2
  have hprof_pos : -profileX 1 ≤ profileX 1 := by
    have := profileX_pos 1 (by norm_num); linarith
  have hsplit := integral_moving_split_subst (a := a) (b := 1) hab
    (x := profileX) (y := profileX) RyaboginVolterra.contDiff_profileX RyaboginVolterra.contDiff_profileX
    (P := fun t : ℝ => iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s)
    (Q := fun t : ℝ => iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s)
    hP (fun _ _ => rfl)
    (fun σ hσ => RyaboginVolterra.deriv_profileX_nonpos (le_of_lt (lt_trans ha hσ.1)))
    (fun σ hσ => RyaboginVolterra.deriv_profileX_nonpos (le_of_lt (lt_trans ha hσ.1)))
    rfl rfl hprof_le hprof_le hprof_pos hs
  rw [hsplit]
  have hXi2 : (∫ t in (-profileX 1)..(profileX 1),
        iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s)
      = RyaboginVolterra.Xi2 n (fun _ => 0) s := by
    simp only [RyaboginVolterra.Xi2, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
      Pi.zero_apply, mul_zero, add_zero]
    apply intervalIntegral.integral_congr
    intro t _
    beta_reduce
    rw [show (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
        = (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) *
            (t + deriv (fun _ : ℝ => (0:ℝ)) u)) from by
      funext u
      rw [show deriv (fun _ : ℝ => (0:ℝ)) u = 0 from (hasDerivAt_const u (0:ℝ)).deriv]
      ring]
  rw [hXi2]
  congr 1
  apply intervalIntegral.integral_congr
  intro σ _
  simp only [RyaboginVolterra.Theta, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply,
    RyaboginVolterra.line, RyaboginVolterra.lineSlope, RyaboginVolterra.one_sub_profileX_sq,
    neg_sq, Pi.zero_apply, mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [show (fun u : ℝ => ((σ * profileX σ) ^ 2 - (u * -profileX σ) ^ 2) ^ (n - 1) *
          -profileX σ)
      = (fun u : ℝ => ((σ * -profileX σ) ^ 2 - (u * -profileX σ) ^ 2) ^ (n - 1) *
          (-profileX σ + deriv (fun _ : ℝ => (0:ℝ)) u)) from by
        funext u
        rw [show deriv (fun _ : ℝ => (0:ℝ)) u = 0 from (hasDerivAt_const u (0:ℝ)).deriv]
        ring]
  rw [show (fun u : ℝ => ((σ * profileX σ) ^ 2 - (u * profileX σ) ^ 2) ^ (n - 1) * profileX σ)
      = (fun u : ℝ => ((σ * profileX σ) ^ 2 - (u * profileX σ) ^ 2) ^ (n - 1) *
          (profileX σ + deriv (fun _ : ℝ => (0:ℝ)) u)) from by
        funext u
        rw [show deriv (fun _ : ℝ => (0:ℝ)) u = 0 from (hasDerivAt_const u (0:ℝ)).deriv]
        ring]

/-- **Row 3 of the base-solution identity**: the centroid analogue of
`volterra_base_row2`.  The extra input over row 2 is `momentH_base_eq_zero`,
which collapses `iteratedDeriv n (momentH …) s` to `0`. -/
lemma volterra_base_row3 (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) 3
      = ((∫ σ in s..1,
            RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
          + RyaboginVolterra.Xi n (fun _ => 0) s) 3 := by
  have hprofX : ContDiff ℝ (⊤ : ℕ∞) profileX := RyaboginVolterra.contDiff_profileX
  have hleib0 := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n) (F := fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
    (a := fun u : ℝ => -profileX u) (b := profileX)
    ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ((1 - p.2 ^ 2) - (p.1 * p.2) ^ 2) ^ (n - 1) * p.2)).of_le
      (by exact_mod_cast le_top))
    (hprofX.neg.of_le (by exact_mod_cast le_top))
    (hprofX.of_le (by exact_mod_cast le_top)) (s := s)
  have hleib : iteratedDeriv n
        (RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle) s
      = (∫ t in (-profileX s)..(profileX s),
          iteratedDeriv n (fun u : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t) s)
        + Commons.Analysis.Calculus.boundaryTerm
            (fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
            (fun u : ℝ => -profileX u) profileX n s := by
    rw [← momentH_explicit_eq]
    exact hleib0
  have hcongr := RyaboginVolterra.boundaryTerm_congr
    (F := fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
    (G := RyaboginVolterra.centroidIntegrand n (fun _ => 0) semicircle)
    (a := fun u : ℝ => -profileX u) (b := profileX) (k := n)
    (by
      intro u t ht
      have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp ht
      have hd : deriv (fun _ : ℝ => (0:ℝ)) u = 0 := (hasDerivAt_const u (0:ℝ)).deriv
      simp only [RyaboginVolterra.centroidIntegrand, RyaboginVolterra.line,
        RyaboginVolterra.lineSlope, Pi.zero_apply, mul_zero, add_zero, hd,
        semicircle_sq_of_mem_Icc hmem])
    (by intro σ; rw [abs_neg]; exact abs_le.mpr (profileX_mem_Icc σ))
    (by intro σ; exact abs_le.mpr (profileX_mem_Icc σ))
  have hrow3 := RyaboginVolterra.boundaryTerm_centroidIntegrand_eq_G_row3 (n := n) hn
    (contDiff_const.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0:ℝ)) Set.univ)
    hprofX.contDiffOn hprofX.contDiffOn (RyaboginVolterra.hxy_semicircle) (s := s)
  have hbt : Commons.Analysis.Calculus.boundaryTerm
        (fun u t : ℝ => ((1 - t ^ 2) - (u * t) ^ 2) ^ (n - 1) * t)
        (fun u : ℝ => -profileX u) profileX n s
      = (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) 3 := by
    rw [hcongr, ← show RyaboginVolterra.stateOf profileX profileX s
        = RyaboginVolterra.baseState s from rfl]
    exact hrow3
  have hbase := integral_iteratedDeriv_momentH_base_eq n ha hs
  have hzero : iteratedDeriv n
        (RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle) s = 0 := by
    have hfun : RyaboginVolterra.momentH n (fun _ => 0) profileX profileX semicircle
        = fun _ : ℝ => 0 := funext (momentH_base_eq_zero n)
    rw [hfun, iteratedDeriv_const]
    simp [show n ≠ 0 by omega]
  have hXi : (RyaboginVolterra.Xi n (fun _ => 0) s) 3
      = -(RyaboginVolterra.Xi2 n (fun _ => 0) s) := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  have hcont : Continuous (fun σ : ℝ =>
      RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) :=
    continuous_Theta_integrand n (by fun_prop) hprofX hprofX s
  have hint : ((∫ σ in s..1,
          RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
        + RyaboginVolterra.Xi n (fun _ => 0) s) 3
      = (∫ σ in s..1,
          (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) 3)
        + (RyaboginVolterra.Xi n (fun _ => 0) s) 3 := by
    rw [WithLp.ofLp_add, Pi.add_apply, intervalIntegral_apply_fin hcont]
  rw [hint, hXi, ← hbt]
  linarith [hleib, hzero, hbase]

/-- **Rows 0 and 1 of the base-solution identity.**  With `h = 0` the first two
components of `Θ` are `-deriv profileX` and those of `Ξ` are `profileX 1`, so the
identity reduces to the fundamental theorem of calculus
`∫_s^1 deriv profileX = profileX 1 - profileX s`. -/
lemma volterra_base_row01 (n : ℕ) {a : ℝ} (_ha : 0 < a) {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    ∀ i : Fin 4, (i = 0 ∨ i = 1) →
      (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) i
        = ((∫ σ in s..1,
              RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
            + RyaboginVolterra.Xi n (fun _ => 0) s) i := by
  intro i hi
  have hprofX : ContDiff ℝ (⊤ : ℕ∞) profileX := RyaboginVolterra.contDiff_profileX
  have hcont : Continuous (fun σ : ℝ =>
      RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) :=
    continuous_Theta_integrand n (by fun_prop) hprofX hprofX s
  have hG : (RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)) i
      = profileX s := by
    rcases hi with rfl | rfl <;>
      simp [RyaboginVolterra.G, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  have hθ : ∀ σ : ℝ,
      (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)) i
        = -deriv profileX σ := by
    intro σ
    rcases hi with rfl | rfl <;>
      simp [RyaboginVolterra.Theta, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  have hΞ : (RyaboginVolterra.Xi n (fun _ => 0) s) i = profileX 1 := by
    rcases hi with rfl | rfl <;>
      simp [RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply]
  have hint : ((∫ σ in s..1,
          RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
        + RyaboginVolterra.Xi n (fun _ => 0) s) i
      = (∫ σ in s..1, -deriv profileX σ) + profileX 1 := by
    rw [WithLp.ofLp_add, Pi.add_apply, intervalIntegral_apply_fin hcont, hΞ]
    congr 1
    apply intervalIntegral.integral_congr
    intro σ _
    exact hθ σ
  rw [hG, hint]
  have hftc : (∫ σ in s..1, deriv profileX σ) = profileX 1 - profileX s :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hprofX.differentiable (by simp)).differentiableAt)
      ((hprofX.continuous_deriv (by simp)).intervalIntegrable s 1)
  rw [intervalIntegral.integral_neg, hftc]
  ring

/-- **The base-solution identity.**  With `h = 0`, `x = y = profileX` and
`f = semicircle`, the state `baseState` solves the Volterra system on `[a,1]`:
`G 0 s (baseState s) = ∫_s^1 Θ0(s,σ,baseState σ) dσ + Ξ0(s)`.

Proof route (all ingredients already available above):

* Row 0 and row 1: with `h = 0` the first two components of `Θ` are
  `-deriv profileX`, and `Ξ`'s are `profileX 1`; the identity reduces to
  `∫_s^1 -deriv profileX = profileX s - profileX 1`.

* Row 2: apply the Leibniz formula
  (`Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints`)
  to `F u t = ((1 - t^2) - (u*t)^2)^n`, whose two moving endpoints are
  `-profileX u` and `profileX u` (both `ContDiff ℝ ⊤`).  Since
  `momentRHS n u` is *by definition* `∫ t in (-profileX u)..(profileX u), F u t`,
  this gives
  `iteratedDeriv (n+1) (momentRHS n) s
     = ∫ t in (-profileX s)..(profileX s), (∂/∂s)^{n+1} F s t
       + boundaryTerm F (fun u => -profileX u) profileX (n+1) s`.
  The boundary term is `(G 0 s (baseState s)) 2` by
  `boundaryTerm_momentIntegrand_eq_G_row2` applied with `f := semicircle`
  (the hypothesis `f (y u)^2 = (u * y u + h u)^2` there is the *square*
  condition, which for `f = semicircle`, `y = profileX`, `h = 0` is exactly
  `1 - profileX u^2 = (u * profileX u)^2`, proved from `profileX_sq`).
  The remaining integral is `Xi1 0 s - (∫_s^1 Θ0) 2` by the base case of
  `integral_iteratedDeriv_momentF_eq` with `f := semicircle`, where the only
  ingredients are the pointwise identity `1 - profileX σ^2 = (σ*profileX σ)^2`
  and `contDiff_profileX` / `deriv_profileX_nonpos`.

* Row 3: the same with the centroid integrand; the base integral vanishes by
  oddness in `t`, and `Ξ`'s fourth component is `-Xi2`.

Note.  The row identities above (`integral_iteratedDeriv_momentF_eq` etc.) are
stated with the root hypothesis for *all* `u : ℝ`, which is not satisfiable by
a globally smooth `f` agreeing with the semicircle (that would force
`f^2 = 1 - t^2` on all of `(0,1)`).  For the base solution one therefore uses
`semicircle` itself, whose square does agree with `1 - t^2` on the relevant
intervals; the smoothness needed by the Leibniz formula is available directly
for the explicit integrand `((1 - t^2) - (u*t)^2)^n`. -/
lemma volterra_base_identity (n : ℕ) (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ s ∈ Set.Icc a 1,
      RyaboginVolterra.G n (fun _ => 0) s (RyaboginVolterra.baseState s)
        = (∫ σ in s..1,
            RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ))
          + RyaboginVolterra.Xi n (fun _ => 0) s := by
  intro s hs
  apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
  funext i
  fin_cases i
  · exact volterra_base_row01 n ha hs 0 (Or.inl rfl)
  · exact volterra_base_row01 n ha hs 1 (Or.inr rfl)
  · exact volterra_base_row2 n hn ha hs
  · exact volterra_base_row3 n hn ha hs

/-- **First Volterra hypothesis**: `G` at the base data (`h = 0`) is bounded on
`[a,1] × closedBall (baseState 1) 1`.  Proved by compactness: the domain is
compact and `G` is continuous. -/
lemma volterra_base_G0_bound (n : ℕ) {a : ℝ} (_ha : 0 < a) (_ha1 : a ≤ 1) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc a 1, ∀ z ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1,
      ‖RyaboginVolterra.G n (fun _ => 0) s z‖ ≤ B := by
  have heval : ∀ i : Fin 4, Continuous (fun z : EuclideanSpace ℝ (Fin 4) => z i) := by
    intro i
    simpa using (EuclideanSpace.proj i).continuous
  have hcont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 4) =>
      RyaboginVolterra.G n (fun _ => 0) p.1 p.2) := by
    have hcoe : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 4) =>
        ((RyaboginVolterra.G n (fun _ => 0) p.1 p.2 : EuclideanSpace ℝ (Fin 4)) : Fin 4 → ℝ)) := by
      apply continuous_pi
      intro i
      fin_cases i <;>
        · simp only [RyaboginVolterra.G, RyaboginVolterra.mk4, RyaboginVolterra.endpointC,
            RyaboginVolterra.endpointD, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
            Pi.zero_apply, mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
            Matrix.vecTail, Function.comp_apply]
          fun_prop
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp hcoe
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
    hcont.continuousOn
  exact ⟨B, fun s hs z hz => hB (s, z) ⟨hs, hz⟩⟩

/-- **Second Volterra hypothesis**: `Θ` at the base data is bounded on
`[a,1] × [a,1] × closedBall (baseState 1) 1`.

Obstacle (recorded for the next pass): the third and fourth components of `Θ`
are *parametric* `iteratedDeriv`s whose parameter is multi-dimensional — they
depend on `(σ, x, y)`, not on a single real.  `contDiffOn_parametric_iteratedDeriv`
only covers a parameter in `ℝ`, so joint continuity in the parameter is not
available off the shelf.  Two routes: (a) prove the multi-parameter version of
that lemma by the same induction, or (b) bound the components by explicit
polynomial estimates, since on the base data the inner function is the
polynomial `u ↦ (A^2 - (u*t)^2)^n` in `u` and its `k`-th derivative at `s` is an
explicit finite sum.  The first two components are `-z 2`, `-z 3` and are
continuous outright. -/
private lemma continuous_theta_poly (n k : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv k (fun u : ℝ => (p.1 ^ 2 - u ^ 2) ^ n) p.2) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (p.1 ^ 2 - p.2 ^ 2) ^ n) := by fun_prop
  have hpar := Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv (k := k)
    (F := fun σ u : ℝ => (σ ^ 2 - u ^ 2) ^ n) isOpen_univ hA.contDiffOn
  have h1 := hpar.continuousOn
  rw [continuousOn_univ] at h1
  exact h1

private lemma continuous_theta_poly_comp (n k : ℕ) {X : Type*} [TopologicalSpace X]
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun p : X => iteratedDeriv k (fun u : ℝ => (a p ^ 2 - u ^ 2) ^ n) (b p)) :=
  (continuous_theta_poly n k).comp (ha.prodMk hb)

private lemma innerfactor (n : ℕ) (σ c : ℝ) :
    (fun u : ℝ =>
      (RyaboginVolterra.line (fun _ => 0) σ c ^ 2 - RyaboginVolterra.line (fun _ => 0) u c ^ 2) ^ n)
      = fun u : ℝ => c ^ (2 * n) * (σ ^ 2 - u ^ 2) ^ n := by
  funext u
  simp only [RyaboginVolterra.line, add_zero]
  rw [show ((σ * c) ^ 2 - (u * c) ^ 2) = c ^ 2 * (σ ^ 2 - u ^ 2) by ring]
  rw [mul_pow, ← pow_mul]

private lemma innerfactor_slope (n : ℕ) (σ c : ℝ) :
    (fun u : ℝ =>
      (RyaboginVolterra.line (fun _ => 0) σ c ^ 2 - RyaboginVolterra.line (fun _ => 0) u c ^ 2) ^ (n - 1)
        * RyaboginVolterra.lineSlope (fun _ => 0) u c)
      = fun u : ℝ => (c ^ (2 * (n - 1)) * c) * (σ ^ 2 - u ^ 2) ^ (n - 1) := by
  funext u
  have hz : deriv (fun _ : ℝ => (0 : ℝ)) u = 0 := deriv_const u 0
  simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope, add_zero, hz]
  rw [show ((σ * c) ^ 2 - (u * c) ^ 2) = c ^ 2 * (σ ^ 2 - u ^ 2) by ring]
  rw [mul_pow, ← pow_mul]
  ring

private lemma Theta_base_eq (n : ℕ) :
    (fun p : ℝ × ℝ × RyaboginVolterra.State =>
        RyaboginVolterra.Theta n (fun _ => 0) p.1 p.2.1 p.2.2)
      = fun p : ℝ × ℝ × RyaboginVolterra.State =>
        RyaboginVolterra.mk4 (- p.2.2 2) (- p.2.2 3)
          ((-(p.2.2 0)) ^ (2 * n)
              * iteratedDeriv (n + 1) (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ n) p.1 * p.2.2 2
            + (p.2.2 1) ^ (2 * n)
              * iteratedDeriv (n + 1) (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ n) p.1 * p.2.2 3)
          (((-(p.2.2 0)) ^ (2 * (n - 1)) * (-(p.2.2 0)))
              * iteratedDeriv n (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ (n - 1)) p.1 * p.2.2 2
            + ((p.2.2 1) ^ (2 * (n - 1)) * (p.2.2 1))
              * iteratedDeriv n (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ (n - 1)) p.1 * p.2.2 3) := by
  funext p
  obtain ⟨s, σ, Z⟩ := p
  have h1 := innerfactor n σ (-(Z 0))
  have h2 := innerfactor n σ (Z 1)
  have h3 := innerfactor_slope n σ (-(Z 0))
  have h4 := innerfactor_slope n σ (Z 1)
  have e1 : iteratedDeriv (n + 1)
        (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ (-(Z 0)) ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u (-(Z 0)) ^ 2) ^ n) s
      = (-(Z 0)) ^ (2 * n) * iteratedDeriv (n + 1) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ n) s := by
    rw [h1, iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℝ (↑(n+1)) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ n) s)]
  have e2 : iteratedDeriv (n + 1)
        (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ (Z 1) ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u (Z 1) ^ 2) ^ n) s
      = (Z 1) ^ (2 * n) * iteratedDeriv (n + 1) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ n) s := by
    rw [h2, iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℝ (↑(n+1)) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ n) s)]
  have e3 : iteratedDeriv n
        (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ (-(Z 0)) ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u (-(Z 0)) ^ 2) ^ (n - 1)
          * RyaboginVolterra.lineSlope (fun _ => 0) u (-(Z 0))) s
      = ((-(Z 0)) ^ (2 * (n - 1)) * (-(Z 0)))
          * iteratedDeriv n (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ (n - 1)) s := by
    rw [h3, iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℝ (↑n) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ (n-1)) s)]
  have e4 : iteratedDeriv n
        (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ (Z 1) ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u (Z 1) ^ 2) ^ (n - 1)
          * RyaboginVolterra.lineSlope (fun _ => 0) u (Z 1)) s
      = ((Z 1) ^ (2 * (n - 1)) * (Z 1))
          * iteratedDeriv n (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ (n - 1)) s := by
    rw [h4, iteratedDeriv_const_mul _ (by fun_prop : ContDiffAt ℝ (↑n) (fun u : ℝ => (σ ^ 2 - u ^ 2) ^ (n-1)) s)]
  simp only [RyaboginVolterra.Theta]
  rw [e1, e2, e3, e4]

set_option linter.unusedSimpArgs false in
private lemma continuous_mk4 {X : Type*} [TopologicalSpace X] (a b c d : X → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun p : X => RyaboginVolterra.mk4 (a p) (b p) (c p) (d p)) := by
  have hcoe : Continuous (fun p : X =>
      ((RyaboginVolterra.mk4 (a p) (b p) (c p) (d p) : RyaboginVolterra.State) : Fin 4 → ℝ)) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i <;>
      · simp only [RyaboginVolterra.mk4, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
          Matrix.vecTail]
        first | exact ha | exact hb | exact hc | exact hd
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp hcoe

private lemma continuous_Theta_base (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State =>
      RyaboginVolterra.Theta n (fun _ => 0) p.1 p.2.1 p.2.2) := by
  rw [Theta_base_eq n]
  have hZ : ∀ i : Fin 4, Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State =>
      (p.2.2 : Fin 4 → ℝ) i) := fun i =>
    (EuclideanSpace.proj i).continuous.comp (continuous_snd.comp continuous_snd)
  have hσ : Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hs0 : Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State => p.1) := continuous_fst
  have hP : Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State =>
      iteratedDeriv (n + 1) (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ n) p.1) :=
    continuous_theta_poly_comp n (n + 1) (fun p : ℝ × ℝ × RyaboginVolterra.State => p.2.1)
      (fun p : ℝ × ℝ × RyaboginVolterra.State => p.1) hσ hs0
  have hQ : Continuous (fun p : ℝ × ℝ × RyaboginVolterra.State =>
      iteratedDeriv n (fun u : ℝ => (p.2.1 ^ 2 - u ^ 2) ^ (n - 1)) p.1) :=
    continuous_theta_poly_comp (n - 1) n (fun p : ℝ × ℝ × RyaboginVolterra.State => p.2.1)
      (fun p : ℝ × ℝ × RyaboginVolterra.State => p.1) hσ hs0
  refine continuous_mk4 _ _ _ _ (hZ 2).neg (hZ 3).neg ?_ ?_
  · refine Continuous.add ?_ ?_
    · exact (((hZ 0).neg.pow _).mul hP).mul (hZ 2)
    · exact (((hZ 1).pow _).mul hP).mul (hZ 3)
  · refine Continuous.add ?_ ?_
    · exact ((((hZ 0).neg.pow _).mul (hZ 0).neg).mul hQ).mul (hZ 2)
    · exact ((((hZ 1).pow _).mul (hZ 1)).mul hQ).mul (hZ 3)

/-- **Second Volterra hypothesis**: `Θ` at the base data is bounded on
`[a,1] × [a,1] × closedBall (baseState 1) 1`.

For the base data `h = 0` the third and fourth components of `Θ` are explicit
polynomials in the state `Z` and in `s`, `σ` (the inner functions factor as
`c^{2n} (σ^2-u^2)^n`), so joint continuity in `(s, σ, Z)` follows from
`contDiffOn_parametric_iteratedDeriv`, and boundedness on the compact box is
`IsCompact.exists_bound_of_continuousOn`. -/
lemma volterra_base_Theta0_bound (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      ∀ z ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1,
      ‖RyaboginVolterra.Theta n (fun _ => 0) s σ z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc.prod
    (isCompact_closedBall _ _))).exists_bound_of_continuousOn
    (continuous_Theta_base n).continuousOn
  exact ⟨B, fun s hs σ hσ z hz => hB (s, σ, z) (by exact ⟨hs, hσ, hz⟩)⟩

/-- A smooth bump supported in `[1 - 2τ, 1 - τ]`, flat near `1 - 2τ`. -/
private lemma exists_bump_flat (τ : ℝ) (_hτ0 : 0 < τ) (hτsmall : 2 * τ < 1) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧
      Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) ∧
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0) := by
  let a : ℝ := 1 - 2 * τ
  let b : ℝ := 1 - τ
  have hab : a < b := by dsimp [a, b]; linarith
  have hgap : 0 < b - a := by linarith
  let θ : ℝ := (b - a) / 4
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hbθ : 0 < b - θ - (a + θ) := by dsimp [θ]; linarith
  have ha1 : a < a + θ := by linarith
  have hmid_in : a + θ < a + θ + (b - θ - (a + θ)) / 2 := by linarith
  have hmid_lt : a + θ + (b - θ - (a + θ)) / 2 < b - θ := by linarith
  have hIoo : Set.Ioo (a + θ) (b - θ) ∈ 𝓝 (a + θ + (b - θ - (a + θ)) / 2) :=
    Ioo_mem_nhds hmid_in hmid_lt
  obtain ⟨h, htsupp, _hcomp, hdiff, _hrng, hx⟩ :=
    exists_contDiff_tsupport_subset (E := ℝ) (s := Set.Ioo (a + θ) (b - θ))
      (x := a + θ + (b - θ - (a + θ)) / 2) (n := ⊤) hIoo
  have hsupp : Function.support h ⊆ Set.Icc a b := by
    intro s hs
    have hs_ts : s ∈ tsupport h := subset_tsupport h hs
    have hs_ioo : s ∈ Set.Ioo (a + θ) (b - θ) := htsupp hs_ts
    exact ⟨le_of_lt (lt_trans ha1 hs_ioo.1), le_of_lt (lt_trans hs_ioo.2 (by linarith))⟩
  refine ⟨h, hdiff, hsupp, ?_, ⟨θ, hθ, ?_⟩⟩
  · refine ⟨a + θ + (b - θ - (a + θ)) / 2, ?_, ?_⟩
    · have : a < a + θ + (b - θ - (a + θ)) / 2 := by linarith
      linarith
    · rw [hx]; norm_num
  · intro s hs1 hs2
    by_contra hne
    have hs_supp : s ∈ Function.support h := by simpa [Function.mem_support] using hne
    have hs_ts : s ∈ tsupport h := subset_tsupport h hs_supp
    have hs_ioo : s ∈ Set.Ioo (a + θ) (b - θ) := htsupp hs_ts
    linarith [hs_ioo.1]

/-! ## Auxiliary infrastructure for the local perturbation (Ryabogin, even case) -/


lemma contDiffOn_deriv_snd_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {G : P → ℝ → ℝ} {U : Set (P × ℝ)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : P × ℝ => G p.1 p.2) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : P × ℝ => deriv (fun v : ℝ => G p.1 v) p.2) U := by
  let H : P × ℝ → ℝ := fun p : P × ℝ => G p.1 p.2
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := hG
  have hfderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H) U :=
    hH.fderiv_of_isOpen hU (by simp)
  have hconst : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : P × ℝ => ((0, 1) : P × ℝ)) U :=
    contDiffOn_const
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : P × ℝ => (fderiv ℝ H p) ((0, 1) : P × ℝ)) U :=
    hfderiv.clm_apply hconst
  refine hmain.congr ?_
  intro p hp
  have hdiff : DifferentiableAt ℝ H p := by
    have hdiffOn : DifferentiableOn ℝ H U := hH.differentiableOn (by simp)
    exact hdiffOn.differentiableAt (hU.mem_nhds hp)
  have hdiffH_at : DifferentiableAt ℝ H (p.1, p.2) := by simpa using hdiff
  have hφdiff : DifferentiableAt ℝ (fun v : ℝ => (p.1, v)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hφfderiv : fderiv ℝ (fun v : ℝ => (p.1, v)) p.2 =
      ContinuousLinearMap.inr ℝ P ℝ :=
    (hasFDerivAt_prodMk_right p.1 p.2).fderiv
  have hfd : fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2 =
      (fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ P ℝ) := by
    rw [fderiv_fun_comp p.2 hdiffH_at hφdiff, hφfderiv]
  change deriv (fun v : ℝ => H (p.1, v)) p.2 = (fderiv ℝ H p) ((0, 1) : P × ℝ)
  calc
    deriv (fun v : ℝ => H (p.1, v)) p.2
        = (fderiv ℝ (fun v : ℝ => H (p.1, v)) p.2) 1 := by
          rw [fderiv_apply_one_eq_deriv]
    _ = ((fderiv ℝ H (p.1, p.2)).comp (ContinuousLinearMap.inr ℝ P ℝ)) 1 := by
          rw [hfd]
    _ = (fderiv ℝ H p) ((0, 1) : P × ℝ) := by
          simp

lemma contDiffOn_parametric_iteratedDeriv_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : ℕ} {F : P → ℝ → ℝ} {U : Set (P × ℝ)}
    (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : P × ℝ => F p.1 p.2) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : P × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hF
  | succ k ih =>
      have hprev : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : P × ℝ => iteratedDeriv k (fun v : ℝ => F p.1 v) p.2) U := ih
      let G : P → ℝ → ℝ := fun x v => iteratedDeriv k (fun t : ℝ => F x t) v
      have hprevG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : P × ℝ => G p.1 p.2) U := by
        simpa [G] using hprev
      have hstep : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : P × ℝ =>
            deriv (fun v : ℝ => iteratedDeriv k (fun t : ℝ => F p.1 t) v) p.2) U := by
        simpa [G] using contDiffOn_deriv_snd_prod hU hprevG
      refine hstep.congr ?_
      intro p hp
      rw [iteratedDeriv_succ]

lemma continuousLinearEquivOfDetNeZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] E) (hdet : (f : E →ₗ[ℝ] E).det ≠ 0) :
    ∃ Q : E ≃L[ℝ] E, Q.toContinuousLinearMap = f := by
  set L : E →ₗ[ℝ] E := (f : E →ₗ[ℝ] E) with hL
  have hker : L.ker = ⊥ := by
    by_contra h
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := L)).mpr h)
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective L := ⟨hinj, hsurj⟩
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective L hbij
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  ext x
  show (LinearEquiv.ofBijective L hbij) x = f x
  rw [LinearEquiv.ofBijective_apply]
  rfl

noncomputable def baseG (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) : RyaboginVolterra.State :=
  RyaboginVolterra.G n (fun _ => 0) s z

noncomputable def baseZ (s : ℝ) : RyaboginVolterra.State := RyaboginVolterra.baseState s

lemma baseG_apply_zero (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) : baseG n s z 0 = z 0 := by
  simp [baseG, RyaboginVolterra.G, RyaboginVolterra.mk4_apply]

lemma baseG_apply_one (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) : baseG n s z 1 = z 1 := by
  simp [baseG, RyaboginVolterra.G, RyaboginVolterra.mk4_apply]

set_option linter.unusedSimpArgs false in
lemma baseG_apply_two (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) :
    baseG n s z 2 = (-2:ℝ)^n * (n.factorial : ℝ) * ((s * (z 0)^2)^n * z 2 + (s * (z 1)^2)^n * z 3) := by
  have hz : deriv (fun _ : ℝ => (0:ℝ)) s = 0 := deriv_const s 0
  simp only [baseG, RyaboginVolterra.G, RyaboginVolterra.endpointC, RyaboginVolterra.line,
    RyaboginVolterra.lineSlope, RyaboginVolterra.mk4_apply, hz, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.isValue, Function.comp_apply]
  ring_nf

set_option linter.unusedSimpArgs false in
lemma baseG_apply_three (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) :
    baseG n s z 3 = (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
      ((s * (z 0)^2)^(n-1) * (-(z 0) * z 2) + (s * (z 1)^2)^(n-1) * ((z 1) * z 3)) := by
  have hz : deriv (fun _ : ℝ => (0:ℝ)) s = 0 := deriv_const s 0
  simp only [baseG, RyaboginVolterra.G, RyaboginVolterra.endpointD, RyaboginVolterra.line,
    RyaboginVolterra.lineSlope, RyaboginVolterra.mk4_apply, hz, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.isValue, Function.comp_apply]
  ring_nf

lemma baseZ_apply_zero (s : ℝ) : baseZ s 0 = profileX s := by
  simp [baseZ, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]

lemma baseZ_apply_one (s : ℝ) : baseZ s 1 = profileX s := by
  simp [baseZ, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]

lemma baseZ_apply_two (s : ℝ) : baseZ s 2 = deriv profileX s := by
  simp [baseZ, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]

lemma baseZ_apply_three (s : ℝ) : baseZ s 3 = deriv profileX s := by
  simp [baseZ, RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]

lemma baseG_apply (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) :
    baseG n s z = RyaboginVolterra.mk4 (z 0) (z 1)
      ((-2:ℝ)^n * (n.factorial : ℝ) * ((s * (z 0)^2)^n * z 2 + (s * (z 1)^2)^n * z 3))
      ((-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
        ((s * (z 0)^2)^(n-1) * (-(z 0) * z 2) + (s * (z 1)^2)^(n-1) * ((z 1) * z 3))) := by
  ext i
  fin_cases i
  · simpa [RyaboginVolterra.mk4_apply] using baseG_apply_zero n s z
  · simpa [RyaboginVolterra.mk4_apply] using baseG_apply_one n s z
  · simpa [RyaboginVolterra.mk4_apply] using baseG_apply_two n s z
  · simpa [RyaboginVolterra.mk4_apply] using baseG_apply_three n s z

set_option linter.unusedSimpArgs false in
lemma baseG_differentiableAt (n : ℕ) (s : ℝ) (z : RyaboginVolterra.State) :
    DifferentiableAt ℝ (fun w : RyaboginVolterra.State => baseG n s w) z := by
  have hz : deriv (fun _ : ℝ => (0:ℝ)) s = 0 := deriv_const s 0
  have hcoe : DifferentiableAt ℝ
      (fun w : RyaboginVolterra.State => ((baseG n s w : RyaboginVolterra.State) : Fin 4 → ℝ)) z := by
    rw [differentiableAt_pi]
    intro i
    fin_cases i <;>
      · simp only [baseG, RyaboginVolterra.G, RyaboginVolterra.mk4_apply, RyaboginVolterra.endpointC,
          RyaboginVolterra.endpointD, RyaboginVolterra.line, RyaboginVolterra.lineSlope, hz,
          add_zero, mul_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
          Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
          Fin.reduceFinMk, Function.comp_apply]
        fun_prop
  have h2 : (fun w : RyaboginVolterra.State => ((baseG n s w : RyaboginVolterra.State) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : RyaboginVolterra.State → (Fin 4 → ℝ)) ∘
        (fun w : RyaboginVolterra.State => baseG n s w) := rfl
  rw [h2] at hcoe
  have h3 := ((EuclideanSpace.equiv (Fin 4) ℝ).symm.differentiableAt).comp z hcoe
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Function.comp_apply]

lemma baseG_fderiv_curve (n : ℕ) (v : RyaboginVolterra.State) :
    HasDerivAt (fun t : ℝ => baseG n 1 (baseZ 1 + t • v))
      ((fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)) v) 0 := by
  have hd := baseG_differentiableAt n 1 (baseZ 1)
  have hc : HasDerivAt (fun t : ℝ => baseZ 1 + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) ((1:ℝ) • v) 0 := (hasDerivAt_id (0:ℝ)).smul_const v
    simpa using h1.const_add (baseZ 1)
  have hd' : HasFDerivAt (fun z : RyaboginVolterra.State => baseG n 1 z)
      (fderiv ℝ (fun z : RyaboginVolterra.State => baseG n 1 z) (baseZ 1))
      (baseZ 1 + (0:ℝ) • v) := by
    simpa using hd.hasFDerivAt
  have hmain := hd'.comp_hasDerivAt 0 hc
  refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  rfl




set_option linter.unusedSimpArgs false in
lemma baseG_fderiv_ne_zero (n : ℕ) {v : RyaboginVolterra.State}
    (hv : (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)) v = 0) : v = 0 := by
  have hcv := baseG_fderiv_curve n v
  have hcomp : ∀ i : Fin 4, HasDerivAt (fun t : ℝ => (baseG n 1 (baseZ 1 + t • v)) i)
      (((fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)) v) i) 0 := fun i => by
    have hthis := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hcv
    refine hthis.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    rfl
  have hprof : profileX 1 ≠ 0 := ne_of_gt (profileX_pos 1 (by norm_num))
  have h0 : v 0 = 0 := by
    have h := hcomp 0
    have hfun : (fun t : ℝ => (baseG n 1 (baseZ 1 + t • v)) 0)
        = fun t : ℝ => (baseZ 1) 0 + t * v 0 := by
      funext t
      rw [baseG_apply_zero]
      simp
    rw [hfun] at h
    have h' : HasDerivAt (fun t : ℝ => (baseZ 1) 0 + t * v 0) (v 0) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t * v 0) (1 * v 0) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 0)
      simpa using h1.const_add ((baseZ 1) 0)
    have huu := h.unique h'
    rw [hv] at huu
    simpa using huu.symm
  have h1 : v 1 = 0 := by
    have h := hcomp 1
    have hfun : (fun t : ℝ => (baseG n 1 (baseZ 1 + t • v)) 1)
        = fun t : ℝ => (baseZ 1) 1 + t * v 1 := by
      funext t
      rw [baseG_apply_one]
      simp
    rw [hfun] at h
    have h' : HasDerivAt (fun t : ℝ => (baseZ 1) 1 + t * v 1) (v 1) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t * v 1) (1 * v 1) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 1)
      simpa using h1.const_add ((baseZ 1) 1)
    have huu := h.unique h'
    rw [hv] at huu
    simpa using huu.symm
  have h2 : v 2 + v 3 = 0 := by
    have h := hcomp 2
    have hfun : (fun t : ℝ => (baseG n 1 (baseZ 1 + t • v)) 2)
        = fun t : ℝ => (-2:ℝ)^n * (n.factorial : ℝ) * ((profileX 1)^(2*n) *
            (((baseZ 1) 2 + t * v 2) + ((baseZ 1) 3 + t * v 3))) := by
      funext t
      have hz0 : (baseZ 1 + t • v) 0 = profileX 1 := by simp [h0, baseZ_apply_zero]
      have hz1 : (baseZ 1 + t • v) 1 = profileX 1 := by simp [h1, baseZ_apply_one]
      have hz2 : (baseZ 1 + t • v) 2 = (baseZ 1) 2 + t * v 2 := by simp
      have hz3 : (baseZ 1 + t • v) 3 = (baseZ 1) 3 + t * v 3 := by simp
      rw [baseG_apply_two, hz0, hz1, hz2, hz3]
      simp only [one_mul]
      rw [← pow_mul]
      ring
    rw [hfun] at h
    have h' : HasDerivAt (fun t : ℝ => (-2:ℝ)^n * (n.factorial : ℝ) *
        ((profileX 1)^(2*n) * (((baseZ 1) 2 + t * v 2) + ((baseZ 1) 3 + t * v 3))))
        ((-2:ℝ)^n * (n.factorial : ℝ) * ((profileX 1)^(2*n) * (v 2 + v 3))) 0 := by
      have ha : HasDerivAt (fun t : ℝ => (baseZ 1) 2 + t * v 2) (v 2) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v 2) (1 * v 2) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 2)
        simpa using h1.const_add ((baseZ 1) 2)
      have hb : HasDerivAt (fun t : ℝ => (baseZ 1) 3 + t * v 3) (v 3) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v 3) (1 * v 3) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 3)
        simpa using h1.const_add ((baseZ 1) 3)
      have hsum : HasDerivAt (fun t : ℝ => ((baseZ 1) 2 + t * v 2) + ((baseZ 1) 3 + t * v 3))
          (v 2 + v 3) 0 := ha.add hb
      have hm := hsum.const_mul ((profileX 1)^(2*n))
      exact (hm.const_mul ((-2:ℝ)^n * (n.factorial : ℝ))).congr_deriv (by ring)
    have huu := h.unique h'
    rw [hv] at huu
    have hzero : (-2:ℝ)^n * (n.factorial : ℝ) * ((profileX 1)^(2*n) * (v 2 + v 3)) = 0 := huu.symm
    have hc : ((-2:ℝ)^n * (n.factorial : ℝ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    rcases mul_eq_zero.mp hzero with hA | hB
    · exact absurd hA hc
    · rcases mul_eq_zero.mp hB with hC | hD
      · exact absurd hC (pow_ne_zero _ hprof)
      · exact hD
  have h3 : v 3 - v 2 = 0 := by
    have h := hcomp 3
    have hfun : (fun t : ℝ => (baseG n 1 (baseZ 1 + t • v)) 3)
        = fun t : ℝ => (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
            (((profileX 1)^(2*(n-1)) * profileX 1) *
              (((baseZ 1) 3 + t * v 3) - ((baseZ 1) 2 + t * v 2))) := by
      funext t
      have hz0 : (baseZ 1 + t • v) 0 = profileX 1 := by simp [h0, baseZ_apply_zero]
      have hz1 : (baseZ 1 + t • v) 1 = profileX 1 := by simp [h1, baseZ_apply_one]
      have hz2 : (baseZ 1 + t • v) 2 = (baseZ 1) 2 + t * v 2 := by simp
      have hz3 : (baseZ 1 + t • v) 3 = (baseZ 1) 3 + t * v 3 := by simp
      rw [baseG_apply_three, hz0, hz1, hz2, hz3]
      simp only [one_mul]
      ring_nf
    rw [hfun] at h
    have h' : HasDerivAt (fun t : ℝ => (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
        (((profileX 1)^(2*(n-1)) * profileX 1) *
          (((baseZ 1) 3 + t * v 3) - ((baseZ 1) 2 + t * v 2))))
        ((-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
          (((profileX 1)^(2*(n-1)) * profileX 1) * (v 3 - v 2))) 0 := by
      have ha : HasDerivAt (fun t : ℝ => (baseZ 1) 3 + t * v 3) (v 3) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v 3) (1 * v 3) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 3)
        simpa using h1.const_add ((baseZ 1) 3)
      have hb : HasDerivAt (fun t : ℝ => (baseZ 1) 2 + t * v 2) (v 2) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v 2) (1 * v 2) 0 := (hasDerivAt_id (0:ℝ)).mul_const (v 2)
        simpa using h1.const_add ((baseZ 1) 2)
      have hsum : HasDerivAt (fun t : ℝ => ((baseZ 1) 3 + t * v 3) - ((baseZ 1) 2 + t * v 2))
          (v 3 - v 2) 0 := ha.sub hb
      have hm := hsum.const_mul ((profileX 1)^(2*(n-1)) * profileX 1)
      exact (hm.const_mul ((-2:ℝ)^(n-1) * ((n-1).factorial : ℝ))).congr_deriv (by ring)
    have huu := h.unique h'
    rw [hv] at huu
    have hzero : (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
        (((profileX 1)^(2*(n-1)) * profileX 1) * (v 3 - v 2)) = 0 := huu.symm
    have hc : ((-2:ℝ)^(n-1) * ((n-1).factorial : ℝ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-1)))
    rcases mul_eq_zero.mp hzero with hA | hB
    · exact absurd hA hc
    · rcases mul_eq_zero.mp hB with hC | hD
      · exact absurd hC (mul_ne_zero (pow_ne_zero _ hprof) hprof)
      · exact hD
  have hv3 : v 3 = 0 := by linarith
  have hv2 : v 2 = 0 := by linarith
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using hv2
  · simpa using hv3


lemma baseG_fderiv_det_ne_zero (n : ℕ) :
    (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)).det ≠ 0 := by
  intro h0
  have hker : (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)).toLinearMap.ker ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp h0
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv : (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)) v = 0 := hvmem
  exact hvne (baseG_fderiv_ne_zero n hv)

lemma exists_baseG_equiv (n : ℕ) :
    ∃ Q : RyaboginVolterra.State ≃L[ℝ] RyaboginVolterra.State,
      Q.toContinuousLinearMap = fderiv ℝ (fun z => baseG n 1 z) (baseZ 1) :=
  continuousLinearEquivOfDetNeZero _ (baseG_fderiv_det_ne_zero n)


/-- Base `Θ` for `h ≡ 0`. -/
noncomputable def baseΘ (n : ℕ) (s σ : ℝ) (z : RyaboginVolterra.State) : RyaboginVolterra.State :=
  RyaboginVolterra.Theta n (fun _ => 0) s σ z

/-- Base `Ξ` for `h ≡ 0`. -/
noncomputable def baseΞ (n : ℕ) (s : ℝ) : RyaboginVolterra.State :=
  RyaboginVolterra.Xi n (fun _ => 0) s

/-- The rescaled/normalised system `U ↦ (1/ρ) • Qe.symm (G(s, Z₀(s) + ρ•U))`:
its derivative at the base point vanishes shift and equals the identity, which makes
the Lubarsch–Volterra contraction constant small on the unit ball. -/
noncomputable def TG (n : ℕ) (Qe : RyaboginVolterra.State ≃L[ℝ] RyaboginVolterra.State)
    (ρ : ℝ) (s : ℝ) (U : RyaboginVolterra.State) : RyaboginVolterra.State :=
  (1 / ρ) • Qe.symm (baseG n s (baseZ s + ρ • U))

/-- Similarly transformed `Θ`. -/
noncomputable def TΘ (n : ℕ) (Qe : RyaboginVolterra.State ≃L[ℝ] RyaboginVolterra.State)
    (ρ : ℝ) (s σ : ℝ) (U : RyaboginVolterra.State) : RyaboginVolterra.State :=
  (1 / ρ) • Qe.symm (baseΘ n s σ (baseZ σ + ρ • U))

/-- Similarly transformed `Ξ`. -/
noncomputable def TΞ (n : ℕ) (Qe : RyaboginVolterra.State ≃L[ℝ] RyaboginVolterra.State)
    (ρ : ℝ) (s : ℝ) : RyaboginVolterra.State :=
  (1 / ρ) • Qe.symm (baseΞ n s)


abbrev VS := RyaboginVolterra.State

lemma TG_fderiv_base (n : ℕ) (Qe : VS ≃L[ℝ] VS)
    (hQe : Qe.toContinuousLinearMap = fderiv ℝ (fun z => baseG n 1 z) (baseZ 1))
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    fderiv ℝ (fun U : VS => TG n Qe ρ 1 U) 0 = 1 := by
  have h1 : HasFDerivAt (fun U : VS => baseZ 1 + ρ • U) (ρ • (1 : VS →L[ℝ] VS)) 0 := by
    have hbase : HasFDerivAt (fun U : VS => (ρ • (1 : VS →L[ℝ] VS)) U) (ρ • (1 : VS →L[ℝ] VS)) 0 :=
      ContinuousLinearMap.hasFDerivAt _
    simpa using hbase.const_add (baseZ 1)
  have h2 : HasFDerivAt (fun z : VS => baseG n 1 z)
      (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1)) (baseZ 1) :=
    (baseG_differentiableAt n 1 (baseZ 1)).hasFDerivAt
  have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
      ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n 1 (baseZ 1)) := by
    have hbase : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n 1 (baseZ 1)) :=
      ContinuousLinearMap.hasFDerivAt _
    simpa using hbase
  have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n 1 z))
      (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
        (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1))) (baseZ 1 + ρ • (0 : VS)) := by
    simpa using (HasFDerivAt.comp (baseZ 1) h3 h2)
  have hmain : HasFDerivAt
      (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n 1 z)) ∘
        (fun U : VS => baseZ 1 + ρ • U))
      ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
        (fderiv ℝ (fun z => baseG n 1 z) (baseZ 1))).comp (ρ • (1 : VS →L[ℝ] VS))) 0 :=
    HasFDerivAt.comp (0 : VS) hgb h1
  have hfun : (fun U : VS => TG n Qe ρ 1 U)
      = (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n 1 z)) ∘
          (fun U : VS => baseZ 1 + ρ • U)) := by
    funext U; rfl
  rw [hfun, hmain.fderiv, ← hQe]
  refine ContinuousLinearMap.ext fun U => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  change (1 / ρ) • (Qe.symm (Qe (ρ • U))) = U
  rw [ContinuousLinearEquiv.symm_apply_apply]
  simp [smul_smul, inv_mul_cancel₀ hρ]


lemma Tbase_identity (n : ℕ) (hn : 2 ≤ n) (Qe : VS ≃L[ℝ] VS)
    (hQe : Qe.toContinuousLinearMap = fderiv ℝ (fun z => baseG n 1 z) (baseZ 1))
    {ρ : ℝ} (hρ : ρ ≠ 0) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ s ∈ Set.Icc a 1,
      TG n Qe ρ s 0 = (∫ σ in s..1, TΘ n Qe ρ s σ 0) + TΞ n Qe ρ s := by
  intro s hs
  have hbase := volterra_base_identity n hn ha ha1 s hs
  have hcont : Continuous
      (fun σ : ℝ => RyaboginVolterra.Theta n (fun _ => 0) s σ
        (RyaboginVolterra.baseState σ)) := by
    have h := continuous_Theta_integrand n (h := fun _ => 0) (x := profileX) (y := profileX)
      contDiff_const RyaboginVolterra.contDiff_profileX RyaboginVolterra.contDiff_profileX s
    refine h.congr fun σ => ?_
    simp [RyaboginVolterra.stateOf, RyaboginVolterra.baseState]
  have hint : IntervalIntegrable
      (fun σ : ℝ => RyaboginVolterra.Theta n (fun _ => 0) s σ
        (RyaboginVolterra.baseState σ)) volume s 1 :=
    hcont.intervalIntegrable s 1
  have hL : (∫ σ in s..1, Qe.symm
        (RyaboginVolterra.Theta n (fun _ => 0) s σ (RyaboginVolterra.baseState σ)))
      = Qe.symm (∫ σ in s..1, RyaboginVolterra.Theta n (fun _ => 0) s σ
            (RyaboginVolterra.baseState σ)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm (Qe.symm : VS →L[ℝ] VS) hint
  simp only [TG, TΘ, TΞ, baseΘ, baseΞ, baseZ, baseG, smul_zero, add_zero]
  rw [intervalIntegral.integral_smul]
  rw [hL]
  rw [hbase]
  simp [map_add, smul_add]


lemma TG_fderiv_base_det (n : ℕ) (Qe : VS ≃L[ℝ] VS)
    (hQe : Qe.toContinuousLinearMap = fderiv ℝ (fun z => baseG n 1 z) (baseZ 1))
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    (fderiv ℝ (fun U : VS => TG n Qe ρ 1 U) 0).det ≠ 0 := by
  change LinearMap.det ((fderiv ℝ (fun U : VS => TG n Qe ρ 1 U) 0) : VS →ₗ[ℝ] VS) ≠ 0
  rw [show ((fderiv ℝ (fun U : VS => TG n Qe ρ 1 U) 0) : VS →ₗ[ℝ] VS) = (1 : VS →ₗ[ℝ] VS) from
    congrArg (fun L : VS →L[ℝ] VS => (L : VS →ₗ[ℝ] VS)) (TG_fderiv_base n Qe hQe hρ)]
  rw [show (1 : VS →ₗ[ℝ] VS) = LinearMap.id from rfl, LinearMap.det_id]
  exact one_ne_zero


/-- The base solution of the normalised (`TG`/`TΘ`/`TΞ`) system is the constant zero
function (`baseZ s + ρ • 0 = baseZ s`); in particular it is continuous on any interval. -/
lemma TZ0_cont {a b : ℝ} :
    ContinuousOn (fun _ : ℝ => (0 : VS)) (Set.Icc a b) :=
  continuousOn_const



/-- The transformed kernel `TG` is bounded on `[a,1] × closedBall 0 1`, provided the
base point stays in the ball of radius `1` around `baseState 1` and `ρ ≤ 1/2`. -/
lemma TG_bound (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc a 1, ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖TG n Qe ρ s U‖ ≤ B := by
  obtain ⟨B, hB⟩ := volterra_base_G0_bound n ha0 ha1
  refine ⟨(1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * B, fun s hs U hU => ?_⟩
  have hz : baseZ s + ρ • U ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖baseZ s + ρ • U - baseZ 1‖ ≤ 1
    have h1 : ‖baseZ s - baseZ 1‖ < 1 / 2 := hclose s hs
    have hU' : ‖U‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hU
    have h2 : ‖ρ • U‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0]
      calc ρ * ‖U‖ ≤ (1 / 2) * 1 := mul_le_mul hρ1 hU' (norm_nonneg _) (by norm_num)
        _ = 1 / 2 := by ring
    have h3 : baseZ s + ρ • U - baseZ 1 = (baseZ s - baseZ 1) + ρ • U := by abel
    rw [h3]
    linarith [norm_add_le (baseZ s - baseZ 1) (ρ • U)]
  have hGs : ‖baseG n s (baseZ s + ρ • U)‖ ≤ B := hB s hs _ hz
  have hop : ‖Qe.symm (baseG n s (baseZ s + ρ • U))‖
      ≤ ‖Qe.symm.toContinuousLinearMap‖ * B :=
    le_trans (ContinuousLinearMap.le_opNorm Qe.symm.toContinuousLinearMap
      (baseG n s (baseZ s + ρ • U))) (mul_le_mul_of_nonneg_left hGs (norm_nonneg _))
  calc ‖TG n Qe ρ s U‖
      = ‖(1 / ρ) • Qe.symm (baseG n s (baseZ s + ρ • U))‖ := rfl
    _ ≤ (1 / ρ) * (‖Qe.symm.toContinuousLinearMap‖ * B) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ρ)]
        exact mul_le_mul_of_nonneg_left hop (by positivity)
    _ = (1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * B := by ring


set_option linter.unusedSimpArgs false in
lemma continuous_baseZ : Continuous baseZ := by
  have hcoe : Continuous (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ)) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · have h : (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ) 0) = profileX := by
        funext s; exact baseZ_apply_zero s
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      exact RyaboginVolterra.contDiff_profileX.continuous
    · have h : (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ) 1) = profileX := by
        funext s; exact baseZ_apply_one s
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      exact RyaboginVolterra.contDiff_profileX.continuous
    · have h : (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ) 2) = deriv profileX := by
        funext s; exact baseZ_apply_two s
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      exact RyaboginVolterra.contDiff_profileX.continuous_deriv (by simp)
    · have h : (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ) 3) = deriv profileX := by
        funext s; exact baseZ_apply_three s
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      exact RyaboginVolterra.contDiff_profileX.continuous_deriv (by simp)
  have h2 : (fun s : ℝ => ((baseZ s : VS) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘ baseZ := rfl
  rw [h2] at hcoe
  have h3 := ((EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous).comp hcoe
  have h4 : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) ∘
      ((EuclideanSpace.equiv (Fin 4) ℝ) ∘ baseZ) = baseZ := by
    funext s
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  rw [h4] at h3
  exact h3

/-- The base point `baseZ s` stays within `1/2` of `baseZ 1` on a two-sided
neighbourhood of `1`; this is the `δZ` mechanism used to place the base point
inside `closedBall (baseState 1) 1`. -/
lemma exists_delta_baseZ_close :
    ∃ δ > 0, ∀ s : ℝ, |s - 1| < δ → ‖baseZ s - baseZ 1‖ < 1 / 2 := by
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp continuous_baseZ.continuousAt (1 / 2) (by norm_num)
  refine ⟨δ, hδpos, fun s hs => ?_⟩
  have h := hδ (show dist s 1 < δ from by simpa [Real.dist_eq] using hs)
  simpa [dist_eq_norm] using h


/-- The base point `baseZ s + ρ • U` lands in the unit ball around `baseState 1`,
whenever `s` is close to `1` and `‖U‖ ≤ 1`, `ρ ≤ 1/2`. -/
lemma base_close_ball {ρ a : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) {s : ℝ}
    (hs : s ∈ Set.Icc a 1) {U : VS} (hU : U ∈ Metric.closedBall (0 : VS) 1) :
    baseZ s + ρ • U ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  change ‖baseZ s + ρ • U - baseZ 1‖ ≤ 1
  have h1 : ‖baseZ s - baseZ 1‖ < 1 / 2 := hclose s hs
  have hU' : ‖U‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hU
  have h2 : ‖ρ • U‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0]
    calc ρ * ‖U‖ ≤ (1 / 2) * 1 := mul_le_mul hρ1 hU' (norm_nonneg _) (by norm_num)
      _ = 1 / 2 := by ring
  have h3 : baseZ s + ρ • U - baseZ 1 = (baseZ s - baseZ 1) + ρ • U := by abel
  rw [h3]
  linarith [norm_add_le (baseZ s - baseZ 1) (ρ • U)]

/-- The transformed kernel `TΘ` is bounded on `[a,1]² × closedBall 0 1`. -/
lemma TΘ_bound (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1, ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖TΘ n Qe ρ s σ U‖ ≤ B := by
  obtain ⟨B, hB⟩ := volterra_base_Theta0_bound n ha0 ha1
  refine ⟨(1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * B,
    fun s hs σ hσ U hU => ?_⟩
  have hz := base_close_ball hρ0 hρ1 hclose hσ hU
  have hG : ‖baseΘ n s σ (baseZ σ + ρ • U)‖ ≤ B := hB s hs σ hσ _ hz
  have hop : ‖Qe.symm (baseΘ n s σ (baseZ σ + ρ • U))‖
      ≤ ‖Qe.symm.toContinuousLinearMap‖ * B :=
    le_trans (ContinuousLinearMap.le_opNorm Qe.symm.toContinuousLinearMap
      (baseΘ n s σ (baseZ σ + ρ • U))) (mul_le_mul_of_nonneg_left hG (norm_nonneg _))
  calc ‖TΘ n Qe ρ s σ U‖
      = ‖(1 / ρ) • Qe.symm (baseΘ n s σ (baseZ σ + ρ • U))‖ := rfl
    _ ≤ (1 / ρ) * (‖Qe.symm.toContinuousLinearMap‖ * B) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ρ)]
        exact mul_le_mul_of_nonneg_left hop (by positivity)
    _ = (1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * B := by ring


/-- The transformed inhomogeneous term `TΞ` is bounded on `[a,1]`.  The bound on the
base `Ξ` is read off the base identity `G = ∫Θ + Ξ` combined with the `G` and `Θ`
bounds, so no separate continuity analysis of `Ξ` is needed. -/
lemma TΞ_bound (n : ℕ) (hn : 2 ≤ n) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc a 1, ‖TΞ n Qe ρ s‖ ≤ B := by
  obtain ⟨BG, hBG⟩ := volterra_base_G0_bound n ha0 ha1
  obtain ⟨BT, hBT⟩ := volterra_base_Theta0_bound n ha0 ha1
  have hball : ∀ s ∈ Set.Icc a 1,
      baseZ s ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖baseZ s - baseZ 1‖ ≤ 1
    linarith [hclose s hs]
  refine ⟨(1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * (BG + (1 - a) * max BT 0),
    fun s hs => ?_⟩
  have hbase := volterra_base_identity n hn ha0 ha1 s hs
  have hEq : baseΞ n s = baseG n s (baseZ s) - ∫ σ in s..1, baseΘ n s σ (baseZ σ) := by
    simp only [baseG, baseΘ, baseΞ, baseZ]
    rw [hbase]
    abel
  have hGbd : ‖baseG n s (baseZ s)‖ ≤ BG := hBG s hs _ (hball s hs)
  have hInt : ‖∫ σ in s..1, baseΘ n s σ (baseZ σ)‖ ≤ (1 - a) * max BT 0 := by
    have hΘbd : ∀ σ ∈ Set.uIoc s 1, ‖baseΘ n s σ (baseZ σ)‖ ≤ max BT 0 := by
      intro σ hσ
      rw [Set.uIoc_of_le hs.2] at hσ
      have hσIcc : σ ∈ Set.Icc a 1 := ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
      exact le_trans (hBT s hs σ hσIcc _ (hball σ hσIcc)) (le_max_left _ _)
    have h1 : ‖∫ σ in s..1, baseΘ n s σ (baseZ σ)‖ ≤ max BT 0 * |1 - s| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hΘbd
    have h2 : |1 - s| = 1 - s := abs_of_nonneg (by linarith [hs.2])
    rw [h2] at h1
    have h3 : max BT 0 * (1 - s) ≤ max BT 0 * (1 - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hs.1]) (le_max_right _ _)
    linarith [h1, h3]
  have hnorm : ‖baseG n s (baseZ s) - ∫ σ in s..1, baseΘ n s σ (baseZ σ)‖
      ≤ BG + (1 - a) * max BT 0 := by
    calc ‖baseG n s (baseZ s) - ∫ σ in s..1, baseΘ n s σ (baseZ σ)‖
        ≤ ‖baseG n s (baseZ s)‖ + ‖∫ σ in s..1, baseΘ n s σ (baseZ σ)‖ := norm_sub_le _ _
      _ ≤ BG + (1 - a) * max BT 0 := add_le_add hGbd hInt
  have hop : ‖Qe.symm (baseG n s (baseZ s) - ∫ σ in s..1, baseΘ n s σ (baseZ σ))‖
      ≤ ‖Qe.symm.toContinuousLinearMap‖ * (BG + (1 - a) * max BT 0) :=
    le_trans (ContinuousLinearMap.le_opNorm Qe.symm.toContinuousLinearMap _)
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hval : TΞ n Qe ρ s = (1 / ρ) • Qe.symm (baseG n s (baseZ s)
      - ∫ σ in s..1, baseΘ n s σ (baseZ σ)) := by
    simp only [TΞ, hEq]
  rw [hval]
  calc ‖(1 / ρ) • Qe.symm (baseG n s (baseZ s)
          - ∫ σ in s..1, baseΘ n s σ (baseZ σ))‖
      ≤ (1 / ρ) * (‖Qe.symm.toContinuousLinearMap‖ * (BG + (1 - a) * max BT 0)) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / ρ)]
        exact mul_le_mul_of_nonneg_left hop (by positivity)
    _ = (1 / ρ) * ‖Qe.symm.toContinuousLinearMap‖ * (BG + (1 - a) * max BT 0) := by ring


set_option linter.unusedSimpArgs false in
lemma contDiff_baseG_pair (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × VS => baseG n p.1 p.2) := by
  have hcoe : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · have h : (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ) 0)
          = fun p : ℝ × VS => p.2 0 := by
        funext p; exact baseG_apply_zero n p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
    · have h : (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ) 1)
          = fun p : ℝ × VS => p.2 1 := by
        funext p; exact baseG_apply_one n p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
    · have h : (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ) 2)
          = fun p : ℝ × VS => (-2:ℝ)^n * (n.factorial : ℝ) *
              ((p.1 * (p.2 0)^2)^n * p.2 2 + (p.1 * (p.2 1)^2)^n * p.2 3) := by
        funext p; exact baseG_apply_two n p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
    · have h : (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ) 3)
          = fun p : ℝ × VS => (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
              ((p.1 * (p.2 0)^2)^(n-1) * (-(p.2 0) * p.2 2)
                + (p.1 * (p.2 1)^2)^(n-1) * ((p.2 1) * p.2 3)) := by
        funext p; exact baseG_apply_three n p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
  have h2 : (fun p : ℝ × VS => ((baseG n p.1 p.2 : VS) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘
        (fun p : ℝ × VS => baseG n p.1 p.2) := rfl
  rw [h2] at hcoe
  have h4 : ContDiff ℝ (⊤ : ℕ∞) ((EuclideanSpace.equiv (Fin 4) ℝ).symm :
      (Fin 4 → ℝ) → VS) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := h4.comp hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) ∘
      (((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘
        (fun p : ℝ × VS => baseG n p.1 p.2)) = (fun p : ℝ × VS => baseG n p.1 p.2) := by
    funext p
    simp
  rw [hfun] at h5
  exact h5



set_option linter.unusedSimpArgs false in
lemma continuousAt_fderiv_baseG (n : ℕ) :
    ContinuousAt (fun p : ℝ × VS => fderiv ℝ (fun z : VS => baseG n p.1 z) p.2)
      (1, baseZ 1) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × VS => baseG n p.1 p.2) :=
    contDiff_baseG_pair n
  have hFd : Continuous (fderiv ℝ (fun p : ℝ × VS => baseG n p.1 p.2)) :=
    hF.continuous_fderiv (by simp)
  have hcomp : Continuous (fun L : (ℝ × VS) →L[ℝ] VS =>
      L.comp (ContinuousLinearMap.inr ℝ ℝ VS)) :=
    ((ContinuousLinearMap.compL ℝ VS (ℝ × VS) VS).continuous).clm_apply continuous_const
  have hid : (fun p : ℝ × VS => fderiv ℝ (fun z : VS => baseG n p.1 z) p.2) =
      (fun L : (ℝ × VS) →L[ℝ] VS => L.comp (ContinuousLinearMap.inr ℝ ℝ VS)) ∘
        (fderiv ℝ (fun p : ℝ × VS => baseG n p.1 p.2)) := by
    funext p
    simp only [Function.comp_apply]
    have h1 : HasFDerivAt (fun z : VS => (p.1, z)) (ContinuousLinearMap.inr ℝ ℝ VS) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have h2 : DifferentiableAt ℝ (fun q : ℝ × VS => baseG n q.1 q.2) (p.1, p.2) :=
      (ContDiff.differentiable hF (by simp)).differentiableAt
    have h3 := fderiv_fun_comp (x := p.2)
      (f := fun z : VS => (p.1, z)) (g := fun q : ℝ × VS => baseG n q.1 q.2)
      h2 h1.differentiableAt
    change fderiv ℝ (fun x : VS => baseG n (p.1, x).1 (p.1, x).2) p.2
      = (fderiv ℝ (fun p : ℝ × VS => baseG n p.1 p.2) p).comp
          (ContinuousLinearMap.inr ℝ ℝ VS)
    rw [h3, h1.fderiv]
  rw [hid]
  exact hcomp.continuousAt.comp hFd.continuousAt



set_option linter.unusedSimpArgs false in
lemma TG_cont_at_base (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ContinuousAt (fun p : ℝ × VS => fderiv ℝ (fun U : VS => TG n Qe ρ p.1 U) p.2)
      (1, 0) := by
  have key : ∀ (s : ℝ) (U : VS),
      fderiv ℝ (fun U' : VS => TG n Qe ρ s U') U
        = (Qe.symm : VS →L[ℝ] VS) ∘L
            (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) := by
    intro s U
    have h1 : HasFDerivAt (fun U' : VS => baseZ s + ρ • U') (ρ • (1 : VS →L[ℝ] VS)) U := by
      have hbase : HasFDerivAt (fun U' : VS => (ρ • (1 : VS →L[ℝ] VS)) U')
          (ρ • (1 : VS →L[ℝ] VS)) U := ContinuousLinearMap.hasFDerivAt _
      simpa using hbase.const_add (baseZ s)
    have h2 : HasFDerivAt (fun z : VS => baseG n s z)
        (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) (baseZ s + ρ • U) :=
      (baseG_differentiableAt n s (baseZ s + ρ • U)).hasFDerivAt
    have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n s (baseZ s + ρ • U)) := by
      have hbase : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
          ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n s (baseZ s + ρ • U)) :=
        ContinuousLinearMap.hasFDerivAt _
      simpa using hbase
    have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z))
        (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))) (baseZ s + ρ • U) :=
      HasFDerivAt.comp (baseZ s + ρ • U) h3 h2
    have hmain : HasFDerivAt
        (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z)) ∘
          (fun U' : VS => baseZ s + ρ • U'))
        ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) U :=
      HasFDerivAt.comp U hgb h1
    have hfin : fderiv ℝ (fun U' : VS => TG n Qe ρ s U') U
        = ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) := by
      rw [show (fun U' : VS => TG n Qe ρ s U')
          = (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z)) ∘
              (fun U' : VS => baseZ s + ρ • U')) from rfl]
      exact hmain.fderiv
    rw [hfin]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    have hd : (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) (ρ • v)
        = ρ • (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) v :=
      map_smul _ _ _
    rw [hd]
    have hms : (Qe.symm : VS →L[ℝ] VS) (ρ • (fderiv ℝ (fun z : VS => baseG n s z)
          (baseZ s + ρ • U)) v)
        = ρ • (Qe.symm : VS →L[ℝ] VS) ((fderiv ℝ (fun z : VS => baseG n s z)
          (baseZ s + ρ • U)) v) := map_smul _ _ _
    rw [hms, smul_smul, one_div, inv_mul_cancel₀ hρ, one_smul]
  have hmap : ContinuousAt (fun p : ℝ × VS => (p.1, baseZ p.1 + ρ • p.2)) (1, 0) := by
    refine ContinuousAt.prodMk continuousAt_fst ?_
    have hb : ContinuousAt (fun p : ℝ × VS => baseZ p.1) (1, 0) :=
      continuous_baseZ.continuousAt.comp continuousAt_fst
    exact hb.add (continuousAt_snd.const_smul ρ)
  have hbase' : ContinuousAt (fun q : ℝ × VS => fderiv ℝ (fun z : VS => baseG n q.1 z) q.2)
      (1, baseZ 1 + ρ • (0 : VS)) := by
    simpa using (continuousAt_fderiv_baseG n)
  have hcont1 : ContinuousAt (fun p : ℝ × VS => fderiv ℝ (fun z : VS => baseG n p.1 z)
      (baseZ p.1 + ρ • p.2)) (1, 0) := by
    have hc : ContinuousAt
        ((fun q : ℝ × VS => fderiv ℝ (fun z : VS => baseG n q.1 z) q.2) ∘
          (fun p : ℝ × VS => (p.1, baseZ p.1 + ρ • p.2))) (1, 0) :=
      ContinuousAt.comp hbase' hmap
    exact hc
  have hcont2 : Continuous (fun L : VS →L[ℝ] VS => (Qe.symm : VS →L[ℝ] VS) ∘L L) :=
    (((ContinuousLinearMap.compL ℝ VS VS VS) (Qe.symm : VS →L[ℝ] VS)).continuous)
  rw [show (fun p : ℝ × VS => fderiv ℝ (fun U : VS => TG n Qe ρ p.1 U) p.2)
      = fun p : ℝ × VS => (Qe.symm : VS →L[ℝ] VS) ∘L
          (fderiv ℝ (fun z : VS => baseG n p.1 z) (baseZ p.1 + ρ • p.2)) from
    funext (fun p => key p.1 p.2)]
  exact hcont2.continuousAt.comp hcont1



/-- Multi-parameter parametric `iteratedDeriv` with parameter `(σ, z)`. -/
lemma contDiff_parametric_iteratedDeriv_pair (k : ℕ) (G : (ℝ × VS) → ℝ → ℝ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => G q.1 q.2)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × VS) × ℝ => iteratedDeriv k (fun u : ℝ => G q.1 u) q.2) := by
  have h := contDiffOn_parametric_iteratedDeriv_prod (k := k) (F := G) isOpen_univ hG.contDiffOn
  simpa [contDiffOn_univ] using h

lemma baseTheta_apply_zero (n : ℕ) (s σ : ℝ) (z : VS) : baseΘ n s σ z 0 = -(z 2) := by
  simp [baseΘ, RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]

lemma baseTheta_apply_one (n : ℕ) (s σ : ℝ) (z : VS) : baseΘ n s σ z 1 = -(z 3) := by
  simp [baseΘ, RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]

set_option linter.unusedSimpArgs false in
lemma baseTheta_apply_two (n : ℕ) (s σ : ℝ) (z : VS) :
    baseΘ n s σ z 2 =
      (iteratedDeriv (n + 1) (fun u : ℝ => ((σ * (-(z 0)))^2 - (u * (-(z 0)))^2)^n) s) * (z 2)
      + (iteratedDeriv (n + 1) (fun u : ℝ => ((σ * (z 1))^2 - (u * (z 1))^2)^n) s) * (z 3) := by
  have hz : ∀ u : ℝ, deriv (fun _ : ℝ => (0:ℝ)) u = 0 := fun u => deriv_const u 0
  simp only [baseΘ, RyaboginVolterra.Theta, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
    hz, add_zero, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
    Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceFinMk,
    Function.comp_apply]

set_option linter.unusedSimpArgs false in
lemma baseTheta_apply_three (n : ℕ) (s σ : ℝ) (z : VS) :
    baseΘ n s σ z 3 =
      (iteratedDeriv n (fun u : ℝ =>
          ((σ * (-(z 0)))^2 - (u * (-(z 0)))^2)^(n - 1) * (-(z 0))) s) * (z 2)
      + (iteratedDeriv n (fun u : ℝ =>
          ((σ * (z 1))^2 - (u * (z 1))^2)^(n - 1) * (z 1)) s) * (z 3) := by
  have hz : ∀ u : ℝ, deriv (fun _ : ℝ => (0:ℝ)) u = 0 := fun u => deriv_const u 0
  simp only [baseΘ, RyaboginVolterra.Theta, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
    hz, add_zero, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
    Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceFinMk,
    Function.comp_apply]


set_option linter.unusedSimpArgs false in
lemma contDiff_baseTheta (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) := by
  have h2a : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.1.1 * (-(q.1.2 0)))^2 - (u * (-(q.1.2 0)))^2)^n) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (-(q.2 0)))^2 - (u * (-(q.2 0)))^2)^n) (by fun_prop)
  have h2b : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.1.1 * (q.1.2 1))^2 - (u * (q.1.2 1))^2)^n) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (q.2 1))^2 - (u * (q.2 1))^2)^n) (by fun_prop)
  have h3a : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.1.1 * (-(q.1.2 0)))^2 - (u * (-(q.1.2 0)))^2)^(n - 1) * (-(q.1.2 0))) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (-(q.2 0)))^2 - (u * (-(q.2 0)))^2)^(n - 1) * (-(q.2 0)))
      (by fun_prop)
  have h3b : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.1.1 * (q.1.2 1))^2 - (u * (q.1.2 1))^2)^(n - 1) * (q.1.2 1)) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (q.2 1))^2 - (u * (q.2 1))^2)^(n - 1) * (q.2 1))
      (by fun_prop)
  let Φ : (ℝ × VS) × ℝ → VS := fun q => RyaboginVolterra.mk4 (-(q.1.2 2)) (-(q.1.2 3))
      (iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.1.1 * (-(q.1.2 0)))^2 - (u * (-(q.1.2 0)))^2)^n) q.2 * (q.1.2 2)
        + iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.1.1 * (q.1.2 1))^2 - (u * (q.1.2 1))^2)^n) q.2 * (q.1.2 3))
      (iteratedDeriv n (fun u : ℝ =>
          ((q.1.1 * (-(q.1.2 0)))^2 - (u * (-(q.1.2 0)))^2)^(n - 1) * (-(q.1.2 0))) q.2 * (q.1.2 2)
        + iteratedDeriv n (fun u : ℝ =>
          ((q.1.1 * (q.1.2 1))^2 - (u * (q.1.2 1))^2)^(n - 1) * (q.1.2 1)) q.2 * (q.1.2 3))
  have heq : (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) = Φ := by
    funext q
    ext i
    fin_cases i <;>
      · simp only [Φ, baseTheta_apply_zero, baseTheta_apply_one, baseTheta_apply_two,
          baseTheta_apply_three, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
          Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          Fin.isValue, Fin.reduceFinMk, Function.comp_apply]
  have hcoe : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => ((Φ q : VS) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;>
      · simp only [Φ, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
          Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
          Fin.reduceFinMk, Function.comp_apply]
        first
          | fun_prop
          | exact ContDiff.add (ContDiff.mul h2a (by fun_prop)) (ContDiff.mul h2b (by fun_prop))
          | exact ContDiff.add (ContDiff.mul h3a (by fun_prop)) (ContDiff.mul h3b (by fun_prop))
  have h4 : ContDiff ℝ (⊤ : ℕ∞)
      ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := ContDiff.comp h4 hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) ∘
      (fun q : (ℝ × VS) × ℝ => ((Φ q : VS) : Fin 4 → ℝ)) = Φ := by
    funext q
    simp
  rw [hfun] at h5
  rw [heq]
  exact h5



/-- The derivative of `baseΘ` in its third (`Z`) variable is bounded on
`[a,1]² × closedBall (baseState 1) 1`. -/
lemma exists_bound_fderiv_baseTheta (n : ℕ) {a : ℝ} (_ha : 0 < a) (_ha1 : a ≤ 1) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      ∀ z ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1,
      ‖fderiv ℝ (fun w : VS => baseΘ n s σ w) z‖ ≤ M := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
    contDiff_baseTheta n
  have hFd : Continuous (fderiv ℝ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2)) :=
    ContDiff.continuous_fderiv hF (by simp)
  let K' : VS →L[ℝ] ((ℝ × VS) × ℝ) :=
    (ContinuousLinearMap.inl ℝ (ℝ × VS) ℝ).comp (ContinuousLinearMap.inr ℝ ℝ VS)
  have hK : Continuous (fun L : ((ℝ × VS) × ℝ) →L[ℝ] VS => L.comp K') :=
    ((ContinuousLinearMap.apply ℝ (VS →L[ℝ] VS) K').continuous).comp
      ((ContinuousLinearMap.compL ℝ VS ((ℝ × VS) × ℝ) VS).continuous)
  have key : ∀ (s σ : ℝ) (z : VS),
      fderiv ℝ (fun w : VS => baseΘ n s σ w) z
        = (fderiv ℝ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2)
              ((σ, z), s)).comp K' := by
    intro s σ z
    have hinj' : HasFDerivAt ((fun q : ℝ × VS => (q, s)) ∘ (fun w : VS => (σ, w))) K' z :=
      HasFDerivAt.comp z (hasFDerivAt_prodMk_left (σ, z) s) (hasFDerivAt_prodMk_right σ z)
    have hinj : HasFDerivAt (fun w : VS => ((σ, w), s)) K' z := hinj'
    have hd : DifferentiableAt ℝ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2)
        ((σ, z), s) :=
      (ContDiff.differentiable hF (by simp)).differentiableAt
    have h3 := fderiv_fun_comp (x := z) (f := fun w : VS => ((σ, w), s))
      (g := fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) hd hinj.differentiableAt
    change fderiv ℝ (fun x : VS =>
      (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ((σ, x), s)) z = _
    rw [h3, hinj.fderiv]
  have hcont : Continuous (fun p : ℝ × ℝ × VS =>
      fderiv ℝ (fun w : VS => baseΘ n p.1 p.2.1 w) p.2.2) := by
    have hcomp : Continuous (fun p : ℝ × ℝ × VS =>
        (fderiv ℝ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ((p.2.1, p.2.2), p.1)).comp
          K') :=
      hK.comp (hFd.comp (by fun_prop))
    rw [show (fun p : ℝ × ℝ × VS => fderiv ℝ (fun w : VS => baseΘ n p.1 p.2.1 w) p.2.2)
        = fun p : ℝ × ℝ × VS =>
            (fderiv ℝ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2)
              ((p.2.1, p.2.2), p.1)).comp K' from
      funext (fun p => key p.1 p.2.1 p.2.2)]
    exact hcomp
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc.prod
    (isCompact_closedBall _ _))).exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨M, fun s hs σ hσ z hz => hM (s, σ, z) ⟨hs, hσ, hz⟩⟩





/-- Lipschitz constant for `U ↦ TΘ n Qe ρ s σ U` on the unit ball. -/
lemma lipschitzOnWith_TΘ (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) :
    ∃ L : NNReal, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      LipschitzOnWith L (fun U : VS => TΘ n Qe ρ s σ U) (Metric.closedBall (0 : VS) 1) := by
  obtain ⟨M, hM⟩ := exists_bound_fderiv_baseTheta n ha0 ha1
  have hL : 0 ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0 :=
    mul_nonneg (norm_nonneg _) (le_max_right _ _)
  refine ⟨⟨‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0, hL⟩, fun s hs σ hσ => ?_⟩
  have key : ∀ U : VS,
      fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U
        = (Qe.symm : VS →L[ℝ] VS) ∘L
            (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) := by
    intro U
    have h1 : HasFDerivAt (fun U' : VS => baseZ σ + ρ • U') (ρ • (1 : VS →L[ℝ] VS)) U := by
      have hbase : HasFDerivAt (fun U' : VS => (ρ • (1 : VS →L[ℝ] VS)) U')
          (ρ • (1 : VS →L[ℝ] VS)) U := ContinuousLinearMap.hasFDerivAt _
      simpa using hbase.const_add (baseZ σ)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
      contDiff_baseTheta n
    have hzd : DifferentiableAt ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U) := by
      have h1' : DifferentiableAt ℝ (fun w : VS => (σ, w)) (baseZ σ + ρ • U) := by fun_prop
      have h2' : DifferentiableAt ℝ (fun q : ℝ × VS => (q, s)) (σ, baseZ σ + ρ • U) := by fun_prop
      have hinj : DifferentiableAt ℝ ((fun q : ℝ × VS => (q, s)) ∘ (fun w : VS => (σ, w)))
          (baseZ σ + ρ • U) :=
        DifferentiableAt.comp (baseZ σ + ρ • U) h2' h1'
      have hc : DifferentiableAt ℝ
          ((fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ∘ (fun w : VS => ((σ, w), s)))
          (baseZ σ + ρ • U) :=
        DifferentiableAt.comp (baseZ σ + ρ • U)
          ((ContDiff.differentiable hF (by simp)).differentiableAt) hinj
      exact hc
    have h2 : HasFDerivAt (fun w : VS => baseΘ n s σ w)
        (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) (baseZ σ + ρ • U) :=
      hzd.hasFDerivAt
    have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseΘ n s σ (baseZ σ + ρ • U)) := by
      have hbase : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
          ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseΘ n s σ (baseZ σ + ρ • U)) :=
        ContinuousLinearMap.hasFDerivAt _
      simpa using hbase
    have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z))
        (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)))
        (baseZ σ + ρ • U) :=
      HasFDerivAt.comp (baseZ σ + ρ • U) h3 h2
    have hmain : HasFDerivAt
        (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
          (fun U' : VS => baseZ σ + ρ • U'))
        ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) U :=
      HasFDerivAt.comp U hgb h1
    have hfin : fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U
        = ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) := by
      rw [show (fun U' : VS => TΘ n Qe ρ s σ U')
          = (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
              (fun U' : VS => baseZ σ + ρ • U')) from rfl]
      exact hmain.fderiv
    rw [hfin]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    have hd : (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) (ρ • v)
        = ρ • (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) v :=
      map_smul _ _ _
    rw [hd]
    have hms : (Qe.symm : VS →L[ℝ] VS) (ρ • (fderiv ℝ (fun w : VS => baseΘ n s σ w)
          (baseZ σ + ρ • U)) v)
        = ρ • (Qe.symm : VS →L[ℝ] VS) ((fderiv ℝ (fun w : VS => baseΘ n s σ w)
          (baseZ σ + ρ • U)) v) := map_smul _ _ _
    rw [hms, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hρ0), one_smul]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hdiff : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      DifferentiableAt ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U := by
    intro U _
    rw [show (fun U' : VS => TΘ n Qe ρ s σ U')
        = ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
            (fun U' : VS => baseZ σ + ρ • U') from rfl]
    refine DifferentiableAt.comp U ?_ (by fun_prop)
    refine DifferentiableAt.comp (baseZ σ + ρ • U) (by fun_prop) ?_
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
      contDiff_baseTheta n
    have h1' : DifferentiableAt ℝ (fun w : VS => (σ, w)) (baseZ σ + ρ • U) := by fun_prop
    have h2' : DifferentiableAt ℝ (fun q : ℝ × VS => (q, s)) (σ, baseZ σ + ρ • U) := by fun_prop
    have hinj : DifferentiableAt ℝ ((fun q : ℝ × VS => (q, s)) ∘ (fun w : VS => (σ, w)))
        (baseZ σ + ρ • U) :=
      DifferentiableAt.comp (baseZ σ + ρ • U) h2' h1'
    have hc : DifferentiableAt ℝ
        ((fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ∘ (fun w : VS => ((σ, w), s)))
        (baseZ σ + ρ • U) :=
      DifferentiableAt.comp (baseZ σ + ρ • U)
        ((ContDiff.differentiable hF (by simp)).differentiableAt) hinj
    exact hc
  have hC : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U‖ ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0 := by
    intro U hU
    rw [key U]
    have hzb : baseZ σ + ρ • U ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 :=
      base_close_ball hρ0 hρ1 hclose hσ hU
    have hb : ‖fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)‖ ≤ max M 0 :=
      le_trans (hM s hs σ hσ _ hzb) (le_max_left _ _)
    exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  exact dist_image_sub_le_of_norm_fderiv_le hdiff hC (convex_closedBall _ _) hx hy


/-- Lipschitz constant for `U ↦ TΘ n Qe ρ s σ U` on the unit ball, **uniformly in
`ρ ∈ (0,1/2]`** (the constant does not depend on `ρ`). -/
lemma lipschitzOnWith_TΘ_uniform (n : ℕ) (Qe : VS ≃L[ℝ] VS)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) :
    ∃ L : NNReal, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
        LipschitzOnWith L (fun U : VS => TΘ n Qe ρ s σ U) (Metric.closedBall (0 : VS) 1) := by
  obtain ⟨M, hM⟩ := exists_bound_fderiv_baseTheta n ha0 ha1
  have hL : 0 ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0 :=
    mul_nonneg (norm_nonneg _) (le_max_right _ _)
  refine ⟨⟨‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0, hL⟩, fun ρ hρ0 hρ1 s hs σ hσ => ?_⟩
  have key : ∀ U : VS,
      fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U
        = (Qe.symm : VS →L[ℝ] VS) ∘L
            (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) := by
    intro U
    have h1 : HasFDerivAt (fun U' : VS => baseZ σ + ρ • U') (ρ • (1 : VS →L[ℝ] VS)) U := by
      have hbase : HasFDerivAt (fun U' : VS => (ρ • (1 : VS →L[ℝ] VS)) U')
          (ρ • (1 : VS →L[ℝ] VS)) U := ContinuousLinearMap.hasFDerivAt _
      simpa using hbase.const_add (baseZ σ)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
      contDiff_baseTheta n
    have hzd : DifferentiableAt ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U) := by
      have h1' : DifferentiableAt ℝ (fun w : VS => (σ, w)) (baseZ σ + ρ • U) := by fun_prop
      have h2' : DifferentiableAt ℝ (fun q : ℝ × VS => (q, s)) (σ, baseZ σ + ρ • U) := by fun_prop
      have hinj : DifferentiableAt ℝ ((fun q : ℝ × VS => (q, s)) ∘ (fun w : VS => (σ, w)))
          (baseZ σ + ρ • U) :=
        DifferentiableAt.comp (baseZ σ + ρ • U) h2' h1'
      have hc : DifferentiableAt ℝ
          ((fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ∘ (fun w : VS => ((σ, w), s)))
          (baseZ σ + ρ • U) :=
        DifferentiableAt.comp (baseZ σ + ρ • U)
          ((ContDiff.differentiable hF (by simp)).differentiableAt) hinj
      exact hc
    have h2 : HasFDerivAt (fun w : VS => baseΘ n s σ w)
        (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) (baseZ σ + ρ • U) :=
      hzd.hasFDerivAt
    have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseΘ n s σ (baseZ σ + ρ • U)) := by
      have hbase : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
          ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseΘ n s σ (baseZ σ + ρ • U)) :=
        ContinuousLinearMap.hasFDerivAt _
      simpa using hbase
    have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z))
        (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)))
        (baseZ σ + ρ • U) :=
      HasFDerivAt.comp (baseZ σ + ρ • U) h3 h2
    have hmain : HasFDerivAt
        (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
          (fun U' : VS => baseZ σ + ρ • U'))
        ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) U :=
      HasFDerivAt.comp U hgb h1
    have hfin : fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U
        = ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) := by
      rw [show (fun U' : VS => TΘ n Qe ρ s σ U')
          = (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
              (fun U' : VS => baseZ σ + ρ • U')) from rfl]
      exact hmain.fderiv
    rw [hfin]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    have hd : (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) (ρ • v)
        = ρ • (fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)) v :=
      map_smul _ _ _
    rw [hd]
    have hms : (Qe.symm : VS →L[ℝ] VS) (ρ • (fderiv ℝ (fun w : VS => baseΘ n s σ w)
          (baseZ σ + ρ • U)) v)
        = ρ • (Qe.symm : VS →L[ℝ] VS) ((fderiv ℝ (fun w : VS => baseΘ n s σ w)
          (baseZ σ + ρ • U)) v) := map_smul _ _ _
    rw [hms, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hρ0), one_smul]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hdiff : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      DifferentiableAt ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U := by
    intro U _
    rw [show (fun U' : VS => TΘ n Qe ρ s σ U')
        = ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseΘ n s σ z)) ∘
            (fun U' : VS => baseZ σ + ρ • U') from rfl]
    refine DifferentiableAt.comp U ?_ (by fun_prop)
    refine DifferentiableAt.comp (baseZ σ + ρ • U) (by fun_prop) ?_
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
      contDiff_baseTheta n
    have h1' : DifferentiableAt ℝ (fun w : VS => (σ, w)) (baseZ σ + ρ • U) := by fun_prop
    have h2' : DifferentiableAt ℝ (fun q : ℝ × VS => (q, s)) (σ, baseZ σ + ρ • U) := by fun_prop
    have hinj : DifferentiableAt ℝ ((fun q : ℝ × VS => (q, s)) ∘ (fun w : VS => (σ, w)))
        (baseZ σ + ρ • U) :=
      DifferentiableAt.comp (baseZ σ + ρ • U) h2' h1'
    have hc : DifferentiableAt ℝ
        ((fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ∘ (fun w : VS => ((σ, w), s)))
        (baseZ σ + ρ • U) :=
      DifferentiableAt.comp (baseZ σ + ρ • U)
        ((ContDiff.differentiable hF (by simp)).differentiableAt) hinj
    exact hc
  have hC : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖fderiv ℝ (fun U' : VS => TΘ n Qe ρ s σ U') U‖ ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max M 0 := by
    intro U hU
    rw [key U]
    have hzb : baseZ σ + ρ • U ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 :=
      base_close_ball hρ0 hρ1 hclose hσ hU
    have hb : ‖fderiv ℝ (fun w : VS => baseΘ n s σ w) (baseZ σ + ρ • U)‖ ≤ max M 0 :=
      le_trans (hM s hs σ hσ _ hzb) (le_max_left _ _)
    exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  exact dist_image_sub_le_of_norm_fderiv_le hdiff hC (convex_closedBall _ _) hx hy





/-- Lipschitz constant for `U ↦ U - TG n Qe ρ s U` on the unit ball. -/
lemma lipschitzOnWith_TG (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2)
    {η : ℝ} (hη : ∀ s ∈ Set.Icc a 1,
      ∀ z ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1,
      ‖Qe.toContinuousLinearMap - fderiv ℝ (fun w : VS => baseG n s w) z‖ ≤ η) :
    ∃ K : NNReal, ∀ s ∈ Set.Icc a 1,
      LipschitzOnWith K (fun U : VS => U - TG n Qe ρ s U) (Metric.closedBall (0 : VS) 1) := by
  have hKnn : 0 ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max η 0 :=
    mul_nonneg (norm_nonneg _) (le_max_right _ _)
  refine ⟨⟨‖(Qe.symm : VS →L[ℝ] VS)‖ * max η 0, hKnn⟩, fun s hs => ?_⟩
  have hT : ∀ U : VS, HasFDerivAt (fun U' : VS => TG n Qe ρ s U')
      ((Qe.symm : VS →L[ℝ] VS) ∘L
        (fderiv ℝ (fun w : VS => baseG n s w) (baseZ s + ρ • U))) U := by
    intro U
    have h1 : HasFDerivAt (fun U' : VS => baseZ s + ρ • U') (ρ • (1 : VS →L[ℝ] VS)) U := by
      have hb : HasFDerivAt (fun U' : VS => (ρ • (1 : VS →L[ℝ] VS)) U')
          (ρ • (1 : VS →L[ℝ] VS)) U := ContinuousLinearMap.hasFDerivAt _
      simpa using hb.const_add (baseZ s)
    have h2 : HasFDerivAt (fun w : VS => baseG n s w)
        (fderiv ℝ (fun w : VS => baseG n s w) (baseZ s + ρ • U)) (baseZ s + ρ • U) :=
      (baseG_differentiableAt n s (baseZ s + ρ • U)).hasFDerivAt
    have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n s (baseZ s + ρ • U)) := by
      have hb : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
          ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (baseG n s (baseZ s + ρ • U)) :=
        ContinuousLinearMap.hasFDerivAt _
      simpa using hb
    have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z))
        (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))) (baseZ s + ρ • U) :=
      HasFDerivAt.comp (baseZ s + ρ • U) h3 h2
    have hmain : HasFDerivAt
        (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z)) ∘
          (fun U' : VS => baseZ s + ρ • U'))
        ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS))) U :=
      HasFDerivAt.comp U hgb h1
    have heq : ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp
          (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))).comp
            (ρ • (1 : VS →L[ℝ] VS)))
        = ((Qe.symm : VS →L[ℝ] VS) ∘L
            (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U))) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      have hd : (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) (ρ • v)
          = ρ • (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s + ρ • U)) v := map_smul _ _ _
      rw [hd]
      have hms : (Qe.symm : VS →L[ℝ] VS) (ρ • (fderiv ℝ (fun z : VS => baseG n s z)
            (baseZ s + ρ • U)) v)
          = ρ • (Qe.symm : VS →L[ℝ] VS) ((fderiv ℝ (fun z : VS => baseG n s z)
            (baseZ s + ρ • U)) v) := map_smul _ _ _
      rw [hms, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hρ0), one_smul]
    have hfun : (fun U' : VS => TG n Qe ρ s U') =
        (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => baseG n s z)) ∘
          (fun U' : VS => baseZ s + ρ • U')) := rfl
    rw [← hfun, heq] at hmain
    exact hmain
  have key : ∀ U : VS,
      fderiv ℝ (fun U' : VS => U' - TG n Qe ρ s U') U
        = (Qe.symm : VS →L[ℝ] VS) ∘L
            (Qe.toContinuousLinearMap - fderiv ℝ (fun w : VS => baseG n s w) (baseZ s + ρ • U)) := by
    intro U
    change fderiv ℝ (id - fun U' : VS => TG n Qe ρ s U') U = _
    rw [((hasFDerivAt_id U).sub (hT U)).fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    rw [map_sub]
    congr 1
    exact (ContinuousLinearEquiv.symm_apply_apply Qe v).symm
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hdiff : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      DifferentiableAt ℝ (fun U' : VS => U' - TG n Qe ρ s U') U := by
    intro U _
    exact (hasFDerivAt_id U).sub (hT U) |>.differentiableAt
  have hC : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖fderiv ℝ (fun U' : VS => U' - TG n Qe ρ s U') U‖
        ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ * max η 0 := by
    intro U hU
    rw [key U]
    have hzb : baseZ s + ρ • U ∈ Metric.closedBall (RyaboginVolterra.baseState 1) 1 :=
      base_close_ball hρ0 hρ1 hclose hs hU
    have hb : ‖Qe.toContinuousLinearMap - fderiv ℝ (fun w : VS => baseG n s w)
        (baseZ s + ρ • U)‖ ≤ max η 0 := le_trans (hη s hs _ hzb) (le_max_left _ _)
    exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  exact dist_image_sub_le_of_norm_fderiv_le hdiff hC (convex_closedBall _ _) hx hy



/-! ## Perturbed Volterra data: smoothness and component formulas -/

lemma contDiff_deriv_of_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (deriv h) := by
  have h1 := hh.iterate_deriv 1
  simpa [Function.iterate_one] using h1

abbrev VS1 := RyaboginVolterra.State


set_option linter.unusedSimpArgs false in
lemma G_apply_two (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h s z 2 =
      (-2:ℝ)^n * (n.factorial : ℝ) *
        (((RyaboginVolterra.line h s (-(z 0))) * (RyaboginVolterra.lineSlope h s (-(z 0))))^n * z 2
        + ((RyaboginVolterra.line h s (z 1)) * (RyaboginVolterra.lineSlope h s (z 1)))^n * z 3) := by
  simp only [RyaboginVolterra.G, RyaboginVolterra.endpointC, RyaboginVolterra.mk4_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.isValue, Function.comp_apply]
  ring

set_option linter.unusedSimpArgs false in
lemma G_apply_three (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h s z 3 =
      (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
        (((RyaboginVolterra.line h s (-(z 0))) * (RyaboginVolterra.lineSlope h s (-(z 0))))^(n-1)
            * (RyaboginVolterra.lineSlope h s (-(z 0))) * z 2
        + ((RyaboginVolterra.line h s (z 1)) * (RyaboginVolterra.lineSlope h s (z 1)))^(n-1)
            * (RyaboginVolterra.lineSlope h s (z 1)) * z 3) := by
  simp only [RyaboginVolterra.G, RyaboginVolterra.endpointD, RyaboginVolterra.mk4_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.isValue, Function.comp_apply]
  ring

lemma G_apply_zero (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h s z 0 = z 0 := by
  simp [RyaboginVolterra.G, RyaboginVolterra.mk4_apply]

lemma G_apply_one (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h s z 1 = z 1 := by
  simp [RyaboginVolterra.G, RyaboginVolterra.mk4_apply]



set_option maxHeartbeats 400000 in
lemma contDiff_G_pair (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × VS1 => RyaboginVolterra.G n h p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (deriv h) := contDiff_deriv_of_contDiff hh
  have hcoe : ContDiff ℝ ∞
      (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · have h : (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ) 0)
          = fun p : ℝ × VS1 => p.2 0 := by
        funext p; exact G_apply_zero n h p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
    · have h : (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ) 1)
          = fun p : ℝ × VS1 => p.2 1 := by
        funext p; exact G_apply_one n h p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]; fun_prop
    · have h : (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ) 2)
          = fun p : ℝ × VS1 => (-2:ℝ)^n * (n.factorial : ℝ) *
              (((RyaboginVolterra.line h p.1 (-(p.2 0))) *
                  (RyaboginVolterra.lineSlope h p.1 (-(p.2 0))))^n * p.2 2
                + ((RyaboginVolterra.line h p.1 (p.2 1)) *
                  (RyaboginVolterra.lineSlope h p.1 (p.2 1)))^n * p.2 3) := by
        funext p; exact G_apply_two n h p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope]
      fun_prop
    · have h : (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ) 3)
          = fun p : ℝ × VS1 => (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
              (((RyaboginVolterra.line h p.1 (-(p.2 0))) *
                  (RyaboginVolterra.lineSlope h p.1 (-(p.2 0))))^(n-1)
                  * (RyaboginVolterra.lineSlope h p.1 (-(p.2 0))) * p.2 2
                + ((RyaboginVolterra.line h p.1 (p.2 1)) *
                  (RyaboginVolterra.lineSlope h p.1 (p.2 1)))^(n-1)
                  * (RyaboginVolterra.lineSlope h p.1 (p.2 1)) * p.2 3) := by
        funext p; exact G_apply_three n h p.1 p.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [h]
      simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope]
      fun_prop
  have h2 : (fun p : ℝ × VS1 => ((RyaboginVolterra.G n h p.1 p.2 : VS1) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS1 → (Fin 4 → ℝ)) ∘
        (fun p : ℝ × VS1 => RyaboginVolterra.G n h p.1 p.2) := rfl
  rw [h2] at hcoe
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := h4.comp hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) ∘
      (((EuclideanSpace.equiv (Fin 4) ℝ) : VS1 → (Fin 4 → ℝ)) ∘
        (fun p : ℝ × VS1 => RyaboginVolterra.G n h p.1 p.2)) =
      (fun p : ℝ × VS1 => RyaboginVolterra.G n h p.1 p.2) := by
    funext p; simp
  rw [hfun] at h5
  exact h5



lemma Theta_apply_zero (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : VS1) :
    RyaboginVolterra.Theta n h s σ z 0 = -(z 2) := by
  simp [RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]

lemma Theta_apply_one (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : VS1) :
    RyaboginVolterra.Theta n h s σ z 1 = -(z 3) := by
  simp [RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]

lemma Theta_apply_two (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : VS1) :
    RyaboginVolterra.Theta n h s σ z 2 =
      (iteratedDeriv (n + 1) (fun u : ℝ =>
        (RyaboginVolterra.line h σ (-(z 0))^2 - RyaboginVolterra.line h u (-(z 0))^2)^n) s) * (z 2)
      + (iteratedDeriv (n + 1) (fun u : ℝ =>
        (RyaboginVolterra.line h σ (z 1)^2 - RyaboginVolterra.line h u (z 1)^2)^n) s) * (z 3) := by
  simp [RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]

lemma Theta_apply_three (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : VS1) :
    RyaboginVolterra.Theta n h s σ z 3 =
      (iteratedDeriv n (fun u : ℝ =>
        (RyaboginVolterra.line h σ (-(z 0))^2 - RyaboginVolterra.line h u (-(z 0))^2)^(n - 1)
          * RyaboginVolterra.lineSlope h u (-(z 0))) s) * (z 2)
      + (iteratedDeriv n (fun u : ℝ =>
        (RyaboginVolterra.line h σ (z 1)^2 - RyaboginVolterra.line h u (z 1)^2)^(n - 1)
          * RyaboginVolterra.lineSlope h u (z 1)) s) * (z 3) := by
  simp [RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply]



set_option maxHeartbeats 800000 in
lemma contDiff_Theta (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ => RyaboginVolterra.Theta n h q.2 q.1.1 q.1.2) := by
  have hd : ContDiff ℝ ∞ (deriv h) := contDiff_deriv_of_contDiff hh
  have h2a : ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.1.1 * (-(q.1.2 0)) + h q.1.1)^2 - (u * (-(q.1.2 0)) + h u)^2)^n) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (-(q.2 0)) + h q.1)^2 - (u * (-(q.2 0)) + h u)^2)^n) (by fun_prop)
  have h2b : ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.1.1 * (q.1.2 1) + h q.1.1)^2 - (u * (q.1.2 1) + h u)^2)^n) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (q.2 1) + h q.1)^2 - (u * (q.2 1) + h u)^2)^n) (by fun_prop)
  have h3a : ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.1.1 * (-(q.1.2 0)) + h q.1.1)^2 - (u * (-(q.1.2 0)) + h u)^2)^(n - 1)
          * (-(q.1.2 0) + deriv h u)) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (-(q.2 0)) + h q.1)^2 - (u * (-(q.2 0)) + h u)^2)^(n - 1)
        * (-(q.2 0) + deriv h u)) (by fun_prop)
  have h3b : ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.1.1 * (q.1.2 1) + h q.1.1)^2 - (u * (q.1.2 1) + h u)^2)^(n - 1)
          * ((q.1.2 1) + deriv h u)) q.2) :=
    contDiff_parametric_iteratedDeriv_pair _
      (fun q u => ((q.1 * (q.2 1) + h q.1)^2 - (u * (q.2 1) + h u)^2)^(n - 1)
        * ((q.2 1) + deriv h u)) (by fun_prop)
  let Φ : (ℝ × VS1) × ℝ → VS1 := fun q => RyaboginVolterra.mk4 (-(q.1.2 2)) (-(q.1.2 3))
      (iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.1.1 * (-(q.1.2 0)) + h q.1.1)^2 - (u * (-(q.1.2 0)) + h u)^2)^n) q.2 * (q.1.2 2)
        + iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.1.1 * (q.1.2 1) + h q.1.1)^2 - (u * (q.1.2 1) + h u)^2)^n) q.2 * (q.1.2 3))
      (iteratedDeriv n (fun u : ℝ =>
          ((q.1.1 * (-(q.1.2 0)) + h q.1.1)^2 - (u * (-(q.1.2 0)) + h u)^2)^(n - 1)
            * (-(q.1.2 0) + deriv h u)) q.2 * (q.1.2 2)
        + iteratedDeriv n (fun u : ℝ =>
          ((q.1.1 * (q.1.2 1) + h q.1.1)^2 - (u * (q.1.2 1) + h u)^2)^(n - 1)
            * ((q.1.2 1) + deriv h u)) q.2 * (q.1.2 3))
  have heq : (fun q : (ℝ × VS1) × ℝ => RyaboginVolterra.Theta n h q.2 q.1.1 q.1.2) = Φ := by
    funext q
    ext i
    fin_cases i <;>
      · simp only [Φ, Theta_apply_zero, Theta_apply_one, Theta_apply_two, Theta_apply_three,
          RyaboginVolterra.mk4_apply, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
          Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          Fin.isValue, Fin.reduceFinMk, Function.comp_apply]
  have hcoe : ContDiff ℝ ∞ (fun q : (ℝ × VS1) × ℝ => ((Φ q : VS1) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;>
      · simp only [Φ, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.vecHead,
          Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
          Fin.reduceFinMk, Function.comp_apply]
        first
          | fun_prop
          | exact ContDiff.add (ContDiff.mul h2a (by fun_prop)) (ContDiff.mul h2b (by fun_prop))
          | exact ContDiff.add (ContDiff.mul h3a (by fun_prop)) (ContDiff.mul h3b (by fun_prop))
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := ContDiff.comp h4 hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) ∘
      (fun q : (ℝ × VS1) × ℝ => ((Φ q : VS1) : Fin 4 → ℝ)) = Φ := by
    funext q; simp
  rw [hfun] at h5
  rw [heq]
  exact h5



/-- Smoothness of the parametric `iteratedDeriv` with the parameter in the second slot. -/
lemma contDiff_iteratedDeriv_param_swap (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (fun u : ℝ => F p.2 u) p.1) := by
  have h1 := contDiffOn_parametric_iteratedDeriv_prod (k := k) (F := F) (U := Set.univ)
    isOpen_univ hF.contDiffOn
  have h3 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => iteratedDeriv k (fun u : ℝ => F q.1 u) q.2) :=
    contDiffOn_univ.mp h1
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) := by fun_prop
  have hswap : (fun p : ℝ × ℝ => iteratedDeriv k (fun u : ℝ => F p.2 u) p.1)
      = (fun q : ℝ × ℝ => iteratedDeriv k (fun u : ℝ => F q.1 u) q.2) ∘
          (fun p : ℝ × ℝ => (p.2, p.1)) := by
    funext p; rfl
  rw [hswap]
  exact ContDiff.comp h3 h2

/-- Smoothness of `mk4` built from smooth scalar functions. -/
lemma contDiff_mk4 {a b c d : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) :
    ContDiff ℝ ∞ (fun s : ℝ => RyaboginVolterra.mk4 (a s) (b s) (c s) (d s)) := by
  have hvec : ContDiff ℝ ∞ (fun s : ℝ => ![a s, b s, c s, d s]) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;>
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three]
        first | exact ha | exact hb | exact hc | exact hd
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := ContDiff.comp h4 hvec
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) ∘
      (fun s : ℝ => ![a s, b s, c s, d s]) =
      (fun s : ℝ => RyaboginVolterra.mk4 (a s) (b s) (c s) (d s)) := by
    funext s; rfl
  rwa [hfun] at h5

lemma contDiff_Xi1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun s : ℝ => RyaboginVolterra.Xi1 n h s) := by
  unfold RyaboginVolterra.Xi1
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving ?_ ?_ ?_
  · exact contDiff_iteratedDeriv_param_swap (n + 1)
      (F := fun t u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ n) (by fun_prop)
  · exact contDiff_const
  · exact contDiff_const

lemma contDiff_Xi2 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun s : ℝ => RyaboginVolterra.Xi2 n h s) := by
  unfold RyaboginVolterra.Xi2
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving ?_ ?_ ?_
  · unfold RyaboginVolterra.lineSlope
    exact contDiff_iteratedDeriv_param_swap n
      (F := fun t u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u))
      (by fun_prop)
  · exact contDiff_const
  · exact contDiff_const

lemma contDiff_Xi (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun s : ℝ => RyaboginVolterra.Xi n h s) := by
  have hfun : (fun s : ℝ => RyaboginVolterra.Xi n h s) = fun s : ℝ =>
      RyaboginVolterra.mk4 (profileX 1) (profileX 1)
        (- RyaboginVolterra.Xi1 n h s
          + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s)
        (- RyaboginVolterra.Xi2 n h s) := by
    funext s; rfl
  rw [hfun]
  refine contDiff_mk4 contDiff_const contDiff_const ?_ ?_
  · refine (contDiff_Xi1 n hh).neg.add ?_
    have h := (contDiff_momentRHS n).iterate_deriv (n + 1)
    simpa [iteratedDeriv_eq_iterate] using h
  · exact (contDiff_Xi2 n hh).neg






/-- The `G`-data with the values `h s` and `h' s` as explicit parameters. -/
noncomputable def Gw (n : ℕ) (s a b : ℝ) (z : VS1) : VS1 :=
  RyaboginVolterra.mk4 (z 0) (z 1)
    ((-2:ℝ)^n * (n.factorial : ℝ) *
      (((s * (-(z 0)) + a) * (-(z 0) + b))^n * z 2 + ((s * (z 1) + a) * (z 1 + b))^n * z 3))
    ((-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
      (((s * (-(z 0)) + a) * (-(z 0) + b))^(n-1) * (-(z 0) + b) * z 2
        + ((s * (z 1) + a) * (z 1 + b))^(n-1) * (z 1 + b) * z 3))

set_option linter.unusedSimpArgs false in
lemma Gw_apply_two (n : ℕ) (s a b : ℝ) (z : VS1) :
    Gw n s a b z 2 = (-2:ℝ)^n * (n.factorial : ℝ) *
      (((s*(-(z 0)) + a) * (-(z 0) + b))^n * z 2
        + ((s*(z 1) + a) * (z 1 + b))^n * z 3) := by
  simp [Gw, RyaboginVolterra.mk4_apply]

set_option linter.unusedSimpArgs false in
lemma Gw_apply_three (n : ℕ) (s a b : ℝ) (z : VS1) :
    Gw n s a b z 3 = (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
      (((s*(-(z 0)) + a) * (-(z 0) + b))^(n-1) * (-(z 0) + b) * z 2
        + ((s*(z 1) + a) * (z 1 + b))^(n-1) * (z 1 + b) * z 3) := by
  simp [Gw, RyaboginVolterra.mk4_apply]

lemma Gw_apply_zero (n : ℕ) (s a b : ℝ) (z : VS1) : Gw n s a b z 0 = z 0 := by
  simp [Gw, RyaboginVolterra.mk4_apply]

lemma Gw_apply_one (n : ℕ) (s a b : ℝ) (z : VS1) : Gw n s a b z 1 = z 1 := by
  simp [Gw, RyaboginVolterra.mk4_apply]

lemma G_eq_Gw (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : VS1) :
    RyaboginVolterra.G n h s z = Gw n s (h s) (deriv h s) z := by
  ext i
  fin_cases i
  · simp only [Fin.isValue, Fin.reduceFinMk, G_apply_zero, Gw_apply_zero]
  · simp only [Fin.isValue, Fin.reduceFinMk, G_apply_one, Gw_apply_one]
  · simp only [Gw_apply_two, Fin.isValue, Fin.reduceFinMk, RyaboginVolterra.line,
      RyaboginVolterra.lineSlope]
    exact G_apply_two n h s z
  · simp only [Gw_apply_three, Fin.isValue, Fin.reduceFinMk, RyaboginVolterra.line,
      RyaboginVolterra.lineSlope]
    exact G_apply_three n h s z





lemma contDiffOn_parametric_iteratedDeriv_gen (k : ℕ)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : P → ℝ → ℝ) (hG : ContDiff ℝ ∞ (fun q : P × ℝ => G q.1 q.2)) :
    ContDiff ℝ ∞ (fun q : P × ℝ => iteratedDeriv k (fun u : ℝ => G q.1 u) q.2) := by
  have h := contDiffOn_parametric_iteratedDeriv_prod (k := k) (F := G) (U := Set.univ)
    isOpen_univ hG.contDiffOn
  exact contDiffOn_univ.mp h

set_option maxHeartbeats 1600000 in
/-- Smoothness of `Θ` for a family of perturbations `H ε` of the bump. -/
lemma contDiff_Theta_family (n : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2)) :
    ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      RyaboginVolterra.Theta n (fun u : ℝ => H q.1.1 u) q.1.2.1 q.2 q.1.2.2) := by
  have hdv : ContDiff ℝ ∞
      (fun q : (ℝ × (ℝ × VS1)) × ℝ => deriv (fun v : ℝ => H q.1.1 v) q.2) := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun v : ℝ => H p.1 v) p.2) :=
      contDiffOn_univ.mp (contDiffOn_deriv_snd_prod (P := ℝ) (G := H) isOpen_univ
        (by fun_prop : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => H p.1 p.2) Set.univ))
    exact h1.comp (by fun_prop : ContDiff ℝ ∞
      (fun q : (ℝ × (ℝ × VS1)) × ℝ => (q.1.1, q.2)))
  have key : ∀ (k : ℕ) (F : (ℝ × (ℝ × VS1)) → ℝ → ℝ),
      ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ => F q.1 q.2) →
      ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
        iteratedDeriv k (fun u : ℝ => F (q.1.1, (q.2, q.1.2.2)) u) q.1.2.1) := by
    intro k F hF
    have h1 : ContDiff ℝ ∞
        (fun q : (ℝ × (ℝ × VS1)) × ℝ => iteratedDeriv k (fun u : ℝ => F q.1 u) q.2) :=
      contDiffOn_parametric_iteratedDeriv_gen k F hF
    have h2 : ContDiff ℝ ∞
        (fun q : (ℝ × (ℝ × VS1)) × ℝ => ((q.1.1, (q.2, q.1.2.2)), q.1.2.1)) := by fun_prop
    have h3 := ContDiff.comp h1 h2
    have heq : (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
          iteratedDeriv k (fun u : ℝ => F (q.1.1, (q.2, q.1.2.2)) u) q.1.2.1)
        = (fun q : (ℝ × (ℝ × VS1)) × ℝ => iteratedDeriv k (fun u : ℝ => F q.1 u) q.2) ∘
          (fun q : (ℝ × (ℝ × VS1)) × ℝ => ((q.1.1, (q.2, q.1.2.2)), q.1.2.1)) := by
      funext q; rfl
    rw [heq]
    exact h3
  have h2a : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.2 * (-(q.1.2.2 0)) + H q.1.1 q.2)^2 - (u * (-(q.1.2.2 0)) + H q.1.1 u)^2)^n)
        q.1.2.1) :=
    key (n + 1) (fun p u => ((p.2.1 * (-(p.2.2 0)) + H p.1 p.2.1)^2
      - (u * (-(p.2.2 0)) + H p.1 u)^2)^n) (by fun_prop)
  have h2b : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      iteratedDeriv (n + 1) (fun u : ℝ =>
        ((q.2 * (q.1.2.2 1) + H q.1.1 q.2)^2 - (u * (q.1.2.2 1) + H q.1.1 u)^2)^n)
        q.1.2.1) :=
    key (n + 1) (fun p u => ((p.2.1 * (p.2.2 1) + H p.1 p.2.1)^2
      - (u * (p.2.2 1) + H p.1 u)^2)^n) (by fun_prop)
  have h3a : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.2 * (-(q.1.2.2 0)) + H q.1.1 q.2)^2 - (u * (-(q.1.2.2 0)) + H q.1.1 u)^2)^(n - 1)
          * (-(q.1.2.2 0) + deriv (fun v : ℝ => H q.1.1 v) u)) q.1.2.1) :=
    key n (fun p u => ((p.2.1 * (-(p.2.2 0)) + H p.1 p.2.1)^2
      - (u * (-(p.2.2 0)) + H p.1 u)^2)^(n - 1) * (-(p.2.2 0) + deriv (fun v : ℝ => H p.1 v) u))
      (by fun_prop)
  have h3b : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      iteratedDeriv n (fun u : ℝ =>
        ((q.2 * (q.1.2.2 1) + H q.1.1 q.2)^2 - (u * (q.1.2.2 1) + H q.1.1 u)^2)^(n - 1)
          * ((q.1.2.2 1) + deriv (fun v : ℝ => H q.1.1 v) u)) q.1.2.1) :=
    key n (fun p u => ((p.2.1 * (p.2.2 1) + H p.1 p.2.1)^2
      - (u * (p.2.2 1) + H p.1 u)^2)^(n - 1) * ((p.2.2 1) + deriv (fun v : ℝ => H p.1 v) u))
      (by fun_prop)
  let Φ : (ℝ × (ℝ × VS1)) × ℝ → VS1 := fun q => RyaboginVolterra.mk4 (-(q.1.2.2 2)) (-(q.1.2.2 3))
      (iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.2 * (-(q.1.2.2 0)) + H q.1.1 q.2)^2 - (u * (-(q.1.2.2 0)) + H q.1.1 u)^2)^n) q.1.2.1
            * (q.1.2.2 2)
        + iteratedDeriv (n + 1) (fun u : ℝ =>
          ((q.2 * (q.1.2.2 1) + H q.1.1 q.2)^2 - (u * (q.1.2.2 1) + H q.1.1 u)^2)^n) q.1.2.1
            * (q.1.2.2 3))
      (iteratedDeriv n (fun u : ℝ =>
          ((q.2 * (-(q.1.2.2 0)) + H q.1.1 q.2)^2 - (u * (-(q.1.2.2 0)) + H q.1.1 u)^2)^(n - 1)
            * (-(q.1.2.2 0) + deriv (fun v : ℝ => H q.1.1 v) u)) q.1.2.1 * (q.1.2.2 2)
        + iteratedDeriv n (fun u : ℝ =>
          ((q.2 * (q.1.2.2 1) + H q.1.1 q.2)^2 - (u * (q.1.2.2 1) + H q.1.1 u)^2)^(n - 1)
            * ((q.1.2.2 1) + deriv (fun v : ℝ => H q.1.1 v) u)) q.1.2.1 * (q.1.2.2 3))
  have heq : (fun q : (ℝ × (ℝ × VS1)) × ℝ =>
      RyaboginVolterra.Theta n (fun u : ℝ => H q.1.1 u) q.1.2.1 q.2 q.1.2.2) = Φ := by
    funext q
    ext i
    fin_cases i <;>
      · simp only [Φ, Theta_apply_zero, Theta_apply_one, Theta_apply_two, Theta_apply_three,
          RyaboginVolterra.mk4_apply, RyaboginVolterra.line, RyaboginVolterra.lineSlope,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ_zero_eq_one,
          Fin.succ_one_eq_two, Fin.isValue, Fin.reduceFinMk, Function.comp_apply]
  have hcoe : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × VS1)) × ℝ => ((Φ q : VS1) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;>
      · simp only [Φ, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
          Matrix.vecTail, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
          Fin.reduceFinMk, Function.comp_apply]
        first
          | fun_prop
          | exact ContDiff.add (ContDiff.mul h2a (by fun_prop)) (ContDiff.mul h2b (by fun_prop))
          | exact ContDiff.add (ContDiff.mul h3a (by fun_prop)) (ContDiff.mul h3b (by fun_prop))
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := ContDiff.comp h4 hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) ∘
      (fun q : (ℝ × (ℝ × VS1)) × ℝ => ((Φ q : VS1) : Fin 4 → ℝ)) = Φ := by
    funext q; simp
  rw [hfun] at h5
  rw [heq]
  exact h5




set_option maxHeartbeats 800000 in
lemma contDiff_Gw (n : ℕ) :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × VS1) => Gw n q.2.1 q.1.1 q.1.2 q.2.2) := by
  have hcoe : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × VS1) =>
      ((Gw n q.2.1 q.1.1 q.1.2 q.2.2 : VS1) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;>
      · simp only [Gw, RyaboginVolterra.mk4_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
          Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceFinMk,
          Function.comp_apply, Matrix.cons_val_succ]
        fun_prop
  have h2 : (fun q : (ℝ × ℝ) × (ℝ × VS1) =>
        ((Gw n q.2.1 q.1.1 q.1.2 q.2.2 : VS1) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS1 → (Fin 4 → ℝ)) ∘
        (fun q : (ℝ × ℝ) × (ℝ × VS1) => Gw n q.2.1 q.1.1 q.1.2 q.2.2) := rfl
  rw [h2] at hcoe
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := ContDiff.comp h4 hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS1) ∘
      (((EuclideanSpace.equiv (Fin 4) ℝ) : VS1 → (Fin 4 → ℝ)) ∘
        (fun q : (ℝ × ℝ) × (ℝ × VS1) => Gw n q.2.1 q.1.1 q.1.2 q.2.2)) =
      (fun q : (ℝ × ℝ) × (ℝ × VS1) => Gw n q.2.1 q.1.1 q.1.2 q.2.2) := by
    funext q; simp
  rw [hfun] at h5
  exact h5

/-- The normalised `G`-data with the values `h s`, `h' s` as explicit parameters. -/
noncomputable def GnW (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (s a b : ℝ) (U : VS) : VS :=
  (1 / ρ) • Qe.symm (Gw n s a b (baseZ s + ρ • U))

/-- The normalised perturbed `G`-data. -/
noncomputable def Gn (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (s : ℝ) (U : VS) : VS :=
  GnW n Qe ρ s (h s) (deriv h s) U

/-- The normalised `Θ`-data for the perturbation family `ε ↦ ε • h`. -/
noncomputable def ThnEps (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (ε s σ : ℝ)
    (U : VS) : VS :=
  (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U))

/-- The normalised perturbed `Θ`-data. -/
noncomputable def Thn (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (s σ : ℝ) (U : VS) : VS :=
  ThnEps n Qe ρ h 1 s σ U

/-- The normalised perturbed `Ξ`-data. -/
noncomputable def Xin (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (s : ℝ) : VS :=
  (1 / ρ) • Qe.symm (RyaboginVolterra.Xi n h s)

@[simp] lemma Thn_eq (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (s σ : ℝ) (U : VS) :
    Thn n Qe ρ h s σ U = (1 / ρ) • Qe.symm
      (RyaboginVolterra.Theta n h s σ (baseZ σ + ρ • U)) := by
  simp [Thn, ThnEps]

@[simp] lemma Gn_eq (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (h : ℝ → ℝ) (s : ℝ) (U : VS) :
    Gn n Qe ρ h s U = (1 / ρ) • Qe.symm
      (RyaboginVolterra.G n h s (baseZ s + ρ • U)) := by
  simp only [Gn, GnW, G_eq_Gw]

@[simp] lemma GnW_eq_TG (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (s : ℝ) (U : VS) :
    GnW n Qe ρ s 0 0 U = TG n Qe ρ s U := by
  have hz : deriv (fun _ : ℝ => (0 : ℝ)) s = 0 := deriv_const s 0
  simp only [GnW, TG, baseG, G_eq_Gw, hz]

@[simp] lemma Gn_zero (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (s : ℝ) (U : VS) :
    Gn n Qe ρ (fun _ => 0) s U = TG n Qe ρ s U := by
  have hz : deriv (fun _ : ℝ => (0 : ℝ)) s = 0 := deriv_const s 0
  simp only [Gn, GnW_eq_TG, hz]



lemma fderiv_fixed_fst {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → VS → VS}
    (hF : ContDiff ℝ ∞ (fun q : P × VS => F q.1 q.2)) (q : P × VS) :
    fderiv ℝ (fun z : VS => F q.1 z) q.2 =
      (fderiv ℝ (fun q' : P × VS => F q'.1 q'.2) q).comp (ContinuousLinearMap.inr ℝ P VS) := by
  have hφ : HasFDerivAt (fun z : VS => (q.1, z)) (ContinuousLinearMap.inr ℝ P VS) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have hF_at : HasFDerivAt (fun q' : P × VS => F q'.1 q'.2)
      (fderiv ℝ (fun q' : P × VS => F q'.1 q'.2) q) q :=
    ((ContDiff.differentiable hF (by simp)).differentiableAt).hasFDerivAt
  have hcomp := HasFDerivAt.comp q.2 hF_at hφ
  have heq : (fun q' : P × VS => F q'.1 q'.2) ∘ (fun z : VS => (q.1, z)) = fun z => F q.1 z := by
    funext z; rfl
  rw [heq] at hcomp
  exact hcomp.fderiv

lemma continuous_fderiv_snd {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → VS → VS} (hF : ContDiff ℝ ∞ (fun q : P × VS => F q.1 q.2)) :
    Continuous (fun q : P × VS => fderiv ℝ (fun z : VS => F q.1 z) q.2) := by
  have h1 : Continuous (fun q : P × VS => fderiv ℝ (fun q' : P × VS => F q'.1 q'.2) q) :=
    ContDiff.continuous_fderiv hF (by simp)
  have h2 : Continuous (fun q : P × VS =>
      (fderiv ℝ (fun q' : P × VS => F q'.1 q'.2) q).comp (ContinuousLinearMap.inr ℝ P VS)) :=
    h1.clm_comp continuous_const
  exact h2.congr fun q => (fderiv_fixed_fst hF q).symm




/-- The normalised `Θ`-data with the state argument kept explicit. -/
noncomputable def ThnRaw (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (hW : ℝ → ℝ) (ε s σ : ℝ)
    (z : VS) : VS :=
  (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n (ε • hW) s σ z)

lemma ThnEps_eq_raw (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) (hW : ℝ → ℝ) (ε s σ : ℝ) (U : VS) :
    ThnEps n Qe ρ hW ε s σ U = ThnRaw n Qe ρ hW ε s σ (baseZ σ + ρ • U) := by
  simp [ThnEps, ThnRaw]

set_option maxHeartbeats 1600000 in
lemma contDiff_ThnRaw (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0)
    {hW : ℝ → ℝ} (hhW : ContDiff ℝ ∞ hW) :
    ContDiff ℝ ∞ (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      ThnRaw n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hfamily := contDiff_Theta_family (n := n)
    (H := fun ε u : ℝ => ε * hW u) (by fun_prop)
  have hcomp := hfamily.comp (by fun_prop : ContDiff ℝ ∞
    (fun q : ((ℝ × (ℝ × ℝ)) × VS) => ((q.1.1, (q.1.2.1, q.2)), q.1.2.2)))
  have h2 : ContDiff ℝ ∞ (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n
        (fun u : ℝ => (fun ε u : ℝ => ε * hW u) q.1.1 u) q.1.2.1 q.1.2.2
          (q.2))) := by
    refine ContDiff.const_smul (1 / ρ) ?_
    exact (Qe.symm.contDiff).comp hcomp
  have heq : (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      ThnRaw n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 q.2) =
      (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
        (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n
          (fun u : ℝ => (fun ε u : ℝ => ε * hW u) q.1.1 u) q.1.2.1 q.1.2.2 q.2)) := by
    funext q; rfl
  rw [heq]
  exact h2

lemma continuous_fderiv_ThnRaw (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0)
    {hW : ℝ → ℝ} (hhW : ContDiff ℝ ∞ hW) :
    Continuous (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      fderiv ℝ (fun z : VS => ThnRaw n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 z) q.2) :=
  continuous_fderiv_snd (F := fun p : ℝ × (ℝ × ℝ) => fun z : VS =>
    ThnRaw n Qe ρ hW p.1 p.2.1 p.2.2 z) (contDiff_ThnRaw n Qe hρ hhW)


@[fun_prop]
lemma contDiff_baseZ : ContDiff ℝ ∞ baseZ := by
  have hd : ContDiff ℝ ∞ (deriv profileX) := contDiff_deriv_of_contDiff RyaboginVolterra.contDiff_profileX
  change ContDiff ℝ ∞ (fun s : ℝ => baseZ s)
  have heq : (fun s : ℝ => baseZ s) = fun s : ℝ =>
      RyaboginVolterra.mk4 (profileX s) (profileX s) (deriv profileX s) (deriv profileX s) := by
    funext s; rfl
  rw [heq]
  exact contDiff_mk4 RyaboginVolterra.contDiff_profileX RyaboginVolterra.contDiff_profileX hd hd

set_option maxHeartbeats 1600000 in
lemma contDiff_ThnEps (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0)
    {hW : ℝ → ℝ} (hhW : ContDiff ℝ ∞ hW) :
    ContDiff ℝ ∞ (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      ThnEps n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have h1 := (contDiff_ThnRaw n Qe hρ hhW).comp (by fun_prop : ContDiff ℝ ∞
      (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
        ((q.1.1, (q.1.2.1, q.1.2.2)), baseZ q.1.2.2 + ρ • q.2)))
  have heq : (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
        ThnEps n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 q.2) =
      (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
          ThnRaw n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 q.2) ∘
        (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
          ((q.1.1, (q.1.2.1, q.1.2.2)), baseZ q.1.2.2 + ρ • q.2)) := by
    funext q
    simp only [Function.comp_apply, ThnEps_eq_raw]
  rw [heq]
  exact h1



lemma continuous_fderiv_ThnEps (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0)
    {hW : ℝ → ℝ} (hhW : ContDiff ℝ ∞ hW) :
    Continuous (fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      fderiv ℝ (fun U' : VS => ThnEps n Qe ρ hW q.1.1 q.1.2.1 q.1.2.2 U') q.2) :=
  continuous_fderiv_snd (F := fun p : ℝ × (ℝ × ℝ) => fun z : VS =>
    ThnEps n Qe ρ hW p.1 p.2.1 p.2.2 z) (contDiff_ThnEps n Qe hρ hhW)


end Commons.Geometry.Ulam

-- ===== FILE _restrict.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## Interval-restricted versions of the row identities

The lemmas in `_tau_base` require the root conditions `f (y u) ^ 2 = ...` for *all* `u : ℝ`,
which cannot be satisfied by a smooth configuration.  Below we record the versions in which the
root conditions are assumed only on `Icc a b` and the conclusion is drawn only on the open
interval `Ioo a b`.  The only place where the global hypothesis was used is the recursive
definition of `boundaryTerm`, where `deriv (boundaryTerm ... k) s` is computed: with the
restricted hypothesis, `boundaryTerm ... k` vanishes on the whole neighbourhood `Ioo a b` of `s`,
which is enough. -/

lemma boundaryTerm_momentIntegrand_eq_zero_of_le_Ioo
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) {h x y f : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiffOn ℝ ∞ h Set.univ)
    (hx : ContDiffOn ℝ ∞ x Set.univ)
    (hy : ContDiffOn ℝ ∞ y Set.univ)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    ∀ s ∈ Set.Ioo a b,
      Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f) (fun u : ℝ => -x u) y k s = 0 := by
  induction k with
  | zero => intro s hs; simp [Commons.Analysis.Calculus.boundaryTerm]
  | succ k ih =>
      intro s hs
      have hsa : a ≤ s := hs.1.le
      have hsb : s ≤ b := hs.2.le
      have hxy_s := hxy s ⟨hsa, hsb⟩
      have hk_lt : k < n := Nat.lt_of_succ_le hk
      have hh_glob : ContDiff ℝ ∞ h := contDiffOn_univ.mp hh
      have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
      have hpartial_zero (t : ℝ) (ht : f t ^ 2 = (s * t + h s) ^ 2) :
          Commons.Analysis.Calculus.partialDerivIter (RyaboginVolterra.momentIntegrand n h f) k s t = 0 := by
        let g : ℝ → ℝ := fun u : ℝ => f t ^ 2 - RyaboginVolterra.line h u t ^ 2
        let gpow : ℝ → ℝ := fun u : ℝ => (g u) ^ n
        have hg_cont : ContDiff ℝ n g := by
          dsimp [g, RyaboginVolterra.line]
          fun_prop
        have hzero_g : g s = 0 := by
          dsimp [g, RyaboginVolterra.line]
          rw [ht]
          ring
        have hpow := iteratedDeriv_pow_zero_of_zero (n := n) (k := k) (s := s)
          (g := g) hg_cont hzero_g hk_lt
        have hgpow : iteratedDeriv k gpow s = 0 := by
          simpa [gpow] using hpow
        have hpart : Commons.Analysis.Calculus.partialDerivIter (RyaboginVolterra.momentIntegrand n h f) k s t =
            iteratedDeriv k gpow s := by
          simp [Commons.Analysis.Calculus.partialDerivIter, RyaboginVolterra.momentIntegrand, gpow, g, RyaboginVolterra.line]
        rw [hpart]
        exact hgpow
      have hev : (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f)
          (fun u : ℝ => -x u) y k) =ᶠ[𝓝 s] 0 := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
        exact ih (Nat.le_of_lt hk_lt) u hu
      have hder : deriv (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f)
          (fun u : ℝ => -x u) y k) s = 0 := by
        rw [hev.deriv_eq]
        simp
      rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
      have hyzero := hpartial_zero (y s) hxy_s.1
      have hxzero := hpartial_zero (-x s) hxy_s.2
      have hyzero' : iteratedDeriv k (fun v : ℝ => RyaboginVolterra.momentIntegrand n h f v (y s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hyzero
      have hxzero' : iteratedDeriv k (fun v : ℝ => RyaboginVolterra.momentIntegrand n h f v (-x s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hxzero
      simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
        iteratedDeriv_zero] at hyzero' hxzero' hder ⊢
      rw [hyzero', hxzero', hder]
      simp

lemma boundaryTerm_centroidIntegrand_eq_zero_of_le_Ioo
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n - 1) {h x y f : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiffOn ℝ ∞ h Set.univ)
    (hx : ContDiffOn ℝ ∞ x Set.univ)
    (hy : ContDiffOn ℝ ∞ y Set.univ)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    ∀ s ∈ Set.Ioo a b,
      Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f) (fun u : ℝ => -x u) y k s = 0 := by
  induction k with
  | zero => intro s hs; simp [Commons.Analysis.Calculus.boundaryTerm]
  | succ k ih =>
      intro s hs
      have hsa : a ≤ s := hs.1.le
      have hsb : s ≤ b := hs.2.le
      have hxy_s := hxy s ⟨hsa, hsb⟩
      have hk_lt : k < n - 1 := Nat.lt_of_succ_le hk
      have hh_glob : ContDiff ℝ ∞ h := contDiffOn_univ.mp hh
      have hh_n : ContDiff ℝ n h := (contDiff_infty.mp hh_glob) n
      have hpartial_zero (t : ℝ) (ht : f t ^ 2 = (s * t + h s) ^ 2) :
          Commons.Analysis.Calculus.partialDerivIter (RyaboginVolterra.centroidIntegrand n h f) k s t = 0 := by
        let m : ℕ := n - 1
        let g : ℝ → ℝ := fun u : ℝ => f t ^ 2 - RyaboginVolterra.line h u t ^ 2
        let b' : ℝ → ℝ := fun u : ℝ => RyaboginVolterra.lineSlope h u t
        have hmk : k < m := by dsimp [m]; exact hk_lt
        have hh_m : ContDiff ℝ m h := by
          have hle : m ≤ n := by dsimp [m]; omega
          exact hh_n.of_le (by exact_mod_cast hle)
        have hg_cont : ContDiff ℝ m g := by
          dsimp [g, RyaboginVolterra.line]
          fun_prop
        have hder_cont : ContDiff ℝ m (deriv h) := by
          have hmn : n = m + 1 := by dsimp [m]; omega
          have hd : ContDiff ℝ (m + 1) h := by simpa [hmn] using hh_n
          exact hd.deriv'
        have hb_cont : ContDiff ℝ m b' := by
          dsimp [b', RyaboginVolterra.lineSlope]
          simpa [add_comm] using (contDiff_const.add hder_cont)
        have hzero_g : g s = 0 := by
          dsimp [g, RyaboginVolterra.line]
          rw [ht]
          ring
        have hpow := iteratedDeriv_pow_mul_zero_of_lt (m := m) (k := k) (g := g) (b := b')
          (s := s) hg_cont hb_cont hzero_g hmk
        have hfun : (fun u : ℝ => RyaboginVolterra.centroidIntegrand n h f u t) = fun u : ℝ => (g u) ^ m * b' u := by
          funext u
          dsimp [RyaboginVolterra.centroidIntegrand, RyaboginVolterra.momentIntegrand, g, b', m]
        have hmain : Commons.Analysis.Calculus.partialDerivIter (RyaboginVolterra.centroidIntegrand n h f) k s t =
            iteratedDeriv k (fun u : ℝ => (g u) ^ m * b' u) s := by
          simp [Commons.Analysis.Calculus.partialDerivIter, hfun]
        rw [hmain]
        exact hpow
      have hev : (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
          (fun u : ℝ => -x u) y k) =ᶠ[𝓝 s] 0 := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
        exact ih (Nat.le_of_lt hk_lt) u hu
      have hder : deriv (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
          (fun u : ℝ => -x u) y k) s = 0 := by
        rw [hev.deriv_eq]
        simp
      rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
      have hyzero := hpartial_zero (y s) hxy_s.1
      have hxzero := hpartial_zero (-x s) hxy_s.2
      have hyzero' : iteratedDeriv k (fun v : ℝ => RyaboginVolterra.centroidIntegrand n h f v (y s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hyzero
      have hxzero' : iteratedDeriv k (fun v : ℝ => RyaboginVolterra.centroidIntegrand n h f v (-x s)) s = 0 := by
        simpa [Commons.Analysis.Calculus.partialDerivIter] using hxzero
      simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
        iteratedDeriv_zero] at hyzero' hxzero' hder ⊢
      rw [hyzero', hxzero', hder]
      simp

lemma boundaryTerm_momentIntegrand_eq_G_row2_Ioo
    {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiffOn ℝ ∞ h Set.univ)
    (hx : ContDiffOn ℝ ∞ x Set.univ)
    (hy : ContDiffOn ℝ ∞ y Set.univ)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    ∀ s ∈ Set.Ioo a b,
      Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f)
        (fun u : ℝ => -x u) y (n + 1) s = (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 2 := by
  intro s hs
  have hxy_s := hxy s ⟨hs.1.le, hs.2.le⟩
  have hev : (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f)
      (fun u : ℝ => -x u) y n) =ᶠ[𝓝 s] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact boundaryTerm_momentIntegrand_eq_zero_of_le_Ioo (n := n) (k := n) hn le_rfl hh hx hy hxy u hu
  have hder : deriv (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.momentIntegrand n h f)
      (fun u : ℝ => -x u) y n) s = 0 := by
    rw [hev.deriv_eq]
    simp
  rw [Commons.Analysis.Calculus.boundaryTerm_succ_eq]
  have hyC := partialDerivIter_momentIntegrand_eq_endpointC (n := n) hn hh hxy_s.1
  have hxC := partialDerivIter_momentIntegrand_eq_endpointC (n := n) hn hh hxy_s.2
  have hyC' : iteratedDeriv n (fun v : ℝ => RyaboginVolterra.momentIntegrand n h f v (y s)) s
      = RyaboginVolterra.endpointC n h s (y s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hyC
  have hxC' : iteratedDeriv n (fun v : ℝ => RyaboginVolterra.momentIntegrand n h f v (-x s)) s
      = RyaboginVolterra.endpointC n h s (-x s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hxC
  simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
    iteratedDeriv_zero] at hyC' hxC' hder ⊢
  rw [hyC', hxC', hder]
  simp [mk4, RyaboginVolterra.G, RyaboginVolterra.stateOf, RyaboginVolterra.endpointC]
  ring

lemma boundaryTerm_centroidIntegrand_eq_G_row3_Ioo
    {n : ℕ} (hn : 2 ≤ n) {h x y f : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiffOn ℝ ∞ h Set.univ)
    (hx : ContDiffOn ℝ ∞ x Set.univ)
    (hy : ContDiffOn ℝ ∞ y Set.univ)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2) :
    ∀ s ∈ Set.Ioo a b,
      Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
        (fun u : ℝ => -x u) y n s = (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 3 := by
  intro s hs
  have hxy_s := hxy s ⟨hs.1.le, hs.2.le⟩
  have hev : (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
      (fun u : ℝ => -x u) y (n - 1)) =ᶠ[𝓝 s] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact boundaryTerm_centroidIntegrand_eq_zero_of_le_Ioo (n := n) (k := n - 1) hn le_rfl hh hx hy
      hxy u hu
  have hder : deriv (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
      (fun u : ℝ => -x u) y (n - 1)) s = 0 := by
    rw [hev.deriv_eq]
    simp
  have hstep := Commons.Analysis.Calculus.boundaryTerm_succ_eq
    (F := RyaboginVolterra.centroidIntegrand n h f) (a := fun u : ℝ => -x u) (b := y) (k := n - 1) (s := s)
  have hstep' : Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
      (fun u : ℝ => -x u) y n s =
      Commons.Analysis.Calculus.boundaryTerm
        (Commons.Analysis.Calculus.partialDerivIter (RyaboginVolterra.centroidIntegrand n h f) (n - 1))
        (fun u : ℝ => -x u) y 1 s +
        deriv (Commons.Analysis.Calculus.boundaryTerm (RyaboginVolterra.centroidIntegrand n h f)
          (fun u : ℝ => -x u) y (n - 1)) s := by
    simpa [show (n - 1) + 1 = n by omega] using hstep
  rw [hstep']
  have hyD := partialDerivIter_centroidIntegrand_eq_endpointD (n := n) hn hh hxy_s.1
  have hxD := partialDerivIter_centroidIntegrand_eq_endpointD (n := n) hn hh hxy_s.2
  have hyD' : iteratedDeriv (n - 1) (fun v : ℝ => RyaboginVolterra.centroidIntegrand n h f v (y s)) s
      = RyaboginVolterra.endpointD n h s (y s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hyD
  have hxD' : iteratedDeriv (n - 1) (fun v : ℝ => RyaboginVolterra.centroidIntegrand n h f v (-x s)) s
      = RyaboginVolterra.endpointD n h s (-x s) := by
    simpa [Commons.Analysis.Calculus.partialDerivIter] using hxD
  simp only [Commons.Analysis.Calculus.boundaryTerm, Commons.Analysis.Calculus.partialDerivIter,
    iteratedDeriv_zero] at hyD' hxD' hder ⊢
  rw [hyD', hxD', hder]
  simp [mk4, RyaboginVolterra.G, RyaboginVolterra.stateOf, RyaboginVolterra.endpointD]
  ring

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma integral_iteratedDeriv_momentF_eq_Icc (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv (n + 1) (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s)
      = RyaboginVolterra.Xi1 n h s
        - (∫ σ in s..b, (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv (n + 1)
    (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv (n + 1)
    (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ n) s with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    exact continuous_iteratedDeriv_param (n + 1) (by fun_prop) s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi1 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi1, RyaboginVolterra.line]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ' : σ ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hs.2] at hσ
      exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
    have hy1 := (hxy σ hσ').1
    have hx1 := (hxy σ hσ').2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf,
      RyaboginVolterra.line, hx1, hy1]
  rw [hmain, hQeq, hSum]

lemma integral_iteratedDeriv_momentH_eq_Icc (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv n
          (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s)
      = RyaboginVolterra.Xi2 n h s
        - (∫ σ in s..b, (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    exact continuous_iteratedDeriv_param n (by fun_prop) s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi2 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi2, RyaboginVolterra.line, RyaboginVolterra.lineSlope]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ' : σ ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hs.2] at hσ
      exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
    have hy1 := (hxy σ hσ').1
    have hx1 := (hxy σ hσ').2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope, hx1, hy1]
  rw [hmain, hQeq, hSum]

lemma iteratedDeriv_momentF_eq_volterra_row_Ioo (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (hab : a ≤ b)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b) :
    ∀ s ∈ Set.Ioo a b,
      iteratedDeriv (n + 1)
          (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s =
        (RyaboginVolterra.G n h s (stateOf x y s)) 2
          - ((∫ σ in s..b,
                RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
              + RyaboginVolterra.Xi n h s) 2 := by
  intro s hs
  have hF : ContDiff ℝ (n + 1)
      (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
    have h1 : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
      unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
      fun_prop
    exact h1.of_le (by exact_mod_cast le_top)
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n + 1) (F := fun u t : ℝ => RyaboginVolterra.momentIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le (by exact_mod_cast le_top))
    (hy.of_le (by exact_mod_cast le_top)) (s := s)
  have hbt := boundaryTerm_momentIntegrand_eq_G_row2_Ioo (n := n) hn hh.contDiffOn hx.contDiffOn
    hy.contDiffOn hxy s hs
  have hrow := integral_iteratedDeriv_momentF_eq_Icc n hab hh hx hy hf hxy hxdec hydec hxb hyb hfb
    hxle hyle hord ⟨hs.1.le, hs.2.le⟩
  have hsplit : iteratedDeriv (n + 1)
        (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s
      = iteratedDeriv (n + 1) (fun u : ℝ => RyaboginVolterra.momentF n h x y f u) s
        - iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    change iteratedDeriv (n + 1)
      (RyaboginVolterra.momentF n h x y f - RyaboginVolterra.momentRHS n) s = _
    rw [iteratedDeriv_sub]
    · exact ((RyaboginVolterra.contDiff_momentF n hh hx hy hf).of_le
        (by exact_mod_cast le_top)).contDiffAt
    · exact ((contDiff_momentRHS n).of_le (by exact_mod_cast le_top)).contDiffAt
  have hXi : (RyaboginVolterra.Xi n h s) 2
      = -(RyaboginVolterra.Xi1 n h s)
        + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  rw [hsplit]
  unfold RyaboginVolterra.momentF
  rw [hleib, hbt]
  unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi,
    intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 2]
  ring

lemma iteratedDeriv_momentH_eq_volterra_row_Ioo (n : ℕ) (hn : 2 ≤ n) {a b : ℝ} (hab : a ≤ b)
    {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ ∞ f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b) :
    ∀ s ∈ Set.Ioo a b,
      iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n h x y f u) s =
        (RyaboginVolterra.G n h s (stateOf x y s)) 3
          - ((∫ σ in s..b,
                RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
              + RyaboginVolterra.Xi n h s) 3 := by
  intro s hs
  have hF : ContDiff ℝ n
      (fun p : ℝ × ℝ => RyaboginVolterra.centroidIntegrand n h f p.1 p.2) := by
    have h1 : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => RyaboginVolterra.centroidIntegrand n h f p.1 p.2) := by
      unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
      fun_prop
    exact h1.of_le (by exact_mod_cast le_top)
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n) (F := fun u t : ℝ => RyaboginVolterra.centroidIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le (by exact_mod_cast le_top))
    (hy.of_le (by exact_mod_cast le_top)) (s := s)
  have hbt := boundaryTerm_centroidIntegrand_eq_G_row3_Ioo (n := n) hn hh.contDiffOn hx.contDiffOn
    hy.contDiffOn hxy s hs
  have hrow := integral_iteratedDeriv_momentH_eq_Icc n hab hh hx hy hf hxy hxdec hydec hxb hyb hfb
    hxle hyle hord ⟨hs.1.le, hs.2.le⟩
  have hXi : (RyaboginVolterra.Xi n h s) 3 = -(RyaboginVolterra.Xi2 n h s) := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  unfold RyaboginVolterra.momentH
  rw [hleib, hbt]
  unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi,
    intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 3]
  ring

end Commons.Geometry.Ulam
end

-- ===== FILE _finint.lean =====

noncomputable section
open Filter MeasureTheory Set
open scoped Topology Interval ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Commons.Analysis.Calculus

/-!
# Finite-order smoothness of parametric interval integrals with moving endpoints

This is the finite-order version of
`Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving` (which is stated for the
order `∞`).  It is needed because the "device" profile of the Ulam construction is only `C^{n+2}`,
so the rows must be run at finite order.

Main result: `contDiff_intervalIntegral_of_contDiff_moving_finite (K)`:
for `F` jointly `C^K` and `a, b` of class `C^K`,
`s ↦ ∫ t in (a s)..(b s), F s t` is `C^K`.

The proof follows the `∞`-version: reduce to a fixed lower endpoint (`∫_a^b = ∫_0^b - ∫_0^a`),
then induct on the order using `contDiffAt_succ_iff_hasFDerivAt` and the
"differentiation under the integral sign" formula.
-/

variable {F : ℝ → ℝ → ℝ}

/-- The `s`-partial derivative of `(s,t) ↦ F s t` is one order less smooth. -/
lemma contDiff_fderiv_fst_fin {K : ℕ}
    (hG : ContDiff ℝ (K + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ K (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) p (1, 0)) := by
  have hfd : ContDiff ℝ K (fun q : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) q) := by
    have h := hG.fderiv_right (m := (K : WithTop ℕ∞))
      (by exact_mod_cast (Nat.lt_succ_self K))
    simpa using h
  have hvec : ContDiff ℝ K (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) := contDiff_const
  have h := hfd.clm_apply hvec
  simpa using h

/-- Derivative of `v ↦ F v t` is the `s`-partial derivative at `(u,t)`. -/
lemma hasDerivAt_fderiv_fst_fin {K : ℕ}
    (hG : ContDiff ℝ (K + 1) (fun p : ℝ × ℝ => F p.1 p.2)) :
    ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t)
      (fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (u, t) (1, 0)) u := by
  intro u t
  have hle : ((1 : ℕ) : WithTop ℕ∞) ≤ ((K + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : 1 ≤ K + 1)
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (u, t) :=
    ((hG.contDiffAt (x := (u, t))).of_le hle).differentiableAt (by norm_num)
  have hGfderiv := hdiff.hasFDerivAt
  have hγ : HasDerivAt (fun v : ℝ => (v, t)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u t)
  have hcomp := hGfderiv.comp_hasDerivAt u hγ
  have hfun : (fun v : ℝ => F v t) = (fun p : ℝ × ℝ => F p.1 p.2) ∘ (fun v : ℝ => (v, t)) := by
    funext v; rfl
  rw [hfun]
  exact hcomp

/-- Differentiation under the integral sign for the fixed-lower integral `q ↦ ∫ t in 0..q.2, F q.1 t`. -/
lemma intervalIntegral_hasFDerivAt_fixedLower_fin {K : ℕ}
    (hG : ContDiff ℝ (K + 1) (fun p : ℝ × ℝ => F p.1 p.2)) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => ∫ t in (0 : ℝ)..q.2, F q.1 t)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0 : ℝ)..p.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (p.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F p.1 p.2))) p := by
  let F' : ℝ → ℝ → ℝ := fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
  have hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
    continuous_iff_continuousAt.mpr fun x => (hG.contDiffAt (x := x)).continuousAt
  have hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
    have hF' : ContDiff ℝ K (fun p : ℝ × ℝ => F' p.1 p.2) := by
      simpa [F'] using contDiff_fderiv_fst_fin hG
    exact hF'.continuous
  have hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u := by
    simpa [F'] using hasDerivAt_fderiv_fst_fin hG
  have h := intervalIntegral_hasFDerivAt_upper_of_continuous'
    (a := (0:ℝ)) (b := p.2) (x₀ := p.1) (F := F) (F' := F')
    hF_cont hF'_cont hF'_isDeriv
  simpa [F'] using h

/-- Continuity of `(s,u) ↦ ∫ t in 0..u, F s t`, from continuity of `F` only. -/
lemma continuous_intervalIntegral_fixedLower_fin
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) := by
  let f₂ : (ℝ × ℝ) → ℝ → ℝ := fun p t => F p.1 t
  have hf₂cont : Continuous (Function.uncurry f₂) := by
    have hfun : Function.uncurry f₂ = fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.2 := by
      ext q; rfl
    rw [hfun]
    exact hF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := f₂) (a₀ := (0:ℝ)) (μ := MeasureTheory.volume) (s := fun q : ℝ × ℝ => q.2)
    hf₂cont continuous_snd
  simpa [f₂] using hcont

/-- The `C^0` case of the fixed-lower smoothness theorem. -/
lemma contDiff_zero_intervalIntegral_fixedLower_fin
    (hG : ContDiff ℝ 0 (fun p : ℝ × ℝ => F p.1 p.2)) (p : ℝ × ℝ) :
    ContDiffAt ℝ 0 (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) p := by
  rw [contDiffAt_zero]
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  exact (continuous_intervalIntegral_fixedLower_fin (contDiff_zero.mp hG)).continuousOn

/-- Smoothness of the derivative candidate for the fixed-lower interval integral. -/
lemma contDiffAt_fderiv_intervalIntegral_fixedLower_fin {K : ℕ} {p : ℝ × ℝ}
    (hGat : ContDiffAt ℝ K (fun p : ℝ × ℝ => F p.1 p.2) p)
    (hφD : ContDiffAt ℝ K
      (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2,
        fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)) p) :
    ContDiffAt ℝ K
      (fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2))) p := by
  have hfst : ContDiffAt ℝ K (fun _ : ℝ × ℝ => ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    contDiffAt_const
  have h1 : ContDiffAt ℝ K
      (fun q : ℝ × ℝ => (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (∫ t in (0:ℝ)..q.2,
          fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0))) p :=
    hfst.smulRight hφD
  have hsnd : ContDiffAt ℝ K (fun _ : ℝ × ℝ => ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    contDiffAt_const
  have hGp : ContDiffAt ℝ K (fun q : ℝ × ℝ => F q.1 q.2) p := hGat
  have h2 : ContDiffAt ℝ K
      (fun q : ℝ × ℝ => (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)) p :=
    hsnd.smulRight hGp
  exact h1.add h2

/-- Induction step of the fixed-lower smoothness theorem (finite orders). -/
lemma contDiffAt_succ_intervalIntegral_fixedLower_fin :
    ∀ (m : ℕ), ContDiff ℝ (m + 1) (fun p : ℝ × ℝ => F p.1 p.2) →
      ∀ p : ℝ × ℝ, ContDiffAt ℝ (m + 1) (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) p := by
  intro m
  induction m generalizing F with
  | zero =>
      intro hG p
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)), ?_, ?_⟩
      · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro q _
        exact intervalIntegral_hasFDerivAt_fixedLower_fin hG q
      · let D : ℝ → ℝ → ℝ := fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
        have hDcurry : ContDiff ℝ 0 (fun p : ℝ × ℝ => D p.1 p.2) := by
          simpa [D] using contDiff_fderiv_fst_fin hG
        exact contDiffAt_fderiv_intervalIntegral_fixedLower_fin
          ((hG.contDiffAt (x := p)).of_le (by norm_num))
          (contDiff_zero_intervalIntegral_fixedLower_fin hDcurry p)
  | succ m ih =>
      intro hG p
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)), ?_, ?_⟩
      · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro q _
        exact intervalIntegral_hasFDerivAt_fixedLower_fin hG q
      · let D : ℝ → ℝ → ℝ := fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
        have hDcurry : ContDiff ℝ (m + 1) (fun p : ℝ × ℝ => D p.1 p.2) := by
          simpa [D] using contDiff_fderiv_fst_fin hG
        have hterm : ContDiffAt ℝ (m + 1)
            (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, D q.1 t) p := ih hDcurry p
        exact contDiffAt_fderiv_intervalIntegral_fixedLower_fin
          ((hG.contDiffAt (x := p)).of_le (by norm_num)) hterm

/-- The fixed-lower, moving-upper interval integral `(s,u) ↦ ∫ t in 0..u, F s t` is `C^K`
when `(s,t) ↦ F s t` is `C^K`. -/
theorem contDiff_intervalIntegral_fixedLower_fin :
    ∀ K : ℕ, ContDiff ℝ K (fun p : ℝ × ℝ => F p.1 p.2) →
      ContDiff ℝ K (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) := by
  intro K
  induction K with
  | zero =>
      intro hG
      exact contDiff_zero.mpr (continuous_intervalIntegral_fixedLower_fin (contDiff_zero.mp hG))
  | succ m ih =>
      intro hG
      rw [contDiff_iff_contDiffAt]
      intro p
      exact contDiffAt_succ_intervalIntegral_fixedLower_fin m hG p

/-- Splitting an interval integral at `0`, so that both pieces have fixed lower endpoint `0`. -/
lemma intervalIntegral_eq_sub_fixedZero_fin (s : ℝ)
    (hS : Continuous (fun t : ℝ => F s t)) (a b : ℝ) :
    (∫ t in a..b, F s t) = (∫ t in (0:ℝ)..b, F s t) - (∫ t in (0:ℝ)..a, F s t) := by
  have hInt0a : IntervalIntegrable (fun t : ℝ => F s t) MeasureTheory.volume (0:ℝ) a :=
    hS.intervalIntegrable _ _
  have hIntab : IntervalIntegrable (fun t : ℝ => F s t) MeasureTheory.volume a b :=
    hS.intervalIntegrable _ _
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (f := fun t : ℝ => F s t) (a := (0:ℝ)) (b := a) (c := b) hInt0a hIntab
  linarith

/-- **Finite-order smoothness of a parametric interval integral with moving endpoints.** -/
theorem contDiff_intervalIntegral_of_contDiff_moving_finite (K : ℕ) {a b : ℝ → ℝ}
    (hF : ContDiff ℝ K (fun p : ℝ × ℝ => F p.1 p.2)) (ha : ContDiff ℝ K a)
    (hb : ContDiff ℝ K b) :
    ContDiff ℝ K (fun s : ℝ => ∫ t in (a s)..(b s), F s t) := by
  have hcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
    continuous_iff_continuousAt.mpr fun x => (hF.contDiffAt (x := x)).continuousAt
  have hφ := contDiff_intervalIntegral_fixedLower_fin K hF
  have hbvec : ContDiff ℝ K (fun s : ℝ => (s, b s)) := contDiff_id.prodMk hb
  have havec : ContDiff ℝ K (fun s : ℝ => (s, a s)) := contDiff_id.prodMk ha
  have hdiff := (hφ.comp hbvec).sub (hφ.comp havec)
  rw [← contDiffOn_univ] at hdiff
  rw [← contDiffOn_univ]
  exact hdiff.congr fun s _ =>
    intervalIntegral_eq_sub_fixedZero_fin (F := F) s (by fun_prop) (a s) (b s)

end Commons.Analysis.Calculus
end

-- ===== FILE _finrows.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Finite-order smoothness of the first moment function. -/
lemma contDiff_momentF_fin (n : ℕ) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ (n + 1) (fun s : ℝ => RyaboginVolterra.momentF n h x y f s) := by
  have hle : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1)))
  unfold RyaboginVolterra.momentF
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving_finite (n + 1)
    ?_ (hx.neg.of_le hle) (hy.of_le hle)
  unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
  have hh' : ContDiff ℝ (n + 1) h := hh.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
  have hx' : ContDiff ℝ (n + 1) x := hx.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
  have hy' : ContDiff ℝ (n + 1) y := hy.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
  fun_prop

/-- Finite-order smoothness of the second moment function. -/
lemma contDiff_momentH_fin (n : ℕ) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun s : ℝ => RyaboginVolterra.momentH n h x y f s) := by
  have hle : ((n : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
  unfold RyaboginVolterra.momentH
  refine Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving_finite n
    ?_ (hx.neg.of_le hle) (hy.of_le hle)
  unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
  have hdv : ContDiff ℝ n (fun p : ℝ × ℝ => deriv h p.1) := by
    have hh1 : ContDiff ℝ (n + 1) h := hh.of_le (le_of_lt
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
    fun_prop
  have hh' : ContDiff ℝ n h := hh.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
  have hx' : ContDiff ℝ n x := hx.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
  have hy' : ContDiff ℝ n y := hy.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
  fun_prop

/-- The interval-restricted version of the split of the first moment integral, with the
smoothness hypothesis on `f` weakened to finite order (the original in `_restrict.lean` asks for
`ContDiff ℝ ∞ f`, which the `C^{n+2}` device does not have). -/
lemma integral_iteratedDeriv_momentF_eq_Icc_fin (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ (n + 1) f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv (n + 1) (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s)
      = RyaboginVolterra.Xi1 n h s
        - (∫ σ in s..b, (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv (n + 1)
    (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ n) s with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv (n + 1)
    (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ n) s with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    have hh1 : ContDiff ℝ (n + 1) h := hh.of_le (le_of_lt
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
    have hA : ContDiff ℝ (n + 1)
        (fun p : ℝ × ℝ => (f p.1 ^ 2 - (p.2 * p.1 + h p.2) ^ 2) ^ n) := by fun_prop
    exact Commons.Analysis.Calculus.continuous_iteratedDeriv_param_fin le_rfl hA s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi1 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi1, RyaboginVolterra.line]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 2) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ' : σ ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hs.2] at hσ
      exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
    have hy1 := (hxy σ hσ').1
    have hx1 := (hxy σ hσ').2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf,
      RyaboginVolterra.line, hx1, hy1]
  rw [hmain, hQeq, hSum]

/-- **The first row identity, at finite smoothness.**  The interval-restricted version of
`iteratedDeriv_momentF_eq_volterra_row_Ioo` with `ContDiff ℝ ∞ f` replaced by
`ContDiff ℝ (n + 2) f`; the only place the extra smoothness was used is the split
`iteratedDeriv (n+1) (momentF - momentRHS) = iteratedDeriv (n+1) momentF - iteratedDeriv (n+1)
momentRHS`, now discharged by `contDiff_momentF_fin`. -/
lemma iteratedDeriv_momentF_eq_volterra_row_Ioo_fin (n : ℕ) (hn : 2 ≤ n) {a b : ℝ}
    (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ (n + 2) f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b) :
    ∀ s ∈ Set.Ioo a b,
      iteratedDeriv (n + 1)
          (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s =
        (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 2
          - ((∫ σ in s..b,
                RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
              + RyaboginVolterra.Xi n h s) 2 := by
  intro s hs
  have hle1 : ((n + 1 : ℕ) : ℕ∞ω) ≤ ((n + 2 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  have hF : ContDiff ℝ (n + 1)
      (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
    have hh2 : ContDiff ℝ (n + 2) h := hh.of_le (le_of_lt
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 2))))
    have h1 : ContDiff ℝ (n + 2)
        (fun p : ℝ × ℝ => RyaboginVolterra.momentIntegrand n h f p.1 p.2) := by
      unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
      fun_prop
    exact h1.of_le hle1
  have hlen : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1)))
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n + 1) (F := fun u t : ℝ => RyaboginVolterra.momentIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le hlen) (hy.of_le hlen) (s := s)
  have hbt := boundaryTerm_momentIntegrand_eq_G_row2_Ioo (n := n) hn hh.contDiffOn
    hx.contDiffOn hy.contDiffOn hxy s hs
  have hrow := integral_iteratedDeriv_momentF_eq_Icc_fin n hab hh hx hy (hf.of_le hle1) hxy hxdec hydec hxb hyb
    hfb hxle hyle hord ⟨hs.1.le, hs.2.le⟩
  have hsplit : iteratedDeriv (n + 1)
        (fun u : ℝ => RyaboginVolterra.momentF n h x y f u - RyaboginVolterra.momentRHS n u) s
      = iteratedDeriv (n + 1) (fun u : ℝ => RyaboginVolterra.momentF n h x y f u) s
        - iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    change iteratedDeriv (n + 1)
      (RyaboginVolterra.momentF n h x y f - RyaboginVolterra.momentRHS n) s = _
    rw [iteratedDeriv_sub]
    · exact (contDiff_momentF_fin n hh hx hy (hf.of_le hle1)).contDiffAt
    · exact ((contDiff_momentRHS n).of_le hlen).contDiffAt
  have hXi : (RyaboginVolterra.Xi n h s) 2
      = -(RyaboginVolterra.Xi1 n h s)
        + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) s := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  rw [hsplit]
  unfold RyaboginVolterra.momentF
  rw [hleib, hbt]
  unfold RyaboginVolterra.momentIntegrand RyaboginVolterra.line
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi,
    intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 2]
  ring


/-- Finite-order copy of `integral_iteratedDeriv_momentH_eq_Icc`. -/
lemma integral_iteratedDeriv_momentH_eq_Icc_fin (n : ℕ) {a b : ℝ} (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ n f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b)
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    (∫ t in (-x s)..(y s),
        iteratedDeriv n
          (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s)
      = RyaboginVolterra.Xi2 n h s
        - (∫ σ in s..b, (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
  set P : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (f t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hPdef
  set Q : ℝ → ℝ := fun t => iteratedDeriv n
    (fun u : ℝ => (1 - t ^ 2 - (u * t + h u) ^ 2) ^ (n - 1) * (t + deriv h u)) s with hQdef
  have hPc : Continuous P := by
    rw [hPdef]
    have hh' : ContDiff ℝ n h := hh.of_le (le_of_lt
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)))
    have hh2 : ContDiff ℝ (n + 1) h := hh.of_le (le_of_lt
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
    have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => f p.1 ^ 2) := by fun_prop
    have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => p.2 * p.1 + h p.2) := by fun_prop
    have h3 : ContDiff ℝ n (fun p : ℝ × ℝ => p.1 + deriv h p.2) := by fun_prop
    have hA : ContDiff ℝ n
        (fun p : ℝ × ℝ => (f p.1 ^ 2 - (p.2 * p.1 + h p.2) ^ 2) ^ (n - 1)
          * (p.1 + deriv h p.2)) := by
      simpa only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply] using
        ((h1.sub (h2.pow 2)).pow (n - 1)).mul h3
    exact Commons.Analysis.Calculus.continuous_iteratedDeriv_param_fin le_rfl hA s
  have hPQ : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), P t = Q t := by
    intro t ht
    simp only [hPdef, hQdef]
    congr 1
    funext u
    rw [hfb t ht]
  have hmain := integral_moving_split_subst hab hx hy hPc hPQ hxdec hydec hxb hyb hxle hyle hord hs
  have hQeq : (∫ t in (-profileX 1)..(profileX 1), Q t) = RyaboginVolterra.Xi2 n h s := by
    simp only [hQdef, RyaboginVolterra.Xi2, RyaboginVolterra.line, RyaboginVolterra.lineSlope]
  have hSum : (∫ σ in s..b, (P (-x σ) * deriv x σ + P (y σ) * deriv y σ))
      = (∫ σ in s..b,
          (RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ)) 3) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ' : σ ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hs.2] at hσ
      exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
    have hy1 := (hxy σ hσ').1
    have hx1 := (hxy σ hσ').2
    simp only [hPdef]
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Theta, RyaboginVolterra.stateOf,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope, hx1, hy1]
  rw [hmain, hQeq, hSum]

/-- **The second row identity, at finite smoothness.**  Interval-restricted version of
`iteratedDeriv_momentH_eq_volterra_row_Ioo` with `ContDiff ℝ ∞ f` weakened to `ContDiff ℝ n f`. -/
lemma iteratedDeriv_momentH_eq_volterra_row_Ioo_fin (n : ℕ) (hn : 2 ≤ n) {a b : ℝ}
    (hab : a ≤ b) {h x y f : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hf : ContDiff ℝ n f)
    (hxy : ∀ u ∈ Set.Icc a b, f (y u) ^ 2 = (u * y u + h u) ^ 2 ∧
      f (-x u) ^ 2 = (u * (-x u) + h u) ^ 2)
    (hxdec : ∀ σ ∈ Set.Ioo a b, deriv x σ ≤ 0) (hydec : ∀ σ ∈ Set.Ioo a b, deriv y σ ≤ 0)
    (hxb : x b = profileX 1) (hyb : y b = profileX 1)
    (hfb : ∀ t ∈ Set.Icc (-profileX 1) (profileX 1), f t ^ 2 = 1 - t ^ 2)
    (hxle : ∀ s ∈ Set.Icc a b, x b ≤ x s) (hyle : ∀ s ∈ Set.Icc a b, y b ≤ y s)
    (hord : -x b ≤ y b) :
    ∀ s ∈ Set.Ioo a b,
      iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n h x y f u) s =
        (RyaboginVolterra.G n h s (RyaboginVolterra.stateOf x y s)) 3
          - ((∫ σ in s..b,
                RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf x y σ))
              + RyaboginVolterra.Xi n h s) 3 := by
  intro s hs
  have hlen : ((n : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
  have hh' : ContDiff ℝ n h := hh.of_le hlen
  have hh2 : ContDiff ℝ (n + 1) h := hh.of_le (le_of_lt
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1))))
  have hx' : ContDiff ℝ n x := hx.of_le hlen
  have hy' : ContDiff ℝ n y := hy.of_le hlen
  have hF : ContDiff ℝ n
      (fun p : ℝ × ℝ => RyaboginVolterra.centroidIntegrand n h f p.1 p.2) := by
    unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
    fun_prop
  have hleib := Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints
    (k := n) (F := fun u t : ℝ => RyaboginVolterra.centroidIntegrand n h f u t)
    (a := fun u : ℝ => -x u) (b := y) hF (hx.neg.of_le hlen) (hy.of_le hlen) (s := s)
  have hbt := boundaryTerm_centroidIntegrand_eq_G_row3_Ioo (n := n) hn hh.contDiffOn
    hx.contDiffOn hy.contDiffOn hxy s hs
  have hrow := integral_iteratedDeriv_momentH_eq_Icc_fin n hab hh hx hy hf hxy hxdec hydec hxb hyb
    hfb hxle hyle hord ⟨hs.1.le, hs.2.le⟩
  have hsplit : iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n h x y f u) s
      = iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n h x y f u) s - 0 := by ring
  have hXi : (RyaboginVolterra.Xi n h s) 3 = -(RyaboginVolterra.Xi2 n h s) := by
    simp [RyaboginVolterra.mk4, RyaboginVolterra.Xi]
  unfold RyaboginVolterra.momentH
  rw [hleib, hbt]
  unfold RyaboginVolterra.centroidIntegrand RyaboginVolterra.line RyaboginVolterra.lineSlope
  rw [hrow, WithLp.ofLp_add, Pi.add_apply, hXi,
    intervalIntegral_apply_fin (continuous_Theta_integrand n hh hx hy s) (a := s) (b := b) 3]
  ring

end Commons.Geometry.Ulam
end

-- ===== FILE _moving.lean =====

noncomputable section

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.Geometry.Ulam

open RyaboginVolterra

/-- The constant `(-2)^n n!` of the second row of `baseG`. -/
noncomputable def jA (n : ℕ) : ℝ := (-2 : ℝ) ^ n * (n.factorial : ℝ)

/-- The constant `(-2)^(n-1) (n-1)!` of the third row of `baseG`. -/
noncomputable def jB (n : ℕ) : ℝ := (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)

/-- The `(2,0)`-entry of the Jacobian of `baseG` at `(s, baseZ s)`. -/
noncomputable def jAlpha (n : ℕ) (s : ℝ) : ℝ :=
  2 * jA n * (n : ℝ) * s * profileX s * (s * profileX s ^ 2) ^ (n - 1) * deriv profileX s

/-- The `(2,2)`-entry of the Jacobian of `baseG` at `(s, baseZ s)`. -/
noncomputable def jBeta (n : ℕ) (s : ℝ) : ℝ := jA n * (s * profileX s ^ 2) ^ n

/-- The `(3,0)`-entry of the Jacobian of `baseG` at `(s, baseZ s)`. -/
noncomputable def jGamma (n : ℕ) (s : ℝ) : ℝ :=
  -jB n * (2 * (n : ℝ) - 1) * (s * profileX s ^ 2) ^ (n - 1) * deriv profileX s

/-- The `(3,2)`-entry of the Jacobian of `baseG` at `(s, baseZ s)`. -/
noncomputable def jDelta (n : ℕ) (s : ℝ) : ℝ :=
  -jB n * (s * profileX s ^ 2) ^ (n - 1) * profileX s

/-- The Jacobian of `z ↦ baseG n s z` at `baseZ s`, as an explicit linear map. -/
noncomputable def jacLin (n : ℕ) (s : ℝ) : VS →ₗ[ℝ] VS :=
  { toFun := fun v => mk4 (v 0) (v 1)
      (jAlpha n s * v 0 + jAlpha n s * v 1 + jBeta n s * v 2 + jBeta n s * v 3)
      (jGamma n s * v 0 - jGamma n s * v 1 + jDelta n s * v 2 - jDelta n s * v 3)
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp [RyaboginVolterra.mk4_apply] <;> ring
    map_smul' := by
      intro c v
      ext i
      fin_cases i <;> simp [RyaboginVolterra.mk4_apply] <;> ring }

@[simp] lemma jacLin_apply_zero (n : ℕ) (s : ℝ) (v : VS) : jacLin n s v 0 = v 0 := by
  simp [jacLin, RyaboginVolterra.mk4_apply]

@[simp] lemma jacLin_apply_one (n : ℕ) (s : ℝ) (v : VS) : jacLin n s v 1 = v 1 := by
  simp [jacLin, RyaboginVolterra.mk4_apply]

lemma jacLin_apply_two (n : ℕ) (s : ℝ) (v : VS) :
    jacLin n s v 2 = jAlpha n s * v 0 + jAlpha n s * v 1 + jBeta n s * v 2
      + jBeta n s * v 3 := by
  simp [jacLin, RyaboginVolterra.mk4_apply]

lemma jacLin_apply_three (n : ℕ) (s : ℝ) (v : VS) :
    jacLin n s v 3 = jGamma n s * v 0 - jGamma n s * v 1 + jDelta n s * v 2
      - jDelta n s * v 3 := by
  simp [jacLin, RyaboginVolterra.mk4_apply]

/-- The inverse of `jacLin` as an explicit linear map (valid for `s > 0`). -/
noncomputable def iaLin (n : ℕ) (s : ℝ) : VS →ₗ[ℝ] VS :=
  { toFun := fun v => mk4 (v 0) (v 1)
      ((-jAlpha n s / (2 * jBeta n s) - jGamma n s / (2 * jDelta n s)) * v 0
        + (-jAlpha n s / (2 * jBeta n s) + jGamma n s / (2 * jDelta n s)) * v 1
        + (1 / (2 * jBeta n s)) * v 2 + (1 / (2 * jDelta n s)) * v 3)
      ((-jAlpha n s / (2 * jBeta n s) + jGamma n s / (2 * jDelta n s)) * v 0
        + (-jAlpha n s / (2 * jBeta n s) - jGamma n s / (2 * jDelta n s)) * v 1
        + (1 / (2 * jBeta n s)) * v 2 - (1 / (2 * jDelta n s)) * v 3)
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp [RyaboginVolterra.mk4_apply] <;> ring
    map_smul' := by
      intro c v
      ext i
      fin_cases i <;> simp [RyaboginVolterra.mk4_apply] <;> ring }

@[simp] lemma iaLin_apply_zero (n : ℕ) (s : ℝ) (v : VS) : iaLin n s v 0 = v 0 := by
  simp [iaLin, RyaboginVolterra.mk4_apply]

@[simp] lemma iaLin_apply_one (n : ℕ) (s : ℝ) (v : VS) : iaLin n s v 1 = v 1 := by
  simp [iaLin, RyaboginVolterra.mk4_apply]

lemma iaLin_apply_two (n : ℕ) (s : ℝ) (v : VS) :
    iaLin n s v 2 = (-jAlpha n s / (2 * jBeta n s) - jGamma n s / (2 * jDelta n s)) * v 0
        + (-jAlpha n s / (2 * jBeta n s) + jGamma n s / (2 * jDelta n s)) * v 1
        + (1 / (2 * jBeta n s)) * v 2 + (1 / (2 * jDelta n s)) * v 3 := by
  simp [iaLin, RyaboginVolterra.mk4_apply]

lemma iaLin_apply_three (n : ℕ) (s : ℝ) (v : VS) :
    iaLin n s v 3 = (-jAlpha n s / (2 * jBeta n s) + jGamma n s / (2 * jDelta n s)) * v 0
        + (-jAlpha n s / (2 * jBeta n s) - jGamma n s / (2 * jDelta n s)) * v 1
        + (1 / (2 * jBeta n s)) * v 2 - (1 / (2 * jDelta n s)) * v 3 := by
  simp [iaLin, RyaboginVolterra.mk4_apply]


lemma jBeta_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : jBeta n s ≠ 0 := by
  have h1 : (s * profileX s ^ 2) ≠ 0 :=
    ne_of_gt (mul_pos hs (pow_pos (profileX_pos s hs) 2))
  unfold jBeta jA
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
    (pow_ne_zero _ h1)

lemma jDelta_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : jDelta n s ≠ 0 := by
  have h1 : (s * profileX s ^ 2) ≠ 0 :=
    ne_of_gt (mul_pos hs (pow_pos (profileX_pos s hs) 2))
  have h2 : (-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  unfold jDelta jB
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) (pow_ne_zero _ h1))
    (ne_of_gt (profileX_pos s hs))

/-- `iaLin` is a left inverse of `jacLin` (for `s > 0`). -/
lemma iaLin_jacLin {n : ℕ} {s : ℝ} (hs : 0 < s) (v : VS) :
    iaLin n s (jacLin n s v) = v := by
  have hb : jBeta n s ≠ 0 := jBeta_ne_zero hs
  have hd : jDelta n s ≠ 0 := jDelta_ne_zero hs
  ext i
  fin_cases i
  · show iaLin n s (jacLin n s v) 0 = v 0
    rw [iaLin_apply_zero, jacLin_apply_zero]
  · show iaLin n s (jacLin n s v) 1 = v 1
    rw [iaLin_apply_one, jacLin_apply_one]
  · show iaLin n s (jacLin n s v) 2 = v 2
    rw [iaLin_apply_two, jacLin_apply_two, jacLin_apply_zero, jacLin_apply_one,
      jacLin_apply_three]
    field_simp [mul_ne_zero two_ne_zero hb, mul_ne_zero two_ne_zero hd]
    ring
  · show iaLin n s (jacLin n s v) 3 = v 3
    rw [iaLin_apply_three, jacLin_apply_three, jacLin_apply_zero, jacLin_apply_one,
      jacLin_apply_two]
    field_simp [mul_ne_zero two_ne_zero hb, mul_ne_zero two_ne_zero hd]
    ring

/-- `iaLin` is a right inverse of `jacLin` (for `s > 0`). -/
lemma jacLin_iaLin {n : ℕ} {s : ℝ} (hs : 0 < s) (v : VS) :
    jacLin n s (iaLin n s v) = v := by
  have hb : jBeta n s ≠ 0 := jBeta_ne_zero hs
  have hd : jDelta n s ≠ 0 := jDelta_ne_zero hs
  ext i
  fin_cases i
  · show jacLin n s (iaLin n s v) 0 = v 0
    rw [jacLin_apply_zero, iaLin_apply_zero]
  · show jacLin n s (iaLin n s v) 1 = v 1
    rw [jacLin_apply_one, iaLin_apply_one]
  · show jacLin n s (iaLin n s v) 2 = v 2
    rw [jacLin_apply_two, iaLin_apply_two, iaLin_apply_zero, iaLin_apply_one,
      iaLin_apply_three]
    field_simp [mul_ne_zero two_ne_zero hb, mul_ne_zero two_ne_zero hd]
    ring
  · show jacLin n s (iaLin n s v) 3 = v 3
    rw [jacLin_apply_three, iaLin_apply_three, iaLin_apply_zero, iaLin_apply_one,
      iaLin_apply_two]
    field_simp [mul_ne_zero two_ne_zero hb, mul_ne_zero two_ne_zero hd]
    ring

lemma jacLin_injective {n : ℕ} {s : ℝ} (hs : 0 < s) : Function.Injective (jacLin n s) := by
  intro v w hvw
  have h : jacLin n s (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h2 := congrArg (iaLin n s) h
  rw [iaLin_jacLin hs] at h2
  simp only [map_zero] at h2
  exact sub_eq_zero.mp h2

lemma jacLin_surjective {n : ℕ} {s : ℝ} (hs : 0 < s) : Function.Surjective (jacLin n s) :=
  fun v => ⟨iaLin n s v, jacLin_iaLin hs v⟩

lemma iaLin_isInverse {n : ℕ} {s : ℝ} (hs : 0 < s) :
    (iaLin n s).comp (jacLin n s) = 1 := by
  ext v
  simp [iaLin_jacLin hs v]


/-- **The Jacobian of `baseG` at the base point.**  For `s ∈ ℝ` and `2 ≤ n`,
`jacLin n s` is the derivative of `z ↦ baseG n s z` at `baseZ s`. -/
theorem jacLin_eq_fderiv {n : ℕ} (hn : 2 ≤ n) (s : ℝ) :
    (jacLin n s).toContinuousLinearMap = fderiv ℝ (fun z : VS => baseG n s z) (baseZ s) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- the curve `t ↦ baseZ s + t • v`
  have hcurve : ∀ v : VS, HasDerivAt (fun t : ℝ => baseG n s (baseZ s + t • v))
      ((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v) 0 := by
    intro v
    have hd := baseG_differentiableAt n s (baseZ s)
    have hc : HasDerivAt (fun t : ℝ => baseZ s + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const v
      simpa using h1.const_add (baseZ s)
    have hd' : HasFDerivAt (fun z : VS => baseG n s z)
        (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) (baseZ s + (0 : ℝ) • v) := by
      simpa using hd.hasFDerivAt
    have hmain := hd'.comp_hasDerivAt 0 hc
    refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    rfl
  -- componentwise derivatives
  have hbase0 : ∀ (v : VS) (t : ℝ), (baseZ s + t • v) 0 = profileX s + t * v 0 := by
    intro v t; simp [baseZ_apply_zero]
  have hbase1 : ∀ (v : VS) (t : ℝ), (baseZ s + t • v) 1 = profileX s + t * v 1 := by
    intro v t; simp [baseZ_apply_one]
  have hbase2 : ∀ (v : VS) (t : ℝ), (baseZ s + t • v) 2 = deriv profileX s + t * v 2 := by
    intro v t; simp [baseZ_apply_two]
  have hbase3 : ∀ (v : VS) (t : ℝ), (baseZ s + t • v) 3 = deriv profileX s + t * v 3 := by
    intro v t; simp [baseZ_apply_three]
  apply ContinuousLinearMap.ext
  intro v
  have hc0 : (jacLin n s v).ofLp 0 = ((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 0 := by
    have hcurve0 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 0)
        (((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 0) 0 := by
      have hthis := (EuclideanSpace.proj (0 : Fin 4)).hasFDerivAt.comp_hasDerivAt 0 (hcurve v)
      refine hthis.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
    have hd0 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 0) (v.ofLp 0) 0 := by
      have hfun : (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 0)
          = fun t : ℝ => profileX s + t * v.ofLp 0 := by
        funext t
        rw [baseG_apply_zero]
        exact hbase0 v t
      rw [hfun]
      have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 0) (1 * v.ofLp 0) 0 :=
        (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 0)
      simpa using (h1.const_add (profileX s)).congr_deriv (by ring)
    rw [jacLin_apply_zero]
    exact (hcurve0.unique hd0).symm
  have hc1 : (jacLin n s v).ofLp 1 = ((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 1 := by
    have hcurve1 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 1)
        (((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 1) 0 := by
      have hthis := (EuclideanSpace.proj (1 : Fin 4)).hasFDerivAt.comp_hasDerivAt 0 (hcurve v)
      refine hthis.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
    have hd1 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 1) (v.ofLp 1) 0 := by
      have hfun : (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 1)
          = fun t : ℝ => profileX s + t * v.ofLp 1 := by
        funext t
        rw [baseG_apply_one]
        exact hbase1 v t
      rw [hfun]
      have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 1) (1 * v.ofLp 1) 0 :=
        (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 1)
      simpa using (h1.const_add (profileX s)).congr_deriv (by ring)
    rw [jacLin_apply_one]
    exact (hcurve1.unique hd1).symm
  have hc2 : (jacLin n s v).ofLp 2 = ((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 2 := by
    have hcurve2 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 2)
        (((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 2) 0 := by
      have hthis := (EuclideanSpace.proj (2 : Fin 4)).hasFDerivAt.comp_hasDerivAt 0 (hcurve v)
      refine hthis.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
    have hd2 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 2)
        (jAlpha n s * v.ofLp 0 + jAlpha n s * v.ofLp 1 + jBeta n s * v.ofLp 2
          + jBeta n s * v.ofLp 3) 0 := by
      have hfun : (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 2) = fun t : ℝ =>
          jA n * ((s * (profileX s + t * v.ofLp 0) ^ 2) ^ n * (deriv profileX s + t * v.ofLp 2)
            + (s * (profileX s + t * v.ofLp 1) ^ 2) ^ n * (deriv profileX s + t * v.ofLp 3)) := by
        funext t
        rw [baseG_apply_two]
        rw [hbase0 v t, hbase1 v t, hbase2 v t, hbase3 v t]
        unfold jA
        rfl
      rw [hfun]
      have hp0 : HasDerivAt (fun t : ℝ => profileX s + t * v.ofLp 0) (v.ofLp 0) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 0) (1 * v.ofLp 0) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 0)
        simpa using h1.const_add (profileX s)
      have hs0 : HasDerivAt (fun t : ℝ => s * (profileX s + t * v.ofLp 0) ^ 2)
          (2 * s * profileX s * v.ofLp 0) 0 := by
        have h2 := (hp0.pow 2).const_mul s
        exact h2.congr_deriv (by ring)
      have hpow0 : HasDerivAt (fun t : ℝ => (s * (profileX s + t * v.ofLp 0) ^ 2) ^ n)
          ((n : ℝ) * (s * profileX s ^ 2) ^ (n - 1) * (2 * s * profileX s * v.ofLp 0)) 0 :=
        (hs0.pow n).congr_deriv (by simp only [mul_zero, add_zero]; push_cast [hn1]; ring)
      have hp2 : HasDerivAt (fun t : ℝ => deriv profileX s + t * v.ofLp 2) (v.ofLp 2) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 2) (1 * v.ofLp 2) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 2)
        simpa using h1.const_add (deriv profileX s)
      have ht0 := hpow0.mul hp2
      have hp1 : HasDerivAt (fun t : ℝ => profileX s + t * v.ofLp 1) (v.ofLp 1) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 1) (1 * v.ofLp 1) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 1)
        simpa using h1.const_add (profileX s)
      have hs1 : HasDerivAt (fun t : ℝ => s * (profileX s + t * v.ofLp 1) ^ 2)
          (2 * s * profileX s * v.ofLp 1) 0 := by
        have h2 := (hp1.pow 2).const_mul s
        exact h2.congr_deriv (by ring)
      have hpow1 : HasDerivAt (fun t : ℝ => (s * (profileX s + t * v.ofLp 1) ^ 2) ^ n)
          ((n : ℝ) * (s * profileX s ^ 2) ^ (n - 1) * (2 * s * profileX s * v.ofLp 1)) 0 :=
        (hs1.pow n).congr_deriv (by simp only [mul_zero, add_zero]; push_cast [hn1]; ring)
      have hp3 : HasDerivAt (fun t : ℝ => deriv profileX s + t * v.ofLp 3) (v.ofLp 3) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 3) (1 * v.ofLp 3) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 3)
        simpa using h1.const_add (deriv profileX s)
      have ht1 := hpow1.mul hp3
      have hsum := (ht0.add ht1).const_mul (jA n)
      refine hsum.congr_deriv ?_
      unfold jAlpha jBeta jA
      push_cast [hn1]
      ring_nf
    rw [jacLin_apply_two]
    exact (hcurve2.unique hd2).symm
  have hc3 : (jacLin n s v).ofLp 3 = ((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 3 := by
    have hcurve3 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 3)
        (((fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v).ofLp 3) 0 := by
      have hthis := (EuclideanSpace.proj (3 : Fin 4)).hasFDerivAt.comp_hasDerivAt 0 (hcurve v)
      refine hthis.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
    have hd3 : HasDerivAt (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 3)
        (jGamma n s * v.ofLp 0 - jGamma n s * v.ofLp 1 + jDelta n s * v.ofLp 2
          - jDelta n s * v.ofLp 3) 0 := by
      have hfun : (fun t : ℝ => (baseG n s (baseZ s + t • v)).ofLp 3) = fun t : ℝ =>
          jB n * ((s * (profileX s + t * v.ofLp 0) ^ 2) ^ (n - 1)
              * (-(profileX s + t * v.ofLp 0) * (deriv profileX s + t * v.ofLp 2))
            + (s * (profileX s + t * v.ofLp 1) ^ 2) ^ (n - 1)
              * ((profileX s + t * v.ofLp 1) * (deriv profileX s + t * v.ofLp 3))) := by
        funext t
        rw [baseG_apply_three]
        rw [hbase0 v t, hbase1 v t, hbase2 v t, hbase3 v t]
        unfold jB
        rfl
      rw [hfun]
      unfold jGamma jDelta
      generalize hA : s * profileX s ^ 2 = A
      have h2 : n - 1 - 1 + 1 = n - 1 := Nat.sub_add_cancel (show 1 ≤ n - 1 by omega)
      have hApow : A ^ (n - 1) = A ^ (n - 1 - 1) * A := by rw [← pow_succ, h2]
      have hp0 : HasDerivAt (fun t : ℝ => profileX s + t * v.ofLp 0) (v.ofLp 0) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 0) (1 * v.ofLp 0) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 0)
        simpa using h1.const_add (profileX s)
      have hp1 : HasDerivAt (fun t : ℝ => profileX s + t * v.ofLp 1) (v.ofLp 1) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 1) (1 * v.ofLp 1) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 1)
        simpa using h1.const_add (profileX s)
      have hp2 : HasDerivAt (fun t : ℝ => deriv profileX s + t * v.ofLp 2) (v.ofLp 2) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 2) (1 * v.ofLp 2) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 2)
        simpa using h1.const_add (deriv profileX s)
      have hp3 : HasDerivAt (fun t : ℝ => deriv profileX s + t * v.ofLp 3) (v.ofLp 3) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * v.ofLp 3) (1 * v.ofLp 3) 0 :=
          (hasDerivAt_id (0 : ℝ)).mul_const (v.ofLp 3)
        simpa using h1.const_add (deriv profileX s)
      have hs0 : HasDerivAt (fun t : ℝ => s * (profileX s + t * v.ofLp 0) ^ 2)
          (2 * s * profileX s * v.ofLp 0) 0 := by
        have h2 := (hp0.pow 2).const_mul s
        exact h2.congr_deriv (by ring)
      have hpow0 : HasDerivAt (fun t : ℝ => (s * (profileX s + t * v.ofLp 0) ^ 2) ^ (n - 1))
          (((n : ℝ) - 1) * A ^ (n - 1 - 1)
            * (2 * s * profileX s * v.ofLp 0)) 0 :=
        (hs0.pow (n - 1)).congr_deriv (by
          simp only [mul_zero, zero_mul, add_zero]
          rw [hA]
          push_cast [hn1]
          ring)
      have hprod0 : HasDerivAt
          (fun t : ℝ => -(profileX s + t * v.ofLp 0) * (deriv profileX s + t * v.ofLp 2))
          (-(v.ofLp 0) * deriv profileX s - profileX s * v.ofLp 2) 0 := by
        have h2 := hp0.neg.mul hp2
        exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)
      have ht0 := hpow0.mul hprod0
      have hs1 : HasDerivAt (fun t : ℝ => s * (profileX s + t * v.ofLp 1) ^ 2)
          (2 * s * profileX s * v.ofLp 1) 0 := by
        have h2 := (hp1.pow 2).const_mul s
        exact h2.congr_deriv (by ring)
      have hpow1 : HasDerivAt (fun t : ℝ => (s * (profileX s + t * v.ofLp 1) ^ 2) ^ (n - 1))
          (((n : ℝ) - 1) * A ^ (n - 1 - 1)
            * (2 * s * profileX s * v.ofLp 1)) 0 :=
        (hs1.pow (n - 1)).congr_deriv (by
          simp only [mul_zero, zero_mul, add_zero]
          rw [hA]
          push_cast [hn1]
          ring)
      have hprod1 : HasDerivAt
          (fun t : ℝ => (profileX s + t * v.ofLp 1) * (deriv profileX s + t * v.ofLp 3))
          (v.ofLp 1 * deriv profileX s + profileX s * v.ofLp 3) 0 := by
        have h2 := hp1.mul hp3
        exact h2.congr_deriv (by ring)
      have ht1 := hpow1.mul hprod1
      have hsum := (ht0.add ht1).const_mul (jB n)
      have h2 : n - 1 - 1 + 1 = n - 1 := Nat.sub_add_cancel (show 1 ≤ n - 1 by omega)
      have hpow'' : (s * profileX s ^ 2) ^ (n - 1)
          = (s * profileX s ^ 2) ^ (n - 1 - 1) * (s * profileX s ^ 2) := by
        rw [← pow_succ, h2]
      refine hsum.congr_deriv ?_
      simp only [zero_mul, mul_zero, add_zero]
      rw [← hA, hpow'']
      ring
    rw [jacLin_apply_three]
    exact (hcurve3.unique hd3).symm
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3
/-- `jacLin n s` as a continuous linear equivalence (valid for `s > 0`). -/
noncomputable def jacEquiv (n : ℕ) {s : ℝ} (hs : 0 < s) : VS ≃L[ℝ] VS :=
  ContinuousLinearEquiv.ofBijective (σ := RingHom.id ℝ) ((jacLin n s).toContinuousLinearMap)
    (by
      rw [LinearMap.ker_eq_bot]
      exact jacLin_injective hs)
    (by
      rw [LinearMap.range_eq_top]
      exact jacLin_surjective hs)

lemma jacEquiv_apply (n : ℕ) {s : ℝ} (hs : 0 < s) (v : VS) :
    jacEquiv n hs v = jacLin n s v := rfl

lemma jacEquiv_symm_apply (n : ℕ) {s : ℝ} (hs : 0 < s) (v : VS) :
    (jacEquiv n hs).symm v = iaLin n s v := by
  refine jacLin_injective (n := n) hs ?_
  show jacLin n s ((jacEquiv n hs).symm v) = jacLin n s (iaLin n s v)
  rw [show jacLin n s ((jacEquiv n hs).symm v) = jacEquiv n hs ((jacEquiv n hs).symm v) from
    (jacEquiv_apply n hs _).symm]
  rw [ContinuousLinearEquiv.apply_symm_apply, jacLin_iaLin hs v]

end Commons.Geometry.Ulam
end

-- ===== FILE honest_perturbation_tau.lean =====

/-!
# `honest_perturbation_tau` — the keystone local-perturbation lemma (even dimensions)

Target (Ryabogin, *A negative answer to Ulam's Problem 19 from the Scottish Book*,
Ann. of Math. **195** (2022), Section "The case of even `d ≥ 4"): for `0 < τ`, `2 τ < 1` and a
smooth bump `h` with `support h ⊆ [1 - 2 τ, 1 - τ]`, `h ≠ 0`, flat at the left end of its
support, there are `ε > 0` and functions `x y f` with

* `f` smooth on `(-1,1)`, `support f ⊆ [-1,1]`, `f` strictly concave on `[-1,1]`, `f (±1) = 0`,
  `f > 0` on `(-1,1)`;
* `f (y s) = s * y s + (ε • h) s`, `f (-x s) = -(s * (-x s) + (ε • h) s)` for all `s > 0`;
* the two moment identities
  `∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n = momentRHS n s` and
  `∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) * (t + deriv (ε • h) s) = 0`.

## Machinery used

`Submission/Work/Geometry/Ulam/_tau_base.lean` (imported below for fast iteration — it must be
*inlined* into this file before `declare_proven`, since a commons file may import only Mathlib and
other commons modules) contains, all proved, the paper's reduction to a `4 × 4` Volterra system:

* `Commons.Analysis.Calculus.iteratedDeriv_intervalIntegral_moving_endpoints` (Leibniz formula with
  moving endpoints), `..._eq_zero_of_eq_zero_on_subinterval`;
* namespace `RyaboginVolterra`: `State = EuclideanSpace ℝ (Fin 4)`, `line`, `lineSlope`,
  `momentIntegrand`, `centroidIntegrand`, `momentF`, `momentH`, `momentRHS`, `endpointC`,
  `endpointD`, `G`, `Theta`, `Xi1`, `Xi2`, `Xi`, `baseState`, `stateOf`;
* `integral_moving_split_subst`, `integral_iteratedDeriv_momentF_eq`, `..._momentH_eq`;
* the two **row identities** `iteratedDeriv_momentF_eq_volterra_row` and
  `iteratedDeriv_momentH_eq_volterra_row`: for data `(h, x, y, f)` on `[a,b]`,
  `(d/ds)^(n+1) momentF = (G-row2) - ∫ Θ-row2 + Ξ-row2` and
  `(d/ds)^n momentH = (G-row3) - ∫ Θ-row3 + Ξ-row3`;
* the base data `baseG = G n 0`, `baseΘ`, `baseΞ`, `baseZ = baseState` and the **base identity**
  `volterra_base_identity` (for `0 < a ≤ s ≤ 1`), the det certificate
  `baseG_fderiv_det_ne_zero` (and `volterra_unperturbed_det_ne_zero` in the commons), continuity
  of the base data, and the *normalised/scaled* data `TG`, `TΘ`, `TΞ` with `TG_fderiv_base`,
  `Tbase_identity` (the scaled base solution is the constant zero function `Z₀ = 0`, whose
  continuity modulus is unlimited in the abstract theorem below — this is why the scaled
  formulation is used).

## Remaining pieces and the pitfalls

1. `honest_volterra_solution` (the main gap).  Apply
   `Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small` to the scaled base data
   `(TG, TΘ, TΞ, Z₀ = 0)` and the scaled perturbed data `(Gn, Thn, Xin)` built from `ε • h`.
   Needed inputs: the closeness of the perturbed data to the base data and the Lipschitz
   constants `K_G`, `L_Θ` on the unit ball with
   `K_G + ‖Qe.symm‖ * L_Θ * (b - a) < 1`.
   *Pitfall A (τ range).*  The theorem's conclusion only gives the solution on
   `[b - 3δ, b]` for an existential `δ ≤ (b-a)/3`, and in the proof
   `δ = min ((b-a)/3, δ_Z/4)` where `δ_Z` is a continuity modulus of the base solution.  For the
   unscaled data, `baseZ` varies by `> 1/2` on `[0,1]`, so `δ` is not controlled; using the
   *scaled* data (`Z₀ = 0`) removes this obstruction and yields
   `[b - 3δ, b] ⊇ [b - min (b-a) (3/4), b]`.  For `τ > 3/8` this still does not reach
   `1 - 2τ`; one then *continues* the solution to the left: on a subinterval `[a', b']` with
   `b' = b - 3δ` replace `Ξ` by `Ξ*(s) = Ξ s + ∫ σ in b'..b, Θ s σ (Z σ)` (and likewise for the
   base data), which is again a base identity (split the integral), and apply the theorem again.
   *Pitfall B (base identity at `s = 0`).*  All base-data lemmas in `_tau_base` require `0 < a`.
   For the interval `[a, 1]` with `a > 0` this is fine; if one wants `a = 0` (e.g. with the
   `_unit` variant) the identity extends by continuity from `(0,1]`.
   *Pitfall C (smoothness of the solution).*  The abstract theorem returns only a *continuous*
   `Z` with `dist (Z s) (Z₀ s) < 1/2`.  For the cap `f` one needs `Z s = (x s, y s, x' s, y' s)`
   with `x, y ∈ C²` close to `profileX`.  Two steps: (i) `Z 1 = baseState 1` follows immediately
   from the equation at `s = 1` together with `h = 0` near `1` and the invertibility of the
   `2 × 2` matrix `A` (`volterra_unperturbed_det_ne_zero`); (ii) on `[1-τ, 1]` the equation is
   unperturbed and self-contained, so the contraction gives `Z = baseState` there; the *regularity*
   of `Z` (hence `x'', y''`) then follows from the Volterra fixed-point equation by the
   bootstrap/Gronwall argument (commons: `contDiffOn_of_continuous_volterra_fixedPoint`).
2. `moment_identities_from_volterra`: the row identities turn the fixed-point equation into
   `(d/ds)^(n+1) (momentF - momentRHS) = 0` and `(d/ds)^n momentH = 0` on the solution interval;
   with `Z = baseState` on `[1-τ,1]` both errors vanish there (the semicircle is the unperturbed
   solution), so they vanish on the whole solution interval.
3. `propagation_to_small_s` (paper Steps 3 and 4): on `[c, 1-2τ+η]` (`h = 0`) the differentiated
   identities force `x = y = profileX` (compare `∫ t^(2n-1)` and `∫ t^(2n)`); on `(0, 1-2τ)`
   (where `h = 0`) set `x = y = profileX`; then the error
   `F(s) = ∫ t in (-profileX s)..(profileX s), (f t ^ 2 - (s*t)^2)^n - momentRHS n s`
   equals the *polynomial* `G(s) = ∫ t in D, ((f t ^ 2 - (s*t)^2)^n - ((1-t^2) - (s*t)^2)^n)`
   (`D` = the modification region, contained in the interval for `s ≤ 1 - 2τ`), which vanishes
   on the anchor `[c, 1-2τ]`; hence `F ≡ 0`, and similarly for `momentH`.
4. `exists_profile_of_endpoint_functions` (the envelope): define
   `f t = σ t * t + (ε • h) (σ t)` with `σ = y⁻¹` on `(0,1)` and `σ t = x⁻¹ (-t)` on `(-1,0)`
   (both inverse maps agree near `0` because `x = y = profileX` for `s ≥ 1 - τ`), `f = 0` for
   `|t| ≥ 1`.  Then `f` is `C^∞` by the inverse function theorem
   (`ContDiffAt.to_localInverse`), the endpoint equations hold by construction, and strict
   concavity/positivity follow from `C²`-closeness of `x, y` to `profileX`
   (`f' (y σ) = σ + (y σ + ε h' σ)/y' σ` is strictly increasing).
5. `honest_perturbation_tau`: assemble.

### Item 1 (the Volterra application) — concrete strategy

* **Scaled data.**  Use `TG/TΘ/TΞ` (`submission .../volterra_perturbation_exists_v3_small`
  applied with `G0 := TG n Qe ρ`, `Θ0 := TΘ n Qe ρ`, `Ξ0 := TΞ n Qe ρ`, `Z₀ ≡ 0`,
  `Q := 1`), which removes the `δ_Z` obstruction of Pitfall A.  Contraction
  `K_G + L_Θ * (b - a) < 1` is then available by taking the interval `[1-ℓ, 1]` short and `ρ`
  small: on such a ball `z = baseZ s + ρ • U` is close to `baseZ 1`, so
  `‖1 - Q.symm (D_z G z)‖` is small.  Long intervals are reached by the **leftward
  continuation** (Pitfall A).
* **Better: the "defect" trick.**  For a sub-interval `[a', b']` with a known configuration
  `Z₀`, the base identity can be made to hold *by construction*: take
  `G0 := G`, `Θ0 := Θ` and `Ξ0 s := G s (Z₀ s) - ∫ σ in s..b', Θ s σ (Z₀ σ)`, so the only
  closeness hypothesis left is `‖Ξ - Ξ0‖ < ε`, i.e. the smallness of the *defect*
  `c s = G s (Z₀ s) - ∫ σ in s..b', Θ s σ (Z₀ σ) - Ξ s`.  By the row identities this defect is
  the `(n+1)`-st derivative of the moment error of the *known* configuration, hence
  `O(ε)` — but it does involve the derivatives of `h`, so the analytic core is not removed, only
  concentrated in one scalar function.
* **Closeness of `Θ` and `Ξ`** (no Faà-di-Bruno by hand): use
  `contDiffOn_parametric_iteratedDeriv_prod` (parameter space `P = ℝ × ℝ × VS` for
  `(ε, σ, Z)`), which gives smoothness — hence continuity — of
  `(ε, σ, Z, s) ↦ iteratedDeriv k (fun v => Φ(ε, σ, Z, v)) s` for the polynomial `Φ` defining
  `Θ`/`Ξ`; combined with compactness (or the mean value theorem in `ε`) this yields the uniform
  bound `≤ C ε`.
* **Done in this file:**
  * `Gw_lipschitz_ab` (the `(a,b)`-Lipschitz bound for the `G`-data, via
    `exists_bound_fderiv_Gw_ab` + the commons' mean value inequality);
  * `Gn_close_TG` — **the `G`-row of the theorem's closeness hypothesis**;
  * `continuous_scaled_iteratedDeriv`, `continuous_scaled_iteratedDeriv_slope`
    (joint continuity of the parametric `iteratedDeriv` of the `Ξ`-integrands);
  * `Xi1_close`, `Xi2_close`, `Xi_close_base` — **the whole `Ξ`-row** of the closeness
    hypothesis (uniform in `s ∈ [a,1]`).
* **Remaining in item 1:** (i) `‖Θ - Θ0‖` small (same route: joint continuity of
  `(ε, σ, w, v) ↦ iteratedDeriv k (fun v => ((σ * w + ε * h σ)^2 - (v * w + ε * h v)^2)^n) s`
  for the four components `A, B, C, D` of `Θ`, then uniform continuity on the compact);
  (ii) the two Lipschitz-in-`U` bounds `K_G` (from a bound on `D_z Gw`, same compactness route)
  and `L_Θ`; (iii) continuity of the scaled perturbed data; (iv) the application of
  `volterra_perturbation_exists_v3_small` together with the continuation.

## Already proved in this file (the "unperturbed region" infrastructure)

* `h_eq_zero_of_one_sub_lt`, `h_eq_zero_of_lt`, `h_eq_zero_of_notMem`,
  `deriv_h_eq_zero_of_one_sub_lt`, `deriv_h_eq_zero_of_notMem`,
  `iteratedDeriv_h_eq_zero_of_one_sub_lt`, `iteratedDeriv_h_eq_zero_of_notMem`,
  `h_eventually_zero_of_notMem`: `h` (and all its derivatives) vanishes on the complement of the
  perturbation window;
* `G_eq_baseG_at_one`, `Gn_eq_TG_at_one`, `Xi_eq_at_one`, `Xi_eq_base_of_notMem`,
  `Theta_eq_baseΘ_of_notMem`: on the unperturbed region (`s = 1`, or `s ∉ [1-2τ, 1-τ]`) the
  perturbed Volterra data coincides with the base data;
* `baseG_baseState_one`: `G 1 (baseState 1) = Ξ 1`;
* `eq_baseState_one_of_baseG_eq`: **any** state satisfying the unperturbed equation at `s = 1`
  equals `baseState 1` (Pitfall C(i)).

-/

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace Interval

set_option autoImplicit false

namespace Commons.Geometry.Ulam

/-! ## Helper lemmas (proved) -/

/-- `h` vanishes to the right of the support interval. -/
lemma h_eq_zero_of_one_sub_lt {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ} (hs : 1 - τ < s) :
    h s = 0 := by
  by_contra hne
  have hmem := hsupp (by simpa [Function.mem_support] using hne)
  exact absurd hmem.2 (not_le.mpr hs)

/-- Consequently `deriv h` also vanishes there (for smooth `h`). -/
lemma deriv_h_eq_zero_of_one_sub_lt {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ} (hs : 1 - τ < s) :
    deriv h s = 0 := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact h_eq_zero_of_one_sub_lt hsupp ht
  have hd : deriv h s = deriv (fun _ : ℝ => (0 : ℝ)) s := hev.deriv_eq
  simpa using hd

/-- If `h` and `deriv h` vanish at `1`, then the perturbed `G`-data at `s = 1` coincides with
the unperturbed data. -/
lemma G_eq_baseG_at_one {n : ℕ} {h : ℝ → ℝ} (h0 : h 1 = 0) (h1 : deriv h 1 = 0)
    (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h 1 z = baseG n 1 z := by
  rw [G_eq_Gw, baseG, G_eq_Gw]
  simp [h0, h1]

/-- The normalised perturbed `G`-data at `s = 1` coincides with the normalised unperturbed data
(this is what pins down `Z 1 = baseState 1` in the Volterra fixed point). -/
lemma Gn_eq_TG_at_one {n : ℕ} {Qe : VS ≃L[ℝ] VS} {ρ : ℝ} {h : ℝ → ℝ}
    (h0 : h 1 = 0) (h1 : deriv h 1 = 0) :
    Gn n Qe ρ h 1 = TG n Qe ρ 1 := by
  funext U
  simp [Gn, GnW, TG, baseG, G_eq_Gw, h0, h1]

/-- All iterated derivatives of `h` vanish to the right of the perturbation window. -/
lemma iteratedDeriv_h_eq_zero_of_one_sub_lt {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) (j : ℕ) {s : ℝ}
    (hs : 1 - τ < s) : iteratedDeriv j h s = 0 := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact h_eq_zero_of_one_sub_lt hsupp ht
  have := hev.iteratedDeriv_eq (n := j)
  simpa using this

/-- `Ξ` at `s = 1` is insensitive to the perturbation, because `h` and `deriv h` vanish near `1`. -/
lemma Xi_eq_at_one {n : ℕ} {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) (hlt : 1 - τ < 1) :
    RyaboginVolterra.Xi n h 1 = RyaboginVolterra.Xi n (fun _ => 0) 1 := by
  have hzero : ∀ᶠ u in nhds (1 : ℝ), h u = 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
    exact h_eq_zero_of_one_sub_lt hsupp hu
  have hderiv : ∀ᶠ u in nhds (1 : ℝ), deriv h u = 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
    exact deriv_h_eq_zero_of_one_sub_lt hsupp hu
  have hkey1 : ∀ t : ℝ,
      iteratedDeriv (n + 1)
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line h u t) ^ 2) ^ n) 1 =
        iteratedDeriv (n + 1)
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (fun _ => 0) u t) ^ 2) ^ n) 1 := by
    intro t
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hzero] with u hu
    simp [RyaboginVolterra.line, hu]
  have hkey2 : ∀ t : ℝ,
      iteratedDeriv n
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line h u t) ^ 2) ^ (n - 1) *
            RyaboginVolterra.lineSlope h u t) 1 =
        iteratedDeriv n
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (fun _ => 0) u t) ^ 2) ^ (n - 1) *
            RyaboginVolterra.lineSlope (fun _ => 0) u t) 1 := by
    intro t
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hzero, hderiv] with u hu hu'
    simp [RyaboginVolterra.line, RyaboginVolterra.lineSlope, hu, hu']
  have h1 : RyaboginVolterra.Xi1 n h 1 = RyaboginVolterra.Xi1 n (fun _ => 0) 1 :=
    intervalIntegral.integral_congr fun t _ => hkey1 t
  have h2 : RyaboginVolterra.Xi2 n h 1 = RyaboginVolterra.Xi2 n (fun _ => 0) 1 :=
    intervalIntegral.integral_congr fun t _ => hkey2 t
  simp only [RyaboginVolterra.Xi]
  rw [h1, h2]

/-- The unperturbed base identity at the base point `s = 1`: `G 1 (baseState 1) = Ξ 1`. -/
lemma baseG_baseState_one (n : ℕ) (hn : 2 ≤ n) :
    baseG n 1 (RyaboginVolterra.baseState 1) = baseΞ n 1 := by
  have h := volterra_base_identity n hn (a := 1 / 2) (by norm_num) (by norm_num) 1
    ⟨by norm_num, le_rfl⟩
  simpa [baseG, baseΞ, baseZ] using h

/-- **The base point is pinned by the equation at `s = 1`.**  Any state `z` satisfying the
unperturbed equation at `s = 1` must be `baseState 1`: the first two coordinates are `profileX 1`
and the last two are determined by a `2 × 2` linear system whose matrix is invertible
(`volterra_unperturbed_det_ne_zero`). -/
lemma eq_baseState_one_of_baseG_eq (n : ℕ) (hn : 2 ≤ n) {z : RyaboginVolterra.State}
    (hz : baseG n 1 z = baseΞ n 1) : z = RyaboginVolterra.baseState 1 := by
  have hbase := baseG_baseState_one n hn
  have hz0 : z 0 = profileX 1 := by
    have h := congrArg (fun v : VS => v 0) hz
    rw [baseG_apply_zero] at h
    simpa [baseΞ, RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply] using h
  have hz1 : z 1 = profileX 1 := by
    have h := congrArg (fun v : VS => v 1) hz
    rw [baseG_apply_one] at h
    simpa [baseΞ, RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply] using h
  have hbs0 : RyaboginVolterra.baseState 1 0 = profileX 1 := by
    simp [RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  have hbs1 : RyaboginVolterra.baseState 1 1 = profileX 1 := by
    simp [RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  have hr : profileX 1 ^ 2 ≠ 0 := by
    have hpos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
    positivity
  have h2 : (baseG n 1 z) 2 = (baseG n 1 (RyaboginVolterra.baseState 1)) 2 := by rw [hz, hbase]
  have h3 : (baseG n 1 z) 3 = (baseG n 1 (RyaboginVolterra.baseState 1)) 3 := by rw [hz, hbase]
  rw [baseG_apply_two, baseG_apply_two, hz0, hz1, hbs0, hbs1] at h2
  rw [baseG_apply_three, baseG_apply_three, hz0, hz1, hbs0, hbs1] at h3
  have h2' : z 2 + z 3 =
      RyaboginVolterra.baseState 1 2 + RyaboginVolterra.baseState 1 3 := by
    have hc : ((-2 : ℝ) ^ n * (n.factorial : ℝ) * (1 * (profileX 1) ^ 2) ^ n) ≠ 0 := by
      have h1 : ((-2 : ℝ) ^ n) ≠ 0 := by positivity
      have h2 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      positivity
    have := h2
    field_simp at this
    linarith [this]
  have h3' : z 3 - z 2 =
      RyaboginVolterra.baseState 1 3 - RyaboginVolterra.baseState 1 2 := by
    have hc : ((-2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) *
        (1 * (profileX 1) ^ 2) ^ (n - 1)) ≠ 0 := by
      have h1 : ((-2 : ℝ) ^ (n - 1)) ≠ 0 := by positivity
      have h2 : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
      have h3 : (profileX 1) ^ 2 ≠ 0 := hr
      positivity
    have hpos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
    have := h3
    field_simp at this
    nlinarith [this, hpos]
  have hz2 : z 2 = RyaboginVolterra.baseState 1 2 := by linarith
  have hz3 : z 3 = RyaboginVolterra.baseState 1 3 := by linarith
  have hbs2 : RyaboginVolterra.baseState 1 2 = deriv profileX 1 := by
    simp [RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  have hbs3 : RyaboginVolterra.baseState 1 3 = deriv profileX 1 := by
    simp [RyaboginVolterra.baseState, RyaboginVolterra.mk4_apply]
  ext i
  fin_cases i
  · simpa [hbs0] using hz0
  · simpa [hbs1] using hz1
  · simpa [hbs2] using hz2
  · simpa [hbs3] using hz3

/-- `h` vanishes to the left of the support interval. -/
lemma h_eq_zero_of_lt {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ} (hs : s < 1 - 2 * τ) :
    h s = 0 := by
  by_contra hne
  have hmem := hsupp (by simpa [Function.mem_support] using hne)
  exact absurd hmem.1 (not_le.mpr hs)

/-- `h` vanishes at every point outside the closed support interval. -/
lemma h_eq_zero_of_notMem {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) : h s = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · exact h_eq_zero_of_lt hsupp hs
  · exact h_eq_zero_of_one_sub_lt hsupp hs

/-- `deriv h` vanishes at every point outside the closed support interval. -/
lemma deriv_h_eq_zero_of_notMem {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) : deriv h s = 0 := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := by
    have hopen : IsOpen (Set.Icc (1 - 2 * τ) (1 - τ))ᶜ := isClosed_Icc.isOpen_compl
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact h_eq_zero_of_notMem hsupp ht
  have hd : deriv h s = deriv (fun _ : ℝ => (0 : ℝ)) s := hev.deriv_eq
  simpa using hd

/-- Outside the perturbation window the perturbed `G`-data coincides with the unperturbed data. -/
lemma G_eq_baseG_of_notMem {τ : ℝ} {h : ℝ → ℝ} {n : ℕ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) (z : RyaboginVolterra.State) :
    RyaboginVolterra.G n h s z = baseG n s z := by
  rw [G_eq_Gw, baseG, G_eq_Gw]
  simp [h_eq_zero_of_notMem hsupp hs, deriv_h_eq_zero_of_notMem hsupp hs]

/-- `h` vanishes on a whole neighbourhood of any point outside the closed support interval. -/
lemma h_eventually_zero_of_notMem {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) : ∀ᶠ u in nhds s, h u = 0 := by
  have hopen : IsOpen (Set.Icc (1 - 2 * τ) (1 - τ))ᶜ := isClosed_Icc.isOpen_compl
  filter_upwards [hopen.mem_nhds hs] with t ht
  exact h_eq_zero_of_notMem hsupp ht

/-- All iterated derivatives of `h` vanish outside the closed support interval. -/
lemma iteratedDeriv_h_eq_zero_of_notMem {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) (j : ℕ) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) : iteratedDeriv j h s = 0 := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := h_eventually_zero_of_notMem hsupp hs
  have := hev.iteratedDeriv_eq (n := j)
  simpa using this

/-- On the unperturbed region the inhomogeneity `Ξ` coincides with the base one. -/
lemma Xi_eq_base_of_notMem {τ : ℝ} {h : ℝ → ℝ} {n : ℕ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) :
    RyaboginVolterra.Xi n h s = RyaboginVolterra.Xi n (fun _ => 0) s := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := h_eventually_zero_of_notMem hsupp hs
  have hderiv_near : ∀ᶠ u in nhds s, deriv h u = 0 := by
    obtain ⟨V, hVsub, hVopen, hsV⟩ := mem_nhds_iff.mp (show {t : ℝ | h t = 0} ∈ nhds s from by
      have hopen : IsOpen (Set.Icc (1 - 2 * τ) (1 - τ))ᶜ := isClosed_Icc.isOpen_compl
      filter_upwards [hopen.mem_nhds hs] with t ht
      exact h_eq_zero_of_notMem hsupp ht)
    filter_upwards [hVopen.mem_nhds hsV] with u hu
    have heq : h =ᶠ[nhds u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hVopen.mem_nhds hu] with t ht
      exact hVsub ht
    simpa using heq.deriv_eq
  have hkey : ∀ (k : ℕ) (t : ℝ),
      iteratedDeriv k (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line h u t) ^ 2) ^ n) s =
        iteratedDeriv k
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (fun _ => 0) u t) ^ 2) ^ n) s := by
    intro k t
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hev] with u hu
    simp [RyaboginVolterra.line, hu]
  have hkey2 : ∀ (k : ℕ) (t : ℝ),
      iteratedDeriv k (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line h u t) ^ 2) ^ (n - 1) *
          RyaboginVolterra.lineSlope h u t) s =
        iteratedDeriv k
          (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (fun _ => 0) u t) ^ 2) ^ (n - 1) *
            RyaboginVolterra.lineSlope (fun _ => 0) u t) s := by
    intro k t
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hev, hderiv_near] with u hu hud
    simp [RyaboginVolterra.line, RyaboginVolterra.lineSlope, hu, hud]
  have h1 : RyaboginVolterra.Xi1 n h s = RyaboginVolterra.Xi1 n (fun _ => 0) s :=
    intervalIntegral.integral_congr fun t _ => hkey (n + 1) t
  have h2 : RyaboginVolterra.Xi2 n h s = RyaboginVolterra.Xi2 n (fun _ => 0) s :=
    intervalIntegral.integral_congr fun t _ => hkey2 n t
  simp only [RyaboginVolterra.Xi]
  rw [h1, h2]

/-- On the unperturbed region the Volterra kernel `Θ` coincides with the base kernel. -/
lemma Theta_eq_baseΘ_of_notMem {τ : ℝ} {h : ℝ → ℝ} {n : ℕ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {s σ : ℝ}
    (hs : s ∉ Set.Icc (1 - 2 * τ) (1 - τ)) (hσ : σ ∉ Set.Icc (1 - 2 * τ) (1 - τ))
    (Z : RyaboginVolterra.State) :
    RyaboginVolterra.Theta n h s σ Z = baseΘ n s σ Z := by
  have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) := h_eventually_zero_of_notMem hsupp hs
  have hσ0 : h σ = 0 := h_eq_zero_of_notMem hsupp hσ
  have hderiv_near : ∀ᶠ u in nhds s, deriv h u = 0 := by
    obtain ⟨V, hVsub, hVopen, hsV⟩ := mem_nhds_iff.mp (show {t : ℝ | h t = 0} ∈ nhds s from by
      have hopen : IsOpen (Set.Icc (1 - 2 * τ) (1 - τ))ᶜ := isClosed_Icc.isOpen_compl
      filter_upwards [hopen.mem_nhds hs] with t ht
      exact h_eq_zero_of_notMem hsupp ht)
    filter_upwards [hVopen.mem_nhds hsV] with u hu
    have heq : h =ᶠ[nhds u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hVopen.mem_nhds hu] with t ht
      exact hVsub ht
    simpa using heq.deriv_eq
  have hA : ∀ (k : ℕ) (w : ℝ),
      iteratedDeriv k (fun u : ℝ => (RyaboginVolterra.line h σ w ^ 2 -
          RyaboginVolterra.line h u w ^ 2) ^ n) s =
        iteratedDeriv k (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ w ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u w ^ 2) ^ n) s := by
    intro k w
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hev] with u hu
    simp only [RyaboginVolterra.line, Pi.zero_apply, hσ0, hu]
  have hB : ∀ (k : ℕ) (w : ℝ),
      iteratedDeriv k (fun u : ℝ => (RyaboginVolterra.line h σ w ^ 2 -
          RyaboginVolterra.line h u w ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope h u w) s =
        iteratedDeriv k (fun u : ℝ => (RyaboginVolterra.line (fun _ => 0) σ w ^ 2 -
          RyaboginVolterra.line (fun _ => 0) u w ^ 2) ^ (n - 1) *
            RyaboginVolterra.lineSlope (fun _ => 0) u w) s := by
    intro k w
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hev, hderiv_near] with u hu hud
    simp [RyaboginVolterra.line, RyaboginVolterra.lineSlope, Pi.zero_apply, hσ0, hu, hud]
  simp only [RyaboginVolterra.Theta, baseΘ]
  rw [hA (n + 1) (-(Z 0)), hA (n + 1) (Z 1), hB n (-(Z 0)), hB n (Z 1)]

/-! ## Item 1: the perturbed scaled Volterra data is close to the base data

The whole closeness/Lipschitz layer rests on the fact that `Gw` is a polynomial in `(a, b)` whose
coefficients depend smoothly on `(s, z)`; hence `Gw n s a b z - Gw n s 0 0 z` is bounded by
`C * (|a| + |b|)` on the relevant compact region.  We obtain `C` by compactness rather than by an
explicit Faà-di-Bruno computation. -/

/-- The joint map `(a, b, s, z) ↦ Gw n s a b z` is smooth. -/
lemma contDiff_Gw_joint (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) => Gw n q.2.1 q.1.1 q.1.2 q.2.2) :=
  contDiff_Gw n

/-- Derivative of `(a, b) ↦ Gw n s a b z` is the full derivative composed with the inclusion of
the first factor. -/
lemma hasFDerivAt_Gw_ab (n : ℕ) (q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State)) :
    HasFDerivAt (fun p : ℝ × ℝ => Gw n q.2.1 p.1 p.2 q.2.2)
      ((fderiv ℝ (fun q' : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
          Gw n q'.2.1 q'.1.1 q'.1.2 q'.2.2) q).comp
        (ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × RyaboginVolterra.State))) q.1 := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => (p, q.2))
      (ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × RyaboginVolterra.State)) q.1 :=
    hasFDerivAt_prodMk_left q.1 q.2
  have h2 : HasFDerivAt
      (fun q' : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) => Gw n q'.2.1 q'.1.1 q'.1.2 q'.2.2)
      (fderiv ℝ (fun q' : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
        Gw n q'.2.1 q'.1.1 q'.1.2 q'.2.2) q) q :=
    ((contDiff_Gw_joint n).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h3 := h2.comp q.1 h1
  simpa [Function.comp_def] using h3

/-- The map `(a, b, s, z) ↦ fderiv (a,b) (Gw n s · · z)` is continuous. -/
lemma continuous_fderiv_Gw_ab (n : ℕ) :
    Continuous (fun q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
      fderiv ℝ (fun p : ℝ × ℝ => Gw n q.2.1 p.1 p.2 q.2.2) q.1) := by
  have h : Continuous (fderiv ℝ
      (fun q' : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
        Gw n q'.2.1 q'.1.1 q'.1.2 q'.2.2)) :=
    (contDiff_Gw_joint n).continuous_fderiv (by simp)
  have hfun : (fun q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
        fderiv ℝ (fun p : ℝ × ℝ => Gw n q.2.1 p.1 p.2 q.2.2) q.1) =
      fun q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
        (fderiv ℝ (fun q' : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State) =>
          Gw n q'.2.1 q'.1.1 q'.1.2 q'.2.2) q).comp
          (ContinuousLinearMap.inl ℝ (ℝ × ℝ) (ℝ × RyaboginVolterra.State)) := by
    funext q
    exact (hasFDerivAt_Gw_ab n q).fderiv
  rw [hfun]
  exact h.clm_comp continuous_const

/-- Uniform bound for the `(a,b)`-derivative of `Gw` on the compact region of interest. -/
lemma exists_bound_fderiv_Gw_ab (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State),
      q.1 ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 →
      q.2.1 ∈ Set.Icc (0 : ℝ) 1 →
      q.2.2 ∈ Metric.closedBall (baseZ 1) 1 →
      ‖fderiv ℝ (fun p : ℝ × ℝ => Gw n q.2.1 p.1 p.2 q.2.2) q.1‖ ≤ C := by
  have hK : IsCompact ((Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (baseZ 1) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod (isCompact_closedBall _ _))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_fderiv_Gw_ab n).continuousOn
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun q h1 h2 h3 => ?_⟩
  exact le_trans (hC q ⟨h1, h2, h3⟩) (le_max_left _ _)

/-- **Lipschitz bound for the perturbed `G`-data**: `Gw n s a b z - Gw n s 0 0 z` is controlled
by `|a| + |b|` on `[0,1] × [-1,1]² × closedBall (baseZ 1) 1`. -/
lemma Gw_lipschitz_ab (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s a b : ℝ) (z : RyaboginVolterra.State),
      s ∈ Set.Icc (0 : ℝ) 1 → |a| ≤ 1 → |b| ≤ 1 →
      z ∈ Metric.closedBall (baseZ 1) 1 →
      ‖Gw n s a b z - Gw n s 0 0 z‖ ≤ C * (|a| + |b|) := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_fderiv_Gw_ab n
  refine ⟨C, hCpos, fun s a b z hs ha hb hz => ?_⟩
  have hmem : ∀ x : ℝ × ℝ, x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 →
      x.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    have h : ‖x‖ = max |x.1| |x.2| := by rw [Prod.norm_def]; rfl
    rw [h] at hx
    have h1 : |x.1| ≤ 1 := le_trans (le_max_left _ _) hx
    have h2 : |x.2| ≤ 1 := le_trans (le_max_right _ _) hx
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hsq : (a, b) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h : ‖((a, b) : ℝ × ℝ)‖ = max |a| |b| := by rw [Prod.norm_def]; rfl
    rw [h]
    exact max_le ha hb
  have hdiff : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
      DifferentiableAt ℝ (fun p : ℝ × ℝ => Gw n s p.1 p.2 z) x := by
    intro x hx
    exact (hasFDerivAt_Gw_ab n (x, (s, z))).differentiableAt
  have hCd : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
      ‖fderiv ℝ (fun p : ℝ × ℝ => Gw n s p.1 p.2 z) x‖ ≤ C := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hmem x hx
    exact hC (x, (s, z)) ⟨hx1, hx2⟩ hs hz
  have hmain := dist_image_sub_le_of_norm_fderiv_le hdiff hCd
    (convex_closedBall (0 : ℝ × ℝ) 1) hsq
    (show (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 from by simp)
  rw [dist_eq_norm] at hmain
  have hdist : dist (a, b) (0 : ℝ × ℝ) ≤ |a| + |b| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_le (le_add_of_nonneg_right (abs_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a))
  calc ‖Gw n s a b z - Gw n s 0 0 z‖
      = dist (Gw n s a b z) (Gw n s 0 0 z) := by rw [dist_eq_norm]
    _ ≤ C * dist (a, b) (0 : ℝ × ℝ) := hmain
    _ ≤ C * (|a| + |b|) := mul_le_mul_of_nonneg_left hdist hCpos.le

/-- The perturbed (scaled) `G`-data converges uniformly to the base data as `ε → 0`. -/
lemma Gn_close_TG {n : ℕ} {Qe : VS ≃L[ℝ] VS} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {h : ℝ → ℝ} (hh : Differentiable ℝ h) {a M : ℝ} (hM : 0 < M)
    (hMb : ∀ s ∈ Set.Icc a 1, |h s| ≤ M) (hMd : ∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M)
    (hclose : ∀ s ∈ Set.Icc a 1, ‖baseZ s - baseZ 1‖ < 1 / 2) (ha : 0 ≤ a)
    {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      ∀ U ∈ Metric.closedBall (0 : VS) 1,
      dist (Gn n Qe ρ (ε • h) s U) (TG n Qe ρ s U) < η := by
  obtain ⟨C, hCpos, hC⟩ := Gw_lipschitz_ab n
  set K : ℝ := ‖(Qe.symm : VS →L[ℝ] VS)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨min (1 / (2 * M)) (η * ρ / (2 * C * M * K + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro ε hε s hs U hU
  have hεpos : 0 < ε := hε.1
  have hε1 : ε < 1 / (2 * M) := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε2 : ε < η * ρ / (2 * C * M * K + 1) := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hz : baseZ s + ρ • U ∈ Metric.closedBall (baseZ 1) 1 :=
    base_close_ball hρ0 hρ1 hclose hs hU
  have hder : deriv (ε • h) s = ε * deriv h s := by
    have h' := (hh s).hasDerivAt.const_mul ε
    have hfun : (fun u : ℝ => ε * h u) = (ε • h) := rfl
    rw [← hfun]
    exact h'.deriv
  have hb : |ε * h s| ≤ 1 := by
    rw [abs_mul, abs_of_pos hεpos]
    have h1 : ε * |h s| ≤ ε * M := mul_le_mul_of_nonneg_left (hMb s hs) hεpos.le
    have h2 : ε * M < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hε1 hM
    have h3 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    linarith
  have hb' : |ε * deriv h s| ≤ 1 := by
    rw [abs_mul, abs_of_pos hεpos]
    have h1 : ε * |deriv h s| ≤ ε * M := mul_le_mul_of_nonneg_left (hMd s hs) hεpos.le
    have h2 : ε * M < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hε1 hM
    have h3 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    linarith
  have hGn : Gn n Qe ρ (ε • h) s U
      = (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U)) := by
    simp only [Gn, GnW, Pi.smul_apply, smul_eq_mul, hder]
  have hTG : TG n Qe ρ s U = (1 / ρ) • Qe.symm (Gw n s 0 0 (baseZ s + ρ • U)) := by
    simp only [TG, baseG, G_eq_Gw, Pi.zero_apply, deriv_const]
  rw [dist_eq_norm, hGn, hTG]
  have hsub : (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U)) -
        (1 / ρ) • Qe.symm (Gw n s 0 0 (baseZ s + ρ • U))
      = (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U)) := by
    rw [map_sub, smul_sub]
  rw [hsub, norm_smul]
  have h1 : ‖(1 / ρ : ℝ)‖ = 1 / ρ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1]
  have h2 : ‖Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
        Gw n s 0 0 (baseZ s + ρ • U))‖
      ≤ K * ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U)‖ := by
    have := (Qe.symm : VS →L[ℝ] VS).le_opNorm
      (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U))
    simpa [hK] using this
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha hs.1, hs.2⟩
  have h3 : ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
        Gw n s 0 0 (baseZ s + ρ • U)‖ ≤ C * (|ε * h s| + |ε * deriv h s|) :=
    hC s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) hs01 hb hb' hz
  have h4 : |ε * h s| + |ε * deriv h s| ≤ 2 * (ε * M) := by
    have hb1 : |h s| ≤ M := hMb s hs
    have hd1 : |deriv h s| ≤ M := hMd s hs
    have e1 : |ε * h s| = ε * |h s| := by rw [abs_mul, abs_of_pos hεpos]
    have e2 : |ε * deriv h s| = ε * |deriv h s| := by rw [abs_mul, abs_of_pos hεpos]
    rw [e1, e2]
    have p1 : ε * |h s| ≤ ε * M := mul_le_mul_of_nonneg_left hb1 hεpos.le
    have p2 : ε * |deriv h s| ≤ ε * M := mul_le_mul_of_nonneg_left hd1 hεpos.le
    linarith
  have hεbound : ε * (2 * C * M * K) < η * ρ := by
    have hpos : 0 < 2 * C * M * K + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hε2
    nlinarith [hε2, hK0, hCpos.le, hM.le, mul_nonneg hCpos.le hM.le, hεpos]
  calc (1 / ρ) * ‖Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U))‖
      ≤ (1 / ρ) * (K * ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U)‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (1 / ρ) * (K * (C * (|ε * h s| + |ε * deriv h s|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK0) (by positivity)
    _ ≤ (1 / ρ) * (K * (C * (2 * (ε * M)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h4 hCpos.le) hK0) (by positivity)
    _ = ε * (2 * C * M * K) / ρ := by field_simp
    _ < η * ρ / ρ := div_lt_div_of_pos_right hεbound hρ0
    _ = η := by field_simp

/-! ## Item 1 (continued): closeness of the `Ξ`-data

The map `(ε, s) ↦ Ξ n (ε • h) s` converges to the base data uniformly on `[0,1] × [a,1]` as
`ε → 0`.  The proof uses the smoothness of the parametric `iteratedDeriv`
(`contDiffOn_parametric_iteratedDeriv_gen`) together with uniform continuity of the resulting map
on a compact set — no explicit Faà-di-Bruno estimate. -/

/-- Joint continuity of `(ε, t, s) ↦ (d/ds)^k (1 - t² - (· * t + ε * h ·)²)^n` at the point `s`
(and of its `lineSlope`-twisted version, with the factor `t + ε * g ·`). -/
lemma continuous_scaled_iteratedDeriv (n k : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    Continuous (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv k (fun v : ℝ => (1 - q.2 ^ 2 - (v * q.2 + q.1.1 * h v) ^ 2) ^ n) q.1.2) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => (1 - p.1.2 ^ 2 - (p.2 * p.1.2 + p.1.1 * h p.2) ^ 2) ^ n) := by
    fun_prop
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      iteratedDeriv k (fun v : ℝ => (1 - p.1.2 ^ 2 - (v * p.1.2 + p.1.1 * h v) ^ 2) ^ n) p.2) :=
    (contDiffOn_parametric_iteratedDeriv_gen (k := k)
      (G := fun (x : ℝ × ℝ) (v : ℝ) => (1 - x.2 ^ 2 - (v * x.2 + x.1 * h v) ^ 2) ^ n)
      hG).continuous
  have hmap : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2), q.1.2)) := by fun_prop
  have := hc.comp hmap
  simpa [Function.comp_def] using this

/-- Joint continuity of the `lineSlope`-twisted version of the previous integrand. -/
lemma continuous_scaled_iteratedDeriv_slope (n k : ℕ) {h g : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    Continuous (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv k (fun v : ℝ => (1 - q.2 ^ 2 - (v * q.2 + q.1.1 * h v) ^ 2) ^ (n - 1) *
          (q.2 + q.1.1 * g v)) q.1.2) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => (1 - p.1.2 ^ 2 - (p.2 * p.1.2 + p.1.1 * h p.2) ^ 2) ^ (n - 1) *
          (p.1.2 + p.1.1 * g p.2)) := by
    fun_prop
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      iteratedDeriv k (fun v : ℝ => (1 - p.1.2 ^ 2 - (v * p.1.2 + p.1.1 * h v) ^ 2) ^ (n - 1) *
          (p.1.2 + p.1.1 * g v)) p.2) :=
    (contDiffOn_parametric_iteratedDeriv_gen (k := k)
      (G := fun (x : ℝ × ℝ) (v : ℝ) => (1 - x.2 ^ 2 - (v * x.2 + x.1 * h v) ^ 2) ^ (n - 1) *
          (x.2 + x.1 * g v)) hG).continuous
  have hmap : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2), q.1.2)) := by fun_prop
  have := hc.comp hmap
  simpa [Function.comp_def] using this

/-- **Closeness of `Ξ₁`**: uniform convergence of `ε ↦ Ξ₁ n (ε • h) s → Ξ₁ n 0 s`. -/
lemma Xi1_close {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      |RyaboginVolterra.Xi1 n (ε • h) s - RyaboginVolterra.Xi1 n (fun _ => 0) s| < η := by
  have hf : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv (n + 1) (fun v : ℝ => (1 - q.2 ^ 2 - (v * q.2 + q.1.1 * h v) ^ 2) ^ n) q.1.2) :=
    continuous_scaled_iteratedDeriv n (n + 1) hh
  have hcont : ContinuousOn (fun p : ℝ × ℝ => RyaboginVolterra.Xi1 n (p.1 • h) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1) := by
    have hfun : (fun p : ℝ × ℝ => RyaboginVolterra.Xi1 n (p.1 • h) p.2)
        = fun p : ℝ × ℝ => ∫ t in (-profileX 1)..(profileX 1),
            iteratedDeriv (n + 1)
              (fun v : ℝ => (1 - t ^ 2 - (v * t + p.1 * h v) ^ 2) ^ n) p.2 := by
      funext p
      simp [RyaboginVolterra.Xi1, RyaboginVolterra.line, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf
      (-profileX 1) (profileX 1)).continuousOn
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => RyaboginVolterra.Xi1 n (p.1 • h) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ0 one_pos, ?_⟩
  intro ε hε s hs
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have h1 : (ε, s) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1 := ⟨⟨hε.1.le, hε1⟩, hs⟩
  have h0 : ((0 : ℝ), s) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1 := ⟨⟨le_rfl, zero_le_one⟩, hs⟩
  have hd : dist (ε, s) ((0 : ℝ), s) < δ := by
    have h1 : dist (ε, s) ((0 : ℝ), s) = |ε| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp
    rw [h1, abs_of_pos hε.1]
    exact hεδ
  have hres := hδ (ε, s) h1 ((0 : ℝ), s) h0 hd
  rw [dist_eq_norm, Real.norm_eq_abs] at hres
  have hval0 : RyaboginVolterra.Xi1 n ((0 : ℝ) • h) s
      = RyaboginVolterra.Xi1 n (fun _ => 0) s := by
    rw [zero_smul]
    rfl
  rw [hval0] at hres
  simpa using hres

/-- The derivative of `ε • h`. -/
lemma deriv_smul_const_eq (ε : ℝ) {h : ℝ → ℝ} (hh : Differentiable ℝ h) (u : ℝ) :
    deriv (ε • h) u = ε * deriv h u := by
  have h' := (hh u).hasDerivAt.const_mul ε
  have hfun : (fun x : ℝ => ε * h x) = (ε • h) := rfl
  rw [← hfun]
  exact h'.deriv

/-- **Closeness of `Ξ₂`**: uniform convergence of `ε ↦ Ξ₂ n (ε • h) s → Ξ₂ n 0 s`. -/
lemma Xi2_close {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      |RyaboginVolterra.Xi2 n (ε • h) s - RyaboginVolterra.Xi2 n (fun _ => 0) s| < η := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv h) := contDiff_deriv_of_contDiff hh
  have hf : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv n (fun v : ℝ => (1 - q.2 ^ 2 - (v * q.2 + q.1.1 * h v) ^ 2) ^ (n - 1) *
          (q.2 + q.1.1 * deriv h v)) q.1.2) :=
    continuous_scaled_iteratedDeriv_slope n n hh hg
  have hcont : ContinuousOn (fun p : ℝ × ℝ => RyaboginVolterra.Xi2 n (p.1 • h) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1) := by
    have hfun : (fun p : ℝ × ℝ => RyaboginVolterra.Xi2 n (p.1 • h) p.2)
        = fun p : ℝ × ℝ => ∫ t in (-profileX 1)..(profileX 1),
            iteratedDeriv n
              (fun v : ℝ => (1 - t ^ 2 - (v * t + p.1 * h v) ^ 2) ^ (n - 1) *
                (t + p.1 * deriv h v)) p.2 := by
      funext p
      simp only [RyaboginVolterra.Xi2]
      apply intervalIntegral.integral_congr
      intro t _
      show iteratedDeriv n (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (p.1 • h) u t) ^ 2) ^ (n - 1) * RyaboginVolterra.lineSlope (p.1 • h) u t) p.2
        = iteratedDeriv n (fun v : ℝ => (1 - t ^ 2 - (v * t + p.1 * h v) ^ 2) ^ (n - 1) * (t + p.1 * deriv h v)) p.2
      congr 1
      funext v
      simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope, Pi.smul_apply, smul_eq_mul]
      rw [deriv_smul_const_eq p.1 hd v]
    rw [hfun]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf
      (-profileX 1) (profileX 1)).continuousOn
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => RyaboginVolterra.Xi2 n (p.1 • h) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ0 one_pos, ?_⟩
  intro ε hε s hs
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have h1 : (ε, s) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1 := ⟨⟨hε.1.le, hε1⟩, hs⟩
  have h0 : ((0 : ℝ), s) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a 1 := ⟨⟨le_rfl, zero_le_one⟩, hs⟩
  have hd0 : dist (ε, s) ((0 : ℝ), s) < δ := by
    have h1 : dist (ε, s) ((0 : ℝ), s) = |ε| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp
    rw [h1, abs_of_pos hε.1]
    exact hεδ
  have hres := hδ (ε, s) h1 ((0 : ℝ), s) h0 hd0
  rw [dist_eq_norm, Real.norm_eq_abs] at hres
  have hval0 : RyaboginVolterra.Xi2 n ((0 : ℝ) • h) s
      = RyaboginVolterra.Xi2 n (fun _ => 0) s := by
    rw [zero_smul]
    rfl
  rw [hval0] at hres
  simpa using hres

/-- Norm bound for a state whose first two coordinates vanish. -/
lemma norm_mk4_zero_zero_le (c d : ℝ) :
    ‖RyaboginVolterra.mk4 0 0 c d‖ ≤ |c| + |d| := by
  have h1 : ‖RyaboginVolterra.mk4 0 0 c d‖ ^ 2 = c ^ 2 + d ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp [RyaboginVolterra.mk4_apply]
  have h2 : ‖RyaboginVolterra.mk4 0 0 c d‖ = Real.sqrt (c ^ 2 + d ^ 2) := by
    rw [← h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [h2]
  have h3 : c ^ 2 + d ^ 2 ≤ (|c| + |d|) ^ 2 := by
    nlinarith [sq_abs c, sq_abs d, abs_nonneg c, abs_nonneg d]
  calc Real.sqrt (c ^ 2 + d ^ 2) ≤ Real.sqrt ((|c| + |d|) ^ 2) := Real.sqrt_le_sqrt h3
    _ = |c| + |d| := Real.sqrt_sq (by positivity)

/-- **Closeness of `Ξ`**: uniform convergence of `ε ↦ Ξ n (ε • h) s → Ξ n 0 s` on compacts. -/
lemma Xi_close_base {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      ‖RyaboginVolterra.Xi n (ε • h) s - RyaboginVolterra.Xi n (fun _ => 0) s‖ < η := by
  obtain ⟨ε1, hε1, h1⟩ := Xi1_close (n := n) hh ha (show (0 : ℝ) < η / 2 by positivity)
  obtain ⟨ε2, hε2, h2⟩ := Xi2_close (n := n) hh ha (show (0 : ℝ) < η / 2 by positivity)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun ε hε s hs => ?_⟩
  have hεa : ε < ε1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεb : ε < ε2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have h1' := h1 ε ⟨hε.1, hεa⟩ s hs
  have h2' := h2 ε ⟨hε.1, hεb⟩ s hs
  have hcoord : RyaboginVolterra.Xi n (ε • h) s - RyaboginVolterra.Xi n (fun _ => 0) s
      = RyaboginVolterra.mk4 0 0
          (-(RyaboginVolterra.Xi1 n (ε • h) s - RyaboginVolterra.Xi1 n (fun _ => 0) s))
          (-(RyaboginVolterra.Xi2 n (ε • h) s - RyaboginVolterra.Xi2 n (fun _ => 0) s)) := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
    funext i
    fin_cases i <;>
      simp [RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply] <;> ring
  rw [hcoord]
  calc ‖RyaboginVolterra.mk4 0 0
        (-(RyaboginVolterra.Xi1 n (ε • h) s - RyaboginVolterra.Xi1 n (fun _ => 0) s))
        (-(RyaboginVolterra.Xi2 n (ε • h) s - RyaboginVolterra.Xi2 n (fun _ => 0) s))‖
      ≤ |RyaboginVolterra.Xi1 n (ε • h) s - RyaboginVolterra.Xi1 n (fun _ => 0) s| +
        |RyaboginVolterra.Xi2 n (ε • h) s - RyaboginVolterra.Xi2 n (fun _ => 0) s| := by
        simpa [abs_sub_comm] using norm_mk4_zero_zero_le
          (-(RyaboginVolterra.Xi1 n (ε • h) s - RyaboginVolterra.Xi1 n (fun _ => 0) s))
          (-(RyaboginVolterra.Xi2 n (ε • h) s - RyaboginVolterra.Xi2 n (fun _ => 0) s))
    _ < η / 2 + η / 2 := add_lt_add h1' h2'
    _ = η := by ring

/-- Joint continuity of the parametric `iteratedDeriv` appearing in `Θ`:
`(ε, σ, w, s) ↦ (d/ds)^k ((σ * w + ε * h σ)² - (· * w + ε * h ·)²)^n` at the point `s`. -/
lemma continuous_scaled_iteratedDeriv_theta (n k : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    Continuous (fun q : (((ℝ × ℝ) × ℝ) × ℝ) =>
      iteratedDeriv k (fun v : ℝ =>
        ((q.1.1.2 * q.1.2 + q.1.1.1 * h q.1.1.2) ^ 2 -
          (v * q.1.2 + q.1.1.1 * h v) ^ 2) ^ n) q.2) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (((ℝ × ℝ) × ℝ) × ℝ) =>
        ((p.1.1.2 * p.1.2 + p.1.1.1 * h p.1.1.2) ^ 2 -
          (p.2 * p.1.2 + p.1.1.1 * h p.2) ^ 2) ^ n) := by
    fun_prop
  exact (contDiffOn_parametric_iteratedDeriv_gen (k := k)
    (G := fun (x : ((ℝ × ℝ) × ℝ)) (v : ℝ) =>
      ((x.1.2 * x.2 + x.1.1 * h x.1.2) ^ 2 - (v * x.2 + x.1.1 * h v) ^ 2) ^ n)
    hG).continuous

/-- Joint continuity of the `lineSlope`-twisted `Θ`-integrand (the fourth row). -/
lemma continuous_scaled_iteratedDeriv_theta_slope (n k : ℕ) {h g : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    Continuous (fun q : (((ℝ × ℝ) × ℝ) × ℝ) =>
      iteratedDeriv k (fun v : ℝ =>
        ((q.1.1.2 * q.1.2 + q.1.1.1 * h q.1.1.2) ^ 2 -
          (v * q.1.2 + q.1.1.1 * h v) ^ 2) ^ (n - 1) *
          (q.1.2 + q.1.1.1 * g v)) q.2) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (((ℝ × ℝ) × ℝ) × ℝ) =>
        ((p.1.1.2 * p.1.2 + p.1.1.1 * h p.1.1.2) ^ 2 -
          (p.2 * p.1.2 + p.1.1.1 * h p.2) ^ 2) ^ (n - 1) *
          (p.1.2 + p.1.1.1 * g p.2)) := by
    fun_prop
  exact (contDiffOn_parametric_iteratedDeriv_gen (k := k)
    (G := fun (x : ((ℝ × ℝ) × ℝ)) (v : ℝ) =>
      ((x.1.2 * x.2 + x.1.1 * h x.1.2) ^ 2 - (v * x.2 + x.1.1 * h v) ^ 2) ^ (n - 1) *
        (x.2 + x.1.1 * g v)) hG).continuous

/-- **Uniform closeness to the `ε = 0` slice.**  If `F : ℝ × P → ℝ` is continuous on
`[0,1] × K` with `K` compact, then `F ε p` is uniformly close to `F 0 p` for small `ε`. -/
lemma exists_small_of_continuous_zero {P : Type*} [PseudoMetricSpace P]
    {K : Set P} (hK : IsCompact K) {F : ℝ → P → ℝ}
    (hF : Continuous (fun q : ℝ × P => F q.1 q.2)) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ p ∈ K, |F ε p - F 0 p| < η := by
  have hKc : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have huc : UniformContinuousOn (fun q : ℝ × P => F q.1 q.2) (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
    hKc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun ε hε p hp => ?_⟩
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have h1 : (ε, p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ K := ⟨⟨hε.1.le, hε1⟩, hp⟩
  have h0 : ((0 : ℝ), p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ K := ⟨⟨le_rfl, zero_le_one⟩, hp⟩
  have hd : dist (ε, p) ((0 : ℝ), p) < δ := by
    have hdist : dist (ε, p) ((0 : ℝ), p) = ε := by
      rw [Prod.dist_eq]
      simp [Real.dist_eq, abs_of_pos hε.1, max_eq_left hε.1.le]
    rw [hdist]
    exact hεδ
  have hres := hδ (ε, p) h1 ((0 : ℝ), p) h0 hd
  rw [dist_eq_norm, Real.norm_eq_abs] at hres
  simpa using hres

/-- Coordinates of a state are bounded by its norm. -/
lemma abs_apply_le_norm_state (Z : VS) (i : Fin 4) : |Z i| ≤ ‖Z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le Z i

/-- **Closeness of `Θ`**: uniform convergence of `ε ↦ Θ n (ε • h) s σ Z → Θ n 0 s σ Z` on the
compact set `s ∈ [a,1]`, `σ ∈ [a,1]`, `Z ∈ closedBall (baseZ 1) 1`. -/
lemma Theta_close_base {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      ∀ Z ∈ Metric.closedBall (baseZ 1) 1,
      ‖RyaboginVolterra.Theta n (ε • h) s σ Z - baseΘ n s σ Z‖ < η := by
  set Φ : ℝ → ℝ → ℝ → ℝ → ℝ := fun ε σ w s =>
    iteratedDeriv (n + 1) (fun v : ℝ => ((σ * w + ε * h σ) ^ 2 - (v * w + ε * h v) ^ 2) ^ n) s
    with hΦ
  set Ψ : ℝ → ℝ → ℝ → ℝ → ℝ := fun ε σ w s =>
    iteratedDeriv n (fun v : ℝ =>
      ((σ * w + ε * h σ) ^ 2 - (v * w + ε * h v) ^ 2) ^ (n - 1) * (w + ε * deriv h v)) s
    with hΨ
  have hg : ContDiff ℝ ∞ (deriv h) := contDiff_deriv_of_contDiff hh
  have hΦc : Continuous (fun q : ℝ × (ℝ × ℝ × ℝ) => Φ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    have hmap : Continuous (fun q : ℝ × (ℝ × ℝ × ℝ) =>
        (((q.1, q.2.1), q.2.2.1), q.2.2.2)) := by fun_prop
    have hc := (continuous_scaled_iteratedDeriv_theta n (n + 1) hh).comp hmap
    simpa [Function.comp_def, hΦ] using hc
  have hΨc : Continuous (fun q : ℝ × (ℝ × ℝ × ℝ) => Ψ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    have hmap : Continuous (fun q : ℝ × (ℝ × ℝ × ℝ) =>
        (((q.1, q.2.1), q.2.2.1), q.2.2.2)) := by fun_prop
    have hc := (continuous_scaled_iteratedDeriv_theta_slope n n hh hg).comp hmap
    simpa [Function.comp_def, hΨ] using hc
  set R : ℝ := ‖baseZ 1‖ + 1 with hR
  have hRge : 1 ≤ R := by rw [hR]; linarith [norm_nonneg (baseZ 1)]
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hRge
  have htol : 0 < η / (8 * R) := by positivity
  have hK : IsCompact (Set.Icc a 1 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc a 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨ε1, hε1, h1⟩ := exists_small_of_continuous_zero
    (K := Set.Icc a 1 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc a 1)) hK
    (F := fun ε p => Φ ε p.1 p.2.1 p.2.2) hΦc htol
  obtain ⟨ε2, hε2, h2⟩ := exists_small_of_continuous_zero
    (K := Set.Icc a 1 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc a 1)) hK
    (F := fun ε p => Ψ ε p.1 p.2.1 p.2.2) hΨc htol
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun ε hε s hs σ hσ Z hZ => ?_⟩
  have hεa : ε < ε1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεb : ε < ε2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hZn : ‖Z‖ ≤ R := by
    have h1 : ‖Z - baseZ 1‖ ≤ 1 := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hZ
    calc ‖Z‖ = ‖Z - baseZ 1 + baseZ 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖Z - baseZ 1‖ + ‖baseZ 1‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hZ0 : |Z 0| ≤ R := le_trans (abs_apply_le_norm_state Z 0) hZn
  have hZ1 : |Z 1| ≤ R := le_trans (abs_apply_le_norm_state Z 1) hZn
  have hZ2 : |Z 2| ≤ R := le_trans (abs_apply_le_norm_state Z 2) hZn
  have hZ3 : |Z 3| ≤ R := le_trans (abs_apply_le_norm_state Z 3) hZn
  have hZm0 : -(Z 0) ∈ Set.Icc (-R) R :=
    ⟨by linarith [le_abs_self (Z 0), hZ0], by linarith [neg_abs_le (Z 0), hZ0]⟩
  have hZp1 : Z 1 ∈ Set.Icc (-R) R :=
    ⟨by linarith [neg_abs_le (Z 1), hZ1], by linarith [le_abs_self (Z 1), hZ1]⟩
  have hA := h1 ε ⟨hε.1, hεa⟩ (σ, -(Z 0), s) ⟨hσ, hZm0, hs⟩
  have hB := h1 ε ⟨hε.1, hεa⟩ (σ, Z 1, s) ⟨hσ, hZp1, hs⟩
  have hC := h2 ε ⟨hε.1, hεb⟩ (σ, -(Z 0), s) ⟨hσ, hZm0, hs⟩
  have hD := h2 ε ⟨hε.1, hεb⟩ (σ, Z 1, s) ⟨hσ, hZp1, hs⟩
  have hdd : Differentiable ℝ h := hh.differentiable (by simp)
  have hcoord : RyaboginVolterra.Theta n (ε • h) s σ Z - baseΘ n s σ Z
      = RyaboginVolterra.mk4 0 0
          ((Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s) * Z 2
            + (Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s) * Z 3)
          ((Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s) * Z 2
            + (Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s) * Z 3) := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
    funext i
    fin_cases i <;>
      simp [RyaboginVolterra.Theta, baseΘ, RyaboginVolterra.mk4_apply, RyaboginVolterra.line,
        RyaboginVolterra.lineSlope, hΦ, hΨ, Pi.smul_apply, smul_eq_mul,
        deriv_smul_const_eq ε hdd] <;>
      ring
  rw [hcoord]
  have hAb : |Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s| * |Z 2| ≤ η / 8 := by
    calc |Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s| * |Z 2|
        ≤ (η / (8 * R)) * R := mul_le_mul hA.le hZ2 (abs_nonneg _) htol.le
      _ = η / 8 := by field_simp
  have hBb : |Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s| * |Z 3| ≤ η / 8 := by
    calc |Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s| * |Z 3|
        ≤ (η / (8 * R)) * R := mul_le_mul hB.le hZ3 (abs_nonneg _) htol.le
      _ = η / 8 := by field_simp
  have hCb : |Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s| * |Z 2| ≤ η / 8 := by
    calc |Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s| * |Z 2|
        ≤ (η / (8 * R)) * R := mul_le_mul hC.le hZ2 (abs_nonneg _) htol.le
      _ = η / 8 := by field_simp
  have hDb : |Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s| * |Z 3| ≤ η / 8 := by
    calc |Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s| * |Z 3|
        ≤ (η / (8 * R)) * R := mul_le_mul hD.le hZ3 (abs_nonneg _) htol.le
      _ = η / 8 := by field_simp
  have hP : |((Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s) * Z 2
      + (Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s) * Z 3)| ≤ η / 4 := by
    have h1 : |(Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s) * Z 2| ≤ η / 8 := by
      rw [abs_mul]; exact hAb
    have h2 : |(Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s) * Z 3| ≤ η / 8 := by
      rw [abs_mul]; exact hBb
    calc |(Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s) * Z 2
          + (Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s) * Z 3|
        ≤ |(Φ ε σ (-(Z 0)) s - Φ 0 σ (-(Z 0)) s) * Z 2|
          + |(Φ ε σ (Z 1) s - Φ 0 σ (Z 1) s) * Z 3| := by
          exact abs_add_le _ _
      _ ≤ η / 8 + η / 8 := add_le_add h1 h2
      _ = η / 4 := by ring
  have hQ : |((Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s) * Z 2
      + (Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s) * Z 3)| ≤ η / 4 := by
    have h1 : |(Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s) * Z 2| ≤ η / 8 := by
      rw [abs_mul]; exact hCb
    have h2 : |(Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s) * Z 3| ≤ η / 8 := by
      rw [abs_mul]; exact hDb
    calc |(Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s) * Z 2
          + (Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s) * Z 3|
        ≤ |(Ψ ε σ (-(Z 0)) s - Ψ 0 σ (-(Z 0)) s) * Z 2|
          + |(Ψ ε σ (Z 1) s - Ψ 0 σ (Z 1) s) * Z 3| := by
          exact abs_add_le _ _
      _ ≤ η / 8 + η / 8 := add_le_add h1 h2
      _ = η / 4 := by ring
  refine lt_of_le_of_lt (norm_mk4_zero_zero_le _ _) ?_
  linarith
end Commons.Geometry.Ulam


-- ===== FILE _app.lean =====

noncomputable section
open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## Continuity of the moving reference `Q s` -/

lemma continuous_profileX : Continuous profileX :=
  RyaboginVolterra.contDiff_profileX.continuous

lemma continuous_deriv_profileX : Continuous (deriv profileX) :=
  RyaboginVolterra.contDiff_profileX.continuous_deriv (by simp)

lemma continuous_jBeta (n : ℕ) : Continuous (fun u : ℝ => jBeta n u) := by
  have h : Continuous (fun u : ℝ => u * profileX u ^ 2) :=
    continuous_id.mul (continuous_profileX.pow 2)
  have h2 : Continuous (fun u : ℝ => (u * profileX u ^ 2) ^ n) := h.pow n
  have h3 : Continuous (fun u : ℝ => (jA n) * (u * profileX u ^ 2) ^ n) :=
    continuous_const.mul h2
  simpa [jBeta] using h3

lemma continuous_jDelta (n : ℕ) : Continuous (fun u : ℝ => jDelta n u) := by
  have h : Continuous (fun u : ℝ => u * profileX u ^ 2) :=
    continuous_id.mul (continuous_profileX.pow 2)
  have h2 : Continuous (fun u : ℝ => (u * profileX u ^ 2) ^ (n - 1)) := h.pow (n - 1)
  have h3 : Continuous (fun u : ℝ => (-jB n) * (u * profileX u ^ 2) ^ (n - 1) * profileX u) :=
    (continuous_const.mul h2).mul continuous_profileX
  simpa [jDelta] using h3

lemma continuous_jAlpha (n : ℕ) : Continuous (fun u : ℝ => jAlpha n u) := by
  have h : Continuous (fun u : ℝ => u * profileX u ^ 2) :=
    continuous_id.mul (continuous_profileX.pow 2)
  have h2 : Continuous (fun u : ℝ => (u * profileX u ^ 2) ^ (n - 1)) := h.pow (n - 1)
  have h3 : Continuous (fun u : ℝ =>
      2 * jA n * (n : ℝ) * u * profileX u * (u * profileX u ^ 2) ^ (n - 1) * deriv profileX u) :=
    ((((continuous_const.mul continuous_const).mul continuous_const).mul continuous_id).mul
      continuous_profileX).mul h2 |>.mul continuous_deriv_profileX
  exact h3

lemma continuous_jGamma (n : ℕ) : Continuous (fun u : ℝ => jGamma n u) := by
  have h : Continuous (fun u : ℝ => u * profileX u ^ 2) :=
    continuous_id.mul (continuous_profileX.pow 2)
  have h2 : Continuous (fun u : ℝ => (u * profileX u ^ 2) ^ (n - 1)) := h.pow (n - 1)
  have h3 : Continuous (fun u : ℝ =>
      -jB n * (2 * (n : ℝ) - 1) * (u * profileX u ^ 2) ^ (n - 1) * deriv profileX u) :=
    ((continuous_const.mul continuous_const).mul h2).mul continuous_deriv_profileX
  simpa [jGamma] using h3

/-- Continuity of a `State`-valued map may be tested on the four coordinates. -/
lemma continuous_state_iff {P : Type*} [TopologicalSpace P] {F : P → VS}
    (h : Continuous fun p : P => ((F p : VS) : Fin 4 → ℝ)) : Continuous F := by
  have h2 : (fun p : P => ((F p : VS) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘ F := rfl
  rw [h2] at h
  have h3 := ((EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous).comp h
  have h4 : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) ∘
      ((EuclideanSpace.equiv (Fin 4) ℝ) ∘ F) = F := by
    funext p
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  rw [h4] at h3
  exact h3

/-- **Continuity of the inverse Jacobian family.**  For `u ≥ a/2 > 0` the explicit inverse
`iaLin n u` of `jacLin n u` is continuous in `(u, v)`. -/
lemma continuous_iaLin_max (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × VS => iaLin n (max p.1 (a / 2)) p.2) := by
  have hu : ∀ p : ℝ × VS, 0 < max p.1 (a / 2) := fun p =>
    lt_of_lt_of_le (by linarith) (le_max_right p.1 (a / 2))
  have hmax : Continuous fun p : ℝ × VS => max p.1 (a / 2) :=
    continuous_fst.max continuous_const
  have hAlpha : Continuous fun p : ℝ × VS => jAlpha n (max p.1 (a / 2)) :=
    (continuous_jAlpha n).comp hmax
  have hBeta : Continuous fun p : ℝ × VS => jBeta n (max p.1 (a / 2)) :=
    (continuous_jBeta n).comp hmax
  have hGamma : Continuous fun p : ℝ × VS => jGamma n (max p.1 (a / 2)) :=
    (continuous_jGamma n).comp hmax
  have hDelta : Continuous fun p : ℝ × VS => jDelta n (max p.1 (a / 2)) :=
    (continuous_jDelta n).comp hmax
  have hBne : ∀ p : ℝ × VS, jBeta n (max p.1 (a / 2)) ≠ 0 := fun p => jBeta_ne_zero (hu p)
  have hDne : ∀ p : ℝ × VS, jDelta n (max p.1 (a / 2)) ≠ 0 := fun p => jDelta_ne_zero (hu p)
  have h2B : Continuous fun p : ℝ × VS => (2 : ℝ) * jBeta n (max p.1 (a / 2)) :=
    continuous_const.mul hBeta
  have h2D : Continuous fun p : ℝ × VS => (2 : ℝ) * jDelta n (max p.1 (a / 2)) :=
    continuous_const.mul hDelta
  have hc1 : Continuous fun p : ℝ × VS =>
      -jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
        - jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2))) :=
    (hAlpha.neg.div h2B (fun p => mul_ne_zero two_ne_zero (hBne p))).sub
      (hGamma.div h2D (fun p => mul_ne_zero two_ne_zero (hDne p)))
  have hc2 : Continuous fun p : ℝ × VS =>
      -jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
        + jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2))) :=
    (hAlpha.neg.div h2B (fun p => mul_ne_zero two_ne_zero (hBne p))).add
      (hGamma.div h2D (fun p => mul_ne_zero two_ne_zero (hDne p)))
  have hc3 : Continuous fun p : ℝ × VS => 1 / (2 * jBeta n (max p.1 (a / 2))) :=
    continuous_const.div h2B (fun p => mul_ne_zero two_ne_zero (hBne p))
  have hc4 : Continuous fun p : ℝ × VS => 1 / (2 * jDelta n (max p.1 (a / 2))) :=
    continuous_const.div h2D (fun p => mul_ne_zero two_ne_zero (hDne p))
  have h0 : Continuous fun p : ℝ × VS => p.2 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).comp continuous_snd
  have h1 : Continuous fun p : ℝ × VS => p.2 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 1).comp continuous_snd
  have h2 : Continuous fun p : ℝ × VS => p.2 2 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 2).comp continuous_snd
  have h3 : Continuous fun p : ℝ × VS => p.2 3 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3).comp continuous_snd
  push_cast
  refine continuous_state_iff ?_
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · simp only [Fin.isValue, Fin.reduceFinMk]
    have hfun : (fun p : ℝ × VS => ((iaLin n (max p.1 (a / 2)) p.2 : VS) : Fin 4 → ℝ) 0)
        = fun p : ℝ × VS => p.2 0 := by
      funext p
      rw [iaLin_apply_zero]
    rw [hfun]
    exact h0
  · simp only [Fin.isValue, Fin.reduceFinMk]
    have hfun : (fun p : ℝ × VS => ((iaLin n (max p.1 (a / 2)) p.2 : VS) : Fin 4 → ℝ) 1)
        = fun p : ℝ × VS => p.2 1 := by
      funext p
      rw [iaLin_apply_one]
    rw [hfun]
    exact h1
  · simp only [Fin.isValue, Fin.reduceFinMk]
    have hfun : (fun p : ℝ × VS => ((iaLin n (max p.1 (a / 2)) p.2 : VS) : Fin 4 → ℝ) 2)
        = fun p : ℝ × VS =>
          (-jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
            - jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2)))) * p.2 0
          + (-jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
            + jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2)))) * p.2 1
          + (1 / (2 * jBeta n (max p.1 (a / 2)))) * p.2 2
          + (1 / (2 * jDelta n (max p.1 (a / 2)))) * p.2 3 := by
      funext p
      rw [iaLin_apply_two]
    rw [hfun]
    exact (((hc1.mul h0).add (hc2.mul h1)).add (hc3.mul h2)).add (hc4.mul h3)
  · simp only [Fin.isValue, Fin.reduceFinMk]
    have hfun : (fun p : ℝ × VS => ((iaLin n (max p.1 (a / 2)) p.2 : VS) : Fin 4 → ℝ) 3)
        = fun p : ℝ × VS =>
          (-jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
            + jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2)))) * p.2 0
          + (-jAlpha n (max p.1 (a / 2)) / (2 * jBeta n (max p.1 (a / 2)))
            - jGamma n (max p.1 (a / 2)) / (2 * jDelta n (max p.1 (a / 2)))) * p.2 1
          + (1 / (2 * jBeta n (max p.1 (a / 2)))) * p.2 2
          - (1 / (2 * jDelta n (max p.1 (a / 2)))) * p.2 3 := by
      funext p
      rw [iaLin_apply_three]
    rw [hfun]
    exact (((hc2.mul h0).add (hc1.mul h1)).add (hc3.mul h2)).sub (hc4.mul h3)

/-! ## The moving reference family `Q` -/

/-- Norm bound for a state in terms of the absolute values of its four coordinates. -/
lemma norm_mk4_le (a b c d : ℝ) :
    ‖RyaboginVolterra.mk4 a b c d‖ ≤ |a| + |b| + |c| + |d| := by
  have h1 : ‖RyaboginVolterra.mk4 a b c d‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp [RyaboginVolterra.mk4_apply]
  have h2 : ‖RyaboginVolterra.mk4 a b c d‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    rw [← h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [h2]
  have h3 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ (|a| + |b| + |c| + |d|) ^ 2 := by
    nlinarith [sq_abs a, sq_abs b, sq_abs c, sq_abs d, abs_nonneg a, abs_nonneg b,
      abs_nonneg c, abs_nonneg d]
  calc Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)
      ≤ Real.sqrt ((|a| + |b| + |c| + |d|) ^ 2) := Real.sqrt_le_sqrt h3
    _ = |a| + |b| + |c| + |d| := Real.sqrt_sq (by positivity)

/-- The moving reference family.  Below `a/2` it is frozen (so that the family is defined on
all of `ℝ`); on `[a/2, ∞)` it is `Qe.symm` composed with the derivative of `baseG` at the base
point `(s, baseZ s)`. -/
noncomputable def Qref (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) :
    ℝ → VS ≃L[ℝ] VS :=
  fun s => (jacEquiv n (lt_of_lt_of_le (by linarith) (le_max_right s (a / 2)))).trans Qe.symm

lemma Qref_apply (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) (s : ℝ) (v : VS) :
    Qref n Qe ha s v = Qe.symm (jacLin n (max s (a / 2)) v) := by
  simp only [Qref, ContinuousLinearEquiv.trans_apply, jacEquiv_apply]

lemma Qref_symm_apply (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) (s : ℝ) (v : VS) :
    (Qref n Qe ha s).symm v = iaLin n (max s (a / 2)) (Qe v) := by
  have hu : 0 < max s (a / 2) := lt_of_lt_of_le (by linarith) (le_max_right s (a / 2))
  rw [ContinuousLinearEquiv.symm_apply_eq]
  rw [Qref_apply, jacLin_iaLin hu (Qe v), ContinuousLinearEquiv.symm_apply_apply]

/-- `(Qref s)⁻¹` acting on the normalised data only sees `iaLin` (the `Qe` cancels). -/
lemma Qref_symm_comp_Qe (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ((Qref n Qe ha s).symm : VS →L[ℝ] VS) ∘L (Qe.symm : VS →L[ℝ] VS)
      = (iaLin n (max s (a / 2))).toContinuousLinearMap := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply]
  change (Qref n Qe ha s).symm (Qe.symm v) = iaLin n (max s (a / 2)) v
  rw [Qref_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- `(Qref s)⁻¹` is continuous in `(s, v)`: the `hQcont` hypothesis of the abstract theorem. -/
lemma Qref_symm_continuous (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × VS => (Qref n Qe ha p.1).symm p.2) := by
  have h : (fun p : ℝ × VS => (Qref n Qe ha p.1).symm p.2)
      = fun p : ℝ × VS => iaLin n (max p.1 (a / 2)) (Qe p.2) := by
    funext p
    rw [Qref_symm_apply]
  rw [h]
  have h1 : Continuous fun p : ℝ × VS => (max p.1 (a / 2), Qe p.2) :=
    (continuous_fst.max continuous_const).prodMk (Qe.continuous.comp continuous_snd)
  refine ((continuous_iaLin_max n ha).comp h1).congr (fun p => ?_)
  simp only [Function.comp_apply, Prod.fst, Prod.snd, max_assoc, max_self]

/-- The scalar quantity controlling `‖iaLin n u‖`. -/
noncomputable def iaLinK (n : ℕ) (u : ℝ) : ℝ :=
  |jAlpha n u / (2 * jBeta n u)| + |jGamma n u / (2 * jDelta n u)|
    + |1 / (2 * jBeta n u)| + |1 / (2 * jDelta n u)|

lemma iaLinK_nonneg (n : ℕ) (u : ℝ) : 0 ≤ iaLinK n u := by
  unfold iaLinK
  have h1 : 0 ≤ |jAlpha n u / (2 * jBeta n u)| := abs_nonneg _
  have h2 : 0 ≤ |jGamma n u / (2 * jDelta n u)| := abs_nonneg _
  have h3 : 0 ≤ |1 / (2 * jBeta n u)| := abs_nonneg _
  have h4 : 0 ≤ |1 / (2 * jDelta n u)| := abs_nonneg _
  linarith

lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  calc |a + -b| ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- Triangle bound for the first coefficient pair of the second row of `iaLin`. -/
lemma abs_coeff_two_a (n : ℕ) (u : ℝ) :
    |-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)| ≤ iaLinK n u := by
  refine le_trans (abs_sub_le_abs_add _ _) ?_
  have h1 : |-jAlpha n u / (2 * jBeta n u)| = |jAlpha n u / (2 * jBeta n u)| := by
    have he : -jAlpha n u / (2 * jBeta n u) = -(jAlpha n u / (2 * jBeta n u)) := by ring
    rw [he, abs_neg]
  rw [h1]
  unfold iaLinK
  have h3 : 0 ≤ |1 / (2 * jBeta n u)| := abs_nonneg _
  have h4 : 0 ≤ |1 / (2 * jDelta n u)| := abs_nonneg _
  linarith

lemma abs_coeff_two_b (n : ℕ) (u : ℝ) :
    |-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)| ≤ iaLinK n u := by
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |-jAlpha n u / (2 * jBeta n u)| = |jAlpha n u / (2 * jBeta n u)| := by
    have he : -jAlpha n u / (2 * jBeta n u) = -(jAlpha n u / (2 * jBeta n u)) := by ring
    rw [he, abs_neg]
  rw [h1]
  unfold iaLinK
  have h3 : 0 ≤ |1 / (2 * jBeta n u)| := abs_nonneg _
  have h4 : 0 ≤ |1 / (2 * jDelta n u)| := abs_nonneg _
  linarith

lemma abs_coeff_three (n : ℕ) (u : ℝ) : |1 / (2 * jBeta n u)| ≤ iaLinK n u := by
  unfold iaLinK
  have h2 : 0 ≤ |jGamma n u / (2 * jDelta n u)| := abs_nonneg _
  have h4 : 0 ≤ |1 / (2 * jDelta n u)| := abs_nonneg _
  have h1 : 0 ≤ |jAlpha n u / (2 * jBeta n u)| := abs_nonneg _
  linarith

lemma abs_coeff_four (n : ℕ) (u : ℝ) : |1 / (2 * jDelta n u)| ≤ iaLinK n u := by
  unfold iaLinK
  have h2 : 0 ≤ |jGamma n u / (2 * jDelta n u)| := abs_nonneg _
  have h3 : 0 ≤ |1 / (2 * jBeta n u)| := abs_nonneg _
  have h1 : 0 ≤ |jAlpha n u / (2 * jBeta n u)| := abs_nonneg _
  linarith

/-- Triangle/power bound for the second coordinate of `iaLin`. -/
lemma abs_iaLin_apply_two_le (n : ℕ) (u : ℝ) (w : VS) :
    |iaLin n u w 2| ≤ (4 * iaLinK n u) * ‖w‖ := by
  have h0 : |w 0| ≤ ‖w‖ := abs_apply_le_norm_state w 0
  have h1 : |w 1| ≤ ‖w‖ := abs_apply_le_norm_state w 1
  have h2 : |w 2| ≤ ‖w‖ := abs_apply_le_norm_state w 2
  have h3 : |w 3| ≤ ‖w‖ := abs_apply_le_norm_state w 3
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hA := abs_coeff_two_a n u
  have hB := abs_coeff_two_b n u
  have hC := abs_coeff_three n u
  have hD := abs_coeff_four n u
  rw [iaLin_apply_two]
  have e1 : |(-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0|
      ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hA h0 (abs_nonneg _) (iaLinK_nonneg n u)
  have e2 : |(-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1|
      ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hB h1 (abs_nonneg _) (iaLinK_nonneg n u)
  have e3 : |(1 / (2 * jBeta n u)) * w 2| ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hC h2 (abs_nonneg _) (iaLinK_nonneg n u)
  have e4 : |(1 / (2 * jDelta n u)) * w 3| ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hD h3 (abs_nonneg _) (iaLinK_nonneg n u)
  have a1 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0
    + (-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1
    + (1 / (2 * jBeta n u)) * w 2) ((1 / (2 * jDelta n u)) * w 3)
  have a2 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0
    + (-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1)
    ((1 / (2 * jBeta n u)) * w 2)
  have a3 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0)
    ((-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1)
  have hK := iaLinK_nonneg n u
  calc |(-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0
        + (-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1
        + (1 / (2 * jBeta n u)) * w 2 + (1 / (2 * jDelta n u)) * w 3|
      ≤ |(-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 0|
        + |(-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 1|
        + |(1 / (2 * jBeta n u)) * w 2| + |(1 / (2 * jDelta n u)) * w 3| := by linarith
    _ ≤ iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ := by
        linarith
    _ = (4 * iaLinK n u) * ‖w‖ := by ring

/-- Triangle/power bound for the third coordinate of `iaLin`. -/
lemma abs_iaLin_apply_three_le (n : ℕ) (u : ℝ) (w : VS) :
    |iaLin n u w 3| ≤ (4 * iaLinK n u) * ‖w‖ := by
  have h0 : |w 0| ≤ ‖w‖ := abs_apply_le_norm_state w 0
  have h1 : |w 1| ≤ ‖w‖ := abs_apply_le_norm_state w 1
  have h2 : |w 2| ≤ ‖w‖ := abs_apply_le_norm_state w 2
  have h3 : |w 3| ≤ ‖w‖ := abs_apply_le_norm_state w 3
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hA := abs_coeff_two_b n u
  have hB := abs_coeff_two_a n u
  have hC := abs_coeff_three n u
  have hD := abs_coeff_four n u
  rw [iaLin_apply_three]
  have e1 : |(-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0|
      ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hA h0 (abs_nonneg _) (iaLinK_nonneg n u)
  have e2 : |(-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1|
      ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hB h1 (abs_nonneg _) (iaLinK_nonneg n u)
  have e3 : |(1 / (2 * jBeta n u)) * w 2| ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul hC h2 (abs_nonneg _) (iaLinK_nonneg n u)
  have e4 : |-(1 / (2 * jDelta n u)) * w 3| ≤ iaLinK n u * ‖w‖ := by
    rw [abs_mul]
    have hD' : |-(1 / (2 * jDelta n u))| ≤ iaLinK n u := by
      rw [abs_neg]; exact hD
    exact mul_le_mul hD' h3 (abs_nonneg _) (iaLinK_nonneg n u)
  have a1 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0
    + (-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1
    + (1 / (2 * jBeta n u)) * w 2) (-(1 / (2 * jDelta n u)) * w 3)
  have a2 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0
    + (-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1)
    ((1 / (2 * jBeta n u)) * w 2)
  have a3 := abs_add_le ((-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0)
    ((-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1)
  have hsub : (-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0
      + (-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1
      + (1 / (2 * jBeta n u)) * w 2 - (1 / (2 * jDelta n u)) * w 3
      = (-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0
        + (-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1
        + (1 / (2 * jBeta n u)) * w 2 + (-(1 / (2 * jDelta n u)) * w 3) := by ring
  rw [hsub]
  have hK := iaLinK_nonneg n u
  calc |(-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0
        + (-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1
        + (1 / (2 * jBeta n u)) * w 2 + (-(1 / (2 * jDelta n u)) * w 3)|
      ≤ |(-jAlpha n u / (2 * jBeta n u) + jGamma n u / (2 * jDelta n u)) * w 0|
        + |(-jAlpha n u / (2 * jBeta n u) - jGamma n u / (2 * jDelta n u)) * w 1|
        + |(1 / (2 * jBeta n u)) * w 2| + |-(1 / (2 * jDelta n u)) * w 3| := by linarith
    _ ≤ iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ + iaLinK n u * ‖w‖ := by
        linarith
    _ = (4 * iaLinK n u) * ‖w‖ := by ring

lemma norm_iaLin_le (n : ℕ) {u : ℝ} (hu : 0 < u) (w : VS) :
    ‖iaLin n u w‖ ≤ (2 + 8 * iaLinK n u) * ‖w‖ := by
  have hcoe : RyaboginVolterra.mk4 (w 0) (w 1) (iaLin n u w 2) (iaLin n u w 3)
      = iaLin n u w := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
    funext i
    fin_cases i <;> simp [RyaboginVolterra.mk4_apply]
  rw [← hcoe]
  have hmain := norm_mk4_le (w 0) (w 1) (iaLin n u w 2) (iaLin n u w 3)
  have h0 : |w 0| ≤ ‖w‖ := abs_apply_le_norm_state w 0
  have h1 : |w 1| ≤ ‖w‖ := abs_apply_le_norm_state w 1
  have h2 := abs_iaLin_apply_two_le n u w
  have h3 := abs_iaLin_apply_three_le n u w
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hK := iaLinK_nonneg n u
  nlinarith [hmain, h0, h1, h2, h3, hw, hK]

lemma continuousOn_iaLinK (n : ℕ) : ContinuousOn (fun u : ℝ => iaLinK n u) (Set.Ioi 0) := by
  have hα : ContinuousOn (fun u : ℝ => jAlpha n u) (Set.Ioi 0) :=
    (continuous_jAlpha n).continuousOn
  have hβ : ContinuousOn (fun u : ℝ => jBeta n u) (Set.Ioi 0) :=
    (continuous_jBeta n).continuousOn
  have hγ : ContinuousOn (fun u : ℝ => jGamma n u) (Set.Ioi 0) :=
    (continuous_jGamma n).continuousOn
  have hδ : ContinuousOn (fun u : ℝ => jDelta n u) (Set.Ioi 0) :=
    (continuous_jDelta n).continuousOn
  have hβne : ∀ u ∈ Set.Ioi (0:ℝ), jBeta n u ≠ 0 := fun u hu => jBeta_ne_zero hu
  have hδne : ∀ u ∈ Set.Ioi (0:ℝ), jDelta n u ≠ 0 := fun u hu => jDelta_ne_zero hu
  have h1 : ContinuousOn (fun u : ℝ => |jAlpha n u / (2 * jBeta n u)|) (Set.Ioi 0) :=
    (hα.div (continuousOn_const.mul hβ)
      (fun u hu => mul_ne_zero two_ne_zero (hβne u hu))).abs
  have h2 : ContinuousOn (fun u : ℝ => |jGamma n u / (2 * jDelta n u)|) (Set.Ioi 0) :=
    (hγ.div (continuousOn_const.mul hδ)
      (fun u hu => mul_ne_zero two_ne_zero (hδne u hu))).abs
  have h3 : ContinuousOn (fun u : ℝ => |1 / (2 * jBeta n u)|) (Set.Ioi 0) :=
    (continuousOn_const.div (continuousOn_const.mul hβ)
      (fun u hu => mul_ne_zero two_ne_zero (hβne u hu))).abs
  have h4 : ContinuousOn (fun u : ℝ => |1 / (2 * jDelta n u)|) (Set.Ioi 0) :=
    (continuousOn_const.div (continuousOn_const.mul hδ)
      (fun u hu => mul_ne_zero two_ne_zero (hδne u hu))).abs
  unfold iaLinK
  exact ((h1.add h2).add h3).add h4

/-- Uniform bound for `‖(Qref s)⁻¹‖` on `s ∈ [a,1]`: the `hQbdd` hypothesis. -/
lemma Qref_symm_bound (n : ℕ) (Qe : VS ≃L[ℝ] VS) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a 1, ‖((Qref n Qe ha s).symm : VS →L[ℝ] VS)‖ ≤ C := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a / 2) (b := 1)).exists_bound_of_continuousOn
    (f := fun u : ℝ => iaLinK n u)
    ((continuousOn_iaLinK n).mono (fun u hu => by
      simp only [Set.mem_Icc] at hu
      exact lt_of_lt_of_le (by linarith) hu.1))
  have hK0 : 0 ≤ K := by
    have h : iaLinK n (a / 2) ≤ K := by
      have h' := hK (a / 2) ⟨le_rfl, by linarith [ha1]⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (iaLinK_nonneg n (a/2))] using h'
    linarith [iaLinK_nonneg n (a/2)]
  refine ⟨(2 + 8 * K) * ‖(Qe : VS →L[ℝ] VS)‖, by positivity, fun s hs => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  have hQ : ((Qref n Qe ha s).symm : VS →L[ℝ] VS) w = iaLin n (max s (a / 2)) (Qe w) :=
    Qref_symm_apply n Qe ha s w
  rw [hQ]
  have hs0 : 0 < max s (a / 2) := lt_of_lt_of_le (by linarith) (le_max_right s (a / 2))
  have hmem : max s (a / 2) ∈ Set.Icc (a / 2) 1 :=
    ⟨le_max_right _ _, max_le hs.2 (by linarith [ha1])⟩
  have hKu : iaLinK n (max s (a/2)) ≤ K := by
    have h := hK (max s (a/2)) hmem
    simpa [Real.norm_eq_abs, abs_of_nonneg (iaLinK_nonneg n _)] using h
  calc ‖iaLin n (max s (a / 2)) (Qe w)‖
      ≤ (2 + 8 * iaLinK n (max s (a/2))) * ‖Qe w‖ := norm_iaLin_le n hs0 (Qe w)
    _ ≤ (2 + 8 * K) * (‖(Qe : VS →L[ℝ] VS)‖ * ‖w‖) := by
        have h1 : ‖Qe w‖ ≤ ‖(Qe : VS →L[ℝ] VS)‖ * ‖w‖ := (Qe : VS →L[ℝ] VS).le_opNorm w
        have h2 : (2 + 8 * iaLinK n (max s (a/2))) ≤ (2 + 8 * K) := by linarith
        have h3 : 0 ≤ ‖(Qe : VS →L[ℝ] VS)‖ * ‖w‖ := by positivity
        have h4 : 0 ≤ 2 + 8 * iaLinK n (max s (a / 2)) :=
          by linarith [iaLinK_nonneg n (max s (a/2))]
        nlinarith [h1, h2, h3, h4, norm_nonneg (Qe w)]
    _ = (2 + 8 * K) * ‖(Qe : VS →L[ℝ] VS)‖ * ‖w‖ := by ring


/-- The joint map `(a, b, s, z) ↦ Gw n s a b z` is smooth. -/
lemma contDiff_Gw_param (n : ℕ) :
    ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × VS => Gw n q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have h : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × VS =>
      (((q.1.2.1, q.1.2.2), (q.1.1, q.2)) : (ℝ × ℝ) × (ℝ × VS))) := by fun_prop
  exact (contDiff_Gw n).comp h

lemma continuous_fderiv_Gw_param (n : ℕ) :
    Continuous (fun q : (ℝ × (ℝ × ℝ)) × VS =>
      fderiv ℝ (fun z : VS => Gw n q.1.1 q.1.2.1 q.1.2.2 z) q.2) :=
  continuous_fderiv_snd (F := fun p : ℝ × (ℝ × ℝ) => fun z : VS =>
    Gw n p.1 p.2.1 p.2.2 z) (contDiff_Gw_param n)

lemma baseG_eq_Gw (n : ℕ) (s : ℝ) (z : VS) : baseG n s z = Gw n s 0 0 z := by
  simp only [baseG, G_eq_Gw, deriv_const]


/-- The `z`-derivative of the perturbed `G`-data. -/
noncomputable def GnDeriv (n : ℕ) (h : ℝ → ℝ) (ε s : ℝ) (w : VS) : VS →L[ℝ] VS :=
  fderiv ℝ (fun z : VS => G n (ε • h) s z) w

/-- The `z`-derivative of the base `G`-data. -/
noncomputable def baseGDeriv (n : ℕ) (s : ℝ) (w : VS) : VS →L[ℝ] VS :=
  fderiv ℝ (fun z : VS => baseG n s z) w

/-- The `z`-derivative of the perturbed `G`-data is continuous in `(ε, s, w)`. -/
lemma continuous_fderiv_Gn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    Continuous (fun q : ℝ × (ℝ × VS) => GnDeriv n h q.1 q.2.1 q.2.2) := by
  have hA : Continuous fun q : ℝ × (ℝ × VS) => q.2.1 := continuous_snd.fst
  have hB : Continuous fun q : ℝ × (ℝ × VS) => q.1 * h q.2.1 :=
    continuous_fst.mul (hh.continuous.comp continuous_snd.fst)
  have hC : Continuous fun q : ℝ × (ℝ × VS) => q.1 * deriv h q.2.1 :=
    continuous_fst.mul ((contDiff_deriv_of_contDiff hh).continuous.comp continuous_snd.fst)
  have hpar : Continuous fun q : ℝ × (ℝ × VS) =>
      (q.2.1, (q.1 * h q.2.1, q.1 * deriv h q.2.1)) :=
    hA.prodMk (hB.prodMk hC)
  have h2 := (continuous_fderiv_Gw_param n).comp (hpar.prodMk continuous_snd.snd)
  refine h2.congr (fun q => ?_)
  have hder : deriv (q.1 • h) q.2.1 = q.1 * deriv h q.2.1 := by
    have h' := ((hh.differentiable (by simp)) q.2.1).hasDerivAt.const_mul q.1
    have hfun : (fun u : ℝ => q.1 * h u) = (q.1 • h) := rfl
    rw [← hfun]
    exact h'.deriv
  have harg : (q.1 • h) q.2.1 = q.1 * h q.2.1 := rfl
  have hfun : (fun z : VS => G n (q.1 • h) q.2.1 z)
      = fun z : VS => Gw n q.2.1 (q.1 * h q.2.1) (q.1 * deriv h q.2.1) z := by
    funext z
    have hG : G n (q.1 • h) q.2.1 z
        = Gw n q.2.1 ((q.1 • h) q.2.1) (deriv (q.1 • h) q.2.1) z :=
      G_eq_Gw n (q.1 • h) q.2.1 z
    rw [hG, harg, hder]
  change fderiv ℝ (fun z : VS => Gw n q.2.1 (q.1 * h q.2.1) (q.1 * deriv h q.2.1) z) q.2.2
      = GnDeriv n h q.1 q.2.1 q.2.2
  rw [GnDeriv, hfun]

lemma continuous_fderiv_Gn_fixed (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (ε : ℝ) :
    Continuous (fun p : ℝ × VS => GnDeriv n h ε p.1 p.2) := by
  have hmap : Continuous (fun p : ℝ × VS => Prod.mk ε (p.1, p.2)) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_snd)
  have h := (continuous_fderiv_Gn n hh).comp hmap
  refine h.congr (fun p => ?_)
  rfl

lemma GnDeriv_zero (n : ℕ) :
    GnDeriv n (fun _ => (0:ℝ)) = fun ε s w => baseGDeriv n s w := by
  funext ε s w
  have hz : (ε • (fun _ : ℝ => (0:ℝ))) = fun _ : ℝ => (0:ℝ) := by funext u; simp
  have hfun : (fun z : VS => G n (ε • fun _ => 0) s z) = fun z : VS => baseG n s z := by
    funext z
    have hG : G n (ε • fun _ => 0) s z
        = Gw n s ((ε • (fun _ : ℝ => 0)) s) (deriv (ε • (fun _ : ℝ => 0)) s) z :=
      G_eq_Gw n (ε • fun _ => 0) s z
    rw [hG, hz, deriv_const]
    exact (baseG_eq_Gw n s z).symm
  simp only [GnDeriv, baseGDeriv]
  rw [hfun]

/-- Uniform closeness to the `ε = 0` slice, for a normed codomain. -/
lemma exists_norm_small_of_continuous_zero {P : Type*} [PseudoMetricSpace P]
    {E : Type*} [NormedAddCommGroup E] {K : Set P} (hK : IsCompact K) {F : ℝ → P → E}
    (hF : Continuous (fun q : ℝ × P => F q.1 q.2)) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ p ∈ K, ‖F ε p - F 0 p‖ < η := by
  have hKc : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have huc : UniformContinuousOn (fun q : ℝ × P => F q.1 q.2) (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
    hKc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun ε hε p hp => ?_⟩
  have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have h1 : (ε, p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ K := ⟨⟨hε.1.le, hε1⟩, hp⟩
  have h0 : ((0 : ℝ), p) ∈ Set.Icc (0 : ℝ) 1 ×ˢ K := ⟨⟨le_rfl, zero_le_one⟩, hp⟩
  have hd : dist (ε, p) ((0 : ℝ), p) < δ := by
    have hdist : dist (ε, p) ((0 : ℝ), p) = ε := by
      rw [Prod.dist_eq]
      simp [abs_of_pos hε.1, max_eq_left hε.1.le]
    rw [hdist]
    exact hεδ
  have hres := hδ (ε, p) h1 ((0 : ℝ), p) h0 hd
  rwa [dist_eq_norm] at hres

/-- Uniform continuity of a continuous map on a compact set, in the `ρ`-form used below. -/
lemma exists_uniform_close_of_continuousOn {P : Type*} [PseudoMetricSpace P]
    {E : Type*} [PseudoMetricSpace E] {K : Set P} (hK : IsCompact K) {F : P → E}
    (hF : ContinuousOn F K) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → dist (F x) (F y) < η := by
  have huc := hK.uniformContinuousOn_of_continuous hF
  rw [Metric.uniformContinuousOn_iff] at huc
  exact huc η hη

/-- Operator-norm bound for `iaLin n s` on `s ∈ [a,1]`. -/
lemma exists_norm_iaLin_le (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K1 : ℝ, 0 < K1 ∧ ∀ s ∈ Set.Icc a 1, ∀ w : VS, ‖iaLin n s w‖ ≤ K1 * ‖w‖ := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn
    (f := fun u : ℝ => iaLinK n u)
    ((continuousOn_iaLinK n).mono (fun u hu => by
      simp only [Set.mem_Icc] at hu
      exact lt_of_lt_of_le ha hu.1))
  have hK0 : 0 ≤ K := by
    have h : iaLinK n a ≤ K := by
      have h' := hK a ⟨le_rfl, ha1⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (iaLinK_nonneg n a)] using h'
    linarith [iaLinK_nonneg n a]
  refine ⟨10 + 8 * K, by linarith, fun s hs w => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hKu : iaLinK n s ≤ K := by
    have h := hK s hs
    simpa [Real.norm_eq_abs, abs_of_nonneg (iaLinK_nonneg n s)] using h
  calc ‖iaLin n s w‖ ≤ (2 + 8 * iaLinK n s) * ‖w‖ := norm_iaLin_le n hs0 w
    _ ≤ (10 + 8 * K) * ‖w‖ := by
        have h : 2 + 8 * iaLinK n s ≤ 10 + 8 * K := by linarith
        exact mul_le_mul_of_nonneg_right h (norm_nonneg w)

/-- A norm bound for the base state on `[a,1]`. -/
lemma exists_baseZ_norm_bound {a : ℝ} :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ s ∈ Set.Icc a 1, ‖baseZ s‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn (f := baseZ)
    continuous_baseZ.continuousOn
  exact ⟨max M 1, le_max_right _ _, fun s hs => le_trans (hM s hs) (le_max_left _ _)⟩

/-- Uniform smallness of the difference of the `z`-derivatives of the perturbed and the base
`G`-data, at the base points. -/
lemma exists_fderiv_Gn_close_base (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ s ∈ Set.Icc a 1, ‖baseZ s‖ ≤ M) {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      ‖GnDeriv n h ε s (baseZ s) - baseGDeriv n s (baseZ s)‖ < η := by
  have hK : IsCompact (Set.Icc a 1 ×ˢ Metric.closedBall (0 : VS) M) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have h1 : Continuous fun q : ℝ × (ℝ × VS) => GnDeriv n h q.1 q.2.1 q.2.2 :=
    continuous_fderiv_Gn n hh
  have h2 : Continuous fun q : ℝ × (ℝ × VS) => baseGDeriv n q.2.1 q.2.2 := by
    have h := (continuous_fderiv_Gn n (h := fun _ => (0:ℝ)) contDiff_const)
    rw [GnDeriv_zero n] at h
    simpa using h
  have hcont : Continuous fun q : ℝ × (ℝ × VS) =>
      (GnDeriv n h q.1 q.2.1 q.2.2 - baseGDeriv n q.2.1 q.2.2) := h1.sub h2
  obtain ⟨εp, hεp, hε⟩ := exists_norm_small_of_continuous_zero
    (K := Set.Icc a 1 ×ˢ Metric.closedBall (0:VS) M) hK
    (F := fun ε p => GnDeriv n h ε p.1 p.2 - baseGDeriv n p.1 p.2) hcont hη
  refine ⟨εp, hεp, fun ε hε' s hs => ?_⟩
  have hmem : (s, baseZ s) ∈ Set.Icc a 1 ×ˢ Metric.closedBall (0 : VS) M :=
    ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hM s hs⟩
  have h0 : GnDeriv n h 0 s (baseZ s) - baseGDeriv n s (baseZ s) = 0 := by
    have hz : ((0:ℝ) • h) = fun _ : ℝ => (0:ℝ) := by funext u; simp
    have hfun : (fun z : VS => G n ((0:ℝ) • h) s z) = fun z : VS => baseG n s z := by
      funext z
      have hG : G n ((0:ℝ) • h) s z
          = Gw n s (((0:ℝ) • h) s) (deriv ((0:ℝ) • h) s) z := G_eq_Gw n ((0:ℝ) • h) s z
      rw [hG, hz, deriv_const]
      exact (baseG_eq_Gw n s z).symm
    simp only [GnDeriv, baseGDeriv]
    rw [hfun, sub_self]
  have hres := hε ε hε' (s, baseZ s) hmem
  have hres' : ‖GnDeriv n h ε s (baseZ s) - baseGDeriv n s (baseZ s)
      - (GnDeriv n h 0 s (baseZ s) - baseGDeriv n s (baseZ s))‖ < η := by
    simpa only using hres
  rw [h0, sub_zero] at hres'
  exact hres'

/-- Uniform continuity in the state variable of the `z`-derivative of the perturbed `G`-data. -/
lemma exists_fderiv_Gn_lipschitz_in_w (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ s ∈ Set.Icc a 1, ‖baseZ s‖ ≤ M) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc a 1, ∀ w w' : VS,
      ‖w - baseZ s‖ ≤ ρ → ‖w' - baseZ s‖ ≤ ρ →
      ‖GnDeriv n h ε s w - GnDeriv n h ε s w'‖ ≤ η := by
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc a 1 ×ˢ Metric.closedBall (0 : VS) (M + 1))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _))
  have hcont : ContinuousOn (fun p : ℝ × (ℝ × VS) => GnDeriv n h p.1 p.2.1 p.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc a 1 ×ˢ Metric.closedBall (0 : VS) (M + 1))) :=
    (continuous_fderiv_Gn n hh).continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := exists_uniform_close_of_continuousOn hK hcont hη
  refine ⟨min (δ / 4) (1 / 4), lt_min (by positivity) (by norm_num), ?_, ?_⟩
  · linarith [min_le_right (δ / 4) (1 / 4)]
  · intro ε hε s hs w w' hw hw'
    have hρ1 : min (δ / 4) (1 / 4) ≤ δ / 4 := min_le_left _ _
    have hmem : ∀ u : VS, ‖u - baseZ s‖ ≤ min (δ / 4) (1 / 4) →
        (ε, (s, u)) ∈ Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc a 1 ×ˢ Metric.closedBall (0 : VS) (M + 1)) := by
      intro u hu
      refine ⟨hε, hs, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h3 : ‖u - baseZ s‖ ≤ 1 := by linarith [min_le_right (δ / 4) (1 / 4)]
      calc ‖u‖ = ‖(u - baseZ s) + baseZ s‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - baseZ s‖ + ‖baseZ s‖ := norm_add_le _ _
        _ ≤ 1 + M := by linarith [hM s hs]
        _ ≤ M + 1 := by linarith
    have hmem_w := hmem w hw
    have hmem_w' := hmem w' hw'
    have hdist : dist (ε, (s, w)) (ε, (s, w')) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      have h2 : ‖w - w'‖ ≤ ‖w - baseZ s‖ + ‖w' - baseZ s‖ := by
        have h3 : w - w' = (w - baseZ s) - (w' - baseZ s) := by
          rw [sub_sub_sub_cancel_right]
        rw [h3]
        exact norm_sub_le _ _
      rw [dist_eq_norm]
      have h5 : ‖w - baseZ s‖ ≤ δ / 4 := le_trans hw hρ1
      have h6 : ‖w' - baseZ s‖ ≤ δ / 4 := le_trans hw' hρ1
      linarith [hδ0]
    have hres := hδ (ε, (s, w)) hmem_w (ε, (s, w')) hmem_w' hdist
    rw [dist_eq_norm] at hres
    exact le_of_lt hres

/-- The perturbed `G`-data as a function of the state variable, with explicit parameters. -/
lemma eq_Gw_fixed (n : ℕ) (h : ℝ → ℝ) (hd : Differentiable ℝ h) (ε s : ℝ) :
    (fun z : VS => G n (ε • h) s z)
      = fun z : VS => Gw n s (ε * h s) (ε * deriv h s) z := by
  funext z
  have hG : G n (ε • h) s z = Gw n s ((ε • h) s) (deriv (ε • h) s) z :=
    G_eq_Gw n (ε • h) s z
  rw [hG, deriv_smul_const_eq ε hd]
  rfl

/-- The `z`-derivative of the perturbed `G`-data, written through `Gw`. -/
lemma GnDeriv_eq (n : ℕ) (h : ℝ → ℝ) (hd : Differentiable ℝ h) (ε s : ℝ) (w : VS) :
    GnDeriv n h ε s w = fderiv ℝ (fun z : VS => Gw n s (ε * h s) (ε * deriv h s) z) w := by
  simp only [GnDeriv]
  rw [eq_Gw_fixed n h hd ε s]

lemma differentiableAt_G_fixed (n : ℕ) (h : ℝ → ℝ) (hd : Differentiable ℝ h) (ε s : ℝ) (w : VS) :
    DifferentiableAt ℝ (fun z : VS => G n (ε • h) s z) w := by
  have hcont : ContDiff ℝ ∞ (fun z : VS => Gw n s (ε * h s) (ε * deriv h s) z) := by
    have hmap : ContDiff ℝ ∞ (fun z : VS =>
        (((ε * h s, ε * deriv h s), (s, z)) : (ℝ × ℝ) × (ℝ × VS))) := by fun_prop
    exact (contDiff_Gw n).comp hmap
  rw [eq_Gw_fixed n h hd ε s]
  exact (hcont.differentiable (by simp)).differentiableAt

/-- Derivative of the normalised perturbed `G`-data in the state variable. -/
lemma hasFDerivAt_Gn (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (ε s : ℝ) (U : VS) :
    HasFDerivAt (fun U' : VS => Gn n Qe ρ (ε • h) s U')
      ((Qe.symm : VS →L[ℝ] VS) ∘L GnDeriv n h ε s (baseZ s + ρ • U)) U := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have h1 : HasFDerivAt (fun U' : VS => baseZ s + ρ • U') (ρ • (1 : VS →L[ℝ] VS)) U := by
    have hb : HasFDerivAt (fun U' : VS => (ρ • (1 : VS →L[ℝ] VS)) U') (ρ • (1 : VS →L[ℝ] VS)) U :=
      ContinuousLinearMap.hasFDerivAt _
    simpa using hb.const_add (baseZ s)
  have h2 : HasFDerivAt (fun z : VS => G n (ε • h) s z)
      (GnDeriv n h ε s (baseZ s + ρ • U)) (baseZ s + ρ • U) :=
    (differentiableAt_G_fixed n h hd ε s (baseZ s + ρ • U)).hasFDerivAt
  have h3 : HasFDerivAt (fun w : VS => (1 / ρ) • Qe.symm w)
      ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (G n (ε • h) s (baseZ s + ρ • U)) := by
    have hb : HasFDerivAt (fun w : VS => ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) w)
        ((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)) (G n (ε • h) s (baseZ s + ρ • U)) :=
      ContinuousLinearMap.hasFDerivAt _
    simpa using hb
  have hgb : HasFDerivAt ((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => G n (ε • h) s z))
      (((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp (GnDeriv n h ε s (baseZ s + ρ • U)))
      (baseZ s + ρ • U) := HasFDerivAt.comp (baseZ s + ρ • U) h3 h2
  have hmain : HasFDerivAt
      (((fun w : VS => (1 / ρ) • Qe.symm w) ∘ (fun z : VS => G n (ε • h) s z)) ∘
        (fun U' : VS => baseZ s + ρ • U'))
      ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp (GnDeriv n h ε s (baseZ s + ρ • U))).comp
        (ρ • (1 : VS →L[ℝ] VS))) U := HasFDerivAt.comp U hgb h1
  have heq : ((((1 / ρ) • (Qe.symm : VS →L[ℝ] VS)).comp (GnDeriv n h ε s (baseZ s + ρ • U))).comp
      (ρ • (1 : VS →L[ℝ] VS))) = ((Qe.symm : VS →L[ℝ] VS) ∘L GnDeriv n h ε s (baseZ s + ρ • U)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [map_smul, map_smul, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hρ0), one_smul]
  rw [heq] at hmain
  refine hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun U' => ?_)
  simp only [Function.comp_apply, Gn_eq]

/-- The contraction map `U ↦ U - Q(s)⁻¹ (Gn(s,U))` of the Volterra fixed point. -/
noncomputable def PhiG (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ ε : ℝ) (h : ℝ → ℝ) {a : ℝ}
    (ha : 0 < a) (s : ℝ) (U : VS) : VS :=
  U - (Qref n Qe ha s).symm (Gn n Qe ρ (ε • h) s U)

lemma hasFDerivAt_PhiG (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 < a) (ε s : ℝ) (U : VS) :
    HasFDerivAt (fun U' : VS => PhiG n Qe ρ ε h ha s U')
      (ContinuousLinearMap.id ℝ VS - (iaLin n (max s (a / 2))).toContinuousLinearMap ∘L
        GnDeriv n h ε s (baseZ s + ρ • U)) U := by
  have hGn := hasFDerivAt_Gn n Qe hρ0 hh ε s U
  have hQ : HasFDerivAt (fun w : VS => ((Qref n Qe ha s).symm : VS →L[ℝ] VS) w)
      (((Qref n Qe ha s).symm : VS →L[ℝ] VS)) (Gn n Qe ρ (ε • h) s U) :=
    ContinuousLinearMap.hasFDerivAt _
  have hcomp : HasFDerivAt ((fun w : VS => ((Qref n Qe ha s).symm : VS →L[ℝ] VS) w) ∘
      (fun U' : VS => Gn n Qe ρ (ε • h) s U'))
      (((Qref n Qe ha s).symm : VS →L[ℝ] VS) ∘L
        ((Qe.symm : VS →L[ℝ] VS) ∘L GnDeriv n h ε s (baseZ s + ρ • U))) U :=
    HasFDerivAt.comp U hQ hGn
  have hsub := (hasFDerivAt_id U).sub hcomp
  have hcomp' : (((Qref n Qe ha s).symm : VS →L[ℝ] VS) ∘L
      ((Qe.symm : VS →L[ℝ] VS) ∘L GnDeriv n h ε s (baseZ s + ρ • U)))
      = (iaLin n (max s (a / 2))).toContinuousLinearMap ∘L GnDeriv n h ε s (baseZ s + ρ • U) := by
    rw [← ContinuousLinearMap.comp_assoc, Qref_symm_comp_Qe]
  rw [hcomp'] at hsub
  exact hsub

/-- `iaLin` is a left inverse of `jacLin`, as continuous linear maps. -/
lemma iaLin_comp_jacLin (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (iaLin n s).toContinuousLinearMap ∘L (jacLin n s).toContinuousLinearMap
      = ContinuousLinearMap.id ℝ VS := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [show (jacLin n s).toContinuousLinearMap v = jacLin n s v from rfl]
  rw [show (iaLin n s).toContinuousLinearMap (jacLin n s v) = iaLin n s (jacLin n s v) from rfl]
  exact iaLin_jacLin hs v

/-- **The contraction of the `G`-row.**  For small `ρ` and small `ε` the map
`U ↦ U - Q(s)⁻¹ (Gn(s,U))` is `1/2`-Lipschitz on the unit ball, uniformly in `s ∈ [a,1]`. -/
lemma exists_lipschitz_PhiG (n : ℕ) (hn : 2 ≤ n) (Qe : VS ≃L[ℝ] VS) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ ρ ∈ Set.Ioo (0:ℝ) (1/2), ∃ εp : ℝ, 0 < εp ∧
      ∀ ε ∈ Set.Ioo (0:ℝ) εp, ∀ s ∈ Set.Icc a 1,
        LipschitzOnWith (1/2) (fun U : VS => PhiG n Qe ρ ε h ha s U)
          (Metric.closedBall (0 : VS) 1) := by
  obtain ⟨M, hM1, hM⟩ := exists_baseZ_norm_bound (a := a)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  obtain ⟨K1, hK1pos, hK1⟩ := exists_norm_iaLin_le n ha ha1
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ 2 * K1 * η ≤ 1 / 2 := by
    refine ⟨1 / (4 * (K1 + 1)), by positivity, ?_⟩
    have h1 : 0 < K1 + 1 := by linarith
    have h2 : K1 / (K1 + 1) ≤ 1 := by
      rw [div_le_one h1]; linarith
    calc 2 * K1 * (1 / (4 * (K1 + 1))) = (K1 / (K1 + 1)) * (1 / 2) := by field_simp; ring
      _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ = 1 / 2 := by ring
  obtain ⟨ρ0, hρ0pos, hρ0half, hlipw⟩ :=
    exists_fderiv_Gn_lipschitz_in_w n hh hM0 hM (η := η) hηpos
  obtain ⟨εp, hεp, hclose⟩ := exists_fderiv_Gn_close_base n hh hM0 hM (η := η) hηpos
  refine ⟨ρ0, ⟨hρ0pos, hρ0half⟩, min εp 1, lt_min hεp one_pos, fun ε hε s hs => ?_⟩
  have hεp' : ε < εp := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hε.2 (min_le_right _ _))
  have hρ2 : ρ0 ≤ 1 / 2 := hρ0half.le
  have hK1s : ‖(iaLin n s).toContinuousLinearMap‖ ≤ K1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK1pos.le (fun w => ?_)
    calc ‖((iaLin n s).toContinuousLinearMap) w‖ = ‖iaLin n s w‖ := rfl
      _ ≤ K1 * ‖w‖ := hK1 s hs w
  have hmax : max s (a / 2) = s := by
    refine max_eq_left ?_
    linarith [hs.1]
  have hjac : (jacLin n s).toContinuousLinearMap = baseGDeriv n s (baseZ s) :=
    jacLin_eq_fderiv hn s
  have hdereq : ∀ U : VS,
      fderiv ℝ (fun U' : VS => PhiG n Qe ρ0 ε h ha s U') U
        = (iaLin n s).toContinuousLinearMap ∘L
            ((jacLin n s).toContinuousLinearMap - GnDeriv n h ε s (baseZ s + ρ0 • U)) := by
    intro U
    rw [(hasFDerivAt_PhiG n Qe hρ0pos hh ha ε s U).fderiv, hmax,
      ← iaLin_comp_jacLin n (lt_of_lt_of_le ha hs.1)]
    rw [ContinuousLinearMap.comp_sub]
  have hU1 : ∀ U ∈ Metric.closedBall (0 : VS) 1, ‖U‖ ≤ 1 := by
    intro U hU
    simpa [Metric.mem_closedBall, dist_zero_right] using hU
  have hbound : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      ‖fderiv ℝ (fun U' : VS => PhiG n Qe ρ0 ε h ha s U') U‖ ≤ 1 / 2 := by
    intro U hU
    have hU1' := hU1 U hU
    have hvar : ‖GnDeriv n h ε s (baseZ s) - GnDeriv n h ε s (baseZ s + ρ0 • U)‖ ≤ η := by
      have hw1 : ‖baseZ s + ρ0 • U - baseZ s‖ ≤ ρ0 := by
        rw [add_sub_cancel_left]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0pos]
        calc ρ0 * ‖U‖ ≤ ρ0 * 1 := mul_le_mul_of_nonneg_left hU1' hρ0pos.le
          _ = ρ0 := by ring
      have hw2 : ‖baseZ s - baseZ s‖ ≤ ρ0 := by
        rw [sub_self, norm_zero]
        exact hρ0pos.le
      have hh' := hlipw ε ⟨hε.1.le, hε1⟩ s hs (baseZ s + ρ0 • U) (baseZ s) hw1 hw2
      simpa [norm_sub_rev] using hh'
    have hδ : ‖baseGDeriv n s (baseZ s) - GnDeriv n h ε s (baseZ s)‖ ≤ η := by
      have h := (hclose ε ⟨hε.1, hεp'⟩ s hs).le
      simpa [GnDeriv, baseGDeriv, norm_sub_rev] using h
    have hnorm : ‖((jacLin n s).toContinuousLinearMap
        - GnDeriv n h ε s (baseZ s + ρ0 • U))‖ ≤ 2 * η := by
      have hsplit : (jacLin n s).toContinuousLinearMap - GnDeriv n h ε s (baseZ s + ρ0 • U)
          = (baseGDeriv n s (baseZ s) - GnDeriv n h ε s (baseZ s))
            + (GnDeriv n h ε s (baseZ s) - GnDeriv n h ε s (baseZ s + ρ0 • U)) := by
        rw [hjac]
        abel
      rw [hsplit]
      calc ‖(baseGDeriv n s (baseZ s) - GnDeriv n h ε s (baseZ s))
              + (GnDeriv n h ε s (baseZ s) - GnDeriv n h ε s (baseZ s + ρ0 • U))‖
          ≤ ‖baseGDeriv n s (baseZ s) - GnDeriv n h ε s (baseZ s)‖
            + ‖GnDeriv n h ε s (baseZ s) - GnDeriv n h ε s (baseZ s + ρ0 • U)‖ := norm_add_le _ _
        _ ≤ η + η := add_le_add hδ hvar
        _ = 2 * η := by ring
    rw [hdereq U]
    calc ‖(iaLin n s).toContinuousLinearMap ∘L
            ((jacLin n s).toContinuousLinearMap - GnDeriv n h ε s (baseZ s + ρ0 • U))‖
        ≤ ‖(iaLin n s).toContinuousLinearMap‖ *
            ‖(jacLin n s).toContinuousLinearMap - GnDeriv n h ε s (baseZ s + ρ0 • U)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K1 * (2 * η) := by
          refine mul_le_mul hK1s hnorm (norm_nonneg _) hK1pos.le
      _ ≤ 1 / 2 := by linarith [hη]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hdiff : ∀ U ∈ Metric.closedBall (0 : VS) 1,
      DifferentiableAt ℝ (fun U' : VS => PhiG n Qe ρ0 ε h ha s U') U := fun U _ =>
    (hasFDerivAt_PhiG n Qe hρ0pos hh ha ε s U).differentiableAt
  have := dist_image_sub_le_of_norm_fderiv_le (f := fun U : VS => PhiG n Qe ρ0 ε h ha s U)
    hdiff hbound (convex_closedBall _ _) hx hy
  simpa using this

/-- Row-2 coefficient of the Volterra kernel `Θ`, as a function of the parameters
`p = (ε, (σ, w))` and the evaluation point `s`:
`(d/ds)^{n+1} ((σ w + ε h σ)² - (· w + ε h ·)²)^n`. -/
noncomputable def thetaP (n : ℕ) (h : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) (s : ℝ) : ℝ :=
  iteratedDeriv (n + 1) (fun u : ℝ =>
    ((p.2.1 * p.2.2 + p.1 * h p.2.1) ^ 2 - (u * p.2.2 + p.1 * h u) ^ 2) ^ n) s

/-- Row-3 coefficient of `Θ` (with the `lineSlope` factor). -/
noncomputable def thetaQ (n : ℕ) (h : ℝ → ℝ) (p : ℝ × (ℝ × ℝ)) (s : ℝ) : ℝ :=
  iteratedDeriv n (fun u : ℝ =>
    ((p.2.1 * p.2.2 + p.1 * h p.2.1) ^ 2 - (u * p.2.2 + p.1 * h u) ^ 2) ^ (n - 1)
      * (p.2.2 + p.1 * deriv h u)) s

/-- Joint smoothness of the row-2 coefficient. -/
lemma contDiff_thetaP (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => thetaP n h q.1 q.2) := by
  have hG : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
      ((q.1.2.1 * q.1.2.2 + q.1.1 * h q.1.2.1) ^ 2
        - (q.2 * q.1.2.2 + q.1.1 * h q.2) ^ 2) ^ n) := by fun_prop
  exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 1)
    (G := fun (p : ℝ × (ℝ × ℝ)) (u : ℝ) =>
      ((p.2.1 * p.2.2 + p.1 * h p.2.1) ^ 2 - (u * p.2.2 + p.1 * h u) ^ 2) ^ n) hG

/-- Joint smoothness of the row-3 coefficient. -/
lemma contDiff_thetaQ (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => thetaQ n h q.1 q.2) := by
  have hG : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
      ((q.1.2.1 * q.1.2.2 + q.1.1 * h q.1.2.1) ^ 2
        - (q.2 * q.1.2.2 + q.1.1 * h q.2) ^ 2) ^ (n - 1)
        * (q.1.2.2 + q.1.1 * deriv h q.2)) := by fun_prop
  exact contDiffOn_parametric_iteratedDeriv_gen (k := n)
    (G := fun (p : ℝ × (ℝ × ℝ)) (u : ℝ) =>
      ((p.2.1 * p.2.2 + p.1 * h p.2.1) ^ 2 - (u * p.2.2 + p.1 * h u) ^ 2) ^ (n - 1)
        * (p.2.2 + p.1 * deriv h u)) hG

/-- The compact parameter box `{ε ∈ [0,1]} × {σ ∈ [a,1]} × {w ∈ [-2,2]} × {s ∈ [a,1]}`. -/
def thetaBox (a : ℝ) : Set ((ℝ × (ℝ × ℝ)) × ℝ) :=
  (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc a 1 ×ˢ Set.Icc (-2:ℝ) 2)) ×ˢ Set.Icc a 1

lemma isCompact_thetaBox (a : ℝ) : IsCompact (thetaBox a) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc

lemma mem_thetaBox {a ε σ w s : ℝ} :
    ((ε, (σ, w)), s) ∈ thetaBox a ↔
      ε ∈ Set.Icc (0:ℝ) 1 ∧ σ ∈ Set.Icc a 1 ∧ w ∈ Set.Icc (-2:ℝ) 2 ∧ s ∈ Set.Icc a 1 := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hε, h3⟩ := h1
    obtain ⟨hσ, hw⟩ := h3
    exact ⟨hε, hσ, hw, h2⟩
  · intro ⟨hε, hσ, hw, hs⟩
    exact ⟨⟨hε, hσ, hw⟩, hs⟩

/-- **Coefficient bound on the box.** -/
lemma exists_bound_on_thetaBox {F : (ℝ × (ℝ × ℝ)) × ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, |F ((ε, (σ, w)), s)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_thetaBox a).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun ε hε σ hσ w hw s hs =>
    by simpa [Real.norm_eq_abs] using hC _ (mem_thetaBox.mpr ⟨hε, hσ, hw, hs⟩)⟩

/-- The linear part of the inclusion `(w, s) ↦ ((ε, (σ, w)), s)`. -/
def thetaInc : (ℝ × ℝ) →L[ℝ] ((ℝ × (ℝ × ℝ)) × ℝ) :=
  ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
    ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma hasFDerivAt_thetaInc (ε σ w s : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => ((ε, (σ, q.1)), q.2)) thetaInc (w, s) := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => ((ε, (σ, q.1)), q.2))
      (((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) (w, s) := by fun_prop
  exact h

lemma fderiv_thetaInc (ε σ w s : ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => ((ε, (σ, q.1)), q.2)) (w, s) = thetaInc :=
  (hasFDerivAt_thetaInc ε σ w s).fderiv

/-- **Derivative bound on the box.**  For a `C^∞` function `F` of the parameters
`((ε, (σ, w)), s)`, the derivative in `(w, s)` (with `ε, σ` fixed) is bounded on the box. -/
lemma exists_bound_fderiv_thetaBox {F : (ℝ × (ℝ × ℝ)) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      ‖fderiv ℝ (fun q : ℝ × ℝ => F ((ε, (σ, q.1)), q.2)) (w, s)‖ ≤ C := by
  have hFd : Continuous (fderiv ℝ F) := ContDiff.continuous_fderiv hF (by simp)
  obtain ⟨C, hC⟩ := (isCompact_thetaBox a).exists_bound_of_continuousOn hFd.continuousOn
  refine ⟨C * ‖thetaInc‖, fun ε hε σ hσ w hw s hs => ?_⟩
  have hkey : fderiv ℝ (fun q : ℝ × ℝ => F ((ε, (σ, q.1)), q.2)) (w, s)
      = (fderiv ℝ F ((ε, (σ, w)), s)).comp thetaInc := by
    have hc : HasFDerivAt F (fderiv ℝ F ((ε, (σ, w)), s)) ((ε, (σ, w)), s) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp := hc.comp (w, s) (hasFDerivAt_thetaInc ε σ w s)
    have hfun : (fun q : ℝ × ℝ => F ((ε, (σ, q.1)), q.2))
        = F ∘ (fun q : ℝ × ℝ => ((ε, (σ, q.1)), q.2)) := rfl
    rw [hfun, hcomp.fderiv]
  rw [hkey]
  calc ‖(fderiv ℝ F ((ε, (σ, w)), s)).comp thetaInc‖
      ≤ ‖fderiv ℝ F ((ε, (σ, w)), s)‖ * ‖thetaInc‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * ‖thetaInc‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact hC _ (mem_thetaBox.mpr ⟨hε, hσ, hw, hs⟩)

/-- The `(w, s)`-slice of the row-2 coefficient `thetaP` (with `ε, σ` fixed). -/
noncomputable def thetaPs (n : ℕ) (h : ℝ → ℝ) (ε σ : ℝ) (q : ℝ × ℝ) : ℝ :=
  iteratedDeriv (n + 1) (fun u : ℝ =>
    ((σ * q.1 + ε * h σ) ^ 2 - (u * q.1 + ε * h u) ^ 2) ^ n) q.2

/-- The `(w, s)`-slice of the row-3 coefficient `thetaQ` (with `ε, σ` fixed). -/
noncomputable def thetaQs (n : ℕ) (h : ℝ → ℝ) (ε σ : ℝ) (q : ℝ × ℝ) : ℝ :=
  iteratedDeriv n (fun u : ℝ =>
    ((σ * q.1 + ε * h σ) ^ 2 - (u * q.1 + ε * h u) ^ 2) ^ (n - 1) * (q.1 + ε * deriv h u)) q.2

lemma thetaPs_eq (n : ℕ) (h : ℝ → ℝ) (ε σ : ℝ) (q : ℝ × ℝ) :
    thetaPs n h ε σ q = thetaP n h (ε, (σ, q.1)) q.2 := rfl

lemma thetaQs_eq (n : ℕ) (h : ℝ → ℝ) (ε σ : ℝ) (q : ℝ × ℝ) :
    thetaQs n h ε σ q = thetaQ n h (ε, (σ, q.1)) q.2 := rfl

lemma contDiff_thetaPs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (ε σ : ℝ) :
    ContDiff ℝ ∞ (thetaPs n h ε σ) := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      ((σ * q.1 + ε * h σ) ^ 2 - (q.2 * q.1 + ε * h q.2) ^ 2) ^ n) := by fun_prop
  exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 1)
    (G := fun (p : ℝ) (u : ℝ) => ((σ * p + ε * h σ) ^ 2 - (u * p + ε * h u) ^ 2) ^ n) hG

lemma contDiff_thetaQs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (ε σ : ℝ) :
    ContDiff ℝ ∞ (thetaQs n h ε σ) := by
  have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      ((σ * q.1 + ε * h σ) ^ 2 - (q.2 * q.1 + ε * h q.2) ^ 2) ^ (n - 1)
        * (q.1 + ε * deriv h q.2)) := by fun_prop
  exact contDiffOn_parametric_iteratedDeriv_gen (k := n)
    (G := fun (p : ℝ) (u : ℝ) =>
      ((σ * p + ε * h σ) ^ 2 - (u * p + ε * h u) ^ 2) ^ (n - 1) * (p + ε * deriv h u)) hG

/-- `(w, s)`-derivative bound for the row-2 coefficient. -/
lemma exists_bound_fderiv_thetaPs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, ‖fderiv ℝ (thetaPs n h ε σ) (w, s)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv_thetaBox (contDiff_thetaP n hh) a
  refine ⟨C, fun ε hε σ hσ w hw s hs => ?_⟩
  have heq : thetaPs n h ε σ = fun q : ℝ × ℝ => thetaP n h (ε, (σ, q.1)) q.2 := by
    funext q
    rfl
  rw [heq]
  exact hC ε hε σ hσ w hw s hs

lemma exists_bound_fderiv_thetaQs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, ‖fderiv ℝ (thetaQs n h ε σ) (w, s)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv_thetaBox (contDiff_thetaQ n hh) a
  refine ⟨C, fun ε hε σ hσ w hw s hs => ?_⟩
  have heq : thetaQs n h ε σ = fun q : ℝ × ℝ => thetaQ n h (ε, (σ, q.1)) q.2 := by
    funext q
    rfl
  rw [heq]
  exact hC ε hε σ hσ w hw s hs

/-- **Lipschitz bound in the `w`-slot** (row 2). -/
lemma exists_lipschitz_thetaPs_w (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ K : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ s ∈ Set.Icc a 1,
      ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2,
      |thetaPs n h ε σ (w, s) - thetaPs n h ε σ (w', s)| ≤ K * |w - w'| := by
  obtain ⟨K, hK⟩ := exists_bound_fderiv_thetaPs n hh a
  refine ⟨K, fun ε hε σ hσ s hs w hw w' hw' => ?_⟩
  have hconv : Convex ℝ (Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1) :=
    Convex.prod (convex_Icc (-2) 2) (convex_Icc a 1)
  have hdiff : ∀ q ∈ Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1,
      DifferentiableAt ℝ (thetaPs n h ε σ) q :=
    fun q _ => ((contDiff_thetaPs n hh ε σ).differentiable (by simp)).differentiableAt
  have hb : ∀ q ∈ Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1,
      ‖fderiv ℝ (thetaPs n h ε σ) q‖ ≤ K :=
    fun q hq => hK ε hε σ hσ q.1 hq.1 q.2 hq.2
  have hres := dist_image_sub_le_of_norm_fderiv_le hdiff hb hconv
    (Set.mk_mem_prod hw hs) (Set.mk_mem_prod hw' hs)
  have hR : dist (w, s) (w', s) = |w - w'| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_eq_left (abs_nonneg _)
  rw [Real.dist_eq, hR] at hres
  exact hres

/-- **Lipschitz bound in the `w`-slot** (row 3). -/
lemma exists_lipschitz_thetaQs_w (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ K : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ s ∈ Set.Icc a 1,
      ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2,
      |thetaQs n h ε σ (w, s) - thetaQs n h ε σ (w', s)| ≤ K * |w - w'| := by
  obtain ⟨K, hK⟩ := exists_bound_fderiv_thetaQs n hh a
  refine ⟨K, fun ε hε σ hσ s hs w hw w' hw' => ?_⟩
  have hconv : Convex ℝ (Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1) :=
    Convex.prod (convex_Icc (-2) 2) (convex_Icc a 1)
  have hdiff : ∀ q ∈ Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1,
      DifferentiableAt ℝ (thetaQs n h ε σ) q :=
    fun q _ => ((contDiff_thetaQs n hh ε σ).differentiable (by simp)).differentiableAt
  have hb : ∀ q ∈ Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc a 1,
      ‖fderiv ℝ (thetaQs n h ε σ) q‖ ≤ K :=
    fun q hq => hK ε hε σ hσ q.1 hq.1 q.2 hq.2
  have hres := dist_image_sub_le_of_norm_fderiv_le hdiff hb hconv
    (Set.mk_mem_prod hw hs) (Set.mk_mem_prod hw' hs)
  have hR : dist (w, s) (w', s) = |w - w'| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_eq_left (abs_nonneg _)
  rw [Real.dist_eq, hR] at hres
  exact hres

/-- Coefficient bound for the row-2 coefficient on the parameter box. -/
lemma exists_bound_thetaP (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, |thetaP n h (ε, (σ, w)) s| ≤ C :=
  exists_bound_on_thetaBox ((contDiff_thetaP n hh).continuous) a

/-- Coefficient bound for the row-3 coefficient on the parameter box. -/
lemma exists_bound_thetaQ (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, |thetaQ n h (ε, (σ, w)) s| ≤ C :=
  exists_bound_on_thetaBox ((contDiff_thetaQ n hh).continuous) a

/-- `(w, s)`-derivative bound for the row-2 coefficient on the box. -/
lemma exists_bound_fderiv_thetaP (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      ‖fderiv ℝ (fun q : ℝ × ℝ => thetaP n h (ε, (σ, q.1)) q.2) (w, s)‖ ≤ C :=
  exists_bound_fderiv_thetaBox (contDiff_thetaP n hh) a

/-- `(w, s)`-derivative bound for the row-3 coefficient on the box. -/
lemma exists_bound_fderiv_thetaQ (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      ‖fderiv ℝ (fun q : ℝ × ℝ => thetaQ n h (ε, (σ, q.1)) q.2) (w, s)‖ ≤ C :=
  exists_bound_fderiv_thetaBox (contDiff_thetaQ n hh) a

/-- Coefficient bound for the row-2 coefficient, in `(w, s)`-slice form. -/
lemma exists_bound_thetaPs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, |thetaPs n h ε σ (w, s)| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_thetaP n hh a
  refine ⟨C, fun ε hε σ hσ w hw s hs => ?_⟩
  have h : thetaPs n h ε σ (w, s) = thetaP n h (ε, (σ, w)) s := thetaPs_eq n h ε σ (w, s)
  rw [h]
  exact hC ε hε σ hσ w hw s hs

/-- Coefficient bound for the row-3 coefficient, in `(w, s)`-slice form. -/
lemma exists_bound_thetaQs (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1, |thetaQs n h ε σ (w, s)| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_thetaQ n hh a
  refine ⟨C, fun ε hε σ hσ w hw s hs => ?_⟩
  have h : thetaQs n h ε σ (w, s) = thetaQ n h (ε, (σ, w)) s := thetaQs_eq n h ε σ (w, s)
  rw [h]
  exact hC ε hε σ hσ w hw s hs

/-- Componentwise subtraction of two states. -/
lemma mk4_sub (a b c d a' b' c' d' : ℝ) :
    RyaboginVolterra.mk4 a b c d - RyaboginVolterra.mk4 a' b' c' d'
      = RyaboginVolterra.mk4 (a - a') (b - b') (c - c') (d - d') := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
  funext i
  fin_cases i <;> simp [RyaboginVolterra.mk4_apply]

/-- Coordinate bound for `zb + ρ • U`. -/
lemma abs_coord_add_smul_le (zb U : VS) {ρ : ℝ} (hρ : 0 ≤ ρ) (i : Fin 4) :
    |(zb + ρ • U) i| ≤ |zb i| + ρ * ‖U‖ := by
  have h1 : (zb + ρ • U) i = zb i + ρ * U i := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1]
  refine le_trans (abs_add_le _ _) ?_
  refine add_le_add le_rfl ?_
  rw [abs_mul, abs_of_nonneg hρ]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_norm_state U i) hρ

/-- Difference bound for the coordinates of `zb + ρ • U` and `zb + ρ • U'`. -/
lemma abs_coord_add_smul_sub_le (zb U U' : VS) {ρ : ℝ} (hρ : 0 ≤ ρ) (i : Fin 4) :
    |(zb + ρ • U) i - (zb + ρ • U') i| ≤ ρ * ‖U - U'‖ := by
  have h1 : (zb + ρ • U) i - (zb + ρ • U') i = ρ * (U - U') i := by
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, abs_mul, abs_of_nonneg hρ]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_norm_state (U - U') i) hρ

/-- Four-term arithmetic bound behind the Lipschitz estimate for the `Θ`-row shape. -/
lemma abs_coeff_mul_sub_le {P : ℝ → ℝ} {z0 z1 z2 z3 z0' z1' z2' z3' CP KP M Δ : ℝ}
    (hP0 : |P z0| ≤ CP) (hP1 : |P z1| ≤ CP)
    (hK0 : |P z0 - P z0'| ≤ KP * Δ) (hK1 : |P z1 - P z1'| ≤ KP * Δ)
    (h2 : |z2 - z2'| ≤ Δ) (h3 : |z3 - z3'| ≤ Δ)
    (h2' : |z2'| ≤ M) (h3' : |z3'| ≤ M) (hΔ : 0 ≤ Δ) (hCP : 0 ≤ CP) (hKP : 0 ≤ KP)
    (hM : 0 ≤ M) :
    |(P z0 * z2 + P z1 * z3) - (P z0' * z2' + P z1' * z3')| ≤ 2 * Δ * (CP + KP * M) := by
  have hid : (P z0 * z2 + P z1 * z3) - (P z0' * z2' + P z1' * z3')
      = P z0 * (z2 - z2') + (P z0 - P z0') * z2' + P z1 * (z3 - z3')
        + (P z1 - P z1') * z3' := by ring
  rw [hid]
  have hKPΔ : 0 ≤ KP * Δ := mul_nonneg hKP hΔ
  have b1 : |P z0 * (z2 - z2')| ≤ CP * Δ := by
    rw [abs_mul]
    exact mul_le_mul hP0 h2 (abs_nonneg _) hCP
  have b2 : |(P z0 - P z0') * z2'| ≤ KP * Δ * M := by
    rw [abs_mul]
    calc |P z0 - P z0'| * |z2'| ≤ (KP * Δ) * M := mul_le_mul hK0 h2' (abs_nonneg _) hKPΔ
      _ = KP * Δ * M := by ring
  have b3 : |P z1 * (z3 - z3')| ≤ CP * Δ := by
    rw [abs_mul]
    exact mul_le_mul hP1 h3 (abs_nonneg _) hCP
  have b4 : |(P z1 - P z1') * z3'| ≤ KP * Δ * M := by
    rw [abs_mul]
    calc |P z1 - P z1'| * |z3'| ≤ (KP * Δ) * M := mul_le_mul hK1 h3' (abs_nonneg _) hKPΔ
      _ = KP * Δ * M := by ring
  have a1 := abs_add_le (P z0 * (z2 - z2') + (P z0 - P z0') * z2' + P z1 * (z3 - z3'))
    ((P z1 - P z1') * z3')
  have a2 := abs_add_le (P z0 * (z2 - z2') + (P z0 - P z0') * z2') (P z1 * (z3 - z3'))
  have a3 := abs_add_le (P z0 * (z2 - z2')) ((P z0 - P z0') * z2')
  have key : |P z0 * (z2 - z2') + (P z0 - P z0') * z2' + P z1 * (z3 - z3')
      + (P z1 - P z1') * z3'|
      ≤ |P z0 * (z2 - z2')| + |(P z0 - P z0') * z2'| + |P z1 * (z3 - z3')|
        + |(P z1 - P z1') * z3'| := by linarith
  calc |P z0 * (z2 - z2') + (P z0 - P z0') * z2' + P z1 * (z3 - z3')
        + (P z1 - P z1') * z3'|
      ≤ CP * Δ + KP * Δ * M + CP * Δ + KP * Δ * M := by linarith
    _ = 2 * Δ * (CP + KP * M) := by ring

/-- The shape of the `Θ`-row: two coefficient functions `P Q`, the first applied to the
*negated* first coordinate of `z = zb + ρ • U` (as in `Theta_apply_two/three`), acting on the last
two coordinates. -/
noncomputable def thetaShape (P Q : ℝ → ℝ) (zb : VS) (ρ : ℝ) (U : VS) : VS :=
  RyaboginVolterra.mk4 (-((zb + ρ • U) 2)) (-((zb + ρ • U) 3))
    (P (-((zb + ρ • U) 0)) * (zb + ρ • U) 2 + P ((zb + ρ • U) 1) * (zb + ρ • U) 3)
    (Q (-((zb + ρ • U) 0)) * (zb + ρ • U) 2 + Q ((zb + ρ • U) 1) * (zb + ρ • U) 3)

/-- **Lipschitz bound for the `Θ`-row shape.** -/
lemma norm_thetaShape_sub_le {P Q : ℝ → ℝ} {zb : VS} {ρ CP CQ KP KQ M : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hz0 : |zb 0| ≤ 1) (hz1 : |zb 1| ≤ 1) (hz2 : |zb 2| ≤ M) (hz3 : |zb 3| ≤ M) (hM : 0 ≤ M)
    (hCP0 : 0 ≤ CP) (hCQ0 : 0 ≤ CQ) (hKP0 : 0 ≤ KP) (hKQ0 : 0 ≤ KQ)
    (hP : ∀ w ∈ Set.Icc (-2:ℝ) 2, |P w| ≤ CP)
    (hQ : ∀ w ∈ Set.Icc (-2:ℝ) 2, |Q w| ≤ CQ)
    (hPK : ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2, |P w - P w'| ≤ KP * |w - w'|)
    (hQK : ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2, |Q w - Q w'| ≤ KQ * |w - w'|)
    {U U' : VS} (hU : U ∈ Metric.closedBall (0 : VS) 1)
    (hU' : U' ∈ Metric.closedBall (0 : VS) 1) :
    ‖thetaShape P Q zb ρ U - thetaShape P Q zb ρ U'‖
      ≤ ρ * (2 + 2 * (CP + KP * (M + 1)) + 2 * (CQ + KQ * (M + 1))) * ‖U - U'‖ := by
  have hU1 : ‖U‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hU
  have hU1' : ‖U'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hU'
  set z : VS := zb + ρ • U with hzdef
  set z' : VS := zb + ρ • U' with hz'def
  have hΔ : 0 ≤ ρ * ‖U - U'‖ := mul_nonneg hρ0.le (norm_nonneg _)
  -- coordinate bounds
  have hdz : ∀ i : Fin 4, |z i - z' i| ≤ ρ * ‖U - U'‖ := fun i =>
    abs_coord_add_smul_sub_le zb U U' hρ0.le i
  have hzmem : ∀ i : Fin 4, |z i| ≤ |zb i| + ρ * ‖U‖ := fun i =>
    abs_coord_add_smul_le zb U hρ0.le i
  have hzmem' : ∀ i : Fin 4, |z' i| ≤ |zb i| + ρ * ‖U'‖ := fun i =>
    abs_coord_add_smul_le zb U' hρ0.le i
  have hmem2 : ∀ w : ℝ, |w| ≤ 2 → w ∈ Set.Icc (-2:ℝ) 2 := by
    intro w hw
    exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩
  have hb0 : |z 0| ≤ 2 := by
    have h1 : ρ * ‖U‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1 hρ0.le
    linarith [hzmem 0, hz0, h1, hρ1]
  have hb1 : |z 1| ≤ 2 := by
    have h1 : ρ * ‖U‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1 hρ0.le
    linarith [hzmem 1, hz1, h1, hρ1]
  have hb0' : |z' 0| ≤ 2 := by
    have h1 : ρ * ‖U'‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1' hρ0.le
    linarith [hzmem' 0, hz0, h1, hρ1]
  have hb1' : |z' 1| ≤ 2 := by
    have h1 : ρ * ‖U'‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1' hρ0.le
    linarith [hzmem' 1, hz1, h1, hρ1]
  have hb2 : |z 2| ≤ M + 1 := by
    have h1 : ρ * ‖U‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1 hρ0.le
    linarith [hzmem 2, hz2, h1, hρ1]
  have hb3 : |z 3| ≤ M + 1 := by
    have h1 : ρ * ‖U‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1 hρ0.le
    linarith [hzmem 3, hz3, h1, hρ1]
  have hb2' : |z' 2| ≤ M + 1 := by
    have h1 : ρ * ‖U'‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1' hρ0.le
    linarith [hzmem' 2, hz2, h1, hρ1]
  have hb3' : |z' 3| ≤ M + 1 := by
    have h1 : ρ * ‖U'‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hU1' hρ0.le
    linarith [hzmem' 3, hz3, h1, hρ1]
  have hnb0 : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hb0
  have hnb1 : |-(z 1)| ≤ 2 := by rw [abs_neg]; exact hb1
  have hnb0' : |-(z' 0)| ≤ 2 := by rw [abs_neg]; exact hb0'
  have hnb1' : |-(z' 1)| ≤ 2 := by rw [abs_neg]; exact hb1'
  have hdz0 : |-(z 0) - -(z' 0)| ≤ ρ * ‖U - U'‖ := by
    rw [show -(z 0) - -(z' 0) = -((z 0) - (z' 0)) by ring, abs_neg]
    exact hdz 0
  have hdz1 : |-(z 1) - -(z' 1)| ≤ ρ * ‖U - U'‖ := by
    rw [show -(z 1) - -(z' 1) = -((z 1) - (z' 1)) by ring, abs_neg]
    exact hdz 1
  have hP0 : |P (-(z 0))| ≤ CP := hP _ (hmem2 _ hnb0)
  have hP1 : |P (z 1)| ≤ CP := hP _ (hmem2 _ hb1)
  have hP0' : |P (-(z' 0))| ≤ CP := hP _ (hmem2 _ hnb0')
  have hP1' : |P (z' 1)| ≤ CP := hP _ (hmem2 _ hb1')
  have hQ0 : |Q (-(z 0))| ≤ CQ := hQ _ (hmem2 _ hnb0)
  have hQ1 : |Q (z 1)| ≤ CQ := hQ _ (hmem2 _ hb1)
  have hQ0' : |Q (-(z' 0))| ≤ CQ := hQ _ (hmem2 _ hnb0')
  have hQ1' : |Q (z' 1)| ≤ CQ := hQ _ (hmem2 _ hb1')
  have hKP0' : |P (-(z 0)) - P (-(z' 0))| ≤ KP * (ρ * ‖U - U'‖) := by
    refine le_trans (hPK _ (hmem2 _ hnb0) _ (hmem2 _ hnb0')) ?_
    exact mul_le_mul_of_nonneg_left hdz0 hKP0
  have hKP1' : |P (z 1) - P (z' 1)| ≤ KP * (ρ * ‖U - U'‖) := by
    refine le_trans (hPK _ (hmem2 _ hb1) _ (hmem2 _ hb1')) ?_
    exact mul_le_mul_of_nonneg_left (hdz 1) hKP0
  have hKQ0' : |Q (-(z 0)) - Q (-(z' 0))| ≤ KQ * (ρ * ‖U - U'‖) := by
    refine le_trans (hQK _ (hmem2 _ hnb0) _ (hmem2 _ hnb0')) ?_
    exact mul_le_mul_of_nonneg_left hdz0 hKQ0
  have hKQ1' : |Q (z 1) - Q (z' 1)| ≤ KQ * (ρ * ‖U - U'‖) := by
    refine le_trans (hQK _ (hmem2 _ hb1) _ (hmem2 _ hb1')) ?_
    exact mul_le_mul_of_nonneg_left (hdz 1) hKQ0
  have hM1 : 0 ≤ M + 1 := by linarith
  have hC3 : |(P (-(z 0)) * z 2 + P (z 1) * z 3) - (P (-(z' 0)) * z' 2 + P (z' 1) * z' 3)|
      ≤ 2 * (ρ * ‖U - U'‖) * (CP + KP * (M + 1)) :=
    abs_coeff_mul_sub_le (P := P) (CP := CP) (KP := KP) (M := M + 1) (Δ := ρ * ‖U - U'‖)
      hP0 hP1 hKP0' hKP1' (hdz 2) (hdz 3) hb2' hb3' hΔ hCP0 hKP0 hM1
  have hC4 : |(Q (-(z 0)) * z 2 + Q (z 1) * z 3) - (Q (-(z' 0)) * z' 2 + Q (z' 1) * z' 3)|
      ≤ 2 * (ρ * ‖U - U'‖) * (CQ + KQ * (M + 1)) :=
    abs_coeff_mul_sub_le (P := Q) (CP := CQ) (KP := KQ) (M := M + 1) (Δ := ρ * ‖U - U'‖)
      hQ0 hQ1 hKQ0' hKQ1' (hdz 2) (hdz 3) hb2' hb3' hΔ hCQ0 hKQ0 hM1
  have hsub_id : thetaShape P Q zb ρ U - thetaShape P Q zb ρ U'
      = RyaboginVolterra.mk4 (-(z 2) - -(z' 2)) (-(z 3) - -(z' 3))
          ((P (-(z 0)) * z 2 + P (z 1) * z 3) - (P (-(z' 0)) * z' 2 + P (z' 1) * z' 3))
          ((Q (-(z 0)) * z 2 + Q (z 1) * z 3) - (Q (-(z' 0)) * z' 2 + Q (z' 1) * z' 3)) := by
    simp only [thetaShape, mk4_sub, hzdef, hz'def]
  rw [hsub_id]
  have h1 : |-(z 2) - -(z' 2)| ≤ ρ * ‖U - U'‖ := by
    rw [show -(z 2) - -(z' 2) = -((z 2) - (z' 2)) by ring, abs_neg]
    exact hdz 2
  have h2 : |-(z 3) - -(z' 3)| ≤ ρ * ‖U - U'‖ := by
    rw [show -(z 3) - -(z' 3) = -((z 3) - (z' 3)) by ring, abs_neg]
    exact hdz 3
  have hnorm := norm_mk4_le (-(z 2) - -(z' 2)) (-(z 3) - -(z' 3))
    ((P (-(z 0)) * z 2 + P (z 1) * z 3) - (P (-(z' 0)) * z' 2 + P (z' 1) * z' 3))
    ((Q (-(z 0)) * z 2 + Q (z 1) * z 3) - (Q (-(z' 0)) * z' 2 + Q (z' 1) * z' 3))
  calc ‖RyaboginVolterra.mk4 (-(z 2) - -(z' 2)) (-(z 3) - -(z' 3))
        ((P (-(z 0)) * z 2 + P (z 1) * z 3) - (P (-(z' 0)) * z' 2 + P (z' 1) * z' 3))
        ((Q (-(z 0)) * z 2 + Q (z 1) * z 3) - (Q (-(z' 0)) * z' 2 + Q (z' 1) * z' 3))‖
      ≤ |-(z 2) - -(z' 2)| + |-(z 3) - -(z' 3)|
        + |(P (-(z 0)) * z 2 + P (z 1) * z 3) - (P (-(z' 0)) * z' 2 + P (z' 1) * z' 3)|
        + |(Q (-(z 0)) * z 2 + Q (z 1) * z 3) - (Q (-(z' 0)) * z' 2 + Q (z' 1) * z' 3)| := hnorm
    _ ≤ ρ * ‖U - U'‖ + ρ * ‖U - U'‖
          + 2 * (ρ * ‖U - U'‖) * (CP + KP * (M + 1))
          + 2 * (ρ * ‖U - U'‖) * (CQ + KQ * (M + 1)) := by linarith [h1, h2, hC3, hC4]
    _ = ρ * (2 + 2 * (CP + KP * (M + 1)) + 2 * (CQ + KQ * (M + 1))) * ‖U - U'‖ := by ring

/-- **The bridge**: the perturbed `Θ`-row evaluated at `baseZ σ + ρ • U` is exactly the shape
function built from the `thetaP`/`thetaQ` coefficient families. -/
lemma Theta_eq_thetaShape (n : ℕ) {h : ℝ → ℝ} (hd : Differentiable ℝ h) (ε s σ ρ : ℝ)
    (U : VS) :
    RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
      = thetaShape (fun w => thetaP n h (ε, (σ, w)) s) (fun w => thetaQ n h (ε, (σ, w)) s)
          (baseZ σ) ρ U := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
  funext i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.reduceFinMk, RyaboginVolterra.Theta, RyaboginVolterra.mk4_apply, RyaboginVolterra.mk4, Theta_apply_zero,
      Theta_apply_one, Theta_apply_two,
      Theta_apply_three, thetaShape, thetaP, thetaQ,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope, Pi.smul_apply, smul_eq_mul,
      deriv_smul_const_eq ε hd]

/-- **The Lipschitz constant of the `Θ`-row** (the last ingredient of the `L_Θ` hypothesis of the
abstract Volterra theorem). -/
lemma exists_lipschitz_Thn (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ∃ L : NNReal, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      LipschitzOnWith L (fun U : VS => ThnEps n Qe ρ h ε s σ U)
        (Metric.closedBall (0 : VS) 1) := by
  obtain ⟨CP0, hCP0⟩ := exists_bound_thetaPs n hh a
  obtain ⟨KP0, hKP0⟩ := exists_lipschitz_thetaPs_w n hh a
  obtain ⟨CQ0, hCQ0⟩ := exists_bound_thetaQs n hh a
  obtain ⟨KQ0, hKQ0⟩ := exists_lipschitz_thetaQs_w n hh a
  obtain ⟨M, hM1, hM⟩ := exists_baseZ_norm_bound (a := a)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hCP : ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ s ∈ Set.Icc a 1,
      |thetaPs n h ε σ (w, s)| ≤ max CP0 0 := fun σ hσ w hw s hs =>
    le_trans (hCP0 ε ⟨hε0, hε1⟩ σ hσ w hw s hs) (le_max_left _ _)
  have hCQ : ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ s ∈ Set.Icc a 1,
      |thetaQs n h ε σ (w, s)| ≤ max CQ0 0 := fun σ hσ w hw s hs =>
    le_trans (hCQ0 ε ⟨hε0, hε1⟩ σ hσ w hw s hs) (le_max_left _ _)
  have hKP : ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      |thetaPs n h ε σ (w, s) - thetaPs n h ε σ (w', s)| ≤ max KP0 0 * |w - w'| :=
    fun σ hσ w hw w' hw' s hs =>
      le_trans (hKP0 ε ⟨hε0, hε1⟩ σ hσ s hs w hw w' hw')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hKQ : ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2, ∀ w' ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      |thetaQs n h ε σ (w, s) - thetaQs n h ε σ (w', s)| ≤ max KQ0 0 * |w - w'| :=
    fun σ hσ w hw w' hw' s hs =>
      le_trans (hKQ0 ε ⟨hε0, hε1⟩ σ hσ s hs w hw w' hw')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  refine ⟨⟨‖(Qe.symm : VS →L[ℝ] VS)‖ *
      (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))),
      by positivity⟩, fun s hs σ hσ => ?_⟩
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hb0 : |baseZ σ 0| ≤ 1 := by
    rw [baseZ_apply_zero]
    exact abs_le.mpr (profileX_mem_Icc σ)
  have hb1 : |baseZ σ 1| ≤ 1 := by
    rw [baseZ_apply_one]
    exact abs_le.mpr (profileX_mem_Icc σ)
  have hb2 : |baseZ σ 2| ≤ M := le_trans (abs_apply_le_norm_state (baseZ σ) 2) (hM σ hσ)
  have hb3 : |baseZ σ 3| ≤ M := le_trans (abs_apply_le_norm_state (baseZ σ) 3) (hM σ hσ)
  have hshape : ∀ x ∈ Metric.closedBall (0 : VS) 1, ∀ y ∈ Metric.closedBall (0 : VS) 1,
      ‖thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
          (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
          (baseZ σ) ρ y‖ ≤ ρ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))) * ‖x - y‖ := by
    intro x hx y hy
    have h := norm_thetaShape_sub_le
      (P := fun w => thetaPs n h ε σ (w, s)) (Q := fun w => thetaQs n h ε σ (w, s))
      (zb := baseZ σ) (ρ := ρ) (CP := max CP0 0) (CQ := max CQ0 0)
      (KP := max KP0 0) (KQ := max KQ0 0) (M := M)
      hρ0 hρ1 hb0 hb1 hb2 hb3 hM0 (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      (le_max_right _ _) (fun w hw => hCP σ hσ w hw s hs) (fun w hw => hCQ σ hσ w hw s hs)
      (fun w hw w' hw' => hKP σ hσ w hw w' hw' s hs)
      (fun w hw w' hw' => hKQ σ hσ w hw w' hw' s hs) hx hy
    exact h
  have hbridge : ∀ U : VS, ThnEps n Qe ρ h ε s σ U = (1 / ρ) • Qe.symm
      (thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
        (baseZ σ) ρ U) := by
    intro U
    have h1 : ThnEps n Qe ρ h ε s σ U = (1 / ρ) • Qe.symm
        (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)) := rfl
    rw [h1, Theta_eq_thetaShape n hd ε s σ ρ U]
    have hfun1 : (fun w => thetaP n h (ε, (σ, w)) s) = fun w => thetaPs n h ε σ (w, s) := by
      funext w
      exact (thetaPs_eq n h ε σ (w, s)).symm
    have hfun2 : (fun w => thetaQ n h (ε, (σ, w)) s) = fun w => thetaQs n h ε σ (w, s) := by
      funext w
      exact (thetaQs_eq n h ε σ (w, s)).symm
    rw [hfun1, hfun2]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hΘ := hshape x hx y hy
  have hdiff : (1 / ρ) • Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x)
      - (1 / ρ) • Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)
      = (1 / ρ) • (Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)) := by
    rw [← smul_sub, ← map_sub]
  rw [dist_eq_norm, hbridge x, hbridge y, hdiff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hρ0)]
  have hQe : ‖(Qe.symm : VS →L[ℝ] VS) (thetaShape (fun w => thetaPs n h ε σ (w, s))
      (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
      - thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)‖
      ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ *
        ‖thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
          - thetaShape (fun w => thetaPs n h ε σ (w, s))
            (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y‖ :=
    (Qe.symm : VS →L[ℝ] VS).le_opNorm _
  calc (1 / ρ) * ‖(Qe.symm : VS →L[ℝ] VS) (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)‖
      ≤ (1 / ρ) * (‖(Qe.symm : VS →L[ℝ] VS)‖ * (ρ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))) * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left
          (le_trans hQe (mul_le_mul_of_nonneg_left hΘ (norm_nonneg _))) (by positivity)
    _ = (‖(Qe.symm : VS →L[ℝ] VS)‖ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1)))) * ‖x - y‖ := by
        field_simp

/-- Uniform bound for the `(a,b)`-derivative of `Gw` on a compact region with an arbitrary state
ball `Metric.closedBall 0 M'`. -/
lemma exists_bound_fderiv_Gw_ab_ball (n : ℕ) (M' : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : (ℝ × ℝ) × (ℝ × RyaboginVolterra.State),
      q.1 ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 →
      q.2.1 ∈ Set.Icc (0 : ℝ) 1 →
      q.2.2 ∈ Metric.closedBall (0 : RyaboginVolterra.State) M' →
      ‖fderiv ℝ (fun p : ℝ × ℝ => Gw n q.2.1 p.1 p.2 q.2.2) q.1‖ ≤ C := by
  have hK : IsCompact ((Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : RyaboginVolterra.State) M')) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod (isCompact_closedBall _ _))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_fderiv_Gw_ab n).continuousOn
  exact ⟨max C 1, lt_max_of_lt_right one_pos, fun q h1 h2 h3 =>
    le_trans (hC q ⟨h1, h2, h3⟩) (le_max_left _ _)⟩

/-- **Lipschitz bound for the perturbed `G`-data** on an arbitrary state ball. -/
lemma Gw_lipschitz_ab_ball (n : ℕ) (M' : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s a b : ℝ) (z : RyaboginVolterra.State),
      s ∈ Set.Icc (0 : ℝ) 1 → |a| ≤ 1 → |b| ≤ 1 →
      z ∈ Metric.closedBall (0 : RyaboginVolterra.State) M' →
      ‖Gw n s a b z - Gw n s 0 0 z‖ ≤ C * (|a| + |b|) := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_fderiv_Gw_ab_ball n M'
  refine ⟨C, hCpos, fun s a b z hs ha hb hz => ?_⟩
  have hmem : ∀ x : ℝ × ℝ, x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 →
      x.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ x.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    have h : ‖x‖ = max |x.1| |x.2| := by rw [Prod.norm_def]; rfl
    rw [h] at hx
    have h1 : |x.1| ≤ 1 := le_trans (le_max_left _ _) hx
    have h2 : |x.2| ≤ 1 := le_trans (le_max_right _ _) hx
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hsq : (a, b) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h : ‖((a, b) : ℝ × ℝ)‖ = max |a| |b| := by rw [Prod.norm_def]; rfl
    rw [h]
    exact max_le ha hb
  have hdiff : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
      DifferentiableAt ℝ (fun p : ℝ × ℝ => Gw n s p.1 p.2 z) x := by
    intro x hx
    exact (hasFDerivAt_Gw_ab n (x, (s, z))).differentiableAt
  have hCd : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1,
      ‖fderiv ℝ (fun p : ℝ × ℝ => Gw n s p.1 p.2 z) x‖ ≤ C := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hmem x hx
    exact hC (x, (s, z)) ⟨hx1, hx2⟩ hs hz
  have hmain := dist_image_sub_le_of_norm_fderiv_le hdiff hCd
    (convex_closedBall (0 : ℝ × ℝ) 1) hsq
    (show (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 from by simp)
  rw [dist_eq_norm] at hmain
  have hdist : dist (a, b) (0 : ℝ × ℝ) ≤ |a| + |b| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    exact max_le (le_add_of_nonneg_right (abs_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a))
  calc ‖Gw n s a b z - Gw n s 0 0 z‖
      = dist (Gw n s a b z) (Gw n s 0 0 z) := by rw [dist_eq_norm]
    _ ≤ C * dist (a, b) (0 : ℝ × ℝ) := hmain
    _ ≤ C * (|a| + |b|) := mul_le_mul_of_nonneg_left hdist hCpos.le

/-- **The `G`-row closeness**, with a norm bound on `baseZ` on `[a,1]` instead of closeness to
`baseZ 1` (so it applies on intervals reaching down to `s = 5/8`). -/
lemma Gn_close_TG_ball {n : ℕ} {Qe : VS ≃L[ℝ] VS} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {h : ℝ → ℝ} (hh : Differentiable ℝ h) {a M M' : ℝ} (hM : 0 < M) (hM' : 0 ≤ M')
    (hMb : ∀ s ∈ Set.Icc a 1, |h s| ≤ M) (hMd : ∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M)
    (hcl : ∀ s ∈ Set.Icc a 1, ‖baseZ s‖ ≤ M') (ha : 0 ≤ a)
    {η : ℝ} (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ (∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      ∀ U ∈ Metric.closedBall (0 : VS) 1,
      dist (Gn n Qe ρ (ε • h) s U) (TG n Qe ρ s U) < η) ∧
      (∀ ε ∈ Set.Ioo (0 : ℝ) εp, ε * M ≤ 1 / 2) := by
  obtain ⟨C, hCpos, hC⟩ := Gw_lipschitz_ab_ball n (M' + 1 / 2)
  set K : ℝ := ‖(Qe.symm : VS →L[ℝ] VS)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨min (1 / (2 * M)) (η * ρ / (2 * C * M * K + 1)), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · intro ε hε s hs U hU
    have hεpos : 0 < ε := hε.1
    have hε1 : ε < 1 / (2 * M) := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε2 : ε < η * ρ / (2 * C * M * K + 1) := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hU1 : ‖U‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hU
    have hz : baseZ s + ρ • U ∈ Metric.closedBall (0 : RyaboginVolterra.State) (M' + 1 / 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h2 : ‖ρ • U‖ ≤ 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0]
        calc ρ * ‖U‖ ≤ (1 / 2) * 1 := mul_le_mul hρ1 hU1 (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      calc ‖baseZ s + ρ • U‖ ≤ ‖baseZ s‖ + ‖ρ • U‖ := norm_add_le _ _
        _ ≤ M' + 1 / 2 := by linarith [hcl s hs]
    have hder : deriv (ε • h) s = ε * deriv h s := by
      have h' := (hh s).hasDerivAt.const_mul ε
      have hfun : (fun u : ℝ => ε * h u) = (ε • h) := rfl
      rw [← hfun]
      exact h'.deriv
    have hb : |ε * h s| ≤ 1 := by
      rw [abs_mul, abs_of_pos hεpos]
      have h1 : ε * |h s| ≤ ε * M := mul_le_mul_of_nonneg_left (hMb s hs) hεpos.le
      have h2 : ε * M < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hε1 hM
      have h3 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
      linarith
    have hb' : |ε * deriv h s| ≤ 1 := by
      rw [abs_mul, abs_of_pos hεpos]
      have h1 : ε * |deriv h s| ≤ ε * M := mul_le_mul_of_nonneg_left (hMd s hs) hεpos.le
      have h2 : ε * M < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hε1 hM
      have h3 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
      linarith
    have hGn : Gn n Qe ρ (ε • h) s U
        = (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U)) := by
      simp only [Gn, GnW, Pi.smul_apply, smul_eq_mul, hder]
    have hTG : TG n Qe ρ s U = (1 / ρ) • Qe.symm (Gw n s 0 0 (baseZ s + ρ • U)) := by
      simp only [TG, baseG, G_eq_Gw, Pi.zero_apply, deriv_const]
    rw [dist_eq_norm, hGn, hTG]
    have hsub : (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U)) -
          (1 / ρ) • Qe.symm (Gw n s 0 0 (baseZ s + ρ • U))
        = (1 / ρ) • Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
            Gw n s 0 0 (baseZ s + ρ • U)) := by
      rw [map_sub, smul_sub]
    rw [hsub, norm_smul]
    have h1 : ‖(1 / ρ : ℝ)‖ = 1 / ρ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h1]
    have h2 : ‖Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U))‖
        ≤ K * ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
            Gw n s 0 0 (baseZ s + ρ • U)‖ := by
      have := (Qe.symm : VS →L[ℝ] VS).le_opNorm
        (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
            Gw n s 0 0 (baseZ s + ρ • U))
      simpa [hK] using this
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha hs.1, hs.2⟩
    have h3 : ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
          Gw n s 0 0 (baseZ s + ρ • U)‖ ≤ C * (|ε * h s| + |ε * deriv h s|) :=
      hC s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) hs01 hb hb' hz
    have h4 : |ε * h s| + |ε * deriv h s| ≤ 2 * (ε * M) := by
      have hb1 : |h s| ≤ M := hMb s hs
      have hd1 : |deriv h s| ≤ M := hMd s hs
      have e1 : |ε * h s| = ε * |h s| := by rw [abs_mul, abs_of_pos hεpos]
      have e2 : |ε * deriv h s| = ε * |deriv h s| := by rw [abs_mul, abs_of_pos hεpos]
      rw [e1, e2]
      have p1 : ε * |h s| ≤ ε * M := mul_le_mul_of_nonneg_left hb1 hεpos.le
      have p2 : ε * |deriv h s| ≤ ε * M := mul_le_mul_of_nonneg_left hd1 hεpos.le
      linarith
    have hεbound : ε * (2 * C * M * K) < η * ρ := by
      have hpos : 0 < 2 * C * M * K + 1 := by positivity
      rw [lt_div_iff₀ hpos] at hε2
      nlinarith [hε2, hK0, hCpos.le, hM.le, mul_nonneg hCpos.le hM.le, hεpos]
    calc (1 / ρ) * ‖Qe.symm (Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
            Gw n s 0 0 (baseZ s + ρ • U))‖
        ≤ (1 / ρ) * (K * ‖Gw n s (ε * h s) (ε * deriv h s) (baseZ s + ρ • U) -
            Gw n s 0 0 (baseZ s + ρ • U)‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 / ρ) * (K * (C * (|ε * h s| + |ε * deriv h s|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK0) (by positivity)
      _ ≤ (1 / ρ) * (K * (C * (2 * (ε * M)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h4 hCpos.le) hK0) (by positivity)
      _ = ε * (2 * C * M * K) / ρ := by field_simp
      _ < η * ρ / ρ := div_lt_div_of_pos_right hεbound hρ0
      _ = η := by field_simp
  · intro ε hε
    have hε1 : ε < 1 / (2 * M) := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have h4 : ε * M < (1 / (2 * M)) * M := mul_lt_mul_of_pos_right hε1 hM
    have h5 : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    linarith

/-- **Θ-row closeness on an arbitrary ball.**  For any `R`, the perturbed `Θ`-row converges to the
base row uniformly on `[a,1]² × closedBall 0 R` as `ε → 0`. -/
lemma Theta_close_base_ball {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a R η : ℝ}
    (hη : 0 < η) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      ∀ Z ∈ Metric.closedBall (0 : VS) R,
      ‖RyaboginVolterra.Theta n (ε • h) s σ Z - baseΘ n s σ Z‖ < η := by
  have hcont : Continuous (fun q : ℝ × ((ℝ × ℝ) × VS) =>
      RyaboginVolterra.Theta n (q.1 • h) q.2.1.1 q.2.1.2 q.2.2 - baseΘ n q.2.1.1 q.2.1.2 q.2.2) := by
    have hmapCont : Continuous (fun q : ℝ × ((ℝ × ℝ) × VS) =>
        Prod.mk (Prod.mk q.1 (Prod.mk q.2.1.1 q.2.2)) q.2.1.2) := by fun_prop
    have h1 : Continuous (fun q : (ℝ × (ℝ × VS)) × ℝ =>
        RyaboginVolterra.Theta n (fun u : ℝ => q.1.1 * h u) q.1.2.1 q.2 q.1.2.2) :=
      (contDiff_Theta_family n (H := fun ε u => ε * h u) (by fun_prop)).continuous
    have h2 : Continuous (fun q : (ℝ × (ℝ × VS)) × ℝ =>
        RyaboginVolterra.Theta n (fun _ => (0 : ℝ)) q.1.2.1 q.2 q.1.2.2) :=
      (contDiff_Theta_family n (H := fun _ _ => (0 : ℝ)) (by fun_prop)).continuous
    refine ((h1.sub h2).comp hmapCont).congr (fun q => ?_)
    show RyaboginVolterra.Theta n (fun u : ℝ => q.1 * h u) q.2.1.1 q.2.1.2 q.2.2
        - RyaboginVolterra.Theta n (fun _ => (0 : ℝ)) q.2.1.1 q.2.1.2 q.2.2
      = RyaboginVolterra.Theta n (q.1 • h) q.2.1.1 q.2.1.2 q.2.2 - baseΘ n q.2.1.1 q.2.1.2 q.2.2
    have hfun : (fun u : ℝ => q.1 * h u) = (q.1 • h) := by
      funext u
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfun, baseΘ]
  have hK : IsCompact ((Set.Icc a 1 ×ˢ Set.Icc a 1) ×ˢ Metric.closedBall (0 : VS) R) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  obtain ⟨εp, hεp, hε⟩ := exists_norm_small_of_continuous_zero
    (K := (Set.Icc a 1 ×ˢ Set.Icc a 1) ×ˢ Metric.closedBall (0 : VS) R) hK
    (F := fun ε p => RyaboginVolterra.Theta n (ε • h) p.1.1 p.1.2 p.2
      - baseΘ n p.1.1 p.1.2 p.2) hcont hη
  refine ⟨εp, hεp, fun ε hε' s hs σ hσ Z hZ => ?_⟩
  have hres := hε ε hε' ((s, σ), Z) ⟨⟨hs, hσ⟩, hZ⟩
  have hz0 : ((0 : ℝ) • h) = fun _ : ℝ => (0 : ℝ) := by funext u; simp
  have h0 : RyaboginVolterra.Theta n ((0 : ℝ) • h) s σ Z - baseΘ n s σ Z = 0 := by
    rw [hz0, baseΘ, sub_self]
  rw [h0, sub_zero] at hres
  exact hres

/-- **The scaled `Θ`-row closeness** — the `Θ`-hypothesis of the abstract Volterra theorem. -/
lemma Thn_close_TΘ (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a : ℝ} {e : ℝ} (he : 0 < e) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      ∀ U ∈ Metric.closedBall (0 : VS) 1,
      dist (ThnEps n Qe ρ h ε s σ U) (TΘ n Qe ρ s σ U) < e := by
  obtain ⟨M, hM1, hM⟩ := exists_baseZ_norm_bound (a := a)
  set K : ℝ := ‖(Qe.symm : VS →L[ℝ] VS)‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  obtain ⟨εp, hεp, hε⟩ := Theta_close_base_ball (n := n) hh (a := a) (R := M + 1 / 2)
    (η := ρ * e / (2 * (K + 1))) (by positivity)
  refine ⟨εp, hεp, fun ε hε' s hs σ hσ U hU => ?_⟩
  have hU1 : ‖U‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hU
  have hZ : baseZ σ + ρ • U ∈ Metric.closedBall (0 : VS) (M + 1 / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖ρ • U‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ0]
      calc ρ * ‖U‖ ≤ (1 / 2) * 1 := mul_le_mul hρ1 hU1 (norm_nonneg _) (by norm_num)
        _ = 1 / 2 := by ring
    calc ‖baseZ σ + ρ • U‖ ≤ ‖baseZ σ‖ + ‖ρ • U‖ := norm_add_le _ _
      _ ≤ M + 1 / 2 := by linarith [hM σ hσ]
  have hclose := hε ε hε' s hs σ hσ (baseZ σ + ρ • U) hZ
  have hA : ThnEps n Qe ρ h ε s σ U
      = (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)) := rfl
  have hB : TΘ n Qe ρ s σ U
      = (1 / ρ) • Qe.symm (baseΘ n s σ (baseZ σ + ρ • U)) := rfl
  rw [dist_eq_norm, hA, hB]
  have hsub : (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U))
        - (1 / ρ) • Qe.symm (baseΘ n s σ (baseZ σ + ρ • U))
      = (1 / ρ) • Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
          - baseΘ n s σ (baseZ σ + ρ • U)) := by
    rw [map_sub, smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / ρ)]
  have hQe : ‖Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
        - baseΘ n s σ (baseZ σ + ρ • U))‖
      ≤ K * ‖RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
          - baseΘ n s σ (baseZ σ + ρ • U)‖ := by
    simpa [hKdef] using (Qe.symm : VS →L[ℝ] VS).le_opNorm
      (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
        - baseΘ n s σ (baseZ σ + ρ • U))
  calc (1 / ρ) * ‖Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
          - baseΘ n s σ (baseZ σ + ρ • U))‖
      ≤ (1 / ρ) * (K * ‖RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
          - baseΘ n s σ (baseZ σ + ρ • U)‖) := mul_le_mul_of_nonneg_left hQe (by positivity)
    _ ≤ (1 / ρ) * (K * (ρ * e / (2 * (K + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hclose.le hK0) (by positivity)
    _ = K * e / (2 * (K + 1)) := by field_simp
    _ < e := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
        nlinarith [hK0, he]

/-- **The scaled `Ξ`-row closeness** — the `Ξ`-hypothesis of the abstract Volterra theorem. -/
lemma Xi_close_TΞ (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 ≤ a) {e : ℝ} (he : 0 < e) :
    ∃ εp : ℝ, 0 < εp ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) εp, ∀ s ∈ Set.Icc a 1,
      dist (Xin n Qe ρ (ε • h) s) (TΞ n Qe ρ s) < e := by
  set K : ℝ := ‖(Qe.symm : VS →L[ℝ] VS)‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  obtain ⟨εp, hεp, hε⟩ := Xi_close_base (n := n) (h := h) hh ha
    (η := ρ * e / (2 * (K + 1))) (by positivity)
  refine ⟨εp, hεp, fun ε hε' s hs => ?_⟩
  have hclose : ‖RyaboginVolterra.Xi n (ε • h) s - baseΞ n s‖ < ρ * e / (2 * (K + 1)) :=
    hε ε hε' s hs
  have hA : Xin n Qe ρ (ε • h) s = (1 / ρ) • Qe.symm (RyaboginVolterra.Xi n (ε • h) s) := rfl
  have hB : TΞ n Qe ρ s = (1 / ρ) • Qe.symm (baseΞ n s) := rfl
  rw [dist_eq_norm, hA, hB]
  have hsub : (1 / ρ) • Qe.symm (RyaboginVolterra.Xi n (ε • h) s) - (1 / ρ) • Qe.symm (baseΞ n s)
      = (1 / ρ) • Qe.symm (RyaboginVolterra.Xi n (ε • h) s - baseΞ n s) := by
    rw [map_sub, smul_sub]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / ρ)]
  have hQe : ‖Qe.symm (RyaboginVolterra.Xi n (ε • h) s - baseΞ n s)‖
      ≤ K * ‖RyaboginVolterra.Xi n (ε • h) s - baseΞ n s‖ := by
    simpa [hKdef] using (Qe.symm : VS →L[ℝ] VS).le_opNorm
      (RyaboginVolterra.Xi n (ε • h) s - baseΞ n s)
  calc (1 / ρ) * ‖Qe.symm (RyaboginVolterra.Xi n (ε • h) s - baseΞ n s)‖
      ≤ (1 / ρ) * (K * ‖RyaboginVolterra.Xi n (ε • h) s - baseΞ n s‖) :=
        mul_le_mul_of_nonneg_left hQe (by positivity)
    _ ≤ (1 / ρ) * (K * (ρ * e / (2 * (K + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hclose.le hK0) (by positivity)
    _ = K * e / (2 * (K + 1)) := by field_simp
    _ < e := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
        nlinarith [hK0, he]

/-- The hypothesis of `Tbase_identity` for the canonical reference
`Qe := jacEquiv n (by norm_num : (0:ℝ) < 1)` (the Jacobian of `baseG` at `(1, baseZ 1)`). -/
lemma hQe_jacEquiv (n : ℕ) (hn : 2 ≤ n) :
    (jacEquiv n (by norm_num : (0 : ℝ) < 1)).toContinuousLinearMap
      = fderiv ℝ (fun z : VS => baseG n 1 z) (baseZ 1) := by
  rw [← jacLin_eq_fderiv hn 1]
  refine ContinuousLinearMap.ext fun v => ?_
  show (jacEquiv n (by norm_num : (0 : ℝ) < 1)) v = jacLin n 1 v
  exact jacEquiv_apply n (by norm_num : (0 : ℝ) < 1) v

/-- **`hbase` for the canonical reference**: the scaled base solution is `0` on `[a,1]`. -/
lemma Tbase_identity_jacEquiv (n : ℕ) (hn : 2 ≤ n) {ρ : ℝ} (hρ : ρ ≠ 0) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ s ∈ Set.Icc a 1,
      TG n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ s 0
        = (∫ σ in s..1, TΘ n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ s σ 0)
          + TΞ n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ s :=
  Tbase_identity n hn _ (hQe_jacEquiv n hn) hρ ha ha1

end Commons.Geometry.Ulam
end

-- ===== FILE _weighted.lean =====

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace Commons.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Extension of a bounded continuous function on `[a,b]` to all of `ℝ`. -/
def bcfExtG {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E) : ℝ → E :=
  Set.IccExtend hab (fun s : Set.Icc a b => Z s)

@[fun_prop]
lemma bcfExtG_continuous {a b : ℝ} (hab : a ≤ b)
    (Z : BoundedContinuousFunction (Set.Icc a b) E) : Continuous (bcfExtG hab Z) := by
  dsimp [bcfExtG]
  exact Z.continuous.Icc_extend'

lemma bcfExtG_of_mem {a b : ℝ} (hab : a ≤ b) (Z : BoundedContinuousFunction (Set.Icc a b) E)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : bcfExtG hab Z x = Z ⟨x, hx⟩ := by
  dsimp [bcfExtG]
  exact Set.IccExtend_of_mem (h := hab) (f := fun s : Set.Icc a b => Z s) hx

theorem volterra_perturbation_exists_weighted
    {a b : ℝ} (hab : a < b)
    {G0 : ℝ → E → E} {Θ0 : ℝ → ℝ → E → E} {Ξ0 : ℝ → E}
    {Q : ℝ → E ≃L[ℝ] E} {K_G L_Θ : NNReal} (hKlt : (K_G : ℝ) < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hQbdd : ∃ C : ℝ, ∀ s ∈ Set.Icc a b, ‖((Q s).symm : E →L[ℝ] E)‖ ≤ C)
    (hQcont : Continuous (fun p : ℝ × E => (Q p.1).symm p.2))
    (hG0_cont : Continuous (fun p : ℝ × E => G0 p.1 p.2))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hΞ0_cont : Continuous Ξ0)
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (0 : E) = (∫ σ in s..b, Θ0 s σ (0 : E)) + Ξ0 s) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (G : ℝ → E → E) (Θ : ℝ → ℝ → E → E) (Ξ : ℝ → E),
        Continuous (fun p : ℝ × E => G p.1 p.2) →
        Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2) →
        Continuous Ξ →
        (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (0 : E) 1, dist (G s z) (G0 s z) < ε) →
        (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (0 : E) 1,
          dist (Θ s σ z) (Θ0 s σ z) < ε) →
        (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
        (∀ s ∈ Set.Icc a b, LipschitzOnWith K_G
          (fun z : E => z - (Q s).symm (G s z)) (Metric.closedBall (0 : E) 1)) →
        (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
          LipschitzOnWith L_Θ (fun z : E => Θ s σ z) (Metric.closedBall (0 : E) 1)) →
        ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧
          (∀ s ∈ Set.Icc a b, dist (Z s) 0 ≤ r) ∧
          (∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s) := by
  classical
  obtain ⟨Craw, hCraw⟩ := hQbdd
  set C : ℝ := max Craw 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCbd : ∀ s ∈ Set.Icc a b, ‖((Q s).symm : E →L[ℝ] E)‖ ≤ C :=
    fun s hs => le_trans (hCraw s hs) (le_max_left _ _)
  have hLnn : 0 ≤ (L_Θ : ℝ) := L_Θ.2
  have h1mk : 0 < 1 - (K_G : ℝ) := by have := hKlt; linarith
  set lam : ℝ := 2 * C * (L_Θ : ℝ) / (1 - (K_G : ℝ)) + 1 with hlam
  have hlam_pos : 0 < lam := by
    have h0 : 0 ≤ 2 * C * (L_Θ : ℝ) / (1 - (K_G : ℝ)) := div_nonneg (by positivity) h1mk.le
    rw [hlam]; linarith
  have hpit : C * (L_Θ : ℝ) / lam < 1 - (K_G : ℝ) := by
    rw [div_lt_iff₀ hlam_pos]
    have hexp : (1 - (K_G : ℝ)) * lam = 2 * C * (L_Θ : ℝ) + (1 - (K_G : ℝ)) := by
      rw [hlam]
      field_simp
    rw [hexp]
    have h2 : 0 ≤ 2 * C * (L_Θ : ℝ) := by positivity
    linarith
  set k : ℝ := (K_G : ℝ) + C * (L_Θ : ℝ) / lam with hk
  have hk_lt : k < 1 := by rw [hk]; linarith
  have hk_nonneg : 0 ≤ k := by rw [hk]; positivity
  set w : ℝ → ℝ := fun s => Real.exp (lam * (s - a)) with hw
  have hw_cont : Continuous w := by rw [hw]; fun_prop
  have hw_pos : ∀ s, 0 < w s := fun s => Real.exp_pos _
  have hw_ge_one : ∀ s, a ≤ s → 1 ≤ w s := by
    intro s hs
    rw [hw, ← Real.exp_zero, Real.exp_le_exp]
    nlinarith
  have hw_mono : Monotone w := by
    intro s t hst
    rw [hw, Real.exp_le_exp]
    nlinarith
  have hw_ratio : ∀ s σ : ℝ, w s / w σ = Real.exp (lam * (s - σ)) := by
    intro s σ
    show Real.exp (lam * (s - a)) / Real.exp (lam * (σ - a)) = Real.exp (lam * (s - σ))
    rw [← Real.exp_sub]
    congr 1
    ring
  have hint : ∀ s ∈ Set.Icc a b, (∫ σ in s..b, w s / w σ) ≤ 1 / lam := by
    intro s hs
    have hval : (∫ σ in s..b, w s / w σ) = (1 - Real.exp (lam * (s - b))) / lam := by
      rw [intervalIntegral.integral_congr (fun σ _ => hw_ratio s σ)]
      have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => - Real.exp (lam * (s - t)) / lam)
          (Real.exp (lam * (s - x))) x := by
        intro x
        have h1 : HasDerivAt (fun t : ℝ => lam * (s - t)) (-lam) x := by
          have := (hasDerivAt_const x s).sub (hasDerivAt_id x)
          simpa using (this.const_mul lam)
        have h2 : HasDerivAt (fun t : ℝ => Real.exp (lam * (s - t)))
            (Real.exp (lam * (s - x)) * (-lam)) x := by
          simpa only [Function.comp_def] using
            (Real.hasDerivAt_exp (lam * (s - x))).comp x h1
        have h4 : HasDerivAt (fun t : ℝ => - Real.exp (lam * (s - t)) / lam)
            (-(Real.exp (lam * (s - x)) * (-lam)) / lam) x := h2.neg.div_const lam
        have heq : -(Real.exp (lam * (s - x)) * (-lam)) / lam
            = Real.exp (lam * (s - x)) := by
          field_simp
        rwa [heq] at h4
      have hcont : Continuous (fun σ : ℝ => Real.exp (lam * (s - σ))) := by fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := b)
        (fun x _ => hderiv x) (hcont.intervalIntegrable s b)]
      rw [sub_self, mul_zero, Real.exp_zero]
      field_simp
      ring
    rw [hval]
    have hge : 0 ≤ Real.exp (lam * (s - b)) := Real.exp_nonneg _
    have hle : 1 - Real.exp (lam * (s - b)) ≤ 1 := by linarith
    exact div_le_div_of_nonneg_right hle hlam_pos.le
  set eps : ℝ := (1 - k) * r / (2 * C * (2 + (b - a)) * w b) with heps
  have heps_pos : 0 < eps := by
    have h1 : 0 < (1 - k) * r := mul_pos (by linarith) hr0
    have h2 : 0 < 2 * C * (2 + (b - a)) * w b := by
      have : 0 < 2 + (b - a) := by linarith
      positivity
    rw [heps]; exact div_pos h1 h2
  have heps_val : C * (2 + (b - a)) * w b * eps = (1 - k) * r / 2 := by
    rw [heps]
    field_simp [ne_of_gt hCpos, ne_of_gt (show (0:ℝ) < 2 + (b - a) by linarith),
      ne_of_gt (hw_pos b)]
  refine ⟨eps, heps_pos, ?_⟩
  intro G Θ Ξ hG_cont hΘ_cont hΞ_cont hG_close hΘ_close hΞ_close hG_lip hΘ_lip
  -- ### helper facts
  have hw_inv_cont : Continuous (fun σ : ℝ => (w σ)⁻¹) :=
    hw_cont.inv₀ (fun σ => (hw_pos σ).ne')
  have hw_inv_le_one : ∀ σ : ℝ, a ≤ σ → (w σ)⁻¹ ≤ 1 := by
    intro σ hσ; rw [inv_le_one₀ (hw_pos σ)]; exact hw_ge_one σ hσ
  have hw_pos' : ∀ σ : ℝ, 0 < w σ := hw_pos
  let dev : BoundedContinuousFunction (Set.Icc a b) E → ℝ → E :=
    fun Z σ => (w σ)⁻¹ • bcfExtG hab.le Z σ
  have dev_cont : ∀ Z : BoundedContinuousFunction (Set.Icc a b) E, Continuous (dev Z) := fun Z => by
    show Continuous (fun σ : ℝ => (w σ)⁻¹ • bcfExtG hab.le Z σ)
    exact hw_inv_cont.smul (bcfExtG_continuous hab.le Z)
  have dev_cont2 : ∀ Z : BoundedContinuousFunction (Set.Icc a b) E,
      Continuous (fun p : ℝ × ℝ => (w p.2)⁻¹ • bcfExtG hab.le Z p.2) := fun Z =>
    (hw_inv_cont.comp continuous_snd).smul ((bcfExtG_continuous hab.le Z).comp continuous_snd)
  have dev_smul : ∀ (Z : BoundedContinuousFunction (Set.Icc a b) E) (σ : ℝ),
      w σ • dev Z σ = bcfExtG hab.le Z σ := by
    intro Z σ
    dsimp only [dev]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hw_pos σ)), one_smul]
  have hdist_ext : ∀ (Z1 Z2 : BoundedContinuousFunction (Set.Icc a b) E) {σ : ℝ}
      (hσ : σ ∈ Set.Icc a b),
      dist (bcfExtG hab.le Z1 σ) (bcfExtG hab.le Z2 σ)
        = dist (Z1 ⟨σ, hσ⟩) (Z2 ⟨σ, hσ⟩) := by
    intro Z1 Z2 σ hσ
    rw [bcfExtG_of_mem hab.le Z1 hσ, bcfExtG_of_mem hab.le Z2 hσ]
  have dev_dist : ∀ (Z1 Z2 : BoundedContinuousFunction (Set.Icc a b) E) (σ : ℝ),
      dist (dev Z1 σ) (dev Z2 σ)
        = (w σ)⁻¹ * dist (bcfExtG hab.le Z1 σ) (bcfExtG hab.le Z2 σ) := by
    intro Z1 Z2 σ
    dsimp only [dev]
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hw_pos σ))]
  have dev_norm : ∀ (Z : BoundedContinuousFunction (Set.Icc a b) E) {σ : ℝ}
      (hσ : σ ∈ Set.Icc a b), ‖dev Z σ‖ ≤ dist Z 0 := by
    intro Z σ hσ
    have h1 : ‖bcfExtG hab.le Z σ‖ ≤ dist Z 0 := by
      rw [bcfExtG_of_mem hab.le Z hσ]
      simpa using BoundedContinuousFunction.dist_coe_le_dist
        (f := Z) (g := (0 : BoundedContinuousFunction (Set.Icc a b) E)) ⟨σ, hσ⟩
    dsimp only [dev]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hw_pos σ))]
    calc (w σ)⁻¹ * ‖bcfExtG hab.le Z σ‖ ≤ 1 * dist Z 0 :=
          mul_le_mul (hw_inv_le_one σ hσ.1) h1 (norm_nonneg _) zero_le_one
      _ = dist Z 0 := one_mul _
  have hdev_zero : ∀ σ : ℝ, dev (0 : BoundedContinuousFunction (Set.Icc a b) E) σ = 0 := by
    intro σ
    have h0 : bcfExtG hab.le (0 : BoundedContinuousFunction (Set.Icc a b) E) σ = 0 := by
      simp [bcfExtG, Set.IccExtend]
    show (w σ)⁻¹ • bcfExtG hab.le (0 : BoundedContinuousFunction (Set.Icc a b) E) σ = 0
    rw [h0, smul_zero]
  let Op : BoundedContinuousFunction (Set.Icc a b) E →
      BoundedContinuousFunction (Set.Icc a b) E :=
    fun Z => BoundedContinuousFunction.mkOfCompact
      { toFun := fun s : Set.Icc a b =>
          w (s:ℝ) • (dev Z (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z σ)) - Ξ (s:ℝ)))
        continuous_toFun := by
          have hU : Continuous (fun s : Set.Icc a b => dev Z (s : ℝ)) :=
            (dev_cont Z).comp continuous_subtype_val
          have hI : Continuous (fun s : ℝ => ∫ σ in s..b, Θ s σ (dev Z σ)) := by
            have hf : Continuous (fun p : ℝ × ℝ => Θ p.1 p.2 (dev Z p.2)) :=
              hΘ_cont.comp (continuous_fst.prodMk (continuous_snd.prodMk (dev_cont2 Z)))
            have h1 : Continuous (fun s : ℝ => ∫ σ in a..s, Θ s σ (dev Z σ)) :=
              intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
                (f := fun s σ => Θ s σ (dev Z σ)) (s := fun x : ℝ => x) hf continuous_id
            have h2 : Continuous (fun s : ℝ => ∫ σ in a..b, Θ s σ (dev Z σ)) :=
              intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
                (f := fun s σ => Θ s σ (dev Z σ)) hf a b
            have hcontσ : ∀ u : ℝ, Continuous (fun σ : ℝ => Θ u σ (dev Z σ)) :=
              fun u => hΘ_cont.comp
                (((continuous_const : Continuous fun _ : ℝ => u)).prodMk
                  (continuous_id.prodMk (by
                    show Continuous (fun σ : ℝ => (w σ)⁻¹ • bcfExtG hab.le Z σ)
                    exact dev_cont Z)))
            have heq : (fun s : ℝ => ∫ σ in s..b, Θ s σ (dev Z σ)) =
                fun s : ℝ => (∫ σ in a..b, Θ s σ (dev Z σ))
                  - (∫ σ in a..s, Θ s σ (dev Z σ)) := by
              funext s
              have hi1 : IntervalIntegrable (fun σ : ℝ => Θ s σ (dev Z σ)) volume a s :=
                (hcontσ s).intervalIntegrable a s
              have hi2 : IntervalIntegrable (fun σ : ℝ => Θ s σ (dev Z σ)) volume s b :=
                (hcontσ s).intervalIntegrable s b
              have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
              rw [eq_sub_iff_add_eq, add_comm]
              exact hsum
            rw [heq]
            exact h2.sub h1
          have hX : Continuous (fun s : ℝ => G s (dev Z s)
              - (∫ σ in s..b, Θ s σ (dev Z σ)) - Ξ s) :=
            ((hG_cont.comp (continuous_id.prodMk (dev_cont Z))).sub hI).sub hΞ_cont
          have hY2 : Continuous (fun s : ℝ => (Q s).symm (G s (dev Z s)
              - (∫ σ in s..b, Θ s σ (dev Z σ)) - Ξ s)) :=
            hQcont.comp (continuous_id.prodMk hX)
          exact ((hw_cont.comp continuous_subtype_val).smul
            (hU.sub (hY2.comp continuous_subtype_val))) }
  have Op_apply : ∀ (Z : BoundedContinuousFunction (Set.Icc a b) E) (s : Set.Icc a b),
      (Op Z) s = w (s:ℝ) • (dev Z (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z σ)) - Ξ (s:ℝ))) := by
    intro Z s
    dsimp only [Op]
    exact BoundedContinuousFunction.mkOfCompact_apply _ s
  have hstep : ∀ (Z1 Z2 : BoundedContinuousFunction (Set.Icc a b) E) (s : Set.Icc a b),
      dist Z1 0 ≤ r → dist Z2 0 ≤ r → dist ((Op Z1) s) ((Op Z2) s) ≤ k * dist Z1 Z2 := by
    intro Z1 Z2 s hZ1 hZ2
    have hs : (s : ℝ) ∈ Set.Icc a b := s.2
    have hsub : ∀ σ ∈ Set.Icc (s:ℝ) b, σ ∈ Set.Icc a b :=
      fun σ hσ => ⟨le_trans hs.1 hσ.1, hσ.2⟩
    have hmem : ∀ (Z : BoundedContinuousFunction (Set.Icc a b) E), dist Z 0 ≤ r →
        ∀ σ ∈ Set.Icc (s:ℝ) b, dev Z σ ∈ Metric.closedBall (0 : E) 1 := by
      intro Z hZ σ hσ
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (dev_norm Z (hsub σ hσ)) (le_trans hZ (le_of_lt hr1))
    have hdd : ∀ σ ∈ Set.Icc (s:ℝ) b, dist (dev Z1 σ) (dev Z2 σ) ≤ (w σ)⁻¹ * dist Z1 Z2 := by
      intro σ hσ
      rw [dev_dist Z1 Z2 σ, hdist_ext Z1 Z2 (hsub σ hσ)]
      exact mul_le_mul_of_nonneg_left
        (BoundedContinuousFunction.dist_coe_le_dist (f := Z1) (g := Z2) ⟨σ, hsub σ hσ⟩)
        (le_of_lt (inv_pos.mpr (hw_pos σ)))
    rw [Op_apply Z1 s, Op_apply Z2 s, dist_eq_norm]
    set A1 : E := dev Z1 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z1 (s:ℝ))) with hA1
    set A2 : E := dev Z2 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z2 (s:ℝ))) with hA2
    set I1 : E := ∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z1 σ) with hI1
    set I2 : E := ∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z2 σ) with hI2
    have hBB : (dev Z1 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z1 (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z1 σ)) - Ξ (s:ℝ)))
        - (dev Z2 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z2 (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z2 σ)) - Ξ (s:ℝ)))
        = (A1 - A2) + (Q (s:ℝ)).symm (I1 - I2) := by
      rw [hA1, hA2, hI1, hI2]
      simp only [map_sub]
      abel
    have hsplit : w (s:ℝ) • (dev Z1 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z1 (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z1 σ)) - Ξ (s:ℝ)))
        - w (s:ℝ) • (dev Z2 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z2 (s:ℝ))
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev Z2 σ)) - Ξ (s:ℝ)))
        = w (s:ℝ) • ((A1 - A2) + (Q (s:ℝ)).symm (I1 - I2)) := by
      rw [← smul_sub, hBB]
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (hw_pos (s:ℝ))]
    have h1 : w (s:ℝ) * ‖A1 - A2‖ ≤ (K_G:ℝ) * dist Z1 Z2 := by
      rw [hA1, hA2]
      have hd : ‖(dev Z1 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z1 (s:ℝ))))
            - (dev Z2 (s:ℝ) - (Q (s:ℝ)).symm (G (s:ℝ) (dev Z2 (s:ℝ))))‖
          ≤ (K_G:ℝ) * dist (dev Z1 (s:ℝ)) (dev Z2 (s:ℝ)) := by
        rw [← dist_eq_norm]
        exact (hG_lip (s:ℝ) hs).dist_le_mul _
          (hmem Z1 hZ1 (s:ℝ) ⟨le_rfl, hs.2⟩) _ (hmem Z2 hZ2 (s:ℝ) ⟨le_rfl, hs.2⟩)
      have hwd : w (s:ℝ) * dist (dev Z1 (s:ℝ)) (dev Z2 (s:ℝ)) ≤ dist Z1 Z2 := by
        rw [dev_dist Z1 Z2 (s:ℝ), hdist_ext Z1 Z2 hs, ← mul_assoc,
          mul_inv_cancel₀ (ne_of_gt (hw_pos (s:ℝ))), one_mul]
        exact BoundedContinuousFunction.dist_coe_le_dist (f := Z1) (g := Z2) ⟨(s:ℝ), hs⟩
      calc w (s:ℝ) * ‖_‖ ≤ w (s:ℝ) * ((K_G:ℝ) * dist (dev Z1 (s:ℝ)) (dev Z2 (s:ℝ))) :=
            mul_le_mul_of_nonneg_left hd (le_of_lt (hw_pos (s:ℝ)))
        _ = (K_G:ℝ) * (w (s:ℝ) * dist (dev Z1 (s:ℝ)) (dev Z2 (s:ℝ))) := by ring
        _ ≤ (K_G:ℝ) * dist Z1 Z2 := mul_le_mul_of_nonneg_left hwd K_G.2
    have h2 : w (s:ℝ) * ‖(Q (s:ℝ)).symm (I1 - I2)‖
        ≤ C * (L_Θ:ℝ) / lam * dist Z1 Z2 := by
      have hcont1 : Continuous (fun σ : ℝ => Θ (s:ℝ) σ (dev Z1 σ)) :=
        hΘ_cont.comp (continuous_const.prodMk (continuous_id.prodMk (dev_cont Z1)))
      have hcont2 : Continuous (fun σ : ℝ => Θ (s:ℝ) σ (dev Z2 σ)) :=
        hΘ_cont.comp (continuous_const.prodMk (continuous_id.prodMk (dev_cont Z2)))
      have hi1 : IntervalIntegrable (fun σ : ℝ => Θ (s:ℝ) σ (dev Z1 σ)) volume (s:ℝ) b :=
        hcont1.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun σ : ℝ => Θ (s:ℝ) σ (dev Z2 σ)) volume (s:ℝ) b :=
        hcont2.intervalIntegrable _ _
      have hIeq : I1 - I2 = ∫ σ in (s:ℝ)..b, (Θ (s:ℝ) σ (dev Z1 σ) - Θ (s:ℝ) σ (dev Z2 σ)) := by
        rw [hI1, hI2]
        exact (intervalIntegral.integral_sub hi1 hi2).symm
      have hpt : ∀ σ ∈ Set.Icc (s:ℝ) b, ‖Θ (s:ℝ) σ (dev Z1 σ) - Θ (s:ℝ) σ (dev Z2 σ)‖
          ≤ (L_Θ:ℝ) * dist (dev Z1 σ) (dev Z2 σ) := by
        intro σ hσ
        rw [← dist_eq_norm]
        exact (hΘ_lip (s:ℝ) hs σ (hsub σ hσ)).dist_le_mul _
          (hmem Z1 hZ1 σ hσ) _ (hmem Z2 hZ2 σ hσ)
      have hnorm : ‖I1 - I2‖ ≤ (L_Θ:ℝ) * (∫ σ in (s:ℝ)..b, dist (dev Z1 σ) (dev Z2 σ)) := by
        rw [hIeq]
        calc ‖∫ σ in (s:ℝ)..b, (Θ (s:ℝ) σ (dev Z1 σ) - Θ (s:ℝ) σ (dev Z2 σ))‖
            ≤ ∫ σ in (s:ℝ)..b, ‖Θ (s:ℝ) σ (dev Z1 σ) - Θ (s:ℝ) σ (dev Z2 σ)‖ :=
              intervalIntegral.norm_integral_le_integral_norm hs.2
          _ ≤ ∫ σ in (s:ℝ)..b, (L_Θ:ℝ) * dist (dev Z1 σ) (dev Z2 σ) :=
              intervalIntegral.integral_mono_on (μ := volume) hs.2
                ((hcont1.sub hcont2).norm.intervalIntegrable (μ := volume) (s:ℝ) b)
                (((continuous_const : Continuous fun _ : ℝ => (L_Θ:ℝ)).mul
                    ((dev_cont Z1).dist (dev_cont Z2))).intervalIntegrable (μ := volume) (s:ℝ) b)
                hpt
          _ = (L_Θ:ℝ) * (∫ σ in (s:ℝ)..b, dist (dev Z1 σ) (dev Z2 σ)) :=
              intervalIntegral.integral_const_mul _ _
      have hcontd : Continuous (fun σ : ℝ => dist (dev Z1 σ) (dev Z2 σ)) :=
        (dev_cont Z1).dist (dev_cont Z2)
      have hIntle : (∫ σ in (s:ℝ)..b, dist (dev Z1 σ) (dev Z2 σ))
          ≤ dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹) := by
        have hmono := intervalIntegral.integral_mono_on (μ := volume) hs.2
          (hcontd.intervalIntegrable (μ := volume) (s:ℝ) b)
          ((hw_inv_cont.mul continuous_const).intervalIntegrable (μ := volume) (s:ℝ) b) hdd
        calc (∫ σ in (s:ℝ)..b, dist (dev Z1 σ) (dev Z2 σ))
            ≤ ∫ σ in (s:ℝ)..b, (w σ)⁻¹ * dist Z1 Z2 := hmono
          _ = (∫ σ in (s:ℝ)..b, (w σ)⁻¹) * dist Z1 Z2 := intervalIntegral.integral_mul_const _ _
          _ = dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹) := by ring
      have hweight : w (s:ℝ) * (∫ σ in (s:ℝ)..b, (w σ)⁻¹) ≤ 1 / lam := by
        rw [← intervalIntegral.integral_const_mul]
        have hfun : (fun σ : ℝ => w (s:ℝ) * (w σ)⁻¹) = fun σ : ℝ => w (s:ℝ) / w σ := by
          funext σ; rw [div_eq_mul_inv]
        rw [hfun]
        exact hint (s:ℝ) hs
      have hQle : ‖(Q (s:ℝ)).symm (I1 - I2)‖ ≤ C * ‖I1 - I2‖ := by
        calc ‖(Q (s:ℝ)).symm (I1 - I2)‖ ≤ ‖((Q (s:ℝ)).symm : E →L[ℝ] E)‖ * ‖I1 - I2‖ :=
              ContinuousLinearMap.le_opNorm ((Q (s:ℝ)).symm : E →L[ℝ] E) (I1 - I2)
          _ ≤ C * ‖I1 - I2‖ := mul_le_mul_of_nonneg_right (hCbd (s:ℝ) hs) (norm_nonneg _)
      have hstep2 : ‖I1 - I2‖ ≤ (L_Θ:ℝ) * (dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹)) := by
        calc ‖I1 - I2‖ ≤ (L_Θ:ℝ) * (∫ σ in (s:ℝ)..b, dist (dev Z1 σ) (dev Z2 σ)) := hnorm
          _ ≤ (L_Θ:ℝ) * (dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹)) :=
              mul_le_mul_of_nonneg_left hIntle hLnn
      calc w (s:ℝ) * ‖(Q (s:ℝ)).symm (I1 - I2)‖
          ≤ w (s:ℝ) * (C * ((L_Θ:ℝ) * (dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hw_pos (s:ℝ)))
            calc ‖(Q (s:ℝ)).symm (I1 - I2)‖ ≤ C * ‖I1 - I2‖ := hQle
              _ ≤ C * ((L_Θ:ℝ) * (dist Z1 Z2 * (∫ σ in (s:ℝ)..b, (w σ)⁻¹))) :=
                  mul_le_mul_of_nonneg_left hstep2 hCpos.le
        _ = C * (L_Θ:ℝ) * dist Z1 Z2 * (w (s:ℝ) * (∫ σ in (s:ℝ)..b, (w σ)⁻¹)) := by ring
        _ ≤ C * (L_Θ:ℝ) * dist Z1 Z2 * (1 / lam) := by
            refine mul_le_mul_of_nonneg_left hweight ?_
            positivity
        _ = C * (L_Θ:ℝ) / lam * dist Z1 Z2 := by ring
    calc w (s:ℝ) * ‖(A1 - A2) + (Q (s:ℝ)).symm (I1 - I2)‖
        ≤ w (s:ℝ) * (‖A1 - A2‖ + ‖(Q (s:ℝ)).symm (I1 - I2)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt (hw_pos (s:ℝ)))
      _ = w (s:ℝ) * ‖A1 - A2‖ + w (s:ℝ) * ‖(Q (s:ℝ)).symm (I1 - I2)‖ := by ring
      _ ≤ (K_G:ℝ) * dist Z1 Z2 + C * (L_Θ:ℝ) / lam * dist Z1 Z2 := add_le_add h1 h2
      _ = k * dist Z1 Z2 := by rw [hk]; ring
  have hOp_lip : ∀ (Z1 Z2 : BoundedContinuousFunction (Set.Icc a b) E),
      dist Z1 0 ≤ r → dist Z2 0 ≤ r → dist (Op Z1) (Op Z2) ≤ k * dist Z1 Z2 :=
    fun Z1 Z2 h1 h2 => (BoundedContinuousFunction.dist_le (mul_nonneg hk_nonneg dist_nonneg)).2
      (fun s => hstep Z1 Z2 s h1 h2)
  have hOp0 : dist (Op (0 : BoundedContinuousFunction (Set.Icc a b) E)) 0 ≤ (1 - k) * r / 2 := by
    refine (BoundedContinuousFunction.dist_le (by
      have h1 : 0 < 1 - k := by linarith
      positivity)).2 (fun s => ?_)
    have hs : (s : ℝ) ∈ Set.Icc a b := s.2
    have hc0 : Continuous (fun σ : ℝ => Θ0 (s:ℝ) σ (0 : E)) :=
      hΘ0_cont.comp (((continuous_const : Continuous fun _ : ℝ => (s:ℝ))).prodMk
        (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (0:E))))
    have hc1 : Continuous (fun σ : ℝ => Θ (s:ℝ) σ (0 : E)) :=
      hΘ_cont.comp (((continuous_const : Continuous fun _ : ℝ => (s:ℝ))).prodMk
        (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (0:E))))
    have hInt : (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (dev (0 : BoundedContinuousFunction (Set.Icc a b) E) σ))
        = ∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0 : E) := by
      apply intervalIntegral.integral_congr
      intro σ _
      simp only [hdev_zero]
    have hGd : dist (G (s:ℝ) (0:E)) (G0 (s:ℝ) (0:E)) < eps :=
      hG_close (s:ℝ) hs (0:E) (by simp)
    have hGd' : ‖G (s:ℝ) (0:E) - G0 (s:ℝ) (0:E)‖ < eps := by
      rwa [dist_eq_norm] at hGd
    have hXd : dist (Ξ (s:ℝ)) (Ξ0 (s:ℝ)) < eps := hΞ_close (s:ℝ) hs
    have hXd' : ‖Ξ0 (s:ℝ) - Ξ (s:ℝ)‖ < eps := by
      rw [norm_sub_rev]; rwa [dist_eq_norm] at hXd
    have hbase0 : G0 (s:ℝ) (0:E)
        - (∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E)) - Ξ0 (s:ℝ) = 0 := by
      rw [hbase (s:ℝ) hs]; abel
    have hintd : ‖(∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E))
        - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E))‖ ≤ eps * (b - (s:ℝ)) := by
      rw [← intervalIntegral.integral_sub (hc0.intervalIntegrable (s:ℝ) b)
        (hc1.intervalIntegrable (s:ℝ) b)]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (C := eps) (fun x hx => ?_)) ?_
      · rw [Set.uIoc_of_le hs.2] at hx
        have h := hΘ_close (s:ℝ) hs x ⟨le_trans hs.1 (le_of_lt hx.1), hx.2⟩ (0:E) (by simp)
        rw [dist_eq_norm, norm_sub_rev] at h
        exact le_of_lt h
      · rw [abs_of_nonneg (by linarith [hs.2])]
    have hb : ‖G (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ)‖
        ≤ eps * (2 + (b - a)) := by
      have hid : G (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ)
          = (G (s:ℝ) (0:E) - G0 (s:ℝ) (0:E))
            + (G0 (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E)) - Ξ0 (s:ℝ))
            + ((∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E))
                - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)))
            + (Ξ0 (s:ℝ) - Ξ (s:ℝ)) := by abel
      calc ‖G (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ)‖
          ≤ ‖G (s:ℝ) (0:E) - G0 (s:ℝ) (0:E)‖
            + ‖(∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E))
                - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E))‖
            + ‖Ξ0 (s:ℝ) - Ξ (s:ℝ)‖ := by
            rw [hid, hbase0, add_zero]
            have ha := norm_add_le (G (s:ℝ) (0:E) - G0 (s:ℝ) (0:E))
              (((∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E))
                - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E))) + (Ξ0 (s:ℝ) - Ξ (s:ℝ)))
            have hb := norm_add_le ((∫ σ in (s:ℝ)..b, Θ0 (s:ℝ) σ (0:E))
              - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E))) (Ξ0 (s:ℝ) - Ξ (s:ℝ))
            rw [add_assoc]
            linarith [ha, hb]
        _ ≤ eps + eps * (b - (s:ℝ)) + eps := by linarith [hGd'.le, hintd, hXd'.le]
        _ ≤ eps * (2 + (b - a)) := by
            have hle : b - (s:ℝ) ≤ b - a := by linarith [hs.1]
            nlinarith [heps_pos.le]
    have h0s : (0 : BoundedContinuousFunction (Set.Icc a b) E) s = 0 := rfl
    rw [Op_apply (0 : BoundedContinuousFunction (Set.Icc a b) E) s, hdev_zero, zero_sub, hInt,
      h0s, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (hw_pos (s:ℝ)),
      norm_neg]
    have hQle : ‖(Q (s:ℝ)).symm (G (s:ℝ) (0:E)
        - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ))‖
        ≤ C * (eps * (2 + (b - a))) := by
      calc ‖(Q (s:ℝ)).symm (G (s:ℝ) (0:E)
            - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ))‖
          ≤ ‖((Q (s:ℝ)).symm : E →L[ℝ] E)‖
            * ‖G (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ)‖ :=
            ContinuousLinearMap.le_opNorm ((Q (s:ℝ)).symm : E →L[ℝ] E) _
        _ ≤ C * ‖G (s:ℝ) (0:E) - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ)‖ :=
            mul_le_mul_of_nonneg_right (hCbd (s:ℝ) hs) (norm_nonneg _)
        _ ≤ C * (eps * (2 + (b - a))) := mul_le_mul_of_nonneg_left hb hCpos.le
    calc w (s:ℝ) * ‖(Q (s:ℝ)).symm (G (s:ℝ) (0:E)
          - (∫ σ in (s:ℝ)..b, Θ (s:ℝ) σ (0:E)) - Ξ (s:ℝ))‖
        ≤ w (s:ℝ) * (C * (eps * (2 + (b - a)))) :=
          mul_le_mul_of_nonneg_left hQle (le_of_lt (hw_pos (s:ℝ)))
      _ ≤ w b * (C * (eps * (2 + (b - a)))) :=
          mul_le_mul_of_nonneg_right (hw_mono hs.2) (by positivity)
      _ = (1 - k) * r / 2 := by rw [← heps_val]; ring
  have hOp_ball : ∀ Z : BoundedContinuousFunction (Set.Icc a b) E, dist Z 0 ≤ r →
      dist (Op Z) 0 ≤ r := by
    intro Z hZ
    have h1 : dist (Op Z) (Op (0 : BoundedContinuousFunction (Set.Icc a b) E)) ≤ k * dist Z 0 :=
      hOp_lip Z 0 hZ (by rw [dist_self]; exact hr0.le)
    have h2 : dist (Op Z) 0 ≤ k * dist Z 0 + (1 - k) * r / 2 := by
      calc dist (Op Z) 0 ≤ dist (Op Z) (Op 0) + dist (Op 0) 0 := dist_triangle _ _ _
        _ ≤ k * dist Z 0 + (1 - k) * r / 2 := add_le_add h1 hOp0
    have h3 : k * dist Z 0 ≤ k * r := mul_le_mul_of_nonneg_left hZ hk_nonneg
    have h4 : k * r + (1 - k) * r / 2 ≤ r := by nlinarith [hr0.le, hk_lt]
    linarith
  haveI : Nonempty (Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r) :=
    ⟨⟨0, by rw [Metric.mem_closedBall, dist_self]; exact hr0.le⟩⟩
  haveI : CompleteSpace (Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r) := by
    haveI : IsClosed (Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r) :=
      Metric.isClosed_closedBall
    infer_instance
  let F : Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r →
      Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r :=
    fun Z => ⟨Op Z.1, hOp_ball Z.1 Z.2⟩
  have hF_lip : LipschitzWith ⟨k, hk_nonneg⟩ F := by
    refine LipschitzWith.of_dist_le_mul (fun Z1 Z2 => ?_)
    exact hOp_lip Z1.1 Z2.1 Z1.2 Z2.2
  have hcontr : ContractingWith ⟨k, hk_nonneg⟩ F := ⟨by exact_mod_cast hk_lt, hF_lip⟩
  set W : Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r :=
    ContractingWith.fixedPoint F hcontr with hW
  have hWfix : F W = W := ContractingWith.fixedPoint_isFixedPt hcontr
  refine ⟨fun t : ℝ => (w t)⁻¹ • bcfExtG hab.le (W : BoundedContinuousFunction (Set.Icc a b) E) t,
    ?_, ?_, ?_⟩
  · exact ((hw_inv_cont.smul (bcfExtG_continuous hab.le _)).continuousOn)
  · intro s hs
    rw [dist_eq_norm, sub_zero]
    show ‖dev (W : BoundedContinuousFunction (Set.Icc a b) E) s‖ ≤ r
    exact le_trans (dev_norm _ hs) W.2
  · intro s hs
    have hfix : (Op (W : BoundedContinuousFunction (Set.Icc a b) E)) (⟨s, hs⟩ : Set.Icc a b)
        = (W : BoundedContinuousFunction (Set.Icc a b) E) (⟨s, hs⟩ : Set.Icc a b) := by
      have h := congrArg (fun f : Set.Icc a b → E => f (⟨s, hs⟩ : Set.Icc a b))
        (congrArg (fun x : Metric.closedBall (0 : BoundedContinuousFunction (Set.Icc a b) E) r =>
          ((x : BoundedContinuousFunction (Set.Icc a b) E) : Set.Icc a b → E)) hWfix)
      show (Op (W : BoundedContinuousFunction (Set.Icc a b) E)) (⟨s, hs⟩ : Set.Icc a b) = _
      exact h
    rw [Op_apply] at hfix
    rw [← bcfExtG_of_mem hab.le (W : BoundedContinuousFunction (Set.Icc a b) E) hs] at hfix
    rw [← dev_smul (W : BoundedContinuousFunction (Set.Icc a b) E) s] at hfix
    have h2 : dev (W : BoundedContinuousFunction (Set.Icc a b) E) s
        - (Q s).symm (G s (dev (W : BoundedContinuousFunction (Set.Icc a b) E) s)
          - (∫ σ in s..b, Θ s σ (dev (W : BoundedContinuousFunction (Set.Icc a b) E) σ))
          - Ξ s)
        = dev (W : BoundedContinuousFunction (Set.Icc a b) E) s := by
      have hcan := congrArg (fun z : E => (w s)⁻¹ • z) hfix
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (hw_pos s)), one_smul] using hcan
    have h3 : (Q s).symm (G s (dev (W : BoundedContinuousFunction (Set.Icc a b) E) s)
          - (∫ σ in s..b, Θ s σ (dev (W : BoundedContinuousFunction (Set.Icc a b) E) σ))
          - Ξ s) = 0 := sub_eq_self.mp h2
    have h4 : G s (dev (W : BoundedContinuousFunction (Set.Icc a b) E) s)
          - (∫ σ in s..b, Θ s σ (dev (W : BoundedContinuousFunction (Set.Icc a b) E) σ))
          - Ξ s = 0 := by
      have h5 := congrArg (fun x => (Q s) x) h3
      simpa using h5
    simpa [add_comm] using eq_add_of_sub_eq (sub_eq_zero.mp h4)
end Commons.Analysis.Calculus
end

-- ===== FILE _app2.lean =====

noncomputable section
open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## Continuity of the concrete stationary and perturbed data -/

lemma continuous_TG (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) :
    Continuous (fun p : ℝ × VS => TG n Qe ρ p.1 p.2) := by
  have hmap : Continuous (fun p : ℝ × VS => (p.1, baseZ p.1 + ρ • p.2)) := by fun_prop
  have h1 : Continuous (fun p : ℝ × VS => baseG n p.1 (baseZ p.1 + ρ • p.2)) :=
    (contDiff_baseG_pair n).continuous.comp hmap
  have h2 : Continuous (fun p : ℝ × VS => Qe.symm (baseG n p.1 (baseZ p.1 + ρ • p.2))) :=
    Qe.symm.continuous.comp h1
  exact (h2.const_smul (1 / ρ)).congr (fun p => by simp [TG])

lemma continuous_TΘ (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) :
    Continuous (fun p : ℝ × ℝ × VS => TΘ n Qe ρ p.1 p.2.1 p.2.2) := by
  have hmap : Continuous (fun p : ℝ × ℝ × VS => ((p.2.1, baseZ p.2.1 + ρ • p.2.2), p.1)) := by
    fun_prop
  have hbase : ContDiff ℝ ∞ (fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) :=
    contDiff_baseTheta n
  have h1 : Continuous (fun p : ℝ × ℝ × VS => baseΘ n p.1 p.2.1 (baseZ p.2.1 + ρ • p.2.2)) := by
    have h : Continuous ((fun q : (ℝ × VS) × ℝ => baseΘ n q.2 q.1.1 q.1.2) ∘
        (fun p : ℝ × ℝ × VS => ((p.2.1, baseZ p.2.1 + ρ • p.2.2), p.1))) :=
      hbase.continuous.comp hmap
    simpa only [Function.comp_def] using h
  have h2 := Qe.symm.continuous.comp h1
  exact (h2.const_smul (1 / ρ)).congr (fun p => by simp [TΘ])

lemma continuous_TΞ (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) :
    Continuous (fun s : ℝ => TΞ n Qe ρ s) := by
  have h1 : Continuous (fun s : ℝ => baseΞ n s) := by
    have h : Continuous (fun s : ℝ => RyaboginVolterra.Xi n (fun _ : ℝ => 0) s) :=
      (contDiff_Xi n contDiff_const).continuous
    simpa [baseΞ] using h
  have h2 := Qe.symm.continuous.comp h1
  exact (h2.const_smul (1 / ρ)).congr (fun s => by simp [TΞ])

lemma continuous_Gn (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    Continuous (fun p : ℝ × VS => Gn n Qe ρ h p.1 p.2) := by
  have hmap : Continuous (fun p : ℝ × VS => (p.1, baseZ p.1 + ρ • p.2)) := by fun_prop
  have h1 : Continuous (fun p : ℝ × VS => RyaboginVolterra.G n h p.1 (baseZ p.1 + ρ • p.2)) :=
    (contDiff_G_pair n hh).continuous.comp hmap
  have h2 : Continuous (fun p : ℝ × VS =>
      Qe.symm (RyaboginVolterra.G n h p.1 (baseZ p.1 + ρ • p.2))) :=
    Qe.symm.continuous.comp h1
  refine (h2.const_smul (1 / ρ)).congr (fun p => ?_)
  simp [Gn_eq]

lemma continuous_ThnEps (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ : ρ ≠ 0) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (ε : ℝ) :
    Continuous (fun p : ℝ × ℝ × VS => ThnEps n Qe ρ h ε p.1 p.2.1 p.2.2) := by
  have hmap : Continuous (fun p : ℝ × ℝ × VS => ((ε, (p.1, p.2.1)), p.2.2)) := by
    fun_prop
  have h : Continuous ((fun q : ((ℝ × (ℝ × ℝ)) × VS) =>
      ThnEps n Qe ρ h q.1.1 q.1.2.1 q.1.2.2 q.2) ∘
      (fun p : ℝ × ℝ × VS => ((ε, (p.1, p.2.1)), p.2.2))) :=
    (contDiff_ThnEps n Qe hρ hh).continuous.comp hmap
  simpa only [Function.comp_def] using h

lemma continuous_Xin (n : ℕ) (Qe : VS ≃L[ℝ] VS) (ρ : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    Continuous (fun s : ℝ => Xin n Qe ρ h s) := by
  have h1 : Continuous (fun s : ℝ => RyaboginVolterra.Xi n h s) := (contDiff_Xi n hh).continuous
  have h2 := Qe.symm.continuous.comp h1
  exact (h2.const_smul (1 / ρ)).congr (fun s => by simp [Xin])



/-- **The Lipschitz constant of the `Θ`-row** (the last ingredient of the `L_Θ` hypothesis of the
abstract Volterra theorem). -/
lemma exists_lipschitz_Thn_uniform (n : ℕ) (Qe : VS ≃L[ℝ] VS) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 2) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {a : ℝ} (ha : 0 < a) :
    ∃ L : NNReal, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1,
      LipschitzOnWith L (fun U : VS => ThnEps n Qe ρ h ε s σ U)
        (Metric.closedBall (0 : VS) 1) := by
  obtain ⟨CP0, hCP0⟩ := exists_bound_thetaPs n hh a
  obtain ⟨KP0, hKP0⟩ := exists_lipschitz_thetaPs_w n hh a
  obtain ⟨CQ0, hCQ0⟩ := exists_bound_thetaQs n hh a
  obtain ⟨KQ0, hKQ0⟩ := exists_lipschitz_thetaQs_w n hh a
  obtain ⟨M, hM1, hM⟩ := exists_baseZ_norm_bound (a := a)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hCP : ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      |thetaPs n h ε σ (w, s)| ≤ max CP0 0 := fun ε hε σ hσ w hw s hs =>
    le_trans (hCP0 ε hε σ hσ w hw s hs) (le_max_left _ _)
  have hCQ : ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ s ∈ Set.Icc a 1,
      |thetaQs n h ε σ (w, s)| ≤ max CQ0 0 := fun ε hε σ hσ w hw s hs =>
    le_trans (hCQ0 ε hε σ hσ w hw s hs) (le_max_left _ _)
  have hKP : ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ w' ∈ Set.Icc (-2:ℝ) 2, ∀ s ∈ Set.Icc a 1,
      |thetaPs n h ε σ (w, s) - thetaPs n h ε σ (w', s)| ≤ max KP0 0 * |w - w'| :=
    fun ε hε σ hσ w hw w' hw' s hs =>
      le_trans (hKP0 ε hε σ hσ s hs w hw w' hw')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hKQ : ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc a 1, ∀ w ∈ Set.Icc (-2:ℝ) 2,
      ∀ w' ∈ Set.Icc (-2:ℝ) 2, ∀ s ∈ Set.Icc a 1,
      |thetaQs n h ε σ (w, s) - thetaQs n h ε σ (w', s)| ≤ max KQ0 0 * |w - w'| :=
    fun ε hε σ hσ w hw w' hw' s hs =>
      le_trans (hKQ0 ε hε σ hσ s hs w hw w' hw')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  refine ⟨⟨‖(Qe.symm : VS →L[ℝ] VS)‖ *
      (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))),
      by positivity⟩, fun ε hε s hs σ hσ => ?_⟩
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hb0 : |baseZ σ 0| ≤ 1 := by
    rw [baseZ_apply_zero]
    exact abs_le.mpr (profileX_mem_Icc σ)
  have hb1 : |baseZ σ 1| ≤ 1 := by
    rw [baseZ_apply_one]
    exact abs_le.mpr (profileX_mem_Icc σ)
  have hb2 : |baseZ σ 2| ≤ M := le_trans (abs_apply_le_norm_state (baseZ σ) 2) (hM σ hσ)
  have hb3 : |baseZ σ 3| ≤ M := le_trans (abs_apply_le_norm_state (baseZ σ) 3) (hM σ hσ)
  have hshape : ∀ x ∈ Metric.closedBall (0 : VS) 1, ∀ y ∈ Metric.closedBall (0 : VS) 1,
      ‖thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
          (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
          (baseZ σ) ρ y‖ ≤ ρ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))) * ‖x - y‖ := by
    intro x hx y hy
    have h := norm_thetaShape_sub_le
      (P := fun w => thetaPs n h ε σ (w, s)) (Q := fun w => thetaQs n h ε σ (w, s))
      (zb := baseZ σ) (ρ := ρ) (CP := max CP0 0) (CQ := max CQ0 0)
      (KP := max KP0 0) (KQ := max KQ0 0) (M := M)
      hρ0 hρ1 hb0 hb1 hb2 hb3 hM0 (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      (le_max_right _ _) (fun w hw => hCP ε hε σ hσ w hw s hs)
      (fun w hw => hCQ ε hε σ hσ w hw s hs)
      (fun w hw w' hw' => hKP ε hε σ hσ w hw w' hw' s hs)
      (fun w hw w' hw' => hKQ ε hε σ hσ w hw w' hw' s hs) hx hy
    exact h
  have hbridge : ∀ U : VS, ThnEps n Qe ρ h ε s σ U = (1 / ρ) • Qe.symm
      (thetaShape (fun w => thetaPs n h ε σ (w, s)) (fun w => thetaQs n h ε σ (w, s))
        (baseZ σ) ρ U) := by
    intro U
    have h1 : ThnEps n Qe ρ h ε s σ U = (1 / ρ) • Qe.symm
        (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)) := rfl
    rw [h1, Theta_eq_thetaShape n hd ε s σ ρ U]
    have hfun1 : (fun w => thetaP n h (ε, (σ, w)) s) = fun w => thetaPs n h ε σ (w, s) := by
      funext w
      exact (thetaPs_eq n h ε σ (w, s)).symm
    have hfun2 : (fun w => thetaQ n h (ε, (σ, w)) s) = fun w => thetaQs n h ε σ (w, s) := by
      funext w
      exact (thetaQs_eq n h ε σ (w, s)).symm
    rw [hfun1, hfun2]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hΘ := hshape x hx y hy
  have hdiff : (1 / ρ) • Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x)
      - (1 / ρ) • Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)
      = (1 / ρ) • (Qe.symm (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)) := by
    rw [← smul_sub, ← map_sub]
  rw [dist_eq_norm, hbridge x, hbridge y, hdiff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hρ0)]
  have hQe : ‖(Qe.symm : VS →L[ℝ] VS) (thetaShape (fun w => thetaPs n h ε σ (w, s))
      (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
      - thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)‖
      ≤ ‖(Qe.symm : VS →L[ℝ] VS)‖ *
        ‖thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
          - thetaShape (fun w => thetaPs n h ε σ (w, s))
            (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y‖ :=
    (Qe.symm : VS →L[ℝ] VS).le_opNorm _
  calc (1 / ρ) * ‖(Qe.symm : VS →L[ℝ] VS) (thetaShape (fun w => thetaPs n h ε σ (w, s))
        (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ x
        - thetaShape (fun w => thetaPs n h ε σ (w, s))
          (fun w => thetaQs n h ε σ (w, s)) (baseZ σ) ρ y)‖
      ≤ (1 / ρ) * (‖(Qe.symm : VS →L[ℝ] VS)‖ * (ρ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1))) * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left
          (le_trans hQe (mul_le_mul_of_nonneg_left hΘ (norm_nonneg _))) (by positivity)
    _ = (‖(Qe.symm : VS →L[ℝ] VS)‖ * (2 + 2 * (max CP0 0 + max KP0 0 * (M + 1)) + 2 * (max CQ0 0 + max KQ0 0 * (M + 1)))) * ‖x - y‖ := by
        field_simp

/-! ## Unscaling the normalised Volterra fixed point -/

lemma unscaled_volterra_fixed {n : ℕ} {Qe : VS ≃L[ℝ] VS} {ρ : ℝ} (hρ : ρ ≠ 0)
    {h : ℝ → ℝ} {ε : ℝ} {Z : ℝ → VS} {a : ℝ} {b : ℝ}
    (hfix : ∀ s ∈ Set.Icc a b,
      Gn n Qe ρ (ε • h) s (Z s)
        = (∫ σ in s..b, ThnEps n Qe ρ h ε s σ (Z σ)) + Xin n Qe ρ (ε • h) s)
    (hint : ∀ s ∈ Set.Icc a b,
      IntervalIntegrable (fun σ => RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
        volume s b) :
    ∀ s ∈ Set.Icc a b,
      RyaboginVolterra.G n (ε • h) s (baseZ s + ρ • Z s)
        = (∫ σ in s..b, RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
          + RyaboginVolterra.Xi n (ε • h) s := by
  intro s hs
  refine Qe.symm.injective ?_
  have hLHS : Qe.symm (RyaboginVolterra.G n (ε • h) s (baseZ s + ρ • Z s))
      = ρ • Gn n Qe ρ (ε • h) s (Z s) := by
    rw [Gn_eq, smul_smul, mul_one_div_cancel hρ, one_smul]
  have hpoint : ∀ σ : ℝ,
      Qe.symm (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
        = ρ • ThnEps n Qe ρ h ε s σ (Z σ) := fun σ => by
    rw [ThnEps, smul_smul, mul_one_div_cancel hρ, one_smul]
  have hR1 : Qe.symm (∫ σ in s..b,
        RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
      = ρ • ∫ σ in s..b, ThnEps n Qe ρ h ε s σ (Z σ) := by
    have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm (Qe.symm : VS →L[ℝ] VS)
      (f := fun σ : ℝ => RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
      (hint s hs)
    calc Qe.symm (∫ σ in s..b,
            RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ))
        = (Qe.symm : VS →L[ℝ] VS) (∫ σ in s..b,
            RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ)) := rfl
      _ = ∫ σ in s..b, (Qe.symm : VS →L[ℝ] VS)
            (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ)) := hcomp.symm
      _ = ∫ σ in s..b, Qe.symm
            (RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • Z σ)) := by
          exact intervalIntegral.integral_congr fun σ _ => rfl
      _ = ∫ σ in s..b, ρ • ThnEps n Qe ρ h ε s σ (Z σ) := by
          exact intervalIntegral.integral_congr fun σ _ => hpoint σ
      _ = ρ • ∫ σ in s..b, ThnEps n Qe ρ h ε s σ (Z σ) :=
          intervalIntegral.integral_smul (f := fun σ : ℝ => ThnEps n Qe ρ h ε s σ (Z σ)) ρ
  have hR2 : Qe.symm (RyaboginVolterra.Xi n (ε • h) s) = ρ • Xin n Qe ρ (ε • h) s := by
    rw [Xin, smul_smul, mul_one_div_cancel hρ, one_smul]
  rw [hLHS, map_add, hR1, hR2, ← smul_add, hfix s hs]

/-- **The Volterra existence step of Ryabogin's even-dimensional construction.**
For a smooth `h` and `0 < a < 1` there is `ε > 0` and a continuous state-valued function `Z` on
`[a,1]` solving the (unscaled) four-by-four Volterra system of the paper. -/
theorem honest_volterra_solution_full (n : ℕ) (hn : 2 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {εmax : ℝ}
    (hεmax : 0 < εmax) :
    ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ L : NNReal, ∃ Z : ℝ → VS,
      ∃ Zsc : ℝ → VS,
      ContinuousOn Z (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      ContinuousOn Zsc (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, dist (Zsc s) 0 ≤ r) ∧
      (∀ s ∈ Set.Icc a 1, Z s = baseZ s + ρ • Zsc s) ∧
      (∀ s ∈ Set.Icc a 1,
        Gn n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ (ε • h) s (Zsc s)
          = (∫ σ in s..1, ThnEps n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ h ε s σ (Zsc σ))
            + Xin n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ (ε • h) s) ∧
      (∀ s ∈ Set.Icc a 1, ∀ σ ∈ Set.Icc a 1, LipschitzOnWith L
        (fun U : VS => ThnEps n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ h ε s σ U)
        (Metric.closedBall (0 : VS) 1)) ∧
      (∀ s ∈ Set.Icc a 1, LipschitzOnWith (1 / 2 : NNReal)
        (fun U : VS => U - ((Qref n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ha) s).symm
          (Gn n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ (ε • h) s U))
        (Metric.closedBall (0 : VS) 1)) ∧
      (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc a 1, |h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  classical
  set Qe : VS ≃L[ℝ] VS := jacEquiv n (by norm_num : (0 : ℝ) < 1) with hQe
  obtain ⟨ρ, hρmem, εpG, hεpG, hLG⟩ := exists_lipschitz_PhiG n hn Qe hh ha ha1.le
  obtain ⟨hρ0, hρ1⟩ := hρmem
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hρ1' : ρ ≤ 1 / 2 := le_of_lt hρ1
  obtain ⟨L, hL⟩ := exists_lipschitz_Thn_uniform n Qe hρ0 hρ1' hh ha
  have hbase : ∀ s ∈ Set.Icc a 1,
      TG n Qe ρ s 0 = (∫ σ in s..1, TΘ n Qe ρ s σ 0) + TΞ n Qe ρ s :=
    Tbase_identity_jacEquiv n hn hρne ha ha1.le
  obtain ⟨εV, hεV⟩ :=
    Commons.Analysis.Calculus.volterra_perturbation_exists_weighted (E := VS) (b := 1) ha1
      (G0 := fun s z => TG n Qe ρ s z) (Θ0 := fun s σ z => TΘ n Qe ρ s σ z)
      (Ξ0 := fun s => TΞ n Qe ρ s) (Q := Qref n Qe ha) (K_G := (1 / 2 : NNReal)) (L_Θ := L)
      (r := r)
      (by norm_num) hr0 hr1
      (by obtain ⟨C, _, hC⟩ := Qref_symm_bound n Qe ha ha1.le; exact ⟨C, hC⟩)
      (Qref_symm_continuous n Qe ha)
      (continuous_TG n Qe ρ) (continuous_TΘ n Qe ρ) (continuous_TΞ n Qe ρ) hbase
  -- bounds on `h`, `deriv h` and `baseZ`
  obtain ⟨M₁, hM₁, hM₁b⟩ := exists_baseZ_norm_bound (a := a)
  have hM₁0 : 0 ≤ M₁ := le_trans zero_le_one hM₁
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn
    (f := h) hh.continuous.continuousOn
  have hCd : Continuous (deriv h) := hh.continuous_deriv (by simp)
  obtain ⟨Cd, hCd'⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn
    (f := deriv h) hCd.continuousOn
  have hle2 : ((2:ℕ) : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have hcon2 : Continuous (fun s : ℝ => iteratedDeriv 2 h s) := by
    have h1 : ContDiff ℝ 1 (deriv h) := ((hh.of_le hle2).deriv')
    have h2 : Continuous (deriv (deriv h)) := h1.continuous_deriv (by norm_num)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h2
  obtain ⟨K₂, hK₂⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn
    hcon2.continuousOn
  set M : ℝ := M₁ + |Ch| + |Cd| + 1 with hMdef
  set M2 : ℝ := M + |K₂| + 1 with hM2def
  have hM2pos : 0 < M2 := by
    rw [hM2def]
    have := abs_nonneg K₂
    have := abs_nonneg Ch
    have := abs_nonneg Cd
    have : 0 < M₁ + |Ch| + |Cd| + 1 := by linarith
    linarith
  have hMM2 : M ≤ M2 := by
    rw [hM2def]
    have := abs_nonneg K₂
    linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    have := abs_nonneg Ch
    have := abs_nonneg Cd
    linarith
  have hMb : ∀ s ∈ Set.Icc a 1, |h s| ≤ M := by
    intro s hs
    have h1 : ‖h s‖ ≤ Ch := hCh s hs
    rw [Real.norm_eq_abs] at h1
    have h2 : Ch ≤ |Ch| := le_abs_self Ch
    have h3 : 0 ≤ |Cd| := abs_nonneg Cd
    rw [hMdef]; linarith
  have hMd : ∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M := by
    intro s hs
    have h1 : ‖deriv h s‖ ≤ Cd := hCd' s hs
    rw [Real.norm_eq_abs] at h1
    have h2 : Cd ≤ |Cd| := le_abs_self Cd
    have h3 : 0 ≤ |Ch| := abs_nonneg Ch
    rw [hMdef]; linarith
  have hhdiff : Differentiable ℝ h := hh.differentiable (by simp)
  -- the three closeness thresholds
  obtain ⟨εp1, hεp1, hcloseG, hsmallG⟩ := Gn_close_TG_ball (n := n) (Qe := Qe) (ρ := ρ) hρ0 hρ1'
    hhdiff hMpos hM₁0 hMb hMd hM₁b ha.le (η := εV) hεV.1
  obtain ⟨εp2, hεp2, hcloseΘ⟩ := Thn_close_TΘ n Qe hρ0 hρ1' hh (a := a) (e := εV) hεV.1
  obtain ⟨εp3, hεp3, hcloseΞ⟩ := Xi_close_TΞ n Qe hρ0 hh (a := a) ha.le (e := εV) hεV.1
  -- choose `ε`
  set M0 : ℝ := min εpG (min εp1 (min εp2 (min εp3 (min εV 1)))) with hM0
  have hM0pos : 0 < M0 := by
    rw [hM0]
    exact lt_min hεpG (lt_min hεp1 (lt_min hεp2 (lt_min hεp3 (lt_min hεV.1 one_pos))))
  have hm0 : 0 < min (min M0 εmax) (1 / (2 * M2)) :=
    lt_min (lt_min hM0pos hεmax) (by positivity)
  obtain ⟨ε, hε0, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < min (min M0 εmax) (1 / (2 * M2)) :=
    ⟨_, half_pos hm0, by linarith⟩
  have hεM0 : ε < M0 := by
    have h1 : ε < min M0 εmax := lt_of_lt_of_le hεlt (min_le_left _ _)
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  have hεmax' : ε < εmax := by
    have h1 : ε < min M0 εmax := lt_of_lt_of_le hεlt (min_le_left _ _)
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  have hεM2 : ε * M2 ≤ 1 / 2 := by
    have h1 : ε < 1 / (2 * M2) := lt_of_lt_of_le hεlt (min_le_right _ _)
    have h2 : ε * M2 < (1 / (2 * M2)) * M2 := mul_lt_mul_of_pos_right h1 hM2pos
    have h3 : (1 / (2 * M2)) * M2 = 1 / 2 := by field_simp
    linarith
  rw [hM0] at hεM0
  have hεpG' : ε < εpG := by
    have := min_le_left εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    linarith
  have hεp1' : ε < εp1 := by
    have h1 := min_le_right εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    have h2 := min_le_left εp1 (min εp2 (min εp3 (min εV 1)))
    linarith
  -- the explicit threshold of `Gn_close_TG_ball` gives `ε * M ≤ 1/2`, i.e. smallness of
  -- `ε * sup |h|` and `ε * sup |deriv h|`
  have hεM : ε * M ≤ 1 / 2 := hsmallG ε ⟨hε0, hεp1'⟩
  have hεp2' : ε < εp2 := by
    have h1 := min_le_right εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    have h2 := min_le_right εp1 (min εp2 (min εp3 (min εV 1)))
    have h3 := min_le_left εp2 (min εp3 (min εV 1))
    linarith
  have hεp3' : ε < εp3 := by
    have h1 := min_le_right εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    have h2 := min_le_right εp1 (min εp2 (min εp3 (min εV 1)))
    have h3 := min_le_right εp2 (min εp3 (min εV 1))
    have h4 := min_le_left εp3 (min εV 1)
    linarith
  have hεV' : ε < εV := by
    have h1 := min_le_right εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    have h2 := min_le_right εp1 (min εp2 (min εp3 (min εV 1)))
    have h3 := min_le_right εp2 (min εp3 (min εV 1))
    have h4 := min_le_right εp3 (min εV 1)
    have h5 := min_le_left εV 1
    linarith
  have hεone : ε ≤ 1 := by
    have h1 := min_le_right εpG (min εp1 (min εp2 (min εp3 (min εV 1))))
    have h2 := min_le_right εp1 (min εp2 (min εp3 (min εV 1)))
    have h3 := min_le_right εp2 (min εp3 (min εV 1))
    have h4 := min_le_right εp3 (min εV 1)
    have h5 := min_le_right εV 1
    linarith
  -- apply the abstract theorem
  obtain ⟨Z, hZcont, hZbd, hZfix⟩ := hεV.2
    (fun s z => Gn n Qe ρ (ε • h) s z) (fun s σ z => ThnEps n Qe ρ h ε s σ z)
    (fun s => Xin n Qe ρ (ε • h) s)
    (continuous_Gn n Qe ρ (hh.const_smul ε))
    (continuous_ThnEps n Qe hρne hh ε)
    (continuous_Xin n Qe ρ (hh.const_smul ε))
    (fun s hs z hz => hcloseG ε ⟨hε0, hεp1'⟩ s hs z hz)
    (fun s hs σ hσ z hz => hcloseΘ ε ⟨hε0, hεp2'⟩ s hs σ hσ z hz)
    (fun s hs => hcloseΞ ε ⟨hε0, hεp3'⟩ s hs)
    (fun s hs => by simpa only [PhiG] using hLG ε ⟨hε0, hεpG'⟩ s hs)
    (fun s hs σ hσ => hL ε ⟨hε0.le, hεone⟩ s hs σ hσ)
  refine ⟨ε, hε0, hεmax', ρ, hρ0, hρ1', L, fun s => baseZ s + ρ • Z s, Z, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact (contDiff_baseZ.continuous.continuousOn).add (hZcont.const_smul ρ)
  · intro s hs
    have h1 : ‖Z s‖ ≤ r := by
      simpa [dist_eq_norm] using hZbd s hs
    have h2 : ‖baseZ s + ρ • Z s - baseZ s‖ = ρ * ‖Z s‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ0]
    rw [h2]
    nlinarith [h1, hZbd s hs, hρ0, hρ1', ρ, hρ0.le]
  · intro s hs
    refine unscaled_volterra_fixed hρne hZfix (fun s hs => ?_) s hs
    have hs1 : s ≤ 1 := hs.2
    have hsub : Set.uIcc s 1 ⊆ Set.Icc a 1 := by
      rw [Set.uIcc_of_le hs1]
      exact Set.Icc_subset_Icc hs.1 le_rfl
    have hW : ContinuousOn (fun σ : ℝ => baseZ σ + ρ • Z σ) (Set.uIcc s 1) :=
      (continuous_baseZ.continuousOn.add (hZcont.const_smul ρ)).mono hsub
    have h1 : ContinuousOn (fun σ : ℝ => ((σ, baseZ σ + ρ • Z σ), s)) (Set.uIcc s 1) :=
      (continuousOn_id.prodMk hW).prodMk continuousOn_const
    have hΘc : Continuous (fun q : (ℝ × VS) × ℝ =>
        RyaboginVolterra.Theta n (ε • h) q.2 q.1.1 q.1.2) :=
      (contDiff_Theta n (hh.const_smul ε)).continuous
    exact (hΘc.continuousOn.comp h1 (fun x _ => Set.mem_univ _)).intervalIntegrable
  · exact hZcont
  · exact hZbd
  · intro s hs; rfl
  · exact hZfix
  · intro s hs σ hσ
    exact hL ε ⟨hε0.le, hεone⟩ s hs σ hσ
  · intro s hs
    have h := hLG ε ⟨hε0, hεpG'⟩ s hs
    simpa only [PhiG] using h

  · refine ⟨M2, hM2pos, ?_, ?_, ?_, hεM2⟩
    · intro s hs
      exact le_trans (hMb s hs) hMM2
    · intro s hs
      exact le_trans (hMd s hs) hMM2
    · intro s hs
      have h := hK₂ s hs
      rw [Real.norm_eq_abs] at h
      exact le_trans h (by rw [hM2def]; have := le_abs_self K₂; linarith)

/-- **The Volterra existence step of Ryabogin's even-dimensional construction.**
For a smooth `h` and `0 < a < 1` there is `ε > 0` and a continuous state-valued function `Z` on
`[a,1]` solving the (unscaled) four-by-four Volterra system of the paper. -/
theorem honest_volterra_solution (n : ℕ) (hn : 2 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ Z : ℝ → VS, ∃ Zsc : ℝ → VS,
      ContinuousOn Z (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      ContinuousOn Zsc (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, dist (Zsc s) 0 ≤ r) ∧
      (∀ s ∈ Set.Icc a 1, Z s = baseZ s + ρ • Zsc s) ∧
      (∀ s ∈ Set.Icc a 1,
        Gn n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ (ε • h) s (Zsc s)
          = (∫ σ in s..1, ThnEps n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ h ε s σ (Zsc σ))
            + Xin n (jacEquiv n (by norm_num : (0 : ℝ) < 1)) ρ (ε • h) s) ∧
      (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc a 1, |h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  obtain ⟨ε, hε0, _hε1, ρ, hρ0, hρ1, _L, Z, Zsc, hZc, hZbd, hZfix, hZsc_c, hZsc_b, hZsc_eq,
    hZsc_fix, _hΘlip, _hGlip, hM⟩ := honest_volterra_solution_full n hn hh ha ha1 hr0 hr1 one_pos
  exact ⟨ε, hε0, ρ, hρ0, hρ1, Z, Zsc, hZc, hZbd, hZfix, hZsc_c, hZsc_b, hZsc_eq, hZsc_fix, hM⟩

end Commons.Geometry.Ulam
end

-- ===== FILE _app3.lean =====

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Pointwise RealInnerProductSpace Interval Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## Coordinates of `Ξ` -/

@[simp] lemma Xi_apply_zero (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    RyaboginVolterra.Xi n h s 0 = profileX 1 := by
  simp [RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply]

@[simp] lemma Xi_apply_one (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    RyaboginVolterra.Xi n h s 1 = profileX 1 := by
  simp [RyaboginVolterra.Xi, RyaboginVolterra.mk4_apply]

/-! ## The globally continuous version of the Volterra solution -/

/-- The Volterra solution of `honest_volterra_solution`, extended to a globally continuous
`VS`-valued function. -/
theorem honest_volterra_solution_global (n : ℕ) (hn : 2 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) := by
  obtain ⟨ε, hε, ρ, hρ0, hρ1, Z, _Zsc, hZcont, hZbd, hZfix, _hZsc_c, _hZsc_b, _hZsc_eq,
    _hZsc_fix, _hM⟩ := honest_volterra_solution n hn hh ha ha1 hr0 hr1
  refine ⟨ε, hε, Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1), ?_, ?_, ?_⟩
  · exact hZcont.domRestrict.Icc_extend'
  · intro s hs
    have hEq : Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1) s = Z s :=
      Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs
    rw [hEq]
    exact hZbd s hs
  · intro s hs
    have hEq : ∀ σ ∈ Set.Icc a 1,
        Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1) σ = Z σ :=
      fun σ hσ => Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hσ
    have hint : (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ
          (Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1) σ))
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hσ1 : σ ∈ Set.Icc a 1 := by
        rw [Set.uIcc_of_le hs.2] at hσ
        exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
      rw [hEq σ hσ1]
    rw [hEq s hs, hint]
    exact hZfix s hs

/-! ## The first two coordinates of the fixed point equation -/

lemma volterra_row_zero {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {ε a : ℝ} {Z : ℝ → VS}
    (hZc : Continuous Z)
    (hfix : ∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
        + RyaboginVolterra.Xi n (ε • h) s)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2 := by
  have hΘc : Continuous (fun q : (ℝ × VS) × ℝ =>
      RyaboginVolterra.Theta n (ε • h) q.2 q.1.1 q.1.2) :=
    (contDiff_Theta n (hh.const_smul ε)).continuous
  have hmap : Continuous (fun σ : ℝ => ((σ, Z σ), s)) := by fun_prop
  have hint : Continuous (fun σ : ℝ => RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) :=
    hΘc.comp hmap
  have hcoord := congrArg (fun v : VS => v 0) (hfix s hs)
  have hG := G_apply_zero n (ε • h) s (Z s)
  have hsum : ((∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
      + RyaboginVolterra.Xi n (ε • h) s) 0
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) 0
        + (RyaboginVolterra.Xi n (ε • h) s) 0 := by
    rw [WithLp.ofLp_add, Pi.add_apply]
  rw [hG, hsum, intervalIntegral_apply_fin hint (a := s) (b := 1) 0, Xi_apply_zero] at hcoord
  have hint2 : ∀ σ : ℝ, (RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) 0 = -(Z σ 2) :=
    fun σ => Theta_apply_zero n (ε • h) s σ (Z σ)
  simp only [hint2] at hcoord
  rw [hcoord, intervalIntegral.integral_neg]
  ring

lemma volterra_row_one {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {ε a : ℝ} {Z : ℝ → VS}
    (hZc : Continuous Z)
    (hfix : ∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
        + RyaboginVolterra.Xi n (ε • h) s)
    {s : ℝ} (hs : s ∈ Set.Icc a 1) :
    Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3 := by
  have hΘc : Continuous (fun q : (ℝ × VS) × ℝ =>
      RyaboginVolterra.Theta n (ε • h) q.2 q.1.1 q.1.2) :=
    (contDiff_Theta n (hh.const_smul ε)).continuous
  have hmap : Continuous (fun σ : ℝ => ((σ, Z σ), s)) := by fun_prop
  have hint : Continuous (fun σ : ℝ => RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) :=
    hΘc.comp hmap
  have hcoord := congrArg (fun v : VS => v 1) (hfix s hs)
  have hG := G_apply_one n (ε • h) s (Z s)
  have hsum : ((∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
      + RyaboginVolterra.Xi n (ε • h) s) 1
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) 1
        + (RyaboginVolterra.Xi n (ε • h) s) 1 := by
    rw [WithLp.ofLp_add, Pi.add_apply]
  rw [hG, hsum, intervalIntegral_apply_fin hint (a := s) (b := 1) 1, Xi_apply_one] at hcoord
  have hint2 : ∀ σ : ℝ, (RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) 1 = -(Z σ 3) :=
    fun σ => Theta_apply_one n (ε • h) s σ (Z σ)
  simp only [hint2] at hcoord
  rw [hcoord, intervalIntegral.integral_neg]
  ring



/-! ## The coordinate functions `Z · 0`, `Z · 1` and their derivatives -/

lemma deriv_coord_zero_eq {Z : ℝ → VS} (hZc : Continuous Z) {a : ℝ}
    (hrow : ∀ s ∈ Set.Icc a 1, Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2) :
    ∀ s ∈ Set.Ioo a 1, deriv (fun u : ℝ => Z u 0) s = Z s 2 := by
  intro s hs
  have hnhds : Set.Ioo a 1 ∈ 𝓝 s := Ioo_mem_nhds hs.1 hs.2
  have hev : (fun u : ℝ => Z u 0) =ᶠ[𝓝 s]
      (fun u : ℝ => profileX 1 - ∫ σ in u..1, Z σ 2) := by
    filter_upwards [hnhds] with u hu
    exact hrow u ⟨hu.1.le, hu.2.le⟩
  rw [hev.deriv_eq]
  have hdcont : Continuous (fun σ : ℝ => Z σ 2) := by fun_prop
  have hd := (intervalIntegral.integral_hasDerivAt_left
    (hdcont.intervalIntegrable s 1) (hdcont.stronglyMeasurableAtFilter volume (𝓝 s))
    hdcont.continuousAt).const_sub (profileX 1)
  simpa using hd.deriv

lemma deriv_coord_one_eq {Z : ℝ → VS} (hZc : Continuous Z) {a : ℝ}
    (hrow : ∀ s ∈ Set.Icc a 1, Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3) :
    ∀ s ∈ Set.Ioo a 1, deriv (fun u : ℝ => Z u 1) s = Z s 3 := by
  intro s hs
  have hnhds : Set.Ioo a 1 ∈ 𝓝 s := Ioo_mem_nhds hs.1 hs.2
  have hev : (fun u : ℝ => Z u 1) =ᶠ[𝓝 s]
      (fun u : ℝ => profileX 1 - ∫ σ in u..1, Z σ 3) := by
    filter_upwards [hnhds] with u hu
    exact hrow u ⟨hu.1.le, hu.2.le⟩
  rw [hev.deriv_eq]
  have hdcont : Continuous (fun σ : ℝ => Z σ 3) := by fun_prop
  have hd := (intervalIntegral.integral_hasDerivAt_left
    (hdcont.intervalIntegrable s 1) (hdcont.stronglyMeasurableAtFilter volume (𝓝 s))
    hdcont.continuousAt).const_sub (profileX 1)
  simpa using hd.deriv

/-- The state `Z` of the (unscaled) Volterra system, written in terms of its first two
coordinates and their derivatives. -/
lemma stateOf_eq_of_volterra {Z : ℝ → VS} (hZc : Continuous Z) {a : ℝ}
    (hrow0 : ∀ s ∈ Set.Icc a 1, Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2)
    (hrow1 : ∀ s ∈ Set.Icc a 1, Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3) :
    ∀ s ∈ Set.Ioo a 1, RyaboginVolterra.stateOf (fun u => Z u 0) (fun u => Z u 1) s = Z s := by
  intro s hs
  have h0 := deriv_coord_zero_eq hZc hrow0 s hs
  have h1 := deriv_coord_one_eq hZc hrow1 s hs
  rw [RyaboginVolterra.stateOf, RyaboginVolterra.mk4, h0, h1]
  ext i
  fin_cases i <;> simp [RyaboginVolterra.mk4_apply]

end Commons.Geometry.Ulam
end

-- ===== FILE _uniq.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Interval

namespace Commons.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniqueness of the weighted Volterra fixed point** (companion of
`volterra_perturbation_exists_weighted`): on `[a,b]` the equation
`G s (Z s) = ∫ σ in s..b, Θ s σ (Z σ) + Ξ s` has at most one solution in the closed ball of
radius `r < 1` around `0`, provided the two Lipschitz hypotheses of the abstract theorem hold.
Proof: `(1 - K_G) ‖Z₁ s - Z₂ s‖ ≤ ‖Q s‖ L_Θ ∫_s^b ‖Z₁ σ - Z₂ σ‖ dσ` and Grönwall. -/
theorem volterra_fixed_unique {a b : ℝ} (hab : a < b)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Q : ℝ → E ≃L[ℝ] E}
    {K_G L_Θ : NNReal} (hKlt : (K_G : ℝ) < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hQbdd : ∃ C : ℝ, ∀ s ∈ Set.Icc a b, ‖((Q s).symm : E →L[ℝ] E)‖ ≤ C)
    (hΘcont : Continuous (fun p : ℝ × (ℝ × E) => Θ p.1 p.2.1 p.2.2))
    (hGlip : ∀ s ∈ Set.Icc a b, LipschitzOnWith K_G
      (fun z : E => z - (Q s).symm (G s z)) (Metric.closedBall (0 : E) 1))
    (hΘlip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      LipschitzOnWith L_Θ (fun z : E => Θ s σ z) (Metric.closedBall (0 : E) 1))
    {Z1 Z2 : ℝ → E}
    (h1c : ContinuousOn Z1 (Set.Icc a b)) (h1b : ∀ s ∈ Set.Icc a b, dist (Z1 s) 0 ≤ r)
    (h1 : ∀ s ∈ Set.Icc a b, G s (Z1 s) = (∫ σ in s..b, Θ s σ (Z1 σ)) + Ξ s)
    (h2c : ContinuousOn Z2 (Set.Icc a b)) (h2b : ∀ s ∈ Set.Icc a b, dist (Z2 s) 0 ≤ r)
    (h2 : ∀ s ∈ Set.Icc a b, G s (Z2 s) = (∫ σ in s..b, Θ s σ (Z2 σ)) + Ξ s) :
    ∀ s ∈ Set.Icc a b, Z1 s = Z2 s := by
  classical
  obtain ⟨C₀, hC₀⟩ := hQbdd
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hCbd : ∀ s ∈ Set.Icc a b, ‖((Q s).symm : E →L[ℝ] E)‖ ≤ C :=
    fun s hs => le_trans (hC₀ s hs) (le_max_left _ _)
  have hLnn : 0 ≤ (L_Θ : ℝ) := L_Θ.2
  have h1K : 0 < 1 - (K_G : ℝ) := by linarith
  set lam : ℝ := C * (L_Θ : ℝ) / (1 - (K_G : ℝ)) with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
  -- pass to globally continuous extensions
  set Z1e : ℝ → E := Set.IccExtend hab.le ((Set.Icc a b).domRestrict Z1) with hZ1edef
  set Z2e : ℝ → E := Set.IccExtend hab.le ((Set.Icc a b).domRestrict Z2) with hZ2edef
  have hZ1ec : Continuous Z1e := h1c.domRestrict.Icc_extend'
  have hZ2ec : Continuous Z2e := h2c.domRestrict.Icc_extend'
  have hZ1eeq : ∀ t ∈ Set.Icc a b, Z1e t = Z1 t := fun t ht =>
    Set.IccExtend_of_mem hab.le ((Set.Icc a b).domRestrict Z1) ht
  have hZ2eeq : ∀ t ∈ Set.Icc a b, Z2e t = Z2 t := fun t ht =>
    Set.IccExtend_of_mem hab.le ((Set.Icc a b).domRestrict Z2) ht
  have h1b' : ∀ s ∈ Set.Icc a b, dist (Z1e s) 0 ≤ r := fun s hs => by
    rw [hZ1eeq s hs]; exact h1b s hs
  have h2b' : ∀ s ∈ Set.Icc a b, dist (Z2e s) 0 ≤ r := fun s hs => by
    rw [hZ2eeq s hs]; exact h2b s hs
  have h1' : ∀ s ∈ Set.Icc a b, G s (Z1e s) = (∫ σ in s..b, Θ s σ (Z1e σ)) + Ξ s := by
    intro s hs
    have hint : (∫ σ in s..b, Θ s σ (Z1e σ)) = ∫ σ in s..b, Θ s σ (Z1 σ) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hσ' : σ ∈ Set.Icc a b := by
        rw [Set.uIcc_of_le hs.2] at hσ
        exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
      rw [hZ1eeq σ hσ']
    rw [hZ1eeq s hs, hint]
    exact h1 s hs
  have h2' : ∀ s ∈ Set.Icc a b, G s (Z2e s) = (∫ σ in s..b, Θ s σ (Z2e σ)) + Ξ s := by
    intro s hs
    have hint : (∫ σ in s..b, Θ s σ (Z2e σ)) = ∫ σ in s..b, Θ s σ (Z2 σ) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hσ' : σ ∈ Set.Icc a b := by
        rw [Set.uIcc_of_le hs.2] at hσ
        exact ⟨le_trans hs.1 hσ.1, hσ.2⟩
      rw [hZ2eeq σ hσ']
    rw [hZ2eeq s hs, hint]
    exact h2 s hs
  set v : ℝ → E := fun s => Z1e s - Z2e s with hvdef
  have hvc : Continuous v := hZ1ec.sub hZ2ec
  -- the pointwise Grönwall inequality
  have hbound : ∀ s ∈ Set.Icc a b, ‖v s‖ ≤ lam * (∫ σ in s..b, ‖v σ‖) := by
    intro s hs
    have hsle : s ≤ b := hs.2
    have hcontr1 : Continuous (fun σ : ℝ => Θ s σ (Z1e σ)) := by
      have hg : Continuous (fun σ : ℝ => (s, (σ, Z1e σ))) := by fun_prop
      have h := hΘcont.comp hg
      rw [show ((fun p : ℝ × (ℝ × E) => Θ p.1 p.2.1 p.2.2) ∘
          fun σ : ℝ => (s, (σ, Z1e σ))) = (fun σ : ℝ => Θ s σ (Z1e σ)) from rfl] at h
      exact h
    have hcontr2 : Continuous (fun σ : ℝ => Θ s σ (Z2e σ)) := by
      have hg : Continuous (fun σ : ℝ => (s, (σ, Z2e σ))) := by fun_prop
      have h := hΘcont.comp hg
      rw [show ((fun p : ℝ × (ℝ × E) => Θ p.1 p.2.1 p.2.2) ∘
          fun σ : ℝ => (s, (σ, Z2e σ))) = (fun σ : ℝ => Θ s σ (Z2e σ)) from rfl] at h
      exact h
    have hi1 : IntervalIntegrable (fun σ : ℝ => Θ s σ (Z1e σ)) volume s b :=
      hcontr1.intervalIntegrable s b
    have hi2 : IntervalIntegrable (fun σ : ℝ => Θ s σ (Z2e σ)) volume s b :=
      hcontr2.intervalIntegrable s b
    -- the two `(Q s).symm` identities
    have hQG1 : (Q s).symm (G s (Z1e s))
        = (Q s).symm (∫ σ in s..b, Θ s σ (Z1e σ)) + (Q s).symm (Ξ s) := by
      calc (Q s).symm (G s (Z1e s))
          = (Q s).symm ((∫ σ in s..b, Θ s σ (Z1e σ)) + Ξ s) := by rw [h1' s hs]
        _ = (Q s).symm (∫ σ in s..b, Θ s σ (Z1e σ)) + (Q s).symm (Ξ s) := map_add _ _ _
    have hQG2 : (Q s).symm (G s (Z2e s))
        = (Q s).symm (∫ σ in s..b, Θ s σ (Z2e σ)) + (Q s).symm (Ξ s) := by
      calc (Q s).symm (G s (Z2e s))
          = (Q s).symm ((∫ σ in s..b, Θ s σ (Z2e σ)) + Ξ s) := by rw [h2' s hs]
        _ = (Q s).symm (∫ σ in s..b, Θ s σ (Z2e σ)) + (Q s).symm (Ξ s) := map_add _ _ _
    have hkey : v s
        = ((Z1e s - (Q s).symm (G s (Z1e s))) - (Z2e s - (Q s).symm (G s (Z2e s))))
          + (Q s).symm ((∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ))) := by
      rw [hvdef, hQG1, hQG2]
      simp only [map_sub]
      abel
    -- membership in the unit ball
    have hmem1 : ∀ σ ∈ Set.Icc a b, Z1e σ ∈ Metric.closedBall (0 : E) 1 := by
      intro σ hσ
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (by simpa [dist_eq_norm] using h1b' σ hσ) (le_of_lt hr1)
    have hmem2 : ∀ σ ∈ Set.Icc a b, Z2e σ ∈ Metric.closedBall (0 : E) 1 := by
      intro σ hσ
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (by simpa [dist_eq_norm] using h2b' σ hσ) (le_of_lt hr1)
    -- first term
    have hFL : ‖(Z1e s - (Q s).symm (G s (Z1e s))) - (Z2e s - (Q s).symm (G s (Z2e s)))‖
        ≤ (K_G : ℝ) * ‖v s‖ := by
      have h := (hGlip s hs).dist_le_mul (Z1e s) (hmem1 s hs) (Z2e s) (hmem2 s hs)
      rw [dist_eq_norm, dist_eq_norm] at h
      simpa [hvdef] using h
    -- second term
    have hIeq : (∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ))
        = ∫ σ in s..b, (Θ s σ (Z1e σ) - Θ s σ (Z2e σ)) :=
      (intervalIntegral.integral_sub hi1 hi2).symm
    have hIntLe : ‖∫ σ in s..b, (Θ s σ (Z1e σ) - Θ s σ (Z2e σ))‖
        ≤ (L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖) := by
      have hpt : ∀ σ ∈ Set.Icc s b, ‖Θ s σ (Z1e σ) - Θ s σ (Z2e σ)‖ ≤ (L_Θ : ℝ) * ‖v σ‖ := by
        intro σ hσ
        have hσab : σ ∈ Set.Icc a b := ⟨le_trans hs.1 hσ.1, hσ.2⟩
        have h := (hΘlip s hs σ hσab).dist_le_mul (Z1e σ) (hmem1 σ hσab)
          (Z2e σ) (hmem2 σ hσab)
        rw [dist_eq_norm, dist_eq_norm] at h
        simpa [hvdef] using h
      calc ‖∫ σ in s..b, (Θ s σ (Z1e σ) - Θ s σ (Z2e σ))‖
          ≤ ∫ σ in s..b, ‖Θ s σ (Z1e σ) - Θ s σ (Z2e σ)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hsle
        _ ≤ ∫ σ in s..b, (L_Θ : ℝ) * ‖v σ‖ := by
            refine intervalIntegral.integral_mono_on (μ := volume) hsle ?_ ?_ hpt
            · exact (hcontr1.sub hcontr2).norm.intervalIntegrable s b
            · exact (continuous_const.mul hvc.norm).intervalIntegrable s b
        _ = (L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖) := intervalIntegral.integral_const_mul _ _
    have hIL : ‖(Q s).symm ((∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ)))‖
        ≤ C * ((L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖)) := by
      calc ‖(Q s).symm ((∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ)))‖
          ≤ ‖((Q s).symm : E →L[ℝ] E)‖
            * ‖(∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ))‖ :=
            ((Q s).symm : E →L[ℝ] E).le_opNorm _
        _ ≤ C * ((L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖)) := by
            refine mul_le_mul (hCbd s hs) ?_ (norm_nonneg _) hCpos.le
            rw [hIeq]
            exact hIntLe
    have hCL : C * ((L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖))
        = lam * (1 - (K_G : ℝ)) * (∫ σ in s..b, ‖v σ‖) := by
      rw [hlamdef]
      field_simp
    have hcomb : ‖v s‖ ≤ (K_G : ℝ) * ‖v s‖
        + lam * (1 - (K_G : ℝ)) * (∫ σ in s..b, ‖v σ‖) := by
      calc ‖v s‖
          ≤ ‖(Z1e s - (Q s).symm (G s (Z1e s))) - (Z2e s - (Q s).symm (G s (Z2e s)))‖
            + ‖(Q s).symm ((∫ σ in s..b, Θ s σ (Z1e σ)) - (∫ σ in s..b, Θ s σ (Z2e σ)))‖ := by
            rw [hkey]; exact norm_add_le _ _
        _ ≤ (K_G : ℝ) * ‖v s‖ + C * ((L_Θ : ℝ) * (∫ σ in s..b, ‖v σ‖)) := add_le_add hFL hIL
        _ = (K_G : ℝ) * ‖v s‖ + lam * (1 - (K_G : ℝ)) * (∫ σ in s..b, ‖v σ‖) := by
            rw [hCL]
    have hstep : (1 - (K_G : ℝ)) * ‖v s‖
        ≤ (1 - (K_G : ℝ)) * (lam * (∫ σ in s..b, ‖v σ‖)) := by
      nlinarith [hcomb]
    exact le_of_mul_le_mul_left hstep h1K
  -- Grönwall
  set g : ℝ → ℝ := fun s => ∫ σ in s..b, ‖v σ‖ with hgdef
  have hφ : Continuous (fun x : ℝ => ∫ σ in (b:ℝ)..x, ‖v σ‖) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun x σ => ‖v σ‖) (hvc.norm.comp continuous_snd) continuous_id
  have hgcont : Continuous g := by
    rw [hgdef]
    refine hφ.neg.congr (fun s => ?_)
    show -((∫ σ in (b:ℝ)..s, ‖v σ‖)) = ∫ σ in s..b, ‖v σ‖
    rw [intervalIntegral.integral_symm (a := s) (b := b)]
    simp
  have hgb : g b = 0 := by
    rw [hgdef]
    simp
  have hgnonneg : ∀ s ∈ Set.Icc a b, 0 ≤ g s := by
    intro s hs
    rw [hgdef]
    exact intervalIntegral.integral_nonneg hs.2 (fun σ _ => norm_nonneg _)
  have hgderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt g (-(‖v s‖)) s := by
    intro s hs
    have hcont : ContinuousAt (fun σ : ℝ => ‖v σ‖) s := hvc.norm.continuousAt
    exact intervalIntegral.integral_hasDerivAt_left
      (hvc.norm.intervalIntegrable s b)
      (hvc.norm.stronglyMeasurableAtFilter volume (𝓝 s)) hcont
  have hmono : MonotoneOn (fun s : ℝ => Real.exp (lam * s) * g s) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hgcont).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      have hd : DifferentiableAt ℝ g s := (hgderiv s hs).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun s : ℝ => Real.exp (lam * s)) s := by fun_prop
      exact (hd2.mul hd).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsab : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.le⟩
      have hd1 : HasDerivAt (fun s : ℝ => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s := by
        have h : HasDerivAt (fun s : ℝ => lam * s) lam s := by
          simpa using (hasDerivAt_id s).const_mul lam
        exact (Real.hasDerivAt_exp (lam * s)).comp s h
      have hd : HasDerivAt (fun s : ℝ => Real.exp (lam * s) * g s)
          (Real.exp (lam * s) * lam * g s + Real.exp (lam * s) * (-(‖v s‖))) s := by
        have h := hd1.mul (hgderiv s hs)
        have hfun : ((fun s : ℝ => Real.exp (lam * s)) * g)
            = (fun s : ℝ => Real.exp (lam * s) * g s) := by
          funext t; rfl
        rw [hfun] at h
        exact h
      rw [hd.deriv]
      have hb' : ‖v s‖ ≤ lam * g s := hbound s hsab
      have hgnn : 0 ≤ g s := hgnonneg s hsab
      have hexp : 0 < Real.exp (lam * s) := Real.exp_pos _
      nlinarith [hb', hgnn, hexp, hlam0]
  intro s hs
  have hgs : g s = 0 := by
    have hle := hmono hs (right_mem_Icc.2 hab.le) hs.2
    simp only at hle
    rw [hgb, mul_zero] at hle
    have h3 : 0 < Real.exp (lam * s) := Real.exp_pos _
    have h4 : g s ≤ 0 := by
      by_contra hneg
      push Not at hneg
      nlinarith [hle, h3, hneg]
    linarith [hgnonneg s hs, h4]
  have hb : ‖v s‖ ≤ lam * g s := hbound s hs
  rw [hgs, mul_zero] at hb
  have hv0 : v s = 0 := by
    rw [← norm_eq_zero]
    exact le_antisymm hb (norm_nonneg _)
  have hthis : Z1e s = Z2e s := sub_eq_zero.mp hv0
  rw [← hZ1eeq s hs, ← hZ2eeq s hs]
  exact hthis

end Commons.Analysis.Calculus
end

-- ===== FILE _app4.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## The perturbed data coincides with the base data on `(1 - τ, ∞)` -/

lemma support_smul_subset {n : ℕ} {τ : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ)) {ε : ℝ} (hε : ε ≠ 0) :
    Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ) := by
  intro s hs
  refine hsupp ?_
  rw [Function.mem_support] at hs ⊢
  intro h0
  exact hs (by simp [Pi.smul_apply, h0])

lemma Gn_eq_TG_of_gt {n : ℕ} {τ : ℝ} {h : ℝ → ℝ} {ε : ℝ}
    (hsupp : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {Qe : VS ≃L[ℝ] VS} {ρ s : ℝ} (hs : 1 - τ < s) (U : VS) :
    Gn n Qe ρ (ε • h) s U = TG n Qe ρ s U := by
  have hs' : s ∉ Set.Icc (1 - 2 * τ) (1 - τ) := fun hc => absurd hc.2 (not_le.mpr hs)
  have h1 : RyaboginVolterra.G n (ε • h) s (baseZ s + ρ • U) = baseG n s (baseZ s + ρ • U) :=
    G_eq_baseG_of_notMem hsupp hs' _
  simp only [Gn_eq, TG, h1]

lemma ThnEps_eq_TΘ_of_gt {n : ℕ} {τ : ℝ} {h : ℝ → ℝ} {ε : ℝ}
    (hsupp : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {Qe : VS ≃L[ℝ] VS} {ρ s σ : ℝ} (hs : 1 - τ < s) (hσ : 1 - τ < σ) (U : VS) :
    ThnEps n Qe ρ h ε s σ U = TΘ n Qe ρ s σ U := by
  have hs' : s ∉ Set.Icc (1 - 2 * τ) (1 - τ) := fun hc => absurd hc.2 (not_le.mpr hs)
  have hσ' : σ ∉ Set.Icc (1 - 2 * τ) (1 - τ) := fun hc => absurd hc.2 (not_le.mpr hσ)
  have h1 : RyaboginVolterra.Theta n (ε • h) s σ (baseZ σ + ρ • U)
      = baseΘ n s σ (baseZ σ + ρ • U) :=
    Theta_eq_baseΘ_of_notMem hsupp hs' hσ' _
  simp only [ThnEps, TΘ, h1]

lemma Xin_eq_TΞ_of_gt {n : ℕ} {τ : ℝ} {h : ℝ → ℝ} {ε : ℝ}
    (hsupp : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {Qe : VS ≃L[ℝ] VS} {ρ s : ℝ} (hs : 1 - τ < s) :
    Xin n Qe ρ (ε • h) s = TΞ n Qe ρ s := by
  have hs' : s ∉ Set.Icc (1 - 2 * τ) (1 - τ) := fun hc => absurd hc.2 (not_le.mpr hs)
  have h1 : RyaboginVolterra.Xi n (ε • h) s = baseΞ n s :=
    Xi_eq_base_of_notMem hsupp hs'
  simp only [Xin, TΞ, h1]

/-! ## The scaled solution vanishes on `[c,1]` for `1 - τ < c < 1` -/

/-- On any `[c,1]` with `1 - τ < c < 1` the perturbed scaled data coincides with the base scaled
data; by `volterra_fixed_unique` the scaled solution `Zsc` therefore coincides with the base
scaled solution `0`. -/
theorem scaled_solution_eq_zero_right {n : ℕ} {h : ℝ → ℝ} {τ : ℝ} {ε : ℝ}
    (hsupp : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {Qe : VS ≃L[ℝ] VS} {Qm : ℝ → VS ≃L[ℝ] VS} {ρ r' : ℝ} {L : NNReal} {c : ℝ}
    (hQbdd : ∃ C : ℝ, ∀ s ∈ Set.Icc c 1, ‖((Qm s).symm : VS →L[ℝ] VS)‖ ≤ C)
    (hΘcont : Continuous (fun p : ℝ × (ℝ × VS) =>
      ThnEps n Qe ρ h ε p.1 p.2.1 p.2.2))
    (hGlip : ∀ s ∈ Set.Icc c 1, LipschitzOnWith (1 / 2)
      (fun z : VS => z - (Qm s).symm (Gn n Qe ρ (ε • h) s z)) (Metric.closedBall (0 : VS) 1))
    (hΘlip : ∀ s ∈ Set.Icc c 1, ∀ σ ∈ Set.Icc c 1, LipschitzOnWith L
      (fun z : VS => ThnEps n Qe ρ h ε s σ z) (Metric.closedBall (0 : VS) 1))
    (hbase : ∀ s ∈ Set.Icc c 1,
      TG n Qe ρ s 0 = (∫ σ in s..1, TΘ n Qe ρ s σ 0) + TΞ n Qe ρ s)
    {Zsc : ℝ → VS} (hZc : ContinuousOn Zsc (Set.Icc c 1))
    (hZb : ∀ s ∈ Set.Icc c 1, dist (Zsc s) 0 ≤ r')
    (hr0 : 0 < r') (hr1 : r' < 1)
    (hZfix : ∀ s ∈ Set.Icc c 1,
      Gn n Qe ρ (ε • h) s (Zsc s)
        = (∫ σ in s..1, ThnEps n Qe ρ h ε s σ (Zsc σ)) + Xin n Qe ρ (ε • h) s)
    (hc : 1 - τ < c) (hc1 : c < 1) :
    ∀ s ∈ Set.Icc c 1, Zsc s = 0 := by
  have hzero : ∀ s ∈ Set.Icc c 1,
      Gn n Qe ρ (ε • h) s (0 : VS)
        = (∫ σ in s..1, ThnEps n Qe ρ h ε s σ (0 : VS)) + Xin n Qe ρ (ε • h) s := by
    intro s hs
    have h0 : 1 - τ < s := lt_of_lt_of_le hc hs.1
    rw [Gn_eq_TG_of_gt hsupp h0 0]
    have hint : (∫ σ in s..1, ThnEps n Qe ρ h ε s σ (0 : VS))
        = ∫ σ in s..1, TΘ n Qe ρ s σ 0 := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hσ' : 1 - τ < σ := by
        rw [Set.uIcc_of_le hs.2] at hσ
        exact lt_of_lt_of_le hc (le_trans hs.1 hσ.1)
      exact ThnEps_eq_TΘ_of_gt hsupp h0 hσ' 0
    rw [hint, Xin_eq_TΞ_of_gt hsupp h0]
    exact hbase s hs
  have huniq := Commons.Analysis.Calculus.volterra_fixed_unique (E := VS) hc1
    (G := fun s z => Gn n Qe ρ (ε • h) s z)
    (Θ := fun s σ z => ThnEps n Qe ρ h ε s σ z)
    (Ξ := fun s => Xin n Qe ρ (ε • h) s) (Q := Qm) (K_G := (1 / 2 : NNReal)) (L_Θ := L)
    (by norm_num) hr0 hr1 hQbdd hΘcont hGlip hΘlip hZc hZb hZfix
    continuousOn_const (fun s _ => by rw [dist_self]; exact hr0.le) hzero
  intro s hs
  exact huniq s hs

end Commons.Geometry.Ulam
end

-- ===== FILE _app5.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The anchor of the perturbation**: if `1 - τ < c < 1`, the perturbed Volterra solution agrees
with the base state on `[c,1]`. -/
theorem volterra_solution_eq_base_right {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {a r c : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hca : a ≤ c) (hc : 1 - τ < c) (hc1 : c < 1) {εmax : ℝ} (hεmax : 0 < εmax) :
    ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) := by
  classical
  set Qe : VS ≃L[ℝ] VS := jacEquiv n (by norm_num : (0 : ℝ) < 1) with hQe
  obtain ⟨ε, hε0, hεmax', ρ, hρ0, hρ1, L, Z, Zsc, hZc, hZbd, hZfix, hZscc, hZscbd, hZsceq,
    hZscfix, hΘlip, hGlip, _hM⟩ := honest_volterra_solution_full n hn hh ha ha1 hr0 hr1 hεmax
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hsupp' : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ) :=
    support_smul_subset (n := n) hsupp hεne
  have hsub : Set.Icc c 1 ⊆ Set.Icc a 1 := Set.Icc_subset_Icc hca le_rfl
  have hone : ∀ s ∈ Set.Icc c 1, Zsc s = 0 :=
    scaled_solution_eq_zero_right (n := n) (h := h) (τ := τ) (ε := ε) hsupp'
      (Qe := Qe) (Qm := Qref n Qe ha) (ρ := ρ) (r' := r) (L := L) (c := c)
      (by obtain ⟨C, _, hC⟩ := Qref_symm_bound n Qe ha ha1.le
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
      (continuous_ThnEps n Qe hρne hh ε)
      (fun s hs => hGlip s (hsub hs))
      (fun s hs σ hσ => hΘlip s (hsub hs) σ (hsub hσ))
      (fun s hs => Tbase_identity_jacEquiv n hn hρne ha ha1.le s (hsub hs))
      (hZscc.mono hsub) (fun s hs => hZscbd s (hsub hs)) hr0 hr1
      (fun s hs => hZscfix s (hsub hs)) hc hc1
  refine ⟨ε, hε0, hεmax', Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1), ?_, ?_, ?_, ?_⟩
  · exact continuous_IccExtend_iff.mpr hZc.domRestrict
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs]
    exact hZbd s hs
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs]
    have hint : (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ
          (Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1) σ))
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le hs.2] at hσ
      rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1)
        ⟨le_trans hs.1 hσ.1, hσ.2⟩]
    rw [hint]
    exact hZfix s hs
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) (hsub hs), hZsceq s (hsub hs),
      hone s hs, smul_zero, add_zero]

end Commons.Geometry.Ulam
end

-- ===== FILE _smooth.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- `Theta` as a `C^∞` function of `(s, (σ, z))`. -/
lemma contDiff_Theta_curried (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.Theta n h p.1 p.2.1 p.2.2) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) =>
      (((p.2.1, p.2.2), p.1) : (ℝ × VS) × ℝ)) := by fun_prop
  exact (contDiff_Theta n hh).comp hmap

/-- The `z`-derivative of the perturbed `G`-data at the (unscaled) solution is invertible.

This is the hypothesis `hG_partial_inv` of the smoothness theorem
`Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint`: the Lipschitz
property of the contraction map `PhiG` bounds the derivative of `U ↦ PhiG s U` by `1/2`, and
that derivative is `1 - iaLin ∘ D_z G`, so `iaLin ∘ D_z G = 1 - N` with `‖N‖ ≤ 1/2` is a
unit; composing with the inverse of the unit `iaLin` gives the invertibility of `D_z G`. -/
lemma isUnit_fderiv_G_of_lipschitz {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {Qe : VS ≃L[ℝ] VS} {ρ ε a : ℝ} (hρ0 : 0 < ρ) (ha : 0 < a) {s : ℝ}
    (hs : s ∈ Set.Icc a 1) {U : VS} (hU : dist U 0 < 1)
    (hlip : LipschitzOnWith (1 / 2 : NNReal) (fun U' : VS => PhiG n Qe ρ ε h ha s U')
      (Metric.closedBall (0 : VS) 1)) :
    IsUnit (fderiv ℝ (fun z : VS => G n (ε • h) s z) (baseZ s + ρ • U)) := by
  have hU' : ‖U‖ < 1 := by simpa [dist_eq_norm] using hU
  have hmem : Metric.closedBall (0 : VS) 1 ∈ 𝓝 U := by
    have hball : U ∈ Metric.ball (0 : VS) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hU'
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hball) Metric.ball_subset_closedBall
  have hbd : ‖fderiv ℝ (fun U' : VS => PhiG n Qe ρ ε h ha s U') U‖ ≤ (1 / 2 : ℝ) :=
    norm_fderiv_le_of_lipschitzOn ℝ hmem hlip
  have hder := (hasFDerivAt_PhiG n Qe hρ0 hh ha ε s U).fderiv
  set A : VS →L[ℝ] VS := (iaLin n (max s (a / 2))).toContinuousLinearMap with hA
  set B : VS →L[ℝ] VS := GnDeriv n h ε s (baseZ s + ρ • U) with hB
  have hmuldef : A * B = A ∘L B := ContinuousLinearMap.mul_def A B
  have hXbd : ‖(1 : VS →L[ℝ] VS) - A * B‖ ≤ 1 / 2 := by
    have h1 : (1 : VS →L[ℝ] VS) - A * B
        = fderiv ℝ (fun U' : VS => PhiG n Qe ρ ε h ha s U') U := by
      rw [hmuldef, hder]
      rfl
    rw [h1]
    exact hbd
  have hXunit : IsUnit (A * B) := by
    have hlt : ‖(1 : VS →L[ℝ] VS) - A * B‖ < 1 := lt_of_le_of_lt hXbd (by norm_num)
    have hu1 := isUnit_one_sub_of_norm_lt_one hlt
    rwa [show (1 : VS →L[ℝ] VS) - (1 - A * B) = A * B from by abel] at hu1
  have hAunit : IsUnit A := by
    have hu : 0 < max s (a / 2) := lt_of_lt_of_le (by linarith) (le_max_right s (a / 2))
    have heq : A = ((jacEquiv n hu).symm : VS →L[ℝ] VS) := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [hA]
      exact (jacEquiv_symm_apply n hu v).symm
    rw [heq]
    exact ⟨(jacEquiv n hu).symm.toUnit, rfl⟩
  have hBunit : IsUnit B := (IsUnit.mul_left_iff hAunit).mp hXunit
  rw [hB] at hBunit
  simpa only [GnDeriv] using hBunit

/-- **Smoothness of the perturbed Volterra solution.**  The continuous solution `Z` of the
perturbed Volterra system produced by `volterra_solution_eq_base_right` is in fact `C^∞` on
`[a,1]`, and it equals the base state on `[c,1]`. -/
theorem volterra_solution_smooth (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {a r c : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hca : a ≤ c) (hc : 1 - τ < c) (hc1 : c < 1) {εmax : ℝ} (hεmax : 0 < εmax) :
    ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      ContDiffOn ℝ ∞ Z (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s)∧
      (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc a 1, |h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  classical
  set Qe : VS ≃L[ℝ] VS := jacEquiv n (by norm_num : (0 : ℝ) < 1) with hQe
  obtain ⟨ε, hε0, hεmax', ρ, hρ0, hρ1, L, Z, Zsc, hZc, hZbd, hZfix, hZscc, hZscbd, hZsceq,
    hZscfix, hΘlip, hGlip, hM⟩ := honest_volterra_solution_full n hn hh ha ha1 hr0 hr1 hεmax
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hsupp' : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ) :=
    support_smul_subset (n := n) hsupp hεne
  have hsub : Set.Icc c 1 ⊆ Set.Icc a 1 := Set.Icc_subset_Icc hca le_rfl
  have hone : ∀ s ∈ Set.Icc c 1, Zsc s = 0 :=
    scaled_solution_eq_zero_right (n := n) (h := h) (τ := τ) (ε := ε) hsupp'
      (Qe := Qe) (Qm := Qref n Qe ha) (ρ := ρ) (r' := r) (L := L) (c := c)
      (by obtain ⟨C, _, hC⟩ := Qref_symm_bound n Qe ha ha1.le
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
      (continuous_ThnEps n Qe hρne hh ε)
      (fun s hs => hGlip s (hsub hs))
      (fun s hs σ hσ => hΘlip s (hsub hs) σ (hsub hσ))
      (fun s hs => Tbase_identity_jacEquiv n hn hρne ha ha1.le s (hsub hs))
      (hZscc.mono hsub) (fun s hs => hZscbd s (hsub hs)) hr0 hr1
      (fun s hs => hZscfix s (hsub hs)) hc hc1
  have hinv : ∀ s ∈ Set.Icc a 1, ∃ e : VS ≃L[ℝ] VS,
      fderiv ℝ (fun z : VS => RyaboginVolterra.G n (ε • h) s z) (Z s)
        = e.toContinuousLinearMap := by
    intro s hs
    have hdist : dist (Zsc s) 0 < 1 := lt_of_le_of_lt (hZscbd s hs) hr1
    rw [hZsceq s hs]
    obtain ⟨u, hu⟩ := isUnit_fderiv_G_of_lipschitz hh hρ0 ha hs hdist (hGlip s hs)
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu.symm⟩
  have hsmooth : ContDiffOn ℝ ∞ Z (Set.Icc a 1) :=
    Commons.Analysis.Calculus.contDiffOn_of_continuous_volterra_fixedPoint (E := VS) (a := a)
      (b := 1) ha1.le hZc hZfix (contDiff_G_pair n (hh.const_smul ε)).contDiffOn
      (contDiff_Theta_curried n (hh.const_smul ε)).contDiffOn
      (contDiff_Xi n (hh.const_smul ε)).contDiffOn hinv
  refine ⟨ε, hε0, hεmax', Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact continuous_IccExtend_iff.mpr hZc.domRestrict
  · refine hsmooth.congr (fun s hs => ?_)
    exact Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs]
    exact hZbd s hs
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) hs]
    have hint : (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ
          (Set.IccExtend ha1.le (fun t : Set.Icc a 1 => Z t.1) σ))
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le hs.2] at hσ
      rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1)
        ⟨le_trans hs.1 hσ.1, hσ.2⟩]
    rw [hint]
    exact hZfix s hs
  · intro s hs
    rw [Set.IccExtend_of_mem ha1.le (fun t : Set.Icc a 1 => Z t.1) (hsub hs),
      hZsceq s (hsub hs), hone s hs, smul_zero, add_zero]
  · exact hM

end Commons.Geometry.Ulam
end

-- ===== FILE _env.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- `profileX` is strictly decreasing: its derivative is negative at every `s > 0`. -/
lemma deriv_profileX_neg {s : ℝ} (hs : 0 < s) : deriv profileX s < 0 := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    have h := ((hasDerivAt_id (x := s)).pow 2).const_add 1
    simpa using h
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s :=
    hinner.sqrt (by positivity)
  have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
  have hfun : profileX = (fun t : ℝ => Real.sqrt (1 + t ^ 2))⁻¹ := by
    funext t
    simp [profileX, one_div]
  have hd : HasDerivAt profileX
      (-((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) / (Real.sqrt (1 + s ^ 2)) ^ 2) s := by
    rw [hfun]
    exact hsqrt.inv hne
  rw [hd.deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

/-- On `[a,1]` with `a > 0`, `-deriv profileX` is bounded below by a positive constant. -/
lemma exists_margin_profileX {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Set.Icc a 1, m ≤ -deriv profileX s := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := a) (b := 1)).exists_isMinOn
    ⟨a, le_rfl, ha1⟩ (continuous_deriv_profileX.neg.continuousOn)
  exact ⟨-deriv profileX x, neg_pos.mpr (deriv_profileX_neg (lt_of_lt_of_le ha hx.1)),
    fun s hs => hmin hs⟩

/-- **The master data of the perturbation.**  For `0 < τ < 1/2` and a smooth bump `h` supported
in `[1-2τ,1-τ]`, there are `ε > 0` (as small as desired), `m, r > 0` and a globally continuous
`Z`, `C^∞` on `[a,1]` (`a := (1-2τ)/2`), solving the Volterra system for the data `ε • h`, with
`‖Z - baseZ‖ ≤ r/2 ≤ m/2` on `[a,1]`, `Z = baseZ` on `[c,1]` for `c > 1-τ`, and the coordinate
functions `s ↦ Z s 0`, `s ↦ Z s 1` strictly decreasing on `[a,1]` (their derivatives are
`Z s 2`, `Z s 3`). -/
theorem volterra_master (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {c : ℝ} (hc : 1 - τ < c) (hc1 : c < 1) {εmax : ℝ} (hεmax : 0 < εmax) :
    ∃ m : ℝ, 0 < m ∧ ∃ r : ℝ, 0 < r ∧ r ≤ m ∧ r < 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      ContDiffOn ℝ ∞ Z (Set.Icc ((1 - 2 * τ) / 2) 1) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) ∧
      (∀ s ∈ Set.Ioo ((1 - 2 * τ) / 2) 1,
        deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, Z s 2 < 0) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, Z s 3 < 0) ∧
      StrictAntiOn (fun s : ℝ => Z s 0) (Set.Icc ((1 - 2 * τ) / 2) 1) ∧
      StrictAntiOn (fun s : ℝ => Z s 1) (Set.Icc ((1 - 2 * τ) / 2) 1) := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_margin_profileX (a := (1 - 2 * τ) / 2) (by linarith) (by linarith)
  set r : ℝ := min m (1 / 2) with hrdef
  have hr0 : 0 < r := lt_min hm0 (by norm_num)
  have hrm : r ≤ m := min_le_left _ _
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ha : (0:ℝ) < (1 - 2 * τ) / 2 := by linarith
  have ha1 : (1 - 2 * τ) / 2 < 1 := by linarith
  have hca : (1 - 2 * τ) / 2 ≤ c := by linarith
  obtain ⟨ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, _hM⟩ :=
    volterra_solution_smooth n hn hh hsupp ha ha1 hr0 hr1 hca hc hc1 hεmax
  have hrow0 : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1,
      Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2 :=
    fun s hs => volterra_row_zero hh hZc hZfix hs
  have hrow1 : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1,
      Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3 :=
    fun s hs => volterra_row_one hh hZc hZfix hs
  have hder0 := deriv_coord_zero_eq hZc hrow0
  have hder1 := deriv_coord_one_eq hZc hrow1
  -- negativity of the two coordinates of `Z`
  have hneg2 : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, Z s 2 < 0 := by
    intro s hsIcc
    have hbound := abs_apply_le_norm_state (Z s - baseZ s) 2
    have h2 : |Z s 2 - baseZ s 2| ≤ r / 2 := by
      refine le_trans (by simpa [Pi.sub_apply] using hbound) (hZbd s hsIcc)
    have h3 : baseZ s 2 = deriv profileX s := baseZ_apply_two s
    have h4 : m ≤ -deriv profileX s := hm s hsIcc
    have h5 : Z s 2 - baseZ s 2 ≤ r / 2 := le_trans (le_abs_self _) h2
    have h6 : deriv profileX s ≤ -m := by linarith
    rw [h3] at h5
    nlinarith [h5, h6, hrm, hm0]
  have hneg3 : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, Z s 3 < 0 := by
    intro s hsIcc
    have hbound := abs_apply_le_norm_state (Z s - baseZ s) 3
    have h2 : |Z s 3 - baseZ s 3| ≤ r / 2 := by
      refine le_trans (by simpa [Pi.sub_apply] using hbound) (hZbd s hsIcc)
    have h3 : baseZ s 3 = deriv profileX s := baseZ_apply_three s
    have h4 : m ≤ -deriv profileX s := hm s hsIcc
    have h5 : Z s 3 - baseZ s 3 ≤ r / 2 := le_trans (le_abs_self _) h2
    have h6 : deriv profileX s ≤ -m := by linarith
    rw [h3] at h5
    nlinarith [h5, h6, hrm, hm0]
  refine ⟨m, hm0, r, hr0, hrm, hr1, ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, ?_, hneg2,
    hneg3, ?_, ?_⟩
  · intro s hs
    exact ⟨hder0 s hs, hder1 s hs⟩
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4)).comp hZc).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hder0 s hs)]
      exact hneg2 s ⟨hs.1.le, hs.2.le⟩
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4)).comp hZc).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hder1 s hs)]
      exact hneg3 s ⟨hs.1.le, hs.2.le⟩

end Commons.Geometry.Ulam
end

-- ===== FILE _res.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The master data of the perturbation, on a general interval `[a,1]` with a free small
radius `r`.**  Given the margin `m` for `-deriv profileX` on `[a,1]` and `r ≤ m`, there are
`ε ∈ (0,εmax)` and a continuous `Z`, `C^∞` on `[a,1]`, solving the Volterra system for the data
`ε • h`, with `‖Z - baseZ‖ ≤ r/2`, `Z = baseZ` on `[c,1]`, `Z·2, Z·3 < 0` and the coordinate
functions `Z·0`, `Z·1` strictly antitone, with derivatives `Z·2`, `Z·3`. -/
theorem volterra_master_gen (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {a r c m εmax : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hca : a ≤ c) (hc : 1 - τ < c) (hc1 : c < 1) (hεmax : 0 < εmax)
    (hm0 : 0 < m) (hrm : r ≤ m) (hm : ∀ s ∈ Set.Icc a 1, m ≤ -deriv profileX s) :
    ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      ContDiffOn ℝ ∞ Z (Set.Icc a 1) ∧
      (∀ s ∈ Set.Icc a 1, ‖Z s - baseZ s‖ ≤ r / 2) ∧
      (∀ s ∈ Set.Icc a 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) ∧
      (∀ s ∈ Set.Ioo a 1, deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧
        deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
      (∀ s ∈ Set.Icc a 1, Z s 2 < 0) ∧
      (∀ s ∈ Set.Icc a 1, Z s 3 < 0) ∧
      StrictAntiOn (fun s : ℝ => Z s 0) (Set.Icc a 1) ∧
      StrictAntiOn (fun s : ℝ => Z s 1) (Set.Icc a 1)∧
      (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc a 1, |h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |deriv h s| ≤ M) ∧
        (∀ s ∈ Set.Icc a 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  classical
  obtain ⟨ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, hM⟩ :=
    volterra_solution_smooth n hn hh hsupp ha ha1 hr0 hr1 hca hc hc1 hεmax
  have hrow0 : ∀ s ∈ Set.Icc a 1, Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2 :=
    fun s hs => volterra_row_zero hh hZc hZfix hs
  have hrow1 : ∀ s ∈ Set.Icc a 1, Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3 :=
    fun s hs => volterra_row_one hh hZc hZfix hs
  have hder0 := deriv_coord_zero_eq hZc hrow0
  have hder1 := deriv_coord_one_eq hZc hrow1
  have hneg2 : ∀ s ∈ Set.Icc a 1, Z s 2 < 0 := by
    intro s hsIcc
    have hbound := abs_apply_le_norm_state (Z s - baseZ s) 2
    have h2 : |Z s 2 - baseZ s 2| ≤ r / 2 := by
      refine le_trans (by simpa [Pi.sub_apply] using hbound) (hZbd s hsIcc)
    have h3 : baseZ s 2 = deriv profileX s := baseZ_apply_two s
    have h4 : m ≤ -deriv profileX s := hm s hsIcc
    have h5 : Z s 2 - baseZ s 2 ≤ r / 2 := le_trans (le_abs_self _) h2
    rw [h3] at h5
    nlinarith [h5, h4, hrm, hm0]
  have hneg3 : ∀ s ∈ Set.Icc a 1, Z s 3 < 0 := by
    intro s hsIcc
    have hbound := abs_apply_le_norm_state (Z s - baseZ s) 3
    have h2 : |Z s 3 - baseZ s 3| ≤ r / 2 := by
      refine le_trans (by simpa [Pi.sub_apply] using hbound) (hZbd s hsIcc)
    have h3 : baseZ s 3 = deriv profileX s := baseZ_apply_three s
    have h4 : m ≤ -deriv profileX s := hm s hsIcc
    have h5 : Z s 3 - baseZ s 3 ≤ r / 2 := le_trans (le_abs_self _) h2
    rw [h3] at h5
    nlinarith [h5, h4, hrm, hm0]
  refine ⟨ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, ?_, hneg2, hneg3, ?_, ?_, hM⟩
  · intro s hs
    exact ⟨hder0 s hs, hder1 s hs⟩
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4)).comp hZc).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      rw [hder0 s hs]
      exact hneg2 s ⟨hs.1.le, hs.2.le⟩
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4)).comp hZc).continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      rw [hder1 s hs]
      exact hneg3 s ⟨hs.1.le, hs.2.le⟩

end Commons.Geometry.Ulam
end

-- ===== FILE _inv.lean =====

open Set Filter Function
open scoped Topology ContDiff

/-!
# The inverse of a strictly antitone `C^k` function on a closed interval

If `f : ℝ → ℝ` is `C^k` (globally) and strictly antitone on `[a,b]` with `deriv f s ≠ 0` for
`s ∈ [a,b]`, then the inverse of `f` on `[f b, f a]` is again `C^k` there, maps `[f b, f a]` into
`[a,b]`, and is a two-sided inverse.  This is the one-dimensional interval form of the inverse
function theorem needed for the "envelope" profile function of the Ulam problem.
-/

namespace Commons.Analysis.Calculus

/-- Multiplication by a nonzero constant, as a continuous linear equivalence of `ℝ`. -/
noncomputable def cleMulOfNeZero (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun := fun x => c * x
  invFun := fun x => x / c
  map_add' := by intro x y; ring
  map_smul' := by intro r x; simp only [smul_eq_mul, RingHom.id_apply]; ring
  left_inv := by intro x; field_simp
  right_inv := by intro x; field_simp
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_id.div_const c

lemma coe_cleMulOfNeZero (c : ℝ) (hc : c ≠ 0) :
    ((cleMulOfNeZero c hc : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) = c • (1 : ℝ →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext_ring ?_
  simp [cleMulOfNeZero]

/-- **The inverse of a strictly antitone `C^k` function on a closed interval is `C^k`.** -/
theorem exists_contDiffOn_invFunOn_of_strictAntiOn {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ k f) (hanti : StrictAntiOn f (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Icc a b, deriv f s ≠ 0) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ k g (Set.Icc (f b) (f a)) ∧
      (∀ t ∈ Set.Icc (f b) (f a), g t ∈ Set.Icc a b) ∧
      (∀ t ∈ Set.Icc (f b) (f a), f (g t) = t) ∧
      (∀ s ∈ Set.Icc a b, g (f s) = s) := by
  classical
  have hinj : InjOn f (Set.Icc a b) := hanti.injOn
  have hanti_le : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → f y ≤ f x := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with h | h
    · rw [h]
    · exact (hanti hx hy h).le
  have hkne : ((k : ℕ) : ℕ∞ω) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdiff : Differentiable ℝ f := hf.differentiable hkne
  -- the image of `[a,b]` is `[f b, f a]`
  have hsurj : ∀ t ∈ Set.Icc (f b) (f a), ∃ s ∈ Set.Icc a b, f s = t := by
    intro t ht
    have hmem : -t ∈ Set.Icc (-f a) (-f b) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab.le hf.continuous.neg.continuousOn hmem
    exact ⟨s, hs, neg_inj.mp (by simpa using hfs)⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ,
      ∀ t, g t = if t ∈ Set.Icc (f b) (f a) then Function.invFunOn f (Set.Icc a b) t else 0 :=
    ⟨_, fun _ => rfl⟩
  have hg_mem : ∀ t ∈ Set.Icc (f b) (f a), g t ∈ Set.Icc a b := by
    intro t ht
    rw [hgdef t, if_pos ht]
    exact Function.invFunOn_mem (hsurj t ht)
  have hg_right : ∀ t ∈ Set.Icc (f b) (f a), f (g t) = t := by
    intro t ht
    rw [hgdef t, if_pos ht]
    exact Function.invFunOn_eq (hsurj t ht)
  have hg_left : ∀ s ∈ Set.Icc a b, g (f s) = s := by
    intro s hs
    have hfs : f s ∈ Set.Icc (f b) (f a) :=
      ⟨hanti_le s hs b ⟨hab.le, le_rfl⟩ hs.2, hanti_le a ⟨le_rfl, hab.le⟩ s hs hs.1⟩
    exact hinj (hg_mem (f s) hfs) hs (hg_right (f s) hfs)
  -- `g` is antitone on `[f b, f a]`
  have hg_mono : ∀ y₁ ∈ Set.Icc (f b) (f a), ∀ y₂ ∈ Set.Icc (f b) (f a),
      y₁ ≤ y₂ → g y₂ ≤ g y₁ := by
    intro y₁ h₁ y₂ h₂ hy
    by_contra hcon
    rw [not_le] at hcon
    have h := hanti (hg_mem y₁ h₁) (hg_mem y₂ h₂) hcon
    rw [hg_right y₂ h₂, hg_right y₁ h₁] at h
    exact absurd h (not_lt.mpr hy)
  -- local `C^k` inverses
  have hlocal : ∀ s ∈ Set.Icc a b, ∃ φ : ℝ → ℝ, ContDiffAt ℝ k φ (f s) ∧ φ (f s) = s ∧
      (∀ᶠ x in 𝓝 s, φ (f x) = x) ∧ (∀ᶠ y in 𝓝 (f s), f (φ y) = y) := by
    intro s hs
    have hcs : ContDiffAt ℝ k f s := hf.contDiffAt
    have hne : deriv f s ≠ 0 := hderiv s hs
    have hfd1 : (fderiv ℝ f s) 1 = deriv f s := by
      have h1 : HasDerivAt f ((fderiv ℝ f s) 1) s :=
        hasFDerivAt_iff_hasDerivAt.mp (hdiff.differentiableAt.hasFDerivAt)
      exact h1.unique (hdiff.differentiableAt.hasDerivAt)
    have heq : ((cleMulOfNeZero (deriv f s) hne : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ)
        = fderiv ℝ f s := by
      rw [coe_cleMulOfNeZero]
      refine ContinuousLinearMap.ext_ring ?_
      rw [smul_apply, one_apply_eq_self, smul_eq_mul, mul_one, hfd1]
    have hf' : HasFDerivAt f ((cleMulOfNeZero (deriv f s) hne : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) s := by
      rw [heq]
      exact hdiff.differentiableAt.hasFDerivAt
    have hstrict : HasStrictFDerivAt f
        ((cleMulOfNeZero (deriv f s) hne : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) s :=
      hcs.hasStrictFDerivAt' hf' hkne
    refine ⟨hcs.localInverse hf' hkne, hcs.to_localInverse hf' hkne,
      hcs.localInverse_apply_image hf' hkne, ?_, ?_⟩
    · exact hstrict.eventually_left_inverse
    · exact hstrict.eventually_right_inverse
  refine ⟨g, ?_, hg_mem, hg_right, hg_left⟩
  refine contDiffOn_of_locally_contDiffOn (fun t ht => ?_)
  obtain ⟨s, hs, hfs⟩ := hsurj t ht
  obtain ⟨φ, hφcd, hφs, hφleft, hφright⟩ := hlocal s hs
  have hφright_mem : {y | f (φ y) = y} ∈ 𝓝 t := by rw [← hfs]; exact hφright
  obtain ⟨W, hWnhds, hWcd⟩ := hφcd.contDiffOn le_rfl (fun h => absurd h (by simp))
  have hWnhds' : W ∈ 𝓝 t := by rw [← hfs]; exact hWnhds
  rcases eq_or_lt_of_le hs.1 with hsa | hsa
  · -- the preimage is `a`
    obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (show {x | φ (f x) = x} ∈ 𝓝 a from by
      rw [hsa]; exact hφleft)
    set a₀ : ℝ := min (a + δ / 2) b with ha₀def
    have ha₀_gt : a < a₀ := lt_min (by linarith) hab
    have ha₀_le : a₀ ≤ b := min_le_right _ _
    have hleft : ∀ x ∈ Set.Icc a a₀, φ (f x) = x := by
      intro x hx
      refine hδ ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      have : a₀ ≤ a + δ / 2 := min_le_left _ _
      linarith [hx.2]
    have hfa₀ : f a₀ ∈ Set.Icc (f b) (f a) :=
      ⟨hanti_le a₀ ⟨ha₀_gt.le, ha₀_le⟩ b ⟨hab.le, le_rfl⟩ ha₀_le,
       hanti_le a ⟨le_rfl, hab.le⟩ a₀ ⟨ha₀_gt.le, ha₀_le⟩ ha₀_gt.le⟩
    obtain ⟨U, hUsub, hUopen, hUt⟩ := mem_nhds_iff.mp
      (Filter.inter_mem hWnhds' hφright_mem)
    have hcomem : t ∈ Set.Ioi (f a₀) := by
      rw [← hfs, ← hsa]
      exact hanti ⟨le_rfl, hab.le⟩ ⟨ha₀_gt.le, ha₀_le⟩ ha₀_gt
    refine ⟨U ∩ Set.Ioi (f a₀), hUopen.inter isOpen_Ioi, ⟨hUt, hcomem⟩, ?_⟩
    refine (hWcd.mono (fun y hy => (hUsub hy.2.1).1)).congr (fun y hy => ?_)
    have hyU : y ∈ U := hy.2.1
    have hygt : f a₀ < y := hy.2.2
    have hgy : g y ≤ g (f a₀) := hg_mono (f a₀) hfa₀ y hy.1 hygt.le
    rw [hg_left a₀ ⟨ha₀_gt.le, ha₀_le⟩] at hgy
    have hgy_mem : g y ∈ Set.Icc a a₀ := ⟨(hg_mem y hy.1).1, hgy⟩
    exact (hleft (g y) hgy_mem).symm.trans (congrArg φ (hg_right y hy.1))
  · rcases eq_or_lt_of_le hs.2 with hsb | hsb
    · -- the preimage is `b`
      obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (show {x | φ (f x) = x} ∈ 𝓝 b from by
        rw [← hsb]; exact hφleft)
      set b₀ : ℝ := max (b - δ / 2) a with hb₀def
      have hb₀_lt : b₀ < b := max_lt (by linarith) hab
      have hb₀_ge : a ≤ b₀ := le_max_right _ _
      have hleft' : ∀ x ∈ Set.Icc b₀ b, φ (f x) = x := by
        intro x hx
        refine hδ ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2])]
        have : b - δ / 2 ≤ b₀ := le_max_left _ _
        linarith [hx.1]
      have hfb₀ : f b₀ ∈ Set.Icc (f b) (f a) :=
        ⟨hanti_le b₀ ⟨hb₀_ge, hb₀_lt.le⟩ b ⟨hab.le, le_rfl⟩ hb₀_lt.le,
         hanti_le a ⟨le_rfl, hab.le⟩ b₀ ⟨hb₀_ge, hb₀_lt.le⟩ hb₀_ge⟩
      obtain ⟨U, hUsub, hUopen, hUt⟩ := mem_nhds_iff.mp
        (Filter.inter_mem hWnhds' hφright_mem)
      have hcomem : t ∈ Set.Iio (f b₀) := by
        rw [← hfs, hsb]
        exact hanti ⟨hb₀_ge, hb₀_lt.le⟩ ⟨hab.le, le_rfl⟩ hb₀_lt
      refine ⟨U ∩ Set.Iio (f b₀), hUopen.inter isOpen_Iio, ⟨hUt, hcomem⟩, ?_⟩
      refine (hWcd.mono (fun y hy => (hUsub hy.2.1).1)).congr (fun y hy => ?_)
      have hyU : y ∈ U := hy.2.1
      have hylt : y < f b₀ := hy.2.2
      have hgy : g (f b₀) ≤ g y := hg_mono y hy.1 (f b₀) hfb₀ hylt.le
      rw [hg_left b₀ ⟨hb₀_ge, hb₀_lt.le⟩] at hgy
      have hgy_mem : g y ∈ Set.Icc b₀ b := ⟨hgy, (hg_mem y hy.1).2⟩
      exact (hleft' (g y) hgy_mem).symm.trans (congrArg φ (hg_right y hy.1))
    · -- interior
      have hφ_mem : φ (f s) ∈ Set.Ioo a b := by rw [hφs]; exact ⟨hsa, hsb⟩
      have hφpre : φ ⁻¹' (Set.Ioo a b) ∈ 𝓝 t := by
        rw [← hfs]
        exact hφcd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hφ_mem)
      obtain ⟨U, hUsub, hUopen, hUt⟩ := mem_nhds_iff.mp
        (Filter.inter_mem hWnhds' (Filter.inter_mem hφpre hφright_mem))
      refine ⟨U, hUopen, hUt, ?_⟩
      refine (hWcd.mono (fun y hy => (hUsub hy.2).1)).congr (fun y hy => ?_)
      have h1 : f (φ y) = y := (hUsub hy.2).2.2
      have h2 : f (g y) = y := hg_right y hy.1
      exact hinj (hg_mem y hy.1) (Ioo_subset_Icc_self (hUsub hy.2).2.1) (by rw [h2, h1])

end Commons.Analysis.Calculus

-- ===== FILE _extend.lean =====

open Set Filter
open scoped Topology ContDiff

/-!
# Extending a `C^k` function on a closed interval to a globally `C^k` function

Given `F : ℝ → ℝ` which is `C^k` on `[a,b]`, the function `taylorExtend F k a b` below agrees with
`F` on `[a,b]` and is `C^k` on all of `ℝ`: outside the interval it is given by the Taylor
polynomials of `F` at the two endpoints.  This is the finite-order version of the Whitney
extension theorem for a closed interval.
-/

namespace Commons.Analysis.Calculus

/-- The Taylor-polynomial extension of a function to the outside of `[a,b]`. -/
noncomputable def taylorExtend (F : ℝ → ℝ) (k : ℕ) (a b : ℝ) : ℝ → ℝ :=
  fun t => if t ≤ a then taylorWithinEval F k (Set.Icc a b) a t
           else if t ≤ b then F t
           else taylorWithinEval F k (Set.Icc a b) b t

section
variable {F : ℝ → ℝ} {k : ℕ} {a b t : ℝ}

lemma taylorExtend_of_le (h : t ≤ a) :
    taylorExtend F k a b t = taylorWithinEval F k (Set.Icc a b) a t := by
  simp [taylorExtend, h]

lemma taylorExtend_of_mem (h : t ∈ Set.Icc a b) : taylorExtend F k a b t = F t := by
  rw [taylorExtend]
  by_cases h' : t ≤ a
  · rw [if_pos h']
    have : t = a := le_antisymm h' h.1
    rw [this, taylorWithinEval_self]
  · rw [if_neg h', if_pos h.2]

lemma taylorExtend_of_gt (hab : a ≤ b) (h : b < t) :
    taylorExtend F k a b t = taylorWithinEval F k (Set.Icc a b) b t := by
  rw [taylorExtend, if_neg (by intro h'; linarith), if_neg (by intro h'; linarith)]

lemma taylorExtend_eqOn_Icc : EqOn (taylorExtend F k a b) F (Set.Icc a b) :=
  fun _ ht => taylorExtend_of_mem ht

/-- The Taylor polynomial of order `k` with base point `x₀` is a polynomial in the evaluation
point, hence `C^k`. -/
lemma contDiff_taylorWithinEval (F : ℝ → ℝ) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    ContDiff ℝ k (fun t : ℝ => taylorWithinEval F k s x₀ t) := by
  have hfun : (fun t : ℝ => taylorWithinEval F k s x₀ t)
      = fun t : ℝ => ∑ j ∈ Finset.range (k + 1),
          (((j.factorial : ℕ) : ℝ)⁻¹ * (t - x₀) ^ j) * iteratedDerivWithin j F s x₀ := by
    funext t
    rw [taylor_within_apply]
    exact Finset.sum_congr rfl (fun j _ => by simp [smul_eq_mul])
  rw [hfun]
  fun_prop

end

/-- **Every `C^k` function on a closed interval `[a,b]` extends to a globally `C^k` function.** -/
theorem contDiff_taylorExtend (k : ℕ) {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ k F (Set.Icc a b)) : ContDiff ℝ k (taylorExtend F k a b) := by
  induction k generalizing F with
  | zero =>
      have hclamp : taylorExtend F 0 a b = F ∘ (fun t : ℝ => min (max t a) b) := by
        funext t
        rw [Function.comp_apply, taylorExtend]
        by_cases h1 : t ≤ a
        · rw [if_pos h1, taylor_within_zero_eval]
          congr 1
          rw [max_eq_right h1, min_eq_left hab.le]
        · rw [if_neg h1]
          by_cases h2 : t ≤ b
          · rw [if_pos h2]
            congr 1
            rw [max_eq_left (not_le.mp h1).le, min_eq_left h2]
          · rw [if_neg h2, taylor_within_zero_eval]
            congr 1
            rw [max_eq_left (not_le.mp h1).le, min_eq_right (not_le.mp h2).le]
      rw [hclamp]
      refine contDiff_zero.mpr (hF.continuousOn.comp_continuous ?_ ?_)
      · exact continuous_min.comp
          ((continuous_max.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const)
      · exact fun t => ⟨le_min (le_max_right t a) hab.le, min_le_right _ _⟩
  | succ k ih =>
      have huniq : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
      have hGcont : ContDiffOn ℝ k (derivWithin F (Set.Icc a b)) (Set.Icc a b) :=
        hF.derivWithin huniq (by norm_num)
      have hIH : ContDiff ℝ k (taylorExtend (derivWithin F (Set.Icc a b)) k a b) := ih hGcont
      have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
      have hmem_b : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
      -- the value of the extension at the two endpoints
      have hderA : HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) a) a := by
        have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) a u)
            (derivWithin F (Set.Icc a b) a) a := by
          have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := a) (x := a) (s := Set.Icc a b) F k
          rwa [taylorWithinEval_self] at h1
        have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) a) (Set.Iio a) a :=
          (hP.hasDerivWithinAt.mono (subset_univ _)).congr
            (fun y hy => (taylorExtend_of_le hy.le)) (by rw [taylorExtend_of_le le_rfl])
        have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) a) (Set.Icc a b) a := by
          have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) a :=
            (hF.differentiableOn (by norm_num)) a hmem_a
          refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_a])
          rw [taylorExtend_of_mem hy]
        have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) a) (Set.Iio a ∪ Set.Icc a b) a := hl.union hr
        have hset : Set.Iio a ∪ Set.Icc a b = Set.Iic b := by
          ext y
          simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact le_of_lt (lt_trans h hab)
            · exact h2
          · intro hy
            rcases lt_or_ge y a with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, hy⟩
        rw [hset] at hunion
        exact hunion.hasDerivAt (Iic_mem_nhds (by linarith))
      have hderB : HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) b) b := by
        have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) b u)
            (derivWithin F (Set.Icc a b) b) b := by
          have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := b) (x := b) (s := Set.Icc a b) F k
          rwa [taylorWithinEval_self] at h1
        have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) b) (Set.Ioi b) b :=
          (hP.hasDerivWithinAt.mono (subset_univ _)).congr
            (fun y hy => (taylorExtend_of_gt hab.le hy)) (by rw [taylorExtend_of_mem hmem_b, taylorWithinEval_self])
        have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) b) (Set.Icc a b) b := by
          have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) b :=
            (hF.differentiableOn (by norm_num)) b hmem_b
          refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_b])
          rw [taylorExtend_of_mem hy]
        have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
            (derivWithin F (Set.Icc a b) b) (Set.Icc a b ∪ Set.Ioi b) b := hl.union hr
        have hset : Set.Icc a b ∪ Set.Ioi b = Set.Ici a := by
          ext y
          simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ici]
          constructor
          · rintro (⟨h1, _⟩ | h)
            · exact h1
            · exact le_trans hab.le h.le
          · intro hy
            rcases lt_or_ge y b with h' | h'
            · exact Or.inl ⟨hy, h'.le⟩
            · rcases eq_or_lt_of_le h' with heq | hlt
              · exact Or.inl ⟨hy, heq ▸ le_rfl⟩
              · exact Or.inr hlt
        rw [hset] at hunion
        exact hunion.hasDerivAt (Ici_mem_nhds (by linarith))
      have hderiv : deriv (taylorExtend F (k + 1) a b)
          = taylorExtend (derivWithin F (Set.Icc a b)) k a b := by
        funext t
        rcases lt_trichotomy t a with h | h | h
        · have hev : taylorExtend F (k + 1) a b
              =ᶠ[𝓝 t] (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) a u) := by
            filter_upwards [isOpen_Iio.mem_nhds h] with u hu
            exact taylorExtend_of_le hu.le
          rw [hev.deriv_eq,
            (hasDerivAt_taylorWithinEval_succ (x₀ := a) (x := t) (s := Set.Icc a b) F k).deriv,
            taylorExtend_of_le h.le]
        · rw [h, hderA.deriv, taylorExtend_of_mem hmem_a]
        · rcases lt_trichotomy t b with h2 | h2 | h2
          · have hev : taylorExtend F (k + 1) a b =ᶠ[𝓝 t] F := by
              filter_upwards [isOpen_Ioo.mem_nhds ⟨h, h2⟩] with u hu
              exact taylorExtend_of_mem ⟨hu.1.le, hu.2.le⟩
            rw [hev.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds h h2),
              taylorExtend_of_mem ⟨h.le, h2.le⟩]
          · rw [h2, hderB.deriv, taylorExtend_of_mem hmem_b]
          · have hev : taylorExtend F (k + 1) a b
                =ᶠ[𝓝 t] (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) b u) := by
              filter_upwards [isOpen_Ioi.mem_nhds h2] with u hu
              exact taylorExtend_of_gt hab.le hu
            rw [hev.deriv_eq,
              (hasDerivAt_taylorWithinEval_succ (x₀ := b) (x := t) (s := Set.Icc a b) F k).deriv,
              taylorExtend_of_gt hab.le h2]
      have hdiff : Differentiable ℝ (taylorExtend F (k + 1) a b) := by
        intro x
        rcases lt_trichotomy x a with hx | hx | hx
        · refine ((contDiff_taylorWithinEval F (k + 1) (Set.Icc a b) a).differentiable
            (by simp)).differentiableAt.congr_of_eventuallyEq ?_
          filter_upwards [isOpen_Iio.mem_nhds hx] with u hu
          exact taylorExtend_of_le hu.le
        · rw [hx]
          exact hderA.differentiableAt
        · rcases lt_trichotomy x b with hx2 | hx2 | hx2
          · have hcd : ContDiffAt ℝ ((k + 1 : ℕ) : ℕ∞ω) F x :=
              (contDiffWithinAt_iff_contDiffAt (Icc_mem_nhds hx hx2)).mp (hF x ⟨hx.le, hx2.le⟩)
            refine (hcd.differentiableAt (by simp)).congr_of_eventuallyEq ?_
            filter_upwards [isOpen_Ioo.mem_nhds ⟨hx, hx2⟩] with u hu
            exact taylorExtend_of_mem ⟨hu.1.le, hu.2.le⟩
          · rw [hx2]
            exact hderB.differentiableAt
          · refine ((contDiff_taylorWithinEval F (k + 1) (Set.Icc a b) b).differentiable
              (by simp)).differentiableAt.congr_of_eventuallyEq ?_
            filter_upwards [isOpen_Ioi.mem_nhds hx2] with u hu
            exact taylorExtend_of_gt hab.le hu
      have hcast : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; rfl
      rw [hcast, contDiff_succ_iff_deriv]
      exact ⟨hdiff, fun hω => absurd hω (by simp), by rw [hderiv]; exact hIH⟩

namespace Commons.Analysis.Calculus

/-- The derivative of the Taylor extension at the LEFT endpoint is the one-sided derivative. -/
lemma hasDerivAt_taylorExtend_left {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) a) a := by
  have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) a u)
      (derivWithin F (Set.Icc a b) a) a := by
    have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := a) (x := a) (s := Set.Icc a b) F k
    rwa [taylorWithinEval_self] at h1
  have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Iio a) a :=
    (hP.hasDerivWithinAt.mono (subset_univ _)).congr
      (fun y hy => (taylorExtend_of_le hy.le)) (by rw [taylorExtend_of_le le_rfl])
  have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Icc a b) a := by
    have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) a :=
      (hF.differentiableOn (by norm_num)) a hmem_a
    refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_a])
    rw [taylorExtend_of_mem hy]
  have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Iio a ∪ Set.Icc a b) a := hl.union hr
  have hset : Set.Iio a ∪ Set.Icc a b = Set.Iic b := by
    ext y
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact le_of_lt (lt_trans h hab)
      · exact h2
    · intro hy
      rcases lt_or_ge y a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hy⟩
  rw [hset] at hunion
  exact hunion.hasDerivAt (Iic_mem_nhds (by linarith))

/-- The derivative of the Taylor extension at the RIGHT endpoint is the one-sided derivative. -/
lemma hasDerivAt_taylorExtend_right {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) b) b := by
  have hmem_b : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) b u)
      (derivWithin F (Set.Icc a b) b) b := by
    have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := b) (x := b) (s := Set.Icc a b) F k
    rwa [taylorWithinEval_self] at h1
  have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Ioi b) b :=
    (hP.hasDerivWithinAt.mono (subset_univ _)).congr
      (fun y hy => (taylorExtend_of_gt hab.le hy))
      (by rw [taylorExtend_of_mem hmem_b, taylorWithinEval_self])
  have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Icc a b) b := by
    have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) b :=
      (hF.differentiableOn (by norm_num)) b hmem_b
    refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_b])
    rw [taylorExtend_of_mem hy]
  have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Icc a b ∪ Set.Ioi b) b := hl.union hr
  have hset : Set.Icc a b ∪ Set.Ioi b = Set.Ici a := by
    ext y
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact le_trans hab.le h.le
    · intro hy
      rcases lt_or_ge y b with h' | h'
      · exact Or.inl ⟨hy, h'.le⟩
      · rcases eq_or_lt_of_le h' with heq | hlt
        · exact Or.inl ⟨hy, heq ▸ le_rfl⟩
        · exact Or.inr hlt
  rw [hset] at hunion
  exact hunion.hasDerivAt (Ici_mem_nhds (by linarith))

lemma deriv_taylorExtend_left {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    deriv (taylorExtend F (k + 1) a b) a = derivWithin F (Set.Icc a b) a :=
  (hasDerivAt_taylorExtend_left hab hF).deriv

lemma deriv_taylorExtend_right {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    deriv (taylorExtend F (k + 1) a b) b = derivWithin F (Set.Icc a b) b :=
  (hasDerivAt_taylorExtend_right hab hF).deriv

end Commons.Analysis.Calculus
end Commons.Analysis.Calculus

-- ===== FILE _endpt.lean =====

open Set Filter
open scoped Topology ContDiff

namespace Commons.Analysis.Calculus

/-- The derivative of the Taylor extension at the LEFT endpoint is the one-sided derivative. -/
lemma hasDerivAt_taylorExtend_left {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) a) a := by
  have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) a u)
      (derivWithin F (Set.Icc a b) a) a := by
    have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := a) (x := a) (s := Set.Icc a b) F k
    rwa [taylorWithinEval_self] at h1
  have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Iio a) a :=
    (hP.hasDerivWithinAt.mono (subset_univ _)).congr
      (fun y hy => (taylorExtend_of_le hy.le)) (by rw [taylorExtend_of_le le_rfl])
  have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Icc a b) a := by
    have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) a :=
      (hF.differentiableOn (by norm_num)) a hmem_a
    refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_a])
    rw [taylorExtend_of_mem hy]
  have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) a) (Set.Iio a ∪ Set.Icc a b) a := hl.union hr
  have hset : Set.Iio a ∪ Set.Icc a b = Set.Iic b := by
    ext y
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact le_of_lt (lt_trans h hab)
      · exact h2
    · intro hy
      rcases lt_or_ge y a with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hy⟩
  rw [hset] at hunion
  exact hunion.hasDerivAt (Iic_mem_nhds (by linarith))

/-- The derivative of the Taylor extension at the RIGHT endpoint is the one-sided derivative. -/
lemma hasDerivAt_taylorExtend_right {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    HasDerivAt (taylorExtend F (k + 1) a b) (derivWithin F (Set.Icc a b) b) b := by
  have hmem_b : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hP : HasDerivAt (fun u : ℝ => taylorWithinEval F (k + 1) (Set.Icc a b) b u)
      (derivWithin F (Set.Icc a b) b) b := by
    have h1 := hasDerivAt_taylorWithinEval_succ (x₀ := b) (x := b) (s := Set.Icc a b) F k
    rwa [taylorWithinEval_self] at h1
  have hr : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Ioi b) b :=
    (hP.hasDerivWithinAt.mono (subset_univ _)).congr
      (fun y hy => (taylorExtend_of_gt hab.le hy))
      (by rw [taylorExtend_of_mem hmem_b, taylorWithinEval_self])
  have hl : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Icc a b) b := by
    have hFd : DifferentiableWithinAt ℝ F (Set.Icc a b) b :=
      (hF.differentiableOn (by norm_num)) b hmem_b
    refine (hFd.hasDerivWithinAt).congr (fun y hy => ?_) (by rw [taylorExtend_of_mem hmem_b])
    rw [taylorExtend_of_mem hy]
  have hunion : HasDerivWithinAt (taylorExtend F (k + 1) a b)
      (derivWithin F (Set.Icc a b) b) (Set.Icc a b ∪ Set.Ioi b) b := hl.union hr
  have hset : Set.Icc a b ∪ Set.Ioi b = Set.Ici a := by
    ext y
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact le_trans hab.le h.le
    · intro hy
      rcases lt_or_ge y b with h' | h'
      · exact Or.inl ⟨hy, h'.le⟩
      · rcases eq_or_lt_of_le h' with heq | hlt
        · exact Or.inl ⟨hy, heq ▸ le_rfl⟩
        · exact Or.inr hlt
  rw [hset] at hunion
  exact hunion.hasDerivAt (Ici_mem_nhds (by linarith))

lemma deriv_taylorExtend_left {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    deriv (taylorExtend F (k + 1) a b) a = derivWithin F (Set.Icc a b) a :=
  (hasDerivAt_taylorExtend_left hab hF).deriv

lemma deriv_taylorExtend_right {k : ℕ} {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (k + 1) F (Set.Icc a b)) :
    deriv (taylorExtend F (k + 1) a b) b = derivWithin F (Set.Icc a b) b :=
  (hasDerivAt_taylorExtend_right hab hF).deriv

end Commons.Analysis.Calculus

-- ===== FILE _sigma.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The primitive representation of a coordinate of the Volterra solution: from the row identities,
the coordinates `0` and `1` of the solution are given by `profileX 1 - ∫ σ in s..1, Z σ i`. -/
noncomputable def statePrim (Z : ℝ → VS) (i : Fin 4) (s : ℝ) : ℝ :=
  profileX 1 - ∫ σ in s..1, Z σ i

@[simp] lemma statePrim_apply (Z : ℝ → VS) (i : Fin 4) (s : ℝ) :
    statePrim Z i s = profileX 1 - ∫ σ in s..1, Z σ i := rfl

/-- The primitive representation of a coordinate is differentiable with the corresponding
coordinate of the state as derivative. -/
lemma hasDerivAt_statePrim {Z : ℝ → VS} {i : Fin 4}
    (hcont : Continuous (fun σ : ℝ => Z σ i)) (s : ℝ) :
    HasDerivAt (statePrim Z i) (Z s i) s := by
  have hd : HasDerivAt (fun u : ℝ => ∫ x in u..(1 : ℝ), Z x i) (-(Z s i)) s :=
    intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable s 1)
      (hcont.stronglyMeasurableAtFilter volume (𝓝 s)) hcont.continuousAt
  have h2 : HasDerivAt (fun u : ℝ => profileX 1 - ∫ x in u..(1 : ℝ), Z x i) (Z s i) s := by
    have hsub := hd.const_sub (profileX 1)
    rw [neg_neg] at hsub
    exact hsub
  exact h2

lemma deriv_statePrim {Z : ℝ → VS} {i : Fin 4} (hcont : Continuous (fun σ : ℝ => Z σ i))
    (s : ℝ) : deriv (statePrim Z i) s = Z s i := (hasDerivAt_statePrim hcont s).deriv

/-- The primitive representation of a coordinate is globally continuous. -/
lemma continuous_statePrim {Z : ℝ → VS} {i : Fin 4} (hcont : Continuous (fun σ : ℝ => Z σ i)) :
    Continuous (statePrim Z i) := by
  have h1 : Continuous (fun b : ℝ => ∫ x in (1 : ℝ)..b, Z x i) :=
    intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 1
  have h2 : Continuous (fun b : ℝ => ∫ x in b..(1 : ℝ), Z x i) := by
    have hfun : (fun b : ℝ => ∫ x in b..(1 : ℝ), Z x i)
        = fun b : ℝ => -(∫ x in (1 : ℝ)..b, Z x i) := by
      funext b
      rw [intervalIntegral.integral_symm]
    rw [hfun]
    exact h1.neg
  have h3 : Continuous (fun b : ℝ => profileX 1 - ∫ x in b..(1 : ℝ), Z x i) :=
    (continuous_const.sub h2)
  exact h3

/-- Coordinate smoothness of a `C^k` state. -/
lemma contDiffOn_state_coord {Z : ℝ → VS} {K : ℕ} {a b : ℝ} {i : Fin 4}
    (hZ : ContDiffOn ℝ K Z (Set.Icc a b)) : ContDiffOn ℝ K (fun s : ℝ => Z s i) (Set.Icc a b) := by
  have hcl : ContDiff ℝ K (fun v : VS => v i) := by fun_prop
  have h := hcl.comp_contDiffOn hZ
  convert h using 1
  · funext s
    rfl

/-- **From the master data to the two global coordinate functions and the envelope inverses.**

With `a := (1-2τ)/2`, the coordinates `s ↦ Z s 0` and `s ↦ Z s 1` of the Volterra solution are
extended to globally `C^{n+2}` functions `X`, `Y` agreeing with them on `[a,1]` (via the primitive
representations `statePrim Z 2`, `statePrim Z 3`), and the strictly antitone functions `Y` and `X`
are inverted on `[profileX 1, Y a]` resp. `[X a, profileX 1]`, the inverses being `C^{n+2}`. -/
theorem envelope_inverse (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {c : ℝ} (hc : 1 - τ < c) (hc1 : c < 1) {εmax : ℝ} (hεmax : 0 < εmax) :
    ∃ ε : ℝ, 0 < ε ∧ ε < εmax ∧ ∃ Z : ℝ → VS, Continuous Z ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) ∧
      ∃ X Y : ℝ → ℝ, ContDiff ℝ (n + 2) X ∧ ContDiff ℝ (n + 2) Y ∧
        (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, X s = Z s 0 ∧ Y s = Z s 1) ∧
        (∀ s ∈ Set.Ioo ((1 - 2 * τ) / 2) 1, deriv X s = Z s 2 ∧ deriv Y s = Z s 3) ∧
        StrictAntiOn X (Set.Icc ((1 - 2 * τ) / 2) 1) ∧
        StrictAntiOn Y (Set.Icc ((1 - 2 * τ) / 2) 1) ∧
        ∃ σ : ℝ → ℝ, ContDiffOn ℝ (n + 2) σ
            (Set.Icc (profileX 1) (Y ((1 - 2 * τ) / 2))) ∧
          (∀ t ∈ Set.Icc (profileX 1) (Y ((1 - 2 * τ) / 2)), σ t ∈ Set.Icc ((1 - 2 * τ) / 2) 1) ∧
          (∀ t ∈ Set.Icc (profileX 1) (Y ((1 - 2 * τ) / 2)), Y (σ t) = t) ∧
          (∀ s ∈ Set.Icc ((1 - 2 * τ) / 2) 1, σ (Y s) = s) := by
  classical
  set a : ℝ := (1 - 2 * τ) / 2 with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  have ha1 : a < 1 := by rw [hadef]; linarith
  obtain ⟨m, hm0, r, hr0, hrm, hr1, ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, hder,
    hneg2, hneg3, hXanti, hYanti⟩ :=
    volterra_master n hn hτ0 hτsmall hh hsupp hc hc1 hεmax
  have hrow0 : ∀ s ∈ Set.Icc a 1, Z s 0 = profileX 1 - ∫ σ in s..1, Z σ 2 :=
    fun s hs => volterra_row_zero (a := a) hh hZc hZfix hs
  have hrow1 : ∀ s ∈ Set.Icc a 1, Z s 1 = profileX 1 - ∫ σ in s..1, Z σ 3 :=
    fun s hs => volterra_row_one (a := a) hh hZc hZfix hs
  -- the global coordinate functions
  have hZ2c : Continuous (fun σ : ℝ => Z σ 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4)).comp hZc
  have hZ3c : Continuous (fun σ : ℝ => Z σ 3) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4)).comp hZc
  have hZsm0 : ContDiffOn ℝ (n + 2) (fun s : ℝ => Z s 0) (Set.Icc a 1) :=
    contDiffOn_state_coord (i := 0) (hZsm.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 2)))))
  have hZsm1 : ContDiffOn ℝ (n + 2) (fun s : ℝ => Z s 1) (Set.Icc a 1) :=
    contDiffOn_state_coord (i := 1) (hZsm.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 2)))))
  have hEq2 : ∀ s ∈ Set.Icc a 1, statePrim Z 2 s = Z s 0 := by
    intro s hs
    simp only [statePrim_apply]
    rw [← hrow0 s hs]
  have hEq3 : ∀ s ∈ Set.Icc a 1, statePrim Z 3 s = Z s 1 := by
    intro s hs
    simp only [statePrim_apply]
    rw [← hrow1 s hs]
  have hprim2 : ContDiffOn ℝ (n + 2) (statePrim Z 2) (Set.Icc a 1) :=
    hZsm0.congr (fun s hs => hEq2 s hs)
  have hprim3 : ContDiffOn ℝ (n + 2) (statePrim Z 3) (Set.Icc a 1) :=
    hZsm1.congr (fun s hs => hEq3 s hs)
  -- the global extensions
  set X : ℝ → ℝ := Commons.Analysis.Calculus.taylorExtend (statePrim Z 2) (n + 2) a 1 with hXdef
  set Y : ℝ → ℝ := Commons.Analysis.Calculus.taylorExtend (statePrim Z 3) (n + 2) a 1 with hYdef
  have hXsm : ContDiff ℝ (n + 2) X := Commons.Analysis.Calculus.contDiff_taylorExtend (n + 2) ha1 hprim2
  have hYsm : ContDiff ℝ (n + 2) Y := Commons.Analysis.Calculus.contDiff_taylorExtend (n + 2) ha1 hprim3
  have hXY : ∀ s ∈ Set.Icc a 1, X s = Z s 0 ∧ Y s = Z s 1 := by
    intro s hs
    constructor
    · rw [hXdef, Commons.Analysis.Calculus.taylorExtend_of_mem hs]
      exact hEq2 s hs
    · rw [hYdef, Commons.Analysis.Calculus.taylorExtend_of_mem hs]
      exact hEq3 s hs
  have hderX : ∀ s ∈ Set.Ioo a 1, deriv X s = Z s 2 := by
    intro s hs
    have hnhds : Set.Icc a 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : X =ᶠ[𝓝 s] statePrim Z 2 := by
      filter_upwards [hnhds] with u hu
      rw [hXdef, Commons.Analysis.Calculus.taylorExtend_of_mem hu]
    rw [hev.deriv_eq, deriv_statePrim hZ2c s]
  have hderY : ∀ s ∈ Set.Ioo a 1, deriv Y s = Z s 3 := by
    intro s hs
    have hnhds : Set.Icc a 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : Y =ᶠ[𝓝 s] statePrim Z 3 := by
      filter_upwards [hnhds] with u hu
      rw [hYdef, Commons.Analysis.Calculus.taylorExtend_of_mem hu]
    rw [hev.deriv_eq, deriv_statePrim hZ3c s]
  have hXa : X a = Z a 0 := (hXY a ⟨le_rfl, ha1.le⟩).1
  have hYa : Y a = Z a 1 := (hXY a ⟨le_rfl, ha1.le⟩).2
  have hX1 : X 1 = profileX 1 := by
    rw [(hXY 1 ⟨ha1.le, le_rfl⟩).1, hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_zero]
  have hY1 : Y 1 = profileX 1 := by
    rw [(hXY 1 ⟨ha1.le, le_rfl⟩).2, hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_one]
  -- strict antitonicity of the global extensions
  have hXanti' : StrictAntiOn X (Set.Icc a 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hXsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderX s hs]
    exact hneg2 s ⟨hs.1.le, hs.2.le⟩
  have hYanti' : StrictAntiOn Y (Set.Icc a 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hYsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderY s hs]
    exact hneg3 s ⟨hs.1.le, hs.2.le⟩
  -- the derivative of `Y` does not vanish on the closed interval
  have hYd : ∀ s ∈ Set.Icc a 1, deriv Y s ≠ 0 := by
    intro s hs
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc a 1) s :=
      uniqueDiffOn_Icc ha1 s hs
    have hwithin_a : derivWithin (statePrim Z 3) (Set.Icc a 1) a = Z a 3 :=
      (hasDerivAt_statePrim hZ3c a).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc ha1 a ⟨le_rfl, ha1.le⟩)
    have hwithin_1 : derivWithin (statePrim Z 3) (Set.Icc a 1) 1 = Z 1 3 :=
      (hasDerivAt_statePrim hZ3c 1).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc ha1 1 ⟨ha1.le, le_rfl⟩)
    rcases eq_or_lt_of_le hs.1 with hsa | hsa
    · rw [hYdef, ← hsa, Commons.Analysis.Calculus.deriv_taylorExtend_left ha1 hprim3, hwithin_a]
      exact ne_of_lt (hneg3 a ⟨le_rfl, ha1.le⟩)
    · rcases eq_or_lt_of_le hs.2 with hsb | hsb
      · rw [hYdef, hsb, Commons.Analysis.Calculus.deriv_taylorExtend_right ha1 hprim3, hwithin_1,
          hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_three]
        exact ne_of_lt (deriv_profileX_neg (by norm_num))
      · rw [hderY s ⟨hsa, hsb⟩]
        exact ne_of_lt (hneg3 s ⟨hsa.le, hsb.le⟩)
  refine ⟨ε, hε0, hεmax', Z, hZc, hZfix, hZb, X, Y, hXsm, hYsm, hXY, ?_, hXanti', hYanti', ?_⟩
  · intro s hs
    exact ⟨hderX s hs, hderY s hs⟩
  · obtain ⟨σ, hσsm, hσmem, hσright, hσleft⟩ :=
      Commons.Analysis.Calculus.exists_contDiffOn_invFunOn_of_strictAntiOn (k := n + 2) (by omega) ha1 hYsm hYanti' hYd
    refine ⟨σ, ?_, ?_, ?_, hσleft⟩
    · rw [← hY1]
      exact hσsm
    · rw [← hY1]
      exact hσmem
    · rw [← hY1]
      exact hσright

end Commons.Geometry.Ulam
end

-- ===== FILE _glue.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise Interval
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Commons.Analysis.Calculus

/-!
## Smooth gluing tools

Two reusable tools:

* `ContDiff.mul_of_contDiffOn_isOpen`: the product of a globally `C^k` function with a function
  that is only `C^k` on an open set containing the (topological) support is globally `C^k`.
* `smoothGlue`: an explicit `C^∞` "flat bump" built from `Real.smoothTransition`, equal to `1`
  on a closed interval and to `0` outside a slightly larger one.
-/

/-- Multiplication by a globally smooth function preserves smoothness of a function that is
smooth on an open set containing the support of the multiplier. -/
lemma ContDiff.mul_of_contDiffOn_isOpen {K : ℕ∞} {χ W : ℝ → ℝ} {U : Set ℝ}
    (hχ : ContDiff ℝ K χ) (hW : ContDiffOn ℝ K W U) (hU : IsOpen U) (hsub : tsupport χ ⊆ U) :
    ContDiff ℝ K (fun t : ℝ => χ t * W t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t ∈ tsupport χ
  · have hWt : ContDiffAt ℝ K W t := hW.contDiffAt (hU.mem_nhds (hsub ht))
    exact hχ.contDiffAt.mul hWt
  · have hmem : (tsupport χ)ᶜ ∈ 𝓝 t :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds ht
    have heq : (fun s : ℝ => χ s * W s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with s hs
      have h0 : χ s = 0 := by
        by_contra hc
        exact hs (subset_tsupport χ (Function.mem_support.mpr hc))
      simp [h0]
    exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq heq

/-- The explicit `C^∞` step function of `Real.smoothTransition`: `0` on `(-∞,α]`, `1` on `[β,∞)`. -/
def smoothStep (α β : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t - α) / (β - α))

lemma contDiff_smoothStep (α β : ℝ) : ContDiff ℝ ∞ (smoothStep α β) := by
  unfold smoothStep
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma smoothStep_of_le {α β t : ℝ} (hαβ : α < β) (h : t ≤ α) : smoothStep α β t = 0 := by
  unfold smoothStep
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

lemma smoothStep_of_le' {α β t : ℝ} (hαβ : α < β) (h : β ≤ t) : smoothStep α β t = 1 := by
  unfold smoothStep
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma smoothStep_nonneg (α β t : ℝ) : 0 ≤ smoothStep α β t := Real.smoothTransition.nonneg _

lemma smoothStep_le_one (α β t : ℝ) : smoothStep α β t ≤ 1 := Real.smoothTransition.le_one _

/-- A `C^∞` flat bump equal to `1` on `[a,b]` and to `0` outside `(α,β)`, where `α < a ≤ b < β`. -/
def smoothGlue (α a b β : ℝ) : ℝ → ℝ := fun t => smoothStep α a t * (1 - smoothStep b β t)

lemma contDiff_smoothGlue (α a b β : ℝ) : ContDiff ℝ ∞ (smoothGlue α a b β) :=
  (contDiff_smoothStep α a).mul
    ((contDiff_const (c := (1:ℝ))).sub (contDiff_smoothStep b β))

lemma smoothGlue_eq_one {α a b β : ℝ} (ha : α < a) (hab : a ≤ b) (hb : b < β) {t : ℝ}
    (ht : t ∈ Set.Icc a b) : smoothGlue α a b β t = 1 := by
  have h1 : smoothStep α a t = 1 := smoothStep_of_le' ha ht.1
  have h2 : smoothStep b β t = 0 := smoothStep_of_le hb ht.2
  simp [smoothGlue, h1, h2]

lemma smoothGlue_eq_zero_left {α a b β : ℝ} (ha : α < a) {t : ℝ} (ht : t ≤ α) :
    smoothGlue α a b β t = 0 := by
  have h1 : smoothStep α a t = 0 := smoothStep_of_le ha ht
  simp [smoothGlue, h1]

lemma smoothGlue_eq_zero_right {α a b β : ℝ} (hb : b < β) {t : ℝ} (ht : β ≤ t) :
    smoothGlue α a b β t = 0 := by
  have h1 : smoothStep b β t = 1 := smoothStep_of_le' hb ht
  simp [smoothGlue, h1]

lemma tsupport_smoothGlue_subset {α a b β : ℝ} (ha : α < a) (hb : b < β) :
    tsupport (smoothGlue α a b β) ⊆ Set.Icc α β := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  simp only [Function.mem_support] at ht
  by_contra hcon
  simp only [Set.mem_Icc, not_and_or, not_le] at hcon
  rcases hcon with h | h
  · rw [smoothGlue_eq_zero_left ha (le_of_lt h)] at ht
    exact ht rfl
  · rw [smoothGlue_eq_zero_right hb (le_of_lt h)] at ht
    exact ht rfl

end Commons.Analysis.Calculus
end

-- ===== FILE _glob.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Coordinate smoothness of a `C^∞` state. -/
lemma contDiffOn_state_coord_inf {Z : ℝ → VS} {a b : ℝ} {i : Fin 4}
    (hZ : ContDiffOn ℝ ∞ Z (Set.Icc a b)) :
    ContDiffOn ℝ ∞ (fun s : ℝ => Z s i) (Set.Icc a b) := by
  have hcl : ContDiff ℝ ∞ (fun v : VS => v i) := by fun_prop
  exact hcl.comp_contDiffOn hZ

/-- **The perturbation data, first layer.**  For `0 < τ`, `2τ < 1` and a smooth bump `h`
supported in `[1-2τ,1-τ]` vanishing near `1-2τ` from the right, we produce a small `ε > 0`, a
Volterra solution `Z` on `[a₀,1]` (`a₀ := (1-2τ)/4`) which is `C^∞` there, `≤ r/2`-close to the base
solution, equal to it on `[c,1]` (`c > 1-τ`), and globally `C^∞` functions `X`, `Y` agreeing with
the first two coordinates of `Z` on `[a',1]` (`a' := 3(1-2τ)/8`) with the derivatives given by the
last two coordinates. -/
theorem perturbation_data (n : ℕ) (hn : 2 ≤ n) {τ : ℝ} (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hflat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0)
    {c : ℝ} (hc : 1 - τ < c) (hc1 : c < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < (1 - 2 * τ) / 8 ∧
      ∃ Z : ℝ → VS, Continuous Z ∧
      ContDiffOn ℝ ∞ Z (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, ‖Z s - baseZ s‖ ≤ 1 / 128) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) ∧
      (∀ s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1,
        deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, Z s 2 < 0) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, Z s 3 < 0) ∧
      StrictAntiOn (fun s : ℝ => Z s 0) (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      StrictAntiOn (fun s : ℝ => Z s 1) (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      ∃ X Y : ℝ → ℝ, ContDiff ℝ ∞ X ∧ ContDiff ℝ ∞ Y ∧
        (∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8) 1, X s = Z s 0 ∧ Y s = Z s 1) ∧
        (∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv X s = Z s 2 ∧ deriv Y s = Z s 3) ∧
        StrictAntiOn X (Set.Icc (3 * (1 - 2 * τ) / 8) 1) ∧
        StrictAntiOn Y (Set.Icc (3 * (1 - 2 * τ) / 8) 1) ∧
        X 1 = profileX 1 ∧ Y 1 = profileX 1 ∧
        (∀ s : ℝ, c ≤ s → X s = profileX s) ∧
        (∀ s : ℝ, c ≤ s → Y s = profileX s) ∧
        (∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
          X s = Z s 0 ∧ Y s = Z s 1) ∧
        (∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
          deriv X s = Z s 2 ∧ deriv Y s = Z s 3)∧
        (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |h s| ≤ M) ∧
          (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |deriv h s| ≤ M) ∧
          (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  classical
  obtain ⟨η, hη0, hη⟩ := hflat
  set a : ℝ := (1 - 2 * τ) / 2 with hadef
  set a₀ : ℝ := a / 2 with ha₀def
  set a' : ℝ := 3 * a / 4 - (1 - 2 * τ) / 32 with hadef'
  set α : ℝ := 5 * a / 8 with hαdef
  have ha : 0 < a := by rw [hadef]; linarith
  have ha1 : a < 1 := by rw [hadef]; linarith
  have ha₀ : 0 < a₀ := by rw [ha₀def]; linarith
  have ha₀1 : a₀ < 1 := by rw [ha₀def]; linarith
  have ha₀a : a₀ ≤ a := by rw [ha₀def]; linarith
  have ha' : a' < a := by rw [hadef', hadef]; linarith
  have ha₀a' : a₀ < a' := by rw [ha₀def, hadef', hadef]; linarith
  have ha'a : a' ≤ a := le_of_lt ha'
  have hα : α < a' := by rw [hαdef, hadef', hadef]; linarith
  have ha₀α : a₀ < α := by rw [ha₀def, hαdef, hadef]; linarith
  have hca : a₀ ≤ c := by rw [ha₀def, hadef]; linarith
  -- the margin and the radius
  obtain ⟨m, hm0, hm⟩ := exists_margin_profileX (a := a₀) ha₀ ha₀1.le
  set r : ℝ := min (min m 1) (1 / 64) with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]; exact lt_min (lt_min hm0 one_pos) (by norm_num)
  have hr1 : r < 1 := by
    have h : r ≤ 1 / 64 := by rw [hrdef]; exact min_le_right _ _
    linarith
  have hrm : r ≤ m := by rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hr2 : r ≤ 1 / 64 := by rw [hrdef]; exact min_le_right _ _
  set εmax : ℝ := min (min (η / 2) (a / 4)) 1 with hεmaxdef
  have hεmax : 0 < εmax := by
    rw [hεmaxdef]; exact lt_min (lt_min (by linarith) (by linarith)) one_pos
  obtain ⟨ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, hder, hneg2, hneg3, hXanti, hYanti,
    hM⟩ :=
    volterra_master_gen n hn hh hsupp ha₀ ha₀1 hr0 hr1 hca hc hc1 hεmax hm0 hrm hm
  have hεa4 : ε < a / 4 := by
    refine lt_of_lt_of_le hεmax' ?_
    rw [hεmaxdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  -- the two global coordinate functions
  have hZ0sm : ContDiffOn ℝ ∞ (fun s : ℝ => Z s 0) (Set.Ioo a₀ 1) :=
    (contDiffOn_state_coord_inf (Z := Z) (a := a₀) (b := 1) (i := 0) hZsm).mono
      (Set.Ioo_subset_Icc_self)
  have hZ1sm : ContDiffOn ℝ ∞ (fun s : ℝ => Z s 1) (Set.Ioo a₀ 1) :=
    (contDiffOn_state_coord_inf (Z := Z) (a := a₀) (b := 1) (i := 1) hZsm).mono
      (Set.Ioo_subset_Icc_self)
  have hZ2c : Continuous (fun σ : ℝ => Z σ 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4)).comp hZc
  have hZ3c : Continuous (fun σ : ℝ => Z σ 3) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4)).comp hZc
  have hac : a < c := by rw [hadef]; linarith
  have ha'c : a' ≤ c := le_of_lt (lt_trans ha' hac)
  set βglue : ℝ := (1 + c) / 2 with hβdef
  have hcβ : c < βglue := by rw [hβdef]; linarith
  have hβ1 : βglue < 1 := by rw [hβdef]; linarith
  set glue : ℝ → ℝ := Commons.Analysis.Calculus.smoothGlue α a' c βglue with hgluedef
  have hglue_sm : ContDiff ℝ ∞ glue := Commons.Analysis.Calculus.contDiff_smoothGlue α a' c βglue
  have hglue_one : ∀ t ∈ Set.Icc a' c, glue t = 1 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_one hα ha'c hcβ ht
  have hglue_zero_right : ∀ t : ℝ, βglue ≤ t → glue t = 0 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_zero_right hcβ ht
  have hglue_zero_left : ∀ t : ℝ, t ≤ α → glue t = 0 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_zero_left hα ht
  have hglue_tsupp : tsupport glue ⊆ Set.Icc α βglue :=
    Commons.Analysis.Calculus.tsupport_smoothGlue_subset hα hcβ
  have hsub : tsupport glue ⊆ Set.Ioo a₀ 1 := by
    intro t ht
    have h1 := hglue_tsupp ht
    exact ⟨lt_of_lt_of_le ha₀α h1.1, lt_of_le_of_lt h1.2 hβ1⟩
  set X : ℝ → ℝ := fun s => glue s * (Z s 0) + (1 - glue s) * profileX s with hXdef
  set Y : ℝ → ℝ := fun s => glue s * (Z s 1) + (1 - glue s) * profileX s with hYdef
  have hXsm : ContDiff ℝ ∞ X := by
    rw [hXdef]
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => glue s * (Z s 0)) :=
      Commons.Analysis.Calculus.ContDiff.mul_of_contDiffOn_isOpen hglue_sm hZ0sm isOpen_Ioo hsub
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 - glue s) * profileX s) :=
      (contDiff_const.sub hglue_sm).mul contDiff_profileX
    exact h1.add h2
  have hYsm : ContDiff ℝ ∞ Y := by
    rw [hYdef]
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => glue s * (Z s 1)) :=
      Commons.Analysis.Calculus.ContDiff.mul_of_contDiffOn_isOpen hglue_sm hZ1sm isOpen_Ioo hsub
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 - glue s) * profileX s) :=
      (contDiff_const.sub hglue_sm).mul contDiff_profileX
    exact h1.add h2
  -- `X = Z 0` and `Y = Z 1` on `[a',1]`
  have hXY : ∀ s ∈ Set.Icc a' 1, X s = Z s 0 ∧ Y s = Z s 1 := by
    intro s hs
    by_cases hsc : s ≤ c
    · have hglue1 : glue s = 1 := hglue_one s ⟨hs.1, hsc⟩
      constructor
      · change glue s * (Z s 0) + (1 - glue s) * profileX s = Z s 0
        rw [hglue1]; simp
      · change glue s * (Z s 1) + (1 - glue s) * profileX s = Z s 1
        rw [hglue1]; simp
    · push_neg at hsc
      have hZeq : Z s 0 = profileX s := by
        rw [hZb s ⟨hsc.le, hs.2⟩, baseZ_apply_zero]
      have hZeq1 : Z s 1 = profileX s := by
        rw [hZb s ⟨hsc.le, hs.2⟩, baseZ_apply_one]
      constructor
      · change glue s * (Z s 0) + (1 - glue s) * profileX s = Z s 0
        rw [hZeq]; ring
      · change glue s * (Z s 1) + (1 - glue s) * profileX s = Z s 1
        rw [hZeq1]; ring
  have hderX : ∀ s ∈ Set.Ioo a' 1, deriv X s = Z s 2 := by
    intro s hs
    have hnhds : Set.Icc a' 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : X =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := by
      filter_upwards [hnhds] with u hu
      exact (hXY u hu).1
    have hev2 : (fun u : ℝ => Z u 0) =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := Filter.EventuallyEq.rfl
    have hd : deriv (fun u : ℝ => Z u 0) s = Z s 2 := (hder s ⟨lt_trans ha₀a' hs.1, hs.2⟩).1
    rw [hev.deriv_eq, hd]
  have hderY : ∀ s ∈ Set.Ioo a' 1, deriv Y s = Z s 3 := by
    intro s hs
    have hnhds : Set.Icc a' 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : Y =ᶠ[𝓝 s] (fun u : ℝ => Z u 1) := by
      filter_upwards [hnhds] with u hu
      exact (hXY u hu).2
    have hd : deriv (fun u : ℝ => Z u 1) s = Z s 3 := (hder s ⟨lt_trans ha₀a' hs.1, hs.2⟩).2
    rw [hev.deriv_eq, hd]
  have hXanti' : StrictAntiOn X (Set.Icc a' 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hXsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderX s hs]
    exact hneg2 s ⟨le_trans ha₀a'.le hs.1.le, hs.2.le⟩
  have hYanti' : StrictAntiOn Y (Set.Icc a' 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hYsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderY s hs]
    exact hneg3 s ⟨le_trans ha₀a'.le hs.1.le, hs.2.le⟩
  have hX1 : X 1 = profileX 1 := (hXY 1 ⟨by linarith [ha'], le_rfl⟩).1.trans (by
    rw [hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_zero])
  have hY1 : Y 1 = profileX 1 := (hXY 1 ⟨by linarith [ha'], le_rfl⟩).2.trans (by
    rw [hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_one])
  have ha₀val : a₀ = (1 - 2 * τ) / 4 := by rw [ha₀def, hadef]; ring
  have ha'val : a' ≤ 3 * (1 - 2 * τ) / 8 := by rw [hadef', hadef]; linarith
  have hεa4' : ε < (1 - 2 * τ) / 8 := by rw [hadef] at hεa4; linarith
  rw [ha₀val] at hZsm hZbd hZfix hder hneg2 hneg3 hXanti hYanti
  have hZbd' : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, ‖Z s - baseZ s‖ ≤ 1 / 128 := by
    intro s hs
    refine le_trans (hZbd s hs) ?_
    linarith [hr2]
  have hXYr : ∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8) 1, X s = Z s 0 ∧ Y s = Z s 1 :=
    fun s hs => hXY s ⟨le_trans ha'val hs.1, hs.2⟩
  have hderXr : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv X s = Z s 2 :=
    fun s hs => hderX s ⟨lt_of_le_of_lt ha'val hs.1, hs.2⟩
  have hderYr : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv Y s = Z s 3 :=
    fun s hs => hderY s ⟨lt_of_le_of_lt ha'val hs.1, hs.2⟩
  have hXantir : StrictAntiOn X (Set.Icc (3 * (1 - 2 * τ) / 8) 1) :=
    hXanti'.mono (Set.Icc_subset_Icc ha'val le_rfl)
  have hYantir : StrictAntiOn Y (Set.Icc (3 * (1 - 2 * τ) / 8) 1) :=
    hYanti'.mono (Set.Icc_subset_Icc ha'val le_rfl)
  have hXp : ∀ s : ℝ, c ≤ s → X s = profileX s := by
    intro s hs
    by_cases hsc : s ≤ βglue
    · have hZeq : Z s 0 = profileX s := by
        rw [hZb s ⟨hs, le_trans hsc hβ1.le⟩, baseZ_apply_zero]
      change glue s * (Z s 0) + (1 - glue s) * profileX s = profileX s
      rw [hZeq]; ring
    · push_neg at hsc
      have hgl0 : glue s = 0 := hglue_zero_right s hsc.le
      change glue s * (Z s 0) + (1 - glue s) * profileX s = profileX s
      rw [hgl0]; simp
  have hYp : ∀ s : ℝ, c ≤ s → Y s = profileX s := by
    intro s hs
    by_cases hsc : s ≤ βglue
    · have hZeq : Z s 1 = profileX s := by
        rw [hZb s ⟨hs, le_trans hsc hβ1.le⟩, baseZ_apply_one]
      change glue s * (Z s 1) + (1 - glue s) * profileX s = profileX s
      rw [hZeq]; ring
    · push_neg at hsc
      have hgl0 : glue s = 0 := hglue_zero_right s hsc.le
      change glue s * (Z s 1) + (1 - glue s) * profileX s = profileX s
      rw [hgl0]; simp
  have ha'e : a' = 3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 := by rw [hadef', hadef]; ring
  have hXYb : ∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
      X s = Z s 0 ∧ Y s = Z s 1 := by
    intro s hs
    have hs' : s ∈ Set.Icc a' 1 := by
      rw [Set.mem_Icc] at hs ⊢
      exact ⟨by linarith [hs.1, ha'e], hs.2⟩
    exact hXY s hs'
  have hderb : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
      deriv X s = Z s 2 ∧ deriv Y s = Z s 3 := by
    intro s hs
    have hs' : s ∈ Set.Ioo a' 1 := by
      rw [Set.mem_Ioo] at hs ⊢
      exact ⟨by linarith [hs.1, ha'e], hs.2⟩
    exact ⟨hderX s hs', hderY s hs'⟩
  have hM' : ∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |h s| ≤ M) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |deriv h s| ≤ M) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |iteratedDeriv 2 h s| ≤ M) ∧
      ε * M ≤ 1 / 2 := by
    simpa only [ha₀val] using hM
  exact ⟨ε, hε0, hεa4', Z, hZc, hZsm, hZbd', hZfix, hZb, hder, hneg2, hneg3, hXanti, hYanti,
    X, Y, hXsm, hYsm, hXYr, fun s hs => ⟨hderXr s hs, hderYr s hs⟩,
    hXantir, hYantir, hX1, hY1,
    hXp, hYp, hXYb, hderb, hM'⟩

end Commons.Geometry.Ulam
end

-- ===== FILE _envelope.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-!
## The envelope profile `F`

On the closed interval `[l, r]` (with `l = -(X a)`, `r = Y a`) the cap function `F` is defined by
three pieces: the envelope `envPos` on `[profileX 1, r]`, the semicircle `envMid` on
`[-profileX 1, profileX 1]`, and the mirror envelope `envNeg` on `[l, -profileX 1]`.
Each piece agrees with the semicircle on a neighbourhood of the two junctions (because
`X = Y = profileX` and `h = 0` on `[c,1]`), which makes `F` of class `C^{n+2}` on `[l,r]`.
-/

/-- The positive-side envelope formula. -/
noncomputable def envPos (h : ℝ → ℝ) (ε : ℝ) (σ : ℝ → ℝ) (t : ℝ) : ℝ :=
  σ t * t + ε * h (σ t)

/-- The semicircle piece. -/
noncomputable def envMid (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

/-- The negative-side envelope formula.  NOTE the sign: the paper's `f` satisfies
`f (-x s) = s * (-x s) + h s` (negative on the left), while the target requires `0 < f t` on
`(-1,1)`; since the target's root conditions are SQUARED, we take the positive branch, i.e. the
negative of the paper's expression.  At the junction `t = -profileX 1` this still equals `envMid`. -/
noncomputable def envNeg (h : ℝ → ℝ) (ε : ℝ) (τ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(τ (-t) * t + ε * h (τ (-t)))

/-- The envelope profile, defined by the three pieces; `l` and `r` are the outer endpoints. -/
noncomputable def envelopeF (h : ℝ → ℝ) (ε : ℝ) (σ τ : ℝ → ℝ) (l r : ℝ) : ℝ → ℝ :=
  fun t => if t ∈ Set.Icc (profileX 1) r then envPos h ε σ t
           else if t ∈ Set.Icc (-profileX 1) (profileX 1) then envMid t
           else if t ∈ Set.Icc l (-profileX 1) then envNeg h ε τ t
           else 0

variable {h : ℝ → ℝ} {ε : ℝ} {σ τ : ℝ → ℝ} {l r t : ℝ}

@[simp] lemma envelopeF_of_mem_pos (ht : t ∈ Set.Icc (profileX 1) r) :
    envelopeF h ε σ τ l r t = envPos h ε σ t := by
  simp only [envelopeF, if_pos ht]

@[simp] lemma envelopeF_of_mem_mid (ht : t ∈ Set.Ioo (-profileX 1) (profileX 1)) :
    envelopeF h ε σ τ l r t = envMid t := by
  rw [envelopeF, if_neg (fun hc : t ∈ Set.Icc (profileX 1) r => absurd hc.1 (not_le.mpr ht.2)),
    if_pos ⟨ht.1.le, ht.2.le⟩]

@[simp] lemma envelopeF_of_mem_neg (ht : t ∈ Set.Ico l (-profileX 1)) :
    envelopeF h ε σ τ l r t = envNeg h ε τ t := by
  have hpos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  have h1 : ¬ t ∈ Set.Icc (profileX 1) r := fun hc => by linarith [hc.1, ht.2, hpos]
  have h2 : ¬ t ∈ Set.Icc (-profileX 1) (profileX 1) := fun hc => by linarith [hc.1, ht.2, hpos]
  rw [envelopeF, if_neg h1, if_neg h2]
  exact if_pos ⟨ht.1, ht.2.le⟩

/-- On the middle interval the envelope is the square of the semicircle. -/
lemma envMid_sq {t : ℝ} (ht : t ∈ Set.Icc (-profileX 1) (profileX 1)) :
    envMid t ^ 2 = 1 - t ^ 2 := by
  have hpos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  have hsq : profileX 1 ^ 2 = 1 / 2 := by
    have h : 1 - profileX 1 ^ 2 = profileX 1 ^ 2 := by
      simpa using one_sub_profileX_sq 1
    linarith
  have habs : |t| ≤ profileX 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have hsq2 : t ^ 2 ≤ profileX 1 ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) habs 2
  rw [envMid, Real.sq_sqrt (by nlinarith)]

/-- **The positive junction.**  On the image of `[c,1]` under `Y` (which is exactly
`[profileX 1, profileX c]`, because `Y = profileX` there and `h` vanishes there) the envelope
`envPos` coincides with the semicircle `envMid`.  This is what makes `F` smooth across the
junction `t = profileX 1`. -/
lemma envPos_eq_envMid {a c τ : ℝ} {h σ Y : ℝ → ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (hc : 1 - τ < c) (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hYc : ∀ s ∈ Set.Icc c 1, Y s = profileX s)
    (hYanti : StrictAntiOn Y (Set.Icc a 1))
    (hσY : ∀ t ∈ Set.Icc (profileX 1) (Y a), Y (σ t) = t)
    (hσmem : ∀ t ∈ Set.Icc (profileX 1) (Y a), σ t ∈ Set.Icc a 1)
    {ε t : ℝ} (ht : t ∈ Set.Icc (profileX 1) (profileX c)) :
    envPos h ε σ t = envMid t := by
  have hcI : c ∈ Set.Icc a 1 := ⟨hac, hc1⟩
  have haI : a ∈ Set.Icc a 1 := ⟨le_rfl, le_trans hac hc1⟩
  have hYc1 : Y c = profileX c := hYc c ⟨le_rfl, hc1⟩
  have hYac : Y c ≤ Y a := by
    rcases eq_or_lt_of_le hac with h | h
    · rw [h]
    · exact (hYanti haI hcI h).le
  have ht' : t ∈ Set.Icc (profileX 1) (Y a) := ⟨ht.1, le_trans ht.2 (by rw [← hYc1]; exact hYac)⟩
  have hYt : Y (σ t) = t := hσY t ht'
  have hmem := hσmem t ht'
  -- `σ t ∈ Icc c 1`
  have hge : c ≤ σ t := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : Y c < Y (σ t) := hYanti hmem hcI hlt
    rw [hYt, hYc1] at h1
    exact absurd h1 (not_lt.mpr ht.2)
  have hσmem' : σ t ∈ Set.Icc c 1 := ⟨hge, hmem.2⟩
  have ht_eq : t = profileX (σ t) := by
    have h1 : Y (σ t) = profileX (σ t) := hYc (σ t) hσmem'
    rw [h1] at hYt
    exact hYt.symm
  have hσpos : 0 < σ t := lt_of_lt_of_le (lt_of_lt_of_le ha hac) hge
  have hh0 : h (σ t) = 0 := h_eq_zero_of_one_sub_lt hsupp (lt_of_lt_of_le hc hge)
  have h2 : 0 ≤ σ t * profileX (σ t) :=
    mul_nonneg hσpos.le (le_of_lt (profileX_pos (σ t) hσpos))
  have hsqt : t ^ 2 = profileX (σ t) ^ 2 := congrArg (fun u : ℝ => u ^ 2) ht_eq
  have hsq' : 1 - t ^ 2 = (σ t * profileX (σ t)) ^ 2 := by
    rw [hsqt, one_sub_profileX_sq]
  have hmid : envMid t = σ t * profileX (σ t) := by
    rw [envMid, hsq', Real.sqrt_sq h2]
  have hpos_eq : σ t * t = σ t * profileX (σ t) := congrArg (fun u : ℝ => σ t * u) ht_eq
  rw [envPos, hh0, mul_zero, add_zero, hpos_eq, ← hmid]

/-- **The negative junction.**  Mirror of `envPos_eq_envMid`: on the image of `[c,1]` under `X`
(namely `[-profileX c, -profileX 1]`) the envelope `envNeg` coincides with the semicircle.  Note
that the semicircle is EVEN, which is what absorbs the sign flip in `envNeg`. -/
lemma envNeg_eq_envMid {a c δ : ℝ} {h : ℝ → ℝ} {X τinv : ℝ → ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (hc : 1 - δ < c) (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * δ) (1 - δ))
    (hXc : ∀ s ∈ Set.Icc c 1, X s = profileX s)
    (hXanti : StrictAntiOn X (Set.Icc a 1))
    (hτX : ∀ u ∈ Set.Icc (profileX 1) (X a), X (τinv u) = u)
    (hτmem : ∀ u ∈ Set.Icc (profileX 1) (X a), τinv u ∈ Set.Icc a 1)
    {ε t : ℝ} (ht : t ∈ Set.Icc (-profileX c) (-profileX 1)) :
    envNeg h ε τinv t = envMid t := by
  set u : ℝ := -t with hudef
  have hu_mem : u ∈ Set.Icc (profileX 1) (profileX c) := by
    rw [hudef]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcI : c ∈ Set.Icc a 1 := ⟨hac, hc1⟩
  have haI : a ∈ Set.Icc a 1 := ⟨le_rfl, le_trans hac hc1⟩
  have hXc1 : X c = profileX c := hXc c ⟨le_rfl, hc1⟩
  have hXac : X c ≤ X a := by
    rcases eq_or_lt_of_le hac with h | h
    · rw [h]
    · exact (hXanti haI hcI h).le
  have hu' : u ∈ Set.Icc (profileX 1) (X a) :=
    ⟨hu_mem.1, le_trans hu_mem.2 (by rw [← hXc1]; exact hXac)⟩
  have hXu : X (τinv u) = u := hτX u hu'
  have hmem := hτmem u hu'
  have hge : c ≤ τinv u := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : X c < X (τinv u) := hXanti hmem hcI hlt
    rw [hXu, hXc1] at h1
    exact absurd h1 (not_lt.mpr hu_mem.2)
  have hτmem' : τinv u ∈ Set.Icc c 1 := ⟨hge, hmem.2⟩
  have hu_eq : u = profileX (τinv u) := by
    have h1 : X (τinv u) = profileX (τinv u) := hXc (τinv u) hτmem'
    rw [h1] at hXu
    exact hXu.symm
  have hτpos : 0 < τinv u := lt_of_lt_of_le (lt_of_lt_of_le ha hac) hge
  have hh0 : h (τinv u) = 0 := h_eq_zero_of_one_sub_lt hsupp (lt_of_lt_of_le hc hge)
  have h2 : 0 ≤ τinv u * profileX (τinv u) :=
    mul_nonneg hτpos.le (le_of_lt (profileX_pos (τinv u) hτpos))
  have hmid : envMid t = τinv u * profileX (τinv u) := by
    have ht_sq : t ^ 2 = u ^ 2 := by rw [hudef]; ring
    have hsq : 1 - u ^ 2 = (τinv u * profileX (τinv u)) ^ 2 := by
      have hsq' : u ^ 2 = profileX (τinv u) ^ 2 := congrArg (fun w : ℝ => w ^ 2) hu_eq
      rw [hsq', one_sub_profileX_sq]
    rw [envMid, ht_sq, hsq, Real.sqrt_sq h2]
  have hL : envNeg h ε τinv t = -(τinv u * t) := by
    rw [envNeg, ← hudef, hh0, mul_zero, add_zero]
  have hpm : τinv u * t = -(τinv u * u) := by
    have ht' : t = -u := by rw [hudef]; ring
    rw [ht']
    ring
  rw [hL, hpm, neg_neg, hmid]
  exact congrArg (fun w : ℝ => τinv u * w) hu_eq

end Commons.Geometry.Ulam
end

-- ===== FILE _glob2.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra
open Commons.Analysis.Calculus

/-- The left endpoint of the interval on which the row argument is run. -/
def aRow (τ : ℝ) : ℝ := 3 * (1 - 2 * τ) / 8

lemma aRow_lt_one {τ : ℝ} (hτ : -5 / 6 < τ) : aRow τ < 1 := by unfold aRow; linarith

lemma aRow_pos {τ : ℝ} (hτ : 2 * τ < 1) : 0 < aRow τ := by unfold aRow; linarith

lemma aRow_pos_of (τ : ℝ) : 0 < aRow τ ↔ 2 * τ < 1 := by
  unfold aRow; constructor <;> intro h <;> linarith

lemma aRow_le (τ : ℝ) (hτ : 0 ≤ τ) : aRow τ ≤ 3 / 8 := by unfold aRow; linarith

lemma aRow_le_one {τ : ℝ} (hτ : -5 / 6 < τ) : aRow τ ≤ 1 := (aRow_lt_one hτ).le

/-- **The inverse of a strictly antitone `C^∞` function on `[aRow τ, 1]`, of class `C^{n+2}`.**
This is the finite-order inverse of `_inv.lean` applied to the state coordinate functions. -/
lemma exists_inv_row (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) {Y : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y)
    (hYanti : StrictAntiOn Y (Set.Icc (aRow τ) 1))
    (hYder : ∀ s ∈ Set.Icc (aRow τ) 1, deriv Y s ≠ 0) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ (n + 2) g (Set.Icc (Y 1) (Y (aRow τ))) ∧
      (∀ t ∈ Set.Icc (Y 1) (Y (aRow τ)), g t ∈ Set.Icc (aRow τ) 1) ∧
      (∀ t ∈ Set.Icc (Y 1) (Y (aRow τ)), Y (g t) = t) ∧
      (∀ s ∈ Set.Icc (aRow τ) 1, g (Y s) = s) := by
  have hle : ((n + 2 : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 2)))
  obtain ⟨g, h1, h2, h3, h4⟩ :=
    Commons.Analysis.Calculus.exists_contDiffOn_invFunOn_of_strictAntiOn
      (k := n + 2) (by omega) (a := aRow τ) (b := 1) (aRow_lt_one (by linarith))
      (hY.of_le hle) hYanti hYder
  exact ⟨g, h1, h2, h3, h4⟩

/-- `envMid` is `C^k` on `[-ρ, ρ]` for any `ρ < 1`. -/
lemma contDiffOn_envMid_gen (K : ℕ) {ρ : ℝ} (hρ : ρ < 1) :
    ContDiffOn ℝ K envMid (Set.Icc (-ρ) ρ) := by
  unfold envMid
  refine ContDiffOn.sqrt (by fun_prop) ?_
  intro t ht
  have h : |t| ≤ ρ := abs_le.mpr ⟨ht.1, ht.2⟩
  have hρ0 : 0 ≤ ρ := by linarith [ht.1, ht.2]
  have h2 : t ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) h 2
  have h3 : ρ ^ 2 < 1 := by nlinarith
  nlinarith [h2, h3]

/-- The square of the semicircle: `envMid t ^ 2 = 1 - t ^ 2` for `|t| ≤ 1`. -/
lemma envMid_sq_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : envMid t ^ 2 = 1 - t ^ 2 := by
  rw [envMid, Real.sq_sqrt (by nlinarith [abs_nonneg t, abs_le.mp ht])]

/-- Monotonicity of an inverse function on its interval. -/
lemma invRow_anti {Y g : ℝ → ℝ} {l p : ℝ} (hanti : StrictAntiOn Y (Set.Icc l 1))
    (hYg : ∀ t ∈ Set.Icc p (Y l), Y (g t) = t)
    (hgmem : ∀ t ∈ Set.Icc p (Y l), g t ∈ Set.Icc l 1) :
    ∀ t₁ ∈ Set.Icc p (Y l), ∀ t₂ ∈ Set.Icc p (Y l), t₁ ≤ t₂ → g t₂ ≤ g t₁ := by
  intro t₁ h₁ t₂ h₂ hy
  by_contra hcon
  rw [not_le] at hcon
  have h := hanti (hgmem t₁ h₁) (hgmem t₂ h₂) hcon
  rw [hYg t₂ h₂, hYg t₁ h₁] at h
  exact absurd h (not_lt.mpr hy)

/-- `envMid` (the semicircle) is `C^k` on `[-profileX 1, profileX 1]`. -/
lemma contDiffOn_envMid (K : ℕ) :
    ContDiffOn ℝ K envMid (Set.Icc (-(profileX 1)) (profileX 1)) := by
  have hp1sq : profileX 1 ^ 2 = 2⁻¹ := by
    have h : 1 - profileX 1 ^ 2 = profileX 1 ^ 2 := by simpa using one_sub_profileX_sq 1
    linarith
  unfold envMid
  refine ContDiffOn.sqrt (by fun_prop) ?_
  intro t ht
  have ht2 : t ^ 2 ≤ profileX 1 ^ 2 := by
    have habs : |t| ≤ profileX 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) habs 2
  nlinarith [ht2, hp1sq]

lemma profileX_le_profileX' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    profileX b ≤ profileX a := by
  unfold profileX
  apply one_div_le_one_div_of_le
  · exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  · exact Real.sqrt_le_sqrt (by nlinarith)

lemma profileX_lt_profileX {a b : ℝ} (ha : 0 < a) (hab : a < b) : profileX b < profileX a := by
  unfold profileX
  refine one_div_lt_one_div_of_lt ?_ (Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg a]) (by nlinarith))
  exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])

/-- **The `C^{n+2}` device `f̂`.**  Globally `C^{n+2}`, its square reproduces the roots of the
perturbed state on `[aRow τ, 1]` and equals `1 - t^2` on the central interval
`[-profileX 1, profileX 1]`.  Built from the two (finite-order) inverses of `Y`, `X` and three
`taylorExtend`s glued by `smoothStep` weights.

PROOF PLAN (see PROGRESS.md UPDATE 42).  Set `σ := Y⁻¹`, `τi := X⁻¹` (from `exists_inv_row`),
`G₊ t := σ t * t + ε * h (σ t)`, `G₋ t := -(τi (-t) * t + ε * h (τi (-t)))`,
`P₊ := taylorExtend G₊ (n+2) (profileX 1) (Y (aRow τ))`,
`P₋ := taylorExtend G₋ (n+2) (-(X (aRow τ))) (-(profileX 1))`,
`Pmid := taylorExtend envMid (n+2) (-(profileX 1)) (profileX 1)`,
`φ₊ := smoothStep (profileX 1) (profileX c)`, `φ₋ := 1 - smoothStep (-(profileX c)) (-(profileX 1))`,
`f̂ := φ₊ * P₊ + φ₋ * P₋ + (1 - φ₊ - φ₋) * Pmid`.
All five are globally `ContDiff ℝ (n+2)` (`contDiff_taylorExtend`, `contDiff_smoothStep`).
The verification uses the TWO KEY IDENTITIES
`smoothStep_mix_pos : t ∈ Icc (profileX 1) (profileX c) → G₊ t = envMid t` and
`smoothStep_mix_neg : t ∈ Icc (-(profileX 1)) (-(profileX c)) → G₋ t = envMid t`
(which say that the weight transitions happen exactly where the mixed pieces agree), together with
`taylorExtend_of_mem`, `envMid_sq`, `one_sub_profileX_sq` and the anchor `Y s = X s = profileX s`
for `s ≥ c`. -/
theorem envelope_device (n : ℕ) (hn : 2 ≤ n) {τ ε c : ℝ} (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h X Y : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hc : 1 - τ < c) (hc1 : c < 1)
    (hXanti : StrictAntiOn X (Set.Icc (aRow τ) 1))
    (hYanti : StrictAntiOn Y (Set.Icc (aRow τ) 1))
    (hXder : ∀ s ∈ Set.Icc (aRow τ) 1, deriv X s ≠ 0)
    (hYder : ∀ s ∈ Set.Icc (aRow τ) 1, deriv Y s ≠ 0)
    (hX1 : X 1 = profileX 1) (hY1 : Y 1 = profileX 1)
    (hXc : ∀ s ∈ Set.Icc c 1, X s = profileX s)
    (hYc : ∀ s ∈ Set.Icc c 1, Y s = profileX s)
    (hXbig : profileX 1 < X (aRow τ)) (hYbig : profileX 1 < Y (aRow τ)) :
    ∃ fhat : ℝ → ℝ, ContDiff ℝ (n + 2) fhat ∧
      (∀ s ∈ Set.Icc (aRow τ) 1,
        fhat (Y s) ^ 2 = (s * Y s + ε * h s) ^ 2 ∧
        fhat (-(X s)) ^ 2 = (s * (-(X s)) + ε * h s) ^ 2) ∧
      (∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), fhat t ^ 2 = 1 - t ^ 2) ∧
      (∀ t ∈ Set.Icc (-(profileX c)) (profileX c), fhat t ^ 2 = 1 - t ^ 2) := by
  classical
  -- the construction and the two key identities; see the PROOF PLAN above.
  have hle : ((n + 2 : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 2)))
  obtain ⟨σ, hσsm, hσmem, hσY, hσleft⟩ := exists_inv_row n hτ0 hY hYanti hYder
  obtain ⟨τi, hτsm, hτmem, hτX, hτleft⟩ := exists_inv_row n hτ0 hX hXanti hXder
  rw [hY1] at hσsm hσmem hσY
  rw [hX1] at hτsm hτmem hτX
  have hσanti := invRow_anti (l := aRow τ) (p := profileX 1) hYanti hσY hσmem
  have hτanti := invRow_anti (l := aRow τ) (p := profileX 1) hXanti hτX hτmem
  have hYc' : Y c = profileX c := hYc c ⟨le_rfl, hc1.le⟩
  have hXc' : X c = profileX c := hXc c ⟨le_rfl, hc1.le⟩
  have hh0 : ∀ s : ℝ, c ≤ s → h s = 0 := by
    intro s hs
    by_contra hne
    have hmem : s ∈ Set.Icc (1 - 2 * τ) (1 - τ) := hsupp (Function.mem_support.mpr hne)
    linarith [hmem.2]
  -- the two envelope pieces (`Gp = envPos h ε σ`, `Gm = envNeg h ε τi` definitionally)
  set Gp : ℝ → ℝ := fun t => σ t * t + ε * h (σ t) with hGp
  set Gm : ℝ → ℝ := fun t => -(τi (-t) * t + ε * h (τi (-t))) with hGm
  have haRow0 : 0 < aRow τ := aRow_pos_of τ |>.mpr hτsmall
  have hp1 : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  have haRow1 : aRow τ < 1 := aRow_lt_one (by linarith)
  have hcpos : 0 < c := by linarith
  have hp1pc : profileX 1 < profileX c := profileX_lt_profileX (a := c) (b := 1) hcpos hc1
  have hnegc : -(profileX c) < -(profileX 1) := neg_lt_neg hp1pc
  have haRowc : aRow τ ≤ c := by
    have h1 : aRow τ ≤ 3 / 8 := aRow_le τ hτ0.le
    have h2 : (3 : ℝ) / 8 < c := by linarith
    linarith
  -- **the two key identities**: the weights' transition ranges are exactly where the mixed
  -- pieces agree (`envPos_eq_envMid` / `envNeg_eq_envMid` of `_envelope.lean`)
  have hGp_mid : ∀ t ∈ Set.Icc (profileX 1) (profileX c), Gp t = envMid t := by
    intro t ht
    have h := envPos_eq_envMid (h := h) (ε := ε) (σ := σ) (Y := Y) (a := aRow τ) (c := c)
      (τ := τ) haRow0 haRowc hc1.le hc hsupp hYc hYanti hσY hσmem ht
    simpa [Gp, envPos] using h
  have hGm_mid : ∀ t ∈ Set.Icc (-(profileX c)) (-(profileX 1)), Gm t = envMid t := by
    intro t ht
    have h := envNeg_eq_envMid (h := h) (ε := ε) (X := X) (τinv := τi) (a := aRow τ) (c := c)
      (δ := τ) haRow0 haRowc hc1.le hc hsupp hXc hXanti hτX hτmem ht
    simpa [Gm, envNeg] using h
  -- smoothness of the two envelope pieces
  have hGpsm : ContDiffOn ℝ (n + 2) Gp (Set.Icc (profileX 1) (Y (aRow τ))) := by
    have h2 : ContDiffOn ℝ (n + 2) (fun t : ℝ => ε * h (σ t))
        (Set.Icc (profileX 1) (Y (aRow τ))) :=
      contDiffOn_const.mul ((hh.of_le hle).contDiffOn.comp hσsm (Set.mapsTo_univ _ _))
    have h3 : ContDiffOn ℝ (n + 2) (fun t : ℝ => σ t * t)
        (Set.Icc (profileX 1) (Y (aRow τ))) := by
      simpa only [Pi.mul_apply, id_eq] using hσsm.mul contDiffOn_id
    have h4 := h3.add h2
    rw [hGp]
    exact h4
  have hGmsm : ContDiffOn ℝ (n + 2) Gm (Set.Icc (-(X (aRow τ))) (-(profileX 1))) := by
    have h1 : ContDiffOn ℝ (n + 2) (fun t : ℝ => τi (-t))
        (Set.Icc (-(X (aRow τ))) (-(profileX 1))) := by
      refine hτsm.comp contDiffOn_id.neg ?_
      intro t ht
      simp only [Set.mem_Icc, neg_neg] at ht ⊢
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h2 : ContDiffOn ℝ (n + 2) (fun t : ℝ => ε * h (τi (-t)))
        (Set.Icc (-(X (aRow τ))) (-(profileX 1))) :=
      contDiffOn_const.mul ((hh.of_le hle).contDiffOn.comp h1 (Set.mapsTo_univ _ _))
    have h3 : ContDiffOn ℝ (n + 2) (fun t : ℝ => τi (-t) * t)
        (Set.Icc (-(X (aRow τ))) (-(profileX 1))) := by
      simpa only [Pi.mul_apply, id_eq] using h1.mul contDiffOn_id
    have h4 := (h3.add h2).neg
    rw [hGm]
    exact h4
  -- the three flat pieces
  set Pp : ℝ → ℝ := taylorExtend Gp (n + 2) (profileX 1) (Y (aRow τ)) with hPp
  set Pm : ℝ → ℝ := taylorExtend Gm (n + 2) (-(X (aRow τ))) (-(profileX 1)) with hPm
  set P0 : ℝ → ℝ := taylorExtend envMid (n + 2) (-(profileX c)) (profileX c) with hP0
  have hPpsm : ContDiff ℝ (n + 2) Pp := contDiff_taylorExtend (n + 2) hYbig hGpsm
  have hPmsm : ContDiff ℝ (n + 2) Pm :=
    contDiff_taylorExtend (n + 2) (by rw [neg_lt_neg_iff]; exact hXbig) hGmsm
  have hpc1 : profileX c < 1 := by
    have h1 : (1 : ℝ) < Real.sqrt (1 + c ^ 2) := by
      rw [Real.lt_sqrt (by nlinarith [sq_nonneg c])]
      nlinarith [sq_nonneg c]
    rw [profileX]
    exact (div_lt_one (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg c]))).mpr h1
  have hP0sm : ContDiff ℝ (n + 2) P0 :=
    contDiff_taylorExtend (n + 2) (by linarith [hp1, hp1pc])
      (contDiffOn_envMid_gen (n + 2) hpc1)
  have hPpG : ∀ t ∈ Set.Icc (profileX 1) (Y (aRow τ)), Pp t = Gp t :=
    fun t ht => taylorExtend_of_mem ht
  have hPmG : ∀ t ∈ Set.Icc (-(X (aRow τ))) (-(profileX 1)), Pm t = Gm t :=
    fun t ht => taylorExtend_of_mem ht
  have hP0e : ∀ t ∈ Set.Icc (-(profileX c)) (profileX c), P0 t = envMid t :=
    fun t ht => taylorExtend_of_mem ht
  -- the weights and the device
  set φp : ℝ → ℝ := smoothStep (profileX 1) (profileX c) with hφp
  set φm : ℝ → ℝ := fun t => 1 - smoothStep (-(profileX c)) (-(profileX 1)) t with hφm
  have hφpsm : ContDiff ℝ (n + 2) φp := (contDiff_smoothStep _ _).of_le hle
  have hφmsm : ContDiff ℝ (n + 2) φm :=
    (contDiff_const.sub (contDiff_smoothStep _ _)).of_le hle
  set fhat : ℝ → ℝ := fun t => φp t * Pp t + φm t * Pm t + (1 - φp t - φm t) * P0 t with hfhat
  have hfhatsm : ContDiff ℝ (n + 2) fhat := by
    rw [hfhat]
    exact ((hφpsm.mul hPpsm).add (hφmsm.mul hPmsm)).add
      (((contDiff_const.sub hφpsm).sub hφmsm).mul hP0sm)
  have hYca : Y c ≤ Y (aRow τ) :=
    (hYanti.le_iff_ge ⟨haRowc, hc1.le⟩ ⟨le_rfl, haRow1.le⟩).mpr haRowc
  have hYc_le : profileX c ≤ Y (aRow τ) := by rw [← hYc']; exact hYca
  -- memberships used below
  have hXac : profileX c ≤ X (aRow τ) := by
    rw [← hXc']
    exact (hXanti.le_iff_ge ⟨haRowc, hc1.le⟩ ⟨le_rfl, haRow1.le⟩).mpr haRowc
  have hmem_pos : ∀ t ∈ Set.Icc (profileX c) (Y (aRow τ)),
      t ∈ Set.Icc (profileX 1) (Y (aRow τ)) :=
    fun t ht => ⟨le_trans hp1pc.le ht.1, ht.2⟩
  have hmem_pmid : ∀ t ∈ Set.Icc (profileX 1) (profileX c),
      t ∈ Set.Icc (-(profileX c)) (profileX c) ∧ t ∈ Set.Icc (profileX 1) (Y (aRow τ)) :=
    fun t ht => ⟨⟨by linarith [ht.1, hp1pc.le], ht.2⟩, ⟨ht.1, le_trans ht.2 hYc_le⟩⟩
  have hmem_neg : ∀ t ∈ Set.Icc (-(X (aRow τ))) (-(profileX c)),
      t ∈ Set.Icc (-(X (aRow τ))) (-(profileX 1)) :=
    fun t ht => ⟨ht.1, le_trans ht.2 hnegc.le⟩
  have hmem_nmid : ∀ t ∈ Set.Icc (-(profileX c)) (-(profileX 1)),
      t ∈ Set.Icc (-(X (aRow τ))) (-(profileX 1)) ∧ t ∈ Set.Icc (-(profileX c)) (profileX c) :=
    fun t ht => ⟨⟨by linarith [ht.1, hXac], ht.2⟩, ⟨ht.1, by linarith [ht.2, hp1]⟩⟩
  have hmem_center : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
      t ∈ Set.Icc (-(profileX c)) (profileX c) :=
    fun t ht => ⟨by linarith [ht.1, hp1pc.le], by linarith [ht.2, hp1pc.le]⟩
  -- **region facts**
  have hreg_pos : ∀ t ∈ Set.Icc (profileX c) (Y (aRow τ)), fhat t = Gp t := by
    intro t ht
    have hφp1 : φp t = 1 := by rw [hφp]; exact smoothStep_of_le' hp1pc ht.1
    have hφm0 : φm t = 0 := by
      rw [hφm]
      have h1 : smoothStep (-(profileX c)) (-(profileX 1)) t = 1 :=
        smoothStep_of_le' hnegc (by linarith [ht.1, hp1pc.le])
      simp [h1]
    change φp t * Pp t + φm t * Pm t + (1 - φp t - φm t) * P0 t = Gp t
    rw [hφp1, hφm0, hPpG t (hmem_pos t ht)]
    ring
  have hreg_pmid : ∀ t ∈ Set.Icc (profileX 1) (profileX c), fhat t = envMid t := by
    intro t ht
    obtain ⟨hm1, hm2⟩ := hmem_pmid t ht
    have hφm0 : φm t = 0 := by
      rw [hφm]
      have h1 : smoothStep (-(profileX c)) (-(profileX 1)) t = 1 :=
        smoothStep_of_le' hnegc (by linarith [ht.1, hp1pc.le])
      simp [h1]
    rw [hfhat]
    simp only [hφm0]
    rw [hPpG t hm2, hP0e t hm1, hGp_mid t ht]
    ring
  have hreg_neg : ∀ t ∈ Set.Icc (-(X (aRow τ))) (-(profileX c)), fhat t = Gm t := by
    intro t ht
    have hφm1 : φm t = 1 := by
      rw [hφm]
      have h1 : smoothStep (-(profileX c)) (-(profileX 1)) t = 0 := by
        refine smoothStep_of_le hnegc ?_
        linarith [ht.2]
      simp [h1]
    have hφp0 : φp t = 0 := by
      rw [hφp]
      exact smoothStep_of_le hp1pc (by linarith [ht.2, hp1])
    rw [hfhat]
    simp only [hφm1, hφp0]
    rw [hPmG t (hmem_neg t ht)]
    ring
  have hreg_nmid : ∀ t ∈ Set.Icc (-(profileX c)) (-(profileX 1)), fhat t = envMid t := by
    intro t ht
    obtain ⟨hm1, hm2⟩ := hmem_nmid t ht
    have hφp0 : φp t = 0 := by
      rw [hφp]
      exact smoothStep_of_le hp1pc (by linarith [ht.2, hp1])
    rw [hfhat]
    simp only [hφp0]
    rw [hPmG t hm1, hP0e t hm2, hGm_mid t ht]
    ring
  have hreg_center : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), fhat t = envMid t := by
    intro t ht
    have hφp0 : φp t = 0 := by
      rw [hφp]
      exact smoothStep_of_le hp1pc ht.2
    have hφm0 : φm t = 0 := by
      rw [hφm]
      have h1 : smoothStep (-(profileX c)) (-(profileX 1)) t = 1 :=
        smoothStep_of_le' hnegc ht.1
      simp [h1]
    rw [hfhat]
    simp only [hφp0, hφm0]
    rw [hP0e t (hmem_center t ht)]
    ring
  refine ⟨fhat, hfhatsm, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : s ≤ 1 := hs.2
    have hsa : aRow τ ≤ s := hs.1
    have hsaI : aRow τ ∈ Set.Icc (aRow τ) 1 := ⟨le_rfl, haRow1.le⟩
    have hsI : s ∈ Set.Icc (aRow τ) 1 := hs
    by_cases hsc : s ≤ c
    · have hscI : c ∈ Set.Icc (aRow τ) 1 := ⟨haRowc, hc1.le⟩
      have hYs_hi : profileX c ≤ Y s := by
        rw [← hYc']
        exact (hYanti.le_iff_ge hscI hsI).mpr hsc
      have hYs_lo : Y s ≤ Y (aRow τ) := (hYanti.le_iff_ge hsI hsaI).mpr hsa
      have hXs_hi : profileX c ≤ X s := by
        rw [← hXc']
        exact (hXanti.le_iff_ge hscI hsI).mpr hsc
      have hXs_lo : X s ≤ X (aRow τ) := (hXanti.le_iff_ge hsI hsaI).mpr hsa
      have h1 : fhat (Y s) = s * Y s + ε * h s := by
        rw [hreg_pos (Y s) ⟨hYs_hi, hYs_lo⟩]
        simp only [hGp, hσleft s hs]
      have h2 : fhat (-(X s)) = -(s * (-(X s)) + ε * h s) := by
        rw [hreg_neg (-(X s)) ⟨neg_le_neg hXs_lo, neg_le_neg hXs_hi⟩]
        simp only [hGm, neg_neg, hτleft s hs]
      constructor
      · rw [h1]
      · rw [h2]; ring
    · push_neg at hsc
      have hscI2 : s ∈ Set.Icc c 1 := ⟨hsc.le, hs1⟩
      have hYs_eq : Y s = profileX s := hYc s hscI2
      have hXs_eq : X s = profileX s := hXc s hscI2
      have hps : profileX s ∈ Set.Icc (profileX 1) (profileX c) :=
        ⟨profileX_le_profileX' (a := s) (b := 1) (le_trans haRow0.le hsa) hs1,
          profileX_le_profileX' (a := c) (b := s) hcpos.le hsc.le⟩
      have hhs : h s = 0 := hh0 s hsc.le
      have hle1 : profileX s ≤ 1 := by
        have hs2 : (1 : ℝ) ≤ Real.sqrt (1 + s ^ 2) :=
          Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg s])
        have hpos : 0 < Real.sqrt (1 + s ^ 2) :=
          Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])
        rw [profileX]
        exact (div_le_one hpos).mpr hs2
      have hmod : |profileX s| ≤ 1 := by
        rw [abs_of_pos (profileX_pos' s)]
        exact hle1
      have hmid1 : fhat (Y s) = envMid (Y s) := by
        rw [hYs_eq]
        exact hreg_pmid (profileX s) hps
      have hmid2 : fhat (-(X s)) = envMid (-(X s)) := by
        rw [hXs_eq]
        exact hreg_nmid (-(profileX s)) ⟨neg_le_neg hps.2, neg_le_neg hps.1⟩
      have henv1 : envMid (Y s) ^ 2 = (s * Y s) ^ 2 := by
        rw [hYs_eq, envMid_sq_of_abs_le_one hmod, one_sub_profileX_sq]
      have henv2 : envMid (-(X s)) ^ 2 = (s * (-(X s))) ^ 2 := by
        rw [hXs_eq]
        have hmod' : |-(profileX s)| ≤ 1 := by rw [abs_neg]; exact hmod
        rw [envMid_sq_of_abs_le_one hmod', neg_sq, one_sub_profileX_sq]
        ring
      constructor
      · rw [hmid1, henv1, hhs]; ring
      · rw [hmid2, henv2, hhs]; ring
  · intro t ht
    rw [hreg_center t ht, envMid_sq ht]
  · intro t ht
    have hmod : |t| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [ht.1, hp1, hp1pc.le], by linarith [ht.2, hp1pc, hpc1.le]⟩
    rcases le_or_gt t (profileX 1) with hle1 | hgt1
    · rcases le_or_gt (-(profileX 1)) t with hge1 | hlt1
      · rw [hreg_center t ⟨hge1, hle1⟩, envMid_sq_of_abs_le_one hmod]
      · rw [hreg_nmid t ⟨ht.1, hlt1.le⟩, envMid_sq_of_abs_le_one hmod]
    · rw [hreg_pmid t ⟨hgt1.le, ht.2⟩, envMid_sq_of_abs_le_one hmod]

end Commons.Geometry.Ulam
end

-- ===== FILE _state.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The state built from the global functions `X`, `Y` is the Volterra solution `Z`.** -/
lemma stateOf_eq_of_data {τ : ℝ} {X Y : ℝ → ℝ} {Z : ℝ → VS}
    (hX0 : ∀ s ∈ Set.Icc (aRow τ) 1, X s = Z s 0)
    (hY1 : ∀ s ∈ Set.Icc (aRow τ) 1, Y s = Z s 1)
    (hX2 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv X s = Z s 2)
    (hY3 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv Y s = Z s 3) :
    ∀ s ∈ Set.Ioo (aRow τ) 1, RyaboginVolterra.stateOf X Y s = Z s := by
  intro s hs
  have hsI : s ∈ Set.Icc (aRow τ) 1 := ⟨hs.1.le, hs.2.le⟩
  ext i
  fin_cases i
  · simpa [RyaboginVolterra.stateOf, RyaboginVolterra.mk4] using hX0 s hsI
  · simpa [RyaboginVolterra.stateOf, RyaboginVolterra.mk4] using hY1 s hsI
  · simpa [RyaboginVolterra.stateOf, RyaboginVolterra.mk4] using hX2 s hs
  · simpa [RyaboginVolterra.stateOf, RyaboginVolterra.mk4] using hY3 s hs

/-- The `Θ`-integral computed with `stateOf X Y` equals the one computed with `Z`: the two
integrands agree except possibly at the right endpoint `1`, which is a null set. -/
lemma integral_theta_stateOf_eq {n : ℕ} {τ : ℝ} {h X Y : ℝ → ℝ} {Z : ℝ → VS}
    (hstate : ∀ σ ∈ Set.Ioo (aRow τ) 1, RyaboginVolterra.stateOf X Y σ = Z σ)
    {s : ℝ} (hs : s ∈ Set.Icc (aRow τ) 1) :
    (∫ σ in s..1, RyaboginVolterra.Theta n h s σ (RyaboginVolterra.stateOf X Y σ))
      = (∫ σ in s..1, RyaboginVolterra.Theta n h s σ (Z σ)) := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_singleton 1)
  intro σ hσ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hσ ⊢
  have hmem : σ ∈ Set.uIoc s 1 := by
    by_contra hmem
    exact hσ fun h => absurd h hmem
  have hne : RyaboginVolterra.stateOf X Y σ ≠ Z σ := by
    intro heq
    exact hσ fun _ => by rw [heq]
  rw [Set.uIoc_of_le hs.2] at hmem
  by_contra h1
  exact hne (hstate σ ⟨lt_of_le_of_lt hs.1 hmem.1, lt_of_le_of_ne hmem.2 h1⟩)

end Commons.Geometry.Ulam
end

-- ===== FILE _errors.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The moment errors of the perturbed data vanish on `(aRow τ, 1)`.**

This is the assembly of the two finite-order row identities with the Volterra fixed-point equation
at the state `Z`: the right-hand sides of the rows cancel against the fixed point equation, so both
`iteratedDeriv (n+1) (momentF − momentRHS)` and `iteratedDeriv n (momentH)` vanish. -/
lemma moment_errors_zero (n : ℕ) (hn : 2 ≤ n) {τ ε : ℝ} {h X Y : ℝ → ℝ}
    (hτ0 : 0 < τ) (hh : ContDiff ℝ ∞ h)
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hXanti : StrictAntiOn X (Set.Icc (aRow τ) 1))
    (hYanti : StrictAntiOn Y (Set.Icc (aRow τ) 1))
    (hX1 : X 1 = profileX 1) (hY1 : Y 1 = profileX 1)
    {fhat : ℝ → ℝ} (hfhat : ContDiff ℝ (n + 2) fhat)
    (hroot : ∀ s ∈ Set.Icc (aRow τ) 1,
      fhat (Y s) ^ 2 = (s * Y s + ε * h s) ^ 2 ∧
      fhat (-(X s)) ^ 2 = (s * (-(X s)) + ε * h s) ^ 2)
    (hfb : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), fhat t ^ 2 = 1 - t ^ 2)
    {Z : ℝ → VS}
    (hX0 : ∀ s ∈ Set.Icc (aRow τ) 1, X s = Z s 0)
    (hY1' : ∀ s ∈ Set.Icc (aRow τ) 1, Y s = Z s 1)
    (hX2 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv X s = Z s 2)
    (hY3 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv Y s = Z s 3)
    (hZneg2 : ∀ s ∈ Set.Icc (aRow τ) 1, Z s 2 < 0)
    (hZneg3 : ∀ s ∈ Set.Icc (aRow τ) 1, Z s 3 < 0)
    (hZfix : ∀ s ∈ Set.Icc (aRow τ) 1, RyaboginVolterra.G n (ε • h) s (Z s)
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
        + RyaboginVolterra.Xi n (ε • h) s) :
    (∀ s ∈ Set.Ioo (aRow τ) 1,
      iteratedDeriv (n + 1)
        (fun u : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat u
          - RyaboginVolterra.momentRHS n u) s = 0) ∧
    (∀ s ∈ Set.Ioo (aRow τ) 1,
      iteratedDeriv n (fun u : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat u) s = 0) := by
  have hab : aRow τ ≤ 1 := by
    have h1 : aRow τ < 1 := aRow_lt_one (by linarith)
    exact h1.le
  have hsm : ContDiff ℝ ∞ (ε • h) := hh.const_smul ε
  have hsm' : ∀ s : ℝ, (ε • h) s = ε * h s := fun s => rfl
  have hneg2 : ∀ σ ∈ Set.Ioo (aRow τ) 1, deriv X σ ≤ 0 := by
    intro σ hσ
    rw [hX2 σ hσ]
    exact (hZneg2 σ ⟨hσ.1.le, hσ.2.le⟩).le
  have hneg3 : ∀ σ ∈ Set.Ioo (aRow τ) 1, deriv Y σ ≤ 0 := by
    intro σ hσ
    rw [hY3 σ hσ]
    exact (hZneg3 σ ⟨hσ.1.le, hσ.2.le⟩).le
  have hxle : ∀ s ∈ Set.Icc (aRow τ) 1, X 1 ≤ X s :=
    fun s hs => (hXanti.le_iff_ge ⟨hab, le_rfl⟩ hs).mpr hs.2
  have hyle : ∀ s ∈ Set.Icc (aRow τ) 1, Y 1 ≤ Y s :=
    fun s hs => (hYanti.le_iff_ge ⟨hab, le_rfl⟩ hs).mpr hs.2
  have hord : -(X 1) ≤ Y 1 := by
    rw [hX1, hY1]
    exact neg_le_self (profileX_pos 1 (by norm_num)).le
  have hxy : ∀ u ∈ Set.Icc (aRow τ) 1,
      fhat (Y u) ^ 2 = (u * Y u + (ε • h) u) ^ 2 ∧
      fhat (-(X u)) ^ 2 = (u * (-(X u)) + (ε • h) u) ^ 2 := by
    intro u hu
    obtain ⟨h1, h2⟩ := hroot u hu
    exact ⟨by simpa only [Pi.smul_apply, smul_eq_mul] using h1,
      by simpa only [Pi.smul_apply, smul_eq_mul] using h2⟩
  have hstate : ∀ σ ∈ Set.Ioo (aRow τ) 1, RyaboginVolterra.stateOf X Y σ = Z σ :=
    stateOf_eq_of_data hX0 hY1' hX2 hY3
  constructor
  · intro s hs
    have hsI : s ∈ Set.Icc (aRow τ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hstateS : RyaboginVolterra.stateOf X Y s = Z s := hstate s hs
    have hint := integral_theta_stateOf_eq (n := n) (h := ε • h) hstate hsI
    have hM := iteratedDeriv_momentF_eq_volterra_row_Ioo_fin n hn hab hsm hX hY
      hfhat hxy hneg2 hneg3 hX1 hY1 hfb
      hxle hyle hord s hs
    have hkill : (RyaboginVolterra.G n (ε • h) s (RyaboginVolterra.stateOf X Y s)) 2
        - ((∫ σ in s..1,
              RyaboginVolterra.Theta n (ε • h) s σ (RyaboginVolterra.stateOf X Y σ))
            + RyaboginVolterra.Xi n (ε • h) s) 2 = 0 := by
      rw [hstateS, hint, ← hZfix s hsI]
      ring
    rw [hM, hkill]
  · intro s hs
    have hsI : s ∈ Set.Icc (aRow τ) 1 := ⟨hs.1.le, hs.2.le⟩
    have hstateS : RyaboginVolterra.stateOf X Y s = Z s := hstate s hs
    have hint := integral_theta_stateOf_eq (n := n) (h := ε • h) hstate hsI
    have hH := iteratedDeriv_momentH_eq_volterra_row_Ioo_fin n hn hab hsm hX hY
      (hfhat.of_le (by exact_mod_cast (by omega : n ≤ n + 2))) hxy hneg2 hneg3 hX1 hY1 hfb
      hxle hyle hord s hs
    have hkill : (RyaboginVolterra.G n (ε • h) s (RyaboginVolterra.stateOf X Y s)) 3
        - ((∫ σ in s..1,
              RyaboginVolterra.Theta n (ε • h) s σ (RyaboginVolterra.stateOf X Y σ))
            + RyaboginVolterra.Xi n (ε • h) s) 3 = 0 := by
      rw [hstateS, hint, ← hZfix s hsI]
      ring
    rw [hH, hkill]

end Commons.Geometry.Ulam
end

-- ===== FILE _prop.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The first moment error is `C^{n+1}` on the row interval (the order the propagation needs). -/
lemma contDiffOn_momentErrorF (n : ℕ) {τ ε : ℝ} {h X Y : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    {fhat : ℝ → ℝ} (hfhat : ContDiff ℝ (n + 2) fhat) :
    ContDiffOn ℝ (n + 1)
      (fun s : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat s
        - RyaboginVolterra.momentRHS n s) (Set.Icc (aRow τ) 1) := by
  have hle1 : ((n + 1 : ℕ) : ℕ∞ω) ≤ ((n + 2 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  have h1 : ContDiff ℝ (n + 1)
      (fun s : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat s) :=
    contDiff_momentF_fin n (hh.const_smul ε) hX hY (hfhat.of_le hle1)
  have h2 : ContDiff ℝ (n + 1) (RyaboginVolterra.momentRHS n) := by
    have hle2 : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
      le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1)))
    exact (contDiff_momentRHS n).of_le hle2
  exact (h1.sub h2).contDiffOn

/-- The second moment function is `C^n` on the row interval. -/
lemma contDiffOn_momentErrorH (n : ℕ) {τ ε : ℝ} {h X Y : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    {fhat : ℝ → ℝ} (hfhat : ContDiff ℝ n fhat) :
    ContDiffOn ℝ n
      (fun s : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat s) (Set.Icc (aRow τ) 1) :=
  (contDiff_momentH_fin n (hh.const_smul ε) hX hY hfhat).contDiffOn

end Commons.Geometry.Ulam
end

-- ===== FILE _prop2.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The unperturbed (anchor) moments.**  If `X`, `Y` agree with `profileX` on `[c,1]`, the bump
`h` vanishes to the right of `c`, and the device `fhat` reproduces the semicircle on the cap
`[-profileX c, profileX c]`, then on `(c,1)` the two perturbed moments are the unperturbed ones:
the first equals `momentRHS` and the second vanishes. -/
lemma moment_base_on_anchor (n : ℕ) {ε c : ℝ} (hcpos : 0 < c) (hc1 : c < 1)
    {h X Y fhat : ℝ → ℝ}
    (hXc : ∀ s ∈ Set.Icc c 1, X s = profileX s)
    (hYc : ∀ s ∈ Set.Icc c 1, Y s = profileX s)
    (hh0 : ∀ s : ℝ, c ≤ s → h s = 0)
    (hfC : ∀ t ∈ Set.Icc (-(profileX c)) (profileX c), fhat t ^ 2 = 1 - t ^ 2) :
    (∀ s ∈ Set.Ioo c 1, RyaboginVolterra.momentF n (ε • h) X Y fhat s
        = RyaboginVolterra.momentRHS n s) ∧
    (∀ s ∈ Set.Ioo c 1, RyaboginVolterra.momentH n (ε • h) X Y fhat s = 0) := by
  have hpc0 : 0 < profileX c := profileX_pos c hcpos
  have hpc1 : profileX c ≤ 1 := (profileX_mem_Icc c).2
  have hsm : ∀ {s : ℝ}, c ≤ s → (ε • h) s = 0 := by
    intro s hs
    simp only [Pi.smul_apply, smul_eq_mul, hh0 s hs, mul_zero]
  have hdv : ∀ {s : ℝ}, c < s → deriv (ε • h) s = 0 := by
    intro s hs
    have hev : h =ᶠ[𝓝 s] 0 := by
      filter_upwards [Ioo_mem_nhds hs (show s < s + 1 by linarith)] with u hu
      exact hh0 u hu.1.le
    have h1 : (ε • h) =ᶠ[𝓝 s] (0 : ℝ → ℝ) := by
      filter_upwards [hev] with u hu
      simp only [Pi.smul_apply, smul_eq_mul, hu, mul_zero, Pi.zero_apply]
    rw [h1.deriv_eq]
    exact deriv_const s 0
  have hmem : ∀ {s t : ℝ}, c ≤ s → s ≤ 1 → t ∈ Set.uIcc (-(profileX s)) (profileX s) →
      t ∈ Set.Icc (-(profileX c)) (profileX c) := by
    intro s t hcs hs1 ht
    have hps : profileX s ≤ profileX c := profileX_le_profileX' hcpos.le hcs
    rw [Set.uIcc_of_le (neg_le_self (profileX_pos s (lt_of_lt_of_le hcpos hcs)).le)] at ht
    exact ⟨by linarith [ht.1, hps], by linarith [ht.2, hps]⟩
  constructor
  · intro s hs
    have hcs : c ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2.le
    rw [RyaboginVolterra.momentF, RyaboginVolterra.momentRHS,
      hXc s ⟨hcs, hs1⟩, hYc s ⟨hcs, hs1⟩, profileX]
    apply intervalIntegral.integral_congr
    intro t ht
    have hft : fhat t ^ 2 = 1 - t ^ 2 := hfC t (hmem hcs hs1 ht)
    simp only [RyaboginVolterra.momentIntegrand, RyaboginVolterra.line, Pi.smul_apply,
      smul_eq_mul, hsm hcs, add_zero, hft]
  · intro s hs
    have hcs : c ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2.le
    have hft : ∀ t ∈ Set.uIcc (-(profileX s)) (profileX s), fhat t ^ 2 = semicircle t ^ 2 := by
      intro t ht
      have htmem := hmem hcs hs1 ht
      exact (hfC t htmem).trans (semicircle_sq_of_mem_Icc ⟨by linarith [htmem.1, hpc1],
        by linarith [htmem.2, hpc1]⟩).symm
    have key : RyaboginVolterra.momentH n (ε • h) X Y fhat s
        = RyaboginVolterra.momentH n (fun _ : ℝ => 0) profileX profileX semicircle s := by
      rw [RyaboginVolterra.momentH, RyaboginVolterra.momentH,
        hXc s ⟨hcs, hs1⟩, hYc s ⟨hcs, hs1⟩, profileX]
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [RyaboginVolterra.centroidIntegrand, RyaboginVolterra.line,
        RyaboginVolterra.lineSlope, Pi.smul_apply, smul_eq_mul, hsm hcs, hft t ht,
        hdv hs.1, deriv_const, add_zero]
    rw [key, momentH_base_eq_zero]

/-- **The two moment identities of the device on the row interval `[aRow τ, 1]`.**

The moment errors of the perturbed data vanish to all orders on `(aRow τ, 1)`
(`moment_errors_zero`), and they vanish on a neighbourhood of an interior anchor point `c'` of the
interval `(c,1)` on which the data coincide with the unperturbed ones (`moment_base_on_anchor`).
Taylor's formula with Lagrange remainder (the commons lemma
`eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero`) then propagates the vanishing
leftwards to the whole interval. -/
theorem device_moment_identities (n : ℕ) (hn : 2 ≤ n) {τ ε c c' : ℝ}
    (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h X Y : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsup : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hXanti : StrictAntiOn X (Set.Icc (aRow τ) 1))
    (hYanti : StrictAntiOn Y (Set.Icc (aRow τ) 1))
    (hX1 : X 1 = profileX 1) (hY1 : Y 1 = profileX 1)
    {fhat : ℝ → ℝ} (hfhat : ContDiff ℝ (n + 2) fhat)
    (hroot : ∀ s ∈ Set.Icc (aRow τ) 1,
      fhat (Y s) ^ 2 = (s * Y s + ε * h s) ^ 2 ∧
      fhat (-(X s)) ^ 2 = (s * (-(X s)) + ε * h s) ^ 2)
    (hfb : ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), fhat t ^ 2 = 1 - t ^ 2)
    (hfbC : ∀ t ∈ Set.Icc (-(profileX c)) (profileX c), fhat t ^ 2 = 1 - t ^ 2)
    {Z : ℝ → VS}
    (hZfix : ∀ s ∈ Set.Icc (aRow τ) 1, RyaboginVolterra.G n (ε • h) s (Z s)
      = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
        + RyaboginVolterra.Xi n (ε • h) s)
    (hX0 : ∀ s ∈ Set.Icc (aRow τ) 1, X s = Z s 0)
    (hY1' : ∀ s ∈ Set.Icc (aRow τ) 1, Y s = Z s 1)
    (hX2 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv X s = Z s 2)
    (hY3 : ∀ s ∈ Set.Ioo (aRow τ) 1, deriv Y s = Z s 3)
    (hZneg2 : ∀ s ∈ Set.Icc (aRow τ) 1, Z s 2 < 0)
    (hZneg3 : ∀ s ∈ Set.Icc (aRow τ) 1, Z s 3 < 0)
    (hc : 1 - τ < c) (hc1 : c < 1)
    (hZb : ∀ s ∈ Set.Icc c 1, Z s = baseZ s)
    (hcc' : c < c') (hc'1 : c' < 1) :
    (∀ s ∈ Set.Icc (aRow τ) 1, RyaboginVolterra.momentF n (ε • h) X Y fhat s
        = RyaboginVolterra.momentRHS n s) ∧
    (∀ s ∈ Set.Icc (aRow τ) 1, RyaboginVolterra.momentH n (ε • h) X Y fhat s = 0) := by
  have haRowc : aRow τ ≤ c := by
    have h1 : aRow τ ≤ 3 / 8 := aRow_le τ hτ0.le
    have h2 : (3 : ℝ) / 8 < c := by linarith
    linarith
  have hcpos : 0 < c := by linarith
  have hh0 : ∀ s : ℝ, c ≤ s → h s = 0 := by
    intro s hs
    by_contra hne
    have hmem := hsup (Function.mem_support.mpr hne)
    linarith [hmem.2, hc]
  have hXc : ∀ s ∈ Set.Icc c 1, X s = profileX s := by
    intro s hs
    rw [hX0 s ⟨le_trans haRowc hs.1, hs.2⟩, hZb s hs, baseZ_apply_zero]
  have hYc : ∀ s ∈ Set.Icc c 1, Y s = profileX s := by
    intro s hs
    rw [hY1' s ⟨le_trans haRowc hs.1, hs.2⟩, hZb s hs, baseZ_apply_one]
  obtain ⟨hbaseF, hbaseH⟩ :=
    moment_base_on_anchor (ε := ε) n hcpos hc1 hXc hYc hh0 hfbC
  obtain ⟨hMerr, hHerr⟩ := moment_errors_zero n hn hτ0 hh hX hY hXanti hYanti hX1 hY1 hfhat hroot
    hfb hX0 hY1' hX2 hY3 hZneg2 hZneg3 hZfix
  have hab : aRow τ < 1 := aRow_lt_one (by linarith)
  have hac' : aRow τ < c' := lt_of_le_of_lt haRowc hcc'
  have huniq : UniqueDiffOn ℝ (Set.Icc (aRow τ) 1) := uniqueDiffOn_Icc hab
  have hle1 : ((n + 1 : ℕ) : ℕ∞ω) ≤ ∞ :=
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + 1)))
  have hlen : ((n : ℕ∞ω)) ≤ ((n + 2 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (by omega : n ≤ n + 2)
  constructor
  · have hcast : ((n : ℕ∞ω) + 1) = ((n + 1 : ℕ) : ℕ∞ω) := by push_cast; rfl
    have hF : ContDiffOn ℝ ((n : ℕ∞ω) + 1)
        (fun s : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat s
          - RyaboginVolterra.momentRHS n s) (Set.Icc (aRow τ) 1) := by
      rw [hcast]
      exact contDiffOn_momentErrorF n hh hX hY hfhat
    have hd : ∀ s ∈ Set.Ioo (aRow τ) 1,
        iteratedDerivWithin (n + 1)
          (fun u : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat u
            - RyaboginVolterra.momentRHS n u) (Set.Icc (aRow τ) 1) s = 0 := by
      intro s hs
      have hcont : ContDiffAt ℝ (n + 1)
          (fun u : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat u
            - RyaboginVolterra.momentRHS n u) s :=
        hF.contDiffAt (Icc_mem_nhds hs.1 hs.2)
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq hcont ⟨hs.1.le, hs.2.le⟩, hMerr s hs]
    have hz : (fun s : ℝ => RyaboginVolterra.momentF n (ε • h) X Y fhat s
          - RyaboginVolterra.momentRHS n s) =ᶠ[𝓝 c'] 0 := by
      filter_upwards [Ioo_mem_nhds hcc' hc'1] with s hs
      simp only [Pi.sub_apply, hbaseF s hs, sub_self, Pi.zero_apply]
    have h := Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
      n hac' hc'1 hF hd hz
    intro s hs
    have hs' := h s hs
    simpa only [Pi.sub_apply, sub_eq_zero] using hs'
  · have hcastH : (((n - 1 : ℕ)) : ℕ∞ω) + 1 = ((n : ℕ) : ℕ∞ω) := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
    have hFn : ContDiffOn ℝ (n : ℕ∞ω)
        (fun s : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat s) (Set.Icc (aRow τ) 1) :=
      contDiffOn_momentErrorH n hh hX hY (hfhat.of_le hlen)
    have hF : ContDiffOn ℝ ((((n - 1 : ℕ)) : ℕ∞ω) + 1)
        (fun s : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat s) (Set.Icc (aRow τ) 1) := by
      rw [hcastH]
      exact hFn
    have hd : ∀ s ∈ Set.Ioo (aRow τ) 1,
        iteratedDerivWithin ((n - 1) + 1)
          (fun u : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat u)
          (Set.Icc (aRow τ) 1) s = 0 := by
      intro s hs
      have hk : ((n - 1) + 1 : ℕ) = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
      rw [hk]
      have hcont : ContDiffAt ℝ n
          (fun u : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat u) s :=
        hFn.contDiffAt (Icc_mem_nhds hs.1 hs.2)
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq hcont ⟨hs.1.le, hs.2.le⟩]
      exact hHerr s hs
    have hz : (fun s : ℝ => RyaboginVolterra.momentH n (ε • h) X Y fhat s) =ᶠ[𝓝 c'] 0 := by
      filter_upwards [Ioo_mem_nhds hcc' hc'1] with s hs
      simpa only [Pi.zero_apply] using hbaseH s hs
    exact Commons.Analysis.Calculus.eq_zero_of_iteratedDerivWithin_eq_zero_of_eventuallyEq_zero
      (n - 1) hac' hc'1 hF hd hz

end Commons.Geometry.Ulam
end

-- ===== FILE _step3.lean =====

namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped Interval ContDiff Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-!
## Ryabogin's Step 3 at finite smoothness of `f`

The commons lemma `returns_to_semicircle_of_moment_eqs` asks for `ContDiff ℝ ∞ f`, but its proof
only ever uses the *continuity* of `f` (the `f`-dependence of the differentiated integrand is
`t ↦ f t ^ 2`, a constant in the differentiation variable `u`).  We reproduce the three derivative
lemmas and the theorem with the hypothesis `Continuous f`, so that the statement applies to the
`C^{n+2}` device `f̂` built in `_glob2.lean`.
-/

lemma hasDerivAt_momentIntegrand_cont {f h : ℝ → ℝ} (hf : Continuous f) (hh : ContDiff ℝ ∞ h)
    (m j : ℕ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
        (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j) u := by
  have h1 : HasDerivAt (fun v : ℝ => v * t) (t) u := by
    simpa using (hasDerivAt_id u).mul_const t
  have h2 : HasDerivAt h (deriv h u) u := (hh.differentiable (by simp) u).hasDerivAt
  have hlin : HasDerivAt (fun v : ℝ => v * t + h v) (t + deriv h u) u := h1.add h2
  have hsq : HasDerivAt (fun v : ℝ => (v * t + h v) ^ 2)
      (2 * (u * t + h u) * (t + deriv h u)) u := by
    have h3 := hlin.pow 2
    rw [show (↑(2:ℕ):ℝ) * (u * t + h u) ^ (2 - 1) * (t + deriv h u)
          = 2 * (u * t + h u) * (t + deriv h u) by norm_num] at h3
    exact h3
  have hg : HasDerivAt (fun v : ℝ => f t ^ 2 - (v * t + h v) ^ 2)
      (-(2 * (u * t + h u) * (t + deriv h u))) u := by
    have hc : HasDerivAt (fun _ : ℝ => f t ^ 2) 0 u := hasDerivAt_const u (f t ^ 2)
    have h3 := hc.sub hsq
    rw [show 0 - 2 * (u * t + h u) * (t + deriv h u)
          = -(2 * (u * t + h u) * (t + deriv h u)) by ring] at h3
    exact h3
  have hgp : HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m)
      ((m : ℝ) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) *
        (-(2 * (u * t + h u) * (t + deriv h u)))) u := hg.pow m
  have h4 := hgp.mul_const (t ^ j)
  rw [show (m : ℝ) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) *
        (-(2 * (u * t + h u) * (t + deriv h u))) * t ^ j
        = -(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
          (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j by ring] at h4
  exact h4

lemma momE_hasDerivAt_cont {f h x y : ℝ → ℝ} (hf : Continuous f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (m j : ℕ) (hm : 1 ≤ m) (s : ℝ)
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot_y : f (y s) ^ 2 = (s * y s + h s) ^ 2)
    (hroot_x : f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (fun u : ℝ => ∫ t in (-x u)..(y u), (f t ^ 2 - (u * t + h u) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * s * ∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (m - 1) * t ^ (j + 2)) s := by
  have hx_at : HasDerivAt x (deriv x s) s := (hx.differentiable (by simp) s).hasDerivAt
  have hy_at : HasDerivAt y (deriv y s) s := (hy.differentiable (by simp) s).hasDerivAt
  have hx_cont : ContinuousAt x s := hx.continuous.continuousAt
  have hy_cont : ContinuousAt y s := hy.continuous.continuousAt
  have hF_cont : Continuous (fun p : ℝ × ℝ => (f p.2 ^ 2 - (p.1 * p.2 + h p.1) ^ 2) ^ m * p.2 ^ j) := by
    fun_prop
  have hF'_cont : Continuous (fun p : ℝ × ℝ => -(2 * (m : ℝ)) * (p.1 * p.2 + h p.1) * (p.2 + deriv h p.1) *
        (f p.2 ^ 2 - (p.1 * p.2 + h p.1) ^ 2) ^ (m - 1) * p.2 ^ j) := by
    have hdh : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
    fun_prop
  have hisDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j) u :=
    fun u t => hasDerivAt_momentIntegrand_cont hf hh m j u t
  have key := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := fun u t => (f t ^ 2 - (u * t + h u) ^ 2) ^ m * t ^ j)
    (F' := fun u t => -(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
        (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j)
    (x := x) (y := y) hF_cont hF'_cont hisDeriv hx_at hy_at hx_cont hy_cont
  have hby : (f (y s) ^ 2 - (s * y s + h s) ^ 2) ^ m * (y s) ^ j = 0 := by
    rw [hroot_y, sub_self, zero_pow (by omega), zero_mul]
  have hbx : (f (-x s) ^ 2 - (s * (-x s) + h s) ^ 2) ^ m * (-x s) ^ j = 0 := by
    rw [hroot_x, sub_self, zero_pow (by omega), zero_mul]
  refine key.congr_deriv ?_
  rw [hby, hbx]
  simp only [zero_mul, sub_zero, zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [hhs, hdhs]
  rw [pow_add]
  ring

lemma momE_deriv_step_cont {f h x y : ℝ → ℝ} (hf : Continuous f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) {n k : ℕ} (hk : k + 1 ≤ n) {s : ℝ}
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot : f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (momE n f h x y k) (-(2 * ((n - k : ℕ) : ℝ)) * s * momE n f h x y (k + 1) s) s := by
  have hm : 1 ≤ n - k := by omega
  have hstep := momE_hasDerivAt_cont hf hh hx hy (n - k) (2 * k) hm s hhs hdhs hroot.1 hroot.2
  have hInt : (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (n - k - 1) * t ^ (2 * k + 2))
      = momE n f h x y (k + 1) s := by
    simp only [momE]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hhs]
    simp only [add_zero]
    have h1 : n - (k + 1) = n - k - 1 := by omega
    rw [h1]
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2]
  rw [hInt] at hstep
  exact hstep

lemma momO_deriv_step_cont {f h x y : ℝ → ℝ} (hf : Continuous f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) {n k : ℕ} (hk : k + 2 ≤ n) {s : ℝ}
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot : f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (momO n f h x y k) (-(2 * ((n - 1 - k : ℕ) : ℝ)) * s * momO n f h x y (k + 1) s) s := by
  have hm : 1 ≤ n - 1 - k := by omega
  have hstep := momE_hasDerivAt_cont hf hh hx hy (n - 1 - k) (2 * k + 1) hm s hhs hdhs hroot.1 hroot.2
  have hInt : (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (n - 1 - k - 1) * t ^ (2 * k + 1 + 2))
      = momO n f h x y (k + 1) s := by
    simp only [momO]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hhs]
    simp only [add_zero]
    have h1 : n - 1 - (k + 1) = n - 1 - k - 1 := by omega
    rw [h1]
    have h2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [h2]
  rw [hInt] at hstep
  exact hstep

/-- **The binomial relations at an anchor point.**  If the two moment identities hold on an open
set `U` on which `h` and `deriv h` vanish and `x = y = profileX`, and the two root conditions hold
there, then all the differentiated "binomial" relations hold on `U`. -/
lemma moment_relations_of_eqOn {n : ℕ} {f h x y : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hU0 : ∀ s ∈ U, s ≠ 0)
    (hf : Continuous f) (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hh0 : ∀ s ∈ U, h s = 0) (hdh : ∀ s ∈ U, deriv h s = 0)
    (hroot : ∀ s ∈ U, f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧
      f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hbaseE : Set.EqOn (momE n f h x y 0) (refE n 0) U)
    (hbaseO : Set.EqOn (momO n f h x y 0) 0 U) :
    (∀ k : ℕ, k ≤ n → Set.EqOn (momE n f h x y k) (refE n k) U) ∧
      (∀ k : ℕ, k ≤ n - 1 → Set.EqOn (momO n f h x y k) 0 U) := by
  have hE : ∀ k, k ≤ n → Set.EqOn (momE n f h x y k) (refE n k) U := by
    intro k
    induction k with
    | zero => intro _; exact hbaseE
    | succ k ih =>
        intro hk
        have ihk := ih (le_trans (Nat.le_succ k) hk)
        intro s hsU
        have hmem : U ∈ 𝓝 s := hU.mem_nhds hsU
        have hev : (momE n f h x y k) =ᶠ[𝓝 s] (refE n k) := ihk.eventuallyEq_of_mem hmem
        have hstepE := momE_deriv_step_cont (f := f) (h := h) (x := x) (y := y) (n := n) (k := k)
          hf hh hx hy hk (hh0 s hsU) (hdh s hsU) (hroot s hsU)
        have hstepR := refE_deriv_step (n := n) (k := k) hk s
        have hD := hstepE.unique (hstepR.congr_of_eventuallyEq hev)
        have hsne : s ≠ 0 := hU0 s hsU
        have hnk : ((n - k : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : n - k ≠ 0)
        have hc : -(2 * ((n - k : ℕ) : ℝ)) * s ≠ 0 := by
          exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnk)) hsne
        exact mul_left_cancel₀ hc hD
  have hO : ∀ k, k ≤ n - 1 → Set.EqOn (momO n f h x y k) 0 U := by
    intro k
    induction k with
    | zero => intro _; exact hbaseO
    | succ k ih =>
        intro hk
        have ihk := ih (le_trans (Nat.le_succ k) hk)
        intro s hsU
        have hmem : U ∈ 𝓝 s := hU.mem_nhds hsU
        have hev : (momO n f h x y k) =ᶠ[𝓝 s] 0 := ihk.eventuallyEq_of_mem hmem
        have hstep := momO_deriv_step_cont (f := f) (h := h) (x := x) (y := y) (n := n) (k := k)
          hf hh hx hy (by omega : k + 2 ≤ n) (hh0 s hsU) (hdh s hsU) (hroot s hsU)
        have hstep0 : HasDerivAt (momO n f h x y k) 0 s :=
          (hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq hev
        have hD := hstep.unique hstep0
        have hsne : s ≠ 0 := hU0 s hsU
        have hnk : ((n - 1 - k : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : n - 1 - k ≠ 0)
        have hc : -(2 * ((n - 1 - k : ℕ) : ℝ)) * s ≠ 0 := by
          exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnk)) hsne
        exact (mul_eq_zero.mp hD).resolve_left hc
  exact ⟨hE, hO⟩

/-- **Step 3 of Ryabogin's even-dimensional construction, finite-smoothness form.**  On an interval
`[A,B]` on which `h` vanishes identically (in a whole neighbourhood) the moment equations force
`x` and `y` back to the semicircle values `profileX`.  Same proof as the commons
`returns_to_semicircle_of_moment_eqs` but with `ContDiff ℝ ∞ f` weakened to `Continuous f` (which
is all that the parametric differentiation uses). -/
theorem returns_to_semicircle_cont
    (n : ℕ) (hn : 2 ≤ n) {x y f h : ℝ → ℝ} {A B ε : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hAB : A < B)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (hf : Continuous f)
    (hh : ContDiff ℝ ∞ h)
    (hh0 : ∀ s ∈ Set.Icc (A - ε) (B + ε), h s = 0)
    (hxpos : ∀ s ∈ Set.Icc (A - ε) (B + ε), 0 < x s)
    (hypos : ∀ s ∈ Set.Icc (A - ε) (B + ε), 0 < y s)
    (hroot : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hF : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hH : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s ∈ Set.Icc A B, x s = profileX s ∧ y s = profileX s := by
  let U : Set ℝ := Set.Ioo (A - ε) (B + ε) ∩ Set.Ioi 0
  have hUopen : IsOpen U := isOpen_Ioo.inter isOpen_Ioi
  have hU0 : ∀ s ∈ U, s ≠ 0 := fun s hs => ne_of_gt hs.2
  have hUB : ∀ s ∈ U, s ∈ Set.Icc (A - ε) (B + ε) :=
    fun s hs => Set.Ioo_subset_Icc_self hs.1
  have hdh : ∀ s ∈ U, deriv h s = 0 := by
    intro s hs
    have hmem : U ∈ 𝓝 s := hUopen.mem_nhds hs
    have hev : h =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
      filter_upwards [hmem] with u hu
      exact hh0 u (hUB u hu)
    rw [hev.deriv_eq]
    simp
  have hABU : Set.Icc A B ⊆ U := by
    intro s hs
    have h3 : 0 < s := lt_of_lt_of_le hA hs.1
    have h1 : A - ε < s := by linarith [hε, hs.1]
    have h2 : s < B + ε := by linarith [hs.2, hAB, hε]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hbaseE : Set.EqOn (momE n f h x y 0) (refE n 0) U := by
    intro s hs
    have hthis := hF s (hUB s hs)
    simpa [momE, refE] using hthis
  have hbaseO : Set.EqOn (momO n f h x y 0) 0 U := by
    intro s hs
    have hthis := hH s (hUB s hs)
    rw [hdh s hs] at hthis
    simpa [momO] using hthis
  obtain ⟨hE, hO⟩ := moment_relations_of_eqOn hUopen hU0 hf hh hx hy
    (fun s hs => hh0 s (hUB s hs)) hdh (fun s hs => hroot s (hUB s hs)) hbaseE hbaseO
  intro s hsAB
  have hsU := hABU hsAB
  have hsI := hUB s hsU
  have hspos : 0 < s := hsU.2
  have hEn := (hE n le_rfl) hsU
  have hOn := (hO (n - 1) le_rfl) hsU
  have hEn2 : (∫ t in (-x s)..(y s), t^(2*n))
      = (∫ t in (-(1/Real.sqrt (1 + s^2)))..(1/Real.sqrt (1+s^2)), t^(2*n)) := by
    have h := hEn
    simpa only [momE, refE, Nat.sub_self, pow_zero, one_mul] using h
  have hOn2 : (∫ t in (-x s)..(y s), t^(2*n-1)) = 0 := by
    have h := hOn
    simp only [momO, Nat.sub_self, pow_zero, one_mul] at h
    have h2n : 2*(n-1)+1 = 2*n-1 := by omega
    rw [h2n] at h
    exact h
  have h1 : (y s)^(2*n+1) + (x s)^(2*n+1) = 2*(profileX s)^(2*n+1) := by
    have hd : (2*(n:ℝ) + 1) ≠ 0 := by positivity
    have hthis := hEn2
    rw [integral_pow_even (x s) (y s) n, integral_pow_sym (1/Real.sqrt (1+s^2)) n] at hthis
    rw [div_eq_div_iff hd hd] at hthis
    have hcancel := mul_right_cancel₀ hd hthis
    simpa [profileX] using hcancel
  have h2 : (y s)^(2*n) = (x s)^(2*n) := by
    have hd : (2*(n:ℝ)) ≠ 0 := by positivity
    have hz : (y s)^(2*n) - (x s)^(2*n) = 0 := by
      have hthis := hOn2
      rw [integral_pow_odd (x s) (y s) n (by omega)] at hthis
      rcases (div_eq_zero_iff.mp hthis) with h | h
      · exact h
      · exact absurd h hd
    exact sub_eq_zero.mp hz
  exact final_conclusion (hxpos s hsI) (hypos s hsI) (profileX_pos s hspos) (by omega) h1 h2

/-- The binomial relations at a single anchor point (pointwise form of
`moment_relations_of_eqOn`). -/
lemma moment_relations_at {n : ℕ} {f h x y : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hU0 : ∀ s ∈ U, s ≠ 0)
    (hf : Continuous f) (hh : ContDiff ℝ ∞ h) (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hh0 : ∀ s ∈ U, h s = 0) (hdh : ∀ s ∈ U, deriv h s = 0)
    (hroot : ∀ s ∈ U, f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧
      f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hbaseE : Set.EqOn (momE n f h x y 0) (refE n 0) U)
    (hbaseO : Set.EqOn (momO n f h x y 0) 0 U)
    {s : ℝ} (hs : s ∈ U) :
    (∀ k : ℕ, k ≤ n → momE n f h x y k s = refE n k s) ∧
      (∀ k : ℕ, k ≤ n - 1 → momO n f h x y k s = 0) := by
  obtain ⟨hE, hO⟩ := moment_relations_of_eqOn hU hU0 hf hh hx hy hh0 hdh hroot hbaseE hbaseO
  exact ⟨fun k hk => hE k hk hs, fun k hk => hO k hk hs⟩

end

end Commons.Geometry.Ulam

-- ===== FILE _asm.lean =====

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma profileX_one_lt : profileX 1 < 1 := by
  have h : (1 : ℝ) < Real.sqrt (1 + 1 ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [profileX]
  exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr h

/-- `h` vanishes on `s ≤ 1 - 2 τ` (using flatness at the left endpoint of the window). -/
lemma h_eq_zero_of_le {τ η : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hflat : ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0)
    (hη : 0 < η) {s : ℝ} (hs : s ≤ 1 - 2 * τ) : h s = 0 := by
  rcases lt_or_eq_of_le hs with h | h
  · by_contra hne
    have hmem := hsupp (by simpa [Function.mem_support] using hne)
    exact absurd hmem.1 (not_le.mpr h)
  · subst h
    exact hflat _ le_rfl (by linarith)

/-- `h` vanishes on `1 - τ ≤ s`. -/
lemma h_eq_zero_of_ge {τ : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {s : ℝ} (hs : 1 - τ ≤ s) : h s = 0 := by
  have hright : ∀ t : ℝ, 1 - τ < t → h t = 0 := by
    intro t ht
    by_contra hne
    have hmem := hsupp (by simpa [Function.mem_support] using hne)
    exact absurd hmem.2 (not_le.mpr ht)
  rcases lt_or_eq_of_le hs with h | h
  · exact hright s h
  · subst h
    have hev : (fun t : ℝ => h t) =ᶠ[𝓝[Set.Ioi (1 - τ)] (1 - τ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hright t (Set.mem_Ioi.mp ht)
    have h1 : Filter.Tendsto (fun t : ℝ => h t) (𝓝[Set.Ioi (1 - τ)] (1 - τ)) (𝓝 0) :=
      tendsto_const_nhds.congr' hev.symm
    have h2 : Filter.Tendsto (fun t : ℝ => h t) (𝓝[Set.Ioi (1 - τ)] (1 - τ)) (𝓝 (h (1 - τ))) :=
      hh.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h2 h1

/-- `deriv h` vanishes at every point where `h` vanishes on a neighbourhood. -/
lemma deriv_h_eq_zero_of_nhds {h : ℝ → ℝ} {s : ℝ}
    (hev : h =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ))) : deriv h s = 0 := by
  have hd := hev.deriv_eq
  simpa using hd

end Commons.Geometry.Ulam

-- ===== FILE _mine_dev1.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Family smoothness of the `G`-data in the scale parameter `a` of `a • h`. -/
lemma contDiff_G_family (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2) := by
  have hcoe : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × VS) =>
      ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · have hG0 : (fun q : ℝ × (ℝ × VS) =>
          ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ) 0)
          = fun q : ℝ × (ℝ × VS) => q.2.2 0 := by
        funext q; exact G_apply_zero n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [hG0]; fun_prop
    · have hG1 : (fun q : ℝ × (ℝ × VS) =>
          ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ) 1)
          = fun q : ℝ × (ℝ × VS) => q.2.2 1 := by
        funext q; exact G_apply_one n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [hG1]; fun_prop
    · have hG2 : (fun q : ℝ × (ℝ × VS) =>
          ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ) 2)
          = fun q : ℝ × (ℝ × VS) => (-2:ℝ)^n * (n.factorial : ℝ) *
              (((RyaboginVolterra.line (fun u : ℝ => q.1 * h u) q.2.1 (-(q.2.2 0))) *
                  (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (-(q.2.2 0))))^n * q.2.2 2
                + ((RyaboginVolterra.line (fun u : ℝ => q.1 * h u) q.2.1 (q.2.2 1)) *
                  (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (q.2.2 1)))^n * q.2.2 3) := by
        funext q; exact G_apply_two n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [hG2]
      simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope]
      have hdv : ∀ a s : ℝ, deriv (fun u : ℝ => a * h u) s = a * deriv h s :=
        fun a s => deriv_const_mul_field a
      simp only [hdv]
      fun_prop
    · have hG3 : (fun q : ℝ × (ℝ × VS) =>
          ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ) 3)
          = fun q : ℝ × (ℝ × VS) => (-2:ℝ)^(n-1) * ((n-1).factorial : ℝ) *
              (((RyaboginVolterra.line (fun u : ℝ => q.1 * h u) q.2.1 (-(q.2.2 0))) *
                  (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (-(q.2.2 0))))^(n-1)
                  * (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (-(q.2.2 0))) * q.2.2 2
                + ((RyaboginVolterra.line (fun u : ℝ => q.1 * h u) q.2.1 (q.2.2 1)) *
                  (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (q.2.2 1)))^(n-1)
                  * (RyaboginVolterra.lineSlope (fun u : ℝ => q.1 * h u) q.2.1 (q.2.2 1)) * q.2.2 3) := by
        funext q; exact G_apply_three n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2
      simp only [Fin.isValue, Fin.reduceFinMk]
      rw [hG3]
      simp only [RyaboginVolterra.line, RyaboginVolterra.lineSlope]
      have hdv : ∀ a s : ℝ, deriv (fun u : ℝ => a * h u) s = a * deriv h s :=
        fun a s => deriv_const_mul_field a
      simp only [hdv]
      fun_prop
  have h2 : (fun q : ℝ × (ℝ × VS) =>
        ((RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2 : VS) : Fin 4 → ℝ)) =
      ((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘
        (fun q : ℝ × (ℝ × VS) => RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2) := rfl
  rw [h2] at hcoe
  have h4 : ContDiff ℝ ∞ ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff
  have h5 := h4.comp hcoe
  have hfun : ((EuclideanSpace.equiv (Fin 4) ℝ).symm : (Fin 4 → ℝ) → VS) ∘
      (((EuclideanSpace.equiv (Fin 4) ℝ) : VS → (Fin 4 → ℝ)) ∘
        (fun q : ℝ × (ℝ × VS) => RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2)) =
      (fun q : ℝ × (ℝ × VS) => RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2) := by
    funext q; simp
  rw [hfun] at h5
  exact h5

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev2.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Differentiating the unscaled Volterra identity in `s`, in the form needed for the `C²`
estimate.  `Z` is the (unscaled) state, `a` the scale of the bump. -/
lemma unscaled_deriv_identity (n : ℕ) {a u₀ s : ℝ} {h : ℝ → ℝ} {Z : ℝ → VS}
    (hZc : Continuous Z)
    (hZ : HasDerivAt Z (deriv Z s) s)
    (hG : ContDiff ℝ ∞ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2))
    (hK : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) Set.univ)
    (hXid : DifferentiableAt ℝ (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s)
    (hid : ∀ u ∈ Set.Icc u₀ 1,
      RyaboginVolterra.G n (a • h) u (Z u)
        = (∫ σ in u..1, RyaboginVolterra.Theta n (a • h) u σ (Z σ))
          + RyaboginVolterra.Xi n (a • h) u)
    (hs : s ∈ Set.Ioo u₀ 1) :
    (fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, Z s))
        ((1 : ℝ), deriv Z s)
      = - RyaboginVolterra.Theta n (a • h) s s (Z s)
        + (∫ σ in s..1, fderiv ℝ
            (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2)
            (s, σ, Z σ) ((1 : ℝ), (0 : ℝ), (0 : VS)))
        + deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s := by
  have h1 : HasDerivAt (fun u : ℝ => RyaboginVolterra.G n (a • h) u (Z u))
      ((fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, Z s))
        ((1 : ℝ), deriv Z s)) s := by
    have hf : HasFDerivAt (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2)
        (fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, Z s))
        (s, Z s) :=
      (hG.differentiable (by simp) (s, Z s)).hasFDerivAt
    have hc : HasDerivAt (fun u : ℝ => (u, Z u)) ((1 : ℝ), deriv Z s) s :=
      (hasDerivAt_id s).prodMk hZ
    exact hf.comp_hasDerivAt s hc
  have h2 : HasDerivAt
      (fun u : ℝ => (∫ σ in u..1, RyaboginVolterra.Theta n (a • h) u σ (Z σ))
        + RyaboginVolterra.Xi n (a • h) u)
      (- RyaboginVolterra.Theta n (a • h) s s (Z s)
        + (∫ σ in s..1, fderiv ℝ
            (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2)
            (s, σ, Z σ) ((1 : ℝ), (0 : ℝ), (0 : VS)))
        + deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s) s := by
    have hint := Commons.Analysis.Calculus.volterraFixedPoint_hasDerivAt_volterra_integral_ext (a := (0:ℝ)) (b := (1 : ℝ)) (s := s)
      (K := fun u σ z => RyaboginVolterra.Theta n (a • h) u σ z) (w := Z) hK hZc
    exact hint.add hXid.hasDerivAt
  have heq : (fun u : ℝ => RyaboginVolterra.G n (a • h) u (Z u)) =ᶠ[𝓝 s]
      (fun u : ℝ => (∫ σ in u..1, RyaboginVolterra.Theta n (a • h) u σ (Z σ))
        + RyaboginVolterra.Xi n (a • h) u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact hid u ⟨hu.1.le, hu.2.le⟩
  exact ((h2.congr_of_eventuallyEq heq).unique h1).symm

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev3.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The `s`-partial of the `G`-data, `∂_s G(a)(s,z)`. -/
noncomputable def GsPart (n : ℕ) (a s : ℝ) (h : ℝ → ℝ) (z : VS) : VS :=
  (fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z))
    ((1 : ℝ), (0 : VS))

/-- The state-derivative of the `G`-data, `D_z G(a)(s,z)`. -/
noncomputable def GzPart (n : ℕ) (a s : ℝ) (h : ℝ → ℝ) (z : VS) : VS →L[ℝ] VS :=
  fderiv ℝ (fun w : VS => RyaboginVolterra.G n (a • h) s w) z

/-- The right-hand side `R` of the differentiated identity. -/
noncomputable def Rterm (n : ℕ) (a s : ℝ) (h : ℝ → ℝ) (Z : ℝ → VS) : VS :=
  - RyaboginVolterra.Theta n (a • h) s s (Z s)
    + (∫ σ in s..1, fderiv ℝ
        (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2)
        (s, σ, Z σ) ((1 : ℝ), (0 : ℝ), (0 : VS)))
    + deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s

/-- The state-partial of the full differential: `FZ (0, w) = D_z G w`. -/
lemma fderiv_pair_inr_apply (n : ℕ) {a s : ℝ} {h : ℝ → ℝ} {z w : VS}
    (hG : DifferentiableAt ℝ
      (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z)) :
    (fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z))
        ((0 : ℝ), w)
      = GzPart n a s h z w := by
  rw [GzPart, Commons.Analysis.Calculus.volterraFixedPoint_fderiv_partial_eq_comp_inr hG,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The linear decomposition of the differential at the solution. -/
lemma fderiv_pair_apply_eq (n : ℕ) {a s : ℝ} {h : ℝ → ℝ} {z w : VS}
    (hG : DifferentiableAt ℝ
      (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z)) :
    (fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z))
        ((1 : ℝ), w)
      = GsPart n a s h z + GzPart n a s h z w := by
  set F := fderiv ℝ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, z) with hF
  have hsplit : ((1 : ℝ), w) = ((1 : ℝ), (0 : VS)) + ((0 : ℝ), w) := by simp
  rw [hsplit, map_add]
  have h1 : F ((1 : ℝ), (0 : VS)) = GsPart n a s h z := by
    rw [hF, GsPart]
  have h2 : F ((0 : ℝ), w) = GzPart n a s h z w := by
    rw [hF]; exact fderiv_pair_inr_apply n hG
  rw [h1, h2]

/-- **Equation for the derivative of the state.**  From the differentiated identity we get a
*linear* equation for `deriv Z s`. -/
lemma deriv_state_eq (n : ℕ) {a u₀ s : ℝ} {h : ℝ → ℝ} {Z : ℝ → VS}
    (hZc : Continuous Z)
    (hZ : HasDerivAt Z (deriv Z s) s)
    (hG : ContDiff ℝ ∞ (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2))
    (hK : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) Set.univ)
    (hXid : DifferentiableAt ℝ (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s)
    (hid : ∀ u ∈ Set.Icc u₀ 1,
      RyaboginVolterra.G n (a • h) u (Z u)
        = (∫ σ in u..1, RyaboginVolterra.Theta n (a • h) u σ (Z σ))
          + RyaboginVolterra.Xi n (a • h) u)
    (hs : s ∈ Set.Ioo u₀ 1) :
    GzPart n a s h (Z s) (deriv Z s) = Rterm n a s h Z - GsPart n a s h (Z s) := by
  have hident := unscaled_deriv_identity (n := n) hZc hZ hG hK hXid hid hs
  have hdiff : DifferentiableAt ℝ
      (fun p : ℝ × VS => RyaboginVolterra.G n (a • h) p.1 p.2) (s, Z s) :=
    (hG.differentiable (by simp) (s, Z s))
  have hdecomp := fderiv_pair_apply_eq (n := n) (a := a) (h := h) (z := Z s) (w := deriv Z s) hdiff
  rw [hdecomp] at hident
  rw [Rterm]
  linear_combination (norm := module) hident

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev4.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **Comparison of the derivative of the state with the base state.**  From the two *linear*
equations for `deriv Z s` and `deriv baseZ s`, plus invertibility of the state-partial at
`(a, s, Z s)`, we get the bound on `deriv Z s - deriv baseZ s`. -/
lemma deriv_diff_bound (n : ℕ) {a s B : ℝ} {h : ℝ → ℝ} {Z : ℝ → VS}
    (hDinv : ∃ e : VS ≃L[ℝ] VS,
      (∀ v : VS, e v = GzPart n a s h (Z s) v) ∧ ‖(e.symm : VS →L[ℝ] VS)‖ ≤ B)
    (h1 : GzPart n a s h (Z s) (deriv Z s) = Rterm n a s h Z - GsPart n a s h (Z s))
    (h2 : GzPart n 0 s h (baseZ s) (deriv baseZ s)
      = Rterm n 0 s h baseZ - GsPart n 0 s h (baseZ s)) :
    ‖deriv Z s - deriv baseZ s‖ ≤
      B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖) := by
  obtain ⟨e, he, hB⟩ := hDinv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hB
  have hDw₀ : GzPart n a s h (Z s) (deriv baseZ s)
      = (GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)
        + (Rterm n 0 s h baseZ - GsPart n 0 s h (baseZ s)) := by
    rw [ContinuousLinearMap.sub_apply, h2]; abel
  have key : e (deriv Z s - deriv baseZ s)
      = (Rterm n a s h Z - Rterm n 0 s h baseZ)
        - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))
        - (GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s) := by
    rw [map_sub, he (deriv Z s), h1, he (deriv baseZ s), hDw₀]; abel
  have hxeq : deriv Z s - deriv baseZ s
      = e.symm ((Rterm n a s h Z - Rterm n 0 s h baseZ)
        - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))
        - (GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)) := by
    rw [← key, ContinuousLinearEquiv.symm_apply_apply]
  have h3 : ‖(Rterm n a s h Z - Rterm n 0 s h baseZ)
        - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))
        - (GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖
      ≤ ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ := by
    have h4 : ‖(Rterm n a s h Z - Rterm n 0 s h baseZ)
        - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))‖
        ≤ ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
          + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖ := norm_sub_le _ _
    calc ‖(Rterm n a s h Z - Rterm n 0 s h baseZ)
          - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))
          - (GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖
        ≤ ‖(Rterm n a s h Z - Rterm n 0 s h baseZ)
            - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))‖
          + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ :=
          norm_sub_le _ _
      _ ≤ (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
            + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖)
          + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ :=
          add_le_add h4 le_rfl
      _ = ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
            + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
            + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ := by
          ring
  rw [hxeq]
  refine le_trans (ContinuousLinearMap.le_opNorm (e.symm : VS →L[ℝ] VS) _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) ?_
  exact mul_le_mul_of_nonneg_left h3 hB0

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev5.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- At scale `0` the state-partial of the `G`-data is the derivative of `baseG` at the base point. -/
lemma GzPart_zero_apply (n : ℕ) {s : ℝ} {h : ℝ → ℝ} (v : VS) :
    GzPart n 0 s h (baseZ s) v = (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v := by
  have h0 : ((0 : ℝ) • h) = fun _ : ℝ => (0 : ℝ) := by funext u; simp
  rw [GzPart, h0]
  rfl

/-- **Uniform bound on the inverse of the base linearisation** on `[α, 1]`. -/
lemma base_inverse_bound (n : ℕ) (hn : 2 ≤ n) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : ℝ → ℝ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ s ∈ Set.Icc α 1, ∃ e : VS ≃L[ℝ] VS,
      (∀ v : VS, e v = GzPart n 0 s h (baseZ s) v) ∧ ‖(e.symm : VS →L[ℝ] VS)‖ ≤ B₀ := by
  obtain ⟨K1, hK1pos, hK1⟩ := exists_norm_iaLin_le n hα hα1
  refine ⟨max K1 1, lt_of_lt_of_le hK1pos (le_max_left _ _), ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le hα hs.1
  refine ⟨jacEquiv n hs0, ?_, ?_⟩
  · intro v
    rw [jacEquiv_apply n hs0 v]
    have h2 : (fderiv ℝ (fun z : VS => baseG n s z) (baseZ s)) v = jacLin n s v := by
      have h3 := congrArg (fun (L : VS →L[ℝ] VS) => L v) (jacLin_eq_fderiv hn s)
      simpa using h3.symm
    rw [← h2]
    exact (GzPart_zero_apply (n := n) (s := s) (h := h) v).symm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    have h1 : ((jacEquiv n hs0).symm : VS →L[ℝ] VS) v = iaLin n s v :=
      jacEquiv_symm_apply n hs0 v
    rw [h1]
    calc ‖iaLin n s v‖ ≤ K1 * ‖v‖ := hK1 s hs v
      _ ≤ max K1 1 * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Base instance of the differentiated identity** (scale `0`, state `baseZ`). -/
lemma base_deriv_eq (n : ℕ) (hn : 2 ≤ n) {h : ℝ → ℝ} {u₀ s : ℝ}
    (ha : 0 < u₀) (ha1 : u₀ ≤ 1) (hs : s ∈ Set.Ioo u₀ 1) :
    GzPart n 0 s h (baseZ s) (deriv baseZ s) = Rterm n 0 s h baseZ - GsPart n 0 s h (baseZ s) := by
  have h0 : ((0 : ℝ) • h) = fun _ : ℝ => (0 : ℝ) := by funext u; simp
  have hG : ContDiff ℝ ∞ (fun p : ℝ × VS => RyaboginVolterra.G n ((0 : ℝ) • h) p.1 p.2) := by
    rw [h0]
    exact contDiff_G_pair n (h := fun _ : ℝ => (0 : ℝ)) contDiff_const
  have hK : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × VS =>
      RyaboginVolterra.Theta n ((0 : ℝ) • h) p.1 p.2.1 p.2.2) Set.univ := by
    rw [h0]
    exact (contDiff_Theta_curried n (h := fun _ : ℝ => (0 : ℝ)) contDiff_const).contDiffOn
  have hXid : DifferentiableAt ℝ (fun u : ℝ => RyaboginVolterra.Xi n ((0 : ℝ) • h) u) s := by
    rw [h0]
    exact (contDiff_Xi n (h := fun _ : ℝ => (0 : ℝ)) contDiff_const).differentiable (by simp) s
  have hid : ∀ u ∈ Set.Icc u₀ 1,
      RyaboginVolterra.G n ((0 : ℝ) • h) u (baseZ u)
        = (∫ σ in u..1, RyaboginVolterra.Theta n ((0 : ℝ) • h) u σ (baseZ σ))
          + RyaboginVolterra.Xi n ((0 : ℝ) • h) u := by
    intro u hu
    rw [h0]
    simpa [baseZ] using volterra_base_identity n hn ha ha1 u hu
  exact deriv_state_eq (n := n) (a := 0) (u₀ := u₀) (h := h) (Z := baseZ)
    contDiff_baseZ.continuous (contDiff_baseZ.differentiable (by simp) s).hasDerivAt
    hG hK hXid hid hs

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev6.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **Uniform continuity on a compact set, in the form used below.** -/
lemma uniform_close_continuous_compact {P E : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup E]
    {Φ : ℝ × P → E} (hΦ : Continuous Φ) {K : Set (ℝ × P)} (hK : IsCompact K) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → ‖Φ x - Φ y‖ ≤ η := by
  intro η hη
  have huc := hK.uniformContinuousOn_of_continuous hΦ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (η / 2) (by linarith)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have h := hδ' x hx y hy hxy
  rw [dist_eq_norm] at h
  linarith

/-- The tube of radius `ρ₀` around the base state over `[α,1]` is compact. -/
lemma isCompact_tube {α ρ₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hρ₀ : 0 ≤ ρ₀) :
    IsCompact {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} := by
  have hK : IsCompact (Set.Icc α 1 ×ˢ Metric.closedBall (0 : VS) ρ₀) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hψ : Continuous (fun q : ℝ × VS => (q.1, baseZ q.1 + q.2)) :=
    continuous_fst.prodMk ((continuous_baseZ.comp continuous_fst).add continuous_snd)
  have himg : (fun q : ℝ × VS => (q.1, baseZ q.1 + q.2)) '' (Set.Icc α 1 ×ˢ Metric.closedBall (0:VS) ρ₀)
      = {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} := by
    ext p
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      refine ⟨hq1, ?_⟩
      have hq2' : ‖q.2‖ ≤ ρ₀ := by simpa [Metric.mem_closedBall, dist_zero_right] using hq2
      have : baseZ q.1 + q.2 - baseZ q.1 = q.2 := by abel
      rw [this]; exact hq2'
    · rintro ⟨hp1, hp2⟩
      refine ⟨(p.1, p.2 - baseZ p.1), ⟨hp1, ?_⟩, ?_⟩
      · simp only [Metric.mem_closedBall, dist_zero_right]; exact hp2
      · exact Prod.ext rfl (by simp)
  rw [← himg]
  exact hK.image hψ

/-- Joint smoothness of the `G`-family in the scale parameter. -/
lemma contDiff_G_joint (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) := by
  have h1 := contDiff_G_family n hh
  have heq : (fun q : ℝ × (ℝ × VS) =>
        RyaboginVolterra.G n (fun u : ℝ => q.1 * h u) q.2.1 q.2.2)
      = fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2 := by
    funext q
    have h2 : (fun u : ℝ => q.1 * h u) = (q.1 • h) := by
      funext u; simp [Pi.smul_apply, smul_eq_mul]
    rw [h2]
  rw [← heq]
  exact h1

/-- **The differential of the `G`-family is uniformly close to the base one** for small scale and
a nearby state. -/
lemma joint_fderiv_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ z : VS, ‖z - baseZ s‖ ≤ ρ →
        ‖fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
            RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))
          - fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
              RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (0, (s, baseZ s))‖ ≤ η := by
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀}) :=
    isCompact_Icc.prod (isCompact_tube hα hα1 (le_of_lt hρ₀))
  have hcont : Continuous (fun p : ℝ × (ℝ × VS) => fderiv ℝ
      (fun q : ℝ × (ℝ × VS) => RyaboginVolterra.G n (q.1 • h) q.2.1 q.2.2) p) :=
    (contDiff_G_joint n hh).continuous_fderiv (by simp)
  intro η hη
  obtain ⟨δ, hδpos, hδ⟩ := uniform_close_continuous_compact hcont hK η hη
  refine ⟨min 1 (δ/2), lt_min one_pos (by linarith), min ρ₀ (δ/2),
    lt_min hρ₀ (by linarith), min_le_left _ _, ?_⟩
  intro a ha s hs z hz
  have ha1 : a ≤ 1 := le_trans ha.2 (min_le_left _ _)
  have haδ : a < δ := lt_of_le_of_lt ha.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hzδ : ‖z - baseZ s‖ < δ :=
    lt_of_le_of_lt hz (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hx : (a, (s, z)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} :=
    ⟨⟨ha.1, ha1⟩, ⟨hs, le_trans hz (min_le_left _ _)⟩⟩
  have hy : ((0:ℝ), (s, baseZ s)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨hs, by simp [le_of_lt hρ₀]⟩⟩
  have hdist : dist (a, (s, z)) ((0:ℝ), (s, baseZ s)) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg ha.1, dist_self,
      dist_eq_norm]
    exact max_lt haδ (max_lt hδpos hzδ)
  exact hδ (a, (s, z)) hx ((0:ℝ), (s, baseZ s)) hy hdist

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev8.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The slice differential is the joint differential composed with `inr`** (general form, target
`VS`, arbitrary `P`). -/
lemma fderiv_slice_eq_comp_inr {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : ℝ × P → VS} {a : ℝ} {p : P} (hF : DifferentiableAt ℝ F (a, p)) :
    fderiv ℝ (fun q : P => F (a, q)) p
      = (fderiv ℝ F (a, p)).comp (ContinuousLinearMap.inr ℝ ℝ P) := by
  have hinc : HasFDerivAt (fun q : P => (a, q)) (ContinuousLinearMap.inr ℝ ℝ P) p := by
    have hc : HasFDerivAt (fun _ : P => (a, (0 : P))) (0 : P →L[ℝ] ℝ × P) p :=
      hasFDerivAt_const (a, (0 : P)) p
    have hl : HasFDerivAt (fun q : P => ((0 : ℝ), q)) (ContinuousLinearMap.inr ℝ ℝ P) p :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ ℝ P)
    have hsum := hc.add hl
    have hfun : (fun q : P => (a, (0 : P))) + (fun q : P => ((0 : ℝ), q)) = fun q : P => (a, q) := by
      funext q; simp
    have hder : (0 : P →L[ℝ] ℝ × P) + ContinuousLinearMap.inr ℝ ℝ P
        = ContinuousLinearMap.inr ℝ ℝ P := by simp
    rw [hfun, hder] at hsum
    exact hsum
  have := (hF.hasFDerivAt.comp p hinc).fderiv
  exact this

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev7.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- `GsPart` viewed through the joint differential in the scale. -/
lemma GsPart_eq_joint (n : ℕ) {a s : ℝ} {h : ℝ → ℝ} {z : VS}
    (hdiff : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))) :
    GsPart n a s h z = (fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z)))
        ((0 : ℝ), ((1 : ℝ), (0 : VS))) := by
  have hmain := fderiv_slice_eq_comp_inr
    (F := fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
    (a := a) (p := (s, z)) hdiff
  have h1 : GsPart n a s h z
      = ((fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
            RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))).comp
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × VS))) ((1 : ℝ), (0 : VS)) := by
    rw [GsPart]
    exact congrArg (fun (L : (ℝ × VS) →L[ℝ] VS) => L ((1 : ℝ), (0 : VS))) hmain
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- `GzPart` viewed through the joint differential in the scale. -/
lemma GzPart_eq_joint (n : ℕ) {a s : ℝ} {h : ℝ → ℝ} {z w : VS}
    (hdiff : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))) :
    GzPart n a s h z w = (fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z)))
        ((0 : ℝ), ((0 : ℝ), w)) := by
  have hmain := fderiv_slice_eq_comp_inr
    (F := fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
    (a := a) (p := (s, z)) hdiff
  have hslice : DifferentiableAt ℝ (fun p : ℝ × VS =>
      RyaboginVolterra.G n (a • h) p.1 p.2) (s, z) :=
    hdiff.comp (s, z) (by fun_prop)
  have h1 : GzPart n a s h z w
      = ((fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
            RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))).comp
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × VS))) ((0 : ℝ), w) := by
    rw [← fderiv_pair_inr_apply n hslice, hmain]
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev9.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma norm_pair_zero_one : ‖((0 : ℝ), ((1 : ℝ), (0 : VS)))‖ = 1 := by
  simp [Prod.norm_def, Real.norm_eq_abs]

lemma norm_pair_zero_zero (w : VS) : ‖((0 : ℝ), ((0 : ℝ), w))‖ = ‖w‖ := by
  simp [Prod.norm_def, Real.norm_eq_abs]

/-- **`GsPart` is uniformly close to the base one** for small scale and a nearby state. -/
lemma GsPart_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ z : VS,
        ‖z - baseZ s‖ ≤ ρ → ‖GsPart n a s h z - GsPart n 0 s h (baseZ s)‖ ≤ η := by
  intro η hη
  obtain ⟨a₀, ha₀, ρ, hρ, hρρ₀, hcl⟩ := joint_fderiv_close n hh hα hα1 hρ₀ η hη
  refine ⟨a₀, ha₀, ρ, hρ, hρρ₀, ?_⟩
  intro a ha s hs z hz
  have hd₁ : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z)) :=
    (contDiff_G_joint n hh).differentiable (by simp) (a, (s, z))
  have hd₂ : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (0, (s, baseZ s)) :=
    (contDiff_G_joint n hh).differentiable (by simp) (0, (s, baseZ s))
  rw [GsPart_eq_joint n hd₁, GsPart_eq_joint n hd₂]
  have hdiff := hcl a ha s hs z hz
  calc ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z))) ((0 : ℝ), ((1 : ℝ), (0 : VS)))
        - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s))) ((0 : ℝ), ((1 : ℝ), (0 : VS)))‖
      = ‖((fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))) ((0 : ℝ), ((1 : ℝ), (0 : VS)))‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))‖ * ‖((0 : ℝ), ((1 : ℝ), (0 : VS)))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))‖ := by rw [norm_pair_zero_one, mul_one]
    _ ≤ η := hdiff

/-- **`GzPart` is uniformly close to the base one** for small scale and a nearby state. -/
lemma GzPart_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ z w : VS,
        ‖z - baseZ s‖ ≤ ρ →
        ‖(GzPart n a s h z - GzPart n 0 s h (baseZ s)) w‖ ≤ η * ‖w‖ := by
  intro η hη
  obtain ⟨a₀, ha₀, ρ, hρ, hρρ₀, hcl⟩ := joint_fderiv_close n hh hα hα1 hρ₀ η hη
  refine ⟨a₀, ha₀, ρ, hρ, hρρ₀, ?_⟩
  intro a ha s hs z w hz
  have hd₁ : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z)) :=
    (contDiff_G_joint n hh).differentiable (by simp) (a, (s, z))
  have hd₂ : DifferentiableAt ℝ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (0, (s, baseZ s)) :=
    (contDiff_G_joint n hh).differentiable (by simp) (0, (s, baseZ s))
  have hm₁ : GzPart n a s h z = ((fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
        RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (a, (s, z))).comp
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × VS))).comp
            (ContinuousLinearMap.inr ℝ ℝ VS) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact GzPart_eq_joint (n := n) (hdiff := hd₁)
  have hm₂ : GzPart n 0 s h (baseZ s) = ((fderiv ℝ (fun p : ℝ × (ℝ × VS) =>
        RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2) (0, (s, baseZ s))).comp
          (ContinuousLinearMap.inr ℝ ℝ (ℝ × VS))).comp
            (ContinuousLinearMap.inr ℝ ℝ VS) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact GzPart_eq_joint (n := n) (hdiff := hd₂)
  rw [hm₁, hm₂, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.inr_apply]
  have hdiff := hcl a ha s hs z hz
  calc ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z))) ((0 : ℝ), ((0 : ℝ), w))
        - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s))) ((0 : ℝ), ((0 : ℝ), w))‖
      = ‖((fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))) ((0 : ℝ), ((0 : ℝ), w))‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))‖ * ‖((0 : ℝ), ((0 : ℝ), w))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (a, (s, z)))
          - (fderiv ℝ (fun p : ℝ × (ℝ × VS) => RyaboginVolterra.G n (p.1 • h) p.2.1 p.2.2)
          (0, (s, baseZ s)))‖ * ‖w‖ := by rw [norm_pair_zero_zero]
    _ ≤ η * ‖w‖ := mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev10.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Joint smoothness in the scale of `(a,s,z) ↦ Θ n (a • h) s s z`. -/
lemma contDiff_Theta_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.1 p.2.2) := by
  have hfam := contDiff_Theta_family n (H := fun a u : ℝ => a * h u) (by fun_prop)
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) =>
      (((p.1, (p.2.1, p.2.2)), p.2.1) : (ℝ × (ℝ × VS)) × ℝ)) := by fun_prop
  have hcomp := hfam.comp hmap
  have hcomp' : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.Theta n (fun u : ℝ => p.1 * h u) p.2.1 p.2.1 p.2.2) := by
    convert hcomp using 1
    funext p
    rfl
  have heq : (fun p : ℝ × (ℝ × VS) =>
        RyaboginVolterra.Theta n (fun u : ℝ => p.1 * h u) p.2.1 p.2.1 p.2.2)
      = fun p : ℝ × (ℝ × VS) =>
        RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.1 p.2.2 := by
    funext p
    have h2 : (fun u : ℝ => p.1 * h u) = (p.1 • h) := by
      funext u; simp [Pi.smul_apply, smul_eq_mul]
    rw [h2]
  rw [heq] at hcomp'
  exact hcomp'

/-- **The value `Θ n (a•h) s s z` is uniformly close to the base one.** -/
lemma Theta_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ z : VS, ‖z - baseZ s‖ ≤ ρ →
        ‖RyaboginVolterra.Theta n (a • h) s s z
          - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s)‖ ≤ η := by
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀}) :=
    isCompact_Icc.prod (isCompact_tube hα hα1 (le_of_lt hρ₀))
  have hcont : Continuous (fun p : ℝ × (ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.1 p.2.2) :=
    (contDiff_Theta_diag n hh).continuous
  intro η hη
  obtain ⟨δ, hδpos, hδ⟩ := uniform_close_continuous_compact hcont hK η hη
  refine ⟨min 1 (δ/2), lt_min one_pos (by linarith), min ρ₀ (δ/2),
    lt_min hρ₀ (by linarith), min_le_left _ _, ?_⟩
  intro a ha s hs z hz
  have ha1 : a ≤ 1 := le_trans ha.2 (min_le_left _ _)
  have haδ : a < δ := lt_of_le_of_lt ha.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hzδ : ‖z - baseZ s‖ < δ :=
    lt_of_le_of_lt hz (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hx : (a, (s, z)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} :=
    ⟨⟨ha.1, ha1⟩, ⟨hs, le_trans hz (min_le_left _ _)⟩⟩
  have hy : ((0:ℝ), (s, baseZ s)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀} :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨hs, by simp [le_of_lt hρ₀]⟩⟩
  have hdist : dist (a, (s, z)) ((0:ℝ), (s, baseZ s)) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg ha.1, dist_self,
      dist_eq_norm]
    exact max_lt haδ (max_lt hδpos hzδ)
  exact hδ (a, (s, z)) hx ((0:ℝ), (s, baseZ s)) hy hdist

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev11.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The `s`-partial of the `Θ`-family at scale `a`, written through the joint differential in
the scale (so that it is manifestly continuous in `(a,s,σ,z)`). -/
noncomputable def DTheta (n : ℕ) (a s σ : ℝ) (h : ℝ → ℝ) (z : VS) : VS :=
  (fderiv ℝ (fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) (a, (s, σ, z)))
    ((0 : ℝ), ((1 : ℝ), (0 : ℝ), (0 : VS)))

/-- `DTheta` is the slice derivative in the `(s,σ,z)`-variables. -/
lemma DTheta_eq_slice (n : ℕ) {a s σ : ℝ} {h : ℝ → ℝ} {z : VS}
    (hdiff : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) (a, (s, σ, z))) :
    DTheta n a s σ h z
      = (fderiv ℝ (fun q : ℝ × ℝ × VS =>
          RyaboginVolterra.Theta n (a • h) q.1 q.2.1 q.2.2) (s, σ, z))
        ((1 : ℝ), (0 : ℝ), (0 : VS)) := by
  have hmain := fderiv_slice_eq_comp_inr
    (F := fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2)
    (a := a) (p := (s, σ, z)) hdiff
  have h := congrArg (fun (L : (ℝ × ℝ × VS) →L[ℝ] VS) =>
    L ((1 : ℝ), (0 : ℝ), (0 : VS))) hmain
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at h
  rw [DTheta]
  exact h.symm

/-- Joint smoothness in the scale of `(a,s,σ,z) ↦ Θ n (a • h) s σ z`. -/
lemma contDiff_Theta_joint4 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) := by
  have hfam := contDiff_Theta_family n (H := fun a u : ℝ => a * h u) (by fun_prop)
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ × VS) =>
      (((p.1, (p.2.1, p.2.2.2)), p.2.2.1) : (ℝ × (ℝ × VS)) × ℝ)) := by fun_prop
  have hcomp := hfam.comp hmap
  have hcomp' : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (fun u : ℝ => p.1 * h u) p.2.1 p.2.2.1 p.2.2.2) := by
    convert hcomp using 1
    funext p
    rfl
  have heq : (fun p : ℝ × (ℝ × ℝ × VS) =>
        RyaboginVolterra.Theta n (fun u : ℝ => p.1 * h u) p.2.1 p.2.2.1 p.2.2.2)
      = fun p : ℝ × (ℝ × ℝ × VS) =>
        RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2 := by
    funext p
    have h2 : (fun u : ℝ => p.1 * h u) = (p.1 • h) := by
      funext u; simp [Pi.smul_apply, smul_eq_mul]
    rw [h2]
  rw [heq] at hcomp'
  exact hcomp'

/-- **The `s`-partial of `Θ` is uniformly close to the base one.** -/
lemma dTheta_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ σ ∈ Set.Icc α 1, ∀ z : VS,
        ‖z - baseZ σ‖ ≤ ρ → ‖DTheta n a s σ h z - DTheta n 0 s σ h (baseZ σ)‖ ≤ η := by
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ
      (Set.Icc α 1 ×ˢ
        {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀})) :=
    isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_tube hα hα1 (le_of_lt hρ₀)))
  have hcont : Continuous (fun p : ℝ × (ℝ × ℝ × VS) =>
      (fderiv ℝ (fun q : ℝ × (ℝ × ℝ × VS) =>
        RyaboginVolterra.Theta n (q.1 • h) q.2.1 q.2.2.1 q.2.2.2) p)
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ), (0 : VS)))) :=
    ((contDiff_Theta_joint4 n hh).continuous_fderiv (by simp)).clm_apply continuous_const
  intro η hη
  obtain ⟨δ, hδpos, hδ⟩ := uniform_close_continuous_compact hcont hK η hη
  refine ⟨min 1 (δ/2), lt_min one_pos (by linarith), min ρ₀ (δ/2),
    lt_min hρ₀ (by linarith), min_le_left _ _, ?_⟩
  intro a ha s hs σ hσ z hz
  have ha1 : a ≤ 1 := le_trans ha.2 (min_le_left _ _)
  have haδ : a < δ := lt_of_le_of_lt ha.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hzδ : ‖z - baseZ σ‖ < δ :=
    lt_of_le_of_lt hz (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hx : (a, (s, σ, z)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      (Set.Icc α 1 ×ˢ
        {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀}) :=
    ⟨⟨ha.1, ha1⟩, ⟨hs, hσ, le_trans hz (min_le_left _ _)⟩⟩
  have hy : ((0:ℝ), (s, σ, baseZ σ)) ∈ Set.Icc (0:ℝ) 1 ×ˢ
      (Set.Icc α 1 ×ˢ
        {p : ℝ × VS | p.1 ∈ Set.Icc α 1 ∧ ‖p.2 - baseZ p.1‖ ≤ ρ₀}) :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨hs, hσ, by simp [le_of_lt hρ₀]⟩⟩
  have hdist : dist (a, (s, σ, z)) ((0:ℝ), (s, σ, baseZ σ)) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg ha.1, dist_self, dist_self, dist_eq_norm]
    exact max_lt haδ (max_lt hδpos (max_lt hδpos hzδ))
  unfold DTheta
  exact hδ (a, (s, σ, z)) hx ((0:ℝ), (s, σ, baseZ σ)) hy hdist

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev12.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The `Θ`-and-`∂_sΘ` part of the `R`-slot is uniformly close to the base one.** -/
lemma Rterm_theta_part_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0:ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ Z : ℝ → VS, Continuous Z →
        (∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ) →
        ‖((- RyaboginVolterra.Theta n (a • h) s s (Z s))
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))
          - ((- RyaboginVolterra.Theta n ((0 : ℝ) • h) s s (baseZ s))
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n ((0 : ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))‖ ≤ η := by
  intro η hη
  obtain ⟨a₁, ha₁, ρ₁, hρ₁, hρ₁₀, hT⟩ := Theta_close n hh hα hα1 hρ₀ (η/2) (by linarith)
  obtain ⟨a₂, ha₂, ρ₂, hρ₂, hρ₂₀, hdT⟩ := dTheta_close n hh hα hα1 hρ₀ (η/2) (by linarith)
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    le_trans (min_le_left _ _) hρ₁₀, ?_⟩
  intro a ha s hs Z hZc hZ
  have ha₁' : a ∈ Set.Icc (0:ℝ) a₁ := ⟨ha.1, le_trans ha.2 (min_le_left _ _)⟩
  have ha₂' : a ∈ Set.Icc (0:ℝ) a₂ := ⟨ha.1, le_trans ha.2 (min_le_right _ _)⟩
  have hρZ₁ : ∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ₁ :=
    fun σ hσ => le_trans (hZ σ hσ) (min_le_left _ _)
  have hρZ₂ : ∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ₂ :=
    fun σ hσ => le_trans (hZ σ hσ) (min_le_right _ _)
  have hpt : ‖RyaboginVolterra.Theta n (a • h) s s (Z s)
      - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s)‖ ≤ η/2 :=
    hT a ha₁' s hs (Z s) (hρZ₁ s hs)
  -- the integrand difference, pointwise
  have hd₁ : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ × VS) =>
      RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) (a, (s, s, Z s)) :=
    (contDiff_Theta_joint4 n hh).differentiable (by simp) (a, (s, s, Z s))
  have hptint : ∀ σ ∈ Set.Icc α 1,
      ‖(fderiv ℝ (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2)
          (s, σ, Z σ) ((1 : ℝ), (0 : ℝ), (0 : VS)))
        - (fderiv ℝ (fun p : ℝ × ℝ × VS => RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2)
          (s, σ, baseZ σ) ((1 : ℝ), (0 : ℝ), (0 : VS)))‖ ≤ η/2 := by
    intro σ hσ
    have hd₁' : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ × VS) =>
        RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) (a, (s, σ, Z σ)) :=
      (contDiff_Theta_joint4 n hh).differentiable (by simp) (a, (s, σ, Z σ))
    have hd₂' : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ × VS) =>
        RyaboginVolterra.Theta n (p.1 • h) p.2.1 p.2.2.1 p.2.2.2) (0, (s, σ, baseZ σ)) :=
      (contDiff_Theta_joint4 n hh).differentiable (by simp) (0, (s, σ, baseZ σ))
    rw [← DTheta_eq_slice (n := n) (a := a) (s := s) (σ := σ) (h := h) (z := Z σ) hd₁',
      ← DTheta_eq_slice (n := n) (a := 0) (s := s) (σ := σ) (h := h) (z := baseZ σ) hd₂']
    exact hdT a ha₂' s hs σ hσ (Z σ) (hρZ₂ σ hσ)
  -- continuity of both integrands on the interval
  have hcont₁ : Continuous (fun σ : ℝ => fderiv ℝ (fun p : ℝ × ℝ × VS =>
      RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
        ((1 : ℝ), (0 : ℝ), (0 : VS))) := by
    have hfd : Continuous (fun q : ℝ × ℝ × VS => fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) q
          ((1 : ℝ), (0 : ℝ), (0 : VS))) :=
      ((contDiff_Theta_curried n (hh.const_smul a)).continuous_fderiv (by simp)).clm_apply
        continuous_const
    exact hfd.comp (continuous_const.prodMk (continuous_id.prodMk hZc))
  have hcont₂ : Continuous (fun σ : ℝ => fderiv ℝ (fun p : ℝ × ℝ × VS =>
      RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
        ((1 : ℝ), (0 : ℝ), (0 : VS))) := by
    have hfd : Continuous (fun q : ℝ × ℝ × VS => fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) q
          ((1 : ℝ), (0 : ℝ), (0 : VS))) :=
      ((contDiff_Theta_curried n ((contDiff_const (c := (0:ℝ))).mul hh)).continuous_fderiv
        (by simp)).clm_apply continuous_const
    exact hfd.comp (continuous_const.prodMk (continuous_id.prodMk continuous_baseZ))
  -- the integral estimate
  set f : ℝ → VS := fun σ => (fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
          ((1 : ℝ), (0 : ℝ), (0 : VS)))
      - (fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
          ((1 : ℝ), (0 : ℝ), (0 : VS))) with hf
  have hint : ‖(∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
          ((1 : ℝ), (0 : ℝ), (0 : VS)))
      - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
          ((1 : ℝ), (0 : ℝ), (0 : VS)))‖ ≤ η/2 := by
    have hsub : (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
          RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
            ((1 : ℝ), (0 : ℝ), (0 : VS)))
        - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
          RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
            ((1 : ℝ), (0 : ℝ), (0 : VS)))
        = ∫ σ in s..1, f σ := by
      rw [hf]
      exact (intervalIntegral.integral_sub (μ := volume) (a := s) (b := 1)
        (hcont₁.intervalIntegrable _ _)
        (hcont₂.intervalIntegrable _ _)).symm
    rw [hsub]
    have h1s : |1 - s| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1, hα]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := 1)
      (f := f) (C := η/2) ?_) ?_
    · intro σ hσ
      rw [Set.uIoc_of_le hs.2] at hσ
      rw [hf]
      exact hptint σ ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
    · calc (η/2) * |1 - s| ≤ (η/2) * 1 := mul_le_mul_of_nonneg_left h1s (by linarith)
        _ = η/2 := by ring
  have hsplit : (- RyaboginVolterra.Theta n (a • h) s s (Z s)
        + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS))))
      - (- RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s)
        + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS))))
      = -(RyaboginVolterra.Theta n (a • h) s s (Z s)
          - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s))
        + ((∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS)))
          - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS)))) := by abel
  rw [hsplit]
  calc ‖-(RyaboginVolterra.Theta n (a • h) s s (Z s)
          - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s))
        + ((∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS)))
          - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS))))‖
      ≤ ‖RyaboginVolterra.Theta n (a • h) s s (Z s)
          - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s)‖
        + ‖(∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS)))
          - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
            RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
              ((1 : ℝ), (0 : ℝ), (0 : VS)))‖ := by
        have h := norm_add_le (-(RyaboginVolterra.Theta n (a • h) s s (Z s)
              - RyaboginVolterra.Theta n ((0:ℝ) • h) s s (baseZ s)))
            ((∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS)))
              - (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n ((0:ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))
        simpa only [norm_neg] using h
    _ ≤ η/2 + η/2 := add_le_add hpt hint
    _ = η := by ring

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev13.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The interchange formula for `Xi1`**: the `s`-derivative of the integral defining `Xi1` is the
integral of the `(n+2)`-nd iterated derivative. -/
lemma hasDerivAt_Xi1 (n : ℕ) {a : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (s : ℝ) :
    HasDerivAt (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u)
      (∫ t in (-(profileX 1))..(profileX 1),
        iteratedDeriv (n + 2) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) s) s := by
  have hgs : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) q.2 q.1) ^ 2) ^ n) := by
    unfold RyaboginVolterra.line; fun_prop
  have hs1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ n) q.2) :=
    contDiffOn_parametric_iteratedDeriv_gen (n + 1)
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n)
      hgs
  have hs2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ n) q.2) :=
    contDiffOn_parametric_iteratedDeriv_gen (n + 2)
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n)
      hgs
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) := by fun_prop
  have hcont₁ : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - p.2 ^ 2 - (RyaboginVolterra.line (a • h) u p.2) ^ 2) ^ n) p.1) :=
    (hs1.comp hswap).continuous
  have hcont₂ : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - p.2 ^ 2 - (RyaboginVolterra.line (a • h) u p.2) ^ 2) ^ n) p.1) :=
    (hs2.comp hswap).continuous
  have hderiv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => iteratedDeriv (n + 1)
      (fun w : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) v)
      (iteratedDeriv (n + 2) (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) u) u := by
    intro u t
    have hψ : ContDiff ℝ ∞ (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) := by
      unfold RyaboginVolterra.line; fun_prop
    have hm : ((n + 1 : ℕ) : ℕ∞ω) < ∞ := by
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = WithTop.some ((n + 1 : ℕ) : ℕ∞) from rfl,
          show (∞ : ℕ∞ω) = WithTop.some (⊤ : ℕ∞) from rfl]
      exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top _)
    have hd : DifferentiableAt ℝ (iteratedDeriv (n + 1) (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n)) u :=
      (ContDiff.differentiable_iteratedDeriv (n + 1) hψ hm).differentiableAt
    simpa only [iteratedDeriv_succ] using hd.hasDerivAt
  have hmain := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := fun u t => iteratedDeriv (n + 1) (fun w : ℝ =>
      (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) u)
    (F' := fun u t => iteratedDeriv (n + 2) (fun w : ℝ =>
      (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) u)
    (x := fun _ : ℝ => profileX 1) (y := fun _ : ℝ => profileX 1)
    (x' := 0) (y' := 0) (s := s)
    hcont₁ hcont₂ hderiv (hasDerivAt_const (x := s) (c := profileX 1))
      (hasDerivAt_const (x := s) (c := profileX 1)) continuousAt_const continuousAt_const
  have hval : (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        iteratedDeriv (n + 1) (fun w : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ n) u)
      = fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u := by
    funext u
    rw [RyaboginVolterra.Xi1]
  rw [hval] at hmain
  simpa using hmain

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- `((m : ℕ) : ℕ∞ω) < ∞` — needed for `ContDiff.differentiable_iteratedDeriv`. -/
lemma nat_cast_lt_infty (m : ℕ) : ((m : ℕ) : ℕ∞ω) < ∞ := by
  rw [show ((m : ℕ) : ℕ∞ω) = WithTop.some ((m : ℕ) : ℕ∞) from rfl,
      show (∞ : ℕ∞ω) = WithTop.some (⊤ : ℕ∞) from rfl]
  exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top _)

/-- **The interchange formula for `Xi2`**. -/
lemma hasDerivAt_Xi2 (n : ℕ) {a : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (s : ℝ) :
    HasDerivAt (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u)
      (∫ t in (-(profileX 1))..(profileX 1),
        iteratedDeriv (n + 1) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
            (t + deriv (a • h) u)) s) s := by
  have hgs : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) q.2 q.1) ^ 2) ^ (n - 1) *
        (q.1 + deriv (a • h) q.2)) := by
    have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (a • h) p.2) := by fun_prop
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun v : ℝ => (a • h) v) p.2) :=
      contDiffOn_univ.mp (contDiffOn_deriv_snd_prod (P := ℝ)
        (G := fun (_ : ℝ) (u : ℝ) => (a • h) u) isOpen_univ (U := Set.univ)
        (by simpa using hG.contDiffOn))
    have h1' : ContDiff ℝ ∞ (fun (p : ℝ × ℝ) => deriv (a • h) p.2) := by
      convert h1 using 1
    unfold RyaboginVolterra.line
    fun_prop
  have hs1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      iteratedDeriv n
        (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ (n - 1) *
          (q.1 + deriv (a • h) u)) q.2) :=
    contDiffOn_parametric_iteratedDeriv_gen n
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) u))
      hgs
  have hs2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ (n - 1) *
          (q.1 + deriv (a • h) u)) q.2) :=
    contDiffOn_parametric_iteratedDeriv_gen (n + 1)
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) u))
      hgs
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1)) := by fun_prop
  have hcont₁ : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv n
        (fun u : ℝ => (1 - p.2 ^ 2 - (RyaboginVolterra.line (a • h) u p.2) ^ 2) ^ (n - 1) *
          (p.2 + deriv (a • h) u)) p.1) :=
    (hs1.comp hswap).continuous
  have hcont₂ : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - p.2 ^ 2 - (RyaboginVolterra.line (a • h) u p.2) ^ 2) ^ (n - 1) *
          (p.2 + deriv (a • h) u)) p.1) :=
    (hs2.comp hswap).continuous
  have hderiv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => iteratedDeriv n
      (fun w : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) w)) v)
      (iteratedDeriv (n + 1) (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
          (t + deriv (a • h) w)) u) u := by
    intro u t
    have hψ : ContDiff ℝ ∞ (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
          (t + deriv (a • h) w)) := by
      unfold RyaboginVolterra.line; fun_prop
    have hd : DifferentiableAt ℝ (iteratedDeriv n (fun w : ℝ =>
        (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
          (t + deriv (a • h) w))) u :=
      (ContDiff.differentiable_iteratedDeriv n hψ (nat_cast_lt_infty n)).differentiableAt
    simpa only [iteratedDeriv_succ] using hd.hasDerivAt
  have hmain := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := fun u t => iteratedDeriv n (fun w : ℝ =>
      (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) w)) u)
    (F' := fun u t => iteratedDeriv (n + 1) (fun w : ℝ =>
      (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) w)) u)
    (x := fun _ : ℝ => profileX 1) (y := fun _ : ℝ => profileX 1)
    (x' := 0) (y' := 0) (s := s)
    hcont₁ hcont₂ hderiv (hasDerivAt_const (x := s) (c := profileX 1))
      (hasDerivAt_const (x := s) (c := profileX 1)) continuousAt_const continuousAt_const
  have hval : (fun u : ℝ => ∫ t in (-(profileX 1))..(profileX 1),
        iteratedDeriv n (fun w : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) w t) ^ 2) ^ (n - 1) *
            (t + deriv (a • h) w)) u)
      = fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u := by
    funext u
    simp only [RyaboginVolterra.Xi2, RyaboginVolterra.lineSlope]
  rw [hval] at hmain
  simpa using hmain

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev14.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The common `(scale, t, s)` closeness argument. -/
lemma uniform_scale_close {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : Continuous Φ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Icc (0 : ℝ) a₀,
      ∀ s ∈ Set.Icc α 1, ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1),
        ‖Φ (a, (t, s)) - Φ (0, (t, s))‖ ≤ η := by
  intro η hη
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (-(profileX 1)) (profileX 1) ×ˢ
      Set.Icc α 1)) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨δ, hδpos, hδ⟩ := uniform_close_continuous_compact hΦ hK η hη
  refine ⟨min (δ / 2) 1, lt_min (by linarith) zero_lt_one, fun a ha s hs t ht => ?_⟩
  have ha1 : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.1, le_trans ha.2 (min_le_right _ _)⟩
  have hx : (0, (t, s)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (-(profileX 1)) (profileX 1) ×ˢ
      Set.Icc α 1) := ⟨⟨le_refl 0, zero_le_one⟩, ⟨ht, hs⟩⟩
  have hy : (a, (t, s)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (-(profileX 1)) (profileX 1) ×ˢ
      Set.Icc α 1) := ⟨ha1, ⟨ht, hs⟩⟩
  have hd : dist (a, (t, s)) (0, (t, s)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, sub_zero,
      abs_of_nonneg ha.1]
    have h1 : a ≤ δ / 2 := le_trans ha.2 (min_le_left _ _)
    linarith
  exact hδ _ hy _ hx hd

/-- **The `s`-derivative of `Xi1` is uniformly close to the base one.** -/
lemma Xi1_deriv_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Icc (0 : ℝ) a₀, ∀ s ∈ Set.Icc α 1,
      ‖deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
        - deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s‖ ≤ η := by
  intro η hη
  have hp1pos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  set η' : ℝ := η / (2 * profileX 1 + 1) with hη'def
  have hη'pos : 0 < η' := by rw [hη'def]; positivity
  have hj : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - q.1.2 ^ 2 - (RyaboginVolterra.line (q.1.1 • h) u q.1.2) ^ 2) ^ n) q.2) := by
    have hG : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
        (1 - q.1.2 ^ 2 - (RyaboginVolterra.line (q.1.1 • h) q.2 q.1.2) ^ 2) ^ n) := by
      unfold RyaboginVolterra.line
      simp only [Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 2)
      (P := ℝ × ℝ)
      (G := fun (p : ℝ × ℝ) (u : ℝ) =>
        (1 - p.2 ^ 2 - (RyaboginVolterra.line (p.1 • h) u p.2) ^ 2) ^ n) hG
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((p.1, p.2.1), p.2.2)) := by fun_prop
  have hΦ : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - p.2.1 ^ 2 - (RyaboginVolterra.line (p.1 • h) u p.2.1) ^ 2) ^ n) p.2.2) :=
    (hj.comp hmap).continuous
  have hslice : ∀ a : ℝ, ContDiff ℝ ∞ (fun q : ℝ × ℝ => iteratedDeriv (n + 2)
      (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ n) q.2) := by
    intro a
    have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
        (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) q.2 q.1) ^ 2) ^ n) := by
      unfold RyaboginVolterra.line
      simp only [Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 2) (P := ℝ)
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) hG
  obtain ⟨a₀, ha₀pos, ha₀⟩ := uniform_scale_close hΦ hα hα1 η' hη'pos
  refine ⟨a₀, ha₀pos, fun a ha s hs => ?_⟩
  rw [(hasDerivAt_Xi1 n hh s).deriv, (hasDerivAt_Xi1 n hh s).deriv]
  have hcont_a : Continuous (fun t : ℝ => iteratedDeriv (n + 2)
      (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) s) :=
    ((hslice a).comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t, s)))).continuous
  have hcont_0 : Continuous (fun t : ℝ => iteratedDeriv (n + 2)
      (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ n) s) :=
    ((hslice 0).comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t, s)))).continuous
  have hpt : ∀ t ∈ Ι (-(profileX 1)) (profileX 1),
      ‖iteratedDeriv (n + 2) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) s
        - iteratedDeriv (n + 2) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ n) s‖ ≤ η' := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    exact ha₀ a ha s hs t ⟨le_of_lt ht.1, ht.2⟩
  have hsub : (∫ t in (-(profileX 1))..(profileX 1), iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) s)
      - (∫ t in (-(profileX 1))..(profileX 1), iteratedDeriv (n + 2)
        (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ n) s)
      = ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 2) (fun u : ℝ =>
              (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ n) s
            - iteratedDeriv (n + 2) (fun u : ℝ =>
              (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ n) s) :=
    (intervalIntegral.integral_sub (μ := volume) (a := -(profileX 1)) (b := profileX 1)
      (hcont_a.intervalIntegrable _ _) (hcont_0.intervalIntegrable _ _)).symm
  rw [hsub]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(profileX 1)) (b := profileX 1) (C := η') hpt
  have hδ2 : |profileX 1 - -(profileX 1)| = 2 * profileX 1 := by
    rw [abs_of_nonneg] <;> linarith
  rw [hδ2] at hbound
  have hfin : η' * (2 * profileX 1) ≤ η := by
    rw [hη'def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  linarith [hbound, hfin]

/-- **The `s`-derivative of `Xi2` is uniformly close to the base one.** -/
lemma Xi2_deriv_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Icc (0 : ℝ) a₀, ∀ s ∈ Set.Icc α 1,
      ‖deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s
        - deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s‖ ≤ η := by
  intro η hη
  have hp1pos : 0 < profileX 1 := profileX_pos 1 (by norm_num)
  set η' : ℝ := η / (2 * profileX 1 + 1) with hη'def
  have hη'pos : 0 < η' := by rw [hη'def]; positivity
  have hdv : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => deriv (q.1.1 • h) q.2) := by
    have hG : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => (p.1.1 • h) p.2) := by
      simp only [Pi.smul_apply, smul_eq_mul]; fun_prop
    have h1 := contDiffOn_univ.mp (contDiffOn_deriv_snd_prod (P := ℝ × ℝ)
      (G := fun (p : ℝ × ℝ) (u : ℝ) => (p.1 • h) u) isOpen_univ (U := Set.univ)
      (by simpa using hG.contDiffOn))
    convert h1 using 1
  have hj : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - q.1.2 ^ 2 - (RyaboginVolterra.line (q.1.1 • h) u q.1.2) ^ 2) ^ (n - 1) *
          (q.1.2 + deriv (q.1.1 • h) u)) q.2) := by
    have hG : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
        (1 - q.1.2 ^ 2 - (RyaboginVolterra.line (q.1.1 • h) q.2 q.1.2) ^ 2) ^ (n - 1) *
          (q.1.2 + deriv (q.1.1 • h) q.2)) := by
      unfold RyaboginVolterra.line
      simp only [Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 1)
      (P := ℝ × ℝ)
      (G := fun (p : ℝ × ℝ) (u : ℝ) =>
        (1 - p.2 ^ 2 - (RyaboginVolterra.line (p.1 • h) u p.2) ^ 2) ^ (n - 1) *
          (p.2 + deriv (p.1 • h) u)) hG
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((p.1, p.2.1), p.2.2)) := by fun_prop
  have hΦ : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - p.2.1 ^ 2 - (RyaboginVolterra.line (p.1 • h) u p.2.1) ^ 2) ^ (n - 1) *
          (p.2.1 + deriv (p.1 • h) u)) p.2.2) :=
    (hj.comp hmap).continuous
  have hslice : ∀ a : ℝ, ContDiff ℝ ∞ (fun q : ℝ × ℝ => iteratedDeriv (n + 1)
      (fun u : ℝ => (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) u q.1) ^ 2) ^ (n - 1) *
        (q.1 + deriv (a • h) u)) q.2) := by
    intro a
    have hG : ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
        (1 - q.1 ^ 2 - (RyaboginVolterra.line (a • h) q.2 q.1) ^ 2) ^ (n - 1) *
          (q.1 + deriv (a • h) q.2)) := by
      unfold RyaboginVolterra.line
      simp only [Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact contDiffOn_parametric_iteratedDeriv_gen (k := n + 1) (P := ℝ)
      (G := fun (t : ℝ) (u : ℝ) => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) u)) hG
  obtain ⟨a₀, ha₀pos, ha₀⟩ := uniform_scale_close hΦ hα hα1 η' hη'pos
  refine ⟨a₀, ha₀pos, fun a ha s hs => ?_⟩
  rw [(hasDerivAt_Xi2 n hh s).deriv, (hasDerivAt_Xi2 n hh s).deriv]
  have hcont_a : Continuous (fun t : ℝ => iteratedDeriv (n + 1)
      (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
        (t + deriv (a • h) u)) s) :=
    ((hslice a).comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t, s)))).continuous
  have hcont_0 : Continuous (fun t : ℝ => iteratedDeriv (n + 1)
      (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ (n - 1) *
        (t + deriv ((0 : ℝ) • h) u)) s) :=
    ((hslice 0).comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => (t, s)))).continuous
  have hpt : ∀ t ∈ Ι (-(profileX 1)) (profileX 1),
      ‖iteratedDeriv (n + 1) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
            (t + deriv (a • h) u)) s
        - iteratedDeriv (n + 1) (fun u : ℝ =>
          (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ (n - 1) *
            (t + deriv ((0 : ℝ) • h) u)) s‖ ≤ η' := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    exact ha₀ a ha s hs t ⟨le_of_lt ht.1, ht.2⟩
  have hsub : (∫ t in (-(profileX 1))..(profileX 1), iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
          (t + deriv (a • h) u)) s)
      - (∫ t in (-(profileX 1))..(profileX 1), iteratedDeriv (n + 1)
        (fun u : ℝ => (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ (n - 1) *
          (t + deriv ((0 : ℝ) • h) u)) s)
      = ∫ t in (-(profileX 1))..(profileX 1),
          (iteratedDeriv (n + 1) (fun u : ℝ =>
              (1 - t ^ 2 - (RyaboginVolterra.line (a • h) u t) ^ 2) ^ (n - 1) *
                (t + deriv (a • h) u)) s
            - iteratedDeriv (n + 1) (fun u : ℝ =>
              (1 - t ^ 2 - (RyaboginVolterra.line ((0 : ℝ) • h) u t) ^ 2) ^ (n - 1) *
                (t + deriv ((0 : ℝ) • h) u)) s) :=
    (intervalIntegral.integral_sub (μ := volume) (a := -(profileX 1)) (b := profileX 1)
      (hcont_a.intervalIntegrable _ _) (hcont_0.intervalIntegrable _ _)).symm
  rw [hsub]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(profileX 1)) (b := profileX 1) (C := η') hpt
  have hδ2 : |profileX 1 - -(profileX 1)| = 2 * profileX 1 := by
    rw [abs_of_nonneg] <;> linarith
  rw [hδ2] at hbound
  have hfin : η' * (2 * profileX 1) ≤ η := by
    rw [hη'def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  linarith [hbound, hfin]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev15.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The `mk4` vectors `mk4 0 0 · ·` form a two-dimensional subspace. -/
lemma mk4_zero_zero_sub (b c b' c' : ℝ) :
    RyaboginVolterra.mk4 0 0 b c - RyaboginVolterra.mk4 0 0 b' c'
      = RyaboginVolterra.mk4 0 0 (b - b') (c - c') := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
  funext i
  fin_cases i <;> simp [RyaboginVolterra.mk4]

lemma norm_mk4_zero_zero_sub_le (b c b' c' : ℝ) :
    ‖RyaboginVolterra.mk4 0 0 b c - RyaboginVolterra.mk4 0 0 b' c'‖
      ≤ |b - b'| + |c - c'| := by
  rw [mk4_zero_zero_sub]
  exact norm_mk4_zero_zero_le _ _

/-- **The `s`-derivative of `Ξ`, componentwise.** -/
lemma Xi_deriv_eq (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (a s : ℝ) :
    deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s
      = RyaboginVolterra.mk4 0 0
          (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
            + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
          (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s) := by
  have hsm : ContDiff ℝ ∞ (a • h) := hh.const_smul a
  have hXi1 : ContDiff ℝ ∞ (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) :=
    contDiff_Xi1 n hsm
  have hXi2 : ContDiff ℝ ∞ (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) :=
    contDiff_Xi2 n hsm
  have hM : ContDiff ℝ ∞
      (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) := by
    have h := (contDiff_momentRHS n).iterate_deriv (n + 1)
    simpa [iteratedDeriv_eq_iterate] using h
  have hXd : ContDiff ℝ ∞ (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) :=
    contDiff_Xi n hsm
  apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
  have hΦe : (fun u : ℝ => (EuclideanSpace.equiv (Fin 4) ℝ) (RyaboginVolterra.Xi n (a • h) u))
      = fun u : ℝ => ![profileX 1, profileX 1,
          (- RyaboginVolterra.Xi1 n (a • h) u
            + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u),
          (- RyaboginVolterra.Xi2 n (a • h) u)] := by
    funext u
    unfold RyaboginVolterra.Xi RyaboginVolterra.mk4
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hchain : (EuclideanSpace.equiv (Fin 4) ℝ)
      (deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s)
      = deriv (fun u : ℝ => (EuclideanSpace.equiv (Fin 4) ℝ)
          (RyaboginVolterra.Xi n (a • h) u)) s :=
    ((ContinuousLinearEquiv.hasFDerivAt (EuclideanSpace.equiv (Fin 4) ℝ)).comp_hasDerivAt s
      (hXd.differentiable (by simp) s).hasDerivAt).deriv.symm
  rw [hchain, hΦe]
  have hpi : HasDerivAt (fun u : ℝ => ![profileX 1, profileX 1,
        (- RyaboginVolterra.Xi1 n (a • h) u
          + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u),
        (- RyaboginVolterra.Xi2 n (a • h) u)])
      ![0, 0,
        (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
          + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s),
        (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s)] s := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun _ : ℝ => profileX 1) 0 s
      exact hasDerivAt_const (x := s) (c := profileX 1)
    · show HasDerivAt (fun _ : ℝ => profileX 1) 0 s
      exact hasDerivAt_const (x := s) (c := profileX 1)
    · show HasDerivAt (fun x : ℝ => -RyaboginVolterra.Xi1 n (a • h) x
          + iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) x)
          (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
            + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s) s
      exact ((hXi1.differentiable (by simp) s).hasDerivAt.neg).add
          ((hM.differentiable (by simp) s).hasDerivAt)
    · show HasDerivAt (fun x : ℝ => -RyaboginVolterra.Xi2 n (a • h) x)
          (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s) s
      exact (hXi2.differentiable (by simp) s).hasDerivAt.neg
  rw [hpi.deriv]
  unfold RyaboginVolterra.mk4
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- **The `s`-derivative of `Ξ` is uniformly close to the base one.** -/
lemma Xi_deriv_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Icc (0 : ℝ) a₀, ∀ s ∈ Set.Icc α 1,
      ‖deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s
        - deriv (fun u : ℝ => RyaboginVolterra.Xi n ((0 : ℝ) • h) u) s‖ ≤ η := by
  intro η hη
  obtain ⟨a₁, ha₁pos, ha₁⟩ := Xi1_deriv_close n hh hα hα1 (η / 2) (by linarith)
  obtain ⟨a₂, ha₂pos, ha₂⟩ := Xi2_deriv_close n hh hα hα1 (η / 2) (by linarith)
  refine ⟨min a₁ a₂, lt_min ha₁pos ha₂pos, fun a ha s hs => ?_⟩
  have hb1 : ‖deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
      - deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s‖ ≤ η / 2 :=
    ha₁ a ⟨ha.1, le_trans ha.2 (min_le_left _ _)⟩ s hs
  have hb2 : ‖deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s
      - deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s‖ ≤ η / 2 :=
    ha₂ a ⟨ha.1, le_trans ha.2 (min_le_right _ _)⟩ s hs
  rw [Xi_deriv_eq n hh a s, Xi_deriv_eq n hh 0 s]
  have hnorm := norm_mk4_zero_zero_sub_le
    (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
      + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
    (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s)
    (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s
      + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
    (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s)
  have h1 : |(-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
      + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
      - (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s
      + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)|
      ≤ η / 2 := by
    have he : (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
        + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
        - (-deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s
        + deriv (fun u : ℝ => iteratedDeriv (n + 1) (RyaboginVolterra.momentRHS n) u) s)
        = -(deriv (fun u : ℝ => RyaboginVolterra.Xi1 n (a • h) u) s
            - deriv (fun u : ℝ => RyaboginVolterra.Xi1 n ((0 : ℝ) • h) u) s) := by ring
    rw [he, abs_neg]
    simpa [Real.norm_eq_abs] using hb1
  have h2 : |(-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s)
      - (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s)| ≤ η / 2 := by
    have he : (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s)
        - (-deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s)
        = -(deriv (fun u : ℝ => RyaboginVolterra.Xi2 n (a • h) u) s
            - deriv (fun u : ℝ => RyaboginVolterra.Xi2 n ((0 : ℝ) • h) u) s) := by ring
    rw [he, abs_neg]
    simpa [Real.norm_eq_abs] using hb2
  linarith [hnorm, h1, h2]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev16.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The whole `R`-slot is uniformly close to the base one.** -/
lemma Rterm_close (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0 : ℝ) a₀, ∀ s ∈ Set.Icc α 1, ∀ Z : ℝ → VS, Continuous Z →
        (∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ) →
        ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖ ≤ η := by
  intro η hη
  obtain ⟨a₁, ha₁, ρ₁, hρ₁, hρ₁le, h₁⟩ :=
    Rterm_theta_part_close n hh hα hα1 hρ₀ (η / 2) (by linarith)
  obtain ⟨a₂, ha₂, h₂⟩ := Xi_deriv_close n hh hα hα1 (η / 2) (by linarith)
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ρ₁, hρ₁, hρ₁le, fun a ha s hs Z hZc hZbd => ?_⟩
  have ha₁' : a ∈ Set.Icc (0 : ℝ) a₁ := ⟨ha.1, le_trans ha.2 (min_le_left _ _)⟩
  have ha₂' : a ∈ Set.Icc (0 : ℝ) a₂ := ⟨ha.1, le_trans ha.2 (min_le_right _ _)⟩
  have hA := h₁ a ha₁' s hs Z hZc hZbd
  have hB := h₂ a ha₂' s hs
  have hsplit : Rterm n a s h Z - Rterm n 0 s h baseZ
      = ((- RyaboginVolterra.Theta n (a • h) s s (Z s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))
          - (- RyaboginVolterra.Theta n ((0 : ℝ) • h) s s (baseZ s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n ((0 : ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS)))))
        + (deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s
            - deriv (fun u : ℝ => RyaboginVolterra.Xi n ((0 : ℝ) • h) u) s) := by
    rw [Rterm, Rterm]; abel
  rw [hsplit]
  calc ‖((- RyaboginVolterra.Theta n (a • h) s s (Z s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))
          - (- RyaboginVolterra.Theta n ((0 : ℝ) • h) s s (baseZ s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n ((0 : ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS)))))
        + (deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s
            - deriv (fun u : ℝ => RyaboginVolterra.Xi n ((0 : ℝ) • h) u) s)‖
      ≤ ‖(- RyaboginVolterra.Theta n (a • h) s s (Z s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n (a • h) p.1 p.2.1 p.2.2) (s, σ, Z σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))
          - (- RyaboginVolterra.Theta n ((0 : ℝ) • h) s s (baseZ s)
            + (∫ σ in s..1, fderiv ℝ (fun p : ℝ × ℝ × VS =>
                RyaboginVolterra.Theta n ((0 : ℝ) • h) p.1 p.2.1 p.2.2) (s, σ, baseZ σ)
                  ((1 : ℝ), (0 : ℝ), (0 : VS))))‖
        + ‖deriv (fun u : ℝ => RyaboginVolterra.Xi n (a • h) u) s
            - deriv (fun u : ℝ => RyaboginVolterra.Xi n ((0 : ℝ) • h) u) s‖ :=
        norm_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hA hB
    _ = η := by ring

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev17.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Uniform bound on `‖deriv baseZ s‖` on `[α,1]`. -/
lemma exists_bound_deriv_baseZ {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc α 1, ‖deriv (fun u : ℝ => baseZ u) s‖ ≤ C := by
  have hcont : Continuous (deriv (fun u : ℝ => baseZ u)) :=
    contDiff_baseZ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun s hs => le_trans (hC s hs) (le_max_left _ _)⟩

/-- Norm bound for a triple difference. -/
lemma norm_sub_sub_sub_le {E : Type*} [NormedAddCommGroup E] (A B C D : E) :
    ‖A - B - C - D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have h1 : ‖A - B - C - D‖ ≤ ‖A - B - C‖ + ‖D‖ := norm_sub_le _ _
  have h2 : ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le _ _
  have h3 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  linarith

/-- **Comparison of `deriv Z s` with `deriv baseZ s` using the *base* inverse.**  The two linear
equations for `deriv Z s` and `deriv baseZ s` differ by a small operator; solving with the base
inverse gives the bound. -/
lemma deriv_diff_bound2 (n : ℕ) {a s B : ℝ} {h : ℝ → ℝ} {Z : ℝ → VS}
    (hBinv : ∃ e : VS ≃L[ℝ] VS, (∀ v : VS, e v = GzPart n 0 s h (baseZ s) v)
      ∧ ‖(e.symm : VS →L[ℝ] VS)‖ ≤ B)
    (h1 : GzPart n a s h (Z s) (deriv Z s) = Rterm n a s h Z - GsPart n a s h (Z s))
    (h2 : GzPart n 0 s h (baseZ s) (deriv baseZ s)
      = Rterm n 0 s h baseZ - GsPart n 0 s h (baseZ s))
    (hsmall : B * ‖GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)‖ ≤ 1 / 2) :
    ‖deriv Z s - deriv baseZ s‖ ≤ 2 * B *
      (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖) := by
  obtain ⟨e, he, hBb⟩ := hBinv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hBb
  set T : VS →L[ℝ] VS := GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s) with hT
  have hBT : B * ‖T‖ ≤ 1 / 2 := by rw [hT]; exact hsmall
  have hTZ : GzPart n 0 s h (baseZ s) (deriv Z s)
      = GzPart n a s h (Z s) (deriv Z s) - T (deriv Z s) := by
    rw [hT, ContinuousLinearMap.sub_apply]; abel
  have hTsplit : T (deriv Z s) = T (deriv baseZ s) + T (deriv Z s - deriv baseZ s) := by
    conv_lhs => rw [show deriv Z s = deriv baseZ s + (deriv Z s - deriv baseZ s) from by abel]
    rw [map_add]
  have hkey : e (deriv Z s - deriv baseZ s)
      = (Rterm n a s h Z - Rterm n 0 s h baseZ)
        - (GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s))
        - T (deriv baseZ s) - T (deriv Z s - deriv baseZ s) := by
    rw [map_sub, he (deriv Z s), he (deriv baseZ s), h2, hTZ, h1, hTsplit]
    abel
  have hb1 : ‖e (deriv Z s - deriv baseZ s)‖ ≤
      ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖T (deriv baseZ s)‖ + ‖T (deriv Z s - deriv baseZ s)‖ := by
    rw [hkey]
    exact norm_sub_sub_sub_le _ _ _ _
  have hb2 : ‖T (deriv Z s - deriv baseZ s)‖ ≤ ‖T‖ * ‖deriv Z s - deriv baseZ s‖ :=
    ContinuousLinearMap.le_opNorm T _
  have hmain : ‖deriv Z s - deriv baseZ s‖ ≤
      B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖T (deriv baseZ s)‖) + (B * ‖T‖) * ‖deriv Z s - deriv baseZ s‖ := by
    calc ‖deriv Z s - deriv baseZ s‖ = ‖e.symm (e (deriv Z s - deriv baseZ s))‖ := by
          rw [ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖(e.symm : VS →L[ℝ] VS)‖ * ‖e (deriv Z s - deriv baseZ s)‖ :=
          ContinuousLinearMap.le_opNorm (e.symm : VS →L[ℝ] VS) _
      _ ≤ B * ‖e (deriv Z s - deriv baseZ s)‖ :=
          mul_le_mul_of_nonneg_right hBb (norm_nonneg _)
      _ ≤ B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
            + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
            + ‖T (deriv baseZ s)‖ + ‖T (deriv Z s - deriv baseZ s)‖) :=
          mul_le_mul_of_nonneg_left hb1 hB0
      _ ≤ B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
            + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
            + ‖T (deriv baseZ s)‖ + ‖T‖ * ‖deriv Z s - deriv baseZ s‖) :=
          mul_le_mul_of_nonneg_left (by linarith [hb2]) hB0
      _ = B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
            + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
            + ‖T (deriv baseZ s)‖) + (B * ‖T‖) * ‖deriv Z s - deriv baseZ s‖ := by
          ring
  have hstep : (B * ‖T‖) * ‖deriv Z s - deriv baseZ s‖
      ≤ (1 / 2) * ‖deriv Z s - deriv baseZ s‖ :=
    mul_le_mul_of_nonneg_right hBT (norm_nonneg _)
  have hmain' : ‖deriv Z s - deriv baseZ s‖ ≤
      B * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖T (deriv baseZ s)‖) + (1 / 2) * ‖deriv Z s - deriv baseZ s‖ := by
    linarith [hmain, hstep]
  have hfin : ‖deriv Z s - deriv baseZ s‖ ≤ 2 * (B *
      (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖T (deriv baseZ s)‖)) := by linarith [hmain']
  have hTeq : ‖T (deriv baseZ s)‖
      = ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ := by rw [hT]
  rw [hTeq] at hfin
  linarith [hfin]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev18.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The `C¹`-deviation bound.**  If `Z` solves the differentiated Volterra identity, is within
`ρ` of the base state and the scale `a` is small, then `deriv Z s` is within `η` of `deriv baseZ s`,
uniformly on `(α,1)`. -/
lemma deriv_deviation_bound (n : ℕ) (hn : 2 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∀ η : ℝ, 0 < η → ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧
      ∀ a ∈ Set.Icc (0 : ℝ) a₀, ∀ s ∈ Set.Ioo α 1, ∀ Z : ℝ → VS, Continuous Z →
        (∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ) →
        GzPart n a s h (Z s) (deriv Z s) = Rterm n a s h Z - GsPart n a s h (Z s) →
        ‖deriv Z s - deriv baseZ s‖ ≤ η := by
  intro η hη
  obtain ⟨B₀, hB₀pos, hB₀⟩ := base_inverse_bound n hn hα hα1 h
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_baseZ hα hα1
  have hden1 : 0 < 4 * B₀ * (C + 3) + 1 := by positivity
  have hden2 : 0 < 2 * B₀ + 1 := by positivity
  set η₀ : ℝ := min (η / (4 * B₀ * (C + 3) + 1)) (1 / (2 * B₀ + 1)) with hη₀def
  have hη₀pos : 0 < η₀ := by rw [hη₀def]; exact lt_min (by positivity) (by positivity)
  have hη₀le1 : η₀ ≤ η / (4 * B₀ * (C + 3) + 1) := by rw [hη₀def]; exact min_le_left _ _
  have hη₀le2 : η₀ ≤ 1 / (2 * B₀ + 1) := by rw [hη₀def]; exact min_le_right _ _
  obtain ⟨a₁, ha₁, ρ₁, hρ₁, hρ₁le, hR⟩ := Rterm_close n hh hα hα1 hρ₀ η₀ hη₀pos
  obtain ⟨a₂, ha₂, ρ₂, hρ₂, hρ₂le, hGs⟩ := GsPart_close n hh hα hα1 hρ₀ η₀ hη₀pos
  obtain ⟨a₃, ha₃, ρ₃, hρ₃, hρ₃le, hGz⟩ := GzPart_close n hh hα hα1 hρ₀ η₀ hη₀pos
  refine ⟨min a₁ (min a₂ a₃), lt_min ha₁ (lt_min ha₂ ha₃), min ρ₁ (min ρ₂ ρ₃),
    lt_min hρ₁ (lt_min hρ₂ hρ₃), le_trans (min_le_left _ _) hρ₁le, ?_⟩
  intro a ha s hs Z hZc hZbd hEq
  have ha₁' : a ∈ Set.Icc (0 : ℝ) a₁ := ⟨ha.1, le_trans ha.2 (min_le_left _ _)⟩
  have ha₂' : a ∈ Set.Icc (0 : ℝ) a₂ :=
    ⟨ha.1, le_trans ha.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have ha₃' : a ∈ Set.Icc (0 : ℝ) a₃ :=
    ⟨ha.1, le_trans ha.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hsIcc : s ∈ Set.Icc α 1 := ⟨hs.1.le, hs.2.le⟩
  have hρ₁' : ∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ₁ :=
    fun σ hσ => le_trans (hZbd σ hσ) (min_le_left _ _)
  have hρ₂' : ∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ₂ :=
    fun σ hσ => le_trans (hZbd σ hσ) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ₃' : ∀ σ ∈ Set.Icc α 1, ‖Z σ - baseZ σ‖ ≤ ρ₃ :=
    fun σ hσ => le_trans (hZbd σ hσ) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hR' := hR a ha₁' s hsIcc Z hZc hρ₁'
  have hGs' := hGs a ha₂' s hsIcc (Z s) (hρ₂' s hsIcc)
  have hGz' : ‖GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)‖ ≤ η₀ :=
    ContinuousLinearMap.opNorm_le_bound _ hη₀pos.le
      (fun w => hGz a ha₃' s hsIcc (Z s) w (hρ₃' s hsIcc))
  have hGzv : ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖ ≤ η₀ * C := by
    have h1 : ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖
        ≤ η₀ * ‖deriv baseZ s‖ := hGz a ha₃' s hsIcc (Z s) (deriv baseZ s) (hρ₃' s hsIcc)
    have h2 : ‖deriv baseZ s‖ ≤ C := hC s hsIcc
    nlinarith [h1, h2, hη₀pos, hC0]
  have hbase : GzPart n 0 s h (baseZ s) (deriv baseZ s)
      = Rterm n 0 s h baseZ - GsPart n 0 s h (baseZ s) :=
    base_deriv_eq n hn hα hα1 hs
  have hsmall : B₀ * ‖GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)‖ ≤ 1 / 2 := by
    have h1 : B₀ * η₀ ≤ 1 / 2 := by
      have h2 : B₀ * η₀ ≤ B₀ * (1 / (2 * B₀ + 1)) :=
        mul_le_mul_of_nonneg_left hη₀le2 hB₀pos.le
      have h3 : B₀ * (1 / (2 * B₀ + 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hden2]; linarith
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left hGz' hB₀pos.le) h1
  have hmain := deriv_diff_bound2 n (a := a) (s := s) (B := B₀)
    (hBinv := hB₀ s hsIcc) hEq hbase hsmall
  have hsum : 2 * B₀ * (η₀ + η₀ + η₀ * C) ≤ η := by
    have h3 : 2 * B₀ * (2 + C) ≤ 4 * B₀ * (C + 3) + 1 := by nlinarith [hB₀pos, hC0]
    have h4 : 2 * B₀ * (2 + C) * (η / (4 * B₀ * (C + 3) + 1)) ≤ η := by
      calc 2 * B₀ * (2 + C) * (η / (4 * B₀ * (C + 3) + 1))
          = (2 * B₀ * (2 + C) * η) / (4 * B₀ * (C + 3) + 1) := by ring
        _ ≤ ((4 * B₀ * (C + 3) + 1) * η) / (4 * B₀ * (C + 3) + 1) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hη.le) hden1.le
        _ = η := by field_simp
    have h5 : 2 * B₀ * (2 + C) * η₀ ≤ 2 * B₀ * (2 + C) * (η / (4 * B₀ * (C + 3) + 1)) :=
      mul_le_mul_of_nonneg_left hη₀le1 (by positivity)
    have h6 : 2 * B₀ * (η₀ + η₀ + η₀ * C) = 2 * B₀ * (2 + C) * η₀ := by ring
    linarith [h4, h5, h6]
  have hbnd : ‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖
      ≤ η₀ + η₀ + η₀ * C := by linarith [hR', hGs', hGzv]
  have hmul : 2 * B₀ * (‖Rterm n a s h Z - Rterm n 0 s h baseZ‖
        + ‖GsPart n a s h (Z s) - GsPart n 0 s h (baseZ s)‖
        + ‖(GzPart n a s h (Z s) - GzPart n 0 s h (baseZ s)) (deriv baseZ s)‖)
      ≤ 2 * B₀ * (η₀ + η₀ + η₀ * C) :=
    mul_le_mul_of_nonneg_left hbnd (by positivity)
  linarith [hmain, hmul, hsum]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev19.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **Parameterised version of `perturbation_data`**: the deviation radius can be prescribed. -/
theorem perturbation_data_param (ρ₀ ε₀ : ℝ) (hρ₀ : 0 < ρ₀) (hε₀ : 0 < ε₀) (n : ℕ) (hn : 2 ≤ n)
    {τ : ℝ} (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hflat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0)
    {c : ℝ} (hc : 1 - τ < c) (hc1 : c < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ε < (1 - 2 * τ) / 8 ∧
      ∃ Z : ℝ → VS, Continuous Z ∧
      ContDiffOn ℝ ∞ Z (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, ‖Z s - baseZ s‖ ≤ ρ₀) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, RyaboginVolterra.G n (ε • h) s (Z s)
        = (∫ σ in s..1, RyaboginVolterra.Theta n (ε • h) s σ (Z σ))
          + RyaboginVolterra.Xi n (ε • h) s) ∧
      (∀ s ∈ Set.Icc c 1, Z s = baseZ s) ∧
      (∀ s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1,
        deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, Z s 2 < 0) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, Z s 3 < 0) ∧
      StrictAntiOn (fun s : ℝ => Z s 0) (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      StrictAntiOn (fun s : ℝ => Z s 1) (Set.Icc ((1 - 2 * τ) / 4) 1) ∧
      ∃ X Y : ℝ → ℝ, ContDiff ℝ ∞ X ∧ ContDiff ℝ ∞ Y ∧
        (∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8) 1, X s = Z s 0 ∧ Y s = Z s 1) ∧
        (∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv X s = Z s 2 ∧ deriv Y s = Z s 3) ∧
        StrictAntiOn X (Set.Icc (3 * (1 - 2 * τ) / 8) 1) ∧
        StrictAntiOn Y (Set.Icc (3 * (1 - 2 * τ) / 8) 1) ∧
        X 1 = profileX 1 ∧ Y 1 = profileX 1 ∧
        (∀ s : ℝ, c ≤ s → X s = profileX s) ∧
        (∀ s : ℝ, c ≤ s → Y s = profileX s) ∧
        (∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
          X s = Z s 0 ∧ Y s = Z s 1) ∧
        (∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
          deriv X s = Z s 2 ∧ deriv Y s = Z s 3)∧
        (∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |h s| ≤ M) ∧
          (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |deriv h s| ≤ M) ∧
          (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |iteratedDeriv 2 h s| ≤ M) ∧ ε * M ≤ 1 / 2) := by
  classical
  obtain ⟨η, hη0, hη⟩ := hflat
  set a : ℝ := (1 - 2 * τ) / 2 with hadef
  set a₀ : ℝ := a / 2 with ha₀def
  set a' : ℝ := 3 * a / 4 - (1 - 2 * τ) / 32 with hadef'
  set α : ℝ := 5 * a / 8 with hαdef
  have ha : 0 < a := by rw [hadef]; linarith
  have ha1 : a < 1 := by rw [hadef]; linarith
  have ha₀ : 0 < a₀ := by rw [ha₀def]; linarith
  have ha₀1 : a₀ < 1 := by rw [ha₀def]; linarith
  have ha₀a : a₀ ≤ a := by rw [ha₀def]; linarith
  have ha' : a' < a := by rw [hadef', hadef]; linarith
  have ha₀a' : a₀ < a' := by rw [ha₀def, hadef', hadef]; linarith
  have ha'a : a' ≤ a := le_of_lt ha'
  have hα : α < a' := by rw [hαdef, hadef', hadef]; linarith
  have ha₀α : a₀ < α := by rw [ha₀def, hαdef, hadef]; linarith
  have hca : a₀ ≤ c := by rw [ha₀def, hadef]; linarith
  -- the margin and the radius
  obtain ⟨m, hm0, hm⟩ := exists_margin_profileX (a := a₀) ha₀ ha₀1.le
  set r : ℝ := min (min m 1) (min (1 / 64) (2 * ρ₀)) with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]; exact lt_min (lt_min hm0 one_pos) (lt_min (by norm_num) (by positivity))
  have hr1 : r < 1 := by
    have h : r ≤ 1 / 64 := by
      rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hrm : r ≤ m := by rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hr2 : r ≤ min (1 / 64) (2 * ρ₀) := by rw [hrdef]; exact min_le_right _ _
  set εmax : ℝ := min (min (min (η / 2) (a / 4)) 1) ε₀ with hεmaxdef
  have hεmax : 0 < εmax := by
    rw [hεmaxdef]
    exact lt_min (lt_min (lt_min (by linarith) (by linarith)) one_pos) hε₀
  obtain ⟨ε, hε0, hεmax', Z, hZc, hZsm, hZbd, hZfix, hZb, hder, hneg2, hneg3, hXanti, hYanti,
    hM⟩ :=
    volterra_master_gen n hn hh hsupp ha₀ ha₀1 hr0 hr1 hca hc hc1 hεmax hm0 hrm hm
  have hεa4 : ε < a / 4 := by
    refine lt_of_lt_of_le hεmax' ?_
    rw [hεmaxdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεε₀ : ε < ε₀ := by
    refine lt_of_lt_of_le hεmax' ?_
    rw [hεmaxdef]
    exact min_le_right _ _
  -- the two global coordinate functions
  have hZ0sm : ContDiffOn ℝ ∞ (fun s : ℝ => Z s 0) (Set.Ioo a₀ 1) :=
    (contDiffOn_state_coord_inf (Z := Z) (a := a₀) (b := 1) (i := 0) hZsm).mono
      (Set.Ioo_subset_Icc_self)
  have hZ1sm : ContDiffOn ℝ ∞ (fun s : ℝ => Z s 1) (Set.Ioo a₀ 1) :=
    (contDiffOn_state_coord_inf (Z := Z) (a := a₀) (b := 1) (i := 1) hZsm).mono
      (Set.Ioo_subset_Icc_self)
  have hZ2c : Continuous (fun σ : ℝ => Z σ 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4)).comp hZc
  have hZ3c : Continuous (fun σ : ℝ => Z σ 3) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4)).comp hZc
  have hac : a < c := by rw [hadef]; linarith
  have ha'c : a' ≤ c := le_of_lt (lt_trans ha' hac)
  set βglue : ℝ := (1 + c) / 2 with hβdef
  have hcβ : c < βglue := by rw [hβdef]; linarith
  have hβ1 : βglue < 1 := by rw [hβdef]; linarith
  set glue : ℝ → ℝ := Commons.Analysis.Calculus.smoothGlue α a' c βglue with hgluedef
  have hglue_sm : ContDiff ℝ ∞ glue := Commons.Analysis.Calculus.contDiff_smoothGlue α a' c βglue
  have hglue_one : ∀ t ∈ Set.Icc a' c, glue t = 1 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_one hα ha'c hcβ ht
  have hglue_zero_right : ∀ t : ℝ, βglue ≤ t → glue t = 0 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_zero_right hcβ ht
  have hglue_zero_left : ∀ t : ℝ, t ≤ α → glue t = 0 :=
    fun t ht => Commons.Analysis.Calculus.smoothGlue_eq_zero_left hα ht
  have hglue_tsupp : tsupport glue ⊆ Set.Icc α βglue :=
    Commons.Analysis.Calculus.tsupport_smoothGlue_subset hα hcβ
  have hsub : tsupport glue ⊆ Set.Ioo a₀ 1 := by
    intro t ht
    have h1 := hglue_tsupp ht
    exact ⟨lt_of_lt_of_le ha₀α h1.1, lt_of_le_of_lt h1.2 hβ1⟩
  set X : ℝ → ℝ := fun s => glue s * (Z s 0) + (1 - glue s) * profileX s with hXdef
  set Y : ℝ → ℝ := fun s => glue s * (Z s 1) + (1 - glue s) * profileX s with hYdef
  have hXsm : ContDiff ℝ ∞ X := by
    rw [hXdef]
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => glue s * (Z s 0)) :=
      Commons.Analysis.Calculus.ContDiff.mul_of_contDiffOn_isOpen hglue_sm hZ0sm isOpen_Ioo hsub
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 - glue s) * profileX s) :=
      (contDiff_const.sub hglue_sm).mul contDiff_profileX
    exact h1.add h2
  have hYsm : ContDiff ℝ ∞ Y := by
    rw [hYdef]
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => glue s * (Z s 1)) :=
      Commons.Analysis.Calculus.ContDiff.mul_of_contDiffOn_isOpen hglue_sm hZ1sm isOpen_Ioo hsub
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (1 - glue s) * profileX s) :=
      (contDiff_const.sub hglue_sm).mul contDiff_profileX
    exact h1.add h2
  -- `X = Z 0` and `Y = Z 1` on `[a',1]`
  have hXY : ∀ s ∈ Set.Icc a' 1, X s = Z s 0 ∧ Y s = Z s 1 := by
    intro s hs
    by_cases hsc : s ≤ c
    · have hglue1 : glue s = 1 := hglue_one s ⟨hs.1, hsc⟩
      constructor
      · change glue s * (Z s 0) + (1 - glue s) * profileX s = Z s 0
        rw [hglue1]; simp
      · change glue s * (Z s 1) + (1 - glue s) * profileX s = Z s 1
        rw [hglue1]; simp
    · push_neg at hsc
      have hZeq : Z s 0 = profileX s := by
        rw [hZb s ⟨hsc.le, hs.2⟩, baseZ_apply_zero]
      have hZeq1 : Z s 1 = profileX s := by
        rw [hZb s ⟨hsc.le, hs.2⟩, baseZ_apply_one]
      constructor
      · change glue s * (Z s 0) + (1 - glue s) * profileX s = Z s 0
        rw [hZeq]; ring
      · change glue s * (Z s 1) + (1 - glue s) * profileX s = Z s 1
        rw [hZeq1]; ring
  have hderX : ∀ s ∈ Set.Ioo a' 1, deriv X s = Z s 2 := by
    intro s hs
    have hnhds : Set.Icc a' 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : X =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := by
      filter_upwards [hnhds] with u hu
      exact (hXY u hu).1
    have hev2 : (fun u : ℝ => Z u 0) =ᶠ[𝓝 s] (fun u : ℝ => Z u 0) := Filter.EventuallyEq.rfl
    have hd : deriv (fun u : ℝ => Z u 0) s = Z s 2 := (hder s ⟨lt_trans ha₀a' hs.1, hs.2⟩).1
    rw [hev.deriv_eq, hd]
  have hderY : ∀ s ∈ Set.Ioo a' 1, deriv Y s = Z s 3 := by
    intro s hs
    have hnhds : Set.Icc a' 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hev : Y =ᶠ[𝓝 s] (fun u : ℝ => Z u 1) := by
      filter_upwards [hnhds] with u hu
      exact (hXY u hu).2
    have hd : deriv (fun u : ℝ => Z u 1) s = Z s 3 := (hder s ⟨lt_trans ha₀a' hs.1, hs.2⟩).2
    rw [hev.deriv_eq, hd]
  have hXanti' : StrictAntiOn X (Set.Icc a' 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hXsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderX s hs]
    exact hneg2 s ⟨le_trans ha₀a'.le hs.1.le, hs.2.le⟩
  have hYanti' : StrictAntiOn Y (Set.Icc a' 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hYsm.continuous.continuousOn fun s hs => ?_
    rw [interior_Icc] at hs
    rw [hderY s hs]
    exact hneg3 s ⟨le_trans ha₀a'.le hs.1.le, hs.2.le⟩
  have hX1 : X 1 = profileX 1 := (hXY 1 ⟨by linarith [ha'], le_rfl⟩).1.trans (by
    rw [hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_zero])
  have hY1 : Y 1 = profileX 1 := (hXY 1 ⟨by linarith [ha'], le_rfl⟩).2.trans (by
    rw [hZb 1 ⟨hc1.le, le_rfl⟩, baseZ_apply_one])
  have ha₀val : a₀ = (1 - 2 * τ) / 4 := by rw [ha₀def, hadef]; ring
  have ha'val : a' ≤ 3 * (1 - 2 * τ) / 8 := by rw [hadef', hadef]; linarith
  have hεa4' : ε < (1 - 2 * τ) / 8 := by rw [hadef] at hεa4; linarith
  rw [ha₀val] at hZsm hZbd hZfix hder hneg2 hneg3 hXanti hYanti
  have hZbd' : ∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, ‖Z s - baseZ s‖ ≤ ρ₀ := by
    intro s hs
    refine le_trans (hZbd s hs) ?_
    have h2 : r ≤ 2 * ρ₀ := le_trans hr2 (min_le_right _ _)
    linarith
  have hXYr : ∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8) 1, X s = Z s 0 ∧ Y s = Z s 1 :=
    fun s hs => hXY s ⟨le_trans ha'val hs.1, hs.2⟩
  have hderXr : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv X s = Z s 2 :=
    fun s hs => hderX s ⟨lt_of_le_of_lt ha'val hs.1, hs.2⟩
  have hderYr : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8) 1, deriv Y s = Z s 3 :=
    fun s hs => hderY s ⟨lt_of_le_of_lt ha'val hs.1, hs.2⟩
  have hXantir : StrictAntiOn X (Set.Icc (3 * (1 - 2 * τ) / 8) 1) :=
    hXanti'.mono (Set.Icc_subset_Icc ha'val le_rfl)
  have hYantir : StrictAntiOn Y (Set.Icc (3 * (1 - 2 * τ) / 8) 1) :=
    hYanti'.mono (Set.Icc_subset_Icc ha'val le_rfl)
  have hXp : ∀ s : ℝ, c ≤ s → X s = profileX s := by
    intro s hs
    by_cases hsc : s ≤ βglue
    · have hZeq : Z s 0 = profileX s := by
        rw [hZb s ⟨hs, le_trans hsc hβ1.le⟩, baseZ_apply_zero]
      change glue s * (Z s 0) + (1 - glue s) * profileX s = profileX s
      rw [hZeq]; ring
    · push_neg at hsc
      have hgl0 : glue s = 0 := hglue_zero_right s hsc.le
      change glue s * (Z s 0) + (1 - glue s) * profileX s = profileX s
      rw [hgl0]; simp
  have hYp : ∀ s : ℝ, c ≤ s → Y s = profileX s := by
    intro s hs
    by_cases hsc : s ≤ βglue
    · have hZeq : Z s 1 = profileX s := by
        rw [hZb s ⟨hs, le_trans hsc hβ1.le⟩, baseZ_apply_one]
      change glue s * (Z s 1) + (1 - glue s) * profileX s = profileX s
      rw [hZeq]; ring
    · push_neg at hsc
      have hgl0 : glue s = 0 := hglue_zero_right s hsc.le
      change glue s * (Z s 1) + (1 - glue s) * profileX s = profileX s
      rw [hgl0]; simp
  have ha'e : a' = 3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 := by rw [hadef', hadef]; ring
  have hXYb : ∀ s ∈ Set.Icc (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
      X s = Z s 0 ∧ Y s = Z s 1 := by
    intro s hs
    have hs' : s ∈ Set.Icc a' 1 := by
      rw [Set.mem_Icc] at hs ⊢
      exact ⟨by linarith [hs.1, ha'e], hs.2⟩
    exact hXY s hs'
  have hderb : ∀ s ∈ Set.Ioo (3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32) 1,
      deriv X s = Z s 2 ∧ deriv Y s = Z s 3 := by
    intro s hs
    have hs' : s ∈ Set.Ioo a' 1 := by
      rw [Set.mem_Ioo] at hs ⊢
      exact ⟨by linarith [hs.1, ha'e], hs.2⟩
    exact ⟨hderX s hs', hderY s hs'⟩
  have hM' : ∃ M : ℝ, 0 < M ∧ (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |h s| ≤ M) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |deriv h s| ≤ M) ∧
      (∀ s ∈ Set.Icc ((1 - 2 * τ) / 4) 1, |iteratedDeriv 2 h s| ≤ M) ∧
      ε * M ≤ 1 / 2 := by
    simpa only [ha₀val] using hM
  exact ⟨ε, hε0, hεε₀, hεa4', Z, hZc, hZsm, hZbd', hZfix, hZb, hder, hneg2, hneg3, hXanti, hYanti,
    X, Y, hXsm, hYsm, hXYr, fun s hs => ⟨hderXr s hs, hderYr s hs⟩,
    hXantir, hYantir, hX1, hY1,
    hXp, hYp, hXYb, hderb, hM'⟩


end Commons.Geometry.Ulam


-- ===== FILE _mine_dev20.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-! ## Tools for the envelope curvature -/

/-- The first derivative of the semicircle. -/
lemma deriv_semicircle (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv semicircle t = -t / semicircle t := by
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  have hsq : semicircle t ^ 2 = 1 - t ^ 2 :=
    semicircle_sq_of_mem_Icc ⟨ht.1.le, ht.2.le⟩
  have hs : 0 < semicircle t := semicircle_pos_of_mem_Ioo ht
  have hd : DifferentiableAt ℝ semicircle t := by
    have h1 : ContDiffAt ℝ ∞ semicircle t :=
      semicircle_contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds ht)
    exact h1.differentiableAt (by simp)
  have hev : (fun u : ℝ => semicircle u ^ 2) =ᶠ[𝓝 t] (fun u : ℝ => 1 - u ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact semicircle_sq_of_mem_Icc ⟨hu.1.le, hu.2.le⟩
  have h1 : deriv (fun u : ℝ => semicircle u ^ 2) t = deriv (fun u : ℝ => 1 - u ^ 2) t :=
    hev.deriv_eq
  have h2 : deriv (fun u : ℝ => semicircle u ^ 2) t = 2 * semicircle t * deriv semicircle t := by
    have hdm : DifferentiableAt ℝ (fun u : ℝ => semicircle u ^ 2) t := hd.pow 2
    have hcomp : (fun u : ℝ => semicircle u ^ 2) = (fun y : ℝ => y ^ 2) ∘ semicircle := rfl
    rw [hcomp, deriv_comp t (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) (semicircle t)) hd]
    simp
  have h3 : deriv (fun u : ℝ => 1 - u ^ 2) t = -2 * t := by
    have : (fun u : ℝ => 1 - u ^ 2) = ((fun _ : ℝ => (1:ℝ)) - (fun u : ℝ => u ^ 2)) := rfl
    rw [this, deriv_sub (by fun_prop) (by fun_prop)]
    simp
  rw [h2, h3] at h1
  have hsne : semicircle t ≠ 0 := ne_of_gt hs
  field_simp at h1 ⊢
  linarith [h1, hsq]

/-- The second derivative of the semicircle. -/
lemma deriv_deriv_semicircle (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv semicircle) t = -1 / (semicircle t) ^ 3 := by
  have hs : 0 < semicircle t := semicircle_pos_of_mem_Ioo ht
  have hsne : semicircle t ≠ 0 := ne_of_gt hs
  have hsq : semicircle t ^ 2 = 1 - t ^ 2 :=
    semicircle_sq_of_mem_Icc ⟨ht.1.le, ht.2.le⟩
  have hd : DifferentiableAt ℝ semicircle t := by
    have h1 : ContDiffAt ℝ ∞ semicircle t :=
      semicircle_contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds ht)
    exact h1.differentiableAt (by simp)
  have hdiff : deriv semicircle =ᶠ[𝓝 t] (fun u : ℝ => -u / semicircle u) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact deriv_semicircle u hu
  rw [hdiff.deriv_eq]
  have hA : HasDerivAt (fun u : ℝ => -u) (-1) t := (hasDerivAt_id t).neg
  have hB : HasDerivAt semicircle (-t / semicircle t) t := by
    have := hd.hasDerivAt
    rwa [deriv_semicircle t ht] at this
  have h := hA.div hB hsne
  change deriv ((fun u : ℝ => -u) / semicircle) t = -1 / (semicircle t) ^ 3
  rw [h.deriv]
  have hsne2 : semicircle t ^ 2 ≠ 0 := pow_ne_zero _ hsne
  field_simp
  linarith [hsq]

/-- `deriv^[2] semicircle 0 < 0`. -/
lemma semicircle_deriv2_zero_neg : deriv^[2] semicircle 0 < 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h := deriv_deriv_semicircle 0 hmem
  have hs : semicircle 0 = 1 := by rw [semicircle]; simp
  have h2 : deriv^[2] semicircle 0 = deriv (deriv semicircle) 0 := rfl
  rw [h2, h, hs]
  norm_num

/-- **Second derivative of a composition with nonvanishing inner derivative.** -/
lemma deriv2_comp_eq_aux {f y v : ℝ → ℝ} {s : ℝ} {U : Set ℝ} (hUo : IsOpen U) (hU : y s ∈ U)
    (hy : deriv y s ≠ 0) (hev : ∀ᶠ u in 𝓝 s, f (y u) = v u)
    (hf : ContDiffOn ℝ 2 f U) (hyc : ContDiff ℝ 2 y) (hvc : ContDiff ℝ 2 v) :
    deriv (deriv f) (y s) =
      (deriv (deriv v) s * deriv y s - deriv v s * deriv (deriv y) s) / (deriv y s) ^ 3 := by
  have hy_diff : DifferentiableAt ℝ y s := (hyc.differentiable (by norm_num)).differentiableAt
  have hy2 : DifferentiableAt ℝ (deriv y) s := hyc.differentiable_deriv_two.differentiableAt
  have hfy : ∀ᶠ u in 𝓝 s, y u ∈ U := ContinuousAt.preimage_mem_nhds hy_diff.continuousAt (hUo.mem_nhds hU)
  have hfd : ∀ᶠ u in 𝓝 s, DifferentiableAt ℝ f (y u) := by
    filter_upwards [hfy] with u hu
    exact (hf.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hu)
  have hf1 : DifferentiableAt ℝ f (y s) :=
    (hf.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hU)
  have hchain : ∀ᶠ u in 𝓝 s, deriv (f ∘ y) u = deriv f (y u) * deriv y u := by
    filter_upwards [hfd] with u hu
    exact deriv_comp u hu ((hyc.differentiable (by norm_num)).differentiableAt)
  have hderivf : DifferentiableAt ℝ (deriv f) (y s) :=
    ((hf.deriv_of_isOpen hUo (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hUo.mem_nhds hU)
  have hA : DifferentiableAt ℝ (fun u : ℝ => deriv f (y u)) s := hderivf.comp s hy_diff
  have hcomp2 : deriv (fun u : ℝ => deriv f (y u)) s = deriv (deriv f) (y s) * deriv y s :=
    deriv_comp s hderivf hy_diff
  have hev' : (fun u : ℝ => f (y u)) =ᶠ[𝓝 s] v := hev
  have hprod : deriv v =ᶠ[𝓝 s] (fun u : ℝ => deriv f (y u) * deriv y u) :=
    (hev'.deriv).symm.trans hchain
  have hstep : deriv (deriv v) s
      = deriv (fun u : ℝ => deriv f (y u) * deriv y u) s := hprod.deriv_eq
  have hmul : deriv (fun u : ℝ => deriv f (y u) * deriv y u) s
      = (deriv (deriv f) (y s) * deriv y s) * deriv y s
        + deriv f (y s) * deriv (deriv y) s := by
    have h := deriv_mul hA hy2
    rw [hcomp2] at h
    exact h
  have hfy_s : deriv f (y s) = deriv v s / deriv y s := by
    have h1 : deriv (fun u : ℝ => f (y u)) s = deriv v s := hev'.deriv_eq
    have h2 : deriv (fun u : ℝ => f (y u)) s = deriv f (y s) * deriv y s :=
      deriv_comp s hf1 hy_diff
    field_simp
    linarith [h1, h2]
  have hkey : deriv (deriv v) s
      = deriv (deriv f) (y s) * (deriv y s) ^ 2
        + (deriv v s / deriv y s) * deriv (deriv y) s := by
    rw [hstep, hmul, hfy_s]
    ring
  rw [hkey]
  field_simp
  ring

/-- **Strict concavity of the envelope.** -/
theorem strictConcaveOn_envelope {y z v w : ℝ → ℝ} {f : ℝ → ℝ}
    (hf_sm : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hy_sm : ContDiff ℝ ∞ y) (hz_sm : ContDiff ℝ ∞ z)
    (hv_sm : ContDiff ℝ ∞ v) (hw_sm : ContDiff ℝ ∞ w)
    (hsc_near : f =ᶠ[𝓝 (0 : ℝ)] semicircle)
    (hy_dec : ∀ s : ℝ, 0 < s → deriv y s < 0)
    (hz_inc : ∀ s : ℝ, 0 < s → 0 < deriv z s)
    (hysurj : ∀ t : ℝ, 0 < t → t < 1 → ∃ s : ℝ, 0 < s ∧ y s = t)
    (hzsurj : ∀ t : ℝ, -1 < t → t < 0 → ∃ s : ℝ, 0 < s ∧ z s = t)
    (hbranch_y : ∀ s : ℝ, 0 < s → f (y s) = v s)
    (hbranch_z : ∀ s : ℝ, 0 < s → f (z s) = w s)
    (hNp : ∀ s : ℝ, 0 < s →
      0 < deriv (deriv v) s * deriv y s - deriv v s * deriv (deriv y) s)
    (hNz : ∀ s : ℝ, 0 < s →
      deriv (deriv w) s * deriv z s - deriv w s * deriv (deriv z) s < 0) :
    StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f := by
  have h2le : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hf_cont fun t ht => ?_
  rw [interior_Icc] at ht
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · obtain ⟨s, hspos, hst⟩ := hzsurj t ht.1 hlt
    have hkey := deriv2_comp_eq_aux (f := f) (y := z) (v := w) (s := s)
      (U := Set.Ioo (-1:ℝ) 1) isOpen_Ioo
      (by rw [hst]; exact ht) (ne_of_gt (hz_inc s hspos))
      (by filter_upwards [Ioi_mem_nhds hspos] with u hu; exact hbranch_z u hu)
      (hf_sm.of_le h2le) (hz_sm.of_le h2le) (hw_sm.of_le h2le)
    have hgoal : deriv^[2] f t = deriv (deriv f) (z s) := by
      rw [show t = z s from hst.symm]
      rfl
    rw [hgoal, hkey]
    exact div_neg_of_neg_of_pos (hNz s hspos) (pow_pos (hz_inc s hspos) 3)
  · subst heq
    have heq2 : deriv^[2] f 0 = deriv^[2] semicircle 0 := (hsc_near.deriv.deriv).eq_of_nhds
    rw [heq2]
    exact semicircle_deriv2_zero_neg
  · obtain ⟨s, hspos, hst⟩ := hysurj t hgt ht.2
    have hkey := deriv2_comp_eq_aux (f := f) (y := y) (v := v) (s := s)
      (U := Set.Ioo (-1:ℝ) 1) isOpen_Ioo
      (by rw [hst]; exact ht) (ne_of_lt (hy_dec s hspos))
      (by filter_upwards [Ioi_mem_nhds hspos] with u hu; exact hbranch_y u hu)
      (hf_sm.of_le h2le) (hy_sm.of_le h2le) (hv_sm.of_le h2le)
    have hgoal : deriv^[2] f t = deriv (deriv f) (y s) := by
      rw [show t = y s from hst.symm]
      rfl
    rw [hgoal, hkey]
    refine div_neg_of_pos_of_neg (hNp s hspos) ?_
    have h1 := hy_dec s hspos
    have h3 : 0 < (deriv y s) ^ 2 := sq_pos_of_ne_zero (ne_of_lt h1)
    have h4 : deriv y s ^ 3 = deriv y s * (deriv y s) ^ 2 := by ring
    rw [h4]
    exact mul_neg_of_neg_of_pos h1 h3

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev22.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma profileX_sq_mul (s : ℝ) : profileX s ^ 2 * (1 + s ^ 2) = 1 := by
  rw [profileX_sq]
  have h : (1:ℝ) + s^2 ≠ 0 := by positivity
  field_simp

lemma deriv_profileX_eq (s : ℝ) : deriv profileX s = -(s / (1 + s ^ 2)) * profileX s := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + u^2) (2*s) s := by
    have h : HasDerivAt (fun u : ℝ => 1 + u^2) (deriv (fun u : ℝ => 1 + u^2) s) s :=
      (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 1 + u^2) s).hasDerivAt
    rwa [show deriv (fun u : ℝ => 1 + u^2) s = 2*s from by simp] at h
  have h2 := h1.sqrt (show (1:ℝ) + s^2 ≠ 0 by positivity)
  have h3 := h2.inv (show Real.sqrt (1 + s^2) ≠ 0 by positivity)
  have hfun : profileX = (fun u : ℝ => Real.sqrt (1 + u^2))⁻¹ := by
    funext u; rw [profileX]; simp [one_div]
  rw [hfun, h3.deriv]
  simp only [Pi.inv_apply]
  rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + s^2)]
  field_simp


/-- `HasDerivAt (fun u => u) 1 s` in a form with uniform instances. -/
lemma hasDerivAt_id' (s : ℝ) : HasDerivAt (fun u : ℝ => u) 1 s := by
  have h : HasDerivAt (fun u : ℝ => u) (deriv (fun u : ℝ => u) s) s :=
    (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => u) s).hasDerivAt
  rwa [show deriv (fun u : ℝ => u) s = 1 from by simp] at h

/-- `deriv profileX` has the explicit derivative `p (2s²-1)/(1+s²)²`. -/
lemma hasDerivAt_deriv_profileX (s : ℝ) :
    HasDerivAt (deriv profileX) (profileX s * (2 * s ^ 2 - 1) / (1 + s ^ 2) ^ 2) s := by
  have hden : HasDerivAt (fun u : ℝ => 1 + u^2) (2*s) s := by
    have h : HasDerivAt (fun u : ℝ => 1 + u^2) (deriv (fun u : ℝ => 1 + u^2) s) s :=
      (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 1 + u^2) s).hasDerivAt
    rwa [show deriv (fun u : ℝ => 1 + u^2) s = 2*s from by simp] at h
  have hne : (1 + s^2) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun u : ℝ => -(u / (1 + u^2)))
      (-((1 * (1 + s^2) - s * (2*s)) / (1 + s^2)^2)) s := by
    have h0 := ((hasDerivAt_id' s).div hden hne).neg
    have hEq : (-((fun u : ℝ => u) / (fun u : ℝ => 1 + u^2)))
        = (fun u : ℝ => -(u / (1 + u^2))) := by funext u; rfl
    rw [hEq] at h0
    exact h0
  have hp : HasDerivAt profileX (-(s / (1 + s^2)) * profileX s) s :=
    (contDiff_profileX.differentiable (by simp) s).hasDerivAt.congr_deriv (deriv_profileX_eq s)
  have hmul := hnum.mul hp
  have hEq : (fun u : ℝ => -(u / (1 + u^2)) * profileX u)
      = ((fun u : ℝ => -(u / (1 + u^2))) * profileX) := rfl
  rw [← hEq] at hmul
  have hval : profileX s * (2 * s ^ 2 - 1) / (1 + s ^ 2) ^ 2
      = -((1 * (1 + s^2) - s * (2*s)) / (1 + s^2)^2) * profileX s
        + (-(s / (1 + s^2))) * (-(s / (1 + s^2)) * profileX s) := by
    field_simp
    ring
  have hmul' := hmul.congr_deriv hval.symm
  have hev : deriv profileX =ᶠ[𝓝 s] (fun u : ℝ => -(u / (1 + u^2)) * profileX u) :=
    Filter.Eventually.of_forall (fun u => deriv_profileX_eq u)
  exact hmul'.congr_of_eventuallyEq hev

lemma deriv_deriv_profileX_eq (s : ℝ) :
    deriv (deriv profileX) s = profileX s * (2 * s ^ 2 - 1) / (1 + s ^ 2) ^ 2 :=
  (hasDerivAt_deriv_profileX s).deriv

lemma hasDerivAt_deriv_profileX' (s : ℝ) :
    HasDerivAt (deriv profileX) (deriv (deriv profileX) s) s :=
  (hasDerivAt_deriv_profileX s).congr_deriv (deriv_deriv_profileX_eq s).symm

/-- `g u = u * profileX u`. -/
lemma hasDerivAt_g (s : ℝ) :
    HasDerivAt (fun u : ℝ => u * profileX u) (profileX s + s * deriv profileX s) s := by
  have h := (hasDerivAt_id' s).mul (contDiff_profileX.differentiable (by simp) s).hasDerivAt
  have hEq : (fun u : ℝ => u * profileX u) = ((fun u : ℝ => u) * profileX) := rfl
  rw [hEq]
  simpa using h

lemma hasDerivAt_deriv_g (s : ℝ) :
    HasDerivAt (deriv (fun u : ℝ => u * profileX u))
      (2 * deriv profileX s + s * deriv (deriv profileX) s) s := by
  have hev : deriv (fun u : ℝ => u * profileX u) =ᶠ[𝓝 s]
      (fun u : ℝ => profileX u + u * deriv profileX u) :=
    Filter.Eventually.of_forall (fun u => (hasDerivAt_g u).deriv)
  have h1 : HasDerivAt (fun u : ℝ => profileX u + u * deriv profileX u)
      (deriv profileX s + (1 * deriv profileX s + s * deriv (deriv profileX) s)) s := by
    have hEq : (fun u : ℝ => profileX u + u * deriv profileX u)
        = (profileX + (fun u : ℝ => u) * deriv profileX) := rfl
    rw [hEq]
    refine ((contDiff_profileX.differentiable (by simp) s).hasDerivAt).add ?_
    exact (hasDerivAt_id' s).mul (hasDerivAt_deriv_profileX' s)
  have hval : deriv profileX s + (1 * deriv profileX s + s * deriv (deriv profileX) s)
      = 2 * deriv profileX s + s * deriv (deriv profileX) s := by ring
  exact (h1.congr_deriv hval).congr_of_eventuallyEq hev

lemma profileX_curvature (s : ℝ) :
    deriv (deriv (fun u : ℝ => u * profileX u)) s * deriv profileX s
      - deriv (fun u : ℝ => u * profileX u) s * deriv (deriv profileX) s
      = 1 / (1 + s ^ 2) ^ 3 := by
  rw [(hasDerivAt_deriv_g s).deriv, (hasDerivAt_g s).deriv, deriv_profileX_eq s,
    deriv_deriv_profileX_eq s]
  have hsq := profileX_sq_mul s
  field_simp
  have hX : -(s ^ 2 * (-(2 * (1 + s ^ 2)) + (2 * s ^ 2 - 1)))
      - (2 * s ^ 2 - 1) * (1 + s ^ 2 + -s ^ 2) = 1 + s ^ 2 := by ring
  rw [hX, hsq]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev23.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- Coordinate-wise derivative of a state-valued curve. -/
lemma deriv_apply_state (Z : ℝ → VS) (i : Fin 4) {s : ℝ} (hZ : DifferentiableAt ℝ Z s) :
    (deriv Z s) i = deriv (fun u : ℝ => Z u i) s := by
  have h := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt s hZ.hasDerivAt
  exact (h.deriv).symm

lemma abs_profileX_le_one (s : ℝ) : |profileX s| ≤ 1 :=
  abs_le.mpr (profileX_mem_Icc s)

lemma abs_deriv_profileX_le (s : ℝ) : |deriv profileX s| ≤ 1 / 2 := by
  rw [deriv_profileX_eq s]
  have h1 : |-(s / (1 + s ^ 2))| ≤ 1 / 2 := by
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + s^2), div_le_iff₀ (by positivity)]
    nlinarith [sq_abs s, sq_nonneg (|s| - 1)]
  have h2 : |profileX s| ≤ 1 := abs_profileX_le_one s
  calc |-(s / (1 + s ^ 2)) * profileX s| = |-(s / (1 + s ^ 2))| * |profileX s| := abs_mul _ _
    _ ≤ (1/2) * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1/2 := by norm_num

lemma abs_deriv2_profileX_le (s : ℝ) (hs : |s| ≤ 1) :
    |deriv (deriv profileX) s| ≤ 1 := by
  rw [deriv_deriv_profileX_eq s, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1+s^2)^2)]
  have hp : |profileX s| ≤ 1 := abs_profileX_le_one s
  have hnum : |2 * s ^ 2 - 1| ≤ 1 + s ^ 2 := by
    have hs2 : s ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg s, sq_abs s, hs]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg s, hs2]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (1+s^2)^2)]
  have hden : (1:ℝ) ≤ (1+s^2)^2 := by nlinarith [sq_nonneg s]
  have h1 : |profileX s| * |2 * s^2 - 1| ≤ 1 * (1 + s^2) :=
    mul_le_mul hp hnum (abs_nonneg _) (by norm_num)
  have h2 : (1:ℝ) * (1 + s^2) ≤ 1 * (1+s^2)^2 := by nlinarith [hden]
  linarith [h1, h2]

lemma abs_le_abs_add_abs_sub (a b : ℝ) : |a| ≤ |b| + |a - b| := by
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le b, le_abs_self b, neg_abs_le (a - b), le_abs_self (a - b)]

lemma abs_chain5 (a b c d e : ℝ) : |a + b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;>
    linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b, neg_abs_le c,
      le_abs_self c, neg_abs_le d, le_abs_self d, neg_abs_le e, le_abs_self e]

lemma branch_deriv {y h : ℝ → ℝ} (hy : ContDiff ℝ ∞ y) (hh : ContDiff ℝ ∞ h) (ε s : ℝ) :
    deriv (fun u : ℝ => u * y u + ε * h u) s = y s + s * deriv y s + ε * deriv h s := by
  have hy_diff : Differentiable ℝ y := hy.differentiable (by simp)
  have hh_diff : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show (fun u : ℝ => u * y u + ε * h u)
      = ((fun u : ℝ => u) * y + (fun u : ℝ => ε) * h) from rfl,
    deriv_add (by fun_prop) (by fun_prop),
    deriv_mul (by fun_prop) (by fun_prop),
    deriv_mul (by fun_prop) (by fun_prop)]
  simp

lemma branch_deriv2 {y h : ℝ → ℝ} (hy : ContDiff ℝ ∞ y) (hh : ContDiff ℝ ∞ h) (ε s : ℝ) :
    deriv (deriv (fun u : ℝ => u * y u + ε * h u)) s
      = 2 * deriv y s + s * deriv (deriv y) s + ε * deriv (deriv h) s := by
  have hy_diff : Differentiable ℝ y := hy.differentiable (by simp)
  have hh_diff : Differentiable ℝ h := hh.differentiable (by simp)
  have hy1 : Differentiable ℝ (deriv y) := by
    have h := hy.iterate_deriv 1
    rw [Function.iterate_one] at h
    exact h.differentiable (by simp)
  have hh1 : Differentiable ℝ (deriv h) := by
    have h := hh.iterate_deriv 1
    rw [Function.iterate_one] at h
    exact h.differentiable (by simp)
  have hd : deriv (fun u : ℝ => u * y u + ε * h u)
      = fun t : ℝ => y t + t * deriv y t + ε * deriv h t := by
    funext t
    exact branch_deriv hy hh ε t
  rw [hd]
  rw [show (fun t : ℝ => y t + t * deriv y t + ε * deriv h t)
      = (((fun t : ℝ => y t) + (fun t : ℝ => t) * (deriv y)) + (fun t : ℝ => ε) * (deriv h))
      from rfl,
    deriv_add (by fun_prop) (by fun_prop),
    deriv_add (by fun_prop) (by fun_prop),
    deriv_mul (by fun_prop) (by fun_prop),
    deriv_mul (by fun_prop) (by fun_prop)]
  simp
  ring

lemma Np_expand {y h : ℝ → ℝ} (hy : ContDiff ℝ ∞ y) (hh : ContDiff ℝ ∞ h) (ε s : ℝ) :
    deriv (deriv (fun u : ℝ => u * y u + ε * h u)) s * deriv y s
      - deriv (fun u : ℝ => u * y u + ε * h u) s * deriv (deriv y) s
      = 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s
        + ε * (deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s) := by
  rw [branch_deriv2 hy hh ε s, branch_deriv hy hh ε s]
  ring

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma profileX_base_curv (s : ℝ) :
    2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s
      = 1 / (1 + s ^ 2) ^ 3 := by
  have h := profileX_curvature s
  rw [(hasDerivAt_deriv_g s).deriv, (hasDerivAt_g s).deriv] at h
  linarith [h]

/-- The quantitative curvature estimate: if `y` is `C²`-close to `profileX` (with deviations `ρ`,
`ρ`, `ηD`) and `ε · h` is small in `C²`, then `N_p(y,ε,h) > 0`. -/
lemma Np_pos_of_close {y h : ℝ → ℝ} {ε ρ ηD Ch Ch' Ch'' τ c : ℝ}
    (hτsmall : 2 * τ < 1) (hc1 : c ≤ 1)
    (hρ0 : 0 ≤ ρ) (hηD0 : 0 ≤ ηD) (hCh'0 : 0 ≤ Ch') (hCh''0 : 0 ≤ Ch'')
    (hy : ContDiff ℝ ∞ y) (hh : ContDiff ℝ ∞ h)
    (hhb : ∀ s : ℝ, |h s| ≤ Ch) (hhb' : ∀ s : ℝ, |deriv h s| ≤ Ch')
    (hhb'' : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ Ch'')
    (hyb : ∀ s : ℝ, 0 < s → |y s - profileX s| ≤ ρ)
    (hyb' : ∀ s : ℝ, 0 < s → |deriv y s - deriv profileX s| ≤ ρ)
    (hyb'' : ∀ s : ℝ, 0 < s → |deriv (deriv y) s - deriv (deriv profileX) s| ≤ ηD)
    (hsmall : 2 * ρ + 2 * ρ ^ 2 + ηD + ρ + ρ * ηD
      + |ε| * (Ch'' * (1 / 2 + ρ) + Ch' * (1 + ηD)) < 1 / 8) :
    ∀ s ∈ Set.Icc (1 - 2 * τ) c,
      0 < deriv (deriv (fun u : ℝ => u * y u + ε * h u)) s * deriv y s
        - deriv (fun u : ℝ => u * y u + ε * h u) s * deriv (deriv y) s := by
  intro s hs
  have hs1 : s ≤ 1 := le_trans hs.2 hc1
  have hs2 : 0 < s := lt_of_lt_of_le (by linarith : (0:ℝ) < 1 - 2 * τ) hs.1
  rw [Np_expand hy hh ε s]
  have hdev : |y s - profileX s| ≤ ρ := hyb s hs2
  have hdev1 : |deriv y s - deriv profileX s| ≤ ρ := hyb' s hs2
  have hdev2 : |deriv (deriv y) s - deriv (deriv profileX) s| ≤ ηD := hyb'' s hs2
  have hpb : |profileX s| ≤ 1 := abs_profileX_le_one s
  have hpb1 : |deriv profileX s| ≤ 1 / 2 := abs_deriv_profileX_le s
  have hpb2 : |deriv (deriv profileX) s| ≤ 1 := by
    apply abs_deriv2_profileX_le
    rw [abs_le]
    exact ⟨by linarith, hs1⟩
  -- the base curvature is at least `1/8`
  have hbase : 1 / 8 ≤ 2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s := by
    rw [profileX_base_curv s, le_div_iff₀ (by positivity)]
    have hsq : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s, hs1]
    have hs2 : (1 + s ^ 2) ≤ 2 := by nlinarith [hsq]
    have h1 : (0:ℝ) ≤ 1 + s ^ 2 := by positivity
    have hcube : (1 + s ^ 2) ^ 3 ≤ 8 := by
      have h23 : (2:ℝ) ^ 3 = 8 := by norm_num
      rw [← h23]
      gcongr
    nlinarith [hcube]
  -- the `q`-part of the error
  have hA : |(2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s)
      - (2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s)|
      ≤ 2 * ρ + 2 * ρ ^ 2 + ηD + ρ + ρ * ηD := by
    have hexp : (2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s)
        - (2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s)
        = 4 * deriv profileX s * (deriv y s - deriv profileX s)
          + 2 * (deriv y s - deriv profileX s) ^ 2
          - profileX s * (deriv (deriv y) s - deriv (deriv profileX) s)
          - (y s - profileX s) * deriv (deriv profileX) s
          - (y s - profileX s) * (deriv (deriv y) s - deriv (deriv profileX) s) := by ring
    rw [hexp]
    have h1 : |4 * deriv profileX s * (deriv y s - deriv profileX s)| ≤ 4 * (1 / 2) * ρ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
      have h := mul_le_mul hpb1 hdev1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1 / 2)
      nlinarith [h, abs_nonneg (deriv profileX s), abs_nonneg (deriv y s - deriv profileX s)]
    have h2 : |2 * (deriv y s - deriv profileX s) ^ 2| ≤ 2 * ρ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow]
      nlinarith [hdev1, abs_nonneg (deriv y s - deriv profileX s)]
    have h3 : |profileX s * (deriv (deriv y) s - deriv (deriv profileX) s)| ≤ 1 * ηD := by
      rw [abs_mul]
      have h := mul_le_mul hpb hdev2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith [h, abs_nonneg (profileX s), abs_nonneg (deriv (deriv y) s - deriv (deriv profileX) s)]
    have h4 : |(y s - profileX s) * deriv (deriv profileX) s| ≤ ρ * 1 := by
      rw [abs_mul]
      have h := mul_le_mul hdev hpb2 (abs_nonneg _) hρ0
      nlinarith [h, abs_nonneg (y s - profileX s), abs_nonneg (deriv (deriv profileX) s)]
    have h5 : |(y s - profileX s) * (deriv (deriv y) s - deriv (deriv profileX) s)|
        ≤ ρ * ηD := by
      rw [abs_mul]
      have h := mul_le_mul hdev hdev2 (abs_nonneg _) hρ0
      nlinarith [h, abs_nonneg (y s - profileX s), abs_nonneg (deriv (deriv y) s - deriv (deriv profileX) s)]
    calc |4 * deriv profileX s * (deriv y s - deriv profileX s)
          + 2 * (deriv y s - deriv profileX s) ^ 2
          - profileX s * (deriv (deriv y) s - deriv (deriv profileX) s)
          - (y s - profileX s) * deriv (deriv profileX) s
          - (y s - profileX s) * (deriv (deriv y) s - deriv (deriv profileX) s)|
        ≤ |4 * deriv profileX s * (deriv y s - deriv profileX s)|
          + |2 * (deriv y s - deriv profileX s) ^ 2|
          + |profileX s * (deriv (deriv y) s - deriv (deriv profileX) s)|
          + |(y s - profileX s) * deriv (deriv profileX) s|
          + |(y s - profileX s) * (deriv (deriv y) s - deriv (deriv profileX) s)| :=
          abs_chain5 _ _ _ _ _
      _ ≤ 4 * (1 / 2) * ρ + 2 * ρ ^ 2 + 1 * ηD + ρ * 1 + ρ * ηD := by
          linarith [h1, h2, h3, h4, h5]
      _ = 2 * ρ + 2 * ρ ^ 2 + ηD + ρ + ρ * ηD := by ring
  -- the `εh`-part of the error
  have hB : |ε * (deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s)|
      ≤ |ε| * (Ch'' * (1 / 2 + ρ) + Ch' * (1 + ηD)) := by
    have hid : deriv (deriv h) s = iteratedDeriv 2 h s := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : |deriv (deriv h) s| ≤ Ch'' := by rw [hid]; exact hhb'' s
    have h2 : |deriv h s| ≤ Ch' := hhb' s
    have h3 : |deriv y s| ≤ 1 / 2 + ρ := by
      have := abs_le_abs_add_abs_sub (deriv y s) (deriv profileX s)
      linarith [this, hdev1, hpb1]
    have h4 : |deriv (deriv y) s| ≤ 1 + ηD := by
      have := abs_le_abs_add_abs_sub (deriv (deriv y) s) (deriv (deriv profileX) s)
      linarith [this, hdev2, hpb2]
    have h5 : |deriv (deriv h) s * deriv y s| ≤ Ch'' * (1 / 2 + ρ) := by
      rw [abs_mul]
      exact mul_le_mul h1 h3 (abs_nonneg _) hCh''0
    have h6 : |deriv h s * deriv (deriv y) s| ≤ Ch' * (1 + ηD) := by
      rw [abs_mul]
      exact mul_le_mul h2 h4 (abs_nonneg _) hCh'0
    have h7 : |deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s|
        ≤ |deriv (deriv h) s * deriv y s| + |deriv h s * deriv (deriv y) s| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (deriv (deriv h) s * deriv y s),
        le_abs_self (deriv (deriv h) s * deriv y s), neg_abs_le (deriv h s * deriv (deriv y) s),
        le_abs_self (deriv h s * deriv (deriv y) s)]
    rw [abs_mul]
    have h8 : |deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s|
        ≤ Ch'' * (1 / 2 + ρ) + Ch' * (1 + ηD) := by linarith [h5, h6, h7]
    exact mul_le_mul_of_nonneg_left h8 (abs_nonneg ε)
  -- conclude
  have h2 : (2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s)
      ≥ (2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s)
        - (2 * ρ + 2 * ρ ^ 2 + ηD + ρ + ρ * ηD) := by
    have := neg_abs_le ((2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s)
      - (2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s))
    linarith [this, hA]
  have h3 : ε * (deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s)
      ≥ -(|ε| * (Ch'' * (1 / 2 + ρ) + Ch' * (1 + ηD))) := by
    have := neg_abs_le (ε * (deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s))
    linarith [this, hB]
  have h4 : (2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s)
      - (2 * ρ + 2 * ρ ^ 2 + ηD + ρ + ρ * ηD)
      - |ε| * (Ch'' * (1 / 2 + ρ) + Ch' * (1 + ηD)) > 0 := by linarith [hbase, hsmall]
  nlinarith [h2, h3, h4]

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev24.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The base curvature of `profileX` is positive. -/
lemma Np_profileX_pos (s : ℝ) :
    0 < deriv (deriv (fun u : ℝ => u * profileX u)) s * deriv profileX s
      - deriv (fun u : ℝ => u * profileX u) s * deriv (deriv profileX) s := by
  have h := Np_expand (y := profileX) (h := fun _ : ℝ => 0) (ε := 0) contDiff_profileX
    contDiff_const s
  have h2 : deriv (deriv (fun u : ℝ => u * profileX u)) s * deriv profileX s
      - deriv (fun u : ℝ => u * profileX u) s * deriv (deriv profileX) s
      = 2 * (deriv profileX s) ^ 2 - profileX s * deriv (deriv profileX) s := by
    simpa using h
  rw [h2, profileX_base_curv s]
  positivity

/-- Outside the perturbative window, `N_p` reduces to the base curvature. -/
lemma Np_pos_of_eventually {y h : ℝ → ℝ} {ε s : ℝ}
    (hy : y =ᶠ[𝓝 s] profileX) (hh : h =ᶠ[𝓝 s] fun _ => (0:ℝ)) :
    0 < deriv (deriv (fun u : ℝ => u * y u + ε * h u)) s * deriv y s
      - deriv (fun u : ℝ => u * y u + ε * h u) s * deriv (deriv y) s := by
  have hfun : (fun u : ℝ => u * y u + ε * h u) =ᶠ[𝓝 s] (fun u : ℝ => u * profileX u) := by
    filter_upwards [hy, hh] with u hu1 hu2
    rw [hu1, hu2]; ring
  have h1 : deriv (fun u : ℝ => u * y u + ε * h u) s = deriv (fun u : ℝ => u * profileX u) s :=
    hfun.deriv_eq
  have h2 : deriv (deriv (fun u : ℝ => u * y u + ε * h u)) s
      = deriv (deriv (fun u : ℝ => u * profileX u)) s := (hfun.deriv.deriv).eq_of_nhds
  have h3 : deriv y s = deriv profileX s := hy.deriv_eq
  have h4 : deriv (deriv y) s = deriv (deriv profileX) s := (hy.deriv.deriv).eq_of_nhds
  rw [h1, h2, h3, h4]
  exact Np_profileX_pos s

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma deriv_neg' (f : ℝ → ℝ) : deriv (fun u : ℝ => -f u) = fun u => -deriv f u := by
  funext u
  rcases Classical.em (DifferentiableAt ℝ f u) with hd | hd
  · exact (hd.hasDerivAt.neg).deriv
  · have h1 : ¬ DifferentiableAt ℝ (fun u : ℝ => -f u) u := by
      intro hc
      exact hd (by simpa using hc.neg)
    rw [deriv_zero_of_not_differentiableAt h1, deriv_zero_of_not_differentiableAt hd]
    simp

/-- **The mirror identity**: the curvature expression for the negative branch equals minus the one
for the positive profile `Xt`. -/
lemma Nn_eq_neg_Np (Xt h : ℝ → ℝ) (ε s : ℝ) :
    deriv (deriv (fun u : ℝ => -(u * (-(Xt u)) + ε * h u))) s * deriv (fun u : ℝ => -(Xt u)) s
      - deriv (fun u : ℝ => -(u * (-(Xt u)) + ε * h u)) s
        * deriv (deriv (fun u : ℝ => -(Xt u))) s
      = - (deriv (deriv (fun u : ℝ => u * Xt u + (-ε) * h u)) s * deriv Xt s
        - deriv (fun u : ℝ => u * Xt u + (-ε) * h u) s * deriv (deriv Xt) s) := by
  have hw : (fun u : ℝ => -(u * (-(Xt u)) + ε * h u))
      = (fun u : ℝ => u * Xt u + (-ε) * h u) := by
    funext u; ring
  have hzw : deriv (fun u : ℝ => -(Xt u)) = fun u : ℝ => -deriv Xt u := deriv_neg' Xt
  rw [hw, hzw, deriv_neg' (deriv Xt)]
  simp only [Pi.neg_apply]
  ring

/-- **Density-free continuity limit.**  If `g` and `φ` are continuous at `t`, agree on `Ioo a b`
and `t ∈ Icc a b`, then they agree at `t`. -/
lemma eq_of_continuousAt_of_eqOn_Ioo {g φ : ℝ → ℝ} {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Set.Icc a b) (hg : ContinuousAt g t) (hφ : ContinuousAt φ t)
    (heq : Set.EqOn g φ (Set.Ioo a b)) : g t = φ t := by
  have hl : (𝓝[Set.Ioo a b] t).NeBot := by
    rw [nhdsWithin_neBot]
    intro s hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    have hc0 : 0 < min (ε / 2) ((b - a) / 2) := lt_min (by linarith) (by linarith)
    have hc1 : min (ε / 2) ((b - a) / 2) ≤ ε / 2 := min_le_left _ _
    have hc2 : min (ε / 2) ((b - a) / 2) ≤ (b - a) / 2 := min_le_right _ _
    rcases lt_or_eq_of_le ht.1 with h | h
    · rcases lt_or_eq_of_le ht.2 with h2 | h2
      · exact ⟨t, hεs (by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩),
          ⟨h, h2⟩⟩
      · refine ⟨b - min (ε / 2) ((b - a) / 2), hεs ?_, ?_⟩
        · rw [h2, Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith
        · exact ⟨by linarith, by linarith⟩
    · refine ⟨a + min (ε / 2) ((b - a) / 2), hεs ?_, ?_⟩
      · rw [← h, Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      · exact ⟨by linarith, by linarith⟩
  have h1 : Tendsto g (𝓝[Set.Ioo a b] t) (𝓝 (g t)) := hg.tendsto.mono_left inf_le_left
  have h2 : Tendsto g (𝓝[Set.Ioo a b] t) (𝓝 (φ t)) :=
    Tendsto.congr' (by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (heq hu).symm)
      (hφ.tendsto.mono_left inf_le_left)
  exact tendsto_nhds_unique h1 h2


end Commons.Geometry.Ulam


-- ===== FILE _mine_dev21.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Commons.Geometry.Ulam
open RyaboginVolterra

lemma profileX_one_lt_v2 : profileX 1 < 1 := by
  have h : (1 : ℝ) < Real.sqrt (1 + 1 ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [profileX]
  exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr h

/-- `h` vanishes on `s ≤ 1 - 2 τ` (using flatness at the left endpoint of the window). -/
lemma h_eq_zero_of_le_v2 {τ η : ℝ} {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hflat : ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0)
    (hη : 0 < η) {s : ℝ} (hs : s ≤ 1 - 2 * τ) : h s = 0 := by
  rcases lt_or_eq_of_le hs with h | h
  · by_contra hne
    have hmem := hsupp (by simpa [Function.mem_support] using hne)
    exact absurd hmem.1 (not_le.mpr h)
  · subst h
    exact hflat _ le_rfl (by linarith)

/-- `h` vanishes on `1 - τ ≤ s`. -/
lemma h_eq_zero_of_ge_v2 {τ : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    {s : ℝ} (hs : 1 - τ ≤ s) : h s = 0 := by
  have hright : ∀ t : ℝ, 1 - τ < t → h t = 0 := by
    intro t ht
    by_contra hne
    have hmem := hsupp (by simpa [Function.mem_support] using hne)
    exact absurd hmem.2 (not_le.mpr ht)
  rcases lt_or_eq_of_le hs with h | h
  · exact hright s h
  · subst h
    have hev : (fun t : ℝ => h t) =ᶠ[𝓝[Set.Ioi (1 - τ)] (1 - τ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hright t (Set.mem_Ioi.mp ht)
    have h1 : Filter.Tendsto (fun t : ℝ => h t) (𝓝[Set.Ioi (1 - τ)] (1 - τ)) (𝓝 0) :=
      tendsto_const_nhds.congr' hev.symm
    have h2 : Filter.Tendsto (fun t : ℝ => h t) (𝓝[Set.Ioi (1 - τ)] (1 - τ)) (𝓝 (h (1 - τ))) :=
      hh.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h2 h1

/-- `deriv h` vanishes at every point where `h` vanishes on a neighbourhood. -/
lemma deriv_h_eq_zero_of_nhds_v2 {h : ℝ → ℝ} {s : ℝ}
    (hev : h =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ))) : deriv h s = 0 := by
  have hd := hev.deriv_eq
  simpa using hd

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- **The even-dimensional perturbation lemma, assembled.**  Same statement as
`honest_perturbation_tau`; the proof collects the Volterra solution, the `C^{n+2}` device `f̂`, the
device's moment identities (Steps 1-2 of the paper) and the final envelope function `f`. -/
lemma honest_perturbation_tau_aux_full (n : ℕ) (hn : 2 ≤ n) (τ : ℝ) (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    (h : ℝ → ℝ)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hh_ne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_flat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x y f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + (ε • h) s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + (ε • h) s) ^ 2) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) * (t + deriv (ε • h) s)) = 0) := by
  have hh : ContDiff ℝ ∞ h := contDiffOn_univ.mp hh_cont
  set c : ℝ := 1 - τ / 2 with hcdef
  have hc : 1 - τ < c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hflat := hh_flat
  obtain ⟨η, hη0, hη⟩ := hflat
  -- ------------------------------------------------------------------
  -- (i) `C²`-bounds for `h` on all of `ℝ` (to control the perturbation `ε • h`)
  -- ------------------------------------------------------------------
  have hsupp_le : ∀ s : ℝ, s ≤ 1 - 2 * τ → h s = 0 :=
    fun s hs => h_eq_zero_of_le_v2 hh_supp hη hη0 hs
  have hsupp_ge : ∀ s : ℝ, 1 - τ ≤ s → h s = 0 :=
    fun s hs => h_eq_zero_of_ge_v2 hh hh_supp hs
  have hα0 : (0:ℝ) < (1 - 2 * τ) / 4 := by linarith
  have hα1le : (1 - 2 * τ) / 4 ≤ 1 := by linarith
  obtain ⟨Ch₀, hCh₀⟩ :=
    (isCompact_Icc (a := (1 - 2 * τ) / 4) (b := 1)).exists_bound_of_continuousOn
      hh.continuous.continuousOn
  have hdcont : Continuous (deriv h) := hh.continuous_deriv (by simp)
  obtain ⟨Chd₀, hChd₀⟩ :=
    (isCompact_Icc (a := (1 - 2 * τ) / 4) (b := 1)).exists_bound_of_continuousOn hdcont.continuousOn
  have h2cont : Continuous (iteratedDeriv 2 h) := by
    have hh2 := (hh.iterate_deriv 2).continuous
    simpa [iteratedDeriv_eq_iterate] using hh2
  obtain ⟨Chdd₀, hChdd₀⟩ :=
    (isCompact_Icc (a := (1 - 2 * τ) / 4) (b := 1)).exists_bound_of_continuousOn h2cont.continuousOn
  set Ch : ℝ := max Ch₀ 0 with hChdef
  set Chd : ℝ := max Chd₀ 0 with hChddef
  set Chdd : ℝ := max Chdd₀ 0 with hChdddef
  have hChd0 : 0 ≤ Chd := le_max_right _ _
  have hChdd0 : 0 ≤ Chdd := le_max_right _ _
  have hzero_nhds : ∀ s : ℝ, s ∉ Set.Icc ((1 - 2 * τ) / 4) 1 → h =ᶠ[𝓝 s] fun _ => (0:ℝ) := by
    intro s hs
    have hs' : s < (1 - 2 * τ) / 4 ∨ 1 < s := by
      by_contra hcon
      push_neg at hcon
      exact hs ⟨hcon.1, hcon.2⟩
    rcases hs' with h1 | h1
    · filter_upwards [Iio_mem_nhds (show s < 1 - 2 * τ by linarith)] with u hu
      exact hsupp_le u hu.le
    · filter_upwards [Ioi_mem_nhds (show 1 - τ < s by linarith)] with u hu
      exact hsupp_ge u hu.le
  have hhb : ∀ s : ℝ, |h s| ≤ Ch := by
    intro s
    by_cases hs : s ∈ Set.Icc ((1 - 2 * τ) / 4) 1
    · have h1 : ‖h s‖ ≤ Ch₀ := hCh₀ s hs
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · have hz : h s = 0 := hzero_nhds s hs |>.eq_of_nhds
      rw [hz, abs_zero]; exact le_max_right _ _
  have hhbd : ∀ s : ℝ, |deriv h s| ≤ Chd := by
    intro s
    by_cases hs : s ∈ Set.Icc ((1 - 2 * τ) / 4) 1
    · have h1 : ‖deriv h s‖ ≤ Chd₀ := hChd₀ s hs
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · have hz : deriv h s = 0 := by
        rw [(hzero_nhds s hs).deriv_eq]; simp
      rw [hz, abs_zero]; exact le_max_right _ _
  have hhbdd : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ Chdd := by
    intro s
    by_cases hs : s ∈ Set.Icc ((1 - 2 * τ) / 4) 1
    · have h1 : ‖iteratedDeriv 2 h s‖ ≤ Chdd₀ := hChdd₀ s hs
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · have hz : iteratedDeriv 2 h s = 0 := by
        rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        rw [(hzero_nhds s hs).deriv.deriv_eq]; simp
      rw [hz, abs_zero]; exact le_max_right _ _
  -- ------------------------------------------------------------------
  -- (ii) the deviation radius of the perturbative window and the C¹ bound
  -- ------------------------------------------------------------------
  have h1_1000 : (0:ℝ) < 1 / 1000 := by norm_num
  obtain ⟨a₀d, ha₀d, ρd, hρd, hρdle, hdev⟩ :=
    deriv_deviation_bound n hn hh (α := (1 - 2 * τ) / 4) hα0 hα1le (ρ₀ := 1 / 1000) (by norm_num)
      (η := 1 / 1000) h1_1000
  -- ------------------------------------------------------------------
  -- (iii) the scale bound
  -- ------------------------------------------------------------------
  set ε₀ : ℝ := min (1 / 1000) (1 / (100 * (Chd + Chdd + 1))) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (by norm_num) (by positivity)
  obtain ⟨ε, hε0, hεmin, hεsmall, Z, hZc, hZsm, hZbd, hZfix, hZb, hZder, hZneg2, hZneg3, hZa0,
    hZa1, X, Y, hXsm, hYsm, hXY, hderXY, hXanti, hYanti, hX1, hY1, hXp, hYp, hXYb, hderb, hMdata⟩ :=
    perturbation_data_param ρd (min ε₀ a₀d) hρd (lt_min hε₀pos ha₀d) n hn hτ0 hτsmall hh hh_supp
      hh_flat hc hc1
  have hεa₀d : ε < a₀d := lt_of_lt_of_le hεmin (min_le_right _ _)
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεmin (min_le_left _ _)
  -- the quantitative smallness of `ε · |h|` and `ε · |deriv h|` from the Volterra layer
  obtain ⟨Mh, hMh0, hMhb, hMhd, hMhd2, hεMh⟩ := hMdata
  have hεMh' : ε * Mh ≤ 1 / 2 := hεMh
  have haRow0 : 0 < aRow τ := aRow_pos_of τ |>.mpr hτsmall
  have haRow_lt1 : aRow τ < 1 := aRow_lt_one (by linarith)
  have haRow_ge : (1 - 2 * τ) / 4 ≤ aRow τ := by unfold aRow; linarith
  have haRow_le38 : aRow τ ≤ 3 / 8 := aRow_le τ hτ0.le
  have h12t : (0:ℝ) < 1 - 2 * τ := by linarith
  set a₁ : ℝ := 3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 with ha₁def
  have ha₁lt : a₁ < aRow τ := by rw [ha₁def]; unfold aRow; linarith
  have ha₁pos : (0:ℝ) < a₁ := by rw [ha₁def]; linarith
  -- `h` vanishes below the window and above it
  have h_le : ∀ s : ℝ, s ≤ 1 - 2 * τ → h s = 0 := fun s hs => h_eq_zero_of_le_v2 hh_supp hη hη0 hs
  have h_ge : ∀ s : ℝ, 1 - τ ≤ s → h s = 0 := fun s hs => h_eq_zero_of_ge_v2 hh hh_supp hs
  -- `deriv X`, `deriv Y` do not vanish on the row interval
  have hXder : ∀ s ∈ Set.Icc (aRow τ) 1, deriv X s ≠ 0 := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have h1 := (hderb s ⟨lt_of_lt_of_le ha₁lt hs.1, hlt⟩).1
      rw [h1]
      exact ne_of_lt (hZneg2 s ⟨le_trans haRow_ge hs.1, hs.2⟩)
    · subst heq
      have hev : X =ᶠ[𝓝 (1:ℝ)] profileX := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (1:ℝ) ∈ Set.Ioi c from hc1)] with u hu
        exact hXp u hu.le
      rw [hev.deriv_eq]
      exact ne_of_lt (deriv_profileX_neg (by norm_num))
  have hYder : ∀ s ∈ Set.Icc (aRow τ) 1, deriv Y s ≠ 0 := by
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have h1 := (hderb s ⟨lt_of_lt_of_le ha₁lt hs.1, hlt⟩).2
      rw [h1]
      exact ne_of_lt (hZneg3 s ⟨le_trans haRow_ge hs.1, hs.2⟩)
    · subst heq
      have hev : Y =ᶠ[𝓝 (1:ℝ)] profileX := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (1:ℝ) ∈ Set.Ioi c from hc1)] with u hu
        exact hYp u hu.le
      rw [hev.deriv_eq]
      exact ne_of_lt (deriv_profileX_neg (by norm_num))
  have hXc' : ∀ s ∈ Set.Icc c 1, X s = profileX s := fun s hs => hXp s hs.1
  have hYc' : ∀ s ∈ Set.Icc c 1, Y s = profileX s := fun s hs => hYp s hs.1
  -- the quantitative separation of the row start from `profileX 1`
  have hXbig : profileX 1 < X (aRow τ) := by
    have hmem : aRow τ ∈ Set.Icc ((1 - 2 * τ) / 4) 1 := ⟨haRow_ge, haRow_lt1.le⟩
    have hbd := abs_apply_le_norm_state (Z (aRow τ) - baseZ (aRow τ)) 0
    have h2 : |Z (aRow τ) 0 - baseZ (aRow τ) 0| ≤ ρd := by
      refine le_trans ?_ (hZbd (aRow τ) hmem)
      simpa [Pi.sub_apply] using hbd
    rw [baseZ_apply_zero] at h2
    have h3 : X (aRow τ) = Z (aRow τ) 0 := (hXY (aRow τ) ⟨le_rfl, haRow_lt1.le⟩).1
    rw [h3]
    have h4 : -|Z (aRow τ) 0 - profileX (aRow τ)| ≤ Z (aRow τ) 0 - profileX (aRow τ) := neg_abs_le _
    have h5 : profileX 1 < profileX (aRow τ) - 1 / 128 := by
      have h6 : (8:ℝ) / 9 ≤ profileX (3 / 8) := by
        have h : (0:ℝ) < 1 + (3 / 8) ^ 2 := by norm_num
        rw [profileX, le_div_iff₀ (Real.sqrt_pos.mpr h)]
        have hsq := Real.sq_sqrt (le_of_lt h)
        nlinarith [hsq, Real.sqrt_nonneg (1 + (3/8)^2)]
      have h7 : profileX (3 / 8) ≤ profileX (aRow τ) :=
        profileX_le_profileX' haRow0.le haRow_le38
      have h8 : profileX 1 ≤ 3 / 4 := by
        rw [profileX, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1 + 1^2))]
        have h4' : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 3/2)]
          norm_num
        calc 1 = (3/4) * (4/3) := by norm_num
          _ ≤ (3/4) * Real.sqrt 2 := by
                have : (4:ℝ)/3 ≤ Real.sqrt 2 := by
                  rw [Real.le_sqrt (by norm_num) (by norm_num)]
                  norm_num
                linarith
          _ = (3/4) * Real.sqrt (1 + 1^2) := by norm_num
      linarith
    linarith
  have hYbig : profileX 1 < Y (aRow τ) := by
    have hmem : aRow τ ∈ Set.Icc ((1 - 2 * τ) / 4) 1 := ⟨haRow_ge, haRow_lt1.le⟩
    have hbd := abs_apply_le_norm_state (Z (aRow τ) - baseZ (aRow τ)) 1
    have h2 : |Z (aRow τ) 1 - baseZ (aRow τ) 1| ≤ ρd := by
      refine le_trans ?_ (hZbd (aRow τ) hmem)
      simpa [Pi.sub_apply] using hbd
    rw [baseZ_apply_one] at h2
    have h3 : Y (aRow τ) = Z (aRow τ) 1 := (hXY (aRow τ) ⟨le_rfl, haRow_lt1.le⟩).2
    rw [h3]
    have h4 : -|Z (aRow τ) 1 - profileX (aRow τ)| ≤ Z (aRow τ) 1 - profileX (aRow τ) := neg_abs_le _
    have h5 : profileX 1 < profileX (aRow τ) - 1 / 128 := by
      have h6 : (8:ℝ) / 9 ≤ profileX (3 / 8) := by
        have h : (0:ℝ) < 1 + (3 / 8) ^ 2 := by norm_num
        rw [profileX, le_div_iff₀ (Real.sqrt_pos.mpr h)]
        have hsq := Real.sq_sqrt (le_of_lt h)
        nlinarith [hsq, Real.sqrt_nonneg (1 + (3/8)^2)]
      have h7 : profileX (3 / 8) ≤ profileX (aRow τ) :=
        profileX_le_profileX' haRow0.le haRow_le38
      have h8 : profileX 1 ≤ 3 / 4 := by
        rw [profileX, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 1 + 1^2))]
        have h4' : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 3/2)]
          norm_num
        calc 1 = (3/4) * (4/3) := by norm_num
          _ ≤ (3/4) * Real.sqrt 2 := by
                have : (4:ℝ)/3 ≤ Real.sqrt 2 := by
                  rw [Real.le_sqrt (by norm_num) (by norm_num)]
                  norm_num
                linarith
          _ = (3/4) * Real.sqrt (1 + 1^2) := by norm_num
      linarith
    linarith
  -- the `C^{n+2}` device
  obtain ⟨fhat, hfhat_sm, hroot, hfb, hfbC⟩ :=
    envelope_device n hn hτ0 hτsmall hh hh_supp hXsm hYsm hc hc1 hXanti hYanti hXder hYder
      hX1 hY1 hXc' hYc' hXbig hYbig
  -- the device's moment identities on the row interval
  have hcs : c < (c + 1) / 2 := by linarith
  have hcs1 : (c + 1) / 2 < 1 := by linarith
  have hId := device_moment_identities (ε := ε) (c := c) (c' := (c + 1) / 2) (Z := Z)
    n hn hτ0 hτsmall hh hh_supp hXsm hYsm hXanti hYanti hX1 hY1
    hfhat_sm hroot hfb hfbC (fun s hs => hZfix s ⟨le_trans haRow_ge hs.1, hs.2⟩) (fun s hs => (hXY s hs).1) (fun s hs => (hXY s hs).2)
    (fun s hs => (hderXY s hs).1) (fun s hs => (hderXY s hs).2)
    (fun s hs => hZneg2 s ⟨le_trans haRow_ge hs.1, hs.2⟩)
    (fun s hs => hZneg3 s ⟨le_trans haRow_ge hs.1, hs.2⟩) hc hc1 hZb hcs hcs1
  have hsm : ∀ s : ℝ, (ε • h) s = ε * h s := fun s => rfl
  -- ----------------------------------------------------------------------
  -- Step 3: on the `h = 0` region the solution returns to the semicircle
  -- ----------------------------------------------------------------------
  set ε₃ : ℝ := min (η / 2) (min (τ / 2) ((1 - 2 * τ - aRow τ) / 4)) with hε₃def
  have hε₃0 : 0 < ε₃ := by
    rw [hε₃def]
    exact lt_min (by linarith) (lt_min (by linarith) (by unfold aRow; linarith))
  have hε₃_η : ε₃ ≤ η / 2 := by rw [hε₃def]; exact min_le_left _ _
  have hε₃_τ : ε₃ ≤ τ / 2 := by
    rw [hε₃def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₃_row : ε₃ ≤ (1 - 2 * τ - aRow τ) / 4 := by
    rw [hε₃def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set s₀ : ℝ := aRow τ + 2 * ε₃ with hs₀def
  have hs₀_gt : aRow τ < s₀ := by rw [hs₀def]; linarith
  have hs₀_lt : s₀ < 1 - 2 * τ := by
    rw [hs₀def]
    have h := hε₃_row
    linarith
  have hεh0 : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃), (ε • h) s = 0 := by
    intro s hs
    have hs_le : s ≤ 1 - 2 * τ + ε₃ := hs.2
    have hs_ge : s₀ - ε₃ ≤ s := hs.1
    have hz : h s = 0 := by
      rcases le_or_gt s (1 - 2 * τ) with h1 | h1
      · exact h_le s h1
      · rcases lt_or_ge s (1 - 2 * τ + η) with h2 | h2
        · exact hη s h1.le h2
        · exact h_ge s (by linarith [h2, hε₃_τ])
    rw [hsm, hz, mul_zero]
  have hXpos : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃), 0 < X s := by
    intro s hs
    have h1 : aRow τ ≤ s := by rw [hs₀def] at hs; linarith [hs.1, hε₃0]
    have h2 : s ≤ 1 := by linarith [hs.2, hε₃_τ, hτ0]
    have hsI : s ∈ Set.Icc (aRow τ) 1 := ⟨h1, h2⟩
    have h3 : X 1 ≤ X s := (hXanti.le_iff_ge ⟨haRow_lt1.le, le_rfl⟩ hsI).mpr h2
    rw [hX1] at h3
    exact lt_of_lt_of_le (profileX_pos 1 (by norm_num)) h3
  have hYpos : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃), 0 < Y s := by
    intro s hs
    have h1 : aRow τ ≤ s := by rw [hs₀def] at hs; linarith [hs.1, hε₃0]
    have h2 : s ≤ 1 := by linarith [hs.2, hε₃_τ, hτ0]
    have hsI : s ∈ Set.Icc (aRow τ) 1 := ⟨h1, h2⟩
    have h3 : Y 1 ≤ Y s := (hYanti.le_iff_ge ⟨haRow_lt1.le, le_rfl⟩ hsI).mpr h2
    rw [hY1] at h3
    exact lt_of_lt_of_le (profileX_pos 1 (by norm_num)) h3
  have hroot' : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃),
      fhat (Y s) ^ 2 = (s * Y s + (ε • h) s) ^ 2 ∧
      fhat (-(X s)) ^ 2 = (s * (-(X s)) + (ε • h) s) ^ 2 := by
    intro s hs
    have h1 : aRow τ ≤ s := by rw [hs₀def] at hs; linarith [hs.1, hε₃0]
    have h2 : s ≤ 1 := by linarith [hs.2, hε₃_τ, hτ0]
    obtain ⟨hr1, hr2⟩ := hroot s ⟨h1, h2⟩
    exact ⟨by rw [hsm, hr1], by rw [hsm, hr2]⟩
  have hF' : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃),
      (∫ t in (-X s)..(Y s), (fhat t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n) := by
    intro s hs
    have h1 : aRow τ ≤ s := by rw [hs₀def] at hs; linarith [hs.1, hε₃0]
    have h2 : s ≤ 1 := by linarith [hs.2, hε₃_τ, hτ0]
    have h := hId.1 s ⟨h1, h2⟩
    simpa only [RyaboginVolterra.momentF, RyaboginVolterra.momentIntegrand,
      RyaboginVolterra.line, RyaboginVolterra.momentRHS] using h
  have hH' : ∀ s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃),
      (∫ t in (-X s)..(Y s), (fhat t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) *
        (t + deriv (ε • h) s)) = 0 := by
    intro s hs
    have h1 : aRow τ ≤ s := by rw [hs₀def] at hs; linarith [hs.1, hε₃0]
    have h2 : s ≤ 1 := by linarith [hs.2, hε₃_τ, hτ0]
    have h := hId.2 s ⟨h1, h2⟩
    simpa only [RyaboginVolterra.momentH, RyaboginVolterra.centroidIntegrand,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope] using h
  have hs₀ε : s₀ - ε₃ = aRow τ + ε₃ := by rw [hs₀def]; ring
  have hstep3 := returns_to_semicircle_cont (x := X) (y := Y) (f := fhat) (h := ε • h)
    n hn (hε := hε₃0)
    (hA := by rw [hs₀def]; linarith) (hAB := by linarith)
    hXsm hYsm hfhat_sm.continuous (hh.const_smul ε) hεh0 hXpos hYpos hroot' hF' hH'
  have hXYsemi : ∀ s ∈ Set.Icc s₀ (1 - 2 * τ), X s = profileX s ∧ Y s = profileX s := hstep3
  -- ----------------------------------------------------------------------
  -- the binomial relations at `s₀`, for the device
  -- ----------------------------------------------------------------------
  have hsU : s₀ ∈ Set.Ioo (s₀ - ε₃) (s₀ + ε₃) := ⟨by linarith, by linarith⟩
  have hUmem2 : ∀ s ∈ Set.Ioo (s₀ - ε₃) (s₀ + ε₃),
      s ∈ Set.Icc (s₀ - ε₃) (1 - 2 * τ + ε₃) := by
    intro s hs
    rw [Set.mem_Ioo] at hs
    exact ⟨hs.1.le, by linarith [hs.2, hs₀_lt]⟩
  have hUmem : ∀ s ∈ Set.Ioo (s₀ - ε₃) (s₀ + ε₃), s ∈ Set.Icc (aRow τ) 1 := by
    intro s hs
    rw [Set.mem_Ioo] at hs
    refine ⟨?_, ?_⟩
    · rw [hs₀def] at hs
      linarith [hs.1, hε₃0]
    · linarith [hs.2, hs₀_lt]
  have hrel' : (∀ k : ℕ, k ≤ n → momE n fhat (ε • h) X Y k s₀ = refE n k s₀) ∧
      (∀ k : ℕ, k ≤ n - 1 → momO n fhat (ε • h) X Y k s₀ = 0) :=
    moment_relations_at (n := n) (U := Set.Ioo (s₀ - ε₃) (s₀ + ε₃)) isOpen_Ioo
      (fun s hs => by
        rw [Set.mem_Ioo] at hs
        have h1 : 0 < s₀ - ε₃ := by rw [hs₀def]; linarith
        linarith)
      hfhat_sm.continuous (hh.const_smul ε) hXsm hYsm
      (fun s hs => hεh0 s ⟨by rw [Set.mem_Ioo] at hs; linarith [hs.1], by rw [Set.mem_Ioo] at hs; linarith [hs.2]⟩)
      (fun s hs => by
        have hev : (ε • h) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
          filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
          exact hεh0 u ⟨by linarith [hu.1], by linarith [hu.2]⟩
        exact deriv_h_eq_zero_of_nhds_v2 hev)
      (fun s hs => hroot' s (hUmem2 s hs))
      (fun s hs => by
        have hm := hId.1 s (hUmem s hs)
        simp only [RyaboginVolterra.momentF, RyaboginVolterra.momentIntegrand,
          RyaboginVolterra.line, RyaboginVolterra.momentRHS] at hm
        simpa only [momE, refE, Pi.smul_apply, smul_eq_mul,
          Nat.sub_zero, Nat.mul_zero, pow_zero, mul_one] using hm)
      (fun s hs => by
        have hm := hId.2 s (hUmem s hs)
        simp only [RyaboginVolterra.momentH, RyaboginVolterra.centroidIntegrand,
          RyaboginVolterra.line, RyaboginVolterra.lineSlope] at hm
        have hdh_s : deriv (ε • h) s = 0 := by
          have hev : (ε • h) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
            filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
            exact hεh0 u ⟨by linarith [hu.1], by linarith [hu.2]⟩
          exact deriv_h_eq_zero_of_nhds_v2 hev
        rw [hdh_s] at hm
        simpa only [momO, Pi.smul_apply, smul_eq_mul, add_zero, pow_one, mul_one,
          Nat.sub_zero, Nat.mul_zero, Nat.zero_add, Pi.zero_apply] using hm)
      hsU
  -- ----------------------------------------------------------------------
  -- the piecewise smooth extensions `Xt`, `Yt` used to define the envelope `f`
  -- ----------------------------------------------------------------------
  have hprof_lt1 : ∀ s : ℝ, 0 < s → profileX s < 1 := by
    intro s hs
    rw [profileX, div_lt_one (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s]))]
    rw [Real.lt_sqrt (by positivity)]
    nlinarith [sq_nonneg s]
  have hXmono : ∀ a b : ℝ, aRow τ ≤ a → a < b → X b < X a := by
    intro a b ha hab
    rcases le_or_gt b 1 with hb | hb
    · exact hXanti ⟨ha, le_trans hab.le hb⟩ ⟨le_trans ha hab.le, hb⟩ hab
    · have hbp : X b = profileX b := hXp b (by linarith [hc1, hb])
      rcases le_or_gt a 1 with ha1 | ha1
      · have hap : profileX 1 ≤ X a := by
          rw [← hX1]
          exact (hXanti.le_iff_ge ⟨haRow_lt1.le, le_rfl⟩ ⟨ha, ha1⟩).mpr ha1
        rw [hbp]
        exact lt_of_lt_of_le (profileX_lt_profileX (by norm_num) hb) hap
      · have hap : X a = profileX a := hXp a (by linarith [hc1, ha1])
        rw [hbp, hap]
        exact profileX_lt_profileX (by linarith) hab
  have hYmono : ∀ a b : ℝ, aRow τ ≤ a → a < b → Y b < Y a := by
    intro a b ha hab
    rcases le_or_gt b 1 with hb | hb
    · exact hYanti ⟨ha, le_trans hab.le hb⟩ ⟨le_trans ha hab.le, hb⟩ hab
    · have hbp : Y b = profileX b := hYp b (by linarith [hc1, hb])
      rcases le_or_gt a 1 with ha1 | ha1
      · have hap : profileX 1 ≤ Y a := by
          rw [← hY1]
          exact (hYanti.le_iff_ge ⟨haRow_lt1.le, le_rfl⟩ ⟨ha, ha1⟩).mpr ha1
        rw [hbp]
        exact lt_of_lt_of_le (profileX_lt_profileX (by norm_num) hb) hap
      · have hap : Y a = profileX a := hYp a (by linarith [hc1, ha1])
        rw [hbp, hap]
        exact profileX_lt_profileX (by linarith) hab
  set Xt : ℝ → ℝ := fun s => if s ≤ s₀ then profileX s else X s with hXtdef
  set Yt : ℝ → ℝ := fun s => if s ≤ s₀ then profileX s else Y s with hYtdef
  have hXt_low : ∀ s : ℝ, s ≤ s₀ → Xt s = profileX s := by
    intro s hs; simp only [hXtdef]; exact if_pos hs
  have hYt_low : ∀ s : ℝ, s ≤ s₀ → Yt s = profileX s := by
    intro s hs; simp only [hYtdef]; exact if_pos hs
  have hXt_high : ∀ s : ℝ, s₀ ≤ s → Xt s = X s := by
    intro s hs
    simp only [hXtdef]
    rcases eq_or_lt_of_le hs with h | h
    · rw [h.symm, if_pos le_rfl]
      exact ((hXYsemi s₀ ⟨le_rfl, hs₀_lt.le⟩).1).symm
    · exact if_neg (not_le.mpr h)
  have hYt_high : ∀ s : ℝ, s₀ ≤ s → Yt s = Y s := by
    intro s hs
    simp only [hYtdef]
    rcases eq_or_lt_of_le hs with h | h
    · rw [h.symm, if_pos le_rfl]
      exact ((hXYsemi s₀ ⟨le_rfl, hs₀_lt.le⟩).2).symm
    · exact if_neg (not_le.mpr h)
  have hXt_sm : ContDiff ℝ ∞ Xt := by
    rw [contDiff_iff_contDiffAt]
    intro s
    rcases lt_trichotomy s s₀ with hlt | heq | hgt
    · refine (contDiff_profileX.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hlt] with u hu
      exact hXt_low u hu.le
    · subst heq
      refine (contDiff_profileX.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show s₀ - 1 < s₀ by linarith)
        (show s₀ < s₀ + (1 - 2 * τ - s₀) by linarith)] with u hu
      by_cases hu' : u ≤ s₀
      · exact hXt_low u hu'
      · rw [hXt_high u (le_of_lt (not_le.mp hu'))]
        exact (hXYsemi u ⟨le_of_lt (not_le.mp hu'), by linarith [hu.2]⟩).1
    · refine hXsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hgt] with u hu
      exact hXt_high u hu.le
  have hYt_sm : ContDiff ℝ ∞ Yt := by
    rw [contDiff_iff_contDiffAt]
    intro s
    rcases lt_trichotomy s s₀ with hlt | heq | hgt
    · refine (contDiff_profileX.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hlt] with u hu
      exact hYt_low u hu.le
    · subst heq
      refine (contDiff_profileX.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (show s₀ - 1 < s₀ by linarith)
        (show s₀ < s₀ + (1 - 2 * τ - s₀) by linarith)] with u hu
      by_cases hu' : u ≤ s₀
      · exact hYt_low u hu'
      · rw [hYt_high u (le_of_lt (not_le.mp hu'))]
        exact (hXYsemi u ⟨le_of_lt (not_le.mp hu'), by linarith [hu.2]⟩).2
    · refine hYsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hgt] with u hu
      exact hYt_high u hu.le
  have hs₀pos : (0:ℝ) < s₀ := lt_trans haRow0 hs₀_gt
  have hcpos : (0:ℝ) < c := by rw [hcdef]; linarith
  have hXs₀ : X s₀ = profileX s₀ := (hXYsemi s₀ ⟨le_rfl, hs₀_lt.le⟩).1
  have hYs₀ : Y s₀ = profileX s₀ := (hXYsemi s₀ ⟨le_rfl, hs₀_lt.le⟩).2
  have hXc : X c = profileX c := hXp c le_rfl
  have hYc : Y c = profileX c := hYp c le_rfl
  have hXt0 : Xt 0 = 1 := by
    rw [hXt_low 0 (by linarith), profileX]; simp
  have hYt0 : Yt 0 = 1 := by
    rw [hYt_low 0 (by linarith), profileX]; simp
  have hXt_mem : ∀ s : ℝ, 0 < s → 0 < Xt s ∧ Xt s < 1 := by
    intro s hs
    rcases le_or_gt s s₀ with h1 | h1
    · rw [hXt_low s h1]
      exact ⟨profileX_pos' s, hprof_lt1 s hs⟩
    · rw [hXt_high s h1.le]
      have hsge : aRow τ ≤ s := le_of_lt (lt_trans hs₀_gt h1)
      constructor
      · rcases le_or_gt s c with h2 | h2
        · have hmem1 : s ∈ Set.Icc (aRow τ) 1 := ⟨hsge, by linarith [h2, hc1]⟩
          have hmem2 : c ∈ Set.Icc (aRow τ) 1 := ⟨le_trans hsge h2, hc1.le⟩
          have h3 : X c ≤ X s := hXanti.antitoneOn hmem1 hmem2 h2
          rw [hXc] at h3
          exact lt_of_lt_of_le (profileX_pos' c) h3
        · rw [hXp s h2.le]
          exact profileX_pos' s
      · have h3 : X s < X s₀ := hXmono s₀ s hs₀_gt.le h1
        rw [hXs₀] at h3
        exact lt_trans h3 (hprof_lt1 s₀ hs₀pos)
  have hYt_mem : ∀ s : ℝ, 0 < s → 0 < Yt s ∧ Yt s < 1 := by
    intro s hs
    rcases le_or_gt s s₀ with h1 | h1
    · rw [hYt_low s h1]
      exact ⟨profileX_pos' s, hprof_lt1 s hs⟩
    · rw [hYt_high s h1.le]
      have hsge : aRow τ ≤ s := le_of_lt (lt_trans hs₀_gt h1)
      constructor
      · rcases le_or_gt s c with h2 | h2
        · have hmem1 : s ∈ Set.Icc (aRow τ) 1 := ⟨hsge, by linarith [h2, hc1]⟩
          have hmem2 : c ∈ Set.Icc (aRow τ) 1 := ⟨le_trans hsge h2, hc1.le⟩
          have h3 : Y c ≤ Y s := hYanti.antitoneOn hmem1 hmem2 h2
          rw [hYc] at h3
          exact lt_of_lt_of_le (profileX_pos' c) h3
        · rw [hYp s h2.le]
          exact profileX_pos' s
      · have h3 : Y s < Y s₀ := hYmono s₀ s hs₀_gt.le h1
        rw [hYs₀] at h3
        exact lt_trans h3 (hprof_lt1 s₀ hs₀pos)
  have hXt_anti : StrictAntiOn Xt (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : 0 < a := ha
    rcases le_or_gt b s₀ with hbs | hbs
    · rw [hXt_low b hbs, hXt_low a (le_trans hab.le hbs)]
      exact profileX_lt_profileX ha0 hab
    · rcases le_or_gt s₀ a with has | has
      · rw [hXt_high b hbs.le, hXt_high a has]
        exact hXmono a b (le_trans hs₀_gt.le has) hab
      · rw [hXt_low a has.le]
        rcases le_or_gt b 1 with hb1 | hb1
        · have h1 : X b < X s₀ := hXmono s₀ b hs₀_gt.le hbs
          rw [hXs₀] at h1
          have h2 : profileX s₀ < profileX a := profileX_lt_profileX (a := a) (b := s₀) ha0 has
          rw [hXt_high b hbs.le]
          linarith
        · rw [hXt_high b hbs.le, hXp b (by linarith [hc1, hb1])]
          have h2 : profileX s₀ < profileX a := profileX_lt_profileX (a := a) (b := s₀) ha0 has
          have h5 : X 1 < X s₀ := hXmono s₀ 1 hs₀_gt.le (by linarith [hs₀_lt])
          rw [hXs₀, hX1] at h5
          have h3 : profileX b < profileX 1 := profileX_lt_profileX (a := (1:ℝ)) (b := b) (by norm_num) hb1
          linarith
  have hYt_anti : StrictAntiOn Yt (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : 0 < a := ha
    rcases le_or_gt b s₀ with hbs | hbs
    · rw [hYt_low b hbs, hYt_low a (le_trans hab.le hbs)]
      exact profileX_lt_profileX ha0 hab
    · rcases le_or_gt s₀ a with has | has
      · rw [hYt_high b hbs.le, hYt_high a has]
        exact hYmono a b (le_trans hs₀_gt.le has) hab
      · rw [hYt_low a has.le]
        rcases le_or_gt b 1 with hb1 | hb1
        · have h1 : Y b < Y s₀ := hYmono s₀ b hs₀_gt.le hbs
          rw [hYs₀] at h1
          have h2 : profileX s₀ < profileX a := profileX_lt_profileX (a := a) (b := s₀) ha0 has
          rw [hYt_high b hbs.le]
          linarith
        · rw [hYt_high b hbs.le, hYp b (by linarith [hc1, hb1])]
          have h2 : profileX s₀ < profileX a := profileX_lt_profileX (a := a) (b := s₀) ha0 has
          have h5 : Y 1 < Y s₀ := hYmono s₀ 1 hs₀_gt.le (by linarith [hs₀_lt])
          rw [hYs₀, hY1] at h5
          have h3 : profileX b < profileX 1 := profileX_lt_profileX (a := (1:ℝ)) (b := b) (by norm_num) hb1
          linarith
  have hXt_pX_nhds : ∀ s : ℝ, s < 1 - 2 * τ → Xt =ᶠ[𝓝 s] profileX := by
    intro s hs
    filter_upwards [Iio_mem_nhds hs] with u hu
    have hu' : u < 1 - 2 * τ := Set.mem_Iio.mp hu
    rcases le_or_gt u s₀ with h1 | h1
    · exact hXt_low u h1
    · rw [hXt_high u h1.le]
      exact (hXYsemi u ⟨h1.le, hu'.le⟩).1
  have hYt_pX_nhds : ∀ s : ℝ, s < 1 - 2 * τ → Yt =ᶠ[𝓝 s] profileX := by
    intro s hs
    filter_upwards [Iio_mem_nhds hs] with u hu
    have hu' : u < 1 - 2 * τ := Set.mem_Iio.mp hu
    rcases le_or_gt u s₀ with h1 | h1
    · exact hYt_low u h1
    · rw [hYt_high u h1.le]
      exact (hXYsemi u ⟨h1.le, hu'.le⟩).2
  have hXt_X_nhds : ∀ s : ℝ, s₀ < s → Xt =ᶠ[𝓝 s] X := by
    intro s hs
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact hXt_high u hu.le
  have hYt_Y_nhds : ∀ s : ℝ, s₀ < s → Yt =ᶠ[𝓝 s] Y := by
    intro s hs
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact hYt_high u hu.le
  have hXt_der : ∀ s : ℝ, 0 < s → deriv Xt s < 0 := by
    intro s hs
    rcases lt_trichotomy s s₀ with hlt | heq | hgt
    · rw [(hXt_pX_nhds s (by linarith [hlt, hs₀_lt])).deriv_eq]
      exact deriv_profileX_neg hs
    · subst heq
      rw [(hXt_pX_nhds s₀ hs₀_lt).deriv_eq]
      exact deriv_profileX_neg hs
    · rw [(hXt_X_nhds s hgt).deriv_eq]
      rcases lt_or_ge s 1 with h1 | h1
      · rw [(hderb s ⟨lt_trans ha₁lt (lt_trans hs₀_gt hgt), h1⟩).1]
        exact hZneg2 s ⟨le_trans haRow_ge (le_of_lt (lt_trans hs₀_gt hgt)), h1.le⟩
      · rw [(by
          filter_upwards [Ioi_mem_nhds (show c < s by linarith [hc1, h1])] with u hu
          exact hXp u hu.le : X =ᶠ[𝓝 s] profileX).deriv_eq]
        exact deriv_profileX_neg hs
  have hYt_der : ∀ s : ℝ, 0 < s → deriv Yt s < 0 := by
    intro s hs
    rcases lt_trichotomy s s₀ with hlt | heq | hgt
    · rw [(hYt_pX_nhds s (by linarith [hlt, hs₀_lt])).deriv_eq]
      exact deriv_profileX_neg hs
    · subst heq
      rw [(hYt_pX_nhds s₀ hs₀_lt).deriv_eq]
      exact deriv_profileX_neg hs
    · rw [(hYt_Y_nhds s hgt).deriv_eq]
      rcases lt_or_ge s 1 with h1 | h1
      · rw [(hderb s ⟨lt_trans ha₁lt (lt_trans hs₀_gt hgt), h1⟩).2]
        exact hZneg3 s ⟨le_trans haRow_ge (le_of_lt (lt_trans hs₀_gt hgt)), h1.le⟩
      · rw [(by
          filter_upwards [Ioi_mem_nhds (show c < s by linarith [hc1, h1])] with u hu
          exact hYp u hu.le : Y =ᶠ[𝓝 s] profileX).deriv_eq]
        exact deriv_profileX_neg hs
  have hs₀c : s₀ < c := by linarith [hs₀_lt, hcdef, hτ0]
  have hXt_surj : ∀ t : ℝ, 0 < t → t < 1 → ∃ s : ℝ, 0 < s ∧ Xt s = t := by
    intro t ht0 ht1
    obtain ⟨N, hNc, hN⟩ : ∃ N : ℝ, c ≤ N ∧ profileX N < t := by
      refine ⟨c + 1 / t + 1, by have := one_div_pos.mpr ht0; linarith, ?_⟩
      have hNpos : 0 < c + 1 / t + 1 := by positivity
      rw [profileX, div_lt_iff₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c + 1/t + 1)]))]
      have h2 : 1 / t < Real.sqrt (1 + (c + 1 / t + 1) ^ 2) := by
        rw [Real.lt_sqrt (by positivity)]
        have h3 : 1 / t < c + 1 / t + 1 := by linarith
        have h4 : (0:ℝ) < 1 / t := one_div_pos.mpr ht0
        nlinarith [h3, h4, sq_nonneg (c + 1 / t + 1 - 1 / t)]
      have h5 : t * (1 / t) < t * Real.sqrt (1 + (c + 1 / t + 1) ^ 2) :=
        mul_lt_mul_of_pos_left h2 ht0
      rw [mul_one_div_cancel (ne_of_gt ht0)] at h5
      linarith
    have hNs : s₀ ≤ N := le_trans hs₀c.le hNc
    have hNmem : Xt N = profileX N := by
      rw [hXt_high N hNs, hXp N hNc]
    have hy : t ∈ Set.Icc (Xt N) (Xt 0) := ⟨by rw [hNmem]; exact hN.le, by rw [hXt0]; linarith [ht1]⟩
    obtain ⟨s, hs, hst⟩ := (intermediate_value_Icc' (show (0:ℝ) ≤ N by linarith [hcpos, hNc])
      hXt_sm.continuous.continuousOn hy)
    refine ⟨s, ?_, hst⟩
    rcases lt_or_eq_of_le hs.1 with h | h
    · exact h
    · exfalso
      rw [← h, hXt0] at hst
      linarith [ht1]
  have hYt_surj : ∀ t : ℝ, 0 < t → t < 1 → ∃ s : ℝ, 0 < s ∧ Yt s = t := by
    intro t ht0 ht1
    obtain ⟨N, hNc, hN⟩ : ∃ N : ℝ, c ≤ N ∧ profileX N < t := by
      refine ⟨c + 1 / t + 1, by have := one_div_pos.mpr ht0; linarith, ?_⟩
      rw [profileX, div_lt_iff₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c + 1/t + 1)]))]
      have h2 : 1 / t < Real.sqrt (1 + (c + 1 / t + 1) ^ 2) := by
        rw [Real.lt_sqrt (by positivity)]
        have h3 : 1 / t < c + 1 / t + 1 := by linarith
        have h4 : (0:ℝ) < 1 / t := one_div_pos.mpr ht0
        nlinarith [h3, h4, sq_nonneg (c + 1 / t + 1 - 1 / t)]
      have h5 : t * (1 / t) < t * Real.sqrt (1 + (c + 1 / t + 1) ^ 2) :=
        mul_lt_mul_of_pos_left h2 ht0
      rw [mul_one_div_cancel (ne_of_gt ht0)] at h5
      linarith
    have hNs : s₀ ≤ N := le_trans hs₀c.le hNc
    have hNmem : Yt N = profileX N := by
      rw [hYt_high N hNs, hYp N hNc]
    have hy : t ∈ Set.Icc (Yt N) (Yt 0) := ⟨by rw [hNmem]; exact hN.le, by rw [hYt0]; linarith [ht1]⟩
    obtain ⟨s, hs, hst⟩ := (intermediate_value_Icc' (show (0:ℝ) ≤ N by linarith [hcpos, hNc])
      hYt_sm.continuous.continuousOn hy)
    refine ⟨s, ?_, hst⟩
    rcases lt_or_eq_of_le hs.1 with h | h
    · exact h
    · exfalso
      rw [← h, hYt0] at hst
      linarith [ht1]
  have hclarge : ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ s : ℝ, c₀ ≤ s → Yt s = 1 / Real.sqrt (1 + s ^ 2) ∧ h s = 0) ∧
      (∀ s : ℝ, c₀ ≤ s → Xt s = 1 / Real.sqrt (1 + s ^ 2)) := by
    refine ⟨c, hcpos, ?_, ?_⟩
    · intro s hs
      have h1 : s₀ ≤ s := le_trans hs₀c.le hs
      refine ⟨?_, h_ge s (by linarith [hs, hcdef, hτ0])⟩
      rw [hYt_high s h1, hYp s hs]
      rfl
    · intro s hs
      have h1 : s₀ ≤ s := le_trans hs₀c.le hs
      rw [hXt_high s h1, hXp s hs]
      rfl
  obtain ⟨f, hf_sm, hf_supp, hf_one, hf_negone, hf_root_pos, hf_root_neg⟩ :=
    Commons.Analysis.Calculus.envelope_smooth_of_strictAntiOn (ε := ε) (h := h) (x := Xt) (y := Yt)
      hXt_sm hYt_sm hh hXt0 hYt0 hXt_mem hYt_mem hXt_anti hYt_anti hXt_der hYt_der
      hXt_surj hYt_surj hclarge
  -- the target's squared root conditions
  have hroot_t : ∀ s : ℝ, 0 < s →
      0 < Xt s ∧ 0 < Yt s ∧
      (f (Yt s)) ^ 2 = (s * Yt s + (ε • h) s) ^ 2 ∧
      (f (-(Xt s))) ^ 2 = (s * (-(Xt s)) + (ε • h) s) ^ 2 := by
    intro s hs
    have h1 := hf_root_pos s hs
    have h2 := hf_root_neg s hs
    have hsm : (ε • h) s = ε * h s := by simp only [Pi.smul_apply, smul_eq_mul]
    refine ⟨(hXt_mem s hs).1, (hYt_mem s hs).1, ?_, ?_⟩
    · rw [h1, hsm]
    · rw [h2, hsm]; ring
  -- `profileX` is small at large arguments
  have hprof_small : ∀ t : ℝ, 0 < t → ∃ N : ℝ, c ≤ N ∧ profileX N < t := by
    intro t ht0
    refine ⟨c + 1 / t + 1, by have := one_div_pos.mpr ht0; linarith, ?_⟩
    rw [profileX, div_lt_iff₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (c + 1/t + 1)]))]
    have h2 : 1 / t < Real.sqrt (1 + (c + 1 / t + 1) ^ 2) := by
      rw [Real.lt_sqrt (by positivity)]
      have h3 : 1 / t < c + 1 / t + 1 := by linarith
      have h4 : (0:ℝ) < 1 / t := one_div_pos.mpr ht0
      nlinarith [h3, h4, sq_nonneg (c + 1 / t + 1 - 1 / t)]
    have h5 : t * (1 / t) < t * Real.sqrt (1 + (c + 1 / t + 1) ^ 2) :=
      mul_lt_mul_of_pos_left h2 ht0
    rw [mul_one_div_cancel (ne_of_gt ht0)] at h5
    linarith
  -- on the cap the profiles are surjective onto `(0, profileX s₀]`
  have hYsurj' : ∀ t : ℝ, 0 < t → t ≤ profileX s₀ → ∃ σ : ℝ, s₀ ≤ σ ∧ Y σ = t := by
    intro t ht0 hts
    obtain ⟨N, hNc, hN⟩ := hprof_small t ht0
    have hNs : s₀ ≤ N := le_trans hs₀c.le hNc
    have hy : t ∈ Set.Icc (Y N) (Y s₀) :=
      ⟨by rw [hYp N hNc]; exact hN.le, by rw [hYs₀]; exact hts⟩
    obtain ⟨σ, hσ, hσt⟩ := intermediate_value_Icc' hNs hYsm.continuous.continuousOn hy
    exact ⟨σ, hσ.1, hσt⟩
  have hXsurj' : ∀ t : ℝ, 0 < t → t ≤ profileX s₀ → ∃ σ : ℝ, s₀ ≤ σ ∧ X σ = t := by
    intro t ht0 hts
    obtain ⟨N, hNc, hN⟩ := hprof_small t ht0
    have hNs : s₀ ≤ N := le_trans hs₀c.le hNc
    have hy : t ∈ Set.Icc (X N) (X s₀) :=
      ⟨by rw [hXp N hNc]; exact hN.le, by rw [hXs₀]; exact hts⟩
    obtain ⟨σ, hσ, hσt⟩ := intermediate_value_Icc' hNs hXsm.continuous.continuousOn hy
    exact ⟨σ, hσ.1, hσt⟩
  -- the final `f` and the device `f̂` have the same square on the cap
  have hsq_pos : ∀ t : ℝ, 0 < t → t ≤ profileX s₀ → f t ^ 2 = fhat t ^ 2 := by
    intro t ht0 hts
    obtain ⟨σ, hσ, hσt⟩ := hYsurj' t ht0 hts
    have hσpos : 0 < σ := lt_of_lt_of_le hs₀pos hσ
    have hYtσ : Yt σ = Y σ := hYt_high σ hσ
    have hf_val : f t = σ * t + ε * h σ := by
      have h := hf_root_pos σ hσpos
      rw [hYtσ, hσt] at h
      exact h
    have hfa : fhat t ^ 2 = (σ * t + ε * h σ) ^ 2 := by
      have h' : fhat (Y σ) ^ 2 = (σ * Y σ + ε * h σ) ^ 2 := by
        rcases le_or_gt σ 1 with h1 | h1
        · have hm := (hroot σ ⟨le_trans hs₀_gt.le hσ, h1⟩).1
          simpa only [Pi.smul_apply, smul_eq_mul] using hm
        · have hYσ : Y σ = profileX σ := hYp σ (by linarith [hc1, h1])
          have hhσ : h σ = 0 := h_ge σ (by linarith)
          have hle1 : profileX σ ≤ profileX 1 :=
            profileX_le_profileX' (by norm_num) h1.le
          have hm := hfb (profileX σ) ⟨by linarith [profileX_pos' σ], hle1⟩
          have hsq := one_sub_profileX_sq σ
          rw [hYσ, hhσ, mul_zero, add_zero, hm, hsq]
      rw [hσt] at h'
      exact h'
    rw [hf_val, hfa]
  have hsq_neg : ∀ t : ℝ, t < 0 → -profileX s₀ ≤ t → f t ^ 2 = fhat t ^ 2 := by
    intro t ht htl
    have hu0 : 0 < -t := neg_pos.mpr ht
    have hus : -t ≤ profileX s₀ := by linarith
    obtain ⟨σ, hσ, hσt⟩ := hXsurj' (-t) hu0 hus
    have hσpos : 0 < σ := lt_of_lt_of_le hs₀pos hσ
    have hXtσ : Xt σ = X σ := hXt_high σ hσ
    have hf_val : f t = -(σ * t + ε * h σ) := by
      have h := hf_root_neg σ hσpos
      rw [hXtσ, hσt] at h
      simp only [neg_neg] at h
      exact h
    have hfa : fhat t ^ 2 = (σ * t + ε * h σ) ^ 2 := by
      have h' : fhat (-(X σ)) ^ 2 = (σ * (-(X σ)) + ε * h σ) ^ 2 := by
        rcases le_or_gt σ 1 with h1 | h1
        · have hm := (hroot σ ⟨le_trans hs₀_gt.le hσ, h1⟩).2
          simpa only [Pi.smul_apply, smul_eq_mul] using hm
        · have hXσ : X σ = profileX σ := hXp σ (by linarith [hc1, h1])
          have hhσ : h σ = 0 := h_ge σ (by linarith)
          have hle1 : profileX σ ≤ profileX 1 :=
            profileX_le_profileX' (by norm_num) h1.le
          have hm := hfb (-(profileX σ)) ⟨by linarith [profileX_pos' σ], by linarith [hle1]⟩
          have hsq := one_sub_profileX_sq σ
          rw [hXσ, hhσ, mul_zero, add_zero, hm,
            show (-(profileX σ)) ^ 2 = profileX σ ^ 2 by ring,
            show (σ * (-(profileX σ))) ^ 2 = (σ * profileX σ) ^ 2 by ring]
          exact hsq
      rw [hσt] at h'
      simpa only [neg_neg] using h'
    rw [hf_val, hfa]
    ring
  -- the profiles stay below the anchor level on `[s₀,1]`
  have hXs_le : ∀ s ∈ Set.Icc s₀ 1, X s ≤ profileX s₀ := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hXs₀]
    · rw [← hXs₀]; exact (hXmono s₀ s hs₀_gt.le h).le
  have hYs_le : ∀ s ∈ Set.Icc s₀ 1, Y s ≤ profileX s₀ := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hYs₀]
    · rw [← hYs₀]; exact (hYmono s₀ s hs₀_gt.le h).le
  -- `f` and `f̂` have the same square on the whole anchor cap, off the origin
  have hsq_all : ∀ t : ℝ, t ≠ 0 → -profileX s₀ ≤ t → t ≤ profileX s₀ → f t ^ 2 = fhat t ^ 2 := by
    intro t ht hlo hhi
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · exact hsq_neg t hneg (by linarith)
    · exact absurd hzero ht
    · exact hsq_pos t hpos (by linarith)
  -- the moment identities on `[s₀,1]` (transported from the device)
  have hM_s : ∀ s ∈ Set.Icc s₀ 1,
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n)
        = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n) := by
    intro s hs
    have h1 : Xt s = X s := hXt_high s hs.1
    have h2 : Yt s = Y s := hYt_high s hs.1
    have hD := hId.1 s ⟨le_trans hs₀_gt.le hs.1, hs.2⟩
    simp only [RyaboginVolterra.momentF, RyaboginVolterra.momentIntegrand,
      RyaboginVolterra.line, RyaboginVolterra.momentRHS] at hD
    rw [h1, h2, ← hD]
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton 0)
    intro t ht
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at ht ⊢
    by_contra hne
    have hmem : t ∈ Set.uIoc (-X s) (Y s) := by
      by_contra hmem
      exact ht fun h => absurd h hmem
    have hspos : 0 < s := lt_of_lt_of_le hs₀pos hs.1
    have hXspos : 0 < X s := by rw [← h1]; exact (hXt_mem s hspos).1
    have hYspos : 0 < Y s := by rw [← h2]; exact (hYt_mem s hspos).1
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have htlo : -profileX s₀ ≤ t := by
      have := hXs_le s hs
      linarith [hmem.1, this]
    have hthi : t ≤ profileX s₀ := le_trans hmem.2 (hYs_le s hs)
    have hval : f t ^ 2 = fhat t ^ 2 := hsq_all t hne htlo hthi
    exact ht fun _ => by rw [hval]
  have hH_s : ∀ s ∈ Set.Icc s₀ 1,
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) *
        (t + deriv (ε • h) s)) = 0 := by
    intro s hs
    have h1 : Xt s = X s := hXt_high s hs.1
    have h2 : Yt s = Y s := hYt_high s hs.1
    have hD := hId.2 s ⟨le_trans hs₀_gt.le hs.1, hs.2⟩
    simp only [RyaboginVolterra.momentH, RyaboginVolterra.centroidIntegrand,
      RyaboginVolterra.line, RyaboginVolterra.lineSlope] at hD
    rw [h1, h2, ← hD]
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton 0)
    intro t ht
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at ht ⊢
    by_contra hne
    have hmem : t ∈ Set.uIoc (-X s) (Y s) := by
      by_contra hmem
      exact ht fun h => absurd h hmem
    have hspos : 0 < s := lt_of_lt_of_le hs₀pos hs.1
    have hXspos : 0 < X s := by rw [← h1]; exact (hXt_mem s hspos).1
    have hYspos : 0 < Y s := by rw [← h2]; exact (hYt_mem s hspos).1
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have htlo : -profileX s₀ ≤ t := by
      have := hXs_le s hs
      linarith [hmem.1, this]
    have hthi : t ≤ profileX s₀ := le_trans hmem.2 (hYs_le s hs)
    have hval : f t ^ 2 = fhat t ^ 2 := hsq_all t hne htlo hthi
    exact ht fun _ => by rw [hval]
  -- the identities for `s ≥ 1` (the unperturbed regime)
  have hM_big : ∀ s : ℝ, 1 ≤ s →
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n)
        = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n) := by
    intro s hs1
    have hspos : 0 < s := lt_of_lt_of_le one_pos hs1
    have hs0 : s₀ ≤ s := by linarith [hs₀_lt, hs1]
    have h1 : Xt s = profileX s := by
      rw [hXt_high s hs0]; exact hXp s (by linarith [hc1, hs1])
    have h2 : Yt s = profileX s := by
      rw [hYt_high s hs0]; exact hYp s (by linarith [hc1, hs1])
    have hsm0 : (ε • h) s = 0 := by
      rw [Pi.smul_apply, smul_eq_mul, h_ge s (by linarith), mul_zero]
    have hps1 : profileX s ≤ profileX 1 := profileX_le_profileX' (by norm_num) hs1
    have hps0 : profileX s ≤ profileX s₀ := profileX_le_profileX' (by linarith [hτ0, hcdef]) hs0
    rw [h1, h2, hsm0]
    simp only [add_zero]
    have hcn : (∫ t in (-profileX s)..(profileX s), ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
        = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n) := by
      simp only [profileX]
    rw [← hcn]
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton 0)
    intro t ht
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at ht ⊢
    by_contra hne
    have hmem : t ∈ Set.uIoc (-profileX s) (profileX s) := by
      by_contra hmem
      exact ht fun h => absurd h hmem
    rw [Set.uIoc_of_le (neg_le_self (profileX_pos' s).le)] at hmem
    have htlo : -profileX s₀ ≤ t := by linarith [hmem.1, hps0]
    have hthi : t ≤ profileX s₀ := by linarith [hmem.2, hps0]
    have ht1 : |t| ≤ profileX 1 := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1, hps1], by linarith [hmem.2, hps1]⟩
    have hval : f t ^ 2 = fhat t ^ 2 := hsq_all t hne htlo hthi
    obtain ⟨ha1, ha2⟩ := abs_le.mp ht1
    exact ht fun _ => by rw [hval, hfb t ⟨by linarith, by linarith⟩]
  have hH_big : ∀ s : ℝ, 1 ≤ s →
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) *
        (t + deriv (ε • h) s)) = 0 := by
    intro s hs1
    have hs0 : s₀ ≤ s := by linarith [hs₀_lt, hs1]
    have h1 : Xt s = profileX s := by
      rw [hXt_high s hs0]; exact hXp s (by linarith [hc1, hs1])
    have h2 : Yt s = profileX s := by
      rw [hYt_high s hs0]; exact hYp s (by linarith [hc1, hs1])
    have hsm0 : (ε • h) s = 0 := by
      rw [Pi.smul_apply, smul_eq_mul, h_ge s (by linarith), mul_zero]
    have hd0 : deriv (ε • h) s = 0 := by
      have hev : (ε • h) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds (show 1 - τ < s by linarith)] with u hu
        rw [Pi.smul_apply, smul_eq_mul, h_ge u hu.le, mul_zero]
      exact deriv_h_eq_zero_of_nhds_v2 hev
    have hps1 : profileX s ≤ profileX 1 := profileX_le_profileX' (by norm_num) hs1
    have hps0 : profileX s ≤ profileX s₀ := profileX_le_profileX' (by linarith [hτ0, hcdef]) hs0
    rw [h1, h2, hsm0, hd0]
    simp only [add_zero]
    have hgoal : (∫ t in (-profileX s)..(profileX s),
        (((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)) = 0 :=
      intervalIntegral_eq_zero_of_odd (a := profileX s)
        (g := fun u : ℝ => ((1 - u ^ 2) - (s * u) ^ 2) ^ (n - 1) * u) (fun x => by ring)
    rw [show (∫ t in (-profileX s)..(profileX s), (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t)
        = (∫ t in (-profileX s)..(profileX s),
            (((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)) from ?_]
    · exact hgoal
    · apply intervalIntegral.integral_congr_ae
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ (measure_singleton 0)
      intro t ht
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at ht ⊢
      by_contra hne
      have hmem : t ∈ Set.uIoc (-profileX s) (profileX s) := by
        by_contra hmem
        exact ht fun h => absurd h hmem
      rw [Set.uIoc_of_le (neg_le_self (profileX_pos' s).le)] at hmem
      have hval : f t ^ 2 = fhat t ^ 2 :=
        hsq_all t hne (by linarith [hmem.1, hps0]) (by linarith [hmem.2, hps0])
      have ht1 : |t| ≤ profileX 1 := by
        rw [abs_le]
        exact ⟨by linarith [hmem.1, hps1], by linarith [hmem.2, hps1]⟩
      obtain ⟨ha1, ha2⟩ := abs_le.mp ht1
      exact ht fun _ => by rw [hval, hfb t ⟨by linarith, by linarith⟩]
  have hsemi_profX : ∀ σ : ℝ, 0 ≤ σ → semicircle (profileX σ) = σ * profileX σ := by
    intro σ hσ
    have hsq := semicircle_profileX_sq σ
    have h1 : 0 ≤ semicircle (profileX σ) := Real.sqrt_nonneg _
    have h2 : 0 ≤ σ * profileX σ := mul_nonneg hσ (profileX_pos' σ).le
    nlinarith [hsq, h1, h2]
  have hsymm : ∀ σ : ℝ, 0 ≤ σ → semicircle (-(profileX σ)) = σ * profileX σ := by
    intro σ hσ
    rw [semicircle_even]
    exact hsemi_profX σ hσ
  -- `f` agrees with the semicircle off the anchor cap
  have hf_semi_pos : ∀ t : ℝ, profileX s₀ ≤ t → t < 1 → f t = semicircle t := by
    intro t ht ht1
    obtain ⟨σ, hσpos, hσt⟩ := hYt_surj t (by linarith [ht, profileX_pos' s₀]) ht1
    have hσle : σ ≤ s₀ := by
      by_contra hcon
      have hcon' : s₀ < σ := not_le.mp hcon
      have h3 : Yt σ < Yt s₀ := hYt_anti hs₀pos (lt_of_lt_of_le hs₀pos hcon'.le) hcon'
      rw [hσt, hYt_high s₀ le_rfl, hYs₀] at h3
      linarith
    have hval := hf_root_pos σ hσpos
    have hσt' : t = profileX σ := hσt.symm.trans (hYt_low σ hσle)
    rw [hσt] at hval
    rw [hval, h_le σ (by linarith [hσle, hs₀_lt]), mul_zero, add_zero, hσt',
      hsemi_profX σ hσpos.le]
  have hf_semi_neg : ∀ t : ℝ, t ≤ -profileX s₀ → -1 < t → f t = semicircle t := by
    intro t ht ht1
    obtain ⟨σ, hσpos, hσt⟩ := hXt_surj (-t) (by linarith [ht, profileX_pos' s₀]) (by linarith)
    have hσle : σ ≤ s₀ := by
      by_contra hcon
      have hcon' : s₀ < σ := not_le.mp hcon
      have h3 : Xt σ < Xt s₀ := hXt_anti hs₀pos (lt_of_lt_of_le hs₀pos hcon'.le) hcon'
      rw [hσt, hXt_high s₀ le_rfl, hXs₀] at h3
      linarith
    have hval := hf_root_neg σ hσpos
    have hσt' : -t = profileX σ := hσt.symm.trans (hXt_low σ hσle)
    rw [hσt] at hval
    simp only [neg_neg] at hval
    rw [hval, h_le σ (by linarith [hσle, hs₀_lt]), mul_zero, add_zero]
    rw [show t = -(profileX σ) from by linarith [hσt'], hsymm σ hσpos.le]
    ring
  have hf_semi : ∀ t : ℝ, profileX s₀ ≤ |t| → f t = semicircle t := by
    intro t ht
    rcases le_or_gt 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at ht
      rcases lt_or_ge t 1 with ht1 | ht1
      · exact hf_semi_pos t ht ht1
      · rcases eq_or_lt_of_le ht1 with h | h
        · rw [show t = 1 from by linarith, hf_one]; simp [semicircle]
        · have hnot : t ∉ Set.Icc (-1:ℝ) 1 := by
            simp only [Set.mem_Icc, not_and_or, not_le]
            exact Or.inr (by linarith)
          have hzf : f t = 0 := by
            by_contra hne
            exact hnot (hf_supp (Function.mem_support.mpr hne))
          have hzs : semicircle t = 0 := by
            by_contra hne
            exact hnot (semicircle_support_subset (Function.mem_support.mpr hne))
          rw [hzf, hzs]
    · rw [abs_of_neg ht0] at ht
      rcases lt_or_ge (-1) t with ht1 | ht1
      · exact hf_semi_neg t (by linarith) ht1
      · rcases eq_or_lt_of_le ht1 with h | h
        · rw [show t = -1 from by linarith, hf_negone]; simp [semicircle]
        · have hnot : t ∉ Set.Icc (-1:ℝ) 1 := by
            simp only [Set.mem_Icc, not_and_or, not_le]
            exact Or.inl (by linarith)
          have hzf : f t = 0 := by
            by_contra hne
            exact hnot (hf_supp (Function.mem_support.mpr hne))
          have hzs : semicircle t = 0 := by
            by_contra hne
            exact hnot (semicircle_support_subset (Function.mem_support.mpr hne))
          rw [hzf, hzs]
  -- the binomial relations at `s₀`, transferred from the device to `f`
  have htrans : ∀ (m j : ℕ),
      (∫ t in (-(profileX s₀))..(profileX s₀), (f t ^ 2 - (s₀ * t) ^ 2) ^ m * t ^ j)
        = (∫ t in (-(profileX s₀))..(profileX s₀), (fhat t ^ 2 - (s₀ * t) ^ 2) ^ m * t ^ j) := by
    intro m j
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton 0)
    intro t ht
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at ht ⊢
    by_contra hne
    have hmem : t ∈ Set.uIoc (-(profileX s₀)) (profileX s₀) := by
      by_contra hmem
      exact ht fun h => absurd h hmem
    rw [Set.uIoc_of_le (neg_le_self (profileX_pos' s₀).le)] at hmem
    have hval : f t ^ 2 = fhat t ^ 2 :=
      hsq_all t hne (by linarith [hmem.1]) (by linarith [hmem.2])
    exact ht fun _ => by rw [hval]
  have hsm0' : (ε • h) s₀ = 0 := by
    rw [Pi.smul_apply, smul_eq_mul, h_le s₀ (le_of_lt hs₀_lt), mul_zero]
  have hrel'_u : (∀ k : ℕ, k ≤ n → (∫ t in (-(profileX s₀))..(profileX s₀),
        (fhat t ^ 2 - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k))
      = (∫ t in (-(profileX s₀))..(profileX s₀),
          ((1 - t ^ 2) - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k))) ∧
      (∀ k : ℕ, k ≤ n - 1 → (∫ t in (-(profileX s₀))..(profileX s₀),
        (fhat t ^ 2 - (s₀ * t) ^ 2) ^ (n - 1 - k) * t ^ (2 * k + 1)) = 0) := by
    constructor
    · intro k hk
      have hm := hrel'.1 k hk
      simp only [momE, refE, profileX] at hm
      rw [hXs₀, hYs₀, hsm0'] at hm
      simp only [add_zero] at hm
      exact hm
    · intro k hk
      have hm := hrel'.2 k hk
      simp only [momO, profileX] at hm
      rw [hXs₀, hYs₀, hsm0'] at hm
      simp only [add_zero] at hm
      exact hm
  have hrel_f : (∀ k : ℕ, k ≤ n → (∫ t in (-(profileX s₀))..(profileX s₀),
        (f t ^ 2 - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k))
      = (∫ t in (-(profileX s₀))..(profileX s₀),
          ((1 - t ^ 2) - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k))) ∧
      (∀ k : ℕ, k ≤ n - 1 → (∫ t in (-(profileX s₀))..(profileX s₀),
        (f t ^ 2 - (s₀ * t) ^ 2) ^ (n - 1 - k) * t ^ (2 * k + 1)) = 0) := by
    constructor
    · intro k hk
      rw [htrans (n - k) (2 * k)]
      exact hrel'_u.1 k hk
    · intro k hk
      rw [htrans (n - 1 - k) (2 * k + 1)]
      exact hrel'_u.2 k hk
  -- the identities below the anchor
  have hbelow := moment_eqs_below_of_relations (n := n) hn (s₀ := s₀) hs₀pos
    (h := ε • h) (x := Xt) (y := Yt) (f := f)
    (fun s hs => by
      rw [Pi.smul_apply, smul_eq_mul, h_le s (by linarith [hs.2, hs₀_lt]), mul_zero])
    (fun s hs => by
      have hev : (ε • h) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [Ioo_mem_nhds (show s - 1 < s by linarith)
          (show s < 1 - 2 * τ by linarith [hs.2, hs₀_lt])] with u hu
        rw [Pi.smul_apply, smul_eq_mul, h_le u hu.2.le, mul_zero]
      exact deriv_h_eq_zero_of_nhds_v2 hev)
    (fun s hs => hXt_low s hs.2)
    (fun s hs => hYt_low s hs.2)
    hf_semi hrel_f
  -- ----------------------------------------------------------------------
  -- the moment identities for all `s > 0`
  -- ----------------------------------------------------------------------
  have hM_all : ∀ s : ℝ, 0 < s →
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n)
        = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n) := by
    intro s hs
    rcases le_or_gt s s₀ with h1 | h1
    · exact (hbelow s ⟨hs.le, h1⟩).1
    · rcases le_or_gt s 1 with h2 | h2
      · exact hM_s s ⟨h1.le, h2⟩
      · exact hM_big s h2.le
  have hH_all : ∀ s : ℝ, 0 < s →
      (∫ t in (-Xt s)..(Yt s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) *
        (t + deriv (ε • h) s)) = 0 := by
    intro s hs
    rcases le_or_gt s s₀ with h1 | h1
    · exact (hbelow s ⟨hs.le, h1⟩).2
    · rcases le_or_gt s 1 with h2 | h2
      · exact hH_s s ⟨h1.le, h2⟩
      · exact hH_big s h2.le
  -- ----------------------------------------------------------------------
  -- continuity on the closed interval and positivity of `f`
  -- ----------------------------------------------------------------------
  have hc_semi : Continuous semicircle := by
    have h : Continuous (fun t : ℝ => Real.sqrt (1 - t ^ 2)) := by fun_prop
    exact h
  have hps0_lt1 : profileX s₀ < 1 := hprof_lt1 s₀ hs₀pos
  have hf_cont_Icc : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
    intro t ht
    rcases lt_trichotomy t 1 with hlt | heq | hgt
    · rcases lt_trichotomy t (-1) with hlt2 | heq2 | hgt2
      · exact absurd ht.1 (not_le.mpr hlt2)
      · subst heq2
        have hev : f =ᶠ[𝓝[Set.Icc (-1 : ℝ) 1] (-1 : ℝ)] semicircle := by
          have hU : Set.Iio (-profileX s₀) ∈ 𝓝 (-1 : ℝ) :=
            Iio_mem_nhds (show (-1 : ℝ) < -profileX s₀ by linarith)
          filter_upwards [nhdsWithin_le_nhds hU] with u hu
          have hu' : u < 0 := by have hp := profileX_pos' s₀; linarith [Set.mem_Iio.mp hu]
          refine hf_semi u ?_
          rw [abs_of_neg hu']
          linarith [Set.mem_Iio.mp hu]
        have h2 : f (-1 : ℝ) = semicircle (-1 : ℝ) := by
          rw [hf_negone]; simp [semicircle]
        exact ((hc_semi.continuousAt).continuousWithinAt).congr_of_eventuallyEq hev h2
      · have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hgt2, hlt⟩
        exact ((hf_sm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).continuousAt).continuousWithinAt
    · subst heq
      have hev : f =ᶠ[𝓝[Set.Icc (-1 : ℝ) 1] (1 : ℝ)] semicircle := by
        have hU : Set.Ioi (profileX s₀) ∈ 𝓝 (1 : ℝ) :=
          Ioi_mem_nhds (show profileX s₀ < 1 by linarith)
        filter_upwards [nhdsWithin_le_nhds hU] with u hu
        refine hf_semi u ?_
        rw [abs_of_pos (by have hp := profileX_pos' s₀; linarith [Set.mem_Ioi.mp hu])]
        linarith [Set.mem_Ioi.mp hu]
      have h2 : f (1 : ℝ) = semicircle (1 : ℝ) := by
        rw [hf_one]; simp [semicircle]
      exact ((hc_semi.continuousAt).continuousWithinAt).congr_of_eventuallyEq hev h2
    · exact absurd ht.2 (not_le.mpr hgt)
  -- (1) derivative identities on the window and the coordinate identities for `Z`
  have hderY' : ∀ s : ℝ, 3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 < s → s < 1 →
      deriv Y s = Z s 3 := by
    intro s h1 h2
    exact (hderb s ⟨h1, h2⟩).2
  have hderX' : ∀ s : ℝ, 3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 < s → s < 1 →
      deriv X s = Z s 2 := by
    intro s h1 h2
    exact (hderb s ⟨h1, h2⟩).1
  have ha₁_lt_of : ∀ s : ℝ, 1 - 2 * τ ≤ s →
      3 * (1 - 2 * τ) / 8 - (1 - 2 * τ) / 32 < s := by
    intro s hs
    nlinarith [hs, h12t]
  have hcoordZ : ∀ i : Fin 4, ∀ s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1,
      (deriv Z s) i = deriv (fun u : ℝ => Z u i) s := by
    intro i s hs
    exact deriv_apply_state Z i
      ((hZsm.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt (by simp))
  have hcoordB : ∀ i : Fin 4, ∀ s : ℝ,
      (deriv baseZ s) i = deriv (fun u : ℝ => baseZ u i) s := by
    intro i s
    exact deriv_apply_state baseZ i ((contDiff_baseZ.differentiable (by simp)) s)
  have hB2 : (fun u : ℝ => baseZ u 2) = deriv profileX :=
    funext (fun u => baseZ_apply_two u)
  have hB3 : (fun u : ℝ => baseZ u 3) = deriv profileX :=
    funext (fun u => baseZ_apply_three u)
  -- the derivative of `Z` is close to the derivative of the base state
  have hZdev : ∀ s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1,
      ‖deriv Z s - deriv baseZ s‖ ≤ 1 / 1000 := by
    intro s hs
    refine hdev ε ⟨hε0.le, le_of_lt hεa₀d⟩ s hs Z hZc hZbd ?_
    have hG : ContDiff ℝ ∞ (fun p : ℝ × VS => RyaboginVolterra.G n (ε • h) p.1 p.2) :=
      contDiff_G_pair n (hh.const_smul ε)
    have hK : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × VS =>
        RyaboginVolterra.Theta n (ε • h) p.1 p.2.1 p.2.2) Set.univ :=
      (contDiff_Theta_curried n (hh.const_smul ε)).contDiffOn
    have hXid : DifferentiableAt ℝ (fun u : ℝ => RyaboginVolterra.Xi n (ε • h) u) s :=
      (contDiff_Xi n (hh.const_smul ε)).differentiable (by simp) s
    have hZ' : HasDerivAt Z (deriv Z s) s :=
      ((hZsm.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt (by simp)).hasDerivAt
    exact deriv_state_eq n hZc hZ' hG hK hXid hZfix hs
  -- (2) the deviation bounds for `Yt`, for all `s > 0`
  have hYt_dev : ∀ s : ℝ, 0 < s →
      |Yt s - profileX s| ≤ ρd ∧ |deriv Yt s - deriv profileX s| ≤ ρd
        ∧ |deriv (deriv Yt) s - deriv (deriv profileX) s| ≤ 1 / 1000 := by
    intro s hs
    by_cases hsc : s ∈ Set.Icc (1 - 2 * τ) c
    · have hsα : s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1 :=
        ⟨by linarith [hsc.1, h12t], by linarith [hsc.2, hc1]⟩
      have hmem : s ∈ Set.Icc ((1 - 2 * τ) / 4) 1 := ⟨hsα.1.le, hsα.2.le⟩
      have hYtY : Yt =ᶠ[𝓝 s] Y := hYt_Y_nhds s (by linarith [hs₀_lt, hsc.1])
      have hXYs : Y s = Z s 1 :=
        (hXY s ⟨by linarith [hsc.1, h12t], le_trans hsc.2 hc1.le⟩).2
      refine ⟨?_, ?_, ?_⟩
      · have h3 : |Z s 1 - baseZ s 1| ≤ ‖Z s - baseZ s‖ := by
          have hbd := abs_apply_le_norm_state (Z s - baseZ s) 1
          simpa [Pi.sub_apply] using hbd
        rw [hYtY.eq_of_nhds, hXYs, ← baseZ_apply_one]
        exact le_trans h3 (hZbd s hmem)
      · have h3 : |Z s 3 - baseZ s 3| ≤ ‖Z s - baseZ s‖ := by
          have hbd := abs_apply_le_norm_state (Z s - baseZ s) 3
          simpa [Pi.sub_apply] using hbd
        rw [hYtY.deriv_eq, hderY' s (ha₁_lt_of s hsc.1) hsα.2, ← baseZ_apply_three]
        exact le_trans h3 (hZbd s hmem)
      · have hev : deriv Y =ᶠ[𝓝 s] (fun u : ℝ => Z u 3) := by
          filter_upwards [Ioo_mem_nhds (ha₁_lt_of s hsc.1) hsα.2] with u hu
          exact hderY' u hu.1 hu.2
        have h5 : deriv (deriv Yt) s = (deriv Z s) 3 := by
          rw [hYtY.deriv.deriv_eq, hev.deriv_eq, hcoordZ 3 s hsα]
        have h6 : deriv (deriv profileX) s = (deriv baseZ s) 3 := by
          rw [hcoordB 3 s, hB3]
        have h7 : |(deriv Z s) 3 - (deriv baseZ s) 3| ≤ 1 / 1000 := by
          have hbd := abs_apply_le_norm_state (deriv Z s - deriv baseZ s) 3
          have hbd' : |(deriv Z s) 3 - (deriv baseZ s) 3|
              ≤ ‖deriv Z s - deriv baseZ s‖ := by
            simpa [Pi.sub_apply] using hbd
          exact le_trans hbd' (hZdev s hsα)
        rw [h5, h6]
        exact h7
    · have hlt : s < 1 - 2 * τ ∨ c < s := by
        by_contra hcon
        push_neg at hcon
        exact hsc ⟨hcon.1, hcon.2⟩
      have hy : Yt =ᶠ[𝓝 s] profileX := by
        rcases hlt with h1 | h1
        · exact hYt_pX_nhds s h1
        · have h2 : Y =ᶠ[𝓝 s] profileX := by
            filter_upwards [Ioi_mem_nhds (show c < s from h1)] with u hu
            exact hYp u hu.le
          exact (hYt_Y_nhds s (by linarith [hs₀c, h1])).trans h2
      refine ⟨?_, ?_, ?_⟩
      · rw [hy.eq_of_nhds, sub_self, abs_zero]; exact hρd.le
      · rw [hy.deriv_eq, sub_self, abs_zero]; exact hρd.le
      · rw [(hy.deriv.deriv).eq_of_nhds, sub_self, abs_zero]; norm_num
  -- (3) the deviation bounds for `Xt`, for all `s > 0`
  have hXt_dev : ∀ s : ℝ, 0 < s →
      |Xt s - profileX s| ≤ ρd ∧ |deriv Xt s - deriv profileX s| ≤ ρd
        ∧ |deriv (deriv Xt) s - deriv (deriv profileX) s| ≤ 1 / 1000 := by
    intro s hs
    by_cases hsc : s ∈ Set.Icc (1 - 2 * τ) c
    · have hsα : s ∈ Set.Ioo ((1 - 2 * τ) / 4) 1 :=
        ⟨by linarith [hsc.1, h12t], by linarith [hsc.2, hc1]⟩
      have hmem : s ∈ Set.Icc ((1 - 2 * τ) / 4) 1 := ⟨hsα.1.le, hsα.2.le⟩
      have hXtX : Xt =ᶠ[𝓝 s] X := hXt_X_nhds s (by linarith [hs₀_lt, hsc.1])
      have hXYs : X s = Z s 0 :=
        (hXY s ⟨by linarith [hsc.1, h12t], le_trans hsc.2 hc1.le⟩).1
      refine ⟨?_, ?_, ?_⟩
      · have h3 : |Z s 0 - baseZ s 0| ≤ ‖Z s - baseZ s‖ := by
          have hbd := abs_apply_le_norm_state (Z s - baseZ s) 0
          simpa [Pi.sub_apply] using hbd
        rw [hXtX.eq_of_nhds, hXYs, ← baseZ_apply_zero]
        exact le_trans h3 (hZbd s hmem)
      · have h3 : |Z s 2 - baseZ s 2| ≤ ‖Z s - baseZ s‖ := by
          have hbd := abs_apply_le_norm_state (Z s - baseZ s) 2
          simpa [Pi.sub_apply] using hbd
        rw [hXtX.deriv_eq, hderX' s (ha₁_lt_of s hsc.1) hsα.2, ← baseZ_apply_two]
        exact le_trans h3 (hZbd s hmem)
      · have hev : deriv X =ᶠ[𝓝 s] (fun u : ℝ => Z u 2) := by
          filter_upwards [Ioo_mem_nhds (ha₁_lt_of s hsc.1) hsα.2] with u hu
          exact hderX' u hu.1 hu.2
        have h5 : deriv (deriv Xt) s = (deriv Z s) 2 := by
          rw [hXtX.deriv.deriv_eq, hev.deriv_eq, hcoordZ 2 s hsα]
        have h6 : deriv (deriv profileX) s = (deriv baseZ s) 2 := by
          rw [hcoordB 2 s, hB2]
        have h7 : |(deriv Z s) 2 - (deriv baseZ s) 2| ≤ 1 / 1000 := by
          have hbd := abs_apply_le_norm_state (deriv Z s - deriv baseZ s) 2
          have hbd' : |(deriv Z s) 2 - (deriv baseZ s) 2|
              ≤ ‖deriv Z s - deriv baseZ s‖ := by
            simpa [Pi.sub_apply] using hbd
          exact le_trans hbd' (hZdev s hsα)
        rw [h5, h6]
        exact h7
    · have hlt : s < 1 - 2 * τ ∨ c < s := by
        by_contra hcon
        push_neg at hcon
        exact hsc ⟨hcon.1, hcon.2⟩
      have hx : Xt =ᶠ[𝓝 s] profileX := by
        rcases hlt with h1 | h1
        · exact hXt_pX_nhds s h1
        · have h2 : X =ᶠ[𝓝 s] profileX := by
            filter_upwards [Ioi_mem_nhds (show c < s from h1)] with u hu
            exact hXp u hu.le
          exact (hXt_X_nhds s (by linarith [hs₀c, h1])).trans h2
      refine ⟨?_, ?_, ?_⟩
      · rw [hx.eq_of_nhds, sub_self, abs_zero]; exact hρd.le
      · rw [hx.deriv_eq, sub_self, abs_zero]; exact hρd.le
      · rw [(hx.deriv.deriv).eq_of_nhds, sub_self, abs_zero]; norm_num
  -- (4) the smallness arithmetic
  have hA0 : 0 ≤ Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000) := by
    have hA1 : (0:ℝ) ≤ Chdd * (1 / 2 + ρd) := mul_nonneg hChdd0 (by linarith [hρd.le])
    have hA2 : (0:ℝ) ≤ Chd * (1 + 1 / 1000) := mul_nonneg hChd0 (by norm_num)
    linarith
  have hε0_le : |ε| ≤ ε₀ := by rw [abs_of_pos hε0]; exact hεε₀.le
  have h2mul : ε₀ * (100 * (Chd + Chdd + 1)) ≤ 1 := by
    have hY : (0:ℝ) < 100 * (Chd + Chdd + 1) := by linarith
    calc ε₀ * (100 * (Chd + Chdd + 1))
        ≤ (1 / (100 * (Chd + Chdd + 1))) * (100 * (Chd + Chdd + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hY.le
      _ = 1 := div_mul_cancel₀ 1 (ne_of_gt hY)
  have h3mul : ε₀ * (Chd + Chdd + 1) ≤ 1 / 100 := by
    have h4 : ε₀ * (Chd + Chdd + 1) * 100 = ε₀ * (100 * (Chd + Chdd + 1)) := by ring
    nlinarith [h2mul, h4]
  have hA_le : Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000)
      ≤ (Chd + Chdd + 1) * (11 / 10) := by
    have h5 : 1 / 2 + ρd ≤ 11 / 10 := by linarith [hρdle]
    have h6 : 1 + 1 / 1000 ≤ 11 / 10 := by norm_num
    nlinarith [hChd0, hChdd0, h5, h6]
  have hεCh : |ε| * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000)) < 1 / 50 := by
    have h7 : |ε| * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000))
        ≤ ε₀ * ((Chd + Chdd + 1) * (11 / 10)) := by
      have h8 : |ε| * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000))
          ≤ ε₀ * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000)) :=
        mul_le_mul_of_nonneg_right hε0_le hA0
      have h9 : ε₀ * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000))
          ≤ ε₀ * ((Chd + Chdd + 1) * (11 / 10)) :=
        mul_le_mul_of_nonneg_left hA_le hε₀pos.le
      linarith
    have h10 : ε₀ * ((Chd + Chdd + 1) * (11 / 10)) ≤ 1 / 100 * (11 / 10) := by
      have h11 : ε₀ * ((Chd + Chdd + 1) * (11 / 10))
          = (ε₀ * (Chd + Chdd + 1)) * (11 / 10) := by ring
      rw [h11]
      exact mul_le_mul_of_nonneg_right h3mul (by norm_num)
    linarith [h7, h10]
  have hsmall' : 2 * ρd + 2 * ρd ^ 2 + (1 / 1000) + ρd + ρd * (1 / 1000)
      + |ε| * (Chdd * (1 / 2 + ρd) + Chd * (1 + 1 / 1000)) < 1 / 8 := by
    have h1 : ρd ≤ 1 / 1000 := hρdle
    have h2 : ρd ^ 2 ≤ (1 / 1000) ^ 2 := by nlinarith [h1, hρd.le]
    have h3 : ρd * (1 / 1000) ≤ (1 / 1000) ^ 2 := by nlinarith [h1, hρd.le]
    nlinarith [h1, h2, h3, hεCh, hρd.le]
  -- (5) the curvature is positive on the window
  have hNp_strip : ∀ s ∈ Set.Icc (1 - 2 * τ) c,
      0 < deriv (deriv (fun u : ℝ => u * Yt u + ε * h u)) s * deriv Yt s
        - deriv (fun u : ℝ => u * Yt u + ε * h u) s * deriv (deriv Yt) s := by
    refine Np_pos_of_close (y := Yt) (h := h) (ε := ε) (ρ := ρd) (ηD := 1 / 1000)
      (Ch := Ch) (Ch' := Chd) (Ch'' := Chdd) hτsmall hc1.le hρd.le (by norm_num) hChd0 hChdd0
      hYt_sm hh hhb hhbd hhbdd ?_ ?_ ?_ hsmall'
    · exact fun s hs => (hYt_dev s hs).1
    · exact fun s hs => (hYt_dev s hs).2.1
    · exact fun s hs => (hYt_dev s hs).2.2
  have hNp_stripX : ∀ s ∈ Set.Icc (1 - 2 * τ) c,
      0 < deriv (deriv (fun u : ℝ => u * Xt u + (-ε) * h u)) s * deriv Xt s
        - deriv (fun u : ℝ => u * Xt u + (-ε) * h u) s * deriv (deriv Xt) s := by
    refine Np_pos_of_close (y := Xt) (h := h) (ε := -ε) (ρ := ρd) (ηD := 1 / 1000)
      (Ch := Ch) (Ch' := Chd) (Ch'' := Chdd) hτsmall hc1.le hρd.le (by norm_num) hChd0 hChdd0
      hXt_sm hh hhb hhbd hhbdd ?_ ?_ ?_ ?_
    · exact fun s hs => (hXt_dev s hs).1
    · exact fun s hs => (hXt_dev s hs).2.1
    · exact fun s hs => (hXt_dev s hs).2.2
    · rw [abs_neg]; exact hsmall'
  -- (6) globally, by the two cases
  have hNp : ∀ s : ℝ, 0 < s →
      0 < deriv (deriv (fun u : ℝ => u * Yt u + ε * h u)) s * deriv Yt s
        - deriv (fun u : ℝ => u * Yt u + ε * h u) s * deriv (deriv Yt) s := by
    intro s hs
    by_cases hsc : s ∈ Set.Icc (1 - 2 * τ) c
    · exact hNp_strip s hsc
    · have hlt : s < 1 - 2 * τ ∨ c < s := by
        by_contra hcon
        push_neg at hcon
        exact hsc ⟨hcon.1, hcon.2⟩
      refine Np_pos_of_eventually (y := Yt) (h := h) (ε := ε) ?_ ?_
      · rcases hlt with h1 | h1
        · exact hYt_pX_nhds s h1
        · have h2 : Y =ᶠ[𝓝 s] profileX := by
            filter_upwards [Ioi_mem_nhds (show c < s from h1)] with u hu
            exact hYp u hu.le
          exact (hYt_Y_nhds s (by linarith [hs₀c, h1])).trans h2
      · rcases hlt with h1 | h1
        · filter_upwards [Iio_mem_nhds (show s < 1 - 2 * τ from h1)] with u hu
          exact h_le u hu.le
        · filter_upwards [Ioi_mem_nhds (show 1 - τ < s by linarith [h1, hcdef, hτ0])] with u hu
          exact h_ge u hu.le
  have hNn : ∀ s : ℝ, 0 < s →
      deriv (deriv (fun u : ℝ => -(u * (-(Xt u)) + ε * h u))) s * deriv (fun u : ℝ => -(Xt u)) s
        - deriv (fun u : ℝ => -(u * (-(Xt u)) + ε * h u)) s
          * deriv (deriv (fun u : ℝ => -(Xt u))) s < 0 := by
    intro s hs
    rw [Nn_eq_neg_Np Xt h ε s]
    by_cases hsc : s ∈ Set.Icc (1 - 2 * τ) c
    · have hNpX := hNp_stripX s hsc
      linarith
    · have hlt : s < 1 - 2 * τ ∨ c < s := by
        by_contra hcon
        push_neg at hcon
        exact hsc ⟨hcon.1, hcon.2⟩
      have hNpX := Np_pos_of_eventually (y := Xt) (h := h) (ε := -ε)
        (by
          rcases hlt with h1 | h1
          · exact hXt_pX_nhds s h1
          · have h2 : X =ᶠ[𝓝 s] profileX := by
              filter_upwards [Ioi_mem_nhds (show c < s from h1)] with u hu
              exact hXp u hu.le
            exact (hXt_X_nhds s (by linarith [hs₀c, h1])).trans h2)
        (by
          rcases hlt with h1 | h1
          · filter_upwards [Iio_mem_nhds (show s < 1 - 2 * τ from h1)] with u hu
            exact h_le u hu.le
          · filter_upwards [Ioi_mem_nhds (show 1 - τ < s by linarith [h1, hcdef, hτ0])] with u hu
            exact h_ge u hu.le)
      linarith
  -- (7) `f` agrees with the semicircle near `0`
  have hsc_near : f =ᶠ[𝓝 (0:ℝ)] semicircle := by
    have hApos : 0 < profileX c := profileX_pos c hcpos
    have hpc1 : profileX c < 1 := hprof_lt1 c hcpos
    have hbr_pos : ∀ t ∈ Set.Ioo (0:ℝ) (profileX c), f t = semicircle t := by
      intro t ht
      obtain ⟨σ, hσpos, hσt⟩ := hYt_surj t (by linarith [ht.1]) (by linarith [ht.2, hpc1])
      have hσc : c ≤ σ := by
        by_contra hcon
        push_neg at hcon
        have h1 : Yt c < Yt σ := hYt_anti hσpos hcpos hcon
        rw [hYt_high c hs₀c.le, hYc, hσt] at h1
        linarith [ht.2]
      have hprof : profileX σ = t := by
        rw [← hYp σ hσc, ← hYt_high σ (le_trans hs₀c.le hσc), hσt]
      have hval : f (Yt σ) = σ * Yt σ + (ε • h) σ := hf_root_pos σ hσpos
      have hσh : (ε • h) σ = 0 := by
        rw [Pi.smul_apply, smul_eq_mul, h_ge σ (by linarith [hσc, hcdef, hτ0]), mul_zero]
      rw [show t = Yt σ from hσt.symm]
      rw [hval, hσt, hσh, add_zero]
      rw [← hprof]
      exact (hsemi_profX σ hσpos.le).symm
    have hbr_neg : ∀ t ∈ Set.Ioo (-(profileX c)) (0:ℝ), f t = semicircle t := by
      intro t ht
      obtain ⟨σ, hσpos, hσt⟩ := hXt_surj (-t) (by linarith [ht.2]) (by linarith [ht.1, hpc1])
      have hσc : c ≤ σ := by
        by_contra hcon
        push_neg at hcon
        have h1 : Xt c < Xt σ := hXt_anti hσpos hcpos hcon
        rw [hXt_high c hs₀c.le, hXc, hσt] at h1
        linarith [ht.1]
      have hprof : profileX σ = -t := by
        rw [← hXp σ hσc, ← hXt_high σ (le_trans hs₀c.le hσc), hσt]
      have hval : f (-(Xt σ)) = -(σ * (-(Xt σ)) + (ε • h) σ) := hf_root_neg σ hσpos
      have hσh : (ε • h) σ = 0 := by
        rw [Pi.smul_apply, smul_eq_mul, h_ge σ (by linarith [hσc, hcdef, hτ0]), mul_zero]
      have ht_eq : t = -(Xt σ) := by rw [hσt, neg_neg]
      rw [ht_eq]
      rw [hval, hσt, neg_neg, hσh, add_zero]
      rw [show -(σ * t) = σ * (-t) by ring]
      rw [show -t = profileX σ from hprof.symm]
      rw [← hsemi_profX σ hσpos.le, hprof]
      exact semicircle_even t
    have hm0 : f 0 = semicircle 0 :=
      eq_of_continuousAt_of_eqOn_Ioo (a := (0:ℝ)) (b := profileX c)
        hApos ⟨le_rfl, hApos.le⟩
        (hf_cont_Icc.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num)))
        hc_semi.continuousAt (fun u hu => hbr_pos u hu)
    rw [Filter.EventuallyEq, Metric.eventually_nhds_iff]
    refine ⟨profileX c, hApos, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_lt] at ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · exact hbr_neg t ⟨by linarith [ht.1], hlt⟩
    · subst heq; exact hm0
    · exact hbr_pos t ⟨hgt, by linarith [ht.2]⟩
  -- (8) strict concavity
  have hv_sm : ContDiff ℝ ∞ (fun u : ℝ => u * Yt u + ε * h u) :=
    (contDiff_id.mul hYt_sm).add (hh.const_smul ε)
  have hw_sm : ContDiff ℝ ∞ (fun u : ℝ => -(u * (-(Xt u)) + ε * h u)) :=
    ((contDiff_id.mul hXt_sm.neg).add (hh.const_smul ε)).neg
  have hconc' : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f :=
    strictConcaveOn_envelope (y := Yt) (z := fun u : ℝ => -(Xt u))
      (v := fun u : ℝ => u * Yt u + ε * h u)
      (w := fun u : ℝ => -(u * (-(Xt u)) + ε * h u))
      hf_sm hf_cont_Icc hYt_sm hXt_sm.neg hv_sm hw_sm hsc_near
      hYt_der (fun s hs => by
        rw [deriv_neg']
        simp only [Pi.neg_apply]
        linarith [hXt_der s hs])
      hYt_surj
      (fun t ht1 ht0 => by
        obtain ⟨s, hs, hst⟩ := hXt_surj (-t) (by linarith) (by linarith)
        exact ⟨s, hs, by rw [hst]; ring⟩)
      hf_root_pos hf_root_neg hNp hNn
  have hpos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t := by
    intro t ht
    obtain ⟨-, hinterp⟩ := hconc'
    have hne := hinterp (x := (-1 : ℝ)) (y := (1 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) (a := (1 - t) / 2) (b := (1 + t) / 2)
      (by linarith [ht.2]) (by linarith [ht.1]) (by ring)
    have harg : ((1 - t) / 2) • (-1 : ℝ) + ((1 + t) / 2) • (1 : ℝ) = t := by
      simp only [smul_eq_mul]; ring
    rw [harg, hf_negone, hf_one] at hne
    simpa using hne
  -- ----------------------------------------------------------------------
  -- the final assembly
  -- ----------------------------------------------------------------------
  exact ⟨ε, hε0, Xt, Yt, f, hf_supp, hf_sm, hconc', hf_negone, hf_one, hpos, hroot_t,
    hM_all, hH_all⟩

end Commons.Geometry.Ulam


-- ===== FILE _mine_dev25.lean =====
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Pointwise RealInnerProductSpace Interval
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Commons.Geometry.Ulam
open RyaboginVolterra

/-- The `τ`-version of the target, with the two extra conjuncts. -/
lemma honest_perturbation_tau_full (n : ℕ) (hn : 2 ≤ n) (τ : ℝ) (hτ0 : 0 < τ) (hτsmall : 2 * τ < 1)
    (h : ℝ → ℝ)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ))
    (hh_ne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_flat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η → h s = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x y f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + (ε • h) s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + (ε • h) s) ^ 2) ∧
      (∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≠ f (-t)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) * (t + deriv (ε • h) s)) = 0) := by
  obtain ⟨ε, hε0, x, y, f, hf_supp, hf_sm, hf_conc, hf_left, hf_right, hf_pos, hroot, hI, hJ⟩ :=
    honest_perturbation_tau_aux_full n hn τ hτ0 hτsmall h hh_cont hh_supp hh_ne hh_flat
  have hconc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f := hf_conc.concaveOn
  have hsupp_smul : Function.support (ε • h) ⊆ Set.Icc (1 - 2 * τ) (1 - τ) := by
    intro s hs
    apply hh_supp
    rw [Function.mem_support] at hs ⊢
    intro hzero
    exact hs (by rw [Pi.smul_apply, smul_eq_mul, hzero, mul_zero])
  have hcont : ContinuousOn f (Set.Icc (-1 : ℝ) 1) :=
    moment_solution_profile_continuous (h := ε • h) hτ0 hτsmall hsupp_smul hf_supp hf_sm hconc
      hf_left hf_right hf_pos hroot
  have hne_smul : ∃ s : ℝ, (ε • h) s ≠ 0 := by
    obtain ⟨s, _, hsne⟩ := hh_ne
    exact ⟨s, by rw [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (ne_of_gt hε0) hsne⟩
  have hcont_smul : ContDiffOn ℝ ∞ (ε • h) Set.univ := hh_cont.const_smul ε
  have hnot_even : ¬ ∀ t : ℝ, f (-t) = f t :=
    even_profile_moment_solution_not_even (h := ε • h) n hn hτ0 hτsmall hsupp_smul hne_smul
      hcont_smul hf_supp hf_sm hconc hf_left hf_right hf_pos hroot hJ
  have hex0 : ∃ t : ℝ, f t ≠ f (-t) := by
    by_contra hcon
    push_neg at hcon
    exact hnot_even (fun t => by simpa using (hcon (-t)))
  obtain ⟨t, ht⟩ := hex0
  have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    by_contra hmem
    have h1 : f t = 0 := by
      by_contra hne
      exact hmem (hf_supp (Function.mem_support.mpr hne))
    have h2 : f (-t) = 0 := by
      by_contra hne
      apply hmem
      have h3 := hf_supp (Function.mem_support.mpr hne)
      rw [Set.mem_Icc] at h3 ⊢
      constructor <;> linarith [h3.1, h3.2]
    exact ht (by rw [h1, h2])
  exact ⟨ε, hε0, x, y, f, hf_supp, hf_sm, hf_conc, hcont, hf_left, hf_right, hf_pos, hroot,
    ⟨t, htmem, ht⟩, hI, hJ⟩

end Commons.Geometry.Ulam

namespace Commons.Geometry.Ulam

lemma even_profile_perturbation_from_smooth_bump_aux_independent_core (n : ℕ) (hn : 2 ≤ n) {c δ : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ0 : 0 < δ) (hδsmall : 2 * δ < c)
    (h : ℝ → ℝ)
    (hh_cont : ContDiffOn ℝ (⊤ : ℕ∞) h Set.univ)
    (hh_supp : Function.support h ⊆ Set.Icc (c - 2 * δ) (c - δ))
    (hh_ne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0)
    (hh_flat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, c - 2 * δ ≤ s → s < c - 2 * δ + η → h s = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ x y f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1) ∧
      StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f ∧
      ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
      f (-1) = 0 ∧ f 1 = 0 ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t) ∧
      (∀ s : ℝ, 0 < s →
        0 < x s ∧ 0 < y s ∧
        (f (y s)) ^ 2 = (s * y s + (ε • h) s) ^ 2 ∧
        (f (-x s)) ^ 2 = (s * (-x s) + (ε • h) s) ^ 2) ∧
      (∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≠ f (-t)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ n) =
          (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
            ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) ∧
      (∀ s : ℝ, 0 < s →
        (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + (ε • h) s) ^ 2) ^ (n - 1) * (t + deriv (ε • h) s)) = 0) := by
  have hmid : (1 - c + 2 * δ) / 2 < min (1 / 2) (1 - c + δ) := by
    apply lt_min <;> linarith
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℝ,
      (1 - c + 2 * δ) / 2 < τ ∧ τ < min (1 / 2) (1 - c + δ) :=
    ⟨((1 - c + 2 * δ) / 2 + min (1 / 2) (1 - c + δ)) / 2,
      by linarith, by linarith⟩
  have hτ0 : 0 < τ := by linarith [hτ1, hc1]
  have hτsmall : 2 * τ < 1 := by
    have := lt_of_lt_of_le hτ2 (min_le_left (1 / 2 : ℝ) (1 - c + δ))
    linarith
  have hleft : 1 - 2 * τ ≤ c - 2 * δ := by linarith [hτ1]
  have hright : c - δ ≤ 1 - τ := by
    have := lt_of_lt_of_le hτ2 (min_le_right (1 / 2 : ℝ) (1 - c + δ))
    linarith
  have hsupp' : Function.support h ⊆ Set.Icc (1 - 2 * τ) (1 - τ) := by
    intro s hs
    have h1 := hh_supp hs
    exact ⟨le_trans hleft h1.1, le_trans h1.2 hright⟩
  obtain ⟨η, hη0, hη⟩ := hh_flat
  have hgap : 0 < c - 2 * δ - (1 - 2 * τ) := by linarith
  have hflat' : ∃ η' : ℝ, 0 < η' ∧
      ∀ s : ℝ, 1 - 2 * τ ≤ s → s < 1 - 2 * τ + η' → h s = 0 := by
    refine ⟨min (c - 2 * δ - (1 - 2 * τ)) η, lt_min hgap hη0, ?_⟩
    intro s hs1 hs2
    rcases lt_or_ge s (c - 2 * δ) with hlt | hge
    · by_contra hne
      have hmem := hh_supp (Function.mem_support.mpr hne)
      exact absurd hmem.1 (not_le.mpr hlt)
    · have hs3 : s < c - 2 * δ + η := by
        have h4 : 1 - 2 * τ + min (c - 2 * δ - (1 - 2 * τ)) η ≤ c - 2 * δ + η := by
          have h5 := min_le_left (c - 2 * δ - (1 - 2 * τ)) η
          have h6 := min_le_right (c - 2 * δ - (1 - 2 * τ)) η
          linarith
        linarith
      exact hη s hge hs3
  exact honest_perturbation_tau_full n hn τ hτ0 hτsmall h hh_cont hsupp' hh_ne hflat'

end Commons.Geometry.Ulam

