import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.dbarCn_dirDeriv_comm
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.isClosedForm_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.NN.Core.holderNorm_zero_univ_lt_top_of_contDiff_one
import Submission.Work.NN.Core.flatMulNorm

/-!
# The `C^{0,α}` regularity of `∂̄_{J+A}(D^k v)`

This file proves `Work.NN.Core.dbarCn_iteratedFDeriv_holder`: for `v` of class `C^{k+1}` with
compact support, vanishing off the polydisc of radii `ρ'`, and with `∂̄_{J+A} v` of class `C^{k,α}`
on that polydisc, the derivative `∂̄_{J+A}(D^k v)` (contracted with any tuple of directions) has
finite `C^{0,α}` norm on all of `ℂⁿ`.

The proof writes `∂̄_{J+A}(D^k v)` as the sum of

* the `k`-th derivative of `∂̄_{J+A}v` (which is `C^{0,α}` by hypothesis), and
* a correction which is of class `C^1` with compact support.

The correction is a higher Leibniz commutator; the relevant algebraic input is that the
`(0,1)`-derivative has constant coefficients and therefore commutes with `D^k`
(`Work.CR.Flat.Cauchy.dbarCoord_iteratedFDeriv`), and that the perturbation term `Lcoef` is the
`(i/2)`-multiple of the pairing of `fderiv v` with the coefficient field `z ↦ A z e_m`.
-/

noncomputable section

open scoped ContDiff NNReal ENNReal BigOperators
open Filter
open scoped Topology

namespace Work.NN.Core

/-- The higher Leibniz correction of the product `ψ·χ`: the `k`-th derivative of the product minus
`χ` times the `k`-th derivative of `ψ`. -/
private def mulCorr {n : ℕ} (k : ℕ) (ψ χ : (Fin n → ℂ) → ℂ) (u : Fin k → (Fin n → ℂ)) :
    (Fin n → ℂ) → ℂ :=
  fun z => iteratedFDeriv ℝ k (fun y => ψ y * χ y) z u - χ z * iteratedFDeriv ℝ k ψ z u

/-- Expansion of a vector of `ℂⁿ` in the real basis `{e_a, i·e_a}`. -/
private lemma eq_sum_re_im {n : ℕ} (x : Fin n → ℂ) :
    x = ∑ a : Fin n, ((x a).re • (Pi.single a (1:ℂ) : Fin n → ℂ)
      + (x a).im • (Pi.single a (Complex.I) : Fin n → ℂ)) := by
  rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun a _ => ?_
  ext b
  by_cases hb : b = a
  · subst hb; simp [Pi.single_eq_same, Complex.re_add_im]
  · simp [Pi.single_eq_of_ne hb]

/-- A real-linear form on `ℂⁿ`, evaluated on `x`, in terms of the real basis. -/
private lemma fderiv_apply_expand {n : ℕ} (T : (Fin n → ℂ) →L[ℝ] ℂ) (x : Fin n → ℂ) :
    T x = ∑ a : Fin n,
      ((x a).re * T (Pi.single a (1:ℂ)) + (x a).im * T (Pi.single a (Complex.I))) := by
  conv_lhs => rw [eq_sum_re_im x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul]
  simp [Complex.real_smul]

/-- **The Leibniz correction is `C^{m+1}`.**  For `ψ` of class `C^{k+m}` and `χ` of class
`C^{k+m+1}`, the function `z ↦ D^k(ψ·χ)(z)(u) - χ(z)·D^kψ(z)(u)` is of class `C^{m+1}`. -/
private theorem mulCorr_contDiff {n : ℕ} : ∀ (k m : ℕ) {ψ χ : (Fin n → ℂ) → ℂ},
    ContDiff ℝ (k + m) ψ → ContDiff ℝ (k + m + 1) χ → ∀ u : Fin k → (Fin n → ℂ),
    ContDiff ℝ (m + 1) (mulCorr k ψ χ u) := by
  intro k
  induction k with
  | zero =>
    intro m ψ χ hψ hχ u
    have h0 : mulCorr 0 ψ χ u = 0 := by
      funext z
      show (iteratedFDeriv ℝ 0 (fun y => ψ y * χ y) z) u - χ z * (iteratedFDeriv ℝ 0 ψ z) u = 0
      simp only [iteratedFDeriv_zero_apply]
      ring
    rw [h0]; exact contDiff_const
  | succ j ih =>
    intro m ψ χ hψ hχ u
    have hψ' : ContDiff ℝ (↑j + (↑m + 1)) ψ := by
      have hexp : ((j : WithTop ℕ∞) + ((m : WithTop ℕ∞) + 1))
          = (((j + 1 : ℕ) : WithTop ℕ∞) + (m : WithTop ℕ∞)) := by push_cast; ring
      rw [hexp]; exact hψ
    have hχ' : ContDiff ℝ (↑j + (↑m + 1) + 1) χ := by
      have hexp : ((j : WithTop ℕ∞) + ((m : WithTop ℕ∞) + 1) + 1)
          = (((j + 1 : ℕ) : WithTop ℕ∞) + (m : WithTop ℕ∞) + 1) := by push_cast; ring
      rw [hexp]; exact hχ
    have hIH : ContDiff ℝ (m + 2) (mulCorr j ψ χ (Fin.tail u)) := ih (m + 1) hψ' hχ' (Fin.tail u)
    have hone : (1 : WithTop ℕ∞) ≤ (↑m : WithTop ℕ∞) + 1 := by
      exact_mod_cast (show (1:ℕ) ≤ m + 1 by omega)
    have hineq1 : ((↑j : WithTop ℕ∞) + 1) ≤ (↑j : WithTop ℕ∞) + ((↑m : WithTop ℕ∞) + 1) :=
      add_le_add le_rfl hone
    have hψj : ContDiff ℝ (↑j + 1) ψ := hψ'.of_le hineq1
    have hχj : ContDiff ℝ (↑j + 1) χ :=
      hχ'.of_le (le_trans hineq1 (le_self_add : ((↑j : WithTop ℕ∞) + ((↑m : WithTop ℕ∞) + 1))
        ≤ (↑j : WithTop ℕ∞) + ((↑m : WithTop ℕ∞) + 1) + 1))
    have hψχj : ContDiff ℝ (↑j + 1) (fun y => ψ y * χ y) := hψj.mul hχj
    have hFBcd : ContDiff ℝ (m+1) (fun t => (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) := by
      have h1 : ContDiff ℝ (m+1) (iteratedFDeriv ℝ j ψ) :=
        hψ'.iteratedFDeriv_right (m := (m+1 : ℕ)) (i := j) (le_of_eq (by push_cast; abel))
      exact ContDiff.continuousLinearMap_comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => (Fin n → ℂ)) ℂ (Fin.tail u)) h1
    have hχfd : ContDiff ℝ (m+1) (fderiv ℝ χ) :=
      hχ'.fderiv_right (m := (m+1 : ℕ))
        (by exact_mod_cast (show (m+1:ℕ)+1 ≤ j+(m+1)+1 by omega))
    have hpoint : mulCorr (j + 1) ψ χ u
        = fun z => fderiv ℝ χ z (u 0) * (iteratedFDeriv ℝ j ψ z (Fin.tail u))
            + fderiv ℝ (mulCorr j ψ χ (Fin.tail u)) z (u 0) := by
      funext z
      simp only [mulCorr]
      have hFBd : DifferentiableAt ℝ (fun t => (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) z :=
        (hFBcd.differentiable (by simp)).differentiableAt
      have hχd : DifferentiableAt ℝ χ z :=
        (hχ'.differentiable (by simp)).differentiableAt
      have hPBd : DifferentiableAt ℝ (fun t => (iteratedFDeriv ℝ j (fun y => ψ y * χ y) t) (Fin.tail u)
            - χ t * (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) z := by
        have hA2cd : ContDiff ℝ (m+1) (fun t => (iteratedFDeriv ℝ j (fun y => ψ y * χ y) t) (Fin.tail u)) := by
          have h1 : ContDiff ℝ (m+1) (iteratedFDeriv ℝ j (fun y => ψ y * χ y)) :=
            (hψ'.mul (hχ'.of_le (le_self_add : ((↑j : WithTop ℕ∞) + ((↑m : WithTop ℕ∞) + 1))
              ≤ (↑j : WithTop ℕ∞) + ((↑m : WithTop ℕ∞) + 1) + 1))).iteratedFDeriv_right
              (m := (m+1 : ℕ)) (i := j) (le_of_eq (by push_cast; abel))
          exact ContDiff.continuousLinearMap_comp
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => (Fin n → ℂ)) ℂ (Fin.tail u)) h1
        exact ((hA2cd.differentiable (by simp)).differentiableAt).sub (hχd.mul hFBd)
      have hmulh : HasFDerivAt (fun t => χ t * (iteratedFDeriv ℝ j ψ t) (Fin.tail u))
          (χ z • fderiv ℝ (fun t => (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) z
            + (iteratedFDeriv ℝ j ψ z) (Fin.tail u) • fderiv ℝ χ z) z := by
        rw [show (fun t => χ t * (iteratedFDeriv ℝ j ψ t) (Fin.tail u))
            = χ * (fun t => (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) from rfl]
        exact hχd.hasFDerivAt.mul hFBd.hasFDerivAt
      have hFh : HasFDerivAt (fun t => (iteratedFDeriv ℝ j (fun y => ψ y * χ y) t) (Fin.tail u))
          (χ z • fderiv ℝ (fun t => (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) z
            + (iteratedFDeriv ℝ j ψ z) (Fin.tail u) • fderiv ℝ χ z
            + fderiv ℝ (fun t => (iteratedFDeriv ℝ j (fun y => ψ y * χ y) t) (Fin.tail u)
                - χ t * (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) z) z := by
        convert hmulh.add hPBd.hasFDerivAt using 1
        funext t; simp only [Pi.add_apply]; ring
      rw [Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hψχj u z,
          Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hψj u z]
      rw [hFh.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [show (mulCorr j ψ χ (Fin.tail u)) = (fun t => (iteratedFDeriv ℝ j (fun y => ψ y * χ y) t) (Fin.tail u) - χ t * (iteratedFDeriv ℝ j ψ t) (Fin.tail u)) from rfl]
      ring
    rw [hpoint]
    refine ContDiff.add ?_ ?_
    · have h1 : ContDiff ℝ (m + 1) (fun z => fderiv ℝ χ z (u 0)) :=
        ContDiff.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ (u 0)) hχfd
      exact h1.mul hFBcd
    · have h3 : ContDiff ℝ (m + 1) (fderiv ℝ (mulCorr j ψ χ (Fin.tail u))) :=
        hIH.fderiv_right (m := (m+1 : ℕ)) (le_of_eq (by push_cast; abel))
      exact ContDiff.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ (u 0)) h3

/-- **The Leibniz correction has compact support** when `ψ` does. -/
private lemma mulCorr_hasCompactSupport {n k : ℕ} {ψ χ : (Fin n → ℂ) → ℂ} (hψs : HasCompactSupport ψ)
    (u : Fin k → (Fin n → ℂ)) : HasCompactSupport (mulCorr k ψ χ u) := by
  refine hψs.mono' fun z hz => ?_
  by_contra hzt
  exact hz (by
    rw [mulCorr]
    have hψ0 : ψ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
    have h10 : (fun y => ψ y * χ y) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hψ0] with y hy
      simp [hy]
    have e1 : (iteratedFDeriv ℝ k (fun y => ψ y * χ y) z) u = 0 := by
      have h := (h10.iteratedFDeriv ℝ k).eq_of_nhds
      rw [h]; simp
    have e2 : (iteratedFDeriv ℝ k ψ z) u = 0 := by
      have h := (hψ0.iteratedFDeriv ℝ k).eq_of_nhds
      rw [h]; simp
    rw [e1, e2]; ring)

/-- The per-coordinate correction computation. -/
private lemma itFDeriv_pair_split {n k : ℕ} {φ ψ χr χi : Cn n → ℂ} (u : Fin k → Cn n)
    (hφ : ContDiff ℝ k φ) (hψ : ContDiff ℝ k ψ) (hχr : ContDiff ℝ k χr) (hχi : ContDiff ℝ k χi)
    (z : Cn n) :
    (iteratedFDeriv ℝ k (fun y => (χr z - χr y) * φ y + (χi z - χi y) * ψ y) z) u
      = -(mulCorr k φ χr u z + mulCorr k ψ χi u z) := by
  have hP1 : ContDiff ℝ k (fun y => χr z * φ y) := ContDiff.mul contDiff_const hφ
  have hP2 : ContDiff ℝ k (fun y => φ y * χr y) := hφ.mul hχr
  have hQ1 : ContDiff ℝ k (fun y => χi z * ψ y) := ContDiff.mul contDiff_const hψ
  have hQ2 : ContDiff ℝ k (fun y => ψ y * χi y) := hψ.mul hχi
  have hPcd : ContDiff ℝ k ((fun y => χr z * φ y) - (fun y => φ y * χr y)) := hP1.sub hP2
  have hQcd : ContDiff ℝ k ((fun y => χi z * ψ y) - (fun y => ψ y * χi y)) := hQ1.sub hQ2
  have hsplit : (fun y => (χr z - χr y) * φ y + (χi z - χi y) * ψ y)
      = ((fun y => χr z * φ y) - (fun y => φ y * χr y))
        + ((fun y => χi z * ψ y) - (fun y => ψ y * χi y)) := by
    funext y; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hsplit, iteratedFDeriv_add hPcd hQcd, iteratedFDeriv_sub hP1 hP2, iteratedFDeriv_sub hQ1 hQ2]
  simp only [Pi.add_apply, Pi.sub_apply, add_apply, sub_apply]
  rw [Work.CR.Flat.Cauchy.iteratedFDeriv_mul_const_apply hφ z u,
    Work.CR.Flat.Cauchy.iteratedFDeriv_mul_const_apply hψ z u, mulCorr, mulCorr]
  ring

/-- **The correction in coordinates.**  The `k`-th derivative at `z` of `y ↦ fderiv v y (X - Y y)`
is minus the sum over the real coordinates of the two Leibniz corrections. -/
private lemma R_expand {n k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} (hA : ∀ m : ℕ, ContDiff ℝ m A)
    {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v) (u : Fin k → Cn n) (m : Fin n) (z : Cn n) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1) - A y (Pi.single m 1))) z u
    = - ∑ a : Fin n,
        (mulCorr k (fun y => fderiv ℝ v y (Pi.single a (1:ℂ)))
            (fun y => ((A y (Pi.single m 1)) a).re) u z
         + mulCorr k (fun y => fderiv ℝ v y (Pi.single a (Complex.I)))
            (fun y => ((A y (Pi.single m 1)) a).im) u z) := by
  let φ : Fin n → Cn n → ℂ := fun a y => fderiv ℝ v y (Pi.single a (1:ℂ))
  let ψ : Fin n → Cn n → ℂ := fun a y => fderiv ℝ v y (Pi.single a (Complex.I))
  let χr : Fin n → Cn n → ℂ := fun a y => (((A y (Pi.single m 1)) a).re : ℂ)
  let χi : Fin n → Cn n → ℂ := fun a y => (((A y (Pi.single m 1)) a).im : ℂ)
  have hfvk : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
  have hφcd : ∀ a, ContDiff ℝ k (φ a) := fun a => hfvk.clm_apply contDiff_const
  have hψcd : ∀ a, ContDiff ℝ k (ψ a) := fun a => hfvk.clm_apply contDiff_const
  have hχcd : ∀ a, ContDiff ℝ k (fun y => (A y (Pi.single m (1:ℂ))) a) := by
    intro a
    have hA0 : ContDiff ℝ k A := hA k
    fun_prop
  have hχrcd : ∀ a, ContDiff ℝ k (χr a) := by
    intro a
    have h2 : ContDiff ℝ k (fun z : ℂ => ((z.re : ℝ) : ℂ)) :=
      ContinuousLinearMap.contDiff (Complex.ofRealCLM.comp Complex.reCLM)
    exact ContDiff.comp h2 (hχcd a)
  have hχicd : ∀ a, ContDiff ℝ k (χi a) := by
    intro a
    have h2 : ContDiff ℝ k (fun z : ℂ => ((z.im : ℝ) : ℂ)) :=
      ContinuousLinearMap.contDiff (Complex.ofRealCLM.comp Complex.imCLM)
    exact ContDiff.comp h2 (hχcd a)
  have hGcd : ∀ a, ContDiff ℝ k
      (fun y => (χr a z - χr a y) * φ a y + (χi a z - χi a y) * ψ a y) := by
    intro a
    have h1 : ContDiff ℝ k (fun y => (χr a z - χr a y) * φ a y) :=
      (contDiff_const.sub (hχrcd a)).mul (hφcd a)
    have h2 : ContDiff ℝ k (fun y => (χi a z - χi a y) * ψ a y) :=
      (contDiff_const.sub (hχicd a)).mul (hψcd a)
    exact h1.add h2
  have hfun : (fun y => fderiv ℝ v y (A z (Pi.single m 1) - A y (Pi.single m 1)))
      = ∑ a : Fin n, fun y => (χr a z - χr a y) * φ a y + (χi a z - χi a y) * ψ a y := by
    funext y
    rw [fderiv_apply_expand (fderiv ℝ v y) (A z (Pi.single m 1) - A y (Pi.single m 1)),
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    simp only [φ, ψ, χr, χi, Pi.sub_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_sub]
  rw [hfun, iteratedFDeriv_sum_apply (fun a _ => (hGcd a).contDiffAt),
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact itFDeriv_pair_split u (hφcd a) (hψcd a) (hχrcd a) (hχicd a) z

private lemma contDiff_dbarCoord {n k : ℕ} {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v) (m : Fin n) :
    ContDiff ℝ k (fun z => Work.CR.Flat.dbarCoord m v z) := by
  have hfv : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
  have ha : ContDiff ℝ k (fun z => fderiv ℝ v z (Pi.single m (1:ℂ))) := hfv.clm_apply contDiff_const
  have hb : ContDiff ℝ k (fun z => fderiv ℝ v z (Pi.single m (Complex.I))) := hfv.clm_apply contDiff_const
  have hI : ContDiff ℝ k (fun z => Complex.I * fderiv ℝ v z (Pi.single m (Complex.I))) :=
    ContDiff.mul contDiff_const hb
  have hsum := (ha.add hI)
  have hfin : ContDiff ℝ k (fun z => (1/2 : ℂ) * (fderiv ℝ v z (Pi.single m (1:ℂ))
      + Complex.I * fderiv ℝ v z (Pi.single m (Complex.I)))) :=
    ContDiff.mul contDiff_const hsum
  simpa [Work.CR.Flat.dbarCoord] using hfin

private lemma contDiff_Lcoef {n k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ m A) {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v) (m : Fin n) :
    ContDiff ℝ k (fun z => Lcoef A v m z) := by
  have hfv : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
  have hc : ContDiff ℝ k (fun y => A y (Pi.single m (1:ℂ))) := (hA k).clm_apply contDiff_const
  have h1 : ContDiff ℝ k (fun y => fderiv ℝ v y (A y (Pi.single m (1:ℂ)))) := hfv.clm_apply hc
  have hfin : ContDiff ℝ k (fun y => (Complex.I/2) * fderiv ℝ v y (A y (Pi.single m (1:ℂ)))) :=
    ContDiff.mul contDiff_const h1
  simpa [Lcoef] using hfin

/-- `dbarCn (Jstd + A) v · e_m` is `C^k` when `v` is `C^{k+1}` and `A` is smooth. -/
private lemma contDiff_dbarCn_apply {n k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ m A) {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v) (m : Fin n) :
    ContDiff ℝ k (fun z => dbarCn (JstdCn n + A) v z (Pi.single m 1)) := by
  have hF : (fun z => dbarCn (JstdCn n + A) v z (Pi.single m 1))
      = fun z => Work.CR.Flat.dbarCoord m v z + Lcoef A v m z :=
    funext fun z => dbarCoef_lin A v m z
  rw [hF]
  exact (contDiff_dbarCoord (hv := hv) m).add (contDiff_Lcoef hA hv m)

/-- **The `∂̄`-derivative of the `k`-th derivative differs from the `k`-th derivative of `∂̄`
by `(i/2)` times the `k`-th derivative of the difference of the frozen and varying pairings.** -/
private lemma dbarCn_iteratedFDeriv_sub_eq {n k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ m A) {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v)
    (u : Fin k → Cn n) (m : Fin n) (z : Cn n) :
    dbarCn (JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1)
      - iteratedFDeriv ℝ k (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u
    = (Complex.I/2) * iteratedFDeriv ℝ k
        (fun y => fderiv ℝ v y (A z (Pi.single m 1) - A y (Pi.single m 1))) z u := by
  have h1 : dbarCn (JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1)
      = Work.CR.Flat.dbarCoord m (fun y => iteratedFDeriv ℝ k v y u) z
        + Lcoef A (fun y => iteratedFDeriv ℝ k v y u) m z :=
    dbarCoef_lin A (fun y => iteratedFDeriv ℝ k v y u) m z
  have h2 : Work.CR.Flat.dbarCoord m (fun y => iteratedFDeriv ℝ k v y u) z
      = iteratedFDeriv ℝ k (fun y => Work.CR.Flat.dbarCoord m v y) z u :=
    Work.CR.Flat.Cauchy.dbarCoord_iteratedFDeriv hv m u z
  have h3 : Lcoef A (fun y => iteratedFDeriv ℝ k v y u) m z
      = (Complex.I/2) * iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1))) z u := by
    rw [Lcoef]
    congr 1
    exact Work.CR.Flat.Cauchy.fderiv_iteratedFDeriv_comm k hv u (A z (Pi.single m 1)) z
  have hP : ContDiff ℝ k (fun y => fderiv ℝ v y (A y (Pi.single m 1))) := by
    have hfv : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
    exact hfv.clm_apply ((hA k).clm_apply contDiff_const)
  have hlc : Lcoef A v m = fun y => (Complex.I/2) * fderiv ℝ v y (A y (Pi.single m 1)) := by
    funext y; rw [Lcoef]
  have h4 : iteratedFDeriv ℝ k (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u
      = iteratedFDeriv ℝ k (fun y => Work.CR.Flat.dbarCoord m v y) z u
        + (Complex.I/2) * iteratedFDeriv ℝ k
            (fun y => fderiv ℝ v y (A y (Pi.single m 1))) z u := by
    have hF : (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1))
        = fun y => Work.CR.Flat.dbarCoord m v y + Lcoef A v m y :=
      funext fun y => dbarCoef_lin A v m y
    rw [hF, Work.CR.Flat.Cauchy.iteratedFDeriv_add_apply' (contDiff_dbarCoord (hv := hv) m)
          (contDiff_Lcoef hA hv m) z u, hlc,
        Work.CR.Flat.Cauchy.iteratedFDeriv_mul_const_apply hP z u]
  have hsub : iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1))) z u
      - iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A y (Pi.single m 1))) z u
      = iteratedFDeriv ℝ k
          (fun y => fderiv ℝ v y (A z (Pi.single m 1) - A y (Pi.single m 1))) z u := by
    have hfun : (fun y => fderiv ℝ v y (A z (Pi.single m 1) - A y (Pi.single m 1)))
        = (fun y => fderiv ℝ v y (A z (Pi.single m 1)))
          - (fun y => fderiv ℝ v y (A y (Pi.single m 1))) :=
      funext fun y => by rw [Pi.sub_apply, map_sub]
    have hP1 : ContDiff ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1))) := by
      have hfv : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
      exact hfv.clm_apply contDiff_const
    rw [hfun, iteratedFDeriv_sub_apply hP1.contDiffAt hP.contDiffAt, sub_apply]
  rw [h1, h2, h3, h4]
  rw [show (iteratedFDeriv ℝ k (fun y => Work.CR.Flat.dbarCoord m v y) z) u
        + (Complex.I/2) * (iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1))) z) u
        - ((iteratedFDeriv ℝ k (fun y => Work.CR.Flat.dbarCoord m v y) z) u
          + (Complex.I/2) * (iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A y (Pi.single m 1))) z) u)
      = (Complex.I/2) * ((iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A z (Pi.single m 1))) z) u
          - (iteratedFDeriv ℝ k (fun y => fderiv ℝ v y (A y (Pi.single m 1))) z) u) from by ring,
      hsub]

/-- **The commutation defect.** -/
private lemma dbarCn_iteratedFDeriv_diff_eq {n k : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ m : ℕ, ContDiff ℝ m A) {v : Cn n → ℂ} (hv : ContDiff ℝ (k+1) v)
    (u : Fin k → Cn n) (m : Fin n) (z : Cn n) :
    dbarCn (JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1)
      - iteratedFDeriv ℝ k (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u
    = (Complex.I/2) * (- ∑ a : Fin n,
        (mulCorr k (fun y => fderiv ℝ v y (Pi.single a (1:ℂ)))
            (fun y => ((A y (Pi.single m 1)) a).re) u z
         + mulCorr k (fun y => fderiv ℝ v y (Pi.single a (Complex.I)))
            (fun y => ((A y (Pi.single m 1)) a).im) u z)) := by
  rw [dbarCn_iteratedFDeriv_sub_eq hA hv u m z]
  congr 1
  exact R_expand hA hv u m z

/-- Compact support of a finite sum of compactly supported functions. -/
private lemma hasCompactSupport_finsetSum {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β]
    {s : Finset ι} {f : ι → α → β} (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [show (fun x => ∑ i ∈ (∅ : Finset ι), f i x) = (0 : α → β) from by funext x; simp]
    exact HasCompactSupport.zero
  | insert a t ha ih =>
    rw [show (fun x => ∑ i ∈ insert a t, f i x)
        = (fun x => f a x + ∑ i ∈ t, f i x) from by funext x; rw [Finset.sum_insert ha]]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem dbarCn_iteratedFDeriv_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) (k : ℕ) {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)} (hA : ∀ m : ℕ, ContDiff ℝ m A) (hAfin : ∀ m : ℕ, ∀ i j : Fin n, Work.CR.Flat.holderNorm m α (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ) < ⊤) {v : (Fin n → ℂ) → ℂ} (hv : ContDiff ℝ (((k+1 : ℕ)) : WithTop ENat) v) (hcs : HasCompactSupport v) (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) (hg : ∀ m : Fin n, Work.CR.Flat.holderNorm k α (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z (Pi.single m 1)) (Work.CR.Flat.polydisc 0 ρ') < ⊤) : ∀ (u : Fin k → (Fin n → ℂ)) (m : Fin n), Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1)) Set.univ < ⊤ := by
  intro u m
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by exact_mod_cast (show 1 ≤ k+1 by omega))
  -- `fderiv v` vanishes on the closed exterior of the polydisc
  have hdv0 : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → fderiv ℝ v z = 0 := by
    intro z hz
    have h1 : iteratedFDeriv ℝ 1 v z = 0 :=
      iteratedFDeriv_eq_zero_of_vanishing_closedComplement hρ'0 hv1 hvan 1 le_rfl z hz
    ext w
    rw [← iteratedFDeriv_one_apply (𝕜 := ℝ) (f := v) (x := z) (m := fun _ : Fin 1 => w)]
    rw [h1]; rfl
  -- the `∂̄` of `v` vanishes on the closed exterior
  have hFvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) →
      dbarCn (JstdCn n + A) v z (Pi.single m 1) = 0 := by
    intro z hz
    have h0 := hdv0 z hz
    rw [dbarCoef_lin A v m z]
    simp [Work.CR.Flat.dbarCoord, Lcoef, h0]
  have hFcd : ContDiff ℝ k (fun z => dbarCn (JstdCn n + A) v z (Pi.single m 1)) :=
    contDiff_dbarCn_apply hA hv m
  have hFfin : Work.CR.Flat.holderNorm k α
      (fun z => dbarCn (JstdCn n + A) v z (Pi.single m 1)) Set.univ < ⊤ :=
    lt_of_le_of_lt
      (holderNorm_univ_le_holderNorm_polydisc_of_contDiff_vanishing hα0 hρ'0 hFcd hFvan)
      (hg m)
  have hg1 : Work.CR.Flat.holderNorm 0 α (fun z =>
      iteratedFDeriv ℝ k (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u) Set.univ < ⊤ :=
    lt_of_le_of_lt
      (Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le (le_refl k) u)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin)
  -- the correction
  let Corr : Cn n → ℂ := fun z => (Complex.I/2) * (- ∑ a : Fin n,
      (mulCorr k (fun y => fderiv ℝ v y (Pi.single a (1:ℂ)))
          (fun y => ((A y (Pi.single m 1)) a).re) u z
       + mulCorr k (fun y => fderiv ℝ v y (Pi.single a (Complex.I)))
          (fun y => ((A y (Pi.single m 1)) a).im) u z))
  have hφcd : ∀ a : Fin n, ContDiff ℝ k (fun y => fderiv ℝ v y (Pi.single a (1:ℂ))) := by
    intro a
    have hfvk : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
    exact hfvk.clm_apply contDiff_const
  have hψcd : ∀ a : Fin n, ContDiff ℝ k (fun y => fderiv ℝ v y (Pi.single a (Complex.I))) := by
    intro a
    have hfvk : ContDiff ℝ k (fderiv ℝ v) := hv.fderiv_right (m := k) le_rfl
    exact hfvk.clm_apply contDiff_const
  have hχrcd : ∀ a : Fin n, ContDiff ℝ (k+1) (fun y => (((A y (Pi.single m 1)) a).re : ℂ)) := by
    intro a
    have h1 : ContDiff ℝ (k+1) (fun y => (A y (Pi.single m (1:ℂ))) a) := by
      have hA0 : ContDiff ℝ (k+1) A := hA (k+1)
      fun_prop
    have h2 : ContDiff ℝ (k+1) (fun z : ℂ => ((z.re : ℝ) : ℂ)) :=
      ContinuousLinearMap.contDiff (Complex.ofRealCLM.comp Complex.reCLM)
    exact ContDiff.comp h2 h1
  have hχicd : ∀ a : Fin n, ContDiff ℝ (k+1) (fun y => (((A y (Pi.single m 1)) a).im : ℂ)) := by
    intro a
    have h1 : ContDiff ℝ (k+1) (fun y => (A y (Pi.single m (1:ℂ))) a) := by
      have hA0 : ContDiff ℝ (k+1) A := hA (k+1)
      fun_prop
    have h2 : ContDiff ℝ (k+1) (fun z : ℂ => ((z.im : ℝ) : ℂ)) :=
      ContinuousLinearMap.contDiff (Complex.ofRealCLM.comp Complex.imCLM)
    exact ContDiff.comp h2 h1
  have hCorr_cd : ContDiff ℝ 1 Corr := by
    have hsum : ContDiff ℝ 1 (fun z => ∑ a : Fin n,
        (mulCorr k (fun y => fderiv ℝ v y (Pi.single a (1:ℂ)))
            (fun y => ((A y (Pi.single m 1)) a).re) u z
         + mulCorr k (fun y => fderiv ℝ v y (Pi.single a (Complex.I)))
            (fun y => ((A y (Pi.single m 1)) a).im) u z)) :=
      ContDiff.sum fun a _ =>
        (mulCorr_contDiff k 0 (hφcd a) (hχrcd a) u).add
          (mulCorr_contDiff k 0 (hψcd a) (hχicd a) u)
    exact ContDiff.mul contDiff_const hsum.neg
  have hφcs : ∀ a : Fin n, HasCompactSupport (fun y => fderiv ℝ v y (Pi.single a (1:ℂ))) := by
    intro a
    refine hcs.mono' fun z hz => ?_
    by_contra hzt
    exact hz (by
      have h0 : v =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
      have h1 : fderiv ℝ v z = 0 := by rw [h0.fderiv_eq]; simp
      simp only [h1, ContinuousLinearMap.zero_apply])
  have hψcs : ∀ a : Fin n, HasCompactSupport (fun y => fderiv ℝ v y (Pi.single a (Complex.I))) := by
    intro a
    refine hcs.mono' fun z hz => ?_
    by_contra hzt
    exact hz (by
      have h0 : v =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hzt
      have h1 : fderiv ℝ v z = 0 := by rw [h0.fderiv_eq]; simp
      simp only [h1, ContinuousLinearMap.zero_apply])
  have hCorr_cs : HasCompactSupport Corr := by
    refine HasCompactSupport.mul_left ?_
    refine HasCompactSupport.neg ?_
    refine hasCompactSupport_finsetSum fun a _ => ?_
    exact (mulCorr_hasCompactSupport (hφcs a) u).add (mulCorr_hasCompactSupport (hψcs a) u)
  have hCorr_fin : Work.CR.Flat.holderNorm 0 α Corr Set.univ < ⊤ :=
    holderNorm_zero_univ_lt_top_of_contDiff_one hα0 hα1 hCorr_cd hCorr_cs
  -- the decomposition
  have hdecomp : (fun z => dbarCn (JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1))
      = (fun z => iteratedFDeriv ℝ k
          (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u) + Corr := by
    funext z
    have h := dbarCn_iteratedFDeriv_diff_eq hA hv u m z
    rw [sub_eq_iff_eq_add] at h
    calc dbarCn (JstdCn n + A) (fun y => iteratedFDeriv ℝ k v y u) z (Pi.single m 1)
        = Corr z + iteratedFDeriv ℝ k
            (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u := h
      _ = iteratedFDeriv ℝ k
            (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u + Corr z := add_comm _ _
  rw [hdecomp]
  refine lt_of_le_of_lt
    (Work.CR.Flat.Holder.holderNorm_add_le ?_ (hCorr_cd.contDiffOn.of_le (by simp)) uniqueDiffOn_univ)
    (ENNReal.add_lt_top.mpr ⟨hg1, hCorr_fin⟩)
  have hcont : Continuous (fun z =>
      iteratedFDeriv ℝ k (fun y => dbarCn (JstdCn n + A) v y (Pi.single m 1)) z u) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Cn n) ℂ u).continuous.comp
      (hFcd.continuous_iteratedFDeriv (m := k) le_rfl)
  exact contDiffOn_univ.mpr (contDiff_zero.mpr hcont)

end Work.NN.Core
