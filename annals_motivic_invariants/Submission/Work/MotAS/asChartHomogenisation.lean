import Mathlib
import Submission.Work.MotAS.ASZChartSetup
import Submission.Work.MotAS.aeval_smul_of_homogeneous

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asChartHomogenise` — homogenisation in the chart of the AS twisted Klein curve

This is the *homogenisation* input `hHom` of `Work.MotAS.ker_le_of_aux`
(`Submission/Work/MotAS/asChartIdeal_isPrime.lean`), proved here so that the chart presentation
`Work.MotAS.ASZChartPresentation` can be obtained from
`Work.MotAS.asChartKernelLe_of_prime`'s alternative route (`asChartPresentation_of_ker`
only needs `RingHom.ker (asChartPhi D g) ≤ asChartIdeal a b g`) without the height bound on
`asChartIdeal`.

Given `f : MvPolynomial (Fin 5) K` with `asChartPhiOm D g f = 0`, we build its homogenisation
`F := ∑ m ∈ f.support, monomial (m + single 0 (d - m.degree)) (f.coeff m)` of degree
`d = f.totalDegree` (adjoin the missing powers of `X 0`), for which

* `F` is homogeneous of degree `d`;
* `F - f ∈ Ideal.span {X 0 - 1}` (substituting `X 0 = 1` in `F` gives `f` back), and
* `aeval (asTwY D g) F = 0`: since `F` is homogeneous of degree `d`,
  `aeval ((asTwY D g 0)⁻¹ • asTwY D g) F = ((asTwY D g 0)⁻¹)^d · aeval (asTwY D g) F`
  (`Work.MotAS.aeval_smul_of_homogeneous`), the left-hand side is `asChartPhiOm D g F`, and
  `asChartPhiOm` kills `F - f` (it kills `X 0 - 1` because `asTwY D g 0 ≠ 0`,
  `Work.MotAS.asTwY_zero_ne_zero`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- **Homogenisation in the AS chart.**  If `asChartPhiOm D g` kills `f`, then `f` is congruent
modulo `X 0 - 1` to a homogeneous polynomial of the same total degree which is killed by the
*unnormalised* evaluation `aeval (asTwY D g)`. -/
theorem asChartHomogenise (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : RatFunc 𝕜) :
    ∀ f : MvPolynomial (Fin 5) (RatFunc 𝕜), asChartPhiOm D g f = 0 →
      ∃ F : MvPolynomial (Fin 5) (RatFunc 𝕜),
        F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (RatFunc 𝕜) f.totalDegree ∧
        MvPolynomial.aeval (asTwY D g) F = 0 ∧
        F - f ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
          Set (MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
  intro f hf
  classical
  set d : ℕ := f.totalDegree with hd
  have hdeg : ∀ m ∈ f.support, m.degree ≤ d := by
    intro m hm
    rw [hd, Finsupp.degree_apply]
    exact MvPolynomial.le_totalDegree hm
  set F : MvPolynomial (Fin 5) (RatFunc 𝕜) :=
    ∑ m ∈ f.support, MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
    with hF
  have hFhom : F.IsHomogeneous d := by
    rw [hF]
    refine MvPolynomial.IsHomogeneous.sum _ _ d (fun m hm => ?_)
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [map_add, Finsupp.degree_single]
    have := hdeg m hm; omega
  have hXk : ∀ k : ℕ,
      (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ k - 1
        ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
            Set (MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h : (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ (k+1) - 1
          = MvPolynomial.X (0 : Fin 5) *
              ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ k - 1)
            + (MvPolynomial.X (0 : Fin 5) - 1) := by ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.subset_span (by simp))
  have hsub : F - f ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
      Set (MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    have hkey : F - f = ∑ m ∈ f.support,
        (MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
         - MvPolynomial.monomial m (f.coeff m)) := by
      rw [Finset.sum_sub_distrib, ← hF, ← MvPolynomial.as_sum f]
    rw [hkey]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    have hmon : MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
        = MvPolynomial.monomial m (f.coeff m) *
          (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ (d - m.degree) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial]
      simp
    rw [hmon]
    have h2 : MvPolynomial.monomial m (f.coeff m) *
          (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ (d - m.degree)
        - MvPolynomial.monomial m (f.coeff m)
        = MvPolynomial.monomial m (f.coeff m) *
          ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) ^ (d - m.degree)
            - 1) := by ring
    rw [h2]
    exact Ideal.mul_mem_left _ _ (hXk (d - m.degree))
  refine ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hFhom, ?_, hsub⟩
  have h0 : asTwY D g 0 ≠ 0 := asTwY_zero_ne_zero D g hD.1
  have hsubker : asChartPhiOm D g (F - f) = 0 := by
    have hle : Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
        Set (MvPolynomial (Fin 5) (RatFunc 𝕜)))
        ≤ RingHom.ker (asChartPhiOm D g).toRingHom := by
      rw [Ideal.span_le]
      rintro x rfl
      show asChartPhiOm D g (MvPolynomial.X (0 : Fin 5) - 1) = 0
      rw [map_sub, map_one, asChartPhiOm_X, div_self h0, sub_self]
    exact RingHom.mem_ker.mp (hle hsub)
  have hphiF : asChartPhiOm D g F = 0 := by
    have hsplit : F = f + (F - f) := by ring
    rw [hsplit, map_add, hf, hsubker, add_zero]
  have hscale := aeval_smul_of_homogeneous (K := RatFunc 𝕜) (R := Work.MotV.Om D)
    hFhom ((asTwY D g 0)⁻¹) (asTwY D g)
  have hL : (fun i => (asTwY D g 0)⁻¹ * asTwY D g i)
      = (fun i => asTwY D g i / asTwY D g 0) := by
    funext i; rw [div_eq_mul_inv, mul_comm]
  rw [hL] at hscale
  have h2 : ((asTwY D g 0)⁻¹) ^ d * MvPolynomial.aeval (asTwY D g) F = 0 := by
    rw [← hscale]; exact hphiF
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero d (inv_ne_zero h0))

end Work.MotAS
