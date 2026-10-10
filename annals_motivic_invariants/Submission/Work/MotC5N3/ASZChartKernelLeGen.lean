import Mathlib
import Submission.Work.MotC5N3.ASZChartSetupGen
import Submission.Work.MotAS.aeval_smul_of_homogeneous

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZChartKernelLeGen` — the kernel inclusion in the AS chart over a general `K`

The `RatFunc 𝕜 ↦ K` fork of `Submission/Work/MotAS/asChartHomogenisation.lean` and
`Submission/Work/MotAS/asChartKernelLe.lean`: the homogenisation `asChartHomogeniseA` and the
reduction `asChartKernelLe_of_aux_A` of the kernel inclusion to the two inputs
`hKAE` (the transported Klein kernel statement, carried by `kerAevalKleinPASGen`) and `hHom`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- **Homogenisation in the AS chart.**  If `asChartPhiOmA D g` kills `f`, then `f` is congruent
modulo `X 0 - 1` to a homogeneous polynomial of the same total degree which is killed by the
*unnormalised* evaluation `aeval (asTwY D g)`. -/
theorem asChartHomogeniseA (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) :
    ∀ f : MvPolynomial (Fin 5) K, asChartPhiOmA D g f = 0 →
      ∃ F : MvPolynomial (Fin 5) K,
        F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) K f.totalDegree ∧
        MvPolynomial.aeval (asTwY D g) F = 0 ∧
        F - f ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
          Set (MvPolynomial (Fin 5) K)) := by
  intro f hf
  classical
  set d : ℕ := f.totalDegree with hd
  have hdeg : ∀ m ∈ f.support, m.degree ≤ d := by
    intro m hm
    rw [hd, Finsupp.degree_apply]
    exact MvPolynomial.le_totalDegree hm
  set F : MvPolynomial (Fin 5) K :=
    ∑ m ∈ f.support, MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
    with hF
  have hFhom : F.IsHomogeneous d := by
    rw [hF]
    refine MvPolynomial.IsHomogeneous.sum _ _ d (fun m hm => ?_)
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [map_add, Finsupp.degree_single]
    have := hdeg m hm; omega
  have hXk : ∀ k : ℕ,
      (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ k - 1
        ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
            Set (MvPolynomial (Fin 5) K)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h : (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ (k+1) - 1
          = MvPolynomial.X (0 : Fin 5) *
              ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ k - 1)
            + (MvPolynomial.X (0 : Fin 5) - 1) := by ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.subset_span (by simp))
  have hsub : F - f ∈ Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
      Set (MvPolynomial (Fin 5) K)) := by
    have hkey : F - f = ∑ m ∈ f.support,
        (MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
         - MvPolynomial.monomial m (f.coeff m)) := by
      rw [Finset.sum_sub_distrib, ← hF, ← MvPolynomial.as_sum f]
    rw [hkey]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    have hmon : MvPolynomial.monomial (m + Finsupp.single 0 (d - m.degree)) (f.coeff m)
        = MvPolynomial.monomial m (f.coeff m) *
          (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ (d - m.degree) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial]
      simp
    rw [hmon]
    have h2 : MvPolynomial.monomial m (f.coeff m) *
          (MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ (d - m.degree)
        - MvPolynomial.monomial m (f.coeff m)
        = MvPolynomial.monomial m (f.coeff m) *
          ((MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ (d - m.degree)
            - 1) := by ring
    rw [h2]
    exact Ideal.mul_mem_left _ _ (hXk (d - m.degree))
  refine ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hFhom, ?_, hsub⟩
  have h0 : asTwY D g 0 ≠ 0 := asTwY_zero_ne_zero D g hD.1
  have hsubker : asChartPhiOmA D g (F - f) = 0 := by
    have hle : Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
        Set (MvPolynomial (Fin 5) K))
        ≤ RingHom.ker (asChartPhiOmA D g).toRingHom := by
      rw [Ideal.span_le]
      rintro x rfl
      show asChartPhiOmA D g (MvPolynomial.X (0 : Fin 5) - 1) = 0
      rw [map_sub, map_one, asChartPhiOmA_X, div_self h0, sub_self]
    exact RingHom.mem_ker.mp (hle hsub)
  have hphiF : asChartPhiOmA D g F = 0 := by
    have hsplit : F = f + (F - f) := by ring
    rw [hsplit, map_add, hf, hsubker, add_zero]
  have hscale := Work.MotAS.aeval_smul_of_homogeneous (K := K) (R := OmA K D)
    hFhom ((asTwY D g 0)⁻¹) (asTwY D g)
  have hL : (fun i => (asTwY D g 0)⁻¹ * asTwY D g i)
      = (fun i => asTwY D g i / asTwY D g 0) := by
    funext i; rw [div_eq_mul_inv, mul_comm]
  rw [hL] at hscale
  have h2 : ((asTwY D g 0)⁻¹) ^ d * MvPolynomial.aeval (asTwY D g) F = 0 := by
    rw [← hscale]; exact hphiF
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero d (inv_ne_zero h0))

/-- **The ideal generated by the five transported (AS) Pfaffians.** -/
noncomputable def asPFIdeal'A (a b g : K) : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span (Set.range (Work.MotAS.kleinPASm a b g))

theorem asPFIdeal'A_le_asQideal (a b g : K) : asPFIdeal'A (K := K) a b g
    ≤ Work.MotAS.asQideal a b g := by
  rw [asPFIdeal'A, Work.MotAS.asQideal]
  refine le_trans (Ideal.span_mono ?_) Ideal.le_radical
  rintro x ⟨k, rfl⟩
  exact ⟨k, rfl⟩

/-- **The kernel of the chart evaluation is contained in the chart ideal**, given the transported
Klein kernel statement `hKAE` and the homogenisation `hHom`. -/
theorem asChartKernelLe_of_aux_A (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hKAE : ∀ (n : ℕ) (F : MvPolynomial (Fin 5) K),
      F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) K n →
      MvPolynomial.aeval (asTwY D g) F = 0 → F ∈ asPFIdeal'A (K := K) (aK K D) (bK K D) g)
    (hHom : ∀ f : MvPolynomial (Fin 5) K, asChartPhiOmA D g f = 0 →
      ∃ F : MvPolynomial (Fin 5) K,
        F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) K f.totalDegree ∧
          MvPolynomial.aeval (asTwY D g) F = 0 ∧
          F - f ∈ Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}) :
    RingHom.ker (asChartPhiA D g) ≤ Work.MotAS.asChartIdeal (aK K D) (bK K D) g := by
  intro f hf
  have hfom : asChartPhiOmA D g f = 0 := by
    have h1 : ((asChartPhiA D g f : ↥(twistFieldAS D g)) : OmA K D) = 0 := by
      rw [RingHom.mem_ker.mp hf]
      simp
    rwa [asChartPhiA_coe] at h1
  obtain ⟨F, hFhom, hFaeval, hFdiff⟩ := hHom f hfom
  have hFmem : F ∈ asPFIdeal'A (K := K) (aK K D) (bK K D) g := hKAE f.totalDegree F hFhom hFaeval
  have hsub : asPFIdeal'A (K := K) (aK K D) (bK K D) g
      ≤ Work.MotAS.asChartIdeal (aK K D) (bK K D) g :=
    le_trans (asPFIdeal'A_le_asQideal (aK K D) (bK K D) g) le_sup_left
  have hspan : (Ideal.span {MvPolynomial.X (0 : Fin 5) - 1} :
      Ideal (MvPolynomial (Fin 5) K)) ≤ Work.MotAS.asChartIdeal (aK K D) (bK K D) g :=
    le_sup_right
  have : f = F - (F - f) := by ring
  rw [this]
  exact Ideal.sub_mem _ (hsub hFmem) (hspan hFdiff)

end Work.MotC5N3
