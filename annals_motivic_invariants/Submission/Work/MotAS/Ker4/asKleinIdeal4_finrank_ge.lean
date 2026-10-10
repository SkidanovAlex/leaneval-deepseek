import Mathlib
import Submission.Work.MotAS.Ker4.ASDefs
import Submission.Work.MotAS.Ker4.Defs
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.Ker4.twIdealFourLower
import Submission.Work.MotAS.Ker4.asTransportP_mv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The degree-4 part of the AS Pfaffian ideal has dimension at least 50

`Work.MotAS.Ker4.kleinIdeal4AS 𝕜 D g` is the `Kb 𝕜`-span of the `75 = 5 × 15` products
`kleinPASm a b g k * monomial m 1` with `m` of degree `2`.  We show that its `Kb 𝕜`-dimension is at
least `50`, by transporting the *split* bound `Work.MotAS.Ker4.twIdealFourLower` (which gives
`50 ≤ finrank (kleinIdeal4 (Kb 𝕜) a b)`) along the Galois-coordinate substitution
`X i ↦ Σ_j (asM w)_{ij} X_j` (`w = asRoot g`).

The substitution is a `Kb 𝕜`-algebra automorphism of `MvPolynomial (Fin 5) (Kb 𝕜)` (its inverse is
the substitution with matrix `asMinv w`, since `asM w * asMinv w = 1`), it sends the split
Pfaffians `kleinP k` to `Σ_j (asN w)_{kj} kleinPASm j`
(`Work.MotAS.Ker4.asTransportP_mv`), and it sends degree-2 monomials to degree-2 *homogeneous*
polynomials, which are spanned by the degree-2 monomials.  Hence it maps `kleinIdeal4` into
`kleinIdeal4AS`, and the dimension bound follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotAS.Ker4

open MvPolynomial

noncomputable section

/-- The `Kb 𝕜`-span of the degree-2 monomials, indexed by the degree-2 exponent vectors. -/
def deg2Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
  Submodule.span (Work.MotV.Kb 𝕜)
    (Set.range (fun m : {m : Fin 5 →₀ ℕ // m.support.sum m = 2} =>
      MvPolynomial.monomial m.1 1))

/-- Homogeneous degree-2 polynomials in 5 variables are spanned by the degree-2 monomials. -/
theorem homogeneous_two_le_deg2Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) 2 ≤ deg2Mons 𝕜 := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single]
  rw [Submodule.span_le]
  rintro x ⟨d, hd, rfl⟩
  change AddMonoidAlgebra.single d 1 ∈ deg2Mons 𝕜
  rw [MvPolynomial.single_eq_monomial]
  refine Submodule.subset_span ⟨⟨d, ?_⟩, rfl⟩
  exact (Finsupp.degree_apply d).symm.trans hd

/-- The Galois-coordinate substitution sends a degree-2 monomial to a homogeneous degree-2
polynomial. -/
theorem aeval_asM_monomial_isHomogeneous (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (w : Work.MotV.Kb 𝕜) (m : Fin 5 →₀ ℕ) (hm : m.support.sum m = 2) :
    (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
      MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
      (MvPolynomial.monomial m (1 : Work.MotV.Kb 𝕜))).IsHomogeneous 2 := by
  have hΦhom : ∀ i : Fin 5,
      (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j).IsHomogeneous 1 := by
    intro i
    exact IsHomogeneous.sum Finset.univ (fun j : Fin 5 =>
      MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) 1
      (fun j _ => (isHomogeneous_X (R := Work.MotV.Kb 𝕜) j).C_mul _)
  have hmon : (MvPolynomial.monomial m (1 : Work.MotV.Kb 𝕜)).IsHomogeneous 2 := by
    apply isHomogeneous_monomial
    rw [Finsupp.degree_apply]
    exact hm
  exact hmon.aeval (fun i : Fin 5 =>
    ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) hΦhom

/-- An AS Pfaffian times an element of `deg2Mons 𝕜` lies in `kleinIdeal4AS 𝕜 D g`. -/
theorem kleinPASm_mul_mem_deg2Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5)
    {f : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)} (hf : f ∈ deg2Mons 𝕜) :
    Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) j * f ∈ kleinIdeal4AS 𝕜 D g := by
  rw [deg2Mons] at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro x ⟨m, rfl⟩
    exact Submodule.subset_span ⟨(j, m), rfl⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · rintro x y _ _ ihx ihy
    rw [mul_add]
    exact Submodule.add_mem _ ihx ihy
  · rintro a x _ ih
    rw [MvPolynomial.smul_eq_C_mul, mul_left_comm, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ a ih

/-- The AS substitution with matrix `asMinv w` is a left inverse of the AS substitution with
matrix `asM w`. -/
theorem aeval_asMinv_aeval_asM (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (w : Work.MotV.Kb 𝕜)
    (p : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :
    MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j)
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) p) = p := by
  have h5 : (5 : Work.MotV.Kb 𝕜) = 0 := CharP.cast_eq_zero (Work.MotV.Kb 𝕜) 5
  have hcomp : (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j)).comp
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j))
      = AlgHom.id (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    have hterm : ∀ x : Fin 5, MvPolynomial.C (Work.MotAS.asM w i x) *
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w x j) * MvPolynomial.X j)
        = ∑ j : Fin 5,
            MvPolynomial.C (Work.MotAS.asM w i x * Work.MotAS.asMinv w x j) * MvPolynomial.X j := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, ← map_mul]
    rw [show MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
          MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j)
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
        = ∑ x : Fin 5, MvPolynomial.C (Work.MotAS.asM w i x) *
            (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w x j) * MvPolynomial.X j) from ?_]
    · rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_comm]
      have hj : ∀ j : Fin 5, (∑ x : Fin 5,
            MvPolynomial.C (Work.MotAS.asM w i x * Work.MotAS.asMinv w x j) * MvPolynomial.X j)
          = MvPolynomial.C ((Work.MotAS.asM w * Work.MotAS.asMinv w) i j) * MvPolynomial.X j := by
        intro j
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun j _ => hj j), Work.MotAS.asM_mul_asMinv h5 w]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, map_one, one_mul]
      · intro j _ hjne
        rw [Matrix.one_apply_ne (Ne.symm hjne), map_zero, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  exact congrArg (fun f => f p) hcomp

theorem asKleinIdeal4_finrank_ge (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (hab : D.a * D.b ≠ 0) :
    50 ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(Work.MotAS.Ker4.kleinIdeal4AS 𝕜 D g) := by
  have ha : algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a ≠ 0 := by
    intro h
    refine hab ?_
    apply RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜))
    rw [map_mul, map_zero, h, zero_mul]
  have hb : algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b ≠ 0 := by
    intro h
    refine hab ?_
    apply RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜))
    rw [map_mul, map_zero, h, mul_zero]
  have hsplit := twIdealFourLower (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
    (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) ha hb
  haveI hfinS : Finite {m : Fin 5 →₀ ℕ // m.support.sum m = 2} := finite_finsupp_deg2
  haveI hfin : Module.Finite (Work.MotV.Kb 𝕜) ↥(kleinIdeal4AS 𝕜 D g) := by
    rw [kleinIdeal4AS]
    exact Module.Finite.span_of_finite (Work.MotV.Kb 𝕜) (Set.finite_range _)
  have hcontain : ∀ x ∈ Work.MotAS.Ker4.kleinIdeal4 (Work.MotV.Kb 𝕜)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b),
      MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) x
        ∈ kleinIdeal4AS 𝕜 D g := by
    intro x hx
    rw [kleinIdeal4] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨q, rfl⟩
      rw [map_mul, asTransportP_mv 𝕜 D g q.1, Finset.sum_mul]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul]
      refine Submodule.smul_mem _ _ ?_
      exact kleinPASm_mul_mem_deg2Mons 𝕜 D g j
        (homogeneous_two_le_deg2Mons 𝕜 ((MvPolynomial.mem_homogeneousSubmodule 2 _).mpr
          (aeval_asM_monomial_isHomogeneous 𝕜 (Work.MotV5.asRoot g) q.2.1 q.2.2)))
    · rw [map_zero]
      exact Submodule.zero_mem _
    · rintro y z _ _ ihy ihz
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
    · rintro a y _ ihy
      rw [map_smul]
      exact Submodule.smul_mem _ a ihy
  have hinj : Function.Injective (fun p : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) =>
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) p
        : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))) := by
    intro x y hxy
    have h2 := congrArg (fun z : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) =>
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) z
        : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))) hxy
    rw [aeval_asMinv_aeval_asM 𝕜 (Work.MotV5.asRoot g) x,
        aeval_asMinv_aeval_asM 𝕜 (Work.MotV5.asRoot g) y] at h2
    exact h2
  have hle : Module.finrank (Work.MotV.Kb 𝕜) ↥(Work.MotAS.Ker4.kleinIdeal4 (Work.MotV.Kb 𝕜)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
      ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(kleinIdeal4AS 𝕜 D g) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := ((MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) :
          MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜]
            MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)).toLinearMap).restrict hcontain) ?_
    intro x y hxy
    apply Subtype.ext
    apply hinj
    have h2 := congrArg Subtype.val hxy
    simpa using h2
  exact le_trans hsplit hle

end

end Work.MotAS.Ker4
