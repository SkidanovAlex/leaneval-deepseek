import Mathlib
import Submission.Work.MotAS.Ker6.Lower
import Submission.Work.MotAS.Ker4.asKleinIdeal4_finrank_ge
import Submission.Work.MotAS.Ker4.asTransportP_mv
import Submission.Work.MotAS.Ker4.kleinPASm_isHomogeneous

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The degree-6 part of the AS Pfaffian ideal has dimension at least 180

`Work.MotAS.asIdeal6 (Kb 𝕜) a b g` is the `Kb 𝕜`-span of the products
`kleinPAS a b g (X ·) k * monomial m 1` with `m` of degree `4`.  We show that its `Kb 𝕜`-dimension
is at least `180`, by transporting the *split* bound `Work.MotAS.Ker6.twIdealSixLower` (which gives
`180 ≤ finrank (kleinIdeal6 (Kb 𝕜) a b)`) along the Galois-coordinate substitution
`X i ↦ Σ_j (asM w)_{ij} X_j` (`w = asRoot g`), exactly as in degree `4`
(`Submission/Work/MotAS/Ker4/asKleinIdeal4_finrank_ge.lean`).

The substitution is a `Kb 𝕜`-algebra automorphism of `MvPolynomial (Fin 5) (Kb 𝕜)` (its inverse
is the substitution with matrix `asMinv w`, since `asM w * asMinv w = 1`), it sends the split
Pfaffians `kleinP k` to `Σ_j (asN w)_{kj} kleinPASm j`
(`Work.MotAS.Ker4.asTransportP_mv`), and it sends degree-`4` monomials to degree-`4` *homogeneous*
polynomials, which are spanned by the degree-`4` monomials.  Hence it maps `kleinIdeal6` into
`asIdeal6`, and the dimension bound follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotAS.Ker6

open MvPolynomial

noncomputable section

/-- The `Kb 𝕜`-submodule `asIdeal6` of the target statement, with the Klein data `D` and the twist
`g : RatFunc 𝕜` substituted in. -/
abbrev asIdeal6K (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (g : RatFunc 𝕜) : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
  Work.MotAS.asIdeal6 (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
    (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)

/-- The `Kb 𝕜`-span of the degree-4 monomials, indexed by the degree-4 exponent vectors. -/
def deg4Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
  Submodule.span (Work.MotV.Kb 𝕜)
    (Set.range (fun m : {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
      MvPolynomial.monomial m.1 1))

/-- Homogeneous degree-4 polynomials in 5 variables are spanned by the degree-4 monomials. -/
theorem homogeneous_four_le_deg4Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) 4 ≤ deg4Mons 𝕜 := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single]
  rw [Submodule.span_le]
  rintro x ⟨d, hd, rfl⟩
  change AddMonoidAlgebra.single d 1 ∈ deg4Mons 𝕜
  rw [MvPolynomial.single_eq_monomial]
  refine Submodule.subset_span ⟨⟨d, ?_⟩, rfl⟩
  exact (Finsupp.degree_apply d).symm.trans hd

/-- The Galois-coordinate substitution sends a degree-4 monomial to a homogeneous degree-4
polynomial. -/
theorem aeval_asM_monomial_isHomogeneous (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (w : Work.MotV.Kb 𝕜) (m : Fin 5 →₀ ℕ) (hm : m.support.sum m = 4) :
    (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
      MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
      (MvPolynomial.monomial m (1 : Work.MotV.Kb 𝕜))).IsHomogeneous 4 := by
  have hΦhom : ∀ i : Fin 5,
      (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j).IsHomogeneous 1 := by
    intro i
    exact IsHomogeneous.sum Finset.univ (fun j : Fin 5 =>
      MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) 1
      (fun j _ => (isHomogeneous_X (R := Work.MotV.Kb 𝕜) j).C_mul _)
  have hmon : (MvPolynomial.monomial m (1 : Work.MotV.Kb 𝕜)).IsHomogeneous 4 := by
    apply isHomogeneous_monomial
    rw [Finsupp.degree_apply]
    exact hm
  exact hmon.aeval (fun i : Fin 5 =>
    ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) hΦhom

/-- The subtype of degree-4 exponent vectors is finite. -/
theorem finite_finsupp_deg4 : Finite {m : Fin 5 →₀ ℕ // m.support.sum m = 4} := by
  have hbound : ∀ (m : {m : Fin 5 →₀ ℕ // m.support.sum m = 4}) (i : Fin 5), m.1 i < 5 := by
    intro m i
    have hle : m.1 i ≤ m.1.support.sum m.1 := by
      by_cases hi : i ∈ m.1.support
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
      · rw [Finsupp.mem_support_iff] at hi
        simp [not_not.mp hi]
    have := m.2
    omega
  refine Finite.of_injective (fun m => fun i => (⟨m.1 i, hbound m i⟩ : Fin 5)) ?_
  intro m m' h
  apply Subtype.ext
  exact Finsupp.ext (fun i => Fin.ext_iff.mp (congrFun h i))

/-- An AS Pfaffian times an element of `deg4Mons 𝕜` lies in `asIdeal6K 𝕜 D g`. -/
theorem kleinPASm_mul_mem_deg4Mons (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5)
    {f : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)} (hf : f ∈ deg4Mons 𝕜) :
    Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) j * f ∈ asIdeal6K 𝕜 D g := by
  rw [deg4Mons] at hf
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

/-- The Galois-coordinate substitution `X i ↦ Σ_j (asM w)_{ij} X_j` is injective, with left
inverse the substitution with matrix `asMinv w`. -/
theorem aeval_asM_injective (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (w : Work.MotV.Kb 𝕜) :
    Function.Injective (fun p : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) =>
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j) p
        : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))) := by
  intro x y hxy
  have h2 := congrArg (fun z : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) =>
    (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
      MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j) z
      : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))) hxy
  rw [Work.MotAS.Ker4.aeval_asMinv_aeval_asM 𝕜 w x,
      Work.MotAS.Ker4.aeval_asMinv_aeval_asM 𝕜 w y] at h2
  exact h2

theorem asIdeal6_finrank_ge (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (g : RatFunc 𝕜) (hab : D.a * D.b ≠ 0) :
    180 ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(Work.MotAS.asIdeal6 (Work.MotV.Kb 𝕜)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
      (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)) := by
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
  have hsplit := twIdealSixLower (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
    (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) ha hb
  haveI hfinS : Finite {m : Fin 5 →₀ ℕ // m.support.sum m = 4} := finite_finsupp_deg4
  haveI hfin : Module.Finite (Work.MotV.Kb 𝕜) ↥(asIdeal6K 𝕜 D g) := by
    rw [asIdeal6K, Work.MotAS.asIdeal6]
    exact Module.Finite.span_of_finite (Work.MotV.Kb 𝕜) (Set.finite_range _)
  have hcontain : ∀ x ∈ kleinIdeal6 (Work.MotV.Kb 𝕜)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b),
      MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) x
        ∈ asIdeal6K 𝕜 D g := by
    intro x hx
    rw [kleinIdeal6] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨q, rfl⟩
      rw [map_mul, Work.MotAS.Ker4.asTransportP_mv 𝕜 D g q.1, Finset.sum_mul]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul]
      refine Submodule.smul_mem _ _ ?_
      exact kleinPASm_mul_mem_deg4Mons 𝕜 D g j
        (homogeneous_four_le_deg4Mons 𝕜 ((MvPolynomial.mem_homogeneousSubmodule 4 _).mpr
          (aeval_asM_monomial_isHomogeneous 𝕜 (Work.MotV5.asRoot g) q.2.1 q.2.2)))
    · rw [map_zero]
      exact Submodule.zero_mem _
    · rintro y z _ _ ihy ihz
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
    · rintro a y _ ihy
      rw [map_smul]
      exact Submodule.smul_mem _ a ihy
  have hinj := aeval_asM_injective 𝕜 (Work.MotV5.asRoot g)
  have hle : Module.finrank (Work.MotV.Kb 𝕜) ↥(kleinIdeal6 (Work.MotV.Kb 𝕜)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
      ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(asIdeal6K 𝕜 D g) := by
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

end Work.MotAS.Ker6
