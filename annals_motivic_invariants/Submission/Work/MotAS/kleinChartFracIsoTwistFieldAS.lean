import Mathlib
import Submission.Work.MotAS.TwistField
import Submission.Work.MotV5.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.twistFieldAS_zero
import Submission.Work.MotAS.KleinKerASMain
import Submission.Work.MotAS.mem_span_mul_monomial_of_mem_ideal_span
import Submission.Work.MotV5.ASLocal.mem_span_of_map_mem_span
import Submission.Work.MotAS.aeval_smul_of_homogeneous
import Submission.Work.MotV.twCoord_eq
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotAS.kleinChartFracIsoTwistFieldAS` — the chart of the Klein curve is the trivial AS twist

This file proves `Work.MotAS.kleinChartFracIsoTwistFieldAS`: over `𝕜` of characteristic `5`, for
Klein data `D` satisfying `Work.MotV5.KleinData.ASGood`, the function field of the affine chart
`X 0 = 1` of the Klein quintic — i.e. the fraction field of
`RatFunc 𝕜[X₀,…,X₄] ⧸ (√(p₀,…,p₄) + (X₀ - 1))`, the five `p_k = kleinP a b ·` being the Klein
(Pfaffian) quadrics — is the Artin–Schreier twist field of the *trivial* class,
`↥(Work.MotAS.twistFieldAS D 0) = ↥(Work.MotV5.kleinField D)`.

## Route

This is the AS-transport-free ("split") version of `Work.MotAS.ASZChartPresentation_gen`.  Let
`K = RatFunc 𝕜`, `S = K[X₀,…,X₄]`, `J = √(p₀,…,p₄)`, `I = J + (X₀ - 1)`, and let
`Φ : S →ₐ[K] ↥(kleinField D)` be the chart evaluation `X i ↦ κ_i/κ_0` (`κ = kleinCoord D (Kb 𝕜)`,
`kleinField D = K(κ_i/κ_0) = K(C)`).  Then

* `I ≤ ker Φ` (the Pfaffians vanish on the κ's by `D.Good.klein_eq`, and `κ_0 ≠ 0` by
  `D.Good.coord0_ne`);
* `ker Φ ≤ I`: homogenise `f ∈ ker Φ` to a form `F` of the same total degree with
  `F - f ∈ (X₀ - 1)` and `aeval κ F = 0` (`splitHomogenise`, the analogue of
  `Work.MotAS.asChartHomogenise`), apply the *split* Klein kernel statement over `RatFunc 𝕜`
  (`kerAevalKleinP`, obtained from the proved `Work.MotAS.kleinKer_mem_v2` over `Kb 𝕜` by
  base change and descent along the graded pieces, as in `Work.MotAS.kerAevalKleinPAS_gen`),
  and split `f = F - (F - f)`.

Hence `ker Φ = I`, so `Φ` descends to an injective `K`-algebra map `S ⧸ I → ↥(kleinField D)`
extending to the fraction field, which is then bijective because the image contains the generators
`κ_i/κ_0`.  The statement follows, using `Work.MotAS.twistFieldAS_zero`
(`twistFieldAS D 0 = kleinField D`).
-/

set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## §0 `Fin 5` index normalisations (as in `Work.MotAS.asChartPhiOm_kleinPAS`) -/

private lemma fin5_zero_coe (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
private lemma fin5_one_coe (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
private lemma fin5_two_coe (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
private lemma fin5_three_coe (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
private lemma fin5_four_coe (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl

/-! ## §1 The split Klein chart ideal -/

/-- The five split Klein Pfaffians read in the affine coordinates `X 0, …, X 4`. -/
noncomputable def splitP (D : Work.MotV.KleinData 𝕜) : Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜) :=
  fun k => Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
    (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b)) (fun i => MvPolynomial.X i) k

/-- **The chart ideal** of the Klein curve in the chart `X 0 = 1`: the radical of the five Pfaffian
quadrics together with `X 0 - 1`. -/
noncomputable def splitChartIdeal (D : Work.MotV.KleinData 𝕜) :
    Ideal (MvPolynomial (Fin 5) (RatFunc 𝕜)) :=
  Ideal.radical (Ideal.span (Set.range (splitP D))) ⊔
    Ideal.span {MvPolynomial.X (0 : Fin 5) - 1}

/-! ## §2 The chart evaluation `X i ↦ κ_i / κ_0` -/

/-- The chart evaluation of the Klein curve, with values in the function field `Om D`. -/
noncomputable def splitPhiOm (D : Work.MotV.KleinData 𝕜) :
    MvPolynomial (Fin 5) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] Work.MotV.Om D :=
  MvPolynomial.aeval fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
    Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0

theorem splitPhiOm_X (D : Work.MotV.KleinData 𝕜) (i : Fin 5) :
    splitPhiOm D (MvPolynomial.X i) = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
      Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
  simp only [splitPhiOm, MvPolynomial.aeval_X]

/-- The Klein field, unfolded as an `adjoin` so that `IntermediateField.adjoin_induction`
applies without a transparency conversion. -/
noncomputable abbrev splitField (D : Work.MotV.KleinData 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜) (Set.range fun i =>
    Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)

theorem splitField_eq_kleinField (D : Work.MotV.KleinData 𝕜) :
    splitField D = Work.MotV5.kleinField D := rfl

theorem splitPhiOm_mem (D : Work.MotV.KleinData 𝕜) (x : MvPolynomial (Fin 5) (RatFunc 𝕜)) :
    splitPhiOm D x ∈ splitField D := by
  have hle : Algebra.adjoin (RatFunc 𝕜) (Set.range fun i =>
      Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      ≤ (splitField D).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Set.mem_range_self i)
  have hx : x ∈ Algebra.adjoin (RatFunc 𝕜)
      (Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    rw [MvPolynomial.adjoin_range_X]; exact Algebra.mem_top
  have himg : splitPhiOm D x ∈
      (Algebra.adjoin (RatFunc 𝕜) (Set.range (MvPolynomial.X :
        Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜)))).map (splitPhiOm D) := ⟨x, hx, rfl⟩
  rw [AlgHom.map_adjoin] at himg
  have hrange : (splitPhiOm D) ''
      Set.range (MvPolynomial.X : Fin 5 → MvPolynomial (Fin 5) (RatFunc 𝕜)) =
      Set.range (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
        Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (splitPhiOm_X D i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, splitPhiOm_X D i⟩
  rw [hrange] at himg
  exact hle himg

/-- The chart evaluation, valued in the Klein field. -/
noncomputable def splitPhi (D : Work.MotV.KleinData 𝕜) :
    MvPolynomial (Fin 5) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] ↥(splitField D) :=
  (splitPhiOm D).codRestrict (splitField D).toSubalgebra (splitPhiOm_mem D)

theorem splitPhi_coe (D : Work.MotV.KleinData 𝕜) (x : MvPolynomial (Fin 5) (RatFunc 𝕜)) :
    ((splitPhi D x : ↥(splitField D)) : Work.MotV.Om D) = splitPhiOm D x :=
  AlgHom.coe_codRestrict _ _ _ _

theorem splitPhi_X (D : Work.MotV.KleinData 𝕜) (i : Fin 5) :
    ((splitPhi D (MvPolynomial.X i) : ↥(splitField D)) : Work.MotV.Om D)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 := by
  rw [splitPhi_coe, splitPhiOm_X]

/-! ## §3 Polynomial naturality and homogeneity of the Pfaffians -/

/-- The five Pfaffians are polynomials with integer coefficients, so `aeval` commutes with them. -/
theorem aeval_kleinP {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (α β : K) (v : Fin 5 → A) (k : Fin 5) :
    MvPolynomial.aeval v (Work.MotK.kleinP (MvPolynomial.C α) (MvPolynomial.C β)
      (fun i : Fin 5 => MvPolynomial.X i) k)
      = Work.MotK.kleinP (algebraMap K A α) (algebraMap K A β) v k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, fin5_zero_coe, fin5_one_coe, fin5_two_coe,
      fin5_three_coe, fin5_four_coe, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_add, map_sub, map_mul,
      map_pow, map_neg]

/-- `MvPolynomial.map` commutes with the Pfaffians. -/
theorem map_kleinP {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R) (k : Fin 5) :
    MvPolynomial.map φ (Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) k)
      = Work.MotK.kleinP (MvPolynomial.C (φ a)) (MvPolynomial.C (φ b))
        (fun i : Fin 5 => MvPolynomial.X i) k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, fin5_zero_coe, fin5_one_coe, fin5_two_coe,
      fin5_three_coe, fin5_four_coe, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_neg, MvPolynomial.map_C,
      MvPolynomial.map_X]

private theorem kleinP0_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP0 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  rw [Work.MotK.kleinP0]
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add ?_ ?_) ?_
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_C (Fin 5) a).neg
      (MvPolynomial.isHomogeneous_C (Fin 5) b))
      (MvPolynomial.isHomogeneous_X_pow (R := K) 0 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) a).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 2))
      (MvPolynomial.isHomogeneous_X (R := K) 3)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) b).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 1))
      (MvPolynomial.isHomogeneous_X (R := K) 4)) using 1

private theorem kleinP1_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP1 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  rw [Work.MotK.kleinP1]
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add ?_ ?_) ?_
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_C (Fin 5) a).neg
      (MvPolynomial.isHomogeneous_C (Fin 5) b))
      (MvPolynomial.isHomogeneous_X_pow (R := K) 2 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) a).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 0))
      (MvPolynomial.isHomogeneous_X (R := K) 4)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) b).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 1))
      (MvPolynomial.isHomogeneous_X (R := K) 3)) using 1

private theorem kleinP2_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP2 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  rw [Work.MotK.kleinP2]
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add ?_ ?_) ?_
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_C (Fin 5) a).neg
      (MvPolynomial.isHomogeneous_C (Fin 5) b))
      (MvPolynomial.isHomogeneous_X_pow (R := K) 4 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) a).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 1))
      (MvPolynomial.isHomogeneous_X (R := K) 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) b).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 0))
      (MvPolynomial.isHomogeneous_X (R := K) 3)) using 1

private theorem kleinP3_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP3 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  rw [Work.MotK.kleinP3]
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add ?_ ?_) ?_
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_C (Fin 5) a).neg
      (MvPolynomial.isHomogeneous_C (Fin 5) b))
      (MvPolynomial.isHomogeneous_X_pow (R := K) 1 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) a).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 3))
      (MvPolynomial.isHomogeneous_X (R := K) 4)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) b).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 0))
      (MvPolynomial.isHomogeneous_X (R := K) 2)) using 1

private theorem kleinP4_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP4 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  rw [Work.MotK.kleinP4]
  refine MvPolynomial.IsHomogeneous.sub (MvPolynomial.IsHomogeneous.add ?_ ?_) ?_
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      (MvPolynomial.isHomogeneous_C (Fin 5) a).neg
      (MvPolynomial.isHomogeneous_C (Fin 5) b))
      (MvPolynomial.isHomogeneous_X_pow (R := K) 3 2)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) a).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 0))
      (MvPolynomial.isHomogeneous_X (R := K) 1)) using 1
  · convert (MvPolynomial.IsHomogeneous.mul (MvPolynomial.IsHomogeneous.mul
      ((MvPolynomial.isHomogeneous_C (Fin 5) b).pow 2)
      (MvPolynomial.isHomogeneous_X (R := K) 2))
      (MvPolynomial.isHomogeneous_X (R := K) 4)) using 1

/-- The Pfaffians are quadratic forms in the coordinates. -/
theorem isHomogeneous_kleinP_X {K : Type*} [CommRing K] (a b : K) (k : Fin 5) :
    (Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i : Fin 5 => MvPolynomial.X i) k : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  fin_cases k
  · exact kleinP0_homog a b
  · exact kleinP1_homog a b
  · exact kleinP2_homog a b
  · exact kleinP3_homog a b
  · exact kleinP4_homog a b

/-! ## §4 The chart evaluation kills the chart ideal -/

theorem splitPhiOm_splitP (D : Work.MotV.KleinData 𝕜) (k : Fin 5) :
    splitPhiOm D (splitP D k)
      = Work.MotK.kleinP (algebraMap (RatFunc 𝕜) (Work.MotV.Om D)
            (algebraMap 𝕜 (RatFunc 𝕜) D.a))
          (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b))
          (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
            Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) k := by
  simp only [splitP, splitPhiOm]
  exact aeval_kleinP _ _ _ k

theorem splitP_mem_ker (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (k : Fin 5) : splitP D k ∈ RingHom.ker (splitPhiOm D) := by
  rw [RingHom.mem_ker, splitPhiOm_splitP]
  have ha : algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a)
      = algebraMap 𝕜 (Work.MotV.Om D) D.a :=
    IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.a
  have hb : algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b)
      = algebraMap 𝕜 (Work.MotV.Om D) D.b :=
    IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.b
  rw [ha, hb]
  have hsplit : (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
        Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)
      = fun i => (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹ *
          Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
    funext i; rw [div_eq_inv_mul]
  have hkeq : Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) k = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.a,
      IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.b]
    exact hD.1.klein_eq (Work.MotV.Kb 𝕜) k
  rw [hsplit, Work.MotV.kleinP_smul, hkeq, mul_zero]

theorem splitPFIdeal_le_ker (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    Ideal.span (Set.range (splitP D)) ≤ RingHom.ker (splitPhiOm D) := by
  rw [Ideal.span_le]
  rintro x ⟨k, rfl⟩
  exact splitP_mem_ker D hD k

theorem splitQideal_le_ker (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    Ideal.radical (Ideal.span (Set.range (splitP D))) ≤ RingHom.ker (splitPhiOm D) := by
  have hspan := splitPFIdeal_le_ker D hD
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker]
  by_contra hne
  exact pow_ne_zero n hne (by rw [← map_pow, RingHom.mem_ker.mp (hspan hn)])

theorem splitChartIdeal_le_ker_Om (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    splitChartIdeal D ≤ RingHom.ker (splitPhiOm D) := by
  refine sup_le (splitQideal_le_ker D hD) ?_
  rw [Ideal.span_le]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact RingHom.mem_ker.mpr (by
    rw [map_sub, map_one, splitPhiOm_X]
    rw [div_self (hD.1.coord0_ne (Work.MotV.Kb 𝕜)), sub_self])

theorem splitChartIdeal_le_ker (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    splitChartIdeal D ≤ RingHom.ker (splitPhi D) := by
  intro x hx
  rw [RingHom.mem_ker]
  apply Subtype.ext
  rw [splitPhi_coe]
  show splitPhiOm D x = (0 : Work.MotV.Om D)
  exact RingHom.mem_ker.mp (splitChartIdeal_le_ker_Om D hD hx)

/-! ## §5 Homogenisation -/

/-- **Homogenisation in the Klein chart.**  If `splitPhiOm D` kills `f`, then `f` is congruent
modulo `X 0 - 1` to a homogeneous polynomial of the same total degree which is killed by the
*unnormalised* evaluation `aeval (kleinCoord D (Kb 𝕜))`. -/
theorem splitHomogenise (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ∀ f : MvPolynomial (Fin 5) (RatFunc 𝕜), splitPhiOm D f = 0 →
      ∃ F : MvPolynomial (Fin 5) (RatFunc 𝕜),
        F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (RatFunc 𝕜) f.totalDegree ∧
        MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) F = 0 ∧
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
  have h0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.1.coord0_ne (Work.MotV.Kb 𝕜)
  have hsubker : splitPhiOm D (F - f) = 0 := by
    have hle : Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
        Set (MvPolynomial (Fin 5) (RatFunc 𝕜)))
        ≤ RingHom.ker (splitPhiOm D).toRingHom := by
      rw [Ideal.span_le]
      rintro x rfl
      show splitPhiOm D (MvPolynomial.X (0 : Fin 5) - 1) = 0
      rw [map_sub, map_one, splitPhiOm_X, div_self h0, sub_self]
    exact RingHom.mem_ker.mp (hle hsub)
  have hphiF : splitPhiOm D F = 0 := by
    have hsplit : F = f + (F - f) := by ring
    rw [hsplit, map_add, hf, hsubker, add_zero]
  have hscale := aeval_smul_of_homogeneous (K := RatFunc 𝕜) (R := Work.MotV.Om D)
    hFhom ((Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹)
    (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜))
  have hL : (fun i => (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹ *
        Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = (fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
          Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) := by
    funext i; rw [div_eq_mul_inv, mul_comm]
  rw [hL] at hscale
  have h2 : ((Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹) ^ d *
      MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) F = 0 := by
    rw [← hscale]; exact hphiF
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero d (inv_ne_zero h0))

/-! ## §6 The split Klein kernel statement -/

/-- **The Klein kernel statement over `RatFunc 𝕜`.**  If a homogeneous polynomial
`F : RatFunc 𝕜[X₀,…,X₄]` vanishes after the substitution of the Klein coordinates
`κ_i = kleinCoord D (Kb 𝕜) i`, then `F` lies in the ideal generated by the five Pfaffians. -/
theorem kerAevalKleinP (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (n : ℕ) (F : MvPolynomial (Fin 5) (RatFunc 𝕜))
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (RatFunc 𝕜) n)
    (hF0 : MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) F = 0) :
    F ∈ Ideal.span (Set.range (splitP D)) := by
  classical
  have hFhom : F.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n F).mp hF
  set G : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
    MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F with hG
  have hGhom : G.IsHomogeneous n := by
    rw [hG]; exact hFhom.map _
  have hG0 : MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) G = 0 := by
    rw [hG, MvPolynomial.aeval_map_algebraMap (Work.MotV.Kb 𝕜)
      (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) F]
    exact hF0
  have hGmem : G ∈ Ideal.span (Set.range (fun k : Fin 5 => Work.MotK.kleinP
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
      (fun i : Fin 5 => MvPolynomial.X i) k)) := by
    have h := kleinKer_mem_v2 𝕜 D hD.1 (Work.MotV.Kb 𝕜) n G
      ((MvPolynomial.mem_homogeneousSubmodule (R := Work.MotV.Kb 𝕜) n G).mpr hGhom) hG0
    simpa only [Work.MotK.TwRuling.kleinKerIdeal] using h
  -- the degree-`n` part of the ideal
  have hGspan : G ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i : Fin 5 => MvPolynomial.X i) q.1 * MvPolynomial.monomial (q.2.1) 1)) :=
    mem_span_mul_monomial_of_mem_ideal_span
      (fun k : Fin 5 => Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
        (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
        (fun i : Fin 5 => MvPolynomial.X i) k)
      (fun k => isHomogeneous_kleinP_X _ _ k) hGhom hGmem
  -- descend to `RatFunc 𝕜`
  set S : Set (MvPolynomial (Fin 5) (RatFunc 𝕜)) :=
    Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
      splitP D q.1 * MvPolynomial.monomial (q.2.1) 1) with hS
  have hset_pt : ∀ q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2},
      MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
        (splitP D q.1 * MvPolynomial.monomial (q.2.1) 1)
      = Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i : Fin 5 => MvPolynomial.X i) q.1 * MvPolynomial.monomial (q.2.1) 1 := by
    intro q
    have hpf : MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (splitP D q.1)
        = Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i : Fin 5 => MvPolynomial.X i) q.1 := by
      have h := map_kleinP (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
        (algebraMap 𝕜 (RatFunc 𝕜) D.a) (algebraMap 𝕜 (RatFunc 𝕜) D.b) q.1
      simpa only [splitP, ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.a,
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.b] using h
    rw [map_mul, hpf, MvPolynomial.map_monomial, map_one]
  have hset : MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) '' S
      = Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i : Fin 5 => MvPolynomial.X i) q.1 * MvPolynomial.monomial (q.2.1) 1) := by
    rw [hS, ← Set.range_comp]
    congr 1
    funext q
    exact hset_pt q
  have hFspan : F ∈ Submodule.span (RatFunc 𝕜) S :=
    Work.MotV5.ASLocal.mem_span_of_map_mem_span (S := S) (x := F) (by rw [hset]; exact hGspan)
  have hmem : ∀ x ∈ Submodule.span (RatFunc 𝕜) S,
      x ∈ (Ideal.span (Set.range (splitP D)) :
        Set (MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨q, rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self q.1))
    · exact Ideal.zero_mem _
    · intro a b _ _ ha hb; exact Ideal.add_mem _ ha hb
    · intro c a _ ha
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ ha
  exact hmem F hFspan

/-! ## §7 The kernel is the chart ideal -/

theorem ker_splitPhi_le (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    RingHom.ker (splitPhi D) ≤ splitChartIdeal D := by
  intro f hf
  have hfom : splitPhiOm D f = 0 := by
    have h1 : ((splitPhi D f : ↥(splitField D)) : Work.MotV.Om D) = 0 := by
      rw [RingHom.mem_ker.mp hf]; simp
    rwa [splitPhi_coe] at h1
  obtain ⟨F, hFhom, hFaeval, hFdiff⟩ := splitHomogenise D hD f hfom
  have hFmem : F ∈ Ideal.span (Set.range (splitP D)) :=
    kerAevalKleinP D hD f.totalDegree F hFhom hFaeval
  have hsub : Ideal.span (Set.range (splitP D)) ≤ splitChartIdeal D :=
    show Ideal.span (Set.range (splitP D)) ≤
      Ideal.radical (Ideal.span (Set.range (splitP D))) ⊔
        Ideal.span {MvPolynomial.X (0 : Fin 5) - 1} from
      le_trans Ideal.le_radical le_sup_left
  have hspan : (Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
      Set (MvPolynomial (Fin 5) (RatFunc 𝕜)))) ≤ splitChartIdeal D :=
    show (Ideal.span ({MvPolynomial.X (0 : Fin 5) - 1} :
        Set (MvPolynomial (Fin 5) (RatFunc 𝕜)))) ≤
      Ideal.radical (Ideal.span (Set.range (splitP D))) ⊔
        Ideal.span {MvPolynomial.X (0 : Fin 5) - 1} from le_sup_right
  have : f = F - (F - f) := by ring
  rw [this]
  exact Ideal.sub_mem _ (hsub hFmem) (hspan hFdiff)

/-! ## §8 The chart presentation -/

/-- **The chart presentation of the Klein curve in the chart `X 0 = 1`.** -/
theorem splitChartPresentation (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ splitChartIdeal D) ≃ₐ[RatFunc 𝕜]
      ↥(splitField D)) := by
  classical
  set I := splitChartIdeal D with hI
  have hIker : I ≤ RingHom.ker (splitPhi D) := splitChartIdeal_le_ker D hD
  have hker' : RingHom.ker (splitPhi D) = I := le_antisymm (ker_splitPhi_le D hD) hIker
  let ψ : (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) →ₐ[RatFunc 𝕜] ↥(splitField D) :=
    Ideal.Quotient.liftₐ I (splitPhi D) (fun a ha => RingHom.mem_ker.mp (hIker ha))
  have hψmk : ∀ x, ψ (Ideal.Quotient.mk I x) = splitPhi D x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : splitPhi D x = splitPhi D y := Subtype.ext (congrArg Subtype.val hab)
    have hxy : x - y ∈ I := by
      have h0 : splitPhi D (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hab'
      rw [← hker']
      exact RingHom.mem_ker.mpr h0
    rw [← sub_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  haveI hdom : IsDomain (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) :=
    Function.Injective.isDomain ψ hψinj
  let Λ : FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I) →ₐ[RatFunc 𝕜]
      ↥(splitField D) := IsFractionRing.liftAlgHom (g := ψ) hψinj
  have hΛ : ∀ a, Λ (algebraMap _ _ a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψinj a
  have hΛinj : Function.Injective Λ := RingHom.injective Λ.toRingHom
  have hsurj : Function.Surjective Λ := by
    intro z
    let p : ∀ x ∈ (↑(splitField D) : Set (Work.MotV.Om D)), Prop :=
      fun x hx => ∃ y : FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I),
        Λ y = (⟨x, hx⟩ : ↥(splitField D))
    have key : ∀ x hx, p x hx := by
      intro x hx
      refine IntermediateField.adjoin_induction (RatFunc 𝕜) (p := p)
        (fun a ha => ?_) (fun c => ?_) (fun a b ha hb iha ihb => ?_) (fun a ha iha => ?_)
        (fun a b ha hb iha ihb => ?_) hx
      · rw [Set.mem_range] at ha
        obtain ⟨i, rfl⟩ := ha
        refine ⟨algebraMap _ _ (Ideal.Quotient.mk I (MvPolynomial.X i)), Subtype.ext ?_⟩
        rw [hΛ, hψmk]
        exact splitPhi_X D i
      · refine ⟨algebraMap (RatFunc 𝕜)
            (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)) c, ?_⟩
        rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜)
          (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)
          (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸ I)) c, hΛ, AlgHom.commutes]
        rfl
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u + v, Subtype.ext (by rw [map_add, hu, hv]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha
        exact ⟨u⁻¹, Subtype.ext (by rw [map_inv₀, hu]; rfl)⟩
      · obtain ⟨u, hu⟩ := iha; obtain ⟨v, hv⟩ := ihb
        exact ⟨u * v, Subtype.ext (by rw [map_mul, hu, hv]; rfl)⟩
    exact key _ z.2
  exact ⟨AlgEquiv.ofBijective Λ ⟨hΛinj, hsurj⟩⟩

/-! ## §9 The target -/

theorem kleinChartFracIsoTwistFieldAS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸
        ((Ideal.radical (Ideal.span (Set.range (fun k : Fin 5 =>
            Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
              (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b))
              (fun i : Fin 5 => MvPolynomial.X i) k))) : Ideal (MvPolynomial (Fin 5) (RatFunc 𝕜))) ⊔
          (Ideal.span {(MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) (RatFunc 𝕜)) - 1} :
            Ideal (MvPolynomial (Fin 5) (RatFunc 𝕜)))))
      ≃ₐ[RatFunc 𝕜] ↥(Work.MotAS.twistFieldAS D 0)) := by
  have hfield : splitField D = Work.MotAS.twistFieldAS D 0 :=
    (splitField_eq_kleinField D).trans (Work.MotAS.twistFieldAS_zero 𝕜 D hD).symm
  have h := splitChartPresentation D hD
  rw [hfield] at h
  exact h

end Work.MotAS
