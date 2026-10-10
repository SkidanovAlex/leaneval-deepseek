import Mathlib
import Submission.Work.MotAS.AsRhoDefs
import Submission.Work.MotAS.aeval_smul_of_homogeneous
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.asY0_curve
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotAS.Ker4.asTransportP_mv
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASLocal.aevalAsMAevalAsMinv
import Submission.Work.MotV5.ASLocal.mem_span_of_map_mem_span

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.MotV5.ASLocal

open MvPolynomial

/-! ## Auxiliary lemmas (proved here) -/

lemma algebraMap_ratFunc_injective {K : Type*} [CommRing K] [IsDomain K] :
    Function.Injective (algebraMap K (RatFunc K)) := by
  intro a b hab
  have hab' : (algebraMap K (RatFunc K)) a = (algebraMap K (RatFunc K)) b := hab
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a,
      IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) b] at hab'
  rw [← Polynomial.C_eq_algebraMap (R := K) a, ← Polynomial.C_eq_algebraMap (R := K) b] at hab'
  exact Polynomial.C_injective (RatFunc.algebraMap_injective K hab')

lemma aeval_algebraMap_comp {K Lf R : Type*} [CommSemiring K] [CommSemiring Lf]
    [CommSemiring R] [Algebra K Lf] [Algebra Lf R] [Algebra K R] [IsScalarTower K Lf R]
    {σ : Type*} (F : MvPolynomial σ K) (y : σ → Lf) :
    MvPolynomial.aeval (fun i => algebraMap Lf R (y i)) F
      = algebraMap Lf R (MvPolynomial.aeval y F) := by
  have hcomp : MvPolynomial.aeval (fun i => algebraMap Lf R (y i))
      = (IsScalarTower.toAlgHom K Lf R).comp (MvPolynomial.aeval y) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.aeval_X]
  rw [hcomp]; rfl

lemma isHomogeneous_aeval_linear {σ R : Type*} [CommRing R] (F : MvPolynomial σ R)
    (n : ℕ) (hF : F.IsHomogeneous n) (ψ : σ → MvPolynomial σ R)
    (hψ : ∀ i, (ψ i).IsHomogeneous 1) :
    (MvPolynomial.aeval ψ F).IsHomogeneous n := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isHomogeneous_zero σ R n
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [MvPolynomial.aeval_monomial, ← MvPolynomial.C_eq_algebraMap]
    refine MvPolynomial.IsHomogeneous.C_mul ?_ r
    rw [Finsupp.prod_of_support_subset d (Finset.Subset.refl _) _ (by intro i _; simp)]
    have hdeg : (∑ i ∈ d.support, d i) = n := by
      have h := hr
      rw [Finsupp.weight_apply] at h
      simpa only [Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] using h
    convert MvPolynomial.IsHomogeneous.prod d.support (fun i => ψ i ^ (d i))
      (fun i => d i) (fun i _ => ?_) using 2
    · exact hdeg.symm
    · simpa using (hψ i).pow (d i)

lemma isHomogeneous_mem_span_monomial {σ R : Type*} [CommSemiring R] {n : ℕ}
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    p ∈ Submodule.span R (Set.range (fun m : {m : σ →₀ ℕ // m.support.sum m = n} =>
      MvPolynomial.monomial m.1 1)) := by
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  have hdeg : Finsupp.degree d = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  have hdeg' : d.support.sum d = n := by
    rw [Finsupp.degree_apply] at hdeg
    exact hdeg
  rw [show MvPolynomial.monomial d (p.coeff d) = p.coeff d • MvPolynomial.monomial d 1 from by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨d, hdeg'⟩, rfl⟩)

lemma kleinTwP_one {R : Type*} [CommRing R] (a b : R) (y : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinTwP a b 1 y k = Work.MotK.kleinP a b y k := by
  have h := congrFun (Work.MotV.kleinTw_one (F := R) a b y) k
  fin_cases k <;> (simpa [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1,
    Work.MotK.kleinTwP2, Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, Work.MotV.kleinTw,
    Work.MotV.twMon, pow_two, mul_comm, mul_left_comm, mul_assoc, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons] using h)

lemma sdBas_baseChange_eq_kleinBas {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) :
    Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜))
      = Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) := by
  funext i
  fin_cases i <;> rfl

lemma map_kleinPAS_poly {K Kb : Type*} [Field K] [Field Kb] (φ : K →+* Kb)
    (aK bK gK : K) (k : Fin 5) :
    MvPolynomial.map φ (Work.MotAS.kleinPAS (MvPolynomial.C aK) (MvPolynomial.C bK)
        (MvPolynomial.C gK) (fun i => MvPolynomial.X i) k)
      = Work.MotAS.kleinPAS (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
        (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i) k := by
  fin_cases k
  · show MvPolynomial.map φ (Work.MotAS.kleinPAS0 (MvPolynomial.C aK) (MvPolynomial.C bK)
          (MvPolynomial.C gK) (fun i => MvPolynomial.X i))
        = Work.MotAS.kleinPAS0 (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
          (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i)
    simp only [Work.MotAS.kleinPAS0, map_add, map_sub, map_mul, map_pow, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X]
  · show MvPolynomial.map φ (Work.MotAS.kleinPAS1 (MvPolynomial.C aK) (MvPolynomial.C bK)
          (MvPolynomial.C gK) (fun i => MvPolynomial.X i))
        = Work.MotAS.kleinPAS1 (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
          (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i)
    simp only [Work.MotAS.kleinPAS1, map_add, map_sub, map_mul, map_pow, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X]
  · show MvPolynomial.map φ (Work.MotAS.kleinPAS2 (MvPolynomial.C aK) (MvPolynomial.C bK)
          (MvPolynomial.C gK) (fun i => MvPolynomial.X i))
        = Work.MotAS.kleinPAS2 (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
          (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i)
    simp only [Work.MotAS.kleinPAS2, map_add, map_sub, map_mul, map_pow, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X]
  · show MvPolynomial.map φ (Work.MotAS.kleinPAS3 (MvPolynomial.C aK) (MvPolynomial.C bK)
          (MvPolynomial.C gK) (fun i => MvPolynomial.X i))
        = Work.MotAS.kleinPAS3 (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
          (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i)
    simp only [Work.MotAS.kleinPAS3, map_add, map_sub, map_mul, map_pow, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X]
  · show MvPolynomial.map φ (Work.MotAS.kleinPAS4 (MvPolynomial.C aK) (MvPolynomial.C bK)
          (MvPolynomial.C gK) (fun i => MvPolynomial.X i))
        = Work.MotAS.kleinPAS4 (MvPolynomial.C (φ aK)) (MvPolynomial.C (φ bK))
          (MvPolynomial.C (φ gK)) (fun i => MvPolynomial.X i)
    simp only [Work.MotAS.kleinPAS4, map_add, map_sub, map_mul, map_pow, map_ofNat,
      MvPolynomial.map_C, MvPolynomial.map_X]

/-! ## The main theorem -/

theorem asKernel6 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (F : MvPolynomial (Fin 5) (RatFunc 𝕜))
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (RatFunc 𝕜) 6)
    (h : MvPolynomial.aeval (fun i => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) i)) F = 0) :
    F ∈ Work.MotAS.asIdeal6 (RatFunc 𝕜) (algebraMap 𝕜 (RatFunc 𝕜) D.a)
      (algebraMap 𝕜 (RatFunc 𝕜) D.b) (Work.MotV.fAS 𝕜) := by
  classical
  set g : RatFunc 𝕜 := Work.MotV.fAS 𝕜 with hg
  have hFhom : F.IsHomogeneous 6 := (MvPolynomial.mem_homogeneousSubmodule 6 F).mp hF
  -- ### Step 1: evaluate at `asY0` inside the twist field
  have hY0 : MvPolynomial.aeval (fun i => Work.MotAS.asY0 D g i) F = 0 := by
    have hcomp := aeval_algebraMap_comp (R := RatFunc ↥(Work.MotAS.twistFieldAS D g))
      F (fun i => Work.MotAS.asY0 D g i)
    have h' : algebraMap ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g))
        (MvPolynomial.aeval (fun i => Work.MotAS.asY0 D g i) F) = 0 := by
      rw [← hcomp]; exact h
    exact algebraMap_ratFunc_injective (by rw [h']; simp)
  have hOm : MvPolynomial.aeval (fun i => (Work.MotAS.asY0 D g i : Work.MotV.Om D)) F = 0 := by
    have hcoe : (fun i => (Work.MotAS.asY0 D g i : Work.MotV.Om D))
        = (fun i => algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
            (Work.MotAS.asY0 D g i)) := rfl
    rw [hcoe, aeval_algebraMap_comp (R := Work.MotV.Om D) F (fun i => Work.MotAS.asY0 D g i),
      hY0, map_zero]
  -- ### Step 2: the same with `asTwY`
  have hTw : MvPolynomial.aeval (Work.MotAS.asTwY D g) F = 0 := by
    have hscale : (fun i => (Work.MotAS.asY0 D g i : Work.MotV.Om D))
        = fun i => (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g i := by
      funext i
      show (Work.MotAS.asTwY D g i / Work.MotAS.asTwY D g 0 : Work.MotV.Om D)
        = (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g i
      rw [div_eq_mul_inv, mul_comm]
    have hsmul := Work.MotAS.aeval_smul_of_homogeneous (K := RatFunc 𝕜) (R := Work.MotV.Om D)
      hFhom ((Work.MotAS.asTwY D g 0)⁻¹) (Work.MotAS.asTwY D g)
    rw [hscale, hsmul] at hOm
    exact (mul_eq_zero.mp hOm).resolve_left
      (pow_ne_zero 6 (inv_ne_zero (Work.MotAS.asTwY_zero_ne_zero D g hD.1)))
  -- ### Step 3: the base change and the two substitutions
  set a₀ : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a with ha₀
  set b₀ : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b with hb₀
  set g₀ : Work.MotV.Kb 𝕜 := algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g with hg₀
  let ψ : Fin 5 → MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) := fun j =>
    ∑ i, MvPolynomial.C (Work.MotAS.asMinv (Work.MotV5.asRoot g) j i) * MvPolynomial.X i
  let G : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
    MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F
  let F' : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) := MvPolynomial.aeval ψ G
  let χ : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜]
      MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
    MvPolynomial.aeval (fun i => ∑ l, MvPolynomial.C
      (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l)
  let JAS : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
    Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotAS.kleinPASm a₀ b₀ g₀ q.1 * MvPolynomial.monomial q.2.1 1))
  -- ### Step 4: `aeval asKap F' = 0`
  have hasKap : MvPolynomial.aeval (Work.MotAS.asKap D) F' = 0 := by
    have hψi : ∀ i, MvPolynomial.aeval (Work.MotAS.asKap D) (ψ i) = Work.MotAS.asTwY D g i := by
      intro i
      have h1 : MvPolynomial.aeval (Work.MotAS.asKap D) (ψ i)
          = ∑ j : Fin 5, algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
              (Work.MotAS.asMinv (Work.MotV5.asRoot g) i j) * Work.MotAS.asKap D j := by
        simp only [ψ, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      have h2 : (∑ j : Fin 5, algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
              (Work.MotAS.asMinv (Work.MotV5.asRoot g) i j) * Work.MotAS.asKap D j)
          = ((Work.MotAS.asNO D g).mulVec (Work.MotAS.asKap D)) i := by
        simp only [Work.MotAS.asNO, Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [h1, h2, ← Work.MotAS.asTwY_eq_mulVec]
    have hcomb : MvPolynomial.aeval (Work.MotAS.asKap D) F'
        = MvPolynomial.aeval (Work.MotAS.asTwY D g) G := by
      show MvPolynomial.aeval (Work.MotAS.asKap D) (MvPolynomial.aeval ψ G)
        = MvPolynomial.aeval (Work.MotAS.asTwY D g) G
      rw [MvPolynomial.comp_aeval_apply]
      rw [show (fun i => MvPolynomial.aeval (Work.MotAS.asKap D) (ψ i))
        = Work.MotAS.asTwY D g from funext hψi]
    rw [hcomb]
    show MvPolynomial.aeval (Work.MotAS.asTwY D g) G = 0
    rw [show G = MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F from rfl,
      MvPolynomial.aeval_map_algebraMap (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) F, hTw]
  -- ### Step 5: homogeneity of `F'`
  have hGhom : G.IsHomogeneous 6 := by
    show (MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F).IsHomogeneous 6
    exact hFhom.map _
  have hψhom : ∀ i, (ψ i).IsHomogeneous 1 := by
    intro i
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun j =>
      MvPolynomial.C (Work.MotAS.asMinv (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) 1
      (fun j _ => (MvPolynomial.isHomogeneous_X (R := Work.MotV.Kb 𝕜) j).C_mul _)
  have hF'hom : F'.IsHomogeneous 6 := by
    show (MvPolynomial.aeval ψ G).IsHomogeneous 6
    exact isHomogeneous_aeval_linear G 6 hGhom ψ hψhom
  have hF'homem : F' ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) 6 :=
    (MvPolynomial.mem_homogeneousSubmodule (R := Work.MotV.Kb 𝕜) 6 F').mpr hF'hom
  -- ### Step 6: apply the split sextic kernel statement
  have hF'ideal : F' ∈ Work.MotK.TwRuling.twIdeal6 (Work.MotV.Kb 𝕜) a₀ b₀ 1 := by
    by_contra hnot
    have hab : a₀ * b₀ ≠ 0 := by
      rw [ha₀, hb₀, ← map_mul]
      intro hh
      exact hD.1.ab_ne (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜)) (by rw [hh, map_zero]))
    have h1 : (1 : Work.MotV.Kb 𝕜) ≠ 0 := one_ne_zero
    refine Work.MotK.TwRuling.sexticTw_notMem_kernel (Work.MotV.Kb 𝕜)
      (D.E.baseChange (Work.MotV.Kb 𝕜)) a₀ b₀ 1 hab h1 (Work.MotAS.asKap D) ?_ ?_ ?_ F' hF'homem ?_ hasKap
    · intro i
      rw [sdBas_baseChange_eq_kleinBas]
      have hsum : Work.MotAS.asKap D i = ∑ m : Fin 5,
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) (D.coord i m)) •
            Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m := by
        simp [Work.MotAS.asKap, Work.MotV.kleinCoord, Work.MotV.kleinBas, Algebra.smul_def]
      rw [hsum]
      exact Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
    · intro m
      rw [sdBas_baseChange_eq_kleinBas]
      obtain ⟨e, he⟩ := hD.1.spans
      rw [he (Work.MotV.Kb 𝕜) m]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro k
      rw [show (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (1 : Work.MotV.Kb 𝕜)
        : Work.MotV.Om D) = 1 from map_one _]
      rw [kleinTwP_one]
      have hke : Work.MotK.kleinP (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a₀)
          (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) b₀) (Work.MotAS.asKap D) k = 0 := by
        rw [ha₀, hb₀,
          show Work.MotAS.asKap D = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) from rfl,
          ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.a,
          ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.b]
        exact hD.1.klein_eq (Work.MotV.Kb 𝕜) k
      exact hke
    · exact hnot
  -- ### Step 7: transport back: `G ∈ JAS`
  have hχ_mon : ∀ m : Fin 5 →₀ ℕ, m.support.sum m = 4 →
      χ (MvPolynomial.monomial m 1) ∈ Submodule.span (Work.MotV.Kb 𝕜)
        (Set.range (fun m' : {m' : Fin 5 →₀ ℕ // m'.support.sum m' = 4} =>
          MvPolynomial.monomial m'.1 1)) := by
    intro m hm
    have hhom : (MvPolynomial.monomial m (1 : Work.MotV.Kb 𝕜)).IsHomogeneous 4 := by
      apply MvPolynomial.isHomogeneous_monomial
      rw [Finsupp.degree_apply]; exact hm
    have hsub : ∀ i, ((fun i => ∑ l, MvPolynomial.C
        (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) i).IsHomogeneous 1 := by
      intro i
      exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun l =>
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) 1
        (fun l _ => (MvPolynomial.isHomogeneous_X (R := Work.MotV.Kb 𝕜) l).C_mul _)
    have hχhom : (χ (MvPolynomial.monomial m 1)).IsHomogeneous 4 := by
      dsimp only [χ]
      exact isHomogeneous_aeval_linear (MvPolynomial.monomial m 1) 4 hhom _ hsub
    exact isHomogeneous_mem_span_monomial hχhom
  have hkin : ∀ (j : Fin 5) {f : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)},
      f ∈ Submodule.span (Work.MotV.Kb 𝕜)
        (Set.range (fun m' : {m' : Fin 5 →₀ ℕ // m'.support.sum m' = 4} =>
          MvPolynomial.monomial m'.1 1)) →
      Work.MotAS.kleinPASm a₀ b₀ g₀ j * f ∈ JAS := by
    intro j f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro x ⟨m', rfl⟩
      exact Submodule.subset_span ⟨(j, m'), rfl⟩
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      rw [mul_add]; exact Submodule.add_mem _ ihx ihy
    · rintro a x _ ih
      rw [MvPolynomial.smul_eq_C_mul, mul_left_comm, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ a ih
  have hχtw : ∀ y ∈ Work.MotK.TwRuling.twIdeal6 (Work.MotV.Kb 𝕜) a₀ b₀ 1, χ y ∈ JAS := by
    intro y hy
    rw [Work.MotK.TwRuling.twIdeal6] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro z ⟨q, rfl⟩
      show χ (Work.MotK.kleinTwP (MvPolynomial.C a₀) (MvPolynomial.C b₀) (MvPolynomial.C 1)
        (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1) ∈ JAS
      rw [map_mul]
      have hk : χ (Work.MotK.kleinTwP (MvPolynomial.C a₀) (MvPolynomial.C b₀) (MvPolynomial.C 1)
            (fun i => MvPolynomial.X i) q.1)
          = ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asN (Work.MotV5.asRoot g) q.1 j)
              * Work.MotAS.kleinPASm a₀ b₀ g₀ j := by
        rw [show (MvPolynomial.C (1 : Work.MotV.Kb 𝕜) : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) = 1
          from map_one _]
        rw [kleinTwP_one]
        show MvPolynomial.aeval (fun i => ∑ l, MvPolynomial.C
            (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l)
          (Work.MotK.kleinP (MvPolynomial.C a₀) (MvPolynomial.C b₀)
            (fun i => MvPolynomial.X i) q.1) = _
        exact Work.MotAS.Ker4.asTransportP_mv 𝕜 D g q.1
      rw [hk, Finset.sum_mul]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (hkin j (hχ_mon q.2.1 q.2.2))
    · rw [map_zero]; exact JAS.zero_mem
    · intro x y _ _ ihx ihy
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
    · intro c x _ ih
      rw [map_smul]; exact Submodule.smul_mem _ c ih
  have hG_mem : G ∈ JAS := by
    have hχeq : χ F' = G := by
      show MvPolynomial.aeval (fun i => ∑ l, MvPolynomial.C
          (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l)
          (MvPolynomial.aeval ψ G) = G
      exact aevalAsMAevalAsMinv (Work.MotV5.asRoot g) G
    rw [← hχeq]
    exact hχtw F' hF'ideal
  -- ### Step 8: descend to `K = RatFunc 𝕜`
  have hset_pt : ∀ q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4},
      MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
        (Work.MotAS.kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b))
          (MvPolynomial.C g) (fun i => MvPolynomial.X i) q.1 *
          MvPolynomial.monomial q.2.1 1)
      = Work.MotAS.kleinPASm a₀ b₀ g₀ q.1 * MvPolynomial.monomial q.2.1 1 := by
    intro q
    rw [map_mul, map_kleinPAS_poly, MvPolynomial.map_monomial, map_one]
    have hpf : Work.MotAS.kleinPAS (MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
          (algebraMap 𝕜 (RatFunc 𝕜) D.a))) (MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)
          (algebraMap 𝕜 (RatFunc 𝕜) D.b))) (MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g))
          (fun i => MvPolynomial.X i) q.1
        = Work.MotAS.kleinPASm a₀ b₀ g₀ q.1 := by
      simp only [Work.MotAS.kleinPASm]
      rw [ha₀, hb₀, hg₀,
        IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.a,
        IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.b]
    rw [hpf]
  have hset : MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) ''
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotAS.kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b))
          (MvPolynomial.C g) (fun i => MvPolynomial.X i) q.1 *
        MvPolynomial.monomial q.2.1 1))
      = Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotAS.kleinPASm a₀ b₀ g₀ q.1 * MvPolynomial.monomial q.2.1 1) := by
    rw [← Set.range_comp]
    congr 1
    funext q
    exact hset_pt q
  have hG_asIdeal : G ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) ''
        (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
          Work.MotAS.kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
            (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b))
            (MvPolynomial.C g) (fun i => MvPolynomial.X i) q.1 *
          MvPolynomial.monomial q.2.1 1))) := by
    rw [hset]
    exact hG_mem
  have hgoal : F ∈ Submodule.span (RatFunc 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotAS.kleinPAS (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (RatFunc 𝕜) D.b))
          (MvPolynomial.C g) (fun i => MvPolynomial.X i) q.1 *
        MvPolynomial.monomial q.2.1 1)) :=
    mem_span_of_map_mem_span hG_asIdeal
  exact hgoal

end Work.MotV5.ASLocal
