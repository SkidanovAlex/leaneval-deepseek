import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.Ker6.Defs
import Submission.Work.MotAS.Ker6.Lower
import Submission.Work.MotAS.Ker6.asIdeal6_finrank_ge
import Submission.Work.MotAS.Ker4.kleinPASm_isHomogeneous
import Submission.Work.MotAS.ASChart3.sdBas_mem_span_asTwY
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.MotAS

open MvPolynomial

/-- The sixfold products of `asTwY D g` span a subspace contained in the range of the evaluation
map on the sextics. -/
private theorem prodSpan6_le_range (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (g : RatFunc 𝕜)
    (Φ : ↥(Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜)) →ₗ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hΦ : Φ = (MvPolynomial.aeval (Work.MotAS.asTwY D g)).toLinearMap.comp
      (Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜)).subtype) :
    Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) 6
      ≤ LinearMap.range Φ := by
  rw [hΦ]
  change Submodule.span (Work.MotV.Kb 𝕜)
    (Set.range (fun p : Fin 6 → Fin 5 => ∏ i, Work.MotAS.asTwY D g (p i))) ≤
      LinearMap.range ((MvPolynomial.aeval (Work.MotAS.asTwY D g)).toLinearMap.comp
        (Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜)).subtype)
  rw [Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  change (∏ i : Fin 6, Work.MotAS.asTwY D g (p i)) ∈
    LinearMap.range ((MvPolynomial.aeval (Work.MotAS.asTwY D g)).toLinearMap.comp
      (Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜)).subtype)
  have hhom : (∏ i : Fin 6, MvPolynomial.X (p i)) ∈ Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜) := by
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin 6))
      (fun i : Fin 6 => MvPolynomial.X (p i)) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X (Work.MotV.Kb 𝕜) (p i))
    simpa [Work.MotAS.Ker6.hom6] using h
  have hval : ((MvPolynomial.aeval (Work.MotAS.asTwY D g)).toLinearMap.comp
        (Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜)).subtype)
      ⟨∏ i : Fin 6, MvPolynomial.X (p i), hhom⟩
      = ∏ i, Work.MotAS.asTwY D g (p i) := by
    show MvPolynomial.aeval (Work.MotAS.asTwY D g) (∏ i : Fin 6, MvPolynomial.X (p i))
      = ∏ i, Work.MotAS.asTwY D g (p i)
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => MvPolynomial.aeval_X _ (p i))
  rw [← hval]
  exact LinearMap.mem_range_self _ _

theorem asKernel6 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (F : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜))
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) 6)
    (hF0 : MvPolynomial.aeval (Work.MotAS.asTwY D g) F = 0) :
    F ∈ Work.MotAS.asIdeal6 (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) := by
  classical
  have hDg : D.Good := hD.1
  have hab : D.a * D.b ≠ 0 := hDg.ab_ne
  set Φbig : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D :=
    MvPolynomial.aeval (Work.MotAS.asTwY D g) with hΦbig
  set T : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
    Work.MotAS.Ker6.hom6 (Work.MotV.Kb 𝕜) with hT
  set J : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
    Work.MotAS.asIdeal6 (Work.MotV.Kb 𝕜) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) with hJ
  set Φ : ↥T →ₗ[Work.MotV.Kb 𝕜] Work.MotV.Om D :=
    Φbig.toLinearMap.comp T.subtype with hΦ
  haveI hTfin : Module.Finite (Work.MotV.Kb 𝕜) ↥T := by
    rw [hT]
    exact Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 5) (Work.MotV.Kb 𝕜) 6)
  haveI hRfin : Module.Finite (Work.MotV.Kb 𝕜) ↥(LinearMap.range Φ) := Module.Finite.range Φ
  -- the degree-6 part of the AS Pfaffian ideal, in `kleinPASm` form
  have hJdef : J = Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 4} =>
        Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
            (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
            (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1
          * MvPolynomial.monomial q.2.1 1)) := rfl
  -- (1) the five AS Pfaffians vanish at the Galois coordinates
  have hgen : ∀ k : Fin 5, Φbig (Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
      (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) k) = 0 := by
    intro k
    have hcoe : ∀ x : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜),
        (((MvPolynomial.aeval (Work.MotAS.asTwY D g) :
          MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
          MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →+* Work.MotV.Om D)) x
        = MvPolynomial.aeval (Work.MotAS.asTwY D g) x := fun x => rfl
    have h := Work.MotAS.map_kleinPAS_apply
      ((MvPolynomial.aeval (Work.MotAS.asTwY D g) :
        MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
        MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →+* Work.MotV.Om D)
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
      (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
      (MvPolynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g))
      (fun i => MvPolynomial.X i) k
    simp only [hcoe, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at h
    rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.b,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g] at h
    rw [congrFun (Work.MotAS.asTwY_kleinPAS D hD g) k] at h
    rw [hΦbig]
    exact h
  -- (2) the degree-6 AS ideal is contained in the kernel of the evaluation
  have hJker : J ≤ LinearMap.ker Φbig.toLinearMap := by
    rw [hJdef, Submodule.span_le]
    rintro y ⟨q, rfl⟩
    show Φbig (Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1
        * MvPolynomial.monomial q.2.1 1) = 0
    rw [map_mul, hgen q.1, zero_mul]
  -- (3) the range of the restriction has dimension at least 30
  have hsd : ∀ m, Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m ∈
      Submodule.span (Work.MotV.Kb 𝕜) (Set.range (Work.MotAS.asTwY D g)) :=
    fun m => Work.MotAS.ASChart3.sdBas_mem_span_asTwY 𝕜 D hDg g m
  have hprod : Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜)
        (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜))) 6
      ≤ Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) 6 :=
    Work.MotK.TwRuling.prodSpanN_le (Work.MotV.Kb 𝕜) 6 hsd
  haveI hPfin : Module.Finite (Work.MotV.Kb 𝕜)
      ↥(Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) 6) := by
    rw [Work.MotK.TwRuling.prodSpanN]
    exact Module.Finite.span_of_finite _ (Set.finite_range _)
  have hrange : Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) 6
      ≤ LinearMap.range Φ := by
    rw [hΦ]
    exact prodSpan6_le_range 𝕜 D g _ rfl
  have hge : 30 ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(LinearMap.range Φ) := by
    calc 30 ≤ Module.finrank (Work.MotV.Kb 𝕜)
          ↥(Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜)
            (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜))) 6) :=
          Work.MotAS.Ker6.finrank_prodSpan6_ge (Work.MotV.Kb 𝕜)
            (D.E.baseChange (Work.MotV.Kb 𝕜))
      _ ≤ Module.finrank (Work.MotV.Kb 𝕜)
          ↥(Work.MotK.TwRuling.prodSpanN (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) 6) :=
          Submodule.finrank_mono hprod
      _ ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥(LinearMap.range Φ) := Submodule.finrank_mono hrange
  -- (4) rank-nullity: the kernel of the evaluation has dimension at most 180
  have hker_le : Module.finrank (Work.MotV.Kb 𝕜) ↥(LinearMap.ker Φ) ≤ 180 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have h210 : Module.finrank (Work.MotV.Kb 𝕜) ↥T = 210 := by
      rw [hT]
      exact Work.MotK.TwRulingSix.finrank_homogeneous_six (Work.MotV.Kb 𝕜)
    omega
  -- (5) the degree-6 part of the AS Pfaffian ideal has dimension at least 180
  have h180 : 180 ≤ Module.finrank (Work.MotV.Kb 𝕜) ↥J := by
    rw [hJ]
    exact Work.MotAS.Ker6.asIdeal6_finrank_ge 𝕜 D g hab
  -- (6) the AS ideal lies in the degree-6 piece
  have hJT : J ≤ T := by
    rw [hJdef, hT, Submodule.span_le]
    rintro y ⟨q, rfl⟩
    have h1 : (Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1).IsHomogeneous 2 :=
      Work.MotAS.Ker4.kleinPASm_isHomogeneous (Work.MotV.Kb 𝕜) _ _ _ q.1
    have h2 : (MvPolynomial.monomial q.2.1 1 : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)
        ).IsHomogeneous 4 := by
      refine MvPolynomial.isHomogeneous_monomial 1 ?_
      rw [Finsupp.degree_apply]
      exact q.2.2
    exact (MvPolynomial.mem_homogeneousSubmodule 6 _).mpr (by simpa using h1.mul h2)
  haveI hJfin : Module.Finite (Work.MotV.Kb 𝕜) ↥J := by
    rw [hJdef]
    haveI hfinS := Work.MotAS.Ker6.finite_finsupp_deg4
    exact Module.Finite.span_of_finite _ (Set.finite_range _)
  -- (7) the dimension count
  have hcomapfin : Module.finrank (Work.MotV.Kb 𝕜) ↥(Submodule.comap T.subtype J)
      = Module.finrank (Work.MotV.Kb 𝕜) ↥J := by
    have hmap : Submodule.map T.subtype (Submodule.comap T.subtype J) = J := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hJT]
    rw [← Submodule.finrank_map_subtype_eq T (Submodule.comap T.subtype J), hmap]
  have hJh : Submodule.comap T.subtype J ≤ LinearMap.ker Φ := by
    intro x hx
    show Φ x = 0
    show Φbig (x : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) = 0
    simpa using hJker hx
  have hker_eq : Submodule.comap T.subtype J = LinearMap.ker Φ :=
    Submodule.eq_of_le_of_finrank_le hJh
      (by rw [hcomapfin]; exact le_trans hker_le h180)
  -- (8) conclude
  have hFmem : F ∈ T := by
    rw [hT]
    exact hF
  have hx : (⟨F, hFmem⟩ : ↥T) ∈ Submodule.comap T.subtype J := by
    rw [hker_eq]
    show Φ ⟨F, hFmem⟩ = 0
    exact hF0
  simpa using (Submodule.mem_comap.mp hx)

end Work.MotAS
