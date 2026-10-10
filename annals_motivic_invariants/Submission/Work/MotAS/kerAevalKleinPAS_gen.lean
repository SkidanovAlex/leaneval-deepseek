import Mathlib
import Submission.Work.MotAS.KleinKerASMain
import Submission.Work.MotV5.ASLocal.asKernel6
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotV5.ASLocal.aevalAsMAevalAsMinv
import Submission.Work.MotV5.ASLocal.mem_span_of_map_mem_span
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotAS.aeval_asM_twIdeal_subset
import Submission.Work.MotAS.mem_span_mul_monomial_of_mem_ideal_span

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

/-! ## Homogeneity of the five split Pfaffians -/

private theorem kleinP0_homog {K : Type*} [CommRing K] (a b : K) :
    (Work.MotK.kleinP0 (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
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
      (fun i => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
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
      (fun i => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
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
      (fun i => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
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
      (fun i => MvPolynomial.X i) : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
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

private theorem isHomogeneous_kleinP_X {K : Type*} [CommRing K] (a b : K) (k : Fin 5) :
    (Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
      (fun i => MvPolynomial.X i) k : MvPolynomial (Fin 5) K).IsHomogeneous 2 := by
  fin_cases k
  · exact kleinP0_homog a b
  · exact kleinP1_homog a b
  · exact kleinP2_homog a b
  · exact kleinP3_homog a b
  · exact kleinP4_homog a b

/-! ## Main theorem -/

/-- **The transported ("AS", characteristic `5`) Klein kernel statement, in every degree.**  Let
`𝕜` be a field of characteristic `5`, `D` Klein data over `𝕜` with
`Work.MotV5.KleinData.ASGood D`, `g : RatFunc 𝕜`, and let `F : MvPolynomial (Fin 5) (RatFunc 𝕜)` be
homogeneous of degree `n` and vanish after the substitution `X i ↦ asTwY D g i` (the Lagrange
coordinates `asM (asRoot g)⁻¹ κ` of the Klein point, `Work.MotAS.asTwY`).  Then `F` lies in the
ideal of `RatFunc 𝕜[X₀,…,X₄]` generated by the five *transported* Pfaffians
`Work.MotAS.kleinPASm (aK D) (bK D) g`.-/
theorem kerAevalKleinPAS_gen (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) (n : ℕ)
    (F : MvPolynomial (Fin 5) (RatFunc 𝕜))
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (RatFunc 𝕜) n)
    (hF0 : MvPolynomial.aeval (Work.MotAS.asTwY D g) F = 0) :
    F ∈ Ideal.span (Set.range (Work.MotAS.kleinPASm (Work.MotAS.aK D) (Work.MotAS.bK D) g)) := by
  classical
  have hFhom : F.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n F).mp hF
  -- ### Step 1: base change and substitutions
  set a₀ : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a with ha₀
  set b₀ : Work.MotV.Kb 𝕜 := algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b with hb₀
  let ψ : Fin 5 → MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) := fun j =>
    ∑ i, MvPolynomial.C (Work.MotAS.asMinv (Work.MotV5.asRoot g) j i) * MvPolynomial.X i
  let G : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
    MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F
  let F' : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) := MvPolynomial.aeval ψ G
  -- ### Step 2: `aeval asKap F' = 0`
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
      MvPolynomial.aeval_map_algebraMap (Work.MotV.Kb 𝕜) (Work.MotAS.asTwY D g) F, hF0]
  -- ### Step 3: homogeneity of `F'`
  have hGhom : G.IsHomogeneous n := by
    show (MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) F).IsHomogeneous n
    exact hFhom.map _
  have hψhom : ∀ i, (ψ i).IsHomogeneous 1 := by
    intro i
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun j =>
      MvPolynomial.C (Work.MotAS.asMinv (Work.MotV5.asRoot g) i j) * MvPolynomial.X j) 1
      (fun j _ => (MvPolynomial.isHomogeneous_X (R := Work.MotV.Kb 𝕜) j).C_mul _)
  have hF'hom : F'.IsHomogeneous n := by
    show (MvPolynomial.aeval ψ G).IsHomogeneous n
    exact Work.MotV5.ASLocal.isHomogeneous_aeval_linear G n hGhom ψ hψhom
  have hF'homem : F' ∈ MvPolynomial.homogeneousSubmodule (Fin 5) (Work.MotV.Kb 𝕜) n :=
    (MvPolynomial.mem_homogeneousSubmodule (R := Work.MotV.Kb 𝕜) n F').mpr hF'hom
  -- ### Step 4: the split Klein kernel statement over the algebraic closure
  have hF'ideal : F' ∈ Work.MotK.TwRuling.kleinKerIdeal (Work.MotV.Kb 𝕜) a₀ b₀ := by
    have h := Work.MotAS.kleinKer_mem_v2 𝕜 D hD.1 (Work.MotV.Kb 𝕜) n F' hF'homem hasKap
    rw [← ha₀, ← hb₀] at h
    exact h
  -- ### Step 5: the degree-`n` part of the ideal
  have hF'tw : F' ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotK.kleinP (MvPolynomial.C a₀) (MvPolynomial.C b₀)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)) :=
    mem_span_mul_monomial_of_mem_ideal_span (fun k => Work.MotK.kleinP (MvPolynomial.C a₀) (MvPolynomial.C b₀)
      (fun i => MvPolynomial.X i) k) (fun k => isHomogeneous_kleinP_X a₀ b₀ k) hF'hom hF'ideal
  -- ### Step 6: transport back with `χ`
  have hG : G ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1 * MvPolynomial.monomial q.2.1 1)) := by
    have hχ : MvPolynomial.aeval (fun i : Fin 5 => ∑ l : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) F' = G :=
      Work.MotV5.ASLocal.aevalAsMAevalAsMinv (Work.MotV5.asRoot g) G
    rw [← hχ]
    exact aeval_asM_twIdeal_subset 𝕜 D g n (by simpa only [ha₀, hb₀] using hF'tw)
  -- ### Step 7: descend along `RatFunc 𝕜 → Kb 𝕜`
  set S : Set (MvPolynomial (Fin 5) (RatFunc 𝕜)) :=
    Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
      Work.MotAS.kleinPASm (Work.MotAS.aK D) (Work.MotAS.bK D) g q.1 *
        MvPolynomial.monomial q.2.1 1) with hS
  have hset_pt : ∀ q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2},
      MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
        (Work.MotAS.kleinPASm (Work.MotAS.aK D) (Work.MotAS.bK D) g q.1 *
          MvPolynomial.monomial q.2.1 1)
      = Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1 *
        MvPolynomial.monomial q.2.1 1 := by
    intro q
    have hpf : MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
        (Work.MotAS.kleinPASm (Work.MotAS.aK D) (Work.MotAS.bK D) g q.1)
        = Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
            (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
            (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1 := by
      simp only [Work.MotAS.kleinPASm]
      rw [Work.MotV5.ASLocal.map_kleinPAS_poly]
      simp only [Work.MotAS.aK, Work.MotAS.bK,
        IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.a,
        IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.b]
    rw [map_mul, hpf, MvPolynomial.map_monomial, map_one]
  have hset : MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) '' S
      = Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
          (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) q.1 * MvPolynomial.monomial q.2.1 1) := by
    rw [hS, ← Set.range_comp]
    congr 1
    funext q
    exact hset_pt q
  have hG_map : G ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (MvPolynomial.map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) '' S) := by
    rw [hset]
    exact hG
  have hFspan : F ∈ Submodule.span (RatFunc 𝕜) S :=
    Work.MotV5.ASLocal.mem_span_of_map_mem_span (S := S) (x := F) hG_map
  -- ### Step 8: conclude membership in the ideal
  have hmem : ∀ x ∈ Submodule.span (RatFunc 𝕜) S,
      x ∈ (Ideal.span (Set.range (Work.MotAS.kleinPASm (Work.MotAS.aK D) (Work.MotAS.bK D) g)) :
        Set (MvPolynomial (Fin 5) (RatFunc 𝕜))) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨q, rfl⟩
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨q.1, rfl⟩)
    · exact Ideal.zero_mem _
    · intro a b _ _ ha hb
      exact Ideal.add_mem _ ha hb
    · intro c a _ ha
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ ha
  exact hmem F hFspan

end Work.MotAS
