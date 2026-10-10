import Mathlib
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotV5.ASLocal.asKernel6
import Submission.Work.MotAS.Ker4.asTransportP_mv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

theorem aeval_asM_twIdeal_subset (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (n : ℕ)
    {f : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)}
    (hf : f ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1))) :
    MvPolynomial.aeval (fun i : Fin 5 => ∑ l : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) f
      ∈ Submodule.span (Work.MotV.Kb 𝕜)
        (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
          Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
            (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)
            q.1 * MvPolynomial.monomial q.2.1 1)) := by
  classical
  set χ : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) →ₐ[Work.MotV.Kb 𝕜]
      MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜) :=
    MvPolynomial.aeval (fun i => ∑ l, MvPolynomial.C
      (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) with hχ
  set T : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
    Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)
          q.1 * MvPolynomial.monomial q.2.1 1)) with hT
  set Pm : Submodule (Work.MotV.Kb 𝕜) (MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)) :=
    Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (fun m' : {m' : Fin 5 →₀ ℕ // m'.support.sum m' = n - 2} =>
        MvPolynomial.monomial m'.1 1)) with hPm
  have hsub : ∀ i : Fin 5, ((fun i : Fin 5 => ∑ l : Fin 5, MvPolynomial.C
      (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) i).IsHomogeneous 1 := by
    intro i
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun l => MvPolynomial.C
      (Work.MotAS.asM (Work.MotV5.asRoot g) i l) * MvPolynomial.X l) 1
      (fun l _ => (MvPolynomial.isHomogeneous_X (R := Work.MotV.Kb 𝕜) l).C_mul _)
  have hkin : ∀ (j : Fin 5) {f' : MvPolynomial (Fin 5) (Work.MotV.Kb 𝕜)},
      f' ∈ Pm → Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
          (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)
          j * f' ∈ T := by
    intro j f' hf'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf'
    · rintro x ⟨m', rfl⟩
      exact Submodule.subset_span ⟨(j, m'), rfl⟩
    · rw [mul_zero]; exact T.zero_mem
    · intro x y _ _ ihx ihy
      rw [mul_add]; exact T.add_mem ihx ihy
    · rintro a x _ ih
      rw [MvPolynomial.smul_eq_C_mul, mul_left_comm, ← MvPolynomial.smul_eq_C_mul]
      exact T.smul_mem a ih
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro z ⟨q, rfl⟩
    rw [map_mul]
    have hk : χ (Work.MotK.kleinP (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a))
          (MvPolynomial.C (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b))
          (fun i => MvPolynomial.X i) q.1)
        = ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asN (Work.MotV5.asRoot g) q.1 j)
            * Work.MotAS.kleinPASm (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
                (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
                (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g) j := by
      rw [hχ]
      exact Work.MotAS.Ker4.asTransportP_mv 𝕜 D g q.1
    have hmon : χ (MvPolynomial.monomial q.2.1 (1 : Work.MotV.Kb 𝕜)) ∈ Pm := by
      have hhom : (MvPolynomial.monomial q.2.1 (1 : Work.MotV.Kb 𝕜)).IsHomogeneous (n - 2) := by
        apply MvPolynomial.isHomogeneous_monomial
        rw [Finsupp.degree_apply]
        exact q.2.2
      have hχhom : (χ (MvPolynomial.monomial q.2.1 (1 : Work.MotV.Kb 𝕜))).IsHomogeneous (n - 2) := by
        rw [hχ]
        exact Work.MotV5.ASLocal.isHomogeneous_aeval_linear _ (n - 2) hhom _ hsub
      exact Work.MotV5.ASLocal.isHomogeneous_mem_span_monomial hχhom
    rw [hk, Finset.sum_mul]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hkin j hmon)
  · rw [map_zero]; exact T.zero_mem
  · intro x y _ _ ihx ihy; rw [map_add]; exact T.add_mem ihx ihy
  · intro c x _ ih; rw [map_smul]; exact T.smul_mem c ih

end Work.MotAS
