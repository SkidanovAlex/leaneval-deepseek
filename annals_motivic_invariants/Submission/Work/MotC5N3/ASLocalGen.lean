import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.AsRuleRankDefs
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotV5.ASLocal.asKernel6
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASLocalGen` — generic (arbitrary `K`) AS local-coordinate bricks

The `RatFunc 𝕜 ↦ K` forks of the local lemmas used by `Work.MotAS.kerAevalKleinPAS_gen`:
the transport of the split Pfaffians along `asM` (as polynomials in the AS coordinates), the
cancellation `aeval (asM w) ∘ aeval (asMinv w) = id`, and the descent of span membership along
`asM`.  All four are stated for an arbitrary `𝕜`-algebra field `K` of characteristic `5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotC5N3

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The constant embedding `MvPolynomial.C` commutes with the source Galois matrix `asM`
evaluated at `asRoot g`. -/
lemma C_asMA_KbA (g : K) (i j : Fin 5) :
    (MvPolynomial.C (Work.MotAS.asM (asRoot g) i j) :
        MvPolynomial (Fin 5) (KbA K))
      = Work.MotAS.asM (MvPolynomial.C (asRoot g)) i j := by
  simp only [Work.MotAS.asM, Matrix.of_apply, map_pow, map_add, map_natCast]

/-- The constant embedding `MvPolynomial.C` commutes with the target Galois matrix `asN`
evaluated at `asRoot g`. -/
lemma C_asNA_KbA (g : K) (k j : Fin 5) :
    (MvPolynomial.C (Work.MotAS.asN (asRoot g) k j) :
        MvPolynomial (Fin 5) (KbA K))
      = Work.MotAS.asN (MvPolynomial.C (asRoot g)) k j := by
  simp only [Work.MotAS.asN, Matrix.of_apply, map_pow, map_add, map_natCast, map_mul, map_ofNat]

/-- `MvPolynomial.aeval` commutes with the Pfaffian `kleinP` in the coordinates `X i`. -/
lemma aeval_kleinP_X_KbA (a b : KbA K)
    (σ : Fin 5 → MvPolynomial (Fin 5) (KbA K)) (k : Fin 5) :
    MvPolynomial.aeval σ (Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
        (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b) σ k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Work.MotK.fin5_zero, Work.MotK.fin5_one,
      Work.MotK.fin5_two, Work.MotK.fin5_three, Work.MotK.fin5_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, map_add, map_sub, map_mul, map_pow, map_neg]

/-- The transported Pfaffians as polynomials: the image of the split Klein Pfaffian under the
source Galois substitution `x_i = Σ_j X_j (w+i)^j` is the `asN`-combination of the transported
Pfaffians `kleinPAS`. -/
theorem asTransportP_mv_A (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    MvPolynomial.aeval
        (fun i : Fin 5 => ∑ j : Fin 5,
          MvPolynomial.C (Work.MotAS.asM (asRoot g) i j) * MvPolynomial.X j)
        (Work.MotK.kleinP (MvPolynomial.C (aK (KbA K) D))
          (MvPolynomial.C (bK (KbA K) D))
          (fun i => MvPolynomial.X i) k)
      = ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asN (asRoot g) k j)
          * Work.MotAS.kleinPASm (aK (KbA K) D) (bK (KbA K) D)
              (algebraMap K (KbA K) g) j := by
  have h5 : (5 : MvPolynomial (Fin 5) (KbA K)) = 0 := CharP.cast_eq_zero _ 5
  have hw : (MvPolynomial.C (asRoot g) : MvPolynomial (Fin 5) (KbA K)) ^ 5
      = MvPolynomial.C (asRoot g)
        + MvPolynomial.C (algebraMap K (KbA K) g) := by
    rw [← map_pow, ← map_add]
    congr 1
    have h := asRoot_spec g
    linear_combination (norm := first | refl_ring1 | ring1) h
  set σ : Fin 5 → MvPolynomial (Fin 5) (KbA K) :=
      fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (asRoot g) i j) * MvPolynomial.X j with hσ
  have hstep : MvPolynomial.aeval σ
        (Work.MotK.kleinP (MvPolynomial.C (aK (KbA K) D))
          (MvPolynomial.C (bK (KbA K) D))
          (fun i => MvPolynomial.X i) k)
      = Work.MotK.kleinP (MvPolynomial.C (aK (KbA K) D))
          (MvPolynomial.C (bK (KbA K) D)) σ k :=
    aeval_kleinP_X_KbA _ _ σ k
  have hσ' : σ = fun i : Fin 5 => ∑ j : Fin 5,
      Work.MotAS.asM (MvPolynomial.C (asRoot g)) i j * MvPolynomial.X j := by
    funext i
    simp only [hσ, C_asMA_KbA]
  have htr := Work.MotAS.asTransportP
      (MvPolynomial.C (aK (KbA K) D))
      (MvPolynomial.C (bK (KbA K) D))
      (MvPolynomial.C (algebraMap K (KbA K) g))
      (MvPolynomial.C (asRoot g)) h5 hw (fun i => MvPolynomial.X i)
  rw [hstep, hσ', htr, Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [C_asNA_KbA g]
  rfl

/-- `aeval (asM w) ∘ aeval (asMinv w) = id` on `MvPolynomial (Fin 5) (KbA K)`. -/
theorem aevalAsMAevalAsMinv_A (w : KbA K) (p : MvPolynomial (Fin 5) (KbA K)) :
    MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j) p) = p := by
  have h5 : (5 : KbA K) = 0 := CharP.cast_eq_zero (KbA K) 5
  have hcomp : (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)).comp
      (MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
        MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j))
      = AlgHom.id (KbA K) (MvPolynomial (Fin 5) (KbA K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.aeval_X]
    have hterm : ∀ x : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i x) *
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w x j) * MvPolynomial.X j)
        = ∑ j : Fin 5,
            MvPolynomial.C (Work.MotAS.asMinv w i x * Work.MotAS.asM w x j) * MvPolynomial.X j := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, ← map_mul]
    rw [show MvPolynomial.aeval (fun i : Fin 5 => ∑ j : Fin 5,
          MvPolynomial.C (Work.MotAS.asM w i j) * MvPolynomial.X j)
        (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i j) * MvPolynomial.X j)
        = ∑ x : Fin 5, MvPolynomial.C (Work.MotAS.asMinv w i x) *
            (∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asM w x j) * MvPolynomial.X j) from ?_]
    · rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_comm]
      have hj : ∀ j : Fin 5, (∑ x : Fin 5,
            MvPolynomial.C (Work.MotAS.asMinv w i x * Work.MotAS.asM w x j) * MvPolynomial.X j)
          = MvPolynomial.C ((Work.MotAS.asMinv w * Work.MotAS.asM w) i j) * MvPolynomial.X j := by
        intro j
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun j _ => hj j), Work.MotAS.asMinv_mul_asM h5 w]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, map_one, one_mul]
      · intro j _ hjne
        rw [Matrix.one_apply_ne (Ne.symm hjne), map_zero, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  exact congrArg (fun f => f p) hcomp

/-- The `asM`-substitution of the degree-`n` part of the split Klein ideal lies in the degree-`n`
part of the transported ideal. -/
theorem aeval_asM_twIdeal_subset_A (D : Work.MotV.KleinData 𝕜) (g : K) (n : ℕ)
    {f : MvPolynomial (Fin 5) (KbA K)}
    (hf : f ∈ Submodule.span (KbA K)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotK.kleinP (MvPolynomial.C (aK (KbA K) D))
          (MvPolynomial.C (bK (KbA K) D))
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1))) :
    MvPolynomial.aeval (fun i : Fin 5 => ∑ l : Fin 5,
        MvPolynomial.C (Work.MotAS.asM (asRoot g) i l) * MvPolynomial.X l) f
      ∈ Submodule.span (KbA K)
        (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
          Work.MotAS.kleinPASm (aK (KbA K) D) (bK (KbA K) D)
            (algebraMap K (KbA K) g) q.1 * MvPolynomial.monomial q.2.1 1)) := by
  classical
  set χ : MvPolynomial (Fin 5) (KbA K) →ₐ[KbA K] MvPolynomial (Fin 5) (KbA K) :=
    MvPolynomial.aeval (fun i => ∑ l, MvPolynomial.C
      (Work.MotAS.asM (asRoot g) i l) * MvPolynomial.X l) with hχ
  set T : Submodule (KbA K) (MvPolynomial (Fin 5) (KbA K)) :=
    Submodule.span (KbA K)
      (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = n - 2} =>
        Work.MotAS.kleinPASm (aK (KbA K) D) (bK (KbA K) D)
          (algebraMap K (KbA K) g) q.1 * MvPolynomial.monomial q.2.1 1)) with hT
  set Pm : Submodule (KbA K) (MvPolynomial (Fin 5) (KbA K)) :=
    Submodule.span (KbA K)
      (Set.range (fun m' : {m' : Fin 5 →₀ ℕ // m'.support.sum m' = n - 2} =>
        MvPolynomial.monomial m'.1 1)) with hPm
  have hsub : ∀ i : Fin 5, ((fun i : Fin 5 => ∑ l : Fin 5, MvPolynomial.C
      (Work.MotAS.asM (asRoot g) i l) * MvPolynomial.X l) i).IsHomogeneous 1 := by
    intro i
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun l => MvPolynomial.C
      (Work.MotAS.asM (asRoot g) i l) * MvPolynomial.X l) 1
      (fun l _ => (MvPolynomial.isHomogeneous_X (R := KbA K) l).C_mul _)
  have hkin : ∀ (j : Fin 5) {f' : MvPolynomial (Fin 5) (KbA K)},
      f' ∈ Pm → Work.MotAS.kleinPASm (aK (KbA K) D) (bK (KbA K) D)
          (algebraMap K (KbA K) g) j * f' ∈ T := by
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
    have hk : χ (Work.MotK.kleinP (MvPolynomial.C (aK (KbA K) D))
          (MvPolynomial.C (bK (KbA K) D))
          (fun i => MvPolynomial.X i) q.1)
        = ∑ j : Fin 5, MvPolynomial.C (Work.MotAS.asN (asRoot g) q.1 j)
            * Work.MotAS.kleinPASm (aK (KbA K) D)
                (bK (KbA K) D)
                (algebraMap K (KbA K) g) j := by
      rw [hχ]
      exact asTransportP_mv_A D g q.1
    have hmon : χ (MvPolynomial.monomial q.2.1 (1 : KbA K)) ∈ Pm := by
      have hhom : (MvPolynomial.monomial q.2.1 (1 : KbA K)).IsHomogeneous (n - 2) := by
        apply MvPolynomial.isHomogeneous_monomial
        rw [Finsupp.degree_apply]
        exact q.2.2
      have hχhom : (χ (MvPolynomial.monomial q.2.1 (1 : KbA K))).IsHomogeneous (n - 2) := by
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

end Work.MotC5N3
