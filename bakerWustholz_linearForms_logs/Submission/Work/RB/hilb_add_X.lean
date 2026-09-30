import Mathlib
import Submission.Work.RB.Defs
import Submission.Work.RB.finrank_quotient_eq_add_finrank_map
import Submission.Work.BW.weightedHomogeneousComponent_mul_of_mem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dimension identity `dim (R/I)_{d + w v} = dim (R/J)_{d + w v} + dim (R/I'')_d`

With `R = MvPolynomial σ ℂ` graded by a weight function `w : σ → ℕ^n`, `I` a `w`-homogeneous
ideal, `J = I + (X v)` and `I'' = (I : X v)`, the multiplication-by-`X v` map fits into the exact
sequence of graded `ℂ`-vector spaces
`(R/I)_d --X v--> (R/I)_{d + w v} → (R/J)_{d + w v} → 0`
whose kernel on `(R/I)_d` is `(I''/I)_d`.  Taking dimensions gives the stated identity.

The key point is that `X v` acts on graded pieces the way multiplication by a variable must: every
element of `(R/I)_{d + w v}` lying in `J/I` is the image of `X v` on `(R/I)_d` (this is
`exists_sub_mul_X_mem_of_mem`, a consequence of multiplicativity of weighted homogeneous
components).
-/

set_option linter.style.haveILetI false

namespace Work.RB

open MvPolynomial

noncomputable section

variable {n : ℕ} {σ : Type*} [Fintype σ]


/-- The `i`-th coordinate of the weighted degree of `D` is `∑ v, D v * (w v) i`. -/
lemma weight_apply_coord (w : σ → Fin n →₀ ℕ) (D : σ →₀ ℕ) (i : Fin n) :
    (Finsupp.weight w D) i = ∑ v, D v * (w v) i := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply']
  exact Finset.sum_congr rfl fun v _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- Summing the coordinates of the weighted degree `weight w D` gives the `ℕ`-weight of `D`
with respect to `v ↦ ∑ i, w v i`. -/
lemma weight_sum_coord (w : σ → Fin n →₀ ℕ) (D : σ →₀ ℕ) :
    Finsupp.weight (fun v => ∑ i, (w v) i) D = ∑ i, (Finsupp.weight w D) i := by
  have h1 : Finsupp.weight (fun v => ∑ i, (w v) i) D = ∑ v, ∑ i, D v * (w v) i := by
    rw [Finsupp.weight_eq_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  have h2 : ∑ i, (Finsupp.weight w D) i = ∑ i, ∑ v, D v * (w v) i :=
    Finset.sum_congr rfl fun i _ => weight_apply_coord w D i
  rw [h1, h2, Finset.sum_comm]

/-- Every weighted homogeneous piece is finite dimensional over `ℂ` when no variable has
weight `0`. -/
theorem homPiece_moduleFinite_aux {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ)
    (hw : ∀ v : σ, w v ≠ 0) (d : Fin n →₀ ℕ) :
    Module.Finite ℂ ↥(homPiece w d) := by
  have hW0 : ∀ v, (∑ i, (w v) i) ≠ 0 := by
    intro v hv
    refine hw v (Finsupp.ext fun i => ?_)
    exact (Finset.sum_eq_zero_iff.mp hv) i (Finset.mem_univ i)
  have hfin : ({(D : σ →₀ ℕ) | Finsupp.weight w D = d}).Finite := by
    refine Set.Finite.subset (Finsupp.finite_of_nat_weight_eq (fun v => ∑ i, (w v) i) hW0
      (∑ i, d i)) ?_
    intro D hD
    simp only [Set.mem_ofPred_eq] at hD ⊢
    rw [weight_sum_coord w D, hD]
  rw [homPiece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    ← MvPolynomial.restrictSupport]
  haveI := hfin.to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

/-- Multiplication by the variable `X v`, as a `ℂ`-linear map from the `d`-th multigraded piece
to the `(d + w v)`-th multigraded piece. -/
def mulXv (w : σ → Fin n →₀ ℕ) (v : σ) (d : Fin n →₀ ℕ) :
    homPiece w d →ₗ[ℂ] homPiece w (d + w v) :=
  LinearMap.codRestrict (homPiece w (d + w v))
    ((LinearMap.mulLeft ℂ (MvPolynomial.X v : MvPolynomial σ ℂ)).comp (homPiece w d).subtype)
    (fun p => by
      have hP : MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.X v : MvPolynomial σ ℂ)
          (w v) := MvPolynomial.isWeightedHomogeneous_X ℂ w v
      have hp : MvPolynomial.IsWeightedHomogeneous w ((p : MvPolynomial σ ℂ)) d :=
        (mem_homPiece w d (p : MvPolynomial σ ℂ)).mp p.2
      exact (mem_homPiece w (d + w v) _).mpr (by simpa [add_comm] using hP.mul hp))

@[simp]
lemma mulXv_apply (w : σ → Fin n →₀ ℕ) (v : σ) (d : Fin n →₀ ℕ) (p : homPiece w d) :
    (mulXv w v d p : MvPolynomial σ ℂ) =
      (MvPolynomial.X v : MvPolynomial σ ℂ) * (p : MvPolynomial σ ℂ) :=
  rfl

/-- **Key step.**  If `y` lies in the `(d + w v)`-th graded piece and in `I + (X v)`, then `y` is
congruent modulo `I` to `X v * p` for some `p` in the `d`-th graded piece. -/
theorem exists_sub_mul_X_mem_of_mem (w : σ → Fin n →₀ ℕ) {v : σ}
    {I : Ideal (MvPolynomial σ ℂ)} (hI : IsWHomog w I) (d : Fin n →₀ ℕ)
    {y : MvPolynomial σ ℂ} (hyB : y ∈ homPiece w (d + w v))
    (hyJ : y ∈ I ⊔ Ideal.span {MvPolynomial.X v}) :
    ∃ p : MvPolynomial σ ℂ, p ∈ homPiece w d ∧ y - MvPolynomial.X v * p ∈ I := by
  obtain ⟨i, hi, x, hx, hix⟩ := Submodule.mem_sup.mp hyJ
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨MvPolynomial.weightedHomogeneousComponent w d r,
    MvPolynomial.weightedHomogeneousComponent_mem w r d, ?_⟩
  have hy : y = i + MvPolynomial.X v * r := hix.symm
  have hX : MvPolynomial.X v ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ w (w v) :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ w (w v) _).mpr
      (MvPolynomial.isWeightedHomogeneous_X ℂ w v)
  have hcomp := Work.BW.weightedHomogeneousComponent_mul_of_mem (R := ℂ) hX r d
  have hπy : MvPolynomial.weightedHomogeneousComponent w (d + w v) y = y :=
    MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same
      ((mem_homPiece w (d + w v) y).mp hyB)
  have hy' : y = MvPolynomial.weightedHomogeneousComponent w (d + w v) i +
      MvPolynomial.X v * MvPolynomial.weightedHomogeneousComponent w d r := by
    rw [hπy.symm, hy, map_add, hcomp]
  have hsub : y - MvPolynomial.X v * MvPolynomial.weightedHomogeneousComponent w d r =
      MvPolynomial.weightedHomogeneousComponent w (d + w v) i := by
    rw [hy']; abel
  rw [hsub]
  exact hI i hi (d + w v)

theorem hilb_add_X {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ)
    (hw : ∀ v : σ, w v ≠ 0) {v : σ}
    (I : Ideal (MvPolynomial σ ℂ)) (hI : IsWHomog w I) (d : Fin n →₀ ℕ) :
    hilb w I (d + w v) =
      hilb w (I ⊔ Ideal.span {MvPolynomial.X v}) (d + w v) +
        hilb w (Submodule.colon (I : Submodule (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
          ({MvPolynomial.X v} : Set (MvPolynomial σ ℂ))) d := by
  have hfinB : Module.Finite ℂ ↥(homPiece w (d + w v)) :=
    homPiece_moduleFinite_aux w hw (d + w v)
  simp only [hilb]
  set J : Ideal (MvPolynomial σ ℂ) := I ⊔ Ideal.span {MvPolynomial.X v} with hJ
  set P : Submodule ℂ ↥(homPiece w (d + w v)) :=
    Submodule.comap (homPiece w (d + w v)).subtype (I.restrictScalars ℂ) with hP
  set Q : Submodule ℂ ↥(homPiece w (d + w v)) :=
    Submodule.comap (homPiece w (d + w v)).subtype (J.restrictScalars ℂ) with hQ
  set I'' : Ideal (MvPolynomial σ ℂ) :=
    Submodule.colon (I : Submodule (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
      ({MvPolynomial.X v} : Set (MvPolynomial σ ℂ)) with hI''
  set P' : Submodule ℂ ↥(homPiece w d) :=
    Submodule.comap (homPiece w d).subtype (I''.restrictScalars ℂ) with hP'
  have hle : P ≤ Q := by
    intro x hx
    rw [hP, Submodule.mem_comap, Submodule.restrictScalars_mem] at hx
    rw [hQ, Submodule.mem_comap, Submodule.restrictScalars_mem, hJ]
    exact Submodule.mem_sup_left hx
  set ψ : ↥(homPiece w d) →ₗ[ℂ] (↥(homPiece w (d + w v)) ⧸ P) :=
    P.mkQ.comp (mulXv w v d) with hψ
  have hker : ψ.ker = P' := by
    rw [hψ, hP', hI'', hP]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.restrictScalars_mem, Submodule.mem_colon_singleton, smul_eq_mul, mulXv_apply]
    constructor <;> intro h <;> rwa [mul_comm] at h
  have hrange : ψ.range = Submodule.map P.mkQ Q := by
    rw [hψ, LinearMap.range_comp]
    refine le_antisymm ?_ ?_
    · apply Submodule.map_mono
      intro z hz
      rw [LinearMap.mem_range] at hz
      obtain ⟨p, rfl⟩ := hz
      rw [hQ, hJ]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem,
        mulXv_apply]
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨p, rfl⟩)
    · intro z hz
      obtain ⟨y, hyQ, hyz⟩ := Submodule.mem_map.mp hz
      rw [← hyz]
      have hyJ : (y : MvPolynomial σ ℂ) ∈ I ⊔ Ideal.span {MvPolynomial.X v} := by
        rw [hQ, Submodule.mem_comap, Submodule.restrictScalars_mem, hJ] at hyQ
        exact hyQ
      obtain ⟨p, hpA, hpI⟩ := exists_sub_mul_X_mem_of_mem w hI d y.2 hyJ
      refine Submodule.mem_map.mpr ⟨mulXv w v d ⟨p, hpA⟩, ?_, ?_⟩
      · exact LinearMap.mem_range.mpr ⟨⟨p, hpA⟩, rfl⟩
      · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP]
        simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.subtype_apply]
        have h' : (MvPolynomial.X v : MvPolynomial σ ℂ) * p - y ∈ I := by
          have := neg_mem hpI
          rwa [neg_sub] at this
        simpa using h'
  have key1 := finrank_quotient_eq_add_finrank_map (K := ℂ)
    (V := ↥(homPiece w (d + w v))) hle
  have key2 : Module.finrank ℂ (Submodule.map P.mkQ Q) =
      Module.finrank ℂ (↥(homPiece w d) ⧸ P') := by
    rw [← hrange, ← hker]
    exact (LinearEquiv.finrank_eq ψ.quotKerEquivRange).symm
  rw [key1, key2]

end

end Work.RB
