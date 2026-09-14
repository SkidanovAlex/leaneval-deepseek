import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.FieldTheory.NumberField.exists_rat_combination_adjoin_eq_top
import Submission.Commons.Algebra.MvPolynomial.eval_sum_trace_pow
import Submission.Commons.Algebra.MvPolynomial.totalDegree_det_le

namespace Commons.RingTheory.Polynomial

open MvPolynomial

set_option linter.style.haveILetI false

/-- If `y` generates `M` over `ℚ`, then the discriminant of the powers of `y` is nonzero. -/
theorem discr_ne_zero_of_adjoin_singleton_eq_top_aux {M : Type*} [Field M] [NumberField M] {y : M}
    (h : Algebra.adjoin ℚ ({y} : Set M) = ⊤) :
    Algebra.discr ℚ (fun p : Fin (Module.finrank ℚ M) => y ^ (p : ℕ)) ≠ 0 := by
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  let pb := Algebra.adjoin.powerBasis hint
  have hdim1 : pb.dim = (minpoly ℚ y).natDegree := Algebra.adjoin.powerBasis_dim hint
  have htop : IntermediateField.adjoin ℚ ({y} : Set M) = ⊤ :=
    IntermediateField.adjoin_eq_top_iff.mpr h
  have hfin : Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({y} : Set M)) =
      Module.finrank ℚ M := by
    rw [htop]; exact finrank_top ℚ M
  have hmin : (minpoly ℚ y).natDegree = Module.finrank ℚ M := by
    rw [← IntermediateField.adjoin.finrank hint]; exact hfin
  have hdim : pb.dim = Module.finrank ℚ M := hdim1.trans hmin
  let ee : ↥(Algebra.adjoin ℚ ({y} : Set M)) ≃ₐ[ℚ] M :=
    (Subalgebra.equivOfEq _ _ h).trans Subalgebra.topEquiv
  let pbL := pb.map ee
  have hgen : pbL.gen = y := by
    rw [PowerBasis.map_gen]
    simp [ee, pb]
  have hdimL : pbL.dim = Module.finrank ℚ M := by
    rw [PowerBasis.map_dim]; exact hdim
  have hd : Algebra.discr ℚ (fun i : Fin pbL.dim => y ^ (i : ℕ)) ≠ 0 := by
    have heqfun : (fun i : Fin pbL.dim => y ^ (i : ℕ)) = ⇑pbL.basis := by
      funext i; rw [PowerBasis.basis_eq_pow, hgen]
    rw [heqfun]
    exact Algebra.discr_not_zero_of_basis ℚ pbL.basis
  rw [← hdimL]
  exact hd

/-- The trace polynomial: the value at `μ` is `trace ℚ L ((∑_i μ_i x_i)^k)`. -/
noncomputable def trPoly {L : Type*} [Field L] [Algebra ℚ L] {ι : Type*} [Fintype ι]
    (x : ι → L) (k : ℕ) : MvPolynomial ι ℚ :=
  ∑ f : Fin k → ι, (∏ j : Fin k, MvPolynomial.X (f j)) *
    MvPolynomial.C (Algebra.trace ℚ L (∏ j : Fin k, x (f j)))

lemma trPoly_totalDegree_le {L : Type*} [Field L] [Algebra ℚ L] {ι : Type*} [Fintype ι]
    (x : ι → L) (k : ℕ) : (trPoly x k).totalDegree ≤ k := by
  rw [trPoly]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro f _
  calc ((∏ j : Fin k, MvPolynomial.X (f j)) *
        MvPolynomial.C (Algebra.trace ℚ L (∏ j : Fin k, x (f j)))).totalDegree
      ≤ (∏ j : Fin k, MvPolynomial.X (f j)).totalDegree +
          (MvPolynomial.C (Algebra.trace ℚ L (∏ j : Fin k, x (f j)))).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ (∑ j : Fin k, (MvPolynomial.X (f j)).totalDegree) + 0 := by
        gcongr
        · exact MvPolynomial.totalDegree_finsetProd _ _
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
    _ = k := by simp

lemma trPoly_eval {L : Type*} [Field L] [Algebra ℚ L] {ι : Type*} [Fintype ι]
    (x : ι → L) (k : ℕ) (μ : ι → ℚ) :
    MvPolynomial.eval μ (trPoly x k) = Algebra.trace ℚ L ((∑ i, μ i • x i) ^ k) :=
  Commons.Algebra.MvPolynomial.eval_sum_trace_pow x k μ

/-- The discriminant polynomial: its value at `a` is `discr ℚ (powers of ∑ a_i x_i)`. -/
noncomputable def discPoly {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι]
    (x : ι → L) : MvPolynomial ι ℚ :=
  (Matrix.of fun p q : Fin (Module.finrank ℚ L) => trPoly x ((p : ℕ) + (q : ℕ))).det

lemma discPoly_totalDegree_le {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι]
    (x : ι → L) :
    (discPoly x).totalDegree ≤ (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) := by
  rw [discPoly]
  apply Commons.Algebra.MvPolynomial.totalDegree_det_le
  intro p q
  exact trPoly_totalDegree_le x ((p : ℕ) + (q : ℕ))

lemma discPoly_eval {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι]
    (x : ι → L) (a : ι → ℚ) :
    MvPolynomial.eval a (discPoly x) =
      Algebra.discr ℚ (fun p : Fin (Module.finrank ℚ L) => (∑ i, a i • x i) ^ (p : ℕ)) := by
  rw [discPoly, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, trPoly_eval]
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, ← pow_add]

/-- If the discriminant of the powers of `y` is nonzero, then `y` generates. -/
theorem adjoin_singleton_eq_top_of_discr_ne_zero {L : Type*} [Field L] [NumberField L] {y : L}
    (h : Algebra.discr ℚ (fun p : Fin (Module.finrank ℚ L) => y ^ (p : ℕ)) ≠ 0) :
    Algebra.adjoin ℚ ({y} : Set L) = ⊤ := by
  have hli : LinearIndependent ℚ (fun p : Fin (Module.finrank ℚ L) => y ^ (p : ℕ)) := by
    by_contra hc
    exact h (Algebra.discr_zero_of_not_linearIndependent ℚ hc)
  haveI : Nonempty (Fin (Module.finrank ℚ L)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (Fintype.card_fin _)
  have hle : Submodule.span ℚ (Set.range (fun p : Fin (Module.finrank ℚ L) => y ^ (p : ℕ))) ≤
      (Algebra.adjoin ℚ ({y} : Set L)).toSubmodule := by
    rw [Submodule.span_le]
    rintro z ⟨p, rfl⟩
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton y)) (p : ℕ)
  rw [hspan] at hle
  rw [eq_top_iff]
  intro z _
  exact hle Submodule.mem_top

theorem exists_adjoin_single_sum_bounded {L : Type*} [Field L] [NumberField L] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (x : ι → L) (hgen : Algebra.adjoin ℚ (Set.range x) = ⊤)
    (j₀ : ι) :
    ∃ μ : ι → ℕ, μ j₀ ≠ 0 ∧ (∀ i : ι, μ i ≤ (Module.finrank ℚ L) ^ 2 + 1) ∧
      Algebra.adjoin ℚ {∑ i, ((μ i : ℕ) : L) * x i} = ⊤ := by
  classical
  obtain ⟨a, ha⟩ := Commons.FieldTheory.NumberField.exists_rat_combination_adjoin_eq_top x hgen
  haveI : Finite ι := Finite.of_fintype ι
  -- the discriminant polynomial is nonzero
  have hDiscNe : discPoly x ≠ 0 := by
    intro hz
    have h1 : MvPolynomial.eval a (discPoly x) = 0 := by rw [hz, map_zero]
    rw [discPoly_eval] at h1
    exact discr_ne_zero_of_adjoin_singleton_eq_top_aux ha h1
  -- the grid
  let c : ι → ℕ := fun i => if i = j₀ then 1 else 0
  let S : ι → Finset ℚ := fun i =>
    (Finset.range ((Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) + 1)).image
      (fun m : ℕ => ((m + c i : ℕ) : ℚ))
  have hcard : ∀ i, (S i).card = (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) + 1 := by
    intro i
    simp only [S]
    rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro m m' hmm
    have h2 : m + c i = m' + c i := Nat.cast_injective hmm
    exact Nat.add_right_cancel h2
  have hdeg : ∀ i, MvPolynomial.degreeOf i (discPoly x) < (S i).card := by
    intro i
    rw [hcard i]
    have h1 : MvPolynomial.degreeOf i (discPoly x) ≤ (discPoly x).totalDegree :=
      MvPolynomial.degreeOf_le_totalDegree _ _
    have h2 : (discPoly x).totalDegree ≤ (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) :=
      discPoly_totalDegree_le x
    exact Nat.lt_succ_of_le (le_trans h1 h2)
  have hex : ∃ a' : ι → ℚ, (∀ i, a' i ∈ S i) ∧ MvPolynomial.eval a' (discPoly x) ≠ 0 := by
    by_contra h
    apply hDiscNe
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (discPoly x) S hdeg ?_
    intro a' ha'
    by_contra hq
    exact h ⟨a', ha', hq⟩
  obtain ⟨a', ha', hne'⟩ := hex
  choose m hm using fun i => Finset.mem_image.mp (ha' i)
  refine ⟨fun i => m i + c i, ?_, ?_, ?_⟩
  · have hcj : c j₀ = 1 := by simp [c]
    change m j₀ + c j₀ ≠ 0
    rw [hcj]; omega
  · intro i
    change m i + c i ≤ (Module.finrank ℚ L) ^ 2 + 1
    have h1 : m i < (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) + 1 :=
      Finset.mem_range.mp (hm i).1
    have h2 : c i ≤ 1 := by simp only [c]; split <;> omega
    have hmul : (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1) ≤ (Module.finrank ℚ L) ^ 2 := by
      calc (Module.finrank ℚ L) * ((Module.finrank ℚ L) - 1)
          ≤ (Module.finrank ℚ L) * (Module.finrank ℚ L) :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (Module.finrank ℚ L) ^ 2 := by ring
    omega
  · have hae : (fun i => (((m i + c i : ℕ)) : ℚ)) = a' := by
      funext i; exact (hm i).2
    have hne2 : MvPolynomial.eval (fun i => (((m i + c i : ℕ)) : ℚ)) (discPoly x) ≠ 0 := by
      rw [hae]; exact hne'
    rw [discPoly_eval] at hne2
    have hadj := adjoin_singleton_eq_top_of_discr_ne_zero hne2
    have hsum : (∑ i, (((m i + c i : ℕ)) : ℚ) • x i) =
        ∑ i, ((((m i + c i : ℕ)) : L)) * x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_natCast]
    rw [hsum] at hadj
    exact hadj

end Commons.RingTheory.Polynomial