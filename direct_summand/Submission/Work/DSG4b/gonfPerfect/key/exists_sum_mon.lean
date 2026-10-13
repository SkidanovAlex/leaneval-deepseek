import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic

/-!
# Spanning of a stage `AN D N` by reduced monomials

Every element of `D.AN N = R[T_j : j ∈ Λ] ⧸ (T_j^{p^N} - b̃_j)` is an `R`-linear combination of the
classes `D.mon N e` of the reduced monomials `e : Λ →₀ ℕ` with entries `< p ^ N`.

The proof uses the "normal form" retraction `RFAux.redLin (D.fN N)` of
`Submission.Work.DSG4b.rootLocal_flat`: it kills the relation ideal `RFAux.qI (D.fN N)`
(`RFAux.sub_redLin_mem_qI`) and its values lie in the span of the reduced monomials
(`RFAux.redLin_mem_qVd`, since `(D.fN N b).natDegree = p ^ N`).  Given `a = mk x`, the element
`redLin (D.fN N) x` is a finite `R`-linear combination of reduced monomials and differs from `x` by
an element of the relation ideal, hence has the same image in the quotient.
-/

namespace Work.DSG4b.gonfPerfect.key

open MvPolynomial Polynomial

/-- The relation polynomial `T ^ (p ^ N) - b̃_j` is monic. -/
lemma fN_monic (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) (b : D.pB) :
    (D.fN N b).Monic := by
  rw [PData.fN_apply]
  exact monic_X_pow_sub_C _ (pow_ne_zero N (Fact.out : p.Prime).ne_zero)

/-- The relation polynomial `T ^ (p ^ N) - b̃_j` is not the unit polynomial. -/
lemma fN_ne_one (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) (b : D.pB) :
    D.fN N b ≠ 1 := by
  intro h
  have h1 : (D.fN N b).natDegree = p ^ N := by
    rw [PData.fN_apply]
    exact natDegree_X_pow_sub_C
  rw [h, Polynomial.natDegree_one] at h1
  exact (pow_ne_zero N (Fact.out : p.Prime).ne_zero) h1.symm

/-- `natDegree (T ^ (p ^ N) - b̃_j) = p ^ N`. -/
lemma fN_natDegree (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) (b : D.pB) :
    (D.fN N b).natDegree = p ^ N := by
  rw [PData.fN_apply]
  exact natDegree_X_pow_sub_C

/-- An element of the span of the range of a family is a finite linear combination of that
family. -/
lemma exists_finsupp_of_mem_span_range {R : Type*} [CommRing R] {ι : Type*} {M : Type*}
    [AddCommMonoid M] [Module R M] {v : ι → M} {x : M}
    (hx : x ∈ Submodule.span R (Set.range v)) :
    ∃ c : ι →₀ R, ∑ i ∈ c.support, c i • v i = x := by
  have key : ∀ y ∈ Submodule.span R (Set.range v), ∃ c : ι →₀ R,
      Finsupp.linearCombination R v c = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨Finsupp.single i 1, by rw [Finsupp.linearCombination_single, one_smul]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add y z hy hz ihy ihz =>
        obtain ⟨c, hc⟩ := ihy
        obtain ⟨d, hd⟩ := ihz
        exact ⟨c + d, by rw [map_add, hc, hd]⟩
    | smul a y hy ih =>
        obtain ⟨c, hc⟩ := ih
        exact ⟨a • c, by rw [map_smul, hc]⟩
  obtain ⟨c, hc⟩ := key x hx
  exact ⟨c, by rw [← hc, Finsupp.linearCombination_apply]; rfl⟩

/-- The image in `D.AN N` of an element of the span of the reduced monomials is an `R`-linear
combination of the classes `D.mon N e`. -/
lemma exists_sum_mon_of_mem_qVd (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) {y : MvPolynomial D.pB R}
    (hy : y ∈ RFAux.qVd (fun _ : D.pB => p ^ N)) :
    ∃ (s : Finset (D.Idx N)) (r : D.Idx N → R),
      Ideal.Quotient.mk (RFAux.qI (D.fN N)) y =
        ∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e := by
  classical
  obtain ⟨c, hc⟩ := exists_finsupp_of_mem_span_range (R := R) (M := MvPolynomial D.pB R)
    (v := fun m : D.Idx N => (MvPolynomial.monomial m.1 1 : MvPolynomial D.pB R)) hy
  refine ⟨c.support, fun e => c e, ?_⟩
  rw [← hc, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem exists_sum_mon (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) (a : D.AN N) :
    ∃ (s : Finset (D.Idx N)) (r : D.Idx N → R),
      ∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e = a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := RFAux.qI (D.fN N)) a
  have hy : RFAux.redLin (D.fN N) x ∈ RFAux.qVd (fun _ : D.pB => p ^ N) := by
    have h := RFAux.redLin_mem_qVd (f := D.fN N) (fun b => fN_monic R p D N b)
      (fun b => fN_ne_one R p D N b) x
    rwa [show (fun s : D.pB => (D.fN N s).natDegree) = (fun _ : D.pB => p ^ N) from
      funext fun s => fN_natDegree R p D N s] at h
  obtain ⟨s, r, hs⟩ := exists_sum_mon_of_mem_qVd R p D N hy
  refine ⟨s, r, ?_⟩
  rw [← hs]
  exact (Ideal.Quotient.eq.mpr (RFAux.sub_redLin_mem_qI (f := D.fN N) x)).symm

end Work.DSG4b.gonfPerfect.key
