import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial Matrix
open scoped BigOperators Matrix

set_option autoImplicit false

noncomputable section

namespace Polynomial

/-- For a monic polynomial `f` of positive degree, `det(sylvesterDeriv f) = Res(f, f')`. -/
lemma det_sylvesterDeriv_eq_resultant_deriv {R : Type*} [CommRing R] {f : R[X]}
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (sylvesterDeriv f).det = f.resultant f.derivative := by
  have hM := sylvesterDeriv_updateRow f hdeg
  have hdet : ((f.derivative.sylvester f (f.natDegree - 1) f.natDegree).det) =
      f.leadingCoeff * (sylvesterDeriv f).det := by
    rw [← hM, Matrix.det_updateRow_smul]
    simp
  rw [hf.leadingCoeff, one_mul] at hdet
  rw [← hdet]
  rw [show (f.derivative.sylvester f (f.natDegree - 1) f.natDegree).det =
      resultant f.derivative f (f.natDegree - 1) f.natDegree by rfl]
  have heven : Even ((f.natDegree - 1) * f.natDegree) := by
    simpa [mul_comm] using Nat.even_mul_pred_self f.natDegree
  rw [resultant_comm, heven.neg_one_pow, one_mul]
  have hd : f.derivative.natDegree ≤ f.natDegree - 1 := by
    exact Nat.le_pred_of_lt (natDegree_derivative_lt (Nat.ne_of_gt hdeg))
  have hred := resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree
      (f.natDegree - 1 - f.derivative.natDegree) le_rfl
  have hdeg' : f.derivative.natDegree + (f.natDegree - 1 - f.derivative.natDegree) = f.natDegree - 1 := by
    omega
  rw [hdeg'] at hred
  rw [hred]
  simp [hf.leadingCoeff]

/-- Discriminant of a monic polynomial of positive degree:
`discr f = (-1)^(n(n-1)/2) * Res(f, f')`. -/
lemma discr_eq_pow_mul_resultant_deriv {R : Type*} [CommRing R] {f : R[X]}
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    discr f = (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.resultant f.derivative := by
  rw [discr]
  rw [det_sylvesterDeriv_eq_resultant_deriv hf hdeg]
  ring

/-- `discr` commutes with injective ring maps, for monic polynomials. -/
lemma discr_map_of_monic {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {f : R[X]} (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  by_cases hdeg : 0 < f.natDegree
  · have hfmon' : (f.map φ).Monic := Monic.map φ hf
    have hdeg' : 0 < (f.map φ).natDegree := by
      rw [natDegree_map_eq_of_injective hφ]
      exact hdeg
    have hrm : (f.map φ).resultant (f.map φ).derivative = φ (f.resultant f.derivative) := by
      rw [derivative_map]
      have h := resultant_map_map f f.derivative f.natDegree f.derivative.natDegree φ
      simpa [natDegree_map_eq_of_injective hφ] using h
    rw [discr_eq_pow_mul_resultant_deriv hfmon' hdeg']
    rw [discr_eq_pow_mul_resultant_deriv hf hdeg]
    rw [hrm]
    rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    congr 1
    rw [natDegree_map_eq_of_injective hφ]
  · have hf1 : f = 1 := (hf.natDegree_eq_zero).mp (Nat.eq_zero_of_not_pos hdeg)
    rw [hf1]
    have hds : discr (1 : S[X]) = 1 := by
      rw [← Polynomial.C_1]
      exact Polynomial.discr_C (1 : S)
    have hdr : discr (1 : R[X]) = 1 := by
      rw [← Polynomial.C_1]
      exact Polynomial.discr_C (1 : R)
    simp [hds, hdr]

variable {K : Type*} [Field K]

/-- derivative of a product of linear factors evaluated at `a i` = product over j≠i of (a i - a j) -/
lemma derivative_prod_X_sub_C_eval {n : ℕ} (a : Fin n → K) (i : Fin n) :
    (∏ j : Fin n, (X - C (a j))).derivative.eval (a i) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j) := by
  classical
  let s : Multiset (Fin n) := (Finset.univ : Finset (Fin n)).val
  have hf : (∏ j : Fin n, (X - C (a j))) = (s.map (fun j => X - C (a j))).prod := by
    exact Finset.prod_eq_multiset_prod _ _
  rw [hf, derivative_prod]
  dsimp [s]
  rw [eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [derivative_X_sub_C, mul_one]
    rw [← Finset.erase_val]
    rw [eval_multiset_prod, Multiset.map_map]
    change (Multiset.map (fun j : Fin n => eval (a i) (X - C (a j))) (Finset.univ.erase i).val).prod =
      ∏ j ∈ (Finset.univ.erase i), (a i - a j)
    rw [← Finset.prod_eq_multiset_prod (Finset.univ.erase i) (fun j => eval (a i) (X - C (a j)))]
    simp
  · intro j hj hji
    simp only [derivative_X_sub_C, mul_one]
    rw [eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨i, ?_, ?_⟩
    · rw [Multiset.mem_erase_of_ne hji.symm]
      simp
    · simp
  · intro hni
    exact absurd (Finset.mem_univ i) hni

lemma prod_X_sub_C_monic {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, (X - C (a i))).Monic := by
  exact monic_prod_of_monic (Finset.univ : Finset (Fin n)) (fun i => X - C (a i))
    (by intro i hi; exact monic_X_sub_C _)

lemma prod_X_sub_C_ne_zero {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, (X - C (a i))) ≠ 0 := (prod_X_sub_C_monic a).ne_zero

lemma prod_X_sub_C_natDegree {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, (X - C (a i))).natDegree = n := by
  rw [natDegree_prod]
  · simp
  · intro i hi
    exact Polynomial.X_sub_C_ne_zero (a i)

/-- Sum of the cardinalities of `Ioi i` over `i : Fin n` is `n(n-1)/2`. -/
lemma sum_card_Ioi (n : ℕ) : (∑ i : Fin n, (Finset.Ioi i).card) = n * (n - 1) / 2 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_range_reflect (fun j : ℕ => j) n]
    rw [Finset.sum_range_id]
  · intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [dif_pos hi', Fin.card_Ioi]

/-- `∏_i ∏_{j ∈ erase i} (a i - a j) = ∏_i ∏_{j ∈ Ioi i} (a i - a j) * (a j - a i)`. -/
lemma prod_erase_sub_eq_prod_Ioi_mul {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j)) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a i - a j) * (a j - a i) := by
  classical
  rw [Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag (α := Fin n) (fun x y : Fin n => a y - a x)]
  refine Finset.prod_congr rfl ?_
  intro i hi
  refine Finset.prod_congr ?_ ?_
  · ext j
    simp
  · intro j hj
    rfl

/-- `∏_i ∏_{j ∈ Ioi i} (a i - a j) * (a j - a i) = (-1)^(Σ |Ioi i|) * ∏_i ∏_{j ∈ Ioi i} (a j - a i)^2`. -/
lemma prod_Ioi_mul_sub_sq {n : ℕ} (a : Fin n → K) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a i - a j) * (a j - a i)) =
      (-1 : K) ^ (∑ i : Fin n, (Finset.Ioi i).card) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a j - a i) ^ 2 := by
  classical
  calc
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a i - a j) * (a j - a i))
        = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, -((a j - a i) ^ 2) := by
          refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
          ring
    _ = ∏ i : Fin n,
          ((-1 : K) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (a j - a i) ^ 2) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          exact Finset.prod_neg (fun j => (a j - a i) ^ 2)
    _ = (-1 : K) ^ (∑ i : Fin n, (Finset.Ioi i).card) *
          ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a j - a i) ^ 2 := by
          rw [Finset.prod_mul_distrib]
          congr 1
          rw [Finset.prod_pow_eq_pow_sum]

/-- Discriminant of a product of linear factors equals product of squared differences. -/
lemma discr_prod_X_sub_C_sq {n : ℕ} (a : Fin n → K) :
    discr (∏ i : Fin n, (X - C (a i))) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a j - a i) ^ 2 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
    rw [← Polynomial.C_1]
    rw [Polynomial.discr_C]
  · have hmon : (∏ i : Fin n, (X - C (a i))).Monic := prod_X_sub_C_monic a
    have hdeg0 : 0 < (∏ i : Fin n, (X - C (a i))).natDegree := by
      rw [prod_X_sub_C_natDegree]
      omega
    let f : K[X] := ∏ i : Fin n, (X - C (a i))
    have hdisc := discr_eq_pow_mul_resultant_deriv (f := f) hmon hdeg0
    have hfres : f.resultant f.derivative =
        ∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j) := by
      have h := resultant_prod_left (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => X - C (a i))
        (g := (∏ i : Fin n, (X - C (a i))).derivative)
        (n := (∏ i : Fin n, (X - C (a i))).derivative.natDegree) (by simp) le_rfl
      dsimp [f]
      calc
        (∏ i : Fin n, (X - C (a i))).resultant (derivative (∏ i : Fin n, (X - C (a i))))
            = (∏ i : Fin n, (X - C (a i))).resultant (derivative (∏ i : Fin n, (X - C (a i))))
                (∏ i : Fin n, (X - C (a i))).natDegree
                (derivative (∏ i : Fin n, (X - C (a i)))).natDegree := rfl
        _ = ∏ i ∈ (Finset.univ : Finset (Fin n)),
              (X - C (a i)).resultant (derivative (∏ i : Fin n, (X - C (a i))))
                (X - C (a i)).natDegree
                (derivative (∏ i : Fin n, (X - C (a i)))).natDegree := by
              simpa using h
        _ = ∏ i ∈ (Finset.univ : Finset (Fin n)),
              (derivative (∏ i : Fin n, (X - C (a i)))).eval (a i) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              simp
        _ = ∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact derivative_prod_X_sub_C_eval a i
    have hn' : f.natDegree = n := by dsimp [f]; rw [prod_X_sub_C_natDegree]
    have hmain : discr f = (-1 : K) ^ (n * (n - 1) / 2) *
        (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j)) := by
      calc
        discr f = (-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.resultant f.derivative := hdisc
        _ = (-1 : K) ^ (n * (n - 1) / 2) * f.resultant f.derivative := by rw [hn']
        _ = (-1 : K) ^ (n * (n - 1) / 2) *
              (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (a i - a j)) := by rw [hfres]
    change discr f = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a j - a i) ^ 2
    rw [hmain, prod_erase_sub_eq_prod_Ioi_mul a, prod_Ioi_mul_sub_sq a]
    rw [sum_card_Ioi n]
    have hc : (-1 : K) ^ (n * (n - 1) / 2) * (-1 : K) ^ (n * (n - 1) / 2) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n * (n - 1) / 2, rfl⟩
    rw [← mul_assoc, hc, one_mul]

end Polynomial

namespace Commons.FieldTheory.Discriminant

/-- For `pb : PowerBasis F S`, the minimal polynomial of `pb.gen`, mapped to the algebraic
closure of `S`, factors as `∏ (X - C (σ pb.gen))` over all embeddings `σ : S →ₐ[F] E`. -/
theorem minpoly_map_eq_prod {F S : Type*} [Field F] [Field S] [Algebra F S]
    {pb : PowerBasis F S} [Algebra.IsSeparable F S]
    (e : Fin pb.dim ≃ (S →ₐ[F] (AlgebraicClosure S))) :
    (minpoly F pb.gen).map (algebraMap F (AlgebraicClosure S)) =
      ∏ i : Fin pb.dim, (X - C (e i pb.gen)) := by
  classical
  let E := AlgebraicClosure S
  let g : E[X] := (minpoly F pb.gen).map (algebraMap F E)
  let Fp : E[X] := ∏ i : Fin pb.dim, (X - C (e i pb.gen))
  have hmon_g : g.Monic := by
    dsimp [g]
    exact Monic.map (algebraMap F E) (minpoly.monic pb.isIntegral_gen)
  have hmon_F : Fp.Monic := by
    dsimp [Fp]
    exact monic_prod_X_sub_C (fun i : Fin pb.dim => e i pb.gen) (Finset.univ)
  have hdegF : Fp.natDegree = pb.dim := by
    dsimp [Fp]
    rw [natDegree_prod]
    · simp
    · intro i hi
      exact X_sub_C_ne_zero (e i pb.gen)
  have hdegG_le : g.natDegree ≤ Fp.natDegree := by
    rw [hdegF]
    dsimp [g]
    rw [natDegree_map_eq_of_injective (algebraMap F E).injective]
    exact le_of_eq pb.natDegree_minpoly
  have hinj : Function.Injective (fun i : Fin pb.dim => e i pb.gen) := by
    intro i j hij
    apply e.injective
    apply pb.algHom_ext
    exact hij
  have hdvd : Fp ∣ g := by
    dsimp [Fp, g]
    refine Fintype.prod_dvd_of_coprime (s := fun i : Fin pb.dim => X - C (e i pb.gen)) ?_ ?_
    · exact pairwise_coprime_X_sub_C hinj
    · intro i
      rw [dvd_iff_isRoot]
      change eval (e i pb.gen) ((minpoly F pb.gen).map (algebraMap F E)) = 0
      rw [eval_map_algebraMap]
      exact (Polynomial.aeval_algHom_apply (e i) pb.gen (minpoly F pb.gen)).trans (by simp)
  exact eq_of_monic_of_dvd_of_natDegree_le hmon_F hmon_g hdvd hdegG_le

/-- For a finite separable field extension `S/F` with power basis `pb`, the discriminant of
the minimal polynomial of the generator equals the discriminant of the power basis. -/
theorem discr_powerBasis_eq_discr {F : Type*} [Field F] {S : Type*} [Field S] [Algebra F S]
    {pb : PowerBasis F S} [Algebra.IsSeparable F S] :
    Polynomial.discr (minpoly F pb.gen) = Algebra.discr F pb.basis := by
  let E := AlgebraicClosure S
  letI : Module.Finite F S := pb.finite
  have e : Fin pb.dim ≃ (S →ₐ[F] E) := by
    refine Fintype.equivOfCardEq ?_
    calc
      Fintype.card (Fin pb.dim) = pb.dim := Fintype.card_fin pb.dim
      _ = Module.finrank F S := (PowerBasis.finrank pb).symm
      _ = Fintype.card (S →ₐ[F] E) := (AlgHom.card (F := F) (E := S) (K := E)).symm
  -- polynomial side
  have hpoly : (algebraMap F E) (Polynomial.discr (minpoly F pb.gen)) =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
    calc
      (algebraMap F E) (Polynomial.discr (minpoly F pb.gen))
          = Polynomial.discr ((minpoly F pb.gen).map (algebraMap F E)) := by
              exact (Polynomial.discr_map_of_monic (algebraMap F E) (algebraMap F E).injective
                (minpoly.monic pb.isIntegral_gen)).symm
      _ = Polynomial.discr (∏ i : Fin pb.dim, (X - C (e i pb.gen))) := by
              rw [minpoly_map_eq_prod e]
      _ = ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
              exact Polynomial.discr_prod_X_sub_C_sq (fun i => e i pb.gen)
  -- algebra side
  have halg : (algebraMap F E) (Algebra.discr F pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
    exact Algebra.discr_powerBasis_eq_prod F E pb e
  -- conclude by injectivity of the map into the algebraic closure
  exact (algebraMap F E).injective (by rw [halg, hpoly])

end Commons.FieldTheory.Discriminant