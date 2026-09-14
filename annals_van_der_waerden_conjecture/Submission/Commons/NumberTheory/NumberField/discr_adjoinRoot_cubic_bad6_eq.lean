import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Tactic.NormNum.Prime
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr_polynomial
import Submission.Commons.FieldTheory.AdjoinRoot.isIntegral_root_map_algebraMap_monic
import Submission.Commons.Polynomial.discr_map_int
import Submission.Commons.NumberTheory.NumberField.discr_eq_of_algEquiv
import Submission.Commons.FieldTheory.AdjoinRoot.algEquiv_comp_X_add_C
import Submission.Commons.FieldTheory.AdjoinRoot.algEquiv_cubic_neg2_0_2_neg1_1_1
import Submission.Commons.FieldTheory.AdjoinRoot.algEquiv_cubic_neg2_0_2_1_1_neg1

set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial
open Module
open Matrix

namespace Commons.NumberTheory.NumberField



lemma sq_eq_one_of_odd_of_dvd_neg44_or_neg76 {m : ℤ} (hodd : ¬ 2 ∣ m)
    (h : m*m ∣ -44 ∨ m*m ∣ -76) : m*m = 1 := by
  rcases h with h | h
  · have hm_dvd_pos : m*m ∣ (44:ℤ) := by
      norm_num at h
      exact h
    have hsq_nonneg : 0 ≤ m*m := by nlinarith [sq_nonneg m]
    have hle_sq : m*m ≤ 44 := Int.le_of_dvd (by norm_num) hm_dvd_pos
    have hm_le : m ≤ 6 := by nlinarith
    have hm_ge : -6 ≤ m := by nlinarith
    interval_cases m <;> norm_num at *
  · have hm_dvd_pos : m*m ∣ (76:ℤ) := by
      norm_num at h
      exact h
    have hsq_nonneg : 0 ≤ m*m := by nlinarith [sq_nonneg m]
    have hle_sq : m*m ≤ 76 := Int.le_of_dvd (by norm_num) hm_dvd_pos
    have hm_le : m ≤ 8 := by nlinarith
    have hm_ge : -8 ≤ m := by nlinarith
    interval_cases m <;> norm_num at *


open Polynomial

lemma irreducible_map_of_isEisensteinAt_two (g : Polynomial ℤ) (hg : g.Monic)
    (hdeg : 0 < g.natDegree)
    (hei : g.IsEisensteinAt (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ))) :
    Irreducible (g.map (algebraMap ℤ ℚ)) := by
  let I : Ideal ℤ := Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)
  have hprime : I.IsPrime := by
    dsimp [I]
    simpa using (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
      (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 2))
  have hirr : Irreducible g := hei.irreducible hprime hg.isPrimitive hdeg
  exact (hg.irreducible_iff_irreducible_map_fraction_map).1 hirr


open Polynomial

lemma eis_two_neg2_0_2 :
    (Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)).IsEisensteinAt
    (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)
  have hg_monic : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  apply Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hg_monic
  · rw [Ideal.ne_top_iff_one]
    intro h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd
  · intro n hn
    have hdeg : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
    have hn3 : n < 3 := by rw [hdeg] at hn; exact hn
    interval_cases n <;> norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Submodule.mem_span_singleton]
  · dsimp [g]
    intro h
    rw [Ideal.span_singleton_pow] at h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd

lemma eis_two_2_0_neg2 :
    (Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)).IsEisensteinAt
    (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)
  have hg_monic : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  apply Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hg_monic
  · rw [Ideal.ne_top_iff_one]
    intro h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd
  · intro n hn
    have hdeg : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
    have hn3 : n < 3 := by rw [hdeg] at hn; exact hn
    interval_cases n <;> norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Submodule.mem_span_singleton]
  · dsimp [g]
    intro h
    rw [Ideal.span_singleton_pow] at h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd

lemma eis_two_2_4_2 :
    (Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)).IsEisensteinAt
    (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)
  have hg_monic : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  apply Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hg_monic
  · rw [Ideal.ne_top_iff_one]
    intro h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd
  · intro n hn
    have hdeg : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
    have hn3 : n < 3 := by rw [hdeg] at hn; exact hn
    interval_cases n
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_C, Submodule.mem_span_singleton]
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      exact (Ideal.mem_span_singleton).2 ⟨2, by norm_num⟩
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Submodule.mem_span_singleton]
  · dsimp [g]
    intro h
    rw [Ideal.span_singleton_pow] at h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd

lemma eis_two_neg2_4_neg2 :
    (Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)).IsEisensteinAt
    (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)
  have hg_monic : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  apply Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hg_monic
  · rw [Ideal.ne_top_iff_one]
    intro h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd
  · intro n hn
    have hdeg : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
    have hn3 : n < 3 := by rw [hdeg] at hn; exact hn
    interval_cases n
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_C, Submodule.mem_span_singleton]
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      exact (Ideal.mem_span_singleton).2 ⟨2, by norm_num⟩
    · norm_num [g, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Submodule.mem_span_singleton]
  · dsimp [g]
    intro h
    rw [Ideal.span_singleton_pow] at h
    have hdvd := Ideal.mem_span_singleton.mp h
    norm_num at hdvd





open Polynomial

lemma minpoly_int_root_map (g : Polynomial ℤ) (hg : g.Monic)
    [Fact (Irreducible (g.map (algebraMap ℤ ℚ)))] :
    minpoly ℤ (AdjoinRoot.root (g.map (algebraMap ℤ ℚ))) = g := by
  let f : Polynomial ℚ := g.map (algebraMap ℤ ℚ)
  let K := AdjoinRoot f
  have hf_monic : f.Monic := hg.map (algebraMap ℤ ℚ)
  have hf_ne : f ≠ 0 := hf_monic.ne_zero
  have hint : IsIntegral ℤ (AdjoinRoot.root f) := by
    simpa [f] using (Commons.FieldTheory.AdjoinRoot.isIntegral_root_map_algebraMap_monic g hg)
  have hroot : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root (g.map (algebraMap ℤ ℚ))
  have hminQ : minpoly ℚ (AdjoinRoot.root f) = f := by
    exact (minpoly.eq_of_irreducible_of_monic (B := AdjoinRoot f) (Fact.out : Irreducible f) hroot hf_monic).symm
  have hminQ2 : minpoly ℚ (AdjoinRoot.root f) = (minpoly ℤ (AdjoinRoot.root f)).map (algebraMap ℤ ℚ) := by
    simpa using (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (S := K) ℚ hint)
  have hmap : (minpoly ℤ (AdjoinRoot.root f)).map (algebraMap ℤ ℚ) = f := by
    rw [← hminQ2, hminQ]
  have hmap' : (minpoly ℤ (AdjoinRoot.root f)).map (algebraMap ℤ ℚ) = g.map (algebraMap ℤ ℚ) := by
    simpa [f] using hmap
  exact (Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int hmap')





set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K] [NumberField K]

set_option maxHeartbeats 500000

theorem prime_not_dvd_toMatrix_det_of_isEisensteinAt
    {p : ℕ} (hp : Nat.Prime p)
    (pb : PowerBasis ℚ K) (hint : IsIntegral ℤ pb.gen)
    (hei : (minpoly ℤ pb.gen).IsEisensteinAt (Submodule.span ℤ ({(p : ℤ)} : Set ℤ)))
    (b : Module.Basis (Fin pb.dim) ℤ (NumberField.RingOfIntegers K)) :
    ¬ (p : ℤ) ∣ (b.toMatrix (fun j : Fin pb.dim =>
        (⟨pb.basis j, by rw [PowerBasis.basis_eq_pow]; exact hint.pow _⟩ : NumberField.RingOfIntegers K))).det := by
  let bpow : Fin pb.dim → NumberField.RingOfIntegers K := fun j =>
    (⟨pb.basis j, by rw [PowerBasis.basis_eq_pow]; exact hint.pow _⟩ : NumberField.RingOfIntegers K)
  let P : Matrix (Fin pb.dim) (Fin pb.dim) ℤ := b.toMatrix bpow
  intro hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  let P₂ : Matrix (Fin pb.dim) (Fin pb.dim) (ZMod p) :=
    (Int.castRingHom (ZMod p)).mapMatrix P
  have hdivP : (p : ℤ) ∣ P.det := by
    simpa [P, bpow] using hdiv
  have hdet₂ : P₂.det = 0 := by
    dsimp [P₂]
    rw [← RingHom.map_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd P.det p).2 hdivP
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := P₂)).2 hdet₂
  choose w hw using fun i => ZMod.intCast_surjective (v i)
  have hw_not_all : ¬ ∀ i, (p : ℤ) ∣ w i := by
    intro hall
    apply hv0
    funext i
    have hwi : (p : ℤ) ∣ w i := hall i
    have hz : ((w i : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (w i) p).2 hwi
    simpa [hw i] using hz
  have hcoeff_mod : ∀ i, (((Matrix.mulVec P w) i : ℤ) : ZMod p) = 0 := by
    intro i
    have hzero := congr_fun hv i
    calc
      (((Matrix.mulVec P w) i : ℤ) : ZMod p)
          = (Matrix.mulVec (P.map (Int.castRingHom (ZMod p))) (fun j => (w j : ZMod p))) i := by
              exact (RingHom.map_mulVec (Int.castRingHom (ZMod p)) P w i)
      _ = (Matrix.mulVec ((Int.castRingHom (ZMod p)).mapMatrix P) v) i := by
              rw [RingHom.mapMatrix_apply]
              congr 1
              · funext j
                exact hw j
      _ = (Matrix.mulVec P₂ v) i := by
              dsimp [P₂]
      _ = 0 := hzero
  have hcoeff_dvd : ∀ i, (p : ℤ) ∣ (Matrix.mulVec P w) i := by
    intro i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((Matrix.mulVec P w) i) p).1 (hcoeff_mod i)
  choose c hc using hcoeff_dvd
  let y𝒪 : NumberField.RingOfIntegers K := ∑ j, w j • bpow j
  let z𝒪 : NumberField.RingOfIntegers K := ∑ i, c i • b i
  have hsum_bpow : ∀ j, ∑ i, P i j • b i = bpow j := by
    intro j
    simpa [P, bpow] using Module.Basis.sum_toMatrix_smul_self b bpow j
  have hy_expand : y𝒪 = ∑ i, (Matrix.mulVec P w) i • b i := by
    simp only [y𝒪]
    calc
      (∑ j, w j • bpow j) = ∑ j, w j • (∑ i, P i j • b i) := by
        simp_rw [hsum_bpow]
      _ = ∑ i, (∑ j, P i j * w j) • b i := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
        simp [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
      _ = ∑ i, (Matrix.mulVec P w) i • b i := by
        rfl
  have hy_eq_pz : y𝒪 = (p : ℤ) • z𝒪 := by
    calc
      y𝒪 = ∑ i, (Matrix.mulVec P w) i • b i := hy_expand
      _ = ∑ i, ((p : ℤ) * c i) • b i := by
            simp [hc]
      _ = ∑ i, (p : ℤ) • (c i • b i) := by
            simp [mul_smul]
      _ = (p : ℤ) • (∑ i, c i • b i) := by
            rw [Finset.smul_sum]
      _ = (p : ℤ) • z𝒪 := rfl
  let yK : K := ∑ j, w j • pb.basis j
  have hyK_eq_y𝒪 : (y𝒪 : K) = yK := by
    dsimp [y𝒪, yK]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (algebraMap (NumberField.RingOfIntegers K) K) (w j • bpow j)
          = (w j : ℚ) • (algebraMap (NumberField.RingOfIntegers K) K) (bpow j) := by
              exact map_intCast_smul (f := (algebraMap (NumberField.RingOfIntegers K) K)) (R := ℤ) (S := ℚ) (x := w j) (a := bpow j)
      _ = (w j : ℚ) • pb.basis j := by
              simp [bpow]
      _ = w j • pb.basis j := by
              rw [← Int.cast_smul_eq_zsmul (R := ℚ)]
  have hyK_adjoin : yK ∈ Algebra.adjoin ℤ ({pb.gen} : Set K) := by
    refine Subalgebra.sum_mem _ (fun j _ => ?_)
    rw [PowerBasis.basis_eq_pow]
    exact Subalgebra.zsmul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ pb.gen) _) _
  have hz_int : IsIntegral ℤ (z𝒪 : K) := by
    exact (z𝒪.property)
  have hy_eq_pz_K : (y𝒪 : K) = (p : ℤ) • (z𝒪 : K) := by
    rw [hy_eq_pz]
    simp [map_zsmul]
  have hz_smul : (p : ℤ) • (z𝒪 : K) ∈ Algebra.adjoin ℤ ({pb.gen} : Set K) := by
    rw [← hy_eq_pz_K]
    rwa [hyK_eq_y𝒪]
  have hz_adjoin := mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt
    (R := ℤ) (K := ℚ) (L := K) (p := (p : ℤ)) (Nat.prime_iff_prime_int.mp hp)
    hint hz_int hz_smul hei
  -- now get polynomial Q and reduce mod minpoly
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ[X], Polynomial.aeval pb.gen Q = (z𝒪 : K) := by
    simpa [Set.mem_range, Algebra.adjoin_singleton_eq_range_aeval] using hz_adjoin
  let fℤ : ℤ[X] := minpoly ℤ pb.gen
  let Qred : ℤ[X] := Q %ₘ fℤ
  have hf_monic : fℤ.Monic := by simpa [fℤ] using minpoly.monic hint
  have hfdeg : fℤ.natDegree = pb.dim := by
    have hmap : minpoly ℚ pb.gen = (minpoly ℤ pb.gen).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (S := K) ℚ hint
    have hdegQ : (minpoly ℚ pb.gen).natDegree = pb.dim := PowerBasis.natDegree_minpoly pb
    have hmapdeg := congrArg Polynomial.natDegree hmap
    rw [hdegQ] at hmapdeg
    rw [(minpoly.monic hint).natDegree_map] at hmapdeg
    simpa [fℤ] using hmapdeg.symm
  have hQred_deg : Qred.natDegree < pb.dim := by
    rw [← hfdeg]
    apply Polynomial.natDegree_modByMonic_lt Q hf_monic
    intro h
    have hdim : pb.dim = 0 := by
      have hnat := congrArg Polynomial.natDegree h
      rw [hfdeg] at hnat
      simpa using hnat
    have hpos : 0 < pb.dim := PowerBasis.dim_pos pb
    omega
  have hQred_aeval : Polynomial.aeval pb.gen Qred = (z𝒪 : K) := by
    calc
      Polynomial.aeval pb.gen Qred = Polynomial.aeval pb.gen Q := by
        dsimp [Qred, fℤ]
        exact Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval ℤ pb.gen)
      _ = (z𝒪 : K) := hQ
  have hright_sum : (p : ℤ) • (z𝒪 : K) = ∑ i : Fin pb.dim, (p * Qred.coeff i) • pb.basis i := by
    calc
      (p : ℤ) • (z𝒪 : K) = (p : ℤ) • Polynomial.aeval pb.gen Qred := by rw [hQred_aeval]
      _ = (p : ℤ) • (∑ i ∈ Finset.range pb.dim, Qred.coeff i • pb.gen ^ i) := by
            rw [Polynomial.aeval_eq_sum_range' hQred_deg pb.gen]
      _ = ∑ i : Fin pb.dim, (p * Qred.coeff i) • pb.basis i := by
            rw [Finset.smul_sum]
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro x hx
            have hxlt : x < pb.dim := Finset.mem_range.mp hx
            simp [hxlt, PowerBasis.basis_eq_pow, mul_smul, mul_assoc, mul_comm, mul_left_comm]
  have hleft_sum : yK = ∑ j : Fin pb.dim, w j • pb.basis j := by
    rfl
  have hyK_eq_pz : yK = (p : ℤ) • (z𝒪 : K) := by
    rw [← hyK_eq_y𝒪, hy_eq_pz]
    simp [map_zsmul]
  have hsum_eq : (∑ j : Fin pb.dim, w j • pb.basis j) =
      (∑ j : Fin pb.dim, (p * Qred.coeff j) • pb.basis j) := by
    rw [← hleft_sum, hyK_eq_pz, hright_sum]
  have hwj : ∀ j, (w j : ℚ) = p * Qred.coeff j := by
    intro j
    have hsum_diff_mul :
        (∑ i : Fin pb.dim, (((w i : ℚ) - ((p * Qred.coeff i : ℤ) : ℚ)) * pb.basis i)) = 0 := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      have hsum_eq_Q :
          (∑ i : Fin pb.dim, (w i : ℚ) * pb.basis i) =
          (∑ i : Fin pb.dim, (((p * Qred.coeff i : ℤ) : ℚ) * pb.basis i)) := by
        simpa [← Int.cast_smul_eq_zsmul] using hsum_eq
      rw [hsum_eq_Q]
      simp
    have hsum_diff :
        (∑ i : Fin pb.dim, ((w i : ℚ) - ((p * Qred.coeff i : ℤ) : ℚ)) • pb.basis i) = 0 := by
      simpa [Algebra.smul_def] using hsum_diff_mul
    have hcoeff := (Fintype.linearIndependent_iff.mp pb.basis.linearIndependent)
      (fun i : Fin pb.dim => (w i : ℚ) - ((p * Qred.coeff i : ℤ) : ℚ)) hsum_diff j
    have hcoeff' := sub_eq_zero.mp hcoeff
    exact_mod_cast hcoeff'
  have hcontra : ∀ j, (p : ℤ) ∣ w j := by
    intro j
    have hwj_int : w j = (p : ℤ) * Qred.coeff j := by
      exact_mod_cast hwj j
    exact ⟨Qred.coeff j, hwj_int⟩
  exact hw_not_all hcontra





set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial
open Module
open Matrix

lemma exists_discr_eq_field_discr_mul_sq_and_not_dvd_of_isEisensteinAt
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    (pb : PowerBasis ℚ K) (hint : IsIntegral ℤ pb.gen)
    (hei : (minpoly ℤ pb.gen).IsEisensteinAt (Submodule.span ℤ ({(p : ℤ)} : Set ℤ))) :
    ∃ m : ℤ, Algebra.discr ℚ pb.basis = (NumberField.discr K : ℚ) * (m * m : ℚ) ∧
      ¬ (p : ℤ) ∣ m := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let bO : Basis ι ℤ (NumberField.RingOfIntegers K) := NumberField.RingOfIntegers.basis K
  let e : ι ≃ Fin pb.dim := by
    apply Fintype.equivOfCardEq
    rw [← Module.finrank_eq_card_basis bO, NumberField.RingOfIntegers.rank, pb.finrank]
    simp
  let bFin : Basis (Fin pb.dim) ℤ (NumberField.RingOfIntegers K) := bO.reindex e
  have hpb_int : ∀ i, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [PowerBasis.basis_eq_pow]
    exact hint.pow _
  let bpow : Fin pb.dim → NumberField.RingOfIntegers K := fun i =>
    ⟨pb.basis i, hpb_int i⟩
  let P : Matrix (Fin pb.dim) (Fin pb.dim) ℤ := fun i j => (bFin.repr (bpow j)) i
  let Pℚ : Matrix (Fin pb.dim) (Fin pb.dim) ℚ := P.map (Int.castRingHom ℚ)
  let bK : Fin pb.dim → K := fun i => algebraMap (NumberField.RingOfIntegers K) K (bFin i)
  have hbK_discr : Algebra.discr ℚ bK = (NumberField.discr K : ℚ) := by
    rw [show bK = ⇑(NumberField.integralBasis K) ∘ e.symm by
      funext i
      simp [bK, bFin, bO, NumberField.integralBasis_apply]]
    rw [Algebra.discr_reindex (A := ℚ) (b := NumberField.integralBasis K) (f := e)]
    exact (NumberField.coe_discr K).symm
  have hbpow_eq : pb.basis = Matrix.vecMul bK (Pℚ.map (algebraMap ℚ K)) := by
    ext j
    dsimp [bpow, P, Pℚ, bK]
    have hsum := bFin.sum_repr (bpow j)
    have hsum' : (∑ i : Fin pb.dim, bK i * ((bFin.repr (bpow j)) i : ℚ)) = pb.basis j := by
      have h := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hsum
      have hrhs : (algebraMap (NumberField.RingOfIntegers K) K) (bpow j) = pb.basis j := rfl
      simpa [bK, bFin, map_sum, smul_eq_mul, mul_comm] using h.trans hrhs
    simp only [P, Pℚ, Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.map, bK]
    simpa [bK, bpow, mul_comm] using hsum'.symm
  have hdiscr_rel : Algebra.discr ℚ pb.basis = Pℚ.det ^ 2 * Algebra.discr ℚ bK := by
    rw [hbpow_eq]
    exact Algebra.discr_of_matrix_vecMul (A := ℚ) (B := K) (b := bK) (P := Pℚ)
  have hdet : Pℚ.det = (P.det : ℚ) := by
    dsimp [Pℚ]
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have hrel : Algebra.discr ℚ pb.basis = (NumberField.discr K : ℚ) * (P.det * P.det : ℚ) := by
    calc
      Algebra.discr ℚ pb.basis = Pℚ.det ^ 2 * Algebra.discr ℚ bK := hdiscr_rel
      _ = (P.det : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by rw [hdet, hbK_discr]
      _ = (NumberField.discr K : ℚ) * (P.det * P.det : ℚ) := by ring
  have hnot : ¬ (p : ℤ) ∣ P.det := by
    change ¬ (p : ℤ) ∣ (bFin.toMatrix bpow).det
    exact prime_not_dvd_toMatrix_det_of_isEisensteinAt (K := K) hp pb hint hei bFin
  exact ⟨P.det, hrel, hnot⟩





set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial
open Module
open Matrix

lemma discr_eq_discr_of_isEisensteinAt_two_of_discr_eq_neg44_or_neg76
    (g : Polynomial ℤ) (hg : g.Monic) [Fact (Irreducible (g.map (algebraMap ℤ ℚ)))]
    (hei : g.IsEisensteinAt (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)))
    (hP : Polynomial.discr g = -44 ∨ Polynomial.discr g = -76) :
    NumberField.discr (AdjoinRoot (g.map (algebraMap ℤ ℚ))) =
      Polynomial.discr (g.map (algebraMap ℤ ℚ)) := by
  let f : Polynomial ℚ := g.map (algebraMap ℤ ℚ)
  let K := AdjoinRoot f
  have hf_monic : f.Monic := by
    dsimp [f]
    exact hg.map (algebraMap ℤ ℚ)
  have hf0 : f ≠ 0 := hf_monic.ne_zero
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hf0
  have hpb_gen : pb.gen = AdjoinRoot.root f := by
    simp [pb, f, K]
  have hint : IsIntegral ℤ pb.gen := by
    rw [hpb_gen]
    dsimp [f]
    exact Commons.FieldTheory.AdjoinRoot.isIntegral_root_map_algebraMap_monic g hg
  have hmin : minpoly ℤ pb.gen = g := by
    rw [hpb_gen]
    dsimp [f]
    exact minpoly_int_root_map g hg
  have hei_int : (minpoly ℤ pb.gen).IsEisensteinAt (Submodule.span ℤ ({(2 : ℤ)} : Set ℤ)) := by
    simpa [hmin] using hei
  obtain ⟨m, hm_rel, hm_odd⟩ :=
    exists_discr_eq_field_discr_mul_sq_and_not_dvd_of_isEisensteinAt (K := K)
      (by norm_num : Nat.Prime 2) pb hint hei_int
  have hdisc_pb : Algebra.discr ℚ pb.basis = Polynomial.discr f := by
    dsimp [pb]
    exact Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr_polynomial hf_monic hf0
  have hmap : Polynomial.discr f = ((Polynomial.discr g : ℤ) : ℚ) := by
    dsimp [f]
    exact Commons.Polynomial.discr_map_int g hg
  have hrel_Q : ((Polynomial.discr g : ℤ) : ℚ) =
      ((NumberField.discr K : ℤ) : ℚ) * (m * m : ℚ) := by
    rw [← hmap, ← hdisc_pb, hm_rel]
  have hrel_int : Polynomial.discr g = NumberField.discr K * (m * m) := by
    exact_mod_cast hrel_Q
  have hm_dvd : m * m ∣ Polynomial.discr g := by
    rw [hrel_int]
    exact dvd_mul_left (m * m) (NumberField.discr K)
  have hsq : m * m = 1 := by
    refine sq_eq_one_of_odd_of_dvd_neg44_or_neg76 hm_odd ?_
    rcases hP with hP | hP
    · left; simpa [hP] using hm_dvd
    · right; simpa [hP] using hm_dvd
  have hD : NumberField.discr K = Polynomial.discr g := by
    have := hrel_int
    rw [hsq] at this
    simpa using this.symm
  have hDf : (NumberField.discr K : ℚ) = Polynomial.discr f := by
    rw [hD, hmap]
  exact hDf






private lemma map_cubic_neg2_0_2_eq :
    (Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)).map (algebraMap ℤ ℚ) =
    Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) := by
  ext n
  simp [Polynomial.coeff_map, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.C_eq_natCast, Polynomial.C_eq_intCast]
  by_cases h0 : n = 0; · subst n; norm_num
  by_cases h1 : n = 1; · subst n; norm_num
  by_cases h2 : n = 2; · subst n; norm_num
  by_cases h3 : n = 3; · subst n; norm_num
  · have hn : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 := by omega
    rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) by exact (Polynomial.C_eq_natCast (R := ℚ) 2).symm]
    simp [Polynomial.coeff_C, hn.1]

private lemma map_cubic_2_0_neg2_eq :
    (Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)).map (algebraMap ℤ ℚ) =
    Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ) := by
  ext n
  simp [Polynomial.coeff_map, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.C_eq_natCast, Polynomial.C_eq_intCast]
  by_cases h0 : n = 0; · subst n; norm_num
  by_cases h1 : n = 1; · subst n; norm_num
  by_cases h2 : n = 2; · subst n; norm_num
  by_cases h3 : n = 3; · subst n; norm_num
  · have hn : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 := by omega
    rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) by exact (Polynomial.C_eq_natCast (R := ℚ) 2).symm]
    simp [Polynomial.coeff_C, hn.1]

private lemma map_cubic_2_4_2_eq_comp_X_add_C :
    (Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)).map (algebraMap ℤ ℚ) =
    (Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ)).comp
        (Polynomial.X + Polynomial.C (1 : ℚ)) := by
  have hC3 : Polynomial.C (3 : ℚ) = (3 : Polynomial ℚ) := by
    exact (Polynomial.C_eq_natCast (R := ℚ) 3).symm
  have hCneg1 : Polynomial.C (-1 : ℚ) = (-1 : Polynomial ℚ) := by
    simpa using (Polynomial.C_eq_intCast (R := ℚ) (-1))
  have hC2 : Polynomial.C (2 : ℚ) = (2 : Polynomial ℚ) := by
    exact (Polynomial.C_eq_natCast (R := ℚ) 2).symm
  simp [Polynomial.map, Polynomial.comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, hC3, hCneg1, hC2]
  ring

private lemma map_cubic_neg2_4_neg2_eq_comp_X_sub_C :
    (Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)).map (algebraMap ℤ ℚ) =
    (Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)).comp
        (Polynomial.X + Polynomial.C (-1 : ℚ)) := by
  have hC3 : Polynomial.C (3 : ℚ) = (3 : Polynomial ℚ) := by
    exact (Polynomial.C_eq_natCast (R := ℚ) 3).symm
  have hCneg1 : Polynomial.C (-1 : ℚ) = (-1 : Polynomial ℚ) := by
    simpa using (Polynomial.C_eq_intCast (R := ℚ) (-1))
  have hC1 : Polynomial.C (1 : ℚ) = (1 : Polynomial ℚ) := by
    exact (Polynomial.C_eq_natCast (R := ℚ) 1).symm
  have hC2 : Polynomial.C (2 : ℚ) = (2 : Polynomial ℚ) := by
    exact (Polynomial.C_eq_natCast (R := ℚ) 2).symm
  simp [Polynomial.map, Polynomial.comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, hC3, hCneg1, hC1, hC2]
  ring

private lemma discr_cubic_neg2_0_2 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)) = -44 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num

private lemma discr_cubic_2_0_neg2 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ)) = -44 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num

private lemma discr_cubic_neg1_1_1 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)) = -44 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num

private lemma discr_cubic_1_1_neg1 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ)) = -44 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num

private lemma discr_cubic_neg1_3_neg1 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ)) = -76 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num

private lemma discr_cubic_1_3_1 :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)) = -76 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
  · compute_degree <;> norm_num




private lemma fact_irreducible_cubic_neg2_0_2_Q :
    Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)
  have hg : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  have hdeg3 : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hdeg : 0 < g.natDegree := by rw [hdeg3]; norm_num
  haveI : Fact (Irreducible (g.map (algebraMap ℤ ℚ))) :=
    ⟨irreducible_map_of_isEisensteinAt_two g hg hdeg eis_two_neg2_0_2⟩
  have hfg := map_cubic_neg2_0_2_eq
  refine ⟨?_⟩
  rw [← hfg]
  exact Fact.out

private lemma fact_irreducible_cubic_2_0_neg2_Q :
    Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ) : Polynomial ℚ)) := by
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)
  have hg : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  have hdeg3 : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hdeg : 0 < g.natDegree := by rw [hdeg3]; norm_num
  haveI : Fact (Irreducible (g.map (algebraMap ℤ ℚ))) :=
    ⟨irreducible_map_of_isEisensteinAt_two g hg hdeg eis_two_2_0_neg2⟩
  have hfg := map_cubic_2_0_neg2_eq
  refine ⟨?_⟩
  rw [← hfg]
  exact Fact.out

private lemma discr_adjoinRoot_direct_neg2_0_2
    [Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ))] :
    (NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ)) : ℚ) =
      Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ) := by
  let f : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)
  have hg : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  have hdeg3 : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hdeg : 0 < g.natDegree := by rw [hdeg3]; norm_num
  haveI : Fact (Irreducible (g.map (algebraMap ℤ ℚ))) :=
    ⟨irreducible_map_of_isEisensteinAt_two g hg hdeg eis_two_neg2_0_2⟩
  have hdeg_g : g.degree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hP : Polynomial.discr g = -44 := by
    dsimp [g]
    rw [Polynomial.discr_of_degree_eq_three hdeg_g]
    simp [g]
  have hdirect := discr_eq_discr_of_isEisensteinAt_two_of_discr_eq_neg44_or_neg76
    g hg eis_two_neg2_0_2 (Or.inl hP)
  have hfg : g.map (algebraMap ℤ ℚ) = f := map_cubic_neg2_0_2_eq
  have e_alg : AdjoinRoot (g.map (algebraMap ℤ ℚ)) ≃ₐ[ℚ] AdjoinRoot f :=
    AdjoinRoot.algEquivOfEq (R := ℚ) (g.map (algebraMap ℤ ℚ)) f hfg
  have hdisc_iso := discr_eq_of_algEquiv e_alg
  have hdisc_isoQ : (NumberField.discr (AdjoinRoot f) : ℚ) =
      (NumberField.discr (AdjoinRoot (g.map (algebraMap ℤ ℚ))) : ℚ) := by
    exact_mod_cast hdisc_iso.symm
  calc
    (NumberField.discr (AdjoinRoot f) : ℚ) = (NumberField.discr (AdjoinRoot (g.map (algebraMap ℤ ℚ))) : ℚ) := hdisc_isoQ
    _ = Polynomial.discr (g.map (algebraMap ℤ ℚ)) := hdirect
    _ = Polynomial.discr f := by rw [hfg]

private lemma discr_adjoinRoot_direct_2_0_neg2
    [Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ) : Polynomial ℚ))] :
    (NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ) : Polynomial ℚ)) : ℚ) =
      Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ) : Polynomial ℚ) := by
  let f : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (-2 : ℚ)
  let g : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
    Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)
  have hg : g.Monic := by
    dsimp [g]
    convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)) (n := 3) ?_ using 1
    · ring
    · compute_degree <;> norm_num
  have hdeg3 : g.natDegree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hdeg : 0 < g.natDegree := by rw [hdeg3]; norm_num
  haveI : Fact (Irreducible (g.map (algebraMap ℤ ℚ))) :=
    ⟨irreducible_map_of_isEisensteinAt_two g hg hdeg eis_two_2_0_neg2⟩
  have hdeg_g : g.degree = 3 := by dsimp [g]; compute_degree <;> norm_num
  have hP : Polynomial.discr g = -44 := by
    dsimp [g]
    rw [Polynomial.discr_of_degree_eq_three hdeg_g]
    simp [g]
  have hdirect := discr_eq_discr_of_isEisensteinAt_two_of_discr_eq_neg44_or_neg76
    g hg eis_two_2_0_neg2 (Or.inl hP)
  have hfg : g.map (algebraMap ℤ ℚ) = f := map_cubic_2_0_neg2_eq
  have e_alg : AdjoinRoot (g.map (algebraMap ℤ ℚ)) ≃ₐ[ℚ] AdjoinRoot f :=
    AdjoinRoot.algEquivOfEq (R := ℚ) (g.map (algebraMap ℤ ℚ)) f hfg
  have hdisc_iso := discr_eq_of_algEquiv e_alg
  have hdisc_isoQ : (NumberField.discr (AdjoinRoot f) : ℚ) =
      (NumberField.discr (AdjoinRoot (g.map (algebraMap ℤ ℚ))) : ℚ) := by
    exact_mod_cast hdisc_iso.symm
  calc
    (NumberField.discr (AdjoinRoot f) : ℚ) = (NumberField.discr (AdjoinRoot (g.map (algebraMap ℤ ℚ))) : ℚ) := hdisc_isoQ
    _ = Polynomial.discr (g.map (algebraMap ℤ ℚ)) := hdirect
    _ = Polynomial.discr f := by rw [hfg]

theorem discr_adjoinRoot_cubic_bad6_eq (a b c : ℤ)
    [Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) : Polynomial ℚ))]
    (h : (a, b, c) ∈ [(-2,0,2), (-1,1,1), (-1,3,-1), (1,1,-1), (1,3,1), (2,0,-2)]) :
    NumberField.discr (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) : Polynomial ℚ)) =
      Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) : Polynomial ℚ) := by
  simp at h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · letI := fact_irreducible_cubic_neg2_0_2_Q
    exact discr_adjoinRoot_direct_neg2_0_2
  · -- (-1,1,1)
    let f1 : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)
    let f2 : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)
    haveI hf1 : Fact (Irreducible f1) := fact_irreducible_cubic_neg2_0_2_Q
    haveI hf2 : Fact (Irreducible f2) := by
      refine ⟨by
        dsimp [f2]
        simpa using ((inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (↑(-1 : ℤ) : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (↑(1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C (↑(1 : ℤ) : ℚ) : Polynomial ℚ))).1)⟩
    obtain ⟨e⟩ := Commons.FieldTheory.AdjoinRoot.algEquiv_cubic_neg2_0_2_neg1_1_1
    have hdisc_iso := Commons.NumberTheory.NumberField.discr_eq_of_algEquiv e
    have hdisc_isoQ : (NumberField.discr (AdjoinRoot f2) : ℚ) =
        (NumberField.discr (AdjoinRoot f1) : ℚ) := by
      exact_mod_cast hdisc_iso
    have hdisc_f1 : (NumberField.discr (AdjoinRoot f1) : ℚ) = Polynomial.discr f1 := by
      simpa [f1] using discr_adjoinRoot_direct_neg2_0_2
    have hpoly : Polynomial.discr f2 = Polynomial.discr f1 := by
      dsimp [f2, f1]
      rw [Polynomial.discr_of_degree_eq_three]
      · rw [Polynomial.discr_of_degree_eq_three]
        norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
        · compute_degree <;> norm_num
      · compute_degree <;> norm_num
    calc
      (NumberField.discr (AdjoinRoot f2) : ℚ) = (NumberField.discr (AdjoinRoot f1) : ℚ) := hdisc_isoQ
      _ = Polynomial.discr f1 := hdisc_f1
      _ = Polynomial.discr f2 := hpoly.symm
  · -- (-1,3,-1) via shift +1
    let f : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ)
    haveI hf : Fact (Irreducible f) := by
      refine ⟨by
        dsimp [f]
        simpa using ((inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (↑(-1 : ℤ) : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (↑(3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C (↑(-1 : ℤ) : ℚ) : Polynomial ℚ))).1)⟩
    let gaux : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)
    have hgaux : gaux.Monic := by
      dsimp [gaux]
      convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (2 : ℤ) * Polynomial.X ^ 2 +
        Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (2 : ℤ)) (n := 3) ?_ using 1
      · ring
      · compute_degree <;> norm_num
    have hdegaux3 : gaux.natDegree = 3 := by dsimp [gaux]; compute_degree <;> norm_num
    have hdegaux : 0 < gaux.natDegree := by rw [hdegaux3]; norm_num
    haveI : Fact (Irreducible (gaux.map (algebraMap ℤ ℚ))) :=
      ⟨irreducible_map_of_isEisensteinAt_two gaux hgaux hdegaux eis_two_2_4_2⟩
    have hdeg_gaux : gaux.degree = 3 := by dsimp [gaux]; compute_degree <;> norm_num
    have hPaux : Polynomial.discr gaux = -76 := by
      dsimp [gaux]
      rw [Polynomial.discr_of_degree_eq_three hdeg_gaux]
      norm_num [gaux, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdirect := discr_eq_discr_of_isEisensteinAt_two_of_discr_eq_neg44_or_neg76
      gaux hgaux eis_two_2_4_2 (Or.inr hPaux)
    have hshift_eq : gaux.map (algebraMap ℤ ℚ) = f.comp (X + C 1) := by
      simpa [gaux, f] using map_cubic_2_4_2_eq_comp_X_add_C
    obtain ⟨e⟩ := Commons.FieldTheory.AdjoinRoot.algEquiv_comp_X_add_C f 1
    have e' : AdjoinRoot (gaux.map (algebraMap ℤ ℚ)) ≃ₐ[ℚ] AdjoinRoot f := by
      exact (AdjoinRoot.algEquivOfEq (R := ℚ) (gaux.map (algebraMap ℤ ℚ)) (f.comp (X + C 1)) hshift_eq).trans e
    have hiso := Commons.NumberTheory.NumberField.discr_eq_of_algEquiv e'
    have hisoQ : (NumberField.discr (AdjoinRoot (gaux.map (algebraMap ℤ ℚ))) : ℚ) =
        (NumberField.discr (AdjoinRoot f) : ℚ) := by
      exact_mod_cast hiso
    have hdisc_aux_map : Polynomial.discr (gaux.map (algebraMap ℤ ℚ)) = (-76 : ℚ) := by
      rw [Commons.Polynomial.discr_map_int gaux hgaux, hPaux]
      norm_num
    have hpoly_f : Polynomial.discr f = -76 := by
      dsimp [f]
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
      · compute_degree <;> norm_num
    calc
      (NumberField.discr (AdjoinRoot f) : ℚ) =
          (NumberField.discr (AdjoinRoot (gaux.map (algebraMap ℤ ℚ))) : ℚ) := hisoQ.symm
      _ = Polynomial.discr (gaux.map (algebraMap ℤ ℚ)) := hdirect
      _ = Polynomial.discr f := by rw [hdisc_aux_map, hpoly_f]
  · -- (1,1,-1)
    let f1 : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)
    let f3 : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ)
    haveI hf1 : Fact (Irreducible f1) := fact_irreducible_cubic_neg2_0_2_Q
    haveI hf3 : Fact (Irreducible f3) := by
      refine ⟨by
        dsimp [f3]
        simpa using ((inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (↑(1 : ℤ) : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (↑(1 : ℤ) : ℚ) * Polynomial.X + Polynomial.C (↑(-1 : ℤ) : ℚ) : Polynomial ℚ))).1)⟩
    obtain ⟨e⟩ := Commons.FieldTheory.AdjoinRoot.algEquiv_cubic_neg2_0_2_1_1_neg1
    have hdisc_iso := Commons.NumberTheory.NumberField.discr_eq_of_algEquiv e
    have hdisc_isoQ : (NumberField.discr (AdjoinRoot f3) : ℚ) =
        (NumberField.discr (AdjoinRoot f1) : ℚ) := by
      exact_mod_cast hdisc_iso
    have hdisc_f1 : (NumberField.discr (AdjoinRoot f1) : ℚ) = Polynomial.discr f1 := by
      simpa [f1] using discr_adjoinRoot_direct_neg2_0_2
    have hpoly : Polynomial.discr f3 = Polynomial.discr f1 := by
      dsimp [f3, f1]
      rw [Polynomial.discr_of_degree_eq_three]
      · rw [Polynomial.discr_of_degree_eq_three]
        norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
        · compute_degree <;> norm_num
      · compute_degree <;> norm_num
    calc
      (NumberField.discr (AdjoinRoot f3) : ℚ) = (NumberField.discr (AdjoinRoot f1) : ℚ) := hdisc_isoQ
      _ = Polynomial.discr f1 := hdisc_f1
      _ = Polynomial.discr f3 := hpoly.symm
  · -- (1,3,1) via shift -1
    let f : Polynomial ℚ := Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (1 : ℚ)
    haveI hf : Fact (Irreducible f) := by
      refine ⟨by
        dsimp [f]
        simpa using ((inferInstance : Fact (Irreducible (Polynomial.X ^ 3 + Polynomial.C (↑(1 : ℤ) : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (↑(3 : ℤ) : ℚ) * Polynomial.X + Polynomial.C (↑(1 : ℤ) : ℚ) : Polynomial ℚ))).1)⟩
    let gaux : Polynomial ℤ := Polynomial.X ^ 3 + Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
      Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)
    have hgaux : gaux.Monic := by
      dsimp [gaux]
      convert monic_X_pow_add (R := ℤ) (p := Polynomial.C (-2 : ℤ) * Polynomial.X ^ 2 +
        Polynomial.C (4 : ℤ) * Polynomial.X + Polynomial.C (-2 : ℤ)) (n := 3) ?_ using 1
      · ring
      · compute_degree <;> norm_num
    have hdegaux3 : gaux.natDegree = 3 := by dsimp [gaux]; compute_degree <;> norm_num
    have hdegaux : 0 < gaux.natDegree := by rw [hdegaux3]; norm_num
    haveI : Fact (Irreducible (gaux.map (algebraMap ℤ ℚ))) :=
      ⟨irreducible_map_of_isEisensteinAt_two gaux hgaux hdegaux eis_two_neg2_4_neg2⟩
    have hdeg_gaux : gaux.degree = 3 := by dsimp [gaux]; compute_degree <;> norm_num
    have hPaux : Polynomial.discr gaux = -76 := by
      dsimp [gaux]
      rw [Polynomial.discr_of_degree_eq_three hdeg_gaux]
      norm_num [gaux, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdirect := discr_eq_discr_of_isEisensteinAt_two_of_discr_eq_neg44_or_neg76
      gaux hgaux eis_two_neg2_4_neg2 (Or.inr hPaux)
    have hshift_eq : gaux.map (algebraMap ℤ ℚ) = f.comp (X + C (-1)) := by
      simpa [gaux, f] using map_cubic_neg2_4_neg2_eq_comp_X_sub_C
    obtain ⟨e⟩ := Commons.FieldTheory.AdjoinRoot.algEquiv_comp_X_add_C f (-1)
    have e' : AdjoinRoot (gaux.map (algebraMap ℤ ℚ)) ≃ₐ[ℚ] AdjoinRoot f := by
      exact (AdjoinRoot.algEquivOfEq (R := ℚ) (gaux.map (algebraMap ℤ ℚ)) (f.comp (X + C (-1))) hshift_eq).trans e
    have hiso := Commons.NumberTheory.NumberField.discr_eq_of_algEquiv e'
    have hisoQ : (NumberField.discr (AdjoinRoot (gaux.map (algebraMap ℤ ℚ))) : ℚ) =
        (NumberField.discr (AdjoinRoot f) : ℚ) := by
      exact_mod_cast hiso
    have hdisc_aux_map : Polynomial.discr (gaux.map (algebraMap ℤ ℚ)) = (-76 : ℚ) := by
      rw [Commons.Polynomial.discr_map_int gaux hgaux, hPaux]
      norm_num
    have hpoly_f : Polynomial.discr f = -76 := by
      dsimp [f]
      rw [Polynomial.discr_of_degree_eq_three]
      · norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one]
      · compute_degree <;> norm_num
    calc
      (NumberField.discr (AdjoinRoot f) : ℚ) =
          (NumberField.discr (AdjoinRoot (gaux.map (algebraMap ℤ ℚ))) : ℚ) := hisoQ.symm
      _ = Polynomial.discr (gaux.map (algebraMap ℤ ℚ)) := hdirect
      _ = Polynomial.discr f := by rw [hdisc_aux_map, hpoly_f]
  · letI := fact_irreducible_cubic_2_0_neg2_Q
    exact discr_adjoinRoot_direct_2_0_neg2

end Commons.NumberTheory.NumberField