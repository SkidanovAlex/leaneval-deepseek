import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Commons.FieldTheory.Polynomial.discr_mul

open Polynomial
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.FieldTheory.Polynomial

variable {F : Type*} [Field F]

private lemma degree_tail_le_one (b c : F) :
    ((C b * X + C c : F[X])).degree ≤ (1 : WithBot ℕ) := by
  exact (Polynomial.degree_add_le (C b * X) (C c)).trans
    (max_le (Polynomial.degree_C_mul_X_le b)
      (Polynomial.degree_C_le.trans (by norm_num : (0 : WithBot ℕ) ≤ (1 : WithBot ℕ))))

private lemma tail_lt_X_pow (n : ℕ) (hn : 2 ≤ n) (b c : F) :
    ((C b * X + C c : F[X])).degree < (X ^ n : F[X]).degree := by
  rw [Polynomial.degree_X_pow]
  exact (degree_tail_le_one b c).trans_lt (by exact_mod_cast (by omega : 1 < n))

private lemma natDegree_X_pow_add_C_mul_X_add_C (n : ℕ) (hn : 2 ≤ n) (b c : F) :
    (X ^ n + C b * X + C c : F[X]).natDegree = n := by
  have hdeg : (X ^ n + (C b * X + C c) : F[X]).degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt (tail_lt_X_pow n hn b c), Polynomial.degree_X_pow]
  have hnat : (X ^ n + (C b * X + C c) : F[X]).natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg
  simpa [add_assoc] using hnat

private lemma monic_X_pow_add_C_mul_X_add_C (n : ℕ) (hn : 2 ≤ n) (b c : F) :
    (X ^ n + C b * X + C c : F[X]).Monic := by
  have hm : (X ^ n + (C b * X + C c) : F[X]).Monic :=
    Polynomial.monic_X_pow_add (by simpa [Polynomial.degree_X_pow] using (tail_lt_X_pow n hn b c))
  simpa [add_assoc] using hm

private lemma derivative_X_pow_add_C_mul_X_add_C (n : ℕ) (b c : F) :
    (X ^ n + C b * X + C c : F[X]).derivative = C (n : F) * X ^ (n - 1) + C b := by
  rw [derivative_add, derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C]
  simp

private lemma pow_succ_nat {K : Type*} [Semiring K] (n : ℕ) (hn : 0 < n) (a : K) :
    a ^ n = a * a ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

private lemma wv_pow {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) (b : K) (hnz : (n : K) ≠ 0) :
    (-b / (n : K)) * (b * (n - 1 : K) / (n : K)) ^ (n - 1) =
      -b ^ n * (n - 1 : K) ^ (n - 1) / (n : K) ^ n := by
  have hbpow : b * b ^ (n - 1) = b ^ n := (pow_succ_nat n hn b).symm
  calc
    (-b / (n : K)) * (b * (n - 1 : K) / (n : K)) ^ (n - 1)
        = (-b / (n : K)) * ((b * (n - 1 : K)) ^ (n - 1) / (n : K) ^ (n - 1)) := by
          rw [div_pow]
    _ = (-b / (n : K)) * (b ^ (n - 1) * (n - 1 : K) ^ (n - 1) / (n : K) ^ (n - 1)) := by
          rw [mul_pow]
    _ = -b ^ n * (n - 1 : K) ^ (n - 1) / (n : K) ^ n := by
          field_simp [hnz, pow_ne_zero (n - 1) hnz]
          rw [pow_succ_nat n hn (n : K)]
          rw [hbpow]
          ring

private lemma inner_n_pow {K : Type*} [Field K] (n : ℕ) (hn : 0 < n) (b c : K)
    (hnz : (n : K) ≠ 0) :
    (n : K) ^ n * (c ^ (n - 1) - (-1 : K) ^ (n - 1) * (-b / (n : K)) *
      (b * (n - 1 : K) / (n : K)) ^ (n - 1)) =
      (n : K) ^ n * c ^ (n - 1) + (-1 : K) ^ (n - 1) * (n - 1 : K) ^ (n - 1) * b ^ n := by
  rw [show (-1 : K) ^ (n - 1) * (-b / (n : K)) * (b * (n - 1 : K) / (n : K)) ^ (n - 1) =
      (-1 : K) ^ (n - 1) * ((-b / (n : K)) * (b * (n - 1 : K) / (n : K)) ^ (n - 1)) by ring]
  rw [wv_pow n hn b hnz]
  field_simp [hnz, pow_ne_zero n hnz]
  ring

private lemma prod_nthRoots_linear' {K : Type*} [Field K] (m : ℕ) (hm : 0 < m) (u v w : K)
    (hsplit : ((X : K[X]) ^ m - C w).Splits) :
    (((Polynomial.nthRoots m w).map (fun β => u + v * β)).prod) =
      u ^ m - (-1 : K) ^ m * w * v ^ m := by
  classical
  let M : Multiset K := Polynomial.nthRoots m w
  have hcard : M.card = m := by
    dsimp [M, Polynomial.nthRoots]
    rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit]
    exact Polynomial.natDegree_X_pow_sub_C
  have hfac : (X : K[X]) ^ m - C w = (M.map fun β => X - C β).prod := by
    dsimp [M, Polynomial.nthRoots]
    exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (p := (X : K[X]) ^ m - C w) (Polynomial.monic_X_pow_sub_C w (by omega : m ≠ 0))
        (Polynomial.Splits.natDegree_eq_card_roots hsplit).symm).symm
  by_cases hv : v = 0
  · have hme : M.map (fun β => u + 0 * β) = M.map (fun _ : K => u) := by
      apply Multiset.map_congr rfl
      intro β hβ
      ring
    have hprod : (M.map (fun β => u + 0 * β)).prod = u ^ m := by
      calc
        (M.map (fun β => u + 0 * β)).prod = (M.map (fun _ : K => u)).prod := by rw [hme]
        _ = (Multiset.replicate (M.card) u).prod := by
          simpa using (Multiset.map_const M u : M.map (Function.const K u) = Multiset.replicate M.card u)
        _ = u ^ M.card := by rw [Multiset.prod_replicate]
        _ = u ^ m := by rw [hcard]
    rw [hv]
    change (M.map (fun β => u + 0 * β)).prod = u ^ m - (-1 : K) ^ m * w * 0 ^ m
    rw [hprod]
    rw [zero_pow (by omega : m ≠ 0)]
    ring
  · let S : K := ((Polynomial.nthRoots m w).map (fun β => u + v * β)).prod
    let x : K := -u / v
    change S = u ^ m - (-1 : K) ^ m * w * v ^ m
    have hx : x ^ m - w = (M.map (fun β => x - β)).prod := by
      calc
        x ^ m - w = Polynomial.eval x ((X : K[X]) ^ m - C w) := by simp
        _ = Polynomial.eval x ((M.map (fun β => X - C β)).prod) := by rw [hfac]
        _ = (M.map (fun β => x - β)).prod := by
          rw [Polynomial.eval_multiset_prod, Multiset.map_map]
          apply congrArg Multiset.prod
          apply Multiset.map_congr rfl
          intro β hβ
          simp
    have hme' : M.map (fun β => x - β) = M.map (fun β => (-v⁻¹) * (u + v * β)) := by
      apply Multiset.map_congr rfl
      intro β hβ
      dsimp [x]
      field_simp [hv]
      ring
    have hmap : (M.map (fun β => x - β)).prod = (-v⁻¹) ^ m * S := by
      calc
        (M.map (fun β => x - β)).prod = (M.map (fun β => (-v⁻¹) * (u + v * β))).prod := by
          rw [hme']
        _ = (M.map (fun _ : K => -v⁻¹)).prod * S := by
          dsimp [S]
          rw [Multiset.prod_map_mul]
        _ = (-v⁻¹) ^ m * S := by
          rw [show M.map (fun _ : K => -v⁻¹) = Multiset.replicate M.card (-v⁻¹) by
            simpa using (Multiset.map_const M (-v⁻¹) : M.map (Function.const K (-v⁻¹)) = Multiset.replicate M.card (-v⁻¹))]
          rw [Multiset.prod_replicate, hcard]
    have hE : x ^ m - w = (-v⁻¹) ^ m * S := by rw [hx, hmap]
    have hcore : (-v⁻¹) * (-v) = (1 : K) := by
      field_simp [hv]
    have hmulpow : (-v⁻¹) ^ m * (-v) ^ m = 1 := by
      rw [← mul_pow, hcore, one_pow]
    have hprod : S = (x ^ m - w) * (-v) ^ m := by
      calc
        S = 1 * S := by ring
        _ = ((-v⁻¹) ^ m * (-v) ^ m) * S := by rw [hmulpow]
        _ = (-v⁻¹) ^ m * S * (-v) ^ m := by ring
        _ = (x ^ m - w) * (-v) ^ m := by rw [← hE]
    have hx' : x * -v = u := by
      dsimp [x]
      field_simp [hv]
    have h1 : (x * -v) ^ m = u ^ m := by rw [hx']
    have hfin : (x ^ m - w) * (-v) ^ m = u ^ m - (-1 : K) ^ m * w * v ^ m := by
      calc
        (x ^ m - w) * (-v) ^ m = x ^ m * (-v) ^ m - w * (-v) ^ m := by ring
        _ = (x * -v) ^ m - w * (-v) ^ m := by rw [← mul_pow]
        _ = u ^ m - w * (-v) ^ m := by rw [h1]
        _ = u ^ m - w * ((-1 : K) ^ m * v ^ m) := by rw [neg_pow]
        _ = u ^ m - (-1 : K) ^ m * w * v ^ m := by ring
    rw [hprod, hfin]

private lemma q_natDegree {K : Type*} [Field K] (n : ℕ) (hn : 2 ≤ n) (b : K) (hnz : (n : K) ≠ 0) :
    (C (n : K) * X ^ (n - 1) + C b : K[X]).natDegree = n - 1 := by
  have hside : (C b : K[X]).natDegree < (C (n : K) * X ^ (n - 1) : K[X]).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul hnz, Polynomial.natDegree_X_pow]
    omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hside]
  rw [Polynomial.natDegree_C_mul hnz, Polynomial.natDegree_X_pow]

private lemma q_leadingCoeff {K : Type*} [Field K] (n : ℕ) (hn : 2 ≤ n) (b : K) (hnz : (n : K) ≠ 0) :
    (C (n : K) * X ^ (n - 1) + C b : K[X]).leadingCoeff = (n : K) := by
  rw [Polynomial.leadingCoeff, q_natDegree n hn b hnz]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  have hn10 : n - 1 ≠ 0 := by omega
  simp [hn10]

private theorem discr_X_pow_add_mul_add_of_algClosed {K : Type*} [Field K] [IsAlgClosed K]
    (n : ℕ) (hn : 2 ≤ n) (b c : K) (hnz : (n : K) ≠ 0) :
    Polynomial.discr (X ^ n + C b * X + C c) =
      (-1 : K) ^ (n * (n - 1) / 2) *
        (((n : K) ^ n) * (c ^ (n - 1)) +
          (-1 : K) ^ (n - 1) * (((n - 1 : K) ^ (n - 1)) * (b ^ n))) := by
  classical
  let p : K[X] := X ^ n + C b * X + C c
  let q : K[X] := C (n : K) * X ^ (n - 1) + C b
  let w : K := -b / (n : K)
  let v : K := b * (n - 1 : K) / (n : K)
  change Polynomial.discr p = (-1 : K) ^ (n * (n - 1) / 2) *
    (((n : K) ^ n) * (c ^ (n - 1)) + (-1 : K) ^ (n - 1) * (((n - 1 : K) ^ (n - 1)) * (b ^ n)))
  have hp_monic : p.Monic := by dsimp [p]; exact monic_X_pow_add_C_mul_X_add_C n hn b c
  have hp_deg : p.natDegree = n := by dsimp [p]; exact natDegree_X_pow_add_C_mul_X_add_C n hn b c
  have hq_def : p.derivative = q := by
    dsimp [p, q]
    exact derivative_X_pow_add_C_mul_X_add_C n b c
  have hq_deg : q.natDegree = n - 1 := by dsimp [q]; exact q_natDegree n hn b hnz
  have hq_lc : q.leadingCoeff = (n : K) := by dsimp [q]; exact q_leadingCoeff n hn b hnz
  have hpos : 0 < p.natDegree := by rw [hp_deg]; omega
  have heven : Even (n * (n - 1)) := by
    have h := Nat.even_mul_succ_self (n - 1)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
    simpa [hn1, mul_comm] using h
  have hneg : (-1 : K) ^ (n * (n - 1)) = 1 := by
    rcases heven with ⟨k, hk⟩
    rw [hk, pow_add]
    exact Commons.FieldTheory.Polynomial.negOne_pow_mul_self k
  have hdisc : Polynomial.discr p = (-1 : K) ^ (n * (n - 1) / 2) * (p.resultant q n (n - 1)) := by
    rw [Commons.FieldTheory.Polynomial.discr_eq_signed_resultant p hp_monic hpos]
    rw [hq_def]
    rw [hp_deg]
  have hres_comm : p.resultant q n (n - 1) = q.resultant p (n - 1) n := by
    rw [Polynomial.resultant_comm]
    rw [hneg]
    simp
  have hqe : q.resultant p q.natDegree n =
      q.leadingCoeff ^ n * (q.roots.map (fun β => Polynomial.eval β p)).prod := by
    exact Polynomial.resultant_eq_prod_eval q p n (by rw [hp_deg]) (IsAlgClosed.splits q)
  have hqe' : q.resultant p (n - 1) n =
      q.leadingCoeff ^ n * (q.roots.map (fun β => Polynomial.eval β p)).prod := by
    rw [hq_deg] at hqe
    exact hqe
  have hw : (n : K) * w = -b := by
    dsimp [w]
    field_simp [hnz]
  have hqeq : q = C (n : K) * ((X : K[X]) ^ (n - 1) - C w) := by
    calc
      q = C (n : K) * X ^ (n - 1) + C b := by dsimp [q]
      _ = C (n : K) * X ^ (n - 1) - C ((n : K) * w) := by
            rw [hw]
            rw [Polynomial.C_neg]
            ring
      _ = C (n : K) * X ^ (n - 1) - C (n : K) * C w := by rw [Polynomial.C_mul]
      _ = C (n : K) * (X ^ (n - 1) - C w) := by rw [mul_sub]
  have hqroots : q.roots = Polynomial.nthRoots (n - 1) w := by
    rw [hqeq]
    rw [Polynomial.roots_C_mul ((X : K[X]) ^ (n - 1) - C w) hnz]
    rfl
  have hmap_eq : q.roots.map (fun β => Polynomial.eval β p) =
      q.roots.map (fun β => c + v * β) := by
    apply Multiset.map_congr rfl
    intro β hβ
    have hβ' : β ∈ Polynomial.nthRoots (n - 1) w := by
      rw [← hqroots]
      exact hβ
    have hpowβ : β ^ (n - 1) = w := (Polynomial.mem_nthRoots (by omega : 0 < n - 1)).mp hβ'
    have hpown : β ^ n = β ^ (n - 1) * β := by
      calc
        β ^ n = β ^ (n - 1 + 1) := congrArg (fun t : ℕ => β ^ t) (by omega : n = n - 1 + 1)
        _ = β ^ (n - 1) * β := pow_succ β (n - 1)
    dsimp [p, v]
    calc
      Polynomial.eval β (X ^ n + C b * X + C c) = β ^ n + b * β + c := by
        simp
      _ = β ^ (n - 1) * β + b * β + c := by rw [hpown]
      _ = w * β + b * β + c := by rw [hpowβ]
      _ = c + (w + b) * β := by ring
      _ = c + (b * (n - 1 : K) / (n : K)) * β := by
            congr 2
            dsimp [w]
            field_simp [hnz]
            ring
  have hprod_vals : (q.roots.map (fun β => Polynomial.eval β p)).prod =
      c ^ (n - 1) - (-1 : K) ^ (n - 1) * w * v ^ (n - 1) := by
    rw [hmap_eq]
    rw [hqroots]
    exact prod_nthRoots_linear' (n - 1) (by omega : 0 < n - 1) c v w
      (IsAlgClosed.splits ((X : K[X]) ^ (n - 1) - C w))
  have hres : p.resultant q n (n - 1) =
      (n : K) ^ n * (c ^ (n - 1) - (-1 : K) ^ (n - 1) * w * v ^ (n - 1)) := by
    calc
      p.resultant q n (n - 1) = q.resultant p (n - 1) n := hres_comm
      _ = q.leadingCoeff ^ n * (q.roots.map (fun β => Polynomial.eval β p)).prod := hqe'
      _ = (n : K) ^ n * (c ^ (n - 1) - (-1 : K) ^ (n - 1) * w * v ^ (n - 1)) := by
            rw [hq_lc, hprod_vals]
  have hmain : (n : K) ^ n * (c ^ (n - 1) - (-1 : K) ^ (n - 1) * w * v ^ (n - 1)) =
      (n : K) ^ n * c ^ (n - 1) + (-1 : K) ^ (n - 1) * (n - 1 : K) ^ (n - 1) * b ^ n := by
    simpa [w, v] using (inner_n_pow n (by omega : 0 < n) b c hnz)
  calc
    Polynomial.discr p = (-1 : K) ^ (n * (n - 1) / 2) * (p.resultant q n (n - 1)) := hdisc
    _ = (-1 : K) ^ (n * (n - 1) / 2) *
          ((n : K) ^ n * (c ^ (n - 1) - (-1 : K) ^ (n - 1) * w * v ^ (n - 1))) := by rw [hres]
    _ = (-1 : K) ^ (n * (n - 1) / 2) *
          ((n : K) ^ n * c ^ (n - 1) + (-1 : K) ^ (n - 1) * (n - 1 : K) ^ (n - 1) * b ^ n) := by
          rw [hmain]
    _ = (-1 : K) ^ (n * (n - 1) / 2) *
          (((n : K) ^ n) * (c ^ (n - 1)) +
            (-1 : K) ^ (n - 1) * (((n - 1 : K) ^ (n - 1)) * (b ^ n))) := by
          ring

theorem discr_X_pow_add_mul_add {F : Type*} [Field F] (n : ℕ) (hn : 2 ≤ n) (b c : F) :
    Polynomial.discr (X ^ n + Polynomial.C b * X + Polynomial.C c) =
      (-1 : F) ^ (n * (n - 1) / 2) *
        (((n : F) ^ n) * (c ^ (n - 1)) +
          (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n))) := by
  classical
  by_cases hnz : (n : F) ≠ 0
  · let K := AlgebraicClosure F
    let φ : F →+* K := algebraMap F K
    have hφi : Function.Injective φ := RingHom.injective φ
    have hm : φ (n : F) = (n : K) := by exact map_natCast φ n
    have hφn : (n : K) ≠ 0 := by
      intro hnK0
      apply hnz
      apply hφi
      rw [hm]
      simpa using hnK0
    let p : F[X] := X ^ n + C b * X + C c
    change Polynomial.discr p = (-1 : F) ^ (n * (n - 1) / 2) *
      (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n)))
    have hp_monic : p.Monic := by dsimp [p]; exact monic_X_pow_add_C_mul_X_add_C n hn b c
    have hK := discr_X_pow_add_mul_add_of_algClosed (K := K) (n := n) (hn := hn)
      (b := φ b) (c := φ c) hφn
    have hmap : (p.map φ) = (X ^ n + C (φ b) * X + C (φ c) : K[X]) := by
      dsimp [p]
      simp
    have hdisc_map : Polynomial.discr (p.map φ) = φ (Polynomial.discr p) := by
      exact Commons.FieldTheory.Polynomial.discr_map φ p hp_monic
    have hφK : (-1 : K) ^ (n * (n - 1) / 2) *
          (((n : K) ^ n) * ((φ c) ^ (n - 1)) +
            (-1 : K) ^ (n - 1) * (((n - 1 : K) ^ (n - 1)) * ((φ b) ^ n))) =
        φ ((-1 : F) ^ (n * (n - 1) / 2) *
          (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n)))) := by
      simp
    have hstep : φ (Polynomial.discr p) = φ ((-1 : F) ^ (n * (n - 1) / 2) *
          (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n)))) := by
      calc
        φ (Polynomial.discr p) = Polynomial.discr (p.map φ) := by rw [hdisc_map]
        _ = Polynomial.discr (X ^ n + C (φ b) * X + C (φ c) : K[X]) := by rw [hmap]
        _ = (-1 : K) ^ (n * (n - 1) / 2) *
              (((n : K) ^ n) * ((φ c) ^ (n - 1)) +
                (-1 : K) ^ (n - 1) * (((n - 1 : K) ^ (n - 1)) * ((φ b) ^ n))) := by
              rw [hK]
        _ = φ ((-1 : F) ^ (n * (n - 1) / 2) *
              (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n)))) := by
              rw [hφK]
    exact hφi hstep
  · have hn0 : (n : F) = 0 := by
      by_contra h
      exact hnz h
    let p : F[X] := X ^ n + C b * X + C c
    change Polynomial.discr p = (-1 : F) ^ (n * (n - 1) / 2) *
      (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n)))
    have hp_monic : p.Monic := by dsimp [p]; exact monic_X_pow_add_C_mul_X_add_C n hn b c
    have hp_deg : p.natDegree = n := by dsimp [p]; exact natDegree_X_pow_add_C_mul_X_add_C n hn b c
    have hpos : 0 < p.natDegree := by rw [hp_deg]; omega
    have hdisc : Polynomial.discr p = (-1 : F) ^ (n * (n - 1) / 2) *
        (p.resultant p.derivative n (n - 1)) := by
      rw [Commons.FieldTheory.Polynomial.discr_eq_signed_resultant p hp_monic hpos]
      rw [hp_deg]
    have hderiv : p.derivative = C b := by
      dsimp [p]
      rw [derivative_X_pow_add_C_mul_X_add_C]
      simp [hn0]
    have hres : p.resultant (C b) n (n - 1) = b ^ n := by
      rw [Polynomial.resultant_C_right]
      have hc : p.coeff n = 1 := by
        simpa [hp_deg] using (Polynomial.coeff_natDegree (p := p)).trans hp_monic.leadingCoeff
      rw [hc]
      simp
    have hnm1 : (n - 1 : F) = -1 := by
      rw [hn0]
      ring
    have hzero : (n : F) ^ n = 0 := by
      rw [hn0]
      exact zero_pow (by omega : n ≠ 0)
    calc
      Polynomial.discr p = (-1 : F) ^ (n * (n - 1) / 2) * (p.resultant p.derivative n (n - 1)) := hdisc
      _ = (-1 : F) ^ (n * (n - 1) / 2) * (p.resultant (C b) n (n - 1)) := by rw [hderiv]
      _ = (-1 : F) ^ (n * (n - 1) / 2) * b ^ n := by rw [hres]
      _ = (-1 : F) ^ (n * (n - 1) / 2) *
            (((n : F) ^ n) * (c ^ (n - 1)) + (-1 : F) ^ (n - 1) * (((n - 1 : F) ^ (n - 1)) * (b ^ n))) := by
          rw [hzero, hnm1, zero_mul, zero_add]
          congr 1
          rw [← mul_assoc]
          rw [Commons.FieldTheory.Polynomial.negOne_pow_mul_self (n - 1)]
          simp

end Commons.FieldTheory.Polynomial