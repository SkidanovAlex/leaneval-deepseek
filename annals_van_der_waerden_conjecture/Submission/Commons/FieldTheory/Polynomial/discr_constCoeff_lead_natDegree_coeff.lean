import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le
import Submission.Commons.FieldTheory.Polynomial.discr_mul
import Submission.Commons.RingTheory.Polynomial.discr_map

open Polynomial
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.FieldTheory.Polynomial

abbrev famR (R : Type*) [CommSemiring R] (n : ℕ) (c : Fin (n - 1) → R) (b : R) : R[X] :=
  X ^ n + (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)) + Polynomial.C b

abbrev scalarFam {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) (t : L) : L[X] :=
  famR L n c t

abbrev dFam {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) : L[X] :=
  Polynomial.C (n : L) * X ^ (n - 1) +
    ∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)

/-- The monic degree-`n` polynomial over `(Polynomial L)[X]` with coefficient vector
`c` on `X^1, ..., X^(n-1)` and constant coefficient the variable `Polynomial.X`. -/
abbrev varFam {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) : (Polynomial L)[X] :=
  famR (Polynomial L) n (fun j : Fin (n - 1) => Polynomial.C (c j)) (Polynomial.X : Polynomial L)

abbrev rootPoly {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) : Polynomial L :=
  ((dFam n c).roots.map (fun β : L => Polynomial.X + Polynomial.C ((scalarFam n c 0).eval β))).prod

lemma natDegree_sum_C_mul_X_pow_add_one_le {R : Type*} [CommSemiring R] (n : ℕ)
    (c : Fin (n - 1) → R) :
    (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)).natDegree ≤ n - 1 := by
  classical
  have h : (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)) =
      ∑ j ∈ (Finset.univ : Finset (Fin (n - 1))), Polynomial.C (c j) * X ^ ((j : ℕ) + 1) := by
    simp
  rw [h]
  exact natDegree_finset_sum_le (F := R) (s := Finset.univ)
    (fun j : Fin (n - 1) => Polynomial.C (c j) * X ^ ((j : ℕ) + 1)) (n - 1) (by
      intro j hj
      exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (c j) ((j : ℕ) + 1))
        (by omega))

lemma famR_natDegree {R : Type*} [CommSemiring R] [Nontrivial R] (n : ℕ) (hn : 1 ≤ n) (c : Fin (n - 1) → R)
    (b : R) : (famR R n c b).natDegree = n := by
  classical
  unfold famR
  have h1 : (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)).natDegree < n :=
    lt_of_le_of_lt (natDegree_sum_C_mul_X_pow_add_one_le n c) (by omega : n - 1 < n)
  have hdeg1 : (X ^ n + (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1))).natDegree = n := by
    rw [natDegree_add_eq_left_of_natDegree_lt (p := X ^ n)
      (q := (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)))]
    · rw [natDegree_X_pow]
    · simpa [natDegree_X_pow] using h1
  rw [natDegree_add_eq_left_of_natDegree_lt (p := X ^ n + (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)))
      (q := Polynomial.C b)]
  · exact hdeg1
  · rw [natDegree_C, hdeg1]
    omega

lemma famR_monic {R : Type*} [CommSemiring R] [Nontrivial R] (n : ℕ) (hn : 1 ≤ n) (c : Fin (n - 1) → R)
    (b : R) : (famR R n c b).Monic := by
  classical
  rw [Monic, leadingCoeff, famR_natDegree (R := R) n hn c b]
  unfold famR
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hsum : (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)).coeff n = 0 := by
    rw [show (∑ j : Fin (n - 1), Polynomial.C (c j) * X ^ ((j : ℕ) + 1)) =
        ∑ j ∈ (Finset.univ : Finset (Fin (n - 1))), Polynomial.C (c j) * X ^ ((j : ℕ) + 1) by simp]
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_C_mul_X_pow]
    have hne : n ≠ (j : ℕ) + 1 := by omega
    simp [hne]
  have hC : (Polynomial.C b : R[X]).coeff n = 0 := by
    rw [Polynomial.coeff_C]
    simp [show n ≠ 0 by omega]
  rw [hsum, hC]
  simp

lemma dFam_eq_derivative_scalarFam {L : Type*} [Field L] (n : ℕ) (hn : 1 ≤ n)
    (c : Fin (n - 1) → L) (t : L) : (scalarFam n c t).derivative = dFam n c := by
  unfold scalarFam dFam famR
  rw [derivative_add, derivative_add]
  rw [derivative_X_pow, derivative_C]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]
  rw [add_zero]
  apply congrArg (fun s : L[X] => Polynomial.C (n : L) * X ^ (n - 1) + s)
  exact Finset.sum_congr (ι := Fin (n - 1)) (M := L[X]) rfl (by
    intro x hx
    rw [show (↑x : ℕ) + 1 - 1 = ↑x by omega]
    have hcast : (↑((x : ℕ) + 1) : L) = ((x : ℕ) : L) + 1 := by simp
    rw [hcast, mul_comm (c x) (((x : ℕ) : L) + 1)])

lemma dFam_natDegree {L : Type*} [Field L] (n : ℕ) (hn : 2 ≤ n) (c : Fin (n - 1) → L)
    (hnc : (n : L) ≠ 0) : (dFam n c).natDegree = n - 1 := by
  unfold dFam
  have htail : (∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)).natDegree ≤ n - 2 := by
    rw [show (∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)) =
        ∑ j ∈ (Finset.univ : Finset (Fin (n - 1))), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ) by simp]
    exact natDegree_finset_sum_le (F := L) (s := (Finset.univ : Finset (Fin (n - 1))))
      (fun j : Fin (n - 1) => Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)) (n - 2) (by
        intro j hj
        exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (((j : ℕ) + 1 : L) * c j) (j : ℕ))
          (by omega))
  rw [natDegree_add_eq_left_of_natDegree_lt (p := Polynomial.C (n : L) * X ^ (n - 1))
      (q := (∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)))]
  · rw [Polynomial.natDegree_C_mul hnc, natDegree_X_pow]
  · rw [Polynomial.natDegree_C_mul hnc, natDegree_X_pow]
    omega

lemma dFam_leadingCoeff {L : Type*} [Field L] (n : ℕ) (hn : 2 ≤ n) (c : Fin (n - 1) → L)
    (hnc : (n : L) ≠ 0) : (dFam n c).leadingCoeff = (n : L) := by
  rw [leadingCoeff, dFam_natDegree n hn c hnc]
  unfold dFam
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X_pow]
  rw [if_pos rfl]
  have hsum : (∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)).coeff (n - 1) = 0 := by
    rw [show (∑ j : Fin (n - 1), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ)) =
        ∑ j ∈ (Finset.univ : Finset (Fin (n - 1))), Polynomial.C (((j : ℕ) + 1 : L) * c j) * X ^ (j : ℕ) by simp]
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_C_mul_X_pow]
    have hne : n - 1 ≠ (j : ℕ) := by omega
    simp [hne]
  rw [hsum]
  simp

lemma scalarFam_add_const {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) (t : L) :
    scalarFam n c t = scalarFam n c 0 + Polynomial.C t := by
  unfold scalarFam famR
  simp [add_assoc]

lemma scalarFam_monic {L : Type*} [Field L] (n : ℕ) (hn : 1 ≤ n) (c : Fin (n - 1) → L) (t : L) :
    (scalarFam n c t).Monic := by
  unfold scalarFam
  exact famR_monic (R := L) n hn c t

lemma scalarFam_natDegree {L : Type*} [Field L] (n : ℕ) (hn : 1 ≤ n) (c : Fin (n - 1) → L) (t : L) :
    (scalarFam n c t).natDegree = n := by
  unfold scalarFam
  exact famR_natDegree (R := L) n hn c t

lemma even_n_mul_pred (n : ℕ) : Even (n * (n - 1)) := by
  have h := Nat.even_mul_pred_self n
  simpa [mul_comm] using h

lemma discr_scalarFam_of_algClosed {L : Type*} [Field L] [IsAlgClosed L] (n : ℕ) (hn : 2 ≤ n)
    (c : Fin (n - 1) → L) (hnc : (n : L) ≠ 0) (t : L) :
    Polynomial.discr (scalarFam n c t) =
      (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n *
        ((dFam n c).roots.map (fun β : L => Polynomial.eval β (scalarFam n c t))).prod := by
  classical
  let p : L[X] := scalarFam n c t
  let q : L[X] := dFam n c
  change Polynomial.discr p = (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n *
      (q.roots.map (fun β : L => Polynomial.eval β p)).prod
  have hp_monic : p.Monic := by dsimp [p]; exact scalarFam_monic n (by omega) c t
  have hp_deg : p.natDegree = n := by dsimp [p]; exact scalarFam_natDegree n (by omega) c t
  have hq_def : p.derivative = q := by
    dsimp [p, q]
    exact dFam_eq_derivative_scalarFam n (by omega) c t
  have hq_deg : q.natDegree = n - 1 := by dsimp [q]; exact dFam_natDegree n hn c hnc
  have hq_lc : q.leadingCoeff = (n : L) := by dsimp [q]; exact dFam_leadingCoeff n hn c hnc
  have hpos : 0 < p.natDegree := by rw [hp_deg]; omega
  have hneg : (-1 : L) ^ (n * (n - 1)) = 1 := by
    rcases (even_n_mul_pred n) with ⟨k, hk⟩
    rw [hk, pow_add]
    exact Commons.FieldTheory.Polynomial.negOne_pow_mul_self k
  have hdisc : Polynomial.discr p =
      (-1 : L) ^ (n * (n - 1) / 2) * (p.resultant q n (n - 1)) := by
    rw [discr_eq_signed_resultant p hp_monic hpos]
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
  calc
    Polynomial.discr p = (-1 : L) ^ (n * (n - 1) / 2) * (p.resultant q n (n - 1)) := hdisc
    _ = (-1 : L) ^ (n * (n - 1) / 2) * (q.resultant p (n - 1) n) := by rw [hres_comm]
    _ = (-1 : L) ^ (n * (n - 1) / 2) *
          (q.leadingCoeff ^ n * (q.roots.map (fun β => Polynomial.eval β p)).prod) := by rw [hqe']
    _ = (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n *
          (q.roots.map (fun β => Polynomial.eval β p)).prod := by
          rw [hq_lc]
          ring

lemma varFam_monic {L : Type*} [Field L] (n : ℕ) (hn : 1 ≤ n) (c : Fin (n - 1) → L) :
    (varFam n c).Monic := by
  unfold varFam
  exact famR_monic (R := Polynomial L) n hn (fun j : Fin (n - 1) => Polynomial.C (c j))
    (Polynomial.X : Polynomial L)

lemma varFam_map_eval {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) (t₀ : L) :
    (varFam n c).map (Polynomial.eval₂RingHom (RingHom.id L) t₀) = scalarFam n c t₀ := by
  unfold varFam scalarFam famR
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow]
  simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval₂_C, Polynomial.eval₂_X]

lemma rootPoly_monic {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) :
    (rootPoly n c).Monic := by
  unfold rootPoly
  apply multiset_prod_monic
  intro p hp
  rcases Multiset.mem_map.mp hp with ⟨β, hβmem, rfl⟩
  exact Polynomial.monic_X_add_C _

lemma rootPoly_natDegree {L : Type*} [Field L] [IsAlgClosed L] (n : ℕ) (hn : 2 ≤ n)
    (c : Fin (n - 1) → L) (hnc : (n : L) ≠ 0) : (rootPoly n c).natDegree = n - 1 := by
  classical
  unfold rootPoly
  have hcard : (dFam n c).roots.card = n - 1 := by
    rw [← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits (dFam n c))]
    exact dFam_natDegree n hn c hnc
  have hmon : ∀ p ∈ (dFam n c).roots.map (fun β : L => Polynomial.X + Polynomial.C ((scalarFam n c 0).eval β)),
      p.Monic := by
    intro p hp
    rcases Multiset.mem_map.mp hp with ⟨β, hβmem, rfl⟩
    exact Polynomial.monic_X_add_C _
  rw [natDegree_multiset_prod_monic (m := (dFam n c).roots.map (fun β : L => Polynomial.X + Polynomial.C ((scalarFam n c 0).eval β))) hmon]
  rw [Multiset.map_map]
  have h1 : (dFam n c).roots.map (fun β : L => Polynomial.natDegree
      (Polynomial.X + Polynomial.C ((scalarFam n c 0).eval β))) =
      (dFam n c).roots.map (fun _ : L => 1) := by
    apply Multiset.map_congr rfl
    intro β hβ
    exact Polynomial.natDegree_X_add_C _
  change (Multiset.map (fun β : L => (Polynomial.X + Polynomial.C ((scalarFam n c 0).eval β)).natDegree)
      (dFam n c).roots).sum = n - 1
  rw [h1]
  simp [hcard]

-- evaluate the rootPoly at t₀
lemma rootPoly_eval {L : Type*} [Field L] (n : ℕ) (c : Fin (n - 1) → L) (t₀ : L) :
    Polynomial.eval t₀ (rootPoly n c) =
      ((dFam n c).roots.map (fun β : L => t₀ + (scalarFam n c 0).eval β)).prod := by
  unfold rootPoly
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro β hβ
  simp

lemma varFam_discr_eq_rootPoly {L : Type*} [Field L] [IsAlgClosed L] (n : ℕ) (hn : 2 ≤ n)
    (c : Fin (n - 1) → L) (hnc : (n : L) ≠ 0) :
    Polynomial.discr (varFam n c) =
      Polynomial.C ((-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n) * rootPoly n c := by
  classical
  let D : Polynomial L := Polynomial.discr (varFam n c)
  let c' : L := (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n
  let Q : Polynomial L := Polynomial.C c' * rootPoly n c
  change D = Q
  have hEq : ∀ t₀ : L, Polynomial.eval t₀ D = Polynomial.eval t₀ Q := by
    intro t₀
    have hD : Polynomial.eval t₀ D = Polynomial.discr (scalarFam n c t₀) := by
      dsimp [D]
      let φ : (Polynomial L) →+* L := Polynomial.eval₂RingHom (RingHom.id L) t₀
      have hφq : ∀ q : Polynomial L, φ q = Polynomial.eval t₀ q := by intro q; rfl
      have hmon : (varFam n c).Monic := varFam_monic n (by omega) c
      have hdm := Commons.RingTheory.Polynomial.discr_map (R := Polynomial L) (S := L) φ hmon
      calc
        Polynomial.eval t₀ (Polynomial.discr (varFam n c))
            = φ (Polynomial.discr (varFam n c)) := by rw [hφq]
        _ = Polynomial.discr ((varFam n c).map φ) := hdm.symm
        _ = Polynomial.discr (scalarFam n c t₀) := by rw [varFam_map_eval n c t₀]
    have hQ : Polynomial.eval t₀ Q =
        c' * ((dFam n c).roots.map (fun β : L => t₀ + (scalarFam n c 0).eval β)).prod := by
      dsimp [Q]
      rw [Polynomial.eval_mul, Polynomial.eval_C, rootPoly_eval]
    have hmap_roots : (dFam n c).roots.map (fun β : L => Polynomial.eval β (scalarFam n c t₀)) =
        (dFam n c).roots.map (fun β : L => t₀ + (scalarFam n c 0).eval β) := by
      apply Multiset.map_congr rfl
      intro β hβ
      calc
        Polynomial.eval β (scalarFam n c t₀)
            = Polynomial.eval β (scalarFam n c 0 + Polynomial.C t₀) := by rw [scalarFam_add_const]
        _ = Polynomial.eval β (scalarFam n c 0) + t₀ := by simp
        _ = t₀ + (scalarFam n c 0).eval β := by ring
    have hsc := discr_scalarFam_of_algClosed n hn c hnc t₀
    calc
      Polynomial.eval t₀ D = Polynomial.discr (scalarFam n c t₀) := hD
      _ = c' * ((dFam n c).roots.map (fun β : L => Polynomial.eval β (scalarFam n c t₀))).prod := by
            dsimp [c']
            rw [hsc]
      _ = c' * ((dFam n c).roots.map (fun β : L => t₀ + (scalarFam n c 0).eval β)).prod := by
            rw [hmap_roots]
      _ = Polynomial.eval t₀ Q := hQ.symm
  have hgz : ∀ t₀ : L, Polynomial.eval t₀ (D - Q) = 0 := by
    intro t₀
    rw [Polynomial.eval_sub, sub_eq_zero]
    exact hEq t₀
  have hset : Set.Infinite {x : L | Polynomial.eval x (D - Q) = 0} := by
    rw [Set.eq_univ_of_forall (fun x => hgz x)]
    exact Set.infinite_univ
  have hz : D - Q = 0 := Polynomial.eq_zero_of_infinite_isRoot (D - Q) (by simpa [Polynomial.IsRoot] using hset)
  calc
    D = (D - Q) + Q := by ring
    _ = Q := by rw [hz, zero_add]

theorem varFam_discr_natDegree_coeff_of_algClosed {L : Type*} [Field L] [IsAlgClosed L] (n : ℕ)
    (hn : 2 ≤ n) (c : Fin (n - 1) → L) (hnc : (n : L) ≠ 0) :
    (Polynomial.discr (varFam n c) : Polynomial L).natDegree = n - 1 ∧
      (Polynomial.discr (varFam n c)).coeff (n - 1) =
        (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n := by
  classical
  constructor
  · rw [varFam_discr_eq_rootPoly n hn c hnc]
    -- natDegree of C(c')*rootPoly
    have hrp : (rootPoly n c).natDegree = n - 1 := rootPoly_natDegree n hn c hnc
    have hc' : ((-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (by norm_num : (-1 : L) ≠ 0)
      · exact pow_ne_zero n hnc
    rw [Polynomial.natDegree_C_mul hc']
    exact hrp
  · rw [varFam_discr_eq_rootPoly n hn c hnc]
    rw [Polynomial.coeff_C_mul]
    have hrp : (rootPoly n c).natDegree = n - 1 := rootPoly_natDegree n hn c hnc
    have hmon : (rootPoly n c).Monic := rootPoly_monic n c
    rw [show (rootPoly n c).coeff (n - 1) = 1 by
      rw [← hmon.coeff_natDegree]
      rw [hrp]]
    simp



theorem discr_constCoeff_lead_natDegree_coeff {F : Type*} [Field F] (n : ℕ) (hn : 2 ≤ n) (hnc : (n : F) ≠ 0) :
    let P := MvPolynomial (Fin (n - 1)) F
    let fam : (Polynomial P)[X] :=
      X ^ n + (∑ j : Fin (n - 1), Polynomial.C (Polynomial.C (MvPolynomial.X j)) * X ^ ((j : ℕ) + 1)) +
        Polynomial.C (Polynomial.X : Polynomial P)
    let inner : Polynomial P := Polynomial.discr fam
    inner.natDegree = n - 1 ∧
      inner.coeff (n - 1) = MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n) := by
  classical
  change (Polynomial.discr (famR (Polynomial (MvPolynomial (Fin (n - 1)) F)) n
    (fun j : Fin (n - 1) => Polynomial.C (MvPolynomial.X j))
    (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)))).natDegree = n - 1 ∧
    (Polynomial.discr (famR (Polynomial (MvPolynomial (Fin (n - 1)) F)) n
    (fun j : Fin (n - 1) => Polynomial.C (MvPolynomial.X j))
    (Polynomial.X : Polynomial (MvPolynomial (Fin (n - 1)) F)))).coeff (n - 1) =
      MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n)
  let P := MvPolynomial (Fin (n - 1)) F
  let fam : (Polynomial P)[X] := famR (Polynomial P) n (fun j : Fin (n - 1) => Polynomial.C (MvPolynomial.X j)) (Polynomial.X : Polynomial P)
  let inner : Polynomial P := Polynomial.discr fam
  change inner.natDegree = n - 1 ∧ inner.coeff (n - 1) =
      MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n)
  let K := FractionRing P
  let L := AlgebraicClosure K
  let ψ : P →+* L := (algebraMap K L).comp (algebraMap P K)
  have hψi : Function.Injective ψ := by
    dsimp [ψ]
    exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective P K)
  have hLchar : (n : L) ≠ 0 := by
    intro hz
    have hmKL : (algebraMap K L) ((n : K)) = (n : L) := by rw [map_natCast]
    have hzK : (n : K) = 0 := by
      exact (RingHom.injective (algebraMap K L) (a₁ := (n : K)) (a₂ := 0)) (by rw [hmKL, map_zero]; exact hz)
    have hmPK : (algebraMap P K) ((n : P)) = (n : K) := by rw [map_natCast]
    have hzP : (n : P) = 0 := by
      exact (IsFractionRing.injective P K (a₁ := (n : P)) (a₂ := 0)) (by rw [hmPK, map_zero]; exact hzK)
    have hmFP : (MvPolynomial.C : F →+* P) ((n : F)) = (n : P) := by rw [map_natCast]
    have hzF : (n : F) = 0 := by
      exact (MvPolynomial.C_injective (Fin (n - 1)) F (a₁ := (n : F)) (a₂ := 0)) (by rw [hmFP, map_zero]; exact hzP)
    exact hnc hzF
  let cL : Fin (n - 1) → L := fun j => ψ (MvPolynomial.X j)
  have hVar := varFam_discr_natDegree_coeff_of_algClosed (L := L) n hn cL hLchar
  let σ : (Polynomial P) →+* (Polynomial L) := Polynomial.mapRingHom ψ
  have hσi : Function.Injective σ := by
    exact Polynomial.map_injective ψ hψi
  have hfam_map : fam.map σ = varFam n cL := by
    dsimp [fam, varFam, σ, cL]
    unfold famR
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow]
    simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_pow, Polynomial.mapRingHom]
  have hmon : fam.Monic := by
    dsimp [fam]
    exact famR_monic (R := Polynomial P) n (by omega) (fun j : Fin (n - 1) => Polynomial.C (MvPolynomial.X j)) (Polynomial.X : Polynomial P)
  have hσ_inner : σ inner = Polynomial.discr (varFam n cL) := by
    dsimp [inner]
    calc
      σ (Polynomial.discr fam) = Polynomial.discr (fam.map σ) :=
        (Commons.RingTheory.Polynomial.discr_map (R := Polynomial P) (S := Polynomial L) σ hmon).symm
      _ = Polynomial.discr (varFam n cL) := by rw [hfam_map]
  constructor
  · rw [← natDegree_map_eq_of_injective hψi inner]
    change (σ inner).natDegree = n - 1
    rw [hσ_inner]
    exact hVar.1
  · have hc : ψ (inner.coeff (n - 1)) = (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n := by
      calc
        ψ (inner.coeff (n - 1)) = (σ inner).coeff (n - 1) := by
          change ψ (inner.coeff (n - 1)) = (Polynomial.map ψ inner).coeff (n - 1)
          rw [Polynomial.coeff_map]
        _ = (Polynomial.discr (varFam n cL)).coeff (n - 1) := by rw [hσ_inner]
        _ = (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n := hVar.2
    let ψF : F →+* L := ψ.comp (MvPolynomial.C : F →+* P)
    have hRHS : ψ (MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n)) =
        (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n := by
      have hψF_neg : ψF (-1 : F) = (-1 : L) := by
        dsimp [ψF]
        simp
      have hψF_nat : ψF (n : F) = (n : L) := by
        dsimp [ψF]
        simp
      calc
        ψ (MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n))
            = ψF ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n) := by rfl
        _ = ψF ((-1 : F) ^ (n * (n - 1) / 2)) * ψF ((n : F) ^ n) := by rw [map_mul]
        _ = (ψF (-1 : F)) ^ (n * (n - 1) / 2) * (ψF (n : F)) ^ n := by rw [map_pow, map_pow]
        _ = (-1 : L) ^ (n * (n - 1) / 2) * (n : L) ^ n := by rw [hψF_neg, hψF_nat]
    apply hψi
    rw [show ψ (inner.coeff (n - 1)) = ψ (MvPolynomial.C ((-1 : F) ^ (n * (n - 1) / 2) * (n : F) ^ n)) by
      rw [hc, hRHS]]

end Commons.FieldTheory.Polynomial