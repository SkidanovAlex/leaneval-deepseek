import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sym.NatCard

namespace Commons.Algebra.MvPolynomial

open Finsupp

/-- The two sum conventions for the total degree of a `ℕ`-valued finsupp agree. -/
private lemma sum_eq_sum_id {α : Type*} (f : α →₀ ℕ) :
    f.sum (fun _ k => k) = f.sum (fun _ => id) := rfl

/-- Pushing forward along `Fin.succ` preserves the total degree. -/
private lemma sum_mapDomain_succ (r : ℕ) (s : Fin r →₀ ℕ) :
    (Finsupp.mapDomain Fin.succ s).sum (fun _ k => k) = s.sum (fun _ k => k) := by
  rw [Finsupp.sum_mapDomain_index]
  · intro b; rfl
  · intro b m₁ m₂; rfl

/-- The total degree of a pullback along `Fin.succ` is the sum of the values on the image. -/
private lemma sum_comapDomain_succ (r : ℕ) (T : Fin (r+1) →₀ ℕ) :
    (Finsupp.comapDomain Fin.succ T (Fin.succ_injective r).injOn).sum (fun _ k => k)
      = ∑ i : Fin r, T (Fin.succ i) := by
  show Finsupp.degree (Finsupp.comapDomain Fin.succ T (Fin.succ_injective r).injOn) = _
  rw [Finsupp.degree_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.comapDomain_apply]

/-- Splitting the total degree of a finsupp on `Fin (r+1)` into the value at `0`
and the sum of the values on the image of `Fin.succ`. -/
private lemma sum_eq_zero_add (r : ℕ) (T : Fin (r+1) →₀ ℕ) :
    T.sum (fun _ k => k) = T 0 + ∑ i : Fin r, T (Fin.succ i) := by
  show Finsupp.degree T = _
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]

/-- The standard bijection between multisets of size at most `d` in `r` variables
(only the nonzero-variable multiplicities are recorded) and multisets of size exactly `d`
in `r + 1` variables (the extra coordinate records the slack `d - (total degree)`). -/
private noncomputable def e1 (r d : ℕ) :
    {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d} ≃
    {T : Fin (r+1) →₀ ℕ // T.sum (fun _ k => k) = d} where
  toFun s :=
    ⟨Finsupp.mapDomain Fin.succ s.1
        + Finsupp.single 0 (d - s.1.sum (fun _ k => k)), by
      rw [Finsupp.sum_add_index' (fun a => rfl) (fun a b₁ b₂ => rfl),
        sum_mapDomain_succ, Finsupp.sum_single_index (h := fun _ k => k) rfl]
      exact Nat.add_sub_of_le s.2⟩
  invFun T :=
    ⟨Finsupp.comapDomain Fin.succ T.1 (Fin.succ_injective r).injOn, by
      rw [sum_comapDomain_succ]
      calc ∑ i : Fin r, T.1 (Fin.succ i)
          ≤ T.1 0 + ∑ i : Fin r, T.1 (Fin.succ i) := Nat.le_add_left _ _
        _ = d := (sum_eq_zero_add r T.1).symm.trans T.2⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    rw [Finsupp.comapDomain_apply, Finsupp.add_apply,
      Finsupp.mapDomain_apply (Fin.succ_injective r) s.1 i,
      Finsupp.single_eq_of_ne (Fin.succ_ne_zero i), add_zero]
  right_inv T := by
    apply Subtype.ext
    ext b
    induction b using Fin.cases with
    | zero =>
      rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, Finsupp.single_eq_same, zero_add]
      · rw [sum_comapDomain_succ]
        have hd : T.1 0 + ∑ i : Fin r, T.1 (Fin.succ i) = d :=
          (sum_eq_zero_add r T.1).symm.trans T.2
        omega
      · rintro ⟨i, hi⟩
        exact Fin.succ_ne_zero i hi
    | succ i =>
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Fin.succ_injective r),
        Finsupp.single_eq_of_ne (Fin.succ_ne_zero i), add_zero,
        Finsupp.comapDomain_apply]

/-- Recording the multiplicities of a multiset as a finitely supported function identifies
multisets of size `d` with finsupps of total degree `d`. -/
private noncomputable def e2 (r d : ℕ) :
    {T : Fin (r+1) →₀ ℕ // T.sum (fun _ k => k) = d} ≃ Sym (Fin (r+1)) d where
  toFun T := ⟨Finsupp.toMultiset T.1, by
    rw [Finsupp.card_toMultiset, ← sum_eq_sum_id T.1]
    exact T.2⟩
  invFun s := ⟨Multiset.toFinsupp (s : Multiset (Fin (r+1))), by
    rw [sum_eq_sum_id, Multiset.toFinsupp_sum_eq]; exact s.2⟩
  left_inv T := by
    apply Subtype.ext
    exact Finsupp.toMultiset_toFinsupp T.1
  right_inv s := by
    apply Subtype.ext
    exact Multiset.toFinsupp_toMultiset (s : Multiset (Fin (r+1)))

theorem card_monomials_le (r d : ℕ) :
    Nat.card {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d} ≤ (d + r).choose r := by
  have h1 : Nat.card {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d}
      = Nat.card {T : Fin (r+1) →₀ ℕ // T.sum (fun _ k => k) = d} :=
    Nat.card_congr (e1 r d)
  have h2 : Nat.card {T : Fin (r+1) →₀ ℕ // T.sum (fun _ k => k) = d}
      = Nat.card (Sym (Fin (r+1)) d) := Nat.card_congr (e2 r d)
  rw [h1, h2, Sym.natCard_sym_eq_choose, Nat.card_fin]
  have hsub : r + 1 + d - 1 = r + d := by omega
  rw [hsub, Nat.choose_symm_of_eq_add (show r + d = d + r by omega)]
  exact le_of_eq (by rw [Nat.add_comm])

end Commons.Algebra.MvPolynomial