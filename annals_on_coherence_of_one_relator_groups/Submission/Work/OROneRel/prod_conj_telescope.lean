import Mathlib

namespace Work.OROneRel

/-- Splitting the product over `Fin n` (for `1 ≤ n`) into the product over `Fin (n-1)` times the last
term. -/
private lemma ofFn_prod_eq_last {M : Type*} [Monoid M] (n : ℕ) (hn : 1 ≤ n) (f : Fin n → M) :
    (List.ofFn f).prod =
      (List.ofFn (fun i : Fin (n - 1) => f ⟨i.1, by omega⟩)).prod * f ⟨n - 1, by omega⟩ := by
  match n, hn with
  | 0, hn => omega
  | m + 1, _ =>
    rw [List.ofFn_succ', List.prod_concat]
    congr 1

/-- The left hand side of the telescoping identity, reindexed so that the dependence on the data is
only through `ℕ`-indexed functions `G`, `H`. -/
private def lhsN {M : Type*} [Group M] (τ : M) (n : ℕ) (G : ℕ → ℤ) (H : ℕ → M) : M :=
  (List.ofFn (fun i : Fin n => τ ^ (G i.1) * H i.1 * τ ^ (-(G i.1)))).prod

/-- The right hand side of the telescoping identity, reindexed so that the dependence on the data is
only through `ℕ`-indexed functions `G`, `H`. -/
private def rhsN {M : Type*} [Group M] (τ : M) (n : ℕ) (G : ℕ → ℤ) (H : ℕ → M) : M :=
  τ ^ (G 0) *
    (((List.ofFn (fun j : Fin (n - 1) => H j.1 * τ ^ (G (j.1 + 1) - G j.1))).prod * H (n - 1)) *
      τ ^ (-(G (n - 1))))

private lemma lhsN_succ {M : Type*} [Group M] (τ : M) (n : ℕ) (G : ℕ → ℤ) (H : ℕ → M) :
    lhsN τ (n + 1) G H = lhsN τ n G H * (τ ^ (G n) * H n * τ ^ (-(G n))) := by
  unfold lhsN
  rw [List.ofFn_succ', List.prod_concat]
  congr 1

private lemma rhsN_succ {M : Type*} [Group M] (τ : M) (n : ℕ) (hmn : 1 ≤ n)
    (G : ℕ → ℤ) (H : ℕ → M) :
    rhsN τ (n + 1) G H = rhsN τ n G H * (τ ^ (G n) * H n * τ ^ (-(G n))) := by
  change τ ^ (G 0) *
      (((List.ofFn (fun j : Fin n => H j.1 * τ ^ (G (j.1 + 1) - G j.1))).prod * H n) *
      τ ^ (-(G n))) = rhsN τ n G H * (τ ^ (G n) * H n * τ ^ (-(G n)))
  unfold rhsN
  rw [ofFn_prod_eq_last n hmn, Nat.sub_add_cancel hmn]
  group

private lemma mainN {M : Type*} [Group M] (τ : M) :
    ∀ n, 1 ≤ n → ∀ (G : ℕ → ℤ) (H : ℕ → M), lhsN τ n G H = rhsN τ n G H := by
  intro n hn
  refine Nat.le_induction
    (m := 1)
    (P := fun n _ => ∀ (G : ℕ → ℤ) (H : ℕ → M), lhsN τ n G H = rhsN τ n G H)
    ?base ?step n hn
  · intro G H
    simp only [lhsN, rhsN, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, one_mul, Fin.val_zero]
    group
  · intro n hmn ih G H
    rw [lhsN_succ, rhsN_succ (hmn := hmn), ih G H]

theorem prod_conj_telescope {M : Type*} [Group M] (τ : M) {n : ℕ} (hn : 1 ≤ n)
    (g : Fin n → ℤ) (h : Fin n → M) :
    (List.ofFn (fun i : Fin n => τ ^ (g i) * h i * τ ^ (-(g i)))).prod =
      τ ^ (g ⟨0, hn⟩) *
        (((List.ofFn (fun j : Fin (n - 1) =>
            h ⟨j.1, by omega⟩ * τ ^ (g ⟨j.1 + 1, by omega⟩ - g ⟨j.1, by omega⟩))).prod *
          h ⟨n - 1, by omega⟩) *
        τ ^ (-(g ⟨n - 1, by omega⟩))) := by
  let G : ℕ → ℤ := fun k => if hk : k < n then g ⟨k, hk⟩ else 0
  let H : ℕ → M := fun k => if hk : k < n then h ⟨k, hk⟩ else 1
  have hL : (List.ofFn (fun i : Fin n => τ ^ (g i) * h i * τ ^ (-(g i)))).prod
      = lhsN τ n G H := by
    unfold lhsN
    apply congrArg List.prod
    rw [List.ofFn_inj]
    funext i
    simp only [G, H, dif_pos i.2]
  have hQ : (List.ofFn (fun j : Fin (n - 1) =>
          h ⟨j.1, by omega⟩ * τ ^ (g ⟨j.1 + 1, by omega⟩ - g ⟨j.1, by omega⟩))).prod
        = (List.ofFn (fun j : Fin (n - 1) => H j.1 * τ ^ (G (j.1 + 1) - G j.1))).prod := by
    apply congrArg List.prod
    rw [List.ofFn_inj]
    funext j
    simp only [G, H, dif_pos (show j.1 < n by omega), dif_pos (show j.1 + 1 < n by omega)]
  have h0 : g ⟨0, hn⟩ = G 0 := by
    simp only [G, dif_pos (show (0 : ℕ) < n by omega)]
  have hh : h ⟨n - 1, by omega⟩ = H (n - 1) := by
    simp only [H, dif_pos (show n - 1 < n by omega)]
  have hg : g ⟨n - 1, by omega⟩ = G (n - 1) := by
    simp only [G, dif_pos (show n - 1 < n by omega)]
  have hR : τ ^ (g ⟨0, hn⟩) *
        (((List.ofFn (fun j : Fin (n - 1) =>
            h ⟨j.1, by omega⟩ * τ ^ (g ⟨j.1 + 1, by omega⟩ - g ⟨j.1, by omega⟩))).prod *
          h ⟨n - 1, by omega⟩) *
        τ ^ (-(g ⟨n - 1, by omega⟩))) = rhsN τ n G H := by
    rw [h0, hQ, hh, hg]
    unfold rhsN
    rfl
  rw [hL, hR]
  exact mainN τ n hn G H

end Work.OROneRel
