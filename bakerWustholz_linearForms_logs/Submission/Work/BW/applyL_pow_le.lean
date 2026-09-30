import Mathlib
import Submission.Work.BW.wuestholzDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BW

/-- One derivation lowers the power of an ideal by one: `Λ (𝔓^(m+1)) ⊆ 𝔓^m`.
Each Leibniz term in an `(m+1)`-fold product leaves `m` factors inside `𝔓`. -/
private lemma leibniz_pow {R : Type*} [CommRing R] (Λ : R → R)
    (hadd : ∀ x y, Λ (x + y) = Λ x + Λ y) (hleib : ∀ x y, Λ (x * y) = Λ x * y + x * Λ y)
    (I : Ideal R) : ∀ m x, x ∈ I ^ (m + 1) → Λ x ∈ I ^ m := by
  intro m
  induction m with
  | zero =>
      intro x hx
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ m ih =>
    intro x hx
    show Λ x ∈ I ^ (m + 1)
    have hx' : x ∈ I ^ (m + 1) * I := by
      have h : I ^ (m + 1) * I = I ^ (m + 1 + 1) := (pow_succ I (m + 1)).symm
      rw [h]
      exact hx
    exact Submodule.mul_induction_on (R := R) (A := R) (M := I ^ (m + 1)) (N := I)
      (C := fun x => Λ x ∈ I ^ (m + 1)) hx'
      (fun a ha b hb => by
        rw [hleib]
        apply Ideal.add_mem
        · rw [pow_succ]
          exact Submodule.mul_mem_mul (ih a ha) hb
        · exact Ideal.mul_mem_right (Λ b) (I ^ (m + 1)) ha)
      (fun x y hx hy => by rw [hadd]; exact Ideal.add_mem _ hx hy)

/-- Iterating a derivation `a` times lowers the power by `a` (with truncated subtraction,
so the statement is vacuous once the power is exhausted). -/
private lemma iterate_mem {R : Type*} [CommRing R] (Λ : R → R)
    (hadd : ∀ x y, Λ (x + y) = Λ x + Λ y) (hleib : ∀ x y, Λ (x * y) = Λ x * y + x * Λ y)
    (I : Ideal R) : ∀ (a m : ℕ) (x : R), x ∈ I ^ m → (Λ^[a]) x ∈ I ^ (m - a) := by
  intro a
  induction a with
  | zero => intro m x hx; simpa using hx
  | succ a ih =>
    intro m x hx
    rw [Function.iterate_succ_apply]
    cases m with
    | zero =>
        rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ m' =>
        have h1 : (Λ^[a]) (Λ x) ∈ I ^ (m' - a) :=
          ih m' (Λ x) (leibniz_pow Λ hadd hleib I m' x hx)
        have he : Nat.succ m' - Nat.succ a = m' - a := by omega
        rwa [he]

/-- A left fold of iterated derivations over a list of indices lowers the power of `I`
by the total weight `∑_{i ∈ s} α i`. -/
private lemma foldr_mem {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (I : Ideal R) (α : Fin ℓ → ℕ) :
    ∀ (s : List (Fin ℓ)) (m : ℕ) (x : R), x ∈ I ^ m →
      s.foldr (fun i q => (Λ i)^[α i] q) x ∈ I ^ (m - (s.map α).sum) := by
  intro s
  induction s with
  | nil => intro m x hx; simpa using hx
  | cons i t ih =>
      intro m x hx
      rw [List.foldr_cons, List.map_cons, List.sum_cons]
      have h1 : t.foldr (fun i q => (Λ i)^[α i] q) x ∈ I ^ (m - (t.map α).sum) := ih m x hx
      have h2 := iterate_mem (Λ i) (hadd i) (hleib i) I (α i) (m - (t.map α).sum)
        (t.foldr (fun i q => (Λ i)^[α i] q) x) h1
      have he : m - (α i + (t.map α).sum) = (m - (t.map α).sum) - α i := by omega
      rwa [he]

/-- The weight of `List.finRange ℓ` is the corresponding `Finset` sum. -/
private lemma finRange_sum (ℓ : ℕ) (α : Fin ℓ → ℕ) :
    ((List.finRange ℓ).map α).sum = ∑ i, α i := by
  have := List.sum_toFinset (f := α) (l := List.finRange ℓ) (List.nodup_finRange ℓ)
  rw [List.toFinset_finRange] at this
  exact this.symm

/-- A composition of `k = ∑ αᵢ` derivations maps the `m`-th power of an ideal into the
`(m-k)`-th power: each Leibniz term leaves an undifferentiated factor. -/
theorem applyL_pow_le {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (𝔓 : Ideal R) {m : ℕ} (α : Fin ℓ → ℕ) (hα : ∑ i, α i ≤ m) :
    ∀ x ∈ 𝔓 ^ m, applyL Λ α x ∈ 𝔓 ^ (m - ∑ i, α i) := by
  intro x hx
  have h := foldr_mem Λ hadd hleib 𝔓 α (List.finRange ℓ) m x hx
  have hsum : ((List.finRange ℓ).map α).sum = ∑ i, α i := finRange_sum ℓ α
  change (List.finRange ℓ).foldr (fun i q => (Λ i)^[α i] q) x ∈ 𝔓 ^ (m - ∑ i, α i)
  rw [hsum] at h
  exact h

end Work.BW
