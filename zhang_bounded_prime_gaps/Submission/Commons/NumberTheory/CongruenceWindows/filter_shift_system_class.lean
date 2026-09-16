import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Submission.Commons.NumberTheory.CongruenceWindows.exists_residue_class_prod
import Submission.Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue

namespace Commons.NumberTheory.CongruenceWindows

open scoped BigOperators

/-- The property `m ∣ n + H` for a nonzero modulus `m` is the condition that `n`
lies in the single residue class `(m - H % m) % m` modulo `m`. -/
private lemma dvd_add_iff_mod_eq {m H n : ℕ} (hm : m ≠ 0) :
    m ∣ n + H ↔ n % m = (m - H % m) % m := by
  rw [Nat.dvd_iff_mod_eq_zero]
  exact add_mod_eq_zero_iff_neg_residue (Nat.pos_of_ne_zero hm)

/-- **CRT collapse of a shifted congruence system to one residue class.**  Let
`W, m i (i : Fin k)` be pairwise coprime nonzero moduli, `b` a residue modulo `W`,
`H i, h` shifts.  Then the set of `n ∈ [N,2N]` with `n ≡ b (mod W)` and
`m i ∣ n + H i` for all `i` is exactly the set of `n ∈ [N,2N]` with
`(n + h) ≡ c (mod W · ∏ i, m i)` for a suitable `c`.

This is the CRT step of the sieve (Polymath8a (45)): the congruences
`n ≡ b (W)`, `n + H i ≡ 0 (m i)` collapse to one class modulo `W·∏ᵢ mᵢ`, and the
θ-weighted prime sum is then taken over that class (with `c` primitive whenever
`p ∣ W·∏ᵢ mᵢ ⟹ p ∤ h - H i`).  Follows from
`Commons.NumberTheory.CongruenceWindows.exists_residue_class_prod` applied to the
index type `Option (Fin k)` with `s none = W`, `s (some i) = m i`, `a none = b % W`,
`a (some i) = (m i - H i % m i) % m i`, together with
`m ∣ n + H ↔ n % m = (m - H % m) % m` and `Fintype.prod_option`. -/
theorem filter_shift_system_class {k N W b h : ℕ} (H : Fin k → ℕ) (m : Fin k → ℕ)
    (hW : W ≠ 0) (hm : ∀ i, m i ≠ 0)
    (hcop : ∀ i, (m i).Coprime W) (hcopm : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    ∃ c : ℕ, ((Finset.Icc N (2 * N)).filter
        (fun n => n % W = b % W ∧ ∀ i : Fin k, m i ∣ n + H i)) =
      (Finset.Icc N (2 * N)).filter
        (fun n => (n + h) % (W * ∏ i, m i) = c % (W * ∏ i, m i)) := by
  classical
  -- Combine the moduli `W` and `m i` into a single family indexed by `Option (Fin k)`.
  set s : Option (Fin k) → ℕ := fun o => match o with | none => W | some i => m i
  set a : Option (Fin k) → ℕ := fun o =>
    match o with | none => b | some i => (m i - H i % m i) % m i
  have hs : ∀ o : Option (Fin k), s o ≠ 0 := by
    intro o
    cases o with
    | none => simpa [s] using hW
    | some i => simpa [s] using hm i
  have hpair : Pairwise (fun x y : Option (Fin k) => (s x).Coprime (s y)) := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact absurd rfl hxy
      | some j => simpa [s] using (hcop j).symm
    | some i =>
      cases y with
      | none => simpa [s] using hcop i
      | some j =>
        have hij : i ≠ j := by intro h; exact hxy (by simp [h])
        simpa [s] using hcopm i j hij
  -- Chinese remainder theorem in residue-class form.
  obtain ⟨r, hr, hiff⟩ := exists_residue_class_prod s a hs hpair
  -- The product over `Option (Fin k)` is `W * ∏ i, m i`, by `Fintype.prod_option`.
  have hprod : ∏ o : Option (Fin k), s o = W * ∏ i, m i := by
    rw [Fintype.prod_option]
  have hrM : r < W * ∏ i, m i := by rwa [← hprod]
  -- Key equivalence: the system of congruences is a single residue class mod `W * ∏ i, m i`.
  have hkey : ∀ n : ℕ,
      (n % W = b % W ∧ ∀ i : Fin k, m i ∣ n + H i) ↔
        (n + h) % (W * ∏ i, m i) = ((r + h) % (W * ∏ i, m i)) % (W * ∏ i, m i) := by
    intro n
    have hL : (n % W = b % W ∧ ∀ i : Fin k, m i ∣ n + H i) ↔
        ∀ o : Option (Fin k), n % s o = a o % s o := by
      constructor
      · rintro ⟨hnW, hnH⟩ o
        cases o with
        | none => simpa [s, a] using hnW
        | some i =>
          have hd : m i ∣ n + H i := hnH i
          have hmod : n % m i = (m i - H i % m i) % m i :=
            (dvd_add_iff_mod_eq (hm i)).mp hd
          simpa [s, a, Nat.mod_mod] using hmod
      · intro h
        refine ⟨?_, ?_⟩
        · have := h none
          simpa [s, a] using this
        · intro i
          have hi := h (some i)
          simp only [s, a, Nat.mod_mod] at hi
          exact (dvd_add_iff_mod_eq (hm i)).mpr hi
    rw [hL, hiff n, hprod]
    have hrle : r % (W * ∏ i, m i) = r := Nat.mod_eq_of_lt hrM
    constructor
    · intro hn
      have hmod : (n + h) % (W * ∏ i, m i) = (r + h) % (W * ∏ i, m i) :=
        Nat.ModEq.add_right h (by rw [Nat.ModEq, hn, hrle])
      simpa [Nat.mod_mod] using hmod
    · intro hn
      have h1 : (n + h) % (W * ∏ i, m i) = (r + h) % (W * ∏ i, m i) := by
        simpa [Nat.mod_mod] using hn
      have hmod : n ≡ r [MOD W * ∏ i, m i] :=
        Nat.ModEq.add_right_cancel' h h1
      rw [Nat.ModEq] at hmod
      rw [hrle] at hmod
      exact hmod
  exact ⟨(r + h) % (W * ∏ i, m i), Finset.filter_congr (fun n _ => hkey n)⟩

end Commons.NumberTheory.CongruenceWindows