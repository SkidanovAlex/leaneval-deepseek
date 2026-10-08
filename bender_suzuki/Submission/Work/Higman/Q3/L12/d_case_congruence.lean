import Mathlib
import Submission.Work.Higman.Q3.L12.sparse_matching
import Submission.Work.Higman.Q3.L12.higman_D_enum

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

theorem multiset_nodup_pair {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    ({a, b} : Multiset α).Nodup := by
  rw [show ({a, b} : Multiset α) = a ::ₘ b ::ₘ 0 from rfl]
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · rw [Multiset.mem_cons]
    rintro (h' | h')
    · exact h h'
    · exact Multiset.notMem_zero a h'
  · exact Multiset.nodup_cons.mpr ⟨Multiset.notMem_zero b, Multiset.nodup_zero⟩

/-- `2 ^ a ≡ 2 ^ (a % n)` modulo `2 ^ n - 1`. -/
theorem pow_two_modEq {n a : ℕ} (hn : 0 < n) : (2 : ℕ) ^ a ≡ 2 ^ (a % n) [MOD 2 ^ n - 1] := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul]
  have hbase : (2 : ℕ) ^ n ≡ 1 [MOD (2 : ℕ) ^ n - 1] := by
    have hle : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    exact ((Nat.modEq_iff_dvd' hle).mpr (dvd_refl ((2 : ℕ) ^ n - 1))).symm
  have h := (hbase.pow (a / n)).mul (Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (2 ^ (a % n)))
  simpa [one_pow, mul_comm] using h

/-- **Higman (1963), the congruence of p. 92, `D` case** (used in the `D(n,θ,ε)` case of
Lemma 12).

If `r, s ∈ (0, n)` with `r + s` and `r - s` non-zero mod `n`, and `i, j ∈ [0, n)` satisfy

`2 ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r) ≡ (1 + 2 ^ r) * (1 + 2 ^ s)  (mod 2 ^ n - 1)`

then, up to interchanging `(r, s, i, j)` with `(s, r, j, i)`,
`5 * r ≡ 0`, `s ≡ 2 * r`, `i ≡ 3 * r`, `j ≡ r  (mod n)` — which is exactly Higman's
"the second gives `5r = 0`, `s = 2r`, `i = 3r`, `j = r`" (the first of his two alternatives is
the interchange, i.e. `X ↔ Y`).

This is the arithmetic heart of the last case of Lemma 12 (`X`, `Y` non-isomorphic, non-abelian).
Exhaustively verified for `n ≤ 40`: solutions exist exactly when `5 ∣ n`, and then they are the
claimed ones.  Proof idea: `2 ^ k` has multiplicative order `n` modulo `2 ^ n - 1`, so writing
`u = 2 ^ r`, `v = 2 ^ s`, the equation is a relation among `1, u, v, uv, u ^ 2 v, u v ^ 2` from
which the exponents must match (Higman's "the exponents on the left must be equal to them, in some
order"), leaving only `v = u ^ 2`, `2 ^ i = u ^ 3`, `2 ^ j = u`, i.e. `u ^ 5 = 1`. -/
theorem d_case_congruence {n r s i j : ℕ} (hn : 0 < n)
    (hr : r < n) (hs : s < n) (hi : i < n) (hj : j < n)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : (r + s) % n ≠ 0) (hrms : (r + n - s) % n ≠ 0)
    (h : 2 ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r) ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
      [MOD 2 ^ n - 1]) :
    (5 * r ≡ 0 [MOD n] ∧ s ≡ 2 * r [MOD n] ∧ i ≡ 3 * r [MOD n] ∧ j ≡ r [MOD n]) ∨
    (5 * s ≡ 0 [MOD n] ∧ r ≡ 2 * s [MOD n] ∧ j ≡ 3 * s [MOD n] ∧ i ≡ s [MOD n]) := by
  -- distinctness of `i` from `(i+s) % n` and of `j` from `(j+r) % n`
  have hσ : (i + s) % n ≠ i := by
    intro hh
    have hmod : (i + s) % n = i % n := by rw [hh, Nat.mod_eq_of_lt hi]
    have hme : i + s ≡ i [MOD n] := hmod
    have hdvd : n ∣ s := by
      have h1 : n ∣ (i + s) - i := (Nat.modEq_iff_dvd' (Nat.le_add_right i s)).mp hme.symm
      rwa [Nat.add_sub_cancel_left] at h1
    exact hs0 (Nat.eq_zero_of_dvd_of_lt hdvd hs)
  have hτ : (j + r) % n ≠ j := by
    intro hh
    have hmod : (j + r) % n = j % n := by rw [hh, Nat.mod_eq_of_lt hj]
    have hme : j + r ≡ j [MOD n] := hmod
    have hdvd : n ∣ r := by
      have h1 : n ∣ (j + r) - j := (Nat.modEq_iff_dvd' (Nat.le_add_right j r)).mp hme.symm
      rwa [Nat.add_sub_cancel_left] at h1
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)
  -- distinctness of the right-hand exponents
  have hrs' : r ≠ s := by
    intro hh
    exact hrms (by rw [hh, Nat.add_sub_cancel_left, Nat.mod_self])
  have hrρ : r ≠ (r + s) % n := by
    intro hh
    have hmod : (r + s) % n = r % n := by rw [← hh, Nat.mod_eq_of_lt hr]
    have hme : r + s ≡ r [MOD n] := hmod
    have hdvd : n ∣ s := by
      have h1 : n ∣ (r + s) - r := (Nat.modEq_iff_dvd' (Nat.le_add_right r s)).mp hme.symm
      rwa [Nat.add_sub_cancel_left] at h1
    exact hs0 (Nat.eq_zero_of_dvd_of_lt hdvd hs)
  have hsρ : s ≠ (r + s) % n := by
    intro hh
    have hmod : (r + s) % n = s % n := by rw [← hh, Nat.mod_eq_of_lt hs]
    have hme : r + s ≡ s [MOD n] := hmod
    have hdvd : n ∣ r := by
      have h1 : n ∣ (r + s) - s := (Nat.modEq_iff_dvd' (Nat.le_add_left s r)).mp hme.symm
      rwa [Nat.add_sub_cancel] at h1
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd hr)
  -- the reduced congruence
  have hL : 2 ^ i * (1 + 2 ^ s) ≡ 2 ^ i + 2 ^ ((i + s) % n) [MOD (2 : ℕ) ^ n - 1] := by
    have he : 2 ^ i * (1 + 2 ^ s) = 2 ^ i + 2 ^ (i + s) := by
      rw [mul_add, mul_one, ← pow_add]
    rw [he]
    exact (Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (2 ^ i)).add (pow_two_modEq hn)
  have hR : 2 ^ j * (1 + 2 ^ r) ≡ 2 ^ j + 2 ^ ((j + r) % n) [MOD (2 : ℕ) ^ n - 1] := by
    have he : 2 ^ j * (1 + 2 ^ r) = 2 ^ j + 2 ^ (j + r) := by
      rw [mul_add, mul_one, ← pow_add]
    rw [he]
    exact (Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (2 ^ j)).add (pow_two_modEq hn)
  have hQ : (1 + 2 ^ r) * (1 + 2 ^ s) ≡ 1 + 2 ^ r + 2 ^ s + 2 ^ ((r + s) % n)
      [MOD (2 : ℕ) ^ n - 1] := by
    have he : (1 + 2 ^ r) * (1 + 2 ^ s) = 1 + 2 ^ r + 2 ^ s + 2 ^ (r + s) := by
      rw [mul_add, mul_one, add_mul, one_mul, ← pow_add]
      ring
    rw [he]
    exact ((Nat.ModEq.refl (n := (2 : ℕ) ^ n - 1) (1 + 2 ^ r + 2 ^ s)).add
      (pow_two_modEq hn))
  have hmain : 2 ^ i + 2 ^ ((i + s) % n) + 2 ^ j + 2 ^ ((j + r) % n)
      ≡ 1 + 2 ^ r + 2 ^ s + 2 ^ ((r + s) % n) [MOD (2 : ℕ) ^ n - 1] := by
    have h' : 2 ^ i + 2 ^ ((i + s) % n) + (2 ^ j + 2 ^ ((j + r) % n))
        ≡ 1 + 2 ^ r + 2 ^ s + 2 ^ ((r + s) % n) [MOD (2 : ℕ) ^ n - 1] :=
      (hL.add hR).symm.trans (h.trans hQ)
    simpa [add_assoc] using h'
  -- rewrite as sums over the multisets of exponents
  have hA : ((({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ).map (fun a => 2 ^ a)).sum)
      = 2 ^ i + 2 ^ ((i + s) % n) + 2 ^ j + 2 ^ ((j + r) % n) := by
    rw [show ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)
        = i ::ₘ (i + s) % n ::ₘ j ::ₘ (j + r) % n ::ₘ 0 from rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_zero, Multiset.sum_zero,
      add_zero]
    ring
  have hB : ((({0, r, s, (r + s) % n} : Multiset ℕ).map (fun b => 2 ^ b)).sum)
      = 1 + 2 ^ r + 2 ^ s + 2 ^ ((r + s) % n) := by
    rw [show ({0, r, s, (r + s) % n} : Multiset ℕ)
        = 0 ::ₘ r ::ₘ s ::ₘ (r + s) % n ::ₘ 0 from rfl]
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_zero, Multiset.sum_zero,
      add_zero, pow_zero]
    ring
  have hmatch : ((({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ).map (fun a => 2 ^ a)).sum)
      ≡ ((({0, r, s, (r + s) % n} : Multiset ℕ).map (fun b => 2 ^ b)).sum)
        [MOD (2 : ℕ) ^ n - 1] := by
    rw [hA, hB]; exact hmain
  -- the counting hypotheses
  have hcarA : (({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)).card = 4 := by simp
  have hcarB : (({0, r, s, (r + s) % n} : Multiset ℕ)).card = 4 := by simp
  have hcntA : ∀ t, (({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)).count t ≤ 2 := by
    intro t
    have hsplit : ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)
        = ({i, (i + s) % n} : Multiset ℕ) + ({j, (j + r) % n} : Multiset ℕ) := rfl
    rw [hsplit, Multiset.count_add]
    have hn1 : ({i, (i + s) % n} : Multiset ℕ).Nodup := multiset_nodup_pair hσ.symm
    have hn2 : ({j, (j + r) % n} : Multiset ℕ).Nodup := multiset_nodup_pair hτ.symm
    have h1 := Multiset.nodup_iff_count_le_one.mp hn1 t
    have h2 := Multiset.nodup_iff_count_le_one.mp hn2 t
    omega
  have hcntB : ∀ t, (({0, r, s, (r + s) % n} : Multiset ℕ)).count t ≤ 1 := by
    have hnod : ({0, r, s, (r + s) % n} : Multiset ℕ).Nodup :=
      nodup_four_of hr0.symm hs0.symm hrs.symm hrs' hrρ hsρ
    exact fun t => Multiset.nodup_iff_count_le_one.mp hnod t
  have hboundA : ∀ a ∈ ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ), a < n := by
    intro a ha
    rw [show ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ)
        = i ::ₘ (i + s) % n ::ₘ j ::ₘ (j + r) % n ::ₘ 0 from rfl] at ha
    rw [Multiset.mem_cons] at ha
    rcases ha with h' | ha
    · rw [h']; exact hi
    rw [Multiset.mem_cons] at ha
    rcases ha with h' | ha
    · rw [h']; exact Nat.mod_lt _ hn
    rw [Multiset.mem_cons] at ha
    rcases ha with h' | ha
    · rw [h']; exact hj
    rw [Multiset.mem_cons] at ha
    rcases ha with h' | ha
    · rw [h']; exact Nat.mod_lt _ hn
    · exact absurd ha (Multiset.notMem_zero a)
  have hboundB : ∀ b ∈ ({0, r, s, (r + s) % n} : Multiset ℕ), b < n := by
    intro b hb
    rw [show ({0, r, s, (r + s) % n} : Multiset ℕ)
        = 0 ::ₘ r ::ₘ s ::ₘ (r + s) % n ::ₘ 0 from rfl] at hb
    rw [Multiset.mem_cons] at hb
    rcases hb with h' | hb
    · rw [h']; exact hn
    rw [Multiset.mem_cons] at hb
    rcases hb with h' | hb
    · rw [h']; exact hr
    rw [Multiset.mem_cons] at hb
    rcases hb with h' | hb
    · rw [h']; exact hs
    rw [Multiset.mem_cons] at hb
    rcases hb with h' | hb
    · rw [h']; exact Nat.mod_lt _ hn
    · exact absurd hb (Multiset.notMem_zero b)
  have hAB : ({i, (i + s) % n, j, (j + r) % n} : Multiset ℕ) = {0, r, s, (r + s) % n} :=
    sparse_matching hn hboundA hboundB hcarA hcarB hcntA hcntB hmatch
  exact higman_D_enum hn hr hs hi hj hr0 hs0 hrs hrms hAB

end Work.Higman.Q3.L12
