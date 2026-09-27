import Mathlib
import Submission.Work.KT.Psi.OrbitBasic

/-!
# `Work.KT.Psi.OrbitFi` — the conjugates `g^i F g^{k-i}` of `F`, and `E * F`

Auxiliary definitions and lemmas for `Work.KT.Psi.OrbitCrux`.

With `g^k = 1`, the element `Fi g F k i = g^i · F · g^{k-i}` is the `g`-conjugate
`g^i F g^{-i}` of `F`.  The orbit sum is `orbSum g F k = Σ_{i<k} Fi g F k i`, and the key
manipulation is `g^j * F = Fi g F k j * g^j` (for `j ≤ k`), which lets one move the conjugates
to the left of the powers of `g`.
-/

namespace Work.KT.Psi

open Finset

noncomputable section

variable {M : Type} [Ring M] [Algebra ℂ M]

/-- The `i`-th conjugate `g^i · F · g^{k-i}` of `F`. -/
def Fi (g F : M) (k i : ℕ) : M := g ^ i * F * g ^ (k - i)

lemma orbSum_eq_sum_Fi (g F : M) (k : ℕ) :
    orbSum g F k = ∑ i ∈ Finset.range k, Fi g F k i := rfl

lemma Fi_zero {g F : M} {k : ℕ} (hg : g ^ k = 1) : Fi g F k 0 = F := by
  simp [Fi, hg]

lemma Fi_self_mul {g F : M} {k i : ℕ} (hi : i ≤ k) (hF : F * F = F) (hg : g ^ k = 1) :
    Fi g F k i * Fi g F k i = Fi g F k i := by
  have h1 : g ^ (k - i) * g ^ i = 1 := by rw [← pow_add, Nat.sub_add_cancel hi, hg]
  have step : (g ^ i * F * g ^ (k - i)) * (g ^ i * F * g ^ (k - i))
      = g ^ i * F * (g ^ (k - i) * g ^ i) * F * g ^ (k - i) := by noncomm_ring
  rw [Fi]
  rw [step, h1, mul_one, mul_assoc (g ^ i) F F, hF]

lemma Fi_mul_orth {g F : M} {k i j : ℕ} (hi : i < k) (hj : j < k) (hij : i ≠ j)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0) :
    Fi g F k i * Fi g F k j = 0 := by
  simpa only [Fi] using horth i j hi hj hij

lemma g_pow_mul_F {g F : M} {k j : ℕ} (hj : j ≤ k) (hg : g ^ k = 1) :
    g ^ j * F = Fi g F k j * g ^ j := by
  have h1 : g ^ (k - j) * g ^ j = 1 := by rw [← pow_add, Nat.sub_add_cancel hj, hg]
  rw [Fi, mul_assoc (g ^ j * F) (g ^ (k - j)) (g ^ j), h1, mul_one]

/-- Expansion of `orbitSpec lam g k * F` in terms of the conjugates `Fi g F k j`. -/
lemma orbitSpec_mul_eq_sum (k : ℕ) (F g : M) (hg : g ^ k = 1) (lam : ℂ) :
    orbitSpec lam g k * F =
      ((k : ℂ)⁻¹) • ∑ j ∈ Finset.range k, (lam⁻¹) ^ j • (Fi g F k j * g ^ j) := by
  have h : ∀ j ∈ Finset.range k,
      qg lam g ^ j * F = (lam⁻¹) ^ j • (Fi g F k j * g ^ j) := by
    intro j hj
    rw [qg_pow, smul_mul_assoc, g_pow_mul_F (Finset.mem_range.mp hj).le hg]
  rw [orbitSpec, smul_mul_assoc, geoSum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl h

end

end Work.KT.Psi
