import Mathlib
import Submission.Work.FIArea2.sq_eq_zmod_two_pow
import Submission.Work.FIArea2.card_sq_eq_sq_two_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

/-- **Reduction of the `a`-twisted count to the `a = 1` count.**  If `a ≡ 1 (mod 8)` then
`a` is a unit of `ZMod N` (`N = 2 ^ ν`) and admits a square root `b`; the substitution
`x ↦ b x` maps the solutions of `a x² = y²` bijectively onto those of `x² = y²`. -/
lemma card_mul_sq_eq_card_sq {N : ℕ} [NeZero N] (a : ℕ) (hUa : IsUnit ((a : ZMod N)))
    (hb : ∃ b : ZMod N, b ^ 2 = (a : ZMod N)) :
    ((Finset.univ : Finset (ZMod N × ZMod N)).filter
        (fun p => (a : ZMod N) * p.1 ^ 2 = p.2 ^ 2)).card
      = ((Finset.univ : Finset (ZMod N × ZMod N)).filter
        (fun p => p.1 ^ 2 = p.2 ^ 2)).card := by
  obtain ⟨b0, hb0⟩ := hb
  have hUb0 : IsUnit b0 := by
    have : IsUnit (b0 * b0) := by rw [← pow_two, hb0]; exact hUa
    exact (IsUnit.mul_iff.mp this).1
  obtain ⟨u, hu⟩ : ∃ u : (ZMod N)ˣ, (↑u : ZMod N) = b0 :=
    ⟨hUb0.unit, IsUnit.unit_spec hUb0⟩
  have ha' : (↑u : ZMod N) ^ 2 = (a : ZMod N) := by rw [hu, hb0]
  classical
  have hkey : (a : ZMod N) * (↑(u⁻¹) : ZMod N) ^ 2 = 1 := by
    have h1 : (↑u : ZMod N) * ↑(u⁻¹) = 1 := Units.mul_inv u
    have h2 : ((↑u : ZMod N) * ↑(u⁻¹)) ^ 2 = 1 := by rw [h1]; ring
    rw [mul_pow] at h2
    rw [← ha']; exact h2
  refine Finset.card_bij' (fun p _ => ((↑u : ZMod N) * p.1, p.2))
    (fun q _ => ((↑(u⁻¹) : ZMod N) * q.1, q.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [mul_pow, ha', hp]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [mul_pow, ← mul_assoc, hkey, one_mul, hq]
  · intro p hp
    obtain ⟨x, y⟩ := p
    simp only
    rw [← mul_assoc, Units.inv_mul, one_mul]
  · intro q hq
    obtain ⟨x, y⟩ := q
    simp only
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- **(*FI* (8.11)): the 2-adic local factor of Lemma 8.4.**  For `ν ≥ 1` and `a ≡ 1 (mod 8)`,
`N(a;2^ν) = #{(γ₁,γ₂) ∈ (ℤ/2^ν)² : aγ₁² ≡ γ₂²} = ν·2^ν`.  Together with
`card_solutions_eight_thirteen` (Corollary 8.3) this is the whole arithmetic input of (8.14),
`G₀ = ν·Σ_{d odd|Δ}(φ(d)/d)(z₂/z₁/d)`; the hypothesis `a ≡ 1 (mod 8)` is exactly what (5.7)
`z₁ ≡ z₂ (mod 8)` supplies for `a = z₂/z₁`, and `ν = ord₂(Δ) ≥ 3` then follows.  (Verified
numerically for `ν ≤ 12` and all `a ≡ 1 (mod 8)`.) -/
theorem card_solutions_two_power (ν a : ℕ) (hν : 1 ≤ ν) (ha : a % 8 = 1) :
    (((Finset.univ : Finset (ZMod (2 ^ ν) × ZMod (2 ^ ν))).filter
        (fun p => (a : ZMod (2 ^ ν)) * p.1 ^ 2 = p.2 ^ 2)).card : ℝ)
      = (ν : ℝ) * (2 : ℝ) ^ ν := by
  have hUa : IsUnit ((a : ZMod (2 ^ ν))) := by
    rw [ZMod.isUnit_iff_coprime]
    have hodd : Odd a := by rw [Nat.odd_iff]; omega
    exact (Nat.coprime_two_right.mpr hodd).pow_right ν
  have hred := card_mul_sq_eq_card_sq a hUa (sq_eq_zmod_two_pow ν a hν ha)
  rw [hred, card_sq_eq_sq_two_pow ν hν]
  push_cast
  ring

end Work.FIArea2
