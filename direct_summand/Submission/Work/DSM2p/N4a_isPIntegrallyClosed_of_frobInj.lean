import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

/-- **Descent step.**  If `ϖ₁` is a unit of `L` lying in the subring `U`, and `hinj` holds, then
for every `z : L` with `z ^ p ∈ U` the *integrality order* of `z` (the least `k` with
`ϖ₁ ^ k * z ∈ U`, which exists by `hgen`) can be driven down to `0`.  This is the strong
induction performed below. -/
theorem N4a_descent {L : Type*} [CommRing L] (p : ℕ) (U : Subring L)
    (ϖ₁ : L) (hϖU : ϖ₁ ∈ U) (hϖL : IsUnit ϖ₁)
    (hinj : ∀ y ∈ U, (∃ c ∈ U, y ^ p = ϖ₁ ^ p * c) → ∃ c ∈ U, y = ϖ₁ * c) :
    ∀ k : ℕ, ∀ z : L, z ^ p ∈ U → ϖ₁ ^ k * z ∈ U → z ∈ U := by
  intro k
  induction k with
  | zero =>
    intro z _ hz
    simpa using hz
  | succ k ih =>
    intro z hzp hz
    -- `w = ϖ₁ ^ k * z`, so that `ϖ₁ ^ (k+1) * z = ϖ₁ * w`
    have hwU : (ϖ₁ ^ k * z) ^ p ∈ U := by
      have h : (ϖ₁ ^ k * z) ^ p = ϖ₁ ^ (k * p) * z ^ p := by
        rw [mul_pow, ← pow_mul]
      rw [h]
      exact U.mul_mem (U.pow_mem hϖU (k * p)) hzp
    have hyw : ϖ₁ ^ (k + 1) * z = ϖ₁ * (ϖ₁ ^ k * z) := by
      rw [pow_succ]
      ring
    have hyU : ϖ₁ * (ϖ₁ ^ k * z) ∈ U := by
      rw [← hyw]
      exact hz
    have hpow : (ϖ₁ * (ϖ₁ ^ k * z)) ^ p = ϖ₁ ^ p * (ϖ₁ ^ k * z) ^ p :=
      mul_pow _ _ _
    obtain ⟨c, hcU, hceq⟩ :=
      hinj (ϖ₁ * (ϖ₁ ^ k * z)) hyU ⟨(ϖ₁ ^ k * z) ^ p, hwU, hpow⟩
    have hweq : ϖ₁ ^ k * z = c := hϖL.mul_left_cancel hceq
    exact ih z hzp (by rw [hweq]; exact hcU)

theorem N4a_isPIntegrallyClosed_of_frobInj {L : Type*} [CommRing L] (p : ℕ) (U : Subring L)
    (ϖ₁ : L) (hϖU : ϖ₁ ∈ U) (hϖL : IsUnit ϖ₁) (hgen : ∀ z : L, ∃ k : ℕ, ϖ₁ ^ k * z ∈ U)
    (hinj : ∀ y ∈ U, (∃ c ∈ U, y ^ p = ϖ₁ ^ p * c) → ∃ c ∈ U, y = ϖ₁ * c) :
    IsPIntegrallyClosedIn p U := by
  intro x hx
  obtain ⟨n, hn⟩ := hgen x
  exact N4a_descent p U ϖ₁ hϖU hϖL hinj n x hx hn

end Work.DSM2p
