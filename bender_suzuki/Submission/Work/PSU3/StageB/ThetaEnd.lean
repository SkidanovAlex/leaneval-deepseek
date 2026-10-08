import Mathlib
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.pow_poly_forces_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

open Work.PSU3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- In a field of characteristic two, squaring is injective. -/
lemma sq_eq_sq_char2 {F : Type*} [Field F] [CharP F 2] {x y : F} (h : x ^ 2 = y ^ 2) :
    x = y := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- **`Work.PSU3.StageB.ThetaEnd`** (Peterfalvi II Ch. VII §3): from the functional equation
`(c + A)^μ = α² + A^μ` for `2ⁿ - 2` fixed values of `A` (where `c = κ ζ + (κ ζ)⁻¹` and
`α` is the `zc`-coordinate of `ω²`), the exponent `μ` of the power map `nm` is a power of two
`2^s = μ`, `α = c^(2^(s-1))`, and hence `nm (a) = a^(2^(i+1))` for `σE`-fixed `a` while
`ω² = zc (c^(2^i))`. -/
theorem ThetaEnd {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G} (hω : Work.PSU3.OmegaHyp fr ω) {μ : ℕ}
    (hμ : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a → fr.nm a = a ^ μ)
    (hμpos : 1 ≤ μ) (hμle : μ ≤ 2 ^ n - 2)
    (hcard : Nat.card {a : (Work.PSU3.E n)ˣ // σE (a : Work.PSU3.E n) = a} = 2 ^ n - 1)
    (S : Finset (Work.PSU3.E n)) (hSfix : ∀ A ∈ S, σE A = A) (hScard : 2 ^ n - 2 ≤ S.card)
    (hFE : ∀ A ∈ S, (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) +
        (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ + A) ^ μ
      = (Work.PSU3.StageB.alpha fr hω) ^ 2 + A ^ μ) :
    ∃ i : ℕ,
      (∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a → fr.nm a = a ^ (2 ^ (i + 1))) ∧
      ω ^ 2 = fr.zc ((((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) +
        (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹) ^ (2 ^ i)) := by
  classical
  -- Abbreviate `c = κ ζ + (κ ζ)⁻¹` in `E n`.
  set C : Work.PSU3.E n := ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) +
    (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ with hC
  -- `c` is fixed by `σE` (since `ζ_norm` says `σ(κζ) = (κζ)⁻¹`).
  have hCfix : σE C = C := by
    rw [hC, map_add, map_inv₀]
    rw [eq_inv_of_mul_eq_one_right fr.ζ_norm, inv_inv, add_comm]
  -- consequently `c ^ (2ⁿ) = c`.
  have hCpow : C ^ (2 ^ n) = C := by
    have h := hCfix
    rw [show σE C = C ^ (2 ^ n) from rfl] at h
    exact h
  -- `c ≠ 0`: otherwise `κ ζ = (κ ζ)⁻¹`, so `(κ ζ)² = 1`, forcing `κ ζ = 1` in char 2.
  have hCne : C ≠ 0 := by
    rw [hC]
    intro h
    have hκζ_ne : (fr.κ fr.ζ : (Work.PSU3.E n)ˣ) ≠ 1 := by
      intro h1
      exact fr.ζ_ne_one (fr.κ_injective (by rw [h1, map_one]))
    have ha_ne : (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ≠ 0 := Units.ne_zero _
    have h1 : (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) =
        (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ := by
      have hh := add_eq_zero_iff_eq_neg.mp h
      rwa [CharTwo.neg_eq] at hh
    have h2 : (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) *
        (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) = 1 := by
      have hh : (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) *
            (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))
          = (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ *
            (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) :=
        congrArg (fun x => x * (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))) h1
      rw [hh, inv_mul_cancel₀ ha_ne]
    have h3 : (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) = 1 :=
      sq_eq_sq_char2 (by simpa [pow_two] using h2)
    exact hκζ_ne (Units.ext h3)
  -- The functional equation, phrased with `C`.
  have hFE' : ∀ A ∈ S, (C + A) ^ μ = (alpha fr hω) ^ 2 + A ^ μ := by
    intro A hA
    rw [hC]
    exact hFE A hA
  -- Root counting forces `μ = 2^s` and `α² = c^μ`.
  obtain ⟨s, hs, hαsq⟩ := pow_poly_forces_pow_two (F := Work.PSU3.E n) (c := C)
    (α := (alpha fr hω) ^ 2) hCne hμpos S (hμle.trans hScard) hFE'
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · -- Degenerate case `s = 0`, i.e. `μ = 1`; take `i = n - 1`.
    have hmu1 : μ = 1 := by rw [hs, hs0]; norm_num
    have hn0 : n ≠ 0 := by
      intro hn
      rw [hn] at hμle
      norm_num at hμle
      omega
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hα : alpha fr hω = C ^ (2 ^ (n - 1)) := by
      have h1 : (alpha fr hω) ^ 2 = C := by rw [hαsq, hs, hs0, pow_zero, pow_one]
      have h2 : (C ^ (2 ^ (n - 1))) ^ 2 = C := by
        have hstep : 2 ^ (n - 1) * 2 = 2 ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn1]
        rw [← pow_mul, hstep, hCpow]
      exact sq_eq_sq_char2 (h1.trans h2.symm)
    refine ⟨n - 1, ?_, ?_⟩
    · intro a ha
      rw [hμ a ha, hmu1, pow_one, Nat.sub_add_cancel hn1]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      have hfix : (a : Work.PSU3.E n) ^ (2 ^ n) = (a : Work.PSU3.E n) := by
        have h := ha
        rw [show σE (a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ (2 ^ n) from rfl] at h
        exact h
      exact hfix.symm
    · rw [pow_two, ← alpha_spec fr hω, hα]
  · -- Case `s ≥ 1`; take `i = s - 1`.
    have hspos' : 1 ≤ s := hspos
    have hα : alpha fr hω = C ^ (2 ^ (s - 1)) := by
      have h1 : (alpha fr hω) ^ 2 = C ^ (2 ^ s) := by rw [hαsq, hs]
      have h2 : (C ^ (2 ^ (s - 1))) ^ 2 = C ^ (2 ^ s) := by
        have hstep : 2 ^ (s - 1) * 2 = 2 ^ s := by
          rw [← pow_succ, Nat.sub_add_cancel hspos']
        rw [← pow_mul, hstep]
      exact sq_eq_sq_char2 (h1.trans h2.symm)
    refine ⟨s - 1, ?_, ?_⟩
    · intro a ha
      rw [hμ a ha, hs, Nat.sub_add_cancel hspos']
    · rw [pow_two, ← alpha_spec fr hω, hα]

end Work.PSU3.StageB
