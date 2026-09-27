import Mathlib
import Submission.Work.Hopf.two_pow_dvd_of_psi_relation

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md (the lead's design for the odd case: Adams–Atiyah via K₀ of rings of continuous functions, ψ² and ψ³ from symmetric-power eigenspaces, Bott periodicity via Atiyah–Bott clutching). Shared definitions: Submission/Work/KT/Defs.lean (do NOT edit). CONVENTION: use [Ring A] plus an explicit commutativity hypothesis, never [CommRing A] on subalgebras (unification timeouts). Siblings run in parallel.

# Node `aa_algebra`

**Statement** (`aa_algebra.lean`, harness format; imports: `Submission.Work.Hopf.two_pow_dvd_of_psi_relation`; namespace `Work.KT`):

```lean
/-- The Adams–Atiyah computation, abstractly: commuting `ψ²`, `ψ³` acting on `G ⊇ ℤb` as
`ψ^k b = k^{2m} b` and on `G / ℤb ↪ A` as `k^m`, with `ψ² a ≡ h b (mod 2)` for odd `h`,
force `2^m ∣ 3^m - 1`. -/
theorem aa_algebra (G A : Type) [AddCommGroup G] [AddCommGroup A] (i : G →+ A)
    (ψ2 ψ3 : G →+ G) (a b : G) (m : ℕ) (hm : 1 ≤ m) (h : ℤ) (hh : Odd h)
    (hcomm : ∀ x, ψ2 (ψ3 x) = ψ3 (ψ2 x))
    (hA : ∀ z : A, 2 • z = 0 → z = 0)
    (hker : ∀ x, i x = 0 → ∃ k : ℤ, x = k • b)
    (hib : i b = 0)
    (hb : ∀ k : ℤ, k • b = 0 → k = 0)
    (hψb2 : ψ2 b = (2 ^ (2 * m) : ℤ) • b) (hψb3 : ψ3 b = (3 ^ (2 * m) : ℤ) • b)
    (hψa2 : i (ψ2 a) = (2 ^ m : ℤ) • i a) (hψa3 : i (ψ3 a) = (3 ^ m : ℤ) • i a)
    (hsq : ∃ y, ψ2 a - h • b = 2 • y) :
    (2 : ℤ) ^ m ∣ (3 : ℤ) ^ m - 1 := by
  -- (proof below)
```

**Size:** 0.2–0.4k lines. **Risk:** low. **Depends on (statements):** Work.Hopf.two_pow_dvd_of_psi_relation (proved). **Day 1:** yes.

## Route

1. From `hker` and `hψa*`: `ψ²a = 2^m a + μ₂ b` and `ψ³a = 3^m a + μ₃ b`.
2. Apply `ψ²ψ³ = ψ³ψ²` to `a`, with `hψb*`. This gives
   `(4^m−2^m)μ₃·b = (9^m−3^m)μ₂·b`; by `hb`, it is an identity of integers.
3. From `hsq`: `2^m a + (μ₂−h)b = 2y`. Apply `i` (`hib`, `hA`): `i y = 2^{m−1} i a`. So
   `y − 2^{m−1}a = ν b`, whence `μ₂ = h + 2ν` is odd.
4. Finish with `Work.Hopf.two_pow_dvd_of_psi_relation`.
-/

namespace Work.KT

/-- A single explicit step of the Adams–Atiyah computation: an additive endomorphism `f`
of an additive commutative group which acts on `a` by `f a = c • a + μ • b` and on `b` by
`f b = d • b` acts on `e • a + ν • b` by `f (e • a + ν • b) = (e * c) • a + (e * μ + ν * d) • b`. -/
lemma map_apply_add_smul (G : Type) [AddCommGroup G] (f : G →+ G) (a b : G)
    (e ν c μ d : ℤ) (hf : f a = c • a + μ • b) (hfb : f b = d • b) :
    f (e • a + ν • b) = (e * c) • a + (e * μ + ν * d) • b := by
  rw [map_add, map_zsmul, map_zsmul, hf, hfb, smul_add, smul_smul, smul_smul, smul_smul,
    add_assoc, ← add_smul]

/-- The Adams–Atiyah computation, abstractly: commuting `ψ²`, `ψ³` acting on `G ⊇ ℤb` as
`ψ^k b = k^{2m} b` and on `G / ℤb ↪ A` as `k^m`, with `ψ² a ≡ h b (mod 2)` for odd `h`,
force `2^m ∣ 3^m - 1`. -/
theorem aa_algebra (G A : Type) [AddCommGroup G] [AddCommGroup A] (i : G →+ A)
    (ψ2 ψ3 : G →+ G) (a b : G) (m : ℕ) (hm : 1 ≤ m) (h : ℤ) (hh : Odd h)
    (hcomm : ∀ x, ψ2 (ψ3 x) = ψ3 (ψ2 x))
    (hA : ∀ z : A, 2 • z = 0 → z = 0)
    (hker : ∀ x, i x = 0 → ∃ k : ℤ, x = k • b)
    (hib : i b = 0)
    (hb : ∀ k : ℤ, k • b = 0 → k = 0)
    (hψb2 : ψ2 b = (2 ^ (2 * m) : ℤ) • b) (hψb3 : ψ3 b = (3 ^ (2 * m) : ℤ) • b)
    (hψa2 : i (ψ2 a) = (2 ^ m : ℤ) • i a) (hψa3 : i (ψ3 a) = (3 ^ m : ℤ) • i a)
    (hsq : ∃ y, ψ2 a - h • b = 2 • y) :
    (2 : ℤ) ^ m ∣ (3 : ℤ) ^ m - 1 := by
  -- Step 1: `ψ² a ≡ 2^m a`, `ψ³ a ≡ 3^m a` modulo `ℤb`; write the corrections as `μ₂`, `μ₃`.
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ : ℤ, ψ2 a = (2:ℤ)^m • a + μ • b := by
    have h1 : i (ψ2 a - (2:ℤ)^m • a) = 0 := by
      rw [map_sub, map_zsmul, hψa2, sub_self]
    obtain ⟨k, hk⟩ := hker _ h1
    exact ⟨k, sub_eq_iff_eq_add'.mp hk⟩
  obtain ⟨μ₃, hμ₃⟩ : ∃ μ : ℤ, ψ3 a = (3:ℤ)^m • a + μ • b := by
    have h1 : i (ψ3 a - (3:ℤ)^m • a) = 0 := by
      rw [map_sub, map_zsmul, hψa3, sub_self]
    obtain ⟨k, hk⟩ := hker _ h1
    exact ⟨k, sub_eq_iff_eq_add'.mp hk⟩
  -- Step 2: expand both sides of `ψ²ψ³ a = ψ³ψ² a` using the values of `ψ^k` on `a` and `b`.
  have hL : ψ2 (ψ3 a) = ((3:ℤ)^m * (2:ℤ)^m) • a + ((3:ℤ)^m * μ₂ + μ₃ * (2:ℤ)^(2*m)) • b := by
    have hh' := map_apply_add_smul G ψ2 a b ((3:ℤ)^m) μ₃ ((2:ℤ)^m) μ₂ ((2:ℤ)^(2*m)) hμ₂ hψb2
    rw [← hμ₃] at hh'
    exact hh'
  have hR : ψ3 (ψ2 a) = ((2:ℤ)^m * (3:ℤ)^m) • a + ((2:ℤ)^m * μ₃ + μ₂ * (3:ℤ)^(2*m)) • b := by
    have hh' := map_apply_add_smul G ψ3 a b ((2:ℤ)^m) μ₂ ((3:ℤ)^m) μ₃ ((3:ℤ)^(2*m)) hμ₃ hψb3
    rw [← hμ₂] at hh'
    exact hh'
  have hXY : ((3:ℤ)^m * μ₂ + μ₃ * (2:ℤ)^(2*m)) • b = ((2:ℤ)^m * μ₃ + μ₂ * (3:ℤ)^(2*m)) • b := by
    have hh' := hcomm a
    rw [hL, hR] at hh'
    rw [show (3:ℤ)^m * (2:ℤ)^m = (2:ℤ)^m * (3:ℤ)^m by ring] at hh'
    exact add_left_cancel hh'
  have hAB : ((3:ℤ)^m * μ₂ + μ₃ * (2:ℤ)^(2*m)) - ((2:ℤ)^m * μ₃ + μ₂ * (3:ℤ)^(2*m)) = 0 :=
    hb _ (by rw [sub_smul]; exact sub_eq_zero.mpr hXY)
  -- The integer identity extracted from the commutation relation.
  have hrel : ((2:ℤ)^(2*m) - (2:ℤ)^m) * μ₃ = ((3:ℤ)^(2*m) - (3:ℤ)^m) * μ₂ := by
    linear_combination hAB
  -- Step 3: `μ₂` is odd.
  have hodd : Odd μ₂ := by
    obtain ⟨y, hy⟩ := hsq
    have hy1 : (2:ℤ)^m • a + (μ₂ - h) • b = 2 • y := by
      rw [hμ₂, add_sub_assoc, ← sub_smul] at hy
      exact hy
    -- Apply `i` and use `hA` to cancel the factor `2`.
    have h2 : (2:ℤ)^m • i a = (2:ℤ) • i y := by
      have hc := congrArg i hy1
      rw [map_add, map_zsmul, map_zsmul, hib, smul_zero, add_zero, map_nsmul] at hc
      rw [← natCast_zsmul] at hc
      exact hc
    have hm1 : (2:ℤ)^m = 2 * (2:ℤ)^(m-1) := by
      have hmm : m = (m-1)+1 := by omega
      conv_lhs => rw [hmm]
      rw [pow_succ]; ring
    have h3 : (2:ℤ) • ((2:ℤ)^(m-1) • i a) = (2:ℤ) • i y := by
      rw [← mul_smul, ← hm1]
      exact h2
    have hz : (2:ℤ) • (i y - (2:ℤ)^(m-1) • i a) = 0 := by
      rw [smul_sub, h3, sub_self]
    have hiy : i y = (2:ℤ)^(m-1) • i a := by
      refine sub_eq_zero.mp (hA _ ?_)
      rw [← natCast_zsmul]
      exact hz
    obtain ⟨ν, hν⟩ := hker (y - (2:ℤ)^(m-1) • a) (by rw [map_sub, map_zsmul, hiy, sub_self])
    have hy2 : (2:ℤ) • y = (2:ℤ)^m • a + (2*ν) • b := by
      rw [sub_eq_iff_eq_add'.mp hν, smul_add, ← mul_smul, ← mul_smul, ← hm1]
    have hyz : (2:ℤ)^m • a + (μ₂ - h) • b = (2:ℤ) • y := by
      rw [hy1]; exact (natCast_zsmul y 2).symm
    have hPQ : (2:ℤ)^m • a + (μ₂ - h) • b = (2:ℤ)^m • a + (2*ν) • b := by rw [hyz, hy2]
    have hbcoef : (μ₂ - h) • b = (2*ν) • b := add_left_cancel hPQ
    have hz2 : μ₂ - h - 2*ν = 0 := hb _ (by rw [sub_smul]; exact sub_eq_zero.mpr hbcoef)
    have hμ2eq : μ₂ = h + 2*ν := by omega
    obtain ⟨q, hq⟩ := hh
    exact ⟨q + ν, by omega⟩
  -- Step 4: the arithmetic of `Work.Hopf`.
  exact Work.Hopf.two_pow_dvd_of_psi_relation m hm μ₂ μ₃ hrel hodd

end Work.KT
