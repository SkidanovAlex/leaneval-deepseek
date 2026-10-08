import Mathlib
import Submission.Work.Higman.h8_arith
import Submission.Work.Higman.clo_arith
import Submission.Work.Higman.core_alt_pairing_new

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

/-- **Singer-cycle transitivity.**  An `𝔽₂`-linear automorphism `ξ` of a finite `𝔽₂`-vector space
`V` of cardinality `2 ^ n` (`2 ≤ n`) whose order is `2 ^ n - 1` and which has no non-zero fixed
vector acts transitively on the non-zero vectors.

This is the converse of `Work.Higman.singer_data_of_transitive`: `exists_singer_iso` identifies
`V` with `GF(2 ^ n)` so that `ξ` becomes multiplication by a primitive element `ν`, and the
powers of `ν` exhaust the `2 ^ n - 1` non-zero elements of the field. -/
theorem transitive_of_singer_data {n : ℕ} (hn : 2 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hVcard : Nat.card V = 2 ^ n) (ξ : V ≃ₗ[ZMod 2] V)
    (hord : orderOf ξ = 2 ^ n - 1) (hfree : ∀ v : V, ξ v = v → v = 0) :
    ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨φ, ν, hνord, hνeq⟩ := exists_singer_iso hn0 hVcard ξ hord hfree
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  have hνF : orderOf ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) = 2 ^ n - 1 := by
    rw [orderOf_units]; exact hνord
  have hνfin : IsOfFinOrder ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 ^ n - 1, ?_, ?_⟩
    · have h1 : 1 < (2 : ℕ) ^ n := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    · have h := pow_orderOf_eq_one ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n)
      rwa [hνF] at h
  -- Every non-zero element of `GF(2 ^ n)` is a power of `ν`.
  have hpow_gen : ∀ z : GaloisField 2 n, z ≠ 0 →
      ∃ k : ℕ, ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k = z := by
    intro z hz
    have hinj : Set.InjOn
        (fun k : ℕ => ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k)
        ↑(Finset.range (2 ^ n - 1)) := by
      intro k hk l hl hkl
      have hk' : k < 2 ^ n - 1 := Finset.mem_range.mp hk
      have hl' : l < 2 ^ n - 1 := Finset.mem_range.mp hl
      have hmod : k ≡ l [MOD orderOf ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n)] :=
        (IsOfFinOrder.pow_eq_pow_iff_modEq hνfin).mp hkl
      rw [hνF] at hmod
      exact Nat.ModEq.eq_of_lt_of_lt hmod hk' hl'
    have hScard : ((Finset.range (2 ^ n - 1)).image
        (fun k => ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k)).card = 2 ^ n - 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hSsub : (Finset.range (2 ^ n - 1)).image
        (fun k => ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k)
        ⊆ (Finset.univ : Finset (GaloisField 2 n)).erase 0 := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, _hk, rfl⟩ := hx
      exact Finset.mem_erase.mpr ⟨pow_ne_zero k (Units.ne_zero ν), Finset.mem_univ _⟩
    have hErase : ((Finset.univ : Finset (GaloisField 2 n)).erase 0).card = 2 ^ n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hFcard]
    have hSeq : (Finset.range (2 ^ n - 1)).image
        (fun k => ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k)
        = (Finset.univ : Finset (GaloisField 2 n)).erase 0 :=
      Finset.eq_of_subset_of_card_le hSsub (by simp [hScard, hErase])
    have hzmem : z ∈ (Finset.range (2 ^ n - 1)).image
        (fun k => ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k) := by
      rw [hSeq]
      exact Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩
    rw [Finset.mem_image] at hzmem
    obtain ⟨k, _hk, hkz⟩ := hzmem
    exact ⟨k, hkz⟩
  -- `φ` intertwines the powers of `ξ` with multiplication by the powers of `ν`.
  have hφpow : ∀ (k : ℕ) (v : V),
      φ ((ξ ^ k) v) = ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ k * φ v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ', LinearEquiv.mul_apply, hνeq, ih, pow_succ]
        ring
  intro a b ha hb
  have hφa : φ a ≠ 0 := fun h => ha (φ.injective (by rw [h, map_zero]))
  have hφb : φ b ≠ 0 := fun h => hb (φ.injective (by rw [h, map_zero]))
  obtain ⟨k, hk⟩ := hpow_gen (φ b * (φ a)⁻¹) (mul_ne_zero hφb (inv_ne_zero hφa))
  refine ⟨k, φ.injective ?_⟩
  rw [hφpow k a, hk, mul_assoc, inv_mul_cancel₀ hφa, mul_one]

/-- **The algebraic core of Higman's Lemma 8** (Higman 1963, §4, Lemma 6 in the Suzuki form).
Let `V`, `W` be finite `𝔽₂`-vector spaces of cardinality `2 ^ n` (`n ≥ 2`) equipped with linear
automorphisms `ξV`, `ξW` of order `2 ^ n - 1` and without nonzero fixed vectors.  Suppose
* `B : V × V → W` is an alternating biadditive `ξ`-equivariant map, not identically zero,
* `s : V → W` is `ξ`-equivariant, vanishes only at `0`, and has polar form `B`
  (`s (a+b) + s a + s b = B a b`),
* `β : V × W → W` is a biadditive `ξ`-equivariant map which is not identically zero and satisfies
  `β a (s a) = 0` for all `a`.
Then we reach a contradiction. -/
theorem h8_core {n : ℕ} (hn : 2 ≤ n)
    {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hVcard : Nat.card V = 2 ^ n) (hWcard : Nat.card W = 2 ^ n)
    (ξV : V ≃ₗ[ZMod 2] V) (ξW : W ≃ₗ[ZMod 2] W)
    (hVord : orderOf ξV = 2 ^ n - 1) (hWord : orderOf ξW = 2 ^ n - 1)
    (hVfree : ∀ v : V, ξV v = v → v = 0) (hWfree : ∀ w : W, ξW w = w → w = 0)
    (B : V → V → W) (hB1 : ∀ a b c : V, B (a + b) c = B a c + B b c)
    (hB2 : ∀ a b c : V, B a (b + c) = B a b + B a c) (hBdiag : ∀ a : V, B a a = 0)
    (hBeq : ∀ a b : V, ξW (B a b) = B (ξV a) (ξV b)) (hBne : ∃ a b : V, B a b ≠ 0)
    (s : V → W) (hs0 : s 0 = 0) (hseq : ∀ a : V, ξW (s a) = s (ξV a))
    (hspol : ∀ a b : V, s (a + b) + s a + s b = B a b)
    (hsne : ∀ a : V, a ≠ 0 → s a ≠ 0)
    (β : V → W → W) (hβ1 : ∀ a a' : V, ∀ b : W, β (a + a') b = β a b + β a' b)
    (hβ2 : ∀ a : V, ∀ b b' : W, β a (b + b') = β a b + β a b')
    (hβeq : ∀ a : V, ∀ b : W, ξW (β a b) = β (ξV a) (ξW b))
    (hβrel : ∀ a : V, β a (s a) = 0) (hβne : ∃ a : V, ∃ b : W, β a b ≠ 0) : False :=
  core_alt_pairing hn hVcard hWcard ξV ξW
    (transitive_of_singer_data hn hVcard ξV hVord hVfree)
    (transitive_of_singer_data hn hWcard ξW hWord hWfree)
    B hB1 hB2 hBdiag hBeq hBne s hs0 hseq hspol hsne β hβ1 hβ2 hβeq hβrel hβne

end Work.Higman
