import Mathlib
import Submission.Work.ZassenhausSuzuki.Tits

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Uniqueness of the Tits endomorphism of `GF(2^(2n+1))`  (D1 of the lead's note)

If `θ` is a Tits endomorphism of `K = GF(2^(2n+1))`, i.e. `θ ≠ 1` and `θ (θ x) = x ^ 2`, then
`θ` is literally `titsTheta n` (`x ↦ x ^ (2 ^ (n+1))`).

Proof.  `K` is a finite field, so it is a Galois extension of its prime field `ZMod 2` with
cyclic Galois group, and every `ZMod 2`-algebra automorphism of `K` is a power of the Frobenius
`F` (`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`).  Writing `Θ = F ^ i` and
`T = F ^ j` for the two automorphisms induced by `θ` and by `titsTheta n`, the relation
`Θ * Θ = T * T` (both are the squaring map, `hθ.2` and `titsTheta_sq_apply`) gives
`F ^ (2i) = F ^ (2j)`, hence `2i ≡ 2j (mod 2n+1)`, and since `2n+1` is odd this forces
`i ≡ j (mod 2n+1)`, i.e. `i = j` because `i, j < 2n+1`.  Then `Θ = T`, and evaluating at `x`
gives `θ = titsTheta n`.

This is `TitsThetaUniqueProp` (`ModelDatum.lean`); it removes the last ambiguity in the model
half of the recognition (`SzModel n` is coordinated by `A(GF(2^m), θ)` for *the* Tits `θ`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem isTitsTheta_eq_titsTheta (n : ℕ)
    {θ : GaloisField 2 (2 * n + 1) ≃+* GaloisField 2 (2 * n + 1)}
    (hθ : IsTitsTheta θ) : θ = titsTheta n := by
  let K := GaloisField 2 (2 * n + 1)
  have hfixθ : ∀ x : ZMod 2, θ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := by
    intro x
    have hx : ((x.val : ℕ) : ZMod 2) = x := ZMod.natCast_zmod_val x
    rw [← hx, map_natCast (algebraMap (ZMod 2) K) x.val]
    exact map_natCast θ x.val
  let Θ : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := θ) hfixθ
  let F : K ≃ₐ[ZMod 2] K := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let T : K ≃ₐ[ZMod 2] K := F ^ (n + 1)
  have hfr : Module.finrank (ZMod 2) K = 2 * n + 1 := GaloisField.finrank 2 (by omega)
  have hForder : orderOf F = 2 * n + 1 := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hfr]
  obtain ⟨i, hi₀⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 Θ
  obtain ⟨j, hj₀⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 T
  have hi : F ^ (i : ℕ) = Θ := hi₀
  have hj : F ^ (j : ℕ) = T := hj₀
  have hΘapp : ∀ x, Θ x = θ x := fun x => AlgEquiv.ofRingEquiv_apply hfixθ x
  have hTapp : ∀ x, T x = titsTheta n x := by
    intro x
    show (F ^ (n + 1)) x = titsTheta n x
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod 2) K (n + 1), ZMod.card 2,
      titsTheta_apply]
  have hΘ2 : F ^ (2 * i.1) = Θ * Θ := by
    rw [show 2 * i.1 = i.1 * 2 by ring, pow_mul, hi, pow_two]
  have hT2 : F ^ (2 * j.1) = T * T := by
    rw [show 2 * j.1 = j.1 * 2 by ring, pow_mul, hj, pow_two]
  have hsq : Θ * Θ = T * T := by
    apply AlgEquiv.ext
    intro x
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    show θ (θ x) = T (T x)
    rw [hθ.2 x, hTapp x, hTapp (titsTheta n x), titsTheta_sq_apply n x]
  have hpow : F ^ (2 * i.1) = F ^ (2 * j.1) := by rw [hΘ2, hsq, hT2]
  have hmod : 2 * i.1 ≡ 2 * j.1 [MOD orderOf F] :=
    (pow_eq_pow_iff_modEq (x := F)).mp hpow
  have hmod' : 2 * i.1 ≡ 2 * j.1 [MOD 2 * n + 1] := by simpa [hForder] using hmod
  have hcop : Nat.Coprime 2 (2 * n + 1) :=
    (Nat.coprime_two_right.mpr ⟨n, by ring⟩ :
      (2 * n + 1).Coprime 2).symm
  have hgcd : (2 * n + 1).gcd 2 = 1 := by
    rw [Nat.gcd_comm (2 * n + 1) 2]
    exact hcop
  have hij : i.1 = j.1 := by
    have h1 := Nat.ModEq.cancel_left_div_gcd (m := 2 * n + 1) (c := 2) (by omega) hmod'
    rw [hgcd, Nat.div_one] at h1
    have hi2 : (i : ℕ) < 2 * n + 1 := by have h := i.2; omega
    have hj2 : (j : ℕ) < 2 * n + 1 := by have h := j.2; omega
    exact h1.eq_of_lt_of_lt hi2 hj2
  have hΘT : Θ = T := by rw [← hi, ← hj, hij]
  apply RingEquiv.ext
  intro x
  exact (hΘapp x).symm.trans ((DFunLike.congr_fun hΘT x).trans (hTapp x))

end Work.ZassenhausSuzuki
