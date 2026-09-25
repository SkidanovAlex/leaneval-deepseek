import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.InvCharSetup
import Submission.Work.CFTLib.splitSetOf_density
import Submission.Work.CFTLib.splitSet_determines_field
import Submission.Work.CFTLib.splitSet_eq_imp_proportional
import Submission.Work.CFTLib.card_oneDim_submodules
import Submission.Work.CFTLib.exists_injective_oneDim_invChar

/-!
# `invChar_le_invCharSubmodule`

The dimension of the space of `Gal(K/F)`-invariant characters of the class group of `K` is bounded
by the dimension of the space of `Gal(K'/F)`-invariant characters of `N = Gal(K'/K)`.

The proof counts one-dimensional subspaces: there is an injection between the corresponding
projective spaces (`exists_injective_oneDim_invChar`) and the number of one-dimensional subspaces of
a `d`-dimensional `𝔽_p`-space is `(p ^ d - 1)/(p - 1)` (`card_oneDim_submodules`), whence
`p ^ m ≤ p ^ n` and `m ≤ n`.
-/

namespace Work.CFTLib

open NumberField CategoryTheory

/-- Arithmetic step: from `(p ^ m - 1) / (p - 1) ≤ (p ^ n - 1) / (p - 1)` conclude `m ≤ n`. -/
theorem pow_le_of_div_le (p m n : ℕ) [Fact p.Prime]
    (h : (p ^ m - 1) / (p - 1) ≤ (p ^ n - 1) / (p - 1)) : m ≤ n := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdvd : p - 1 ∣ p ^ m - 1 := Nat.sub_one_dvd_pow_sub_one p m
  have hdvd' : p - 1 ∣ p ^ n - 1 := Nat.sub_one_dvd_pow_sub_one p n
  have hmul : (p - 1) * ((p ^ m - 1) / (p - 1)) ≤ (p - 1) * ((p ^ n - 1) / (p - 1)) :=
    Nat.mul_le_mul_left _ h
  rw [Nat.mul_div_cancel' hdvd, Nat.mul_div_cancel' hdvd'] at hmul
  have hpow_pos : 1 ≤ p ^ n := Nat.one_le_pow n p (by omega)
  have hpowy : p ^ m ≤ p ^ n := (Nat.sub_le_sub_iff_right hpow_pos).mp hmul
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hpowy

theorem invChar_le_invCharSubmodule (hHCF : CFTLib.PClassFieldArtin)
    (hUAD : CFTLib.UnramifiedAbelianDegreeLe)
    {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (p : ℕ) [Fact p.Prime]
    (hG' : IsPGroup p (K' ≃ₐ[F] K'))
    (hmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
      [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[K] L) →
      CFTLib.IsUnramified K L → Nonempty (L →ₐ[K] K')) :
    Module.finrank (ZMod p) (Work.CFTLib.clInvariantChar F K p)
      ≤ Module.finrank (ZMod p) (Work.CFTLib.invCharSubmodule p
          (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_oneDim_invChar hHCF (F := F) (K := K) (K' := K') p hG' hmax
  haveI : Finite (Additive (ClassGroup (𝓞 K)) →+ ZMod p) :=
    Finite.of_injective (fun f : Additive (ClassGroup (𝓞 K)) →+ ZMod p =>
      (f : Additive (ClassGroup (𝓞 K)) → ZMod p)) (fun a b h => AddMonoidHom.ext (congrFun h))
  haveI : Finite (Additive ((AlgEquiv.restrictNormalHom K :
      (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) →+ ZMod p) :=
    Finite.of_injective (fun f : Additive ((AlgEquiv.restrictNormalHom K :
        (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) →+ ZMod p =>
      (f : Additive ((AlgEquiv.restrictNormalHom K :
        (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) → ZMod p)) (fun a b h => AddMonoidHom.ext (congrFun h))
  haveI : Fintype (Work.CFTLib.clInvariantChar F K p) := Fintype.ofFinite _
  haveI : Fintype (Work.CFTLib.invCharSubmodule p
      (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker) := Fintype.ofFinite _
  have hcard := Nat.card_le_card_of_injective f hf
  rw [card_oneDim_submodules p (Work.CFTLib.clInvariantChar F K p),
      card_oneDim_submodules p (Work.CFTLib.invCharSubmodule p
        (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[F] K') →* (K ≃ₐ[F] K)).ker)] at hcard
  exact pow_le_of_div_le p _ _ hcard

end Work.CFTLib
