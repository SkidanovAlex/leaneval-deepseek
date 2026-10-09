import Mathlib
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZConstruction.kummerCharMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` Kummer character: additivity in the group variable

The wiring of the odd-`p` local Tate pairing (gate `Work.SSGRoute.ZConstruction.auxPairingGate_odd`)
evaluates the Kummer character `χ_β` of a *global* element `β ∈ Kˣ` at a *group element* `σ` of
`Gal(Ω/↥K)`, namely at the local Artin image of the second variable.  The two formal properties of
`Work.SSGRoute.kummerCharZMod` used there are

* additivity in the group variable (`kummerCharZMod_apply_mul`, `kummerCharZMod_apply_pow`), and
* additivity in the coefficient *modulo* a factor of trivial local Kummer character
  (`kummerCharZMod_mul_eq_of_kummerCharMonoidHom_eq_one`), which is what makes the coherence clause of
  `exists_localKummerLift` invisible at the place.

Both were used inline in `localPairingValue.lean` (`exists_levelCharacter`) and are collected here in
the reusable form the pairing construction consumes.  The triviality statement
`kummerCharZMod_eq_zero_of_kummerCharMonoidHom_eq_one` is the *evaluation form* of the local Kummer
dictionary `Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff`, for the elements of
`decomp (k := ↥K) A`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The Kummer character is additive in the group variable.**
`χ_β (σ τ) = χ_β σ + χ_β τ` for every `β ∈ Kˣ`. -/
theorem kummerCharZMod_apply_mul (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b : (↥K)ˣ)
    (σ τ : Ω ≃ₐ[↥K] Ω) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ * τ) =
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ +
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b τ := by
  rw [kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply,
    kummerIdx_mul_apply p hζ b (kummerSqrtUnitZMod (Ω := Ω) p b)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p b) σ τ]

/-- **The Kummer character is additive in the group variable, powers.** -/
theorem kummerCharZMod_apply_pow (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b : (↥K)ˣ)
    (σ : Ω ≃ₐ[↥K] Ω) (n : ℕ) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ ^ n) =
      n • kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ := by
  induction n with
  | zero =>
    have h : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b 1 =
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b 1 +
          kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b 1 := by
      simpa using kummerCharZMod_apply_mul ζ hζ b 1 1
    rw [pow_zero, zero_smul]
    exact (add_left_cancel (by rw [add_zero]; exact h)).symm
  | succ m ih => rw [pow_succ, kummerCharZMod_apply_mul, ih, succ_nsmul]

/-- **A `p`-th power of a group element is invisible to the Kummer character** (the values lie in
`ZMod p`). -/
theorem kummerCharZMod_apply_pow_prime (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b : (↥K)ˣ)
    (σ : Ω ≃ₐ[↥K] Ω) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b (σ ^ p) = 0 := by
  rw [kummerCharZMod_apply_pow,
    ← Nat.cast_smul_eq_nsmul (ZMod p) p (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ),
    ZMod.natCast_self, zero_smul]

/-- **The evaluation form of the local Kummer dictionary.**  A global unit with trivial local Kummer
character at the place `A` has vanishing Kummer character at every element of the local group
`decomp (k := ↥K) A`. -/
theorem kummerCharZMod_eq_zero_of_kummerCharMonoidHom_eq_one (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (↥K)ˣ)
    (hb : kummerCharMonoidHom (ζ := ζ) (hζ := hζ) (A := A) hA b = 1)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : σ ∈ SSGRoute.decomp (k := ↥K) A) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ = 0 := by
  have h1 : kummerCharHom p k Ω K ζ hζ A b = 1 := by
    have h := Subtype.ext_iff.mp hb
    simpa [kummerCharMonoidHom, kummerCharHom, Pi.one_apply] using h
  have h2 : Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ) = 1 := by
    have h := DFunLike.congr_fun h1 (⟨σ, hσ⟩ : ↥(SSGRoute.decomp (k := ↥K) A))
    show Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ) = 1
    exact h
  exact (ofAdd_eq_one).mp h2

/-- **A factor of trivial local Kummer character is invisible in the first variable of the pairing.**
If `γ` has trivial local Kummer character at `A`, then `χ_{b γ}` and `χ_b` agree on the whole local
group `decomp (k := ↥K) A`.  This is the statement that turns the coherence clause of
`exists_localKummerLift` (`β (x + x') = β x · β x'` modulo a local `p`-th power) into additivity of
the pairing in its first variable. -/
theorem kummerCharZMod_mul_eq_of_kummerCharMonoidHom_eq_one' (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b γ : (↥K)ˣ)
    (hγ : kummerCharMonoidHom (ζ := ζ) (hζ := hζ) (A := A) hA γ = 1)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : σ ∈ SSGRoute.decomp (k := ↥K) A) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (b * γ) σ =
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ := by
  rw [kummerCharZMod_add (ζ := ζ) (hζ := hζ) b γ σ,
    kummerCharZMod_eq_zero_of_kummerCharMonoidHom_eq_one ζ hζ A hA γ hγ σ hσ, add_zero]

/-- **The `p`-th power of a group element, transported to a `p`-th power of the character variable.**
If `localImageAt 𝔭 δ` is a `p`-th power in the completion, then *any* Kummer character `χ_b` vanishes
at the element of the local group attached to `η ^ p` — the computation that makes additivity of the
pairing in its *second* variable formal. -/
theorem kummerCharZMod_apply_pow_eq_zero (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b : (↥K)ˣ)
    {σ : Ω ≃ₐ[↥K] Ω} {η : Ω ≃ₐ[↥K] Ω} (h : σ = η ^ p) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ b σ = 0 := by
  rw [h, kummerCharZMod_apply_pow_prime]

end

end Work.SSGRoute.ZConstruction
