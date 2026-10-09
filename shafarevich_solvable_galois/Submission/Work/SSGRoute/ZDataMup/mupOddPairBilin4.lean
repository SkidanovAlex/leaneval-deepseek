import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupOddPairBilin3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Well-definedness of the odd-`p` pairing on local classes

* `oPairGlob_congr_fst`: the pairing computed with global representatives depends on the first
  representative only through its local `p`-th power class (from `oPairGlob_add` and the vanishing
  on locally trivial elements);
* `oPair_eq_oPairGlob`: the pairing value is the one computed with the coherent lift;
* `oPair_congr`: the pairing depends on the two representatives only through their local `p`-th power
  classes;
* `oPair_add_left`: additivity in the first variable.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataMup.OddForm

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

variable (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (hA : SSGRoute.IsFinPlace k A)

/-- **The pairing computed with global representatives depends on the first representative only
through its local `p`-th power class.** -/
theorem oPairGlob_congr_fst (γ γ' β : (↥K)ˣ)
    (h : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) γ') :
    oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA γ β =
      oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA γ' β := by
  classical
  set δ : (↥K)ˣ := γ' * γ⁻¹ with hδdef
  have hδ : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) δ = 1 := by
    rw [hδdef, map_mul, map_inv, h, mul_inv_cancel]
  have hγ' : δ * γ = γ' := by
    rw [hδdef, mul_assoc, inv_mul_cancel, mul_one]
  rw [← hγ', oPairGlob_add (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA δ γ β,
    oPairGlob_eq_zero_of_localPowClass_eq_one (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA δ β hδ,
    zero_add]

/-- **The pairing value is the one computed with the coherent lifts of its arguments.** -/
theorem oPair_eq_oPairGlob (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y =
      oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
        (hLift ζ hζ A hA x) (hLift ζ hζ A hA y) := by
  haveI : FiniteDimensional ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  haveI : IsGalois ↥K ↥(oLevel (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
  rw [oPair_eq_hChar (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y]
  rfl

/-- **The pairing only depends on the local classes of the representatives.** -/
theorem oPair_congr (x y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) (α β : (↥K)ˣ)
    (hα : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) α =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA x))
    (hβ : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA) β =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA y)) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y =
      oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA α β := by
  rw [oPair_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y,
    oPairGlob_congr_fst (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
      (hLift ζ hζ A hA x) α (hLift ζ hζ A hA y) hα.symm,
    oPairGlob_localClass (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
      α (hLift ζ hζ A hA y) β hβ.symm]

/-- **Additivity of the pairing in the first variable.** -/
theorem oPair_add_left (x x' y : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (x + x') y =
      oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y +
        oPair (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x' y := by
  classical
  have hδ : ZConstruction.kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA
      (hLift ζ hζ A hA (x + x') * (hLift ζ hζ A hA x * hLift ζ hζ A hA x')⁻¹) = 1 :=
    hLift_coherent (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA x x'
  have hlc : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
      (hLift ζ hζ A hA (x + x') * (hLift ζ hζ A hA x * hLift ζ hζ A hA x')⁻¹) = 1 :=
    (ZConstruction.kummerCharMonoidHom_eq_one_iff (p := p) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA (oddPrime (K := K) A hA) (oddPrime_spec (K := K) (A := A) hA) _).mp hδ
  have hcoh : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
      (hLift ζ hζ A hA (x + x')) =
      NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA x * hLift ζ hζ A hA x') := by
    have h2 : NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
        (hLift ζ hζ A hA (x + x')) *
        (NK.UchidaKummer.localPowClass ↥K p (oddPrime (K := K) A hA)
          (hLift ζ hζ A hA x * hLift ζ hζ A hA x'))⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact hlc
    exact mul_inv_eq_one.mp h2
  rw [oPair_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA (x + x') y,
    oPair_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y,
    oPair_eq_oPairGlob (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x' y,
    oPairGlob_congr_fst (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
      (hLift ζ hζ A hA (x + x')) (hLift ζ hζ A hA x * hLift ζ hζ A hA x')
      (hLift ζ hζ A hA y) hcoh,
    oPairGlob_add (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
      (hLift ζ hζ A hA x) (hLift ζ hζ A hA x') (hLift ζ hζ A hA y)]

end

end Work.SSGRoute.ZDataMup.OddForm
