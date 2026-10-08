import Mathlib
import Submission.Work.ZASS.Leaf9

/-!
# Area ZASS2: the scaling factor `α` of the Z6.0 coordinates is a monomorphism

`Work.GW2.ZassCoords G X inf zero U` (step Z6.0, `Submission/Work/ZASS2/zassCoord.lean`)
packages the Z2–Z5 output as

* a finite field `E` and a bijection `Θ : X ≃ Option E` with `Θ inf = none`, `Θ zero = some 0`;
* the action of `U` on `X` becomes `y ↦ y + τ u`;
* the action of `H = pairStab G inf zero` on `X` becomes `y ↦ α h * y`.

This file records the elementary consequences of the *last* equivariance, which are used
whenever `α` has to be treated as a multiplicative character of `H`:

* `α` is multiplicative (`zassCoords_alpha`, first conjunct),
* `α 1 = 1`,
* `α` is injective (using faithfulness of the action, `hZ.1`),
* `α h⁻¹ = (α h)⁻¹`,

and the auxiliary fact `α h ≠ 0` (`zassCoords_alpha_ne_zero`).

The proofs only use `C.scale`, `C.Θ_inf` and `FaithfulSMul G X` from `ZassHyps2`: evaluating
the equivariance at the point `e1` with `Θ e1 = some 1` turns the multiplicative law of the
action `h₁ • (h₂ • e1) = (h₁ h₂) • e1` into a statement about `E`.
-/

namespace Work.ZASS2

open Work.GW2

variable {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}

/-- The element of `X` whose coordinate is `1`. -/
private noncomputable def zassOne (C : ZassCoords G X inf zero U) : X :=
  C.Θ.symm (some (1 : C.E))

private theorem zassOne_spec (C : ZassCoords G X inf zero U) :
    C.Θ (zassOne C) = some (1 : C.E) := Equiv.apply_symm_apply C.Θ _

/-- An element of `H = G_{∞0}` never scales by `0`: it cannot collapse a point onto `0`. -/
theorem zassCoords_alpha_ne_zero (C : ZassCoords G X inf zero U)
    (h : Work.Zassenhaus.pairStab G inf zero) : C.α h ≠ 0 := by
  intro h0
  have hx : C.Θ (zassOne C) = some (1 : C.E) := zassOne_spec C
  have hxz : zassOne C ≠ zero := by
    intro hh
    rw [hh, C.Θ_zero] at hx
    simp at hx
  have hhz : (h : G) • zero = zero := (Work.Zassenhaus.mem_pairStab_iff.mp h.2).1
  have hclash : (h : G) • zassOne C ≠ zero := by
    intro hh
    refine hxz (MulAction.injective (h : G) ?_)
    show (h : G) • zassOne C = (h : G) • zero
    rw [hh, hhz]
  have hsc := C.scale h (zassOne C)
  rw [hx] at hsc
  simp [h0] at hsc
  exact hclash (C.Θ.injective (by rw [hsc, C.Θ_zero]))

/-- **Step Z6.0, multiplicative structure of `α`.** The scaling factor
`α : G_{∞0} → E` of the coordinates is a multiplicative injection with `α 1 = 1`, and it
commutes with inversion.

Only `C.scale` (equivariance of the `H`-action), `C.Θ_inf` and the faithfulness of the
action are used; the hypotheses `hZ`, `hq`, `hne` are carried along as in the interface. -/
theorem zassCoords_alpha {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (hZ : Work.GW2.ZassHyps2 G X q) (hq : 2 ≤ q) {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (C : Work.GW2.ZassCoords G X inf zero U) :
    (∀ h₁ h₂ : Work.Zassenhaus.pairStab G inf zero, C.α (h₁ * h₂) = C.α h₁ * C.α h₂) ∧
      C.α 1 = 1 ∧
      (∀ h : Work.Zassenhaus.pairStab G inf zero, C.α h = 1 → h = 1) ∧
      (∀ h : Work.Zassenhaus.pairStab G inf zero, C.α h⁻¹ = (C.α h)⁻¹) := by
  classical
  -- `hα` evaluates the scaling law at the point of coordinate `1`.
  have hα : ∀ h : Work.Zassenhaus.pairStab G inf zero,
      C.Θ ((h : G) • zassOne C) = some (C.α h) := by
    intro h
    rw [C.scale h (zassOne C), zassOne_spec C]
    simp
  have hmul : ∀ h₁ h₂ : Work.Zassenhaus.pairStab G inf zero,
      C.α (h₁ * h₂) = C.α h₁ * C.α h₂ := by
    intro h₁ h₂
    have hcoe : (((h₁ * h₂ : Work.Zassenhaus.pairStab G inf zero)) : G) =
        (h₁ : G) * (h₂ : G) := rfl
    have hA : C.Θ ((((h₁ * h₂ : Work.Zassenhaus.pairStab G inf zero)) : G) • zassOne C) =
        some (C.α (h₁ * h₂)) := hα (h₁ * h₂)
    have hB : C.Θ ((((h₁ * h₂ : Work.Zassenhaus.pairStab G inf zero)) : G) • zassOne C) =
        some (C.α h₁ * C.α h₂) := by
      rw [hcoe, mul_smul]
      calc C.Θ ((h₁ : G) • ((h₂ : G) • zassOne C))
          = (C.Θ ((h₂ : G) • zassOne C)).map (C.α h₁ * ·) :=
            C.scale h₁ ((h₂ : G) • zassOne C)
        _ = (some (C.α h₂)).map (C.α h₁ * ·) := by rw [hα h₂]
        _ = some (C.α h₁ * C.α h₂) := by simp
    exact Option.some.inj (hA.symm.trans hB)
  have hone : C.α 1 = 1 := by
    have h := hα 1
    have h1 : (((1 : Work.Zassenhaus.pairStab G inf zero)) : G) • zassOne C = zassOne C :=
      one_smul _ _
    rw [h1, zassOne_spec C] at h
    exact (Option.some.inj h).symm
  have hinj : ∀ h : Work.Zassenhaus.pairStab G inf zero, C.α h = 1 → h = 1 := by
    intro h hh
    refine Subtype.ext ?_
    apply hZ.1.eq_of_smul_eq_smul
    intro x
    show (h : G) • x = (1 : G) • x
    rw [one_smul]
    apply C.Θ.injective
    rw [C.scale h x, hh]
    simp
  refine ⟨hmul, hone, hinj, fun h => ?_⟩
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hmul h h⁻¹, mul_inv_cancel, hone]

end Work.ZASS2
