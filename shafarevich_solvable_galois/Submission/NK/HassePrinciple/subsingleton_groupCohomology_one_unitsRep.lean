import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.NK.HassePrinciple.Mu
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

set_option maxHeartbeats 1600000 in
/-- **Noether's generalisation of Hilbert's Theorem 90**, in the `CoeffInt` coefficient world:
`H¹(Gal(L/K), Lˣ) = 0` for a finite Galois extension `L/K`, where `Lˣ` carries its natural
`Gal(L/K)`-action and is regarded as a `ULift ℤ`-module. -/
theorem subsingleton_groupCohomology_one_unitsRep {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Subsingleton (groupCohomology (NK.HassePrinciple.unitsRep K L) 1) := by
  -- the `Gal(L/K)`-action on `unitsRep` written multiplicatively
  have hunits : ∀ (g : Gal(L/K)) (a : Additive Lˣ),
      (unitsRep K L).ρ g a = Additive.ofMul (α := Lˣ) (g • Additive.toMul (α := Lˣ) a) :=
    fun _ _ => rfl
  -- it suffices to show that every class in `H¹` vanishes
  have key : ∀ a : groupCohomology (unitsRep K L) 1, a = 0 := by
    intro a
    refine groupCohomology.H1_induction_on a (fun x => ?_)
    -- a cocycle is a coboundary
    refine (groupCohomology.H1π_eq_zero_iff x).2 ?_
    -- rewrite the cocycle `x : Gal(L/K) → Additive Lˣ` into the multiplicative world
    let y : Gal(L/K) → Additive Lˣ := fun g => x.1 g
    have hy : ∀ g, y g = x.1 g := fun _ => rfl
    have hcoc : groupCohomology.IsMulCocycle₁ (M := Lˣ)
        (fun g => Additive.toMul (α := Lˣ) (y g)) := by
      intro g h
      have h1 : y (g * h) =
          Additive.ofMul (α := Lˣ) (g • Additive.toMul (α := Lˣ) (y h)) + y g := by
        have h0 := (groupCohomology.mem_cocycles₁_iff (A := unitsRep K L) (x.1)).1 x.2 g h
        rw [hunits g (y h)] at h0
        exact h0
      calc Additive.toMul (α := Lˣ) (y (g * h))
          = Additive.toMul (α := Lˣ)
              (Additive.ofMul (α := Lˣ) (g • Additive.toMul (α := Lˣ) (y h)) + y g) := by
            rw [h1]
        _ = Additive.toMul (α := Lˣ)
              (Additive.ofMul (α := Lˣ) (g • Additive.toMul (α := Lˣ) (y h)))
              * Additive.toMul (α := Lˣ) (y g) := toMul_add (α := Lˣ) _ _
        _ = (g • Additive.toMul (α := Lˣ) (y h)) * Additive.toMul (α := Lˣ) (y g) := by
            rw [toMul_ofMul]
    -- Hilbert 90: the cocycle is a coboundary
    obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (fun g => Additive.toMul (α := Lˣ) (y g)) hcoc
    -- `g ↦ ρ g (β) - β` is exactly `x`
    let hw : (unitsRep K L).V := Additive.ofMul (α := Lˣ) β
    refine ⟨hw, ?_⟩
    funext g
    rw [groupCohomology.d₀₁_hom_apply]
    simp only [hw]
    rw [show (unitsRep K L).ρ g (Additive.ofMul (α := Lˣ) β) = Additive.ofMul (α := Lˣ) (g • β)
        from rfl]
    change Additive.ofMul (α := Lˣ) (g • β) - Additive.ofMul (α := Lˣ) β = y g
    rw [← ofMul_div (x := g • β) (y := β), hβ g]
    exact ofMul_toMul (α := Lˣ) (y g)
  exact ⟨fun a b => by rw [key a, key b]⟩

end NK.HassePrinciple
