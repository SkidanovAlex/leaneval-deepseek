import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.Sha2Lib

/-- The cocycle equation for a `1`-cocycle `h` of the coinduced representation, written in terms
of the underlying functions. -/
private lemma coind_cocycle_equation {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
    (φ : D →* Γ) (V : Rep.{0} k D)
    (h : Γ → (Rep.coind φ V).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ V) :
      Set (Γ → (Rep.coind φ V).V))) :
    ∀ g g' : Γ, h (g * g') = (Rep.coind φ V).ρ g (h g') + h g :=
  fun g g' => (groupCohomology.mem_cocycles₁_iff h).1 hc g g'

/-- Evaluating the cocycle equation of the coinduced representation at `1` uses the defining
relation of the coinduced module: `(x • f)(1) = f(x)`. -/
private lemma coind_cocycle_value_at_one {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
    (φ : D →* Γ) (V : Rep.{0} k D)
    (h : Γ → (Rep.coind φ V).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ V) :
      Set (Γ → (Rep.coind φ V).V))) :
    ∀ g g' : Γ, (h (g * g')).1 1 = (h g').1 g + (h g).1 1 := by
  intro g g'
  have hkey : ((Rep.coind φ V).ρ g (h g')).1 1 = (h g').1 (1 * g) := rfl
  rw [coind_cocycle_equation φ V h hc g g', Submodule.coe_add, Pi.add_apply, hkey, one_mul]

theorem coind_cocycle_value {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
    (φ : D →* Γ) (V : Rep.{0} k D)
    (h : Γ → (Rep.coind φ V).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ V) :
      Set (Γ → (Rep.coind φ V).V)))
    (γ x : Γ) (δ : D) (hδ : φ δ = x⁻¹ * γ * x) :
    (h γ).1 (x⁻¹) = (h (φ δ)).1 1 + (h x).1 (x⁻¹) - (V.ρ δ) ((h x).1 (x⁻¹)) := by
  have hval := coind_cocycle_value_at_one φ V h hc
  have h_one : h 1 = 0 := groupCohomology.cocycles₁_map_one ⟨h, hc⟩
  -- `h (x⁻¹)` evaluated at `1` is the negative of `h x` evaluated at `x⁻¹`.
  have hd : (h x⁻¹).1 1 = - (h x).1 x⁻¹ := by
    have hh := hval x⁻¹ x
    rw [inv_mul_cancel, h_one] at hh
    simp only [Submodule.coe_zero, Pi.zero_apply] at hh
    exact eq_neg_of_add_eq_zero_right hh.symm
  -- The cocycle equation at `x⁻¹ * γ` and `x` computes `(h (φ δ)).1 1`.
  have hγ : (h (φ δ)).1 1 = V.ρ δ ((h x).1 x⁻¹) + (h γ).1 x⁻¹ + (h x⁻¹).1 1 := by
    rw [hδ]
    -- the defining relation of `coindV`: `(h x).1 (φ δ * x⁻¹) = (V.ρ δ) ((h x).1 x⁻¹)`
    have hcoind : (h x).1 (x⁻¹ * γ) = V.ρ δ ((h x).1 x⁻¹) := by
      have h1 : x⁻¹ * γ = φ δ * x⁻¹ := by rw [hδ]; group
      rw [h1]
      exact (Representation.mem_coindV _ _ _).1 (h x).2 δ x⁻¹
    have e1 : (h (x⁻¹ * γ * x)).1 1 = (h x).1 (x⁻¹ * γ) + (h (x⁻¹ * γ)).1 1 :=
      hval (x⁻¹ * γ) x
    have e2 : (h (x⁻¹ * γ)).1 1 = (h γ).1 x⁻¹ + (h x⁻¹).1 1 := hval x⁻¹ γ
    rw [e1, e2, hcoind]
    abel
  rw [hγ, hd]
  abel

end Work.SSGRoute.Sha2Lib
