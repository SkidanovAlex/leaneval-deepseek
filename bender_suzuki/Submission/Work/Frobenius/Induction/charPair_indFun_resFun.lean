import Mathlib
import Submission.Work.Frobenius.Pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frobenius reciprocity for the trace pairing `charPair`

`charPair (indFun H φ) ψ = charPair φ (resFun H ψ)`.

Both sides are computed directly from the definitions.  Writing
`T x g = if x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, _⟩ else 0`, we have

`charPair (indFun H φ) ψ = |G|⁻¹ |H|⁻¹ ∑_g ∑_x T x g * ψ g⁻¹`.

Swapping the two sums and substituting `g ↦ x⁻¹ g x` in the inner sum turns
`∑_g T x g * ψ g⁻¹` into `∑_{h ∈ H} φ h * ψ (x⁻¹ h⁻¹ x)`; the remaining sum over
`x` is evaluated by `IsClassFun ψ` (`∑_x ψ (x⁻¹ a x) = |G| * ψ a`), giving
`|H|⁻¹ ∑_{h ∈ H} φ h * ψ h⁻¹ = charPair φ (resFun H ψ)`.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Induction

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]

/-- For a class function `ψ` and any `a`, the sum of `ψ` over the conjugates
`x⁻¹ * a * x` equals `|G| * ψ a`. -/
theorem sum_conj_classFun_mul_card {ψ : G → ℂ} (hψ : IsClassFun ψ) (a : G) :
    ∑ x : G, ψ (x⁻¹ * a * x) = (Nat.card G : ℂ) * ψ a := by
  have h : ∀ x : G, ψ (x⁻¹ * a * x) = ψ a := by
    intro x
    have := hψ a x⁻¹
    simpa using this
  calc ∑ x : G, ψ (x⁻¹ * a * x) = ∑ _x : G, ψ a := Finset.sum_congr rfl (fun x _ => h x)
    _ = (Nat.card G : ℂ) * ψ a := by
        rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
        simp

/-- Summation over `H` of an indicator sum over `G`.  For every `x` one has
`(if x ∈ H then g x _ else 0) * c x = 0` unless `x ∈ H`, so the sum collapses to a
sum over the subtype `H`. -/
theorem sum_dite_mem_mul (g : ∀ x : G, x ∈ H → ℂ) (c : G → ℂ) :
    ∑ x : G, (if hx : x ∈ H then g x hx else 0) * c x = ∑ h : H, g ↑h h.property * c ↑h := by
  set phit : G → ℂ := fun x => if hx : x ∈ H then g x hx else 0 with hphit
  have hgoal : ∑ x : G, phit x * c x = ∑ h : H, g ↑h h.property * c ↑h := by
    have h1 : ∑ x : G, phit x * c x
        = ∑ x ∈ (Finset.univ.filter (fun x : G => x ∈ H)), phit x * c x := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x _ hx
      have hxH : ¬ (x ∈ H) := fun h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩)
      simp only [hphit]
      rw [dite_eq_right hxH]
      simp
    rw [h1]
    rw [Finset.sum_subtype (p := fun x : G => x ∈ H)
          (Finset.univ.filter (fun x : G => x ∈ H)) (fun x => by simp) (fun x => phit x * c x)]
    apply Finset.sum_congr rfl
    intro h _
    show phit ↑h * c ↑h = g ↑h h.property * c ↑h
    simp only [hphit]
    rw [dite_eq_left h.property]
  exact hgoal

/-- The inner reindexing step of Frobenius reciprocity: for fixed `x`,
`∑_g T x g * ψ g⁻¹ = ∑_{h ∈ H} φ h * ψ (x⁻¹ h⁻¹ x)`. -/
theorem indFun_pairing_stepInner (φ : H → ℂ) {ψ : G → ℂ} (x : G) :
    ∑ g : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g⁻¹
    = ∑ h : H, φ h * ψ (x⁻¹ * (h : G)⁻¹ * x) := by
  let F : G → ℂ := fun z => (if hz : z ∈ H then φ ⟨z, hz⟩ else 0) * ψ (x⁻¹ * z⁻¹ * x)
  have hfirst : ∑ g : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g⁻¹
      = ∑ g : G, F (x * g * x⁻¹) := by
    apply Finset.sum_congr rfl
    intro g _
    show (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g⁻¹
        = (if hz : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hz⟩ else 0)
            * ψ (x⁻¹ * (x * g * x⁻¹)⁻¹ * x)
    rw [show x⁻¹ * (x * g * x⁻¹)⁻¹ * x = g⁻¹ by group]
  have hsecond : ∑ g : G, F (x * g * x⁻¹) = ∑ g : G, F g := by
    let e : G ≃ G := (MulAut.conj x).toEquiv
    have he : ∀ y : G, e y = x * y * x⁻¹ := by intro y; simp [e, MulAut.conj_apply]
    have : (fun g : G => F (x * g * x⁻¹)) = (fun g : G => F (e g)) := by
      funext g; rw [he]
    rw [this, Equiv.sum_comp]
  have hthird : ∑ g : G, F g = ∑ h : H, φ h * ψ (x⁻¹ * (h : G)⁻¹ * x) := by
    have h3 := sum_dite_mem_mul (H := H) (fun z (hz : z ∈ H) => φ ⟨z, hz⟩)
      (fun z => ψ (x⁻¹ * z⁻¹ * x))
    change ∑ z : G, (if hz : z ∈ H then φ ⟨z, hz⟩ else 0) * ψ (x⁻¹ * z⁻¹ * x)
        = ∑ h : H, φ h * ψ (x⁻¹ * (h : G)⁻¹ * x)
    exact h3
  rw [hfirst, hsecond, hthird]

/-- **Frobenius reciprocity** for the bilinear trace pairing: the induction functor
`indFun H` is left adjoint to restriction `resFun H`. -/
theorem charPair_indFun_resFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]
    (φ : H → ℂ) {ψ : G → ℂ} (hψ : IsClassFun ψ) :
    charPair (indFun H φ) ψ = charPair φ (resFun H ψ) := by
  rw [charPair_apply, charPair_apply]
  -- rewrite the right hand side in terms of `ψ` on `G`
  have hR : (∑ h : H, φ h * resFun H ψ h⁻¹) = ∑ h : H, φ h * ψ ((h : G)⁻¹) := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [resFun]
    rw [Subgroup.coe_inv]
  rw [hR]
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    have : Nonempty G := ⟨1⟩
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  -- evaluate the double sum `∑_g (∑_x T x g) * ψ g⁻¹`
  have hA : (∑ g : G, (∑ x : G,
        (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * ψ g⁻¹)
      = (Nat.card G : ℂ) * ∑ h : H, φ h * ψ ((h : G)⁻¹) := by
    rw [show (∑ g : G, (∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * ψ g⁻¹)
        = ∑ g : G, ∑ x : G,
            (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g⁻¹ from by
      apply Finset.sum_congr rfl; intro g _; rw [Finset.sum_mul]]
    rw [Finset.sum_comm]
    rw [show (∑ x : G, ∑ g : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g⁻¹)
        = ∑ x : G, ∑ h : H, φ h * ψ (x⁻¹ * (h : G)⁻¹ * x) from by
      apply Finset.sum_congr rfl; intro x _; exact indFun_pairing_stepInner φ x]
    rw [Finset.sum_comm]
    rw [show (∑ h : H, ∑ x : G, φ h * ψ (x⁻¹ * (h : G)⁻¹ * x))
        = ∑ h : H, φ h * ∑ x : G, ψ (x⁻¹ * (h : G)⁻¹ * x) from by
      apply Finset.sum_congr rfl; intro h _; rw [Finset.mul_sum]]
    rw [show (∑ h : H, φ h * ∑ x : G, ψ (x⁻¹ * (h : G)⁻¹ * x))
        = ∑ h : H, φ h * ((Nat.card G : ℂ) * ψ ((h : G)⁻¹)) from by
      apply Finset.sum_congr rfl; intro h _
      rw [sum_conj_classFun_mul_card hψ ((h : G)⁻¹)]]
    rw [show (∑ h : H, φ h * ((Nat.card G : ℂ) * ψ ((h : G)⁻¹)))
        = (Nat.card G : ℂ) * ∑ h : H, φ h * ψ ((h : G)⁻¹) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring]
  have h1 : (∑ g : G, indFun H φ g * ψ g⁻¹)
      = (Nat.card H : ℂ)⁻¹ * (∑ g : G, (∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * ψ g⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    simp only [indFun]
    ring
  rw [h1, hA]
  rw [show (Nat.card G : ℂ)⁻¹
        * ((Nat.card H : ℂ)⁻¹ * ((Nat.card G : ℂ) * ∑ h : H, φ h * ψ ((h : G)⁻¹)))
        = (Nat.card H : ℂ)⁻¹ * (∑ h : H, φ h * ψ ((h : G)⁻¹)) from by
      rw [← mul_assoc, ← mul_assoc, mul_comm ((Nat.card G : ℂ)⁻¹) ((Nat.card H : ℂ)⁻¹)]
      rw [mul_assoc ((Nat.card H : ℂ)⁻¹) ((Nat.card G : ℂ)⁻¹) (Nat.card G : ℂ),
        inv_mul_cancel₀ hG, mul_one]]

end Work.Frobenius.Induction
