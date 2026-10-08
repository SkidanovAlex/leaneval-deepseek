/-
# AREA COPR — the fibres of Bender's map `phi` are cosets of `C_X(s)`

Bender's map `phi u = u⁻¹ * u^s` on `X` (see `Submission.Work.COPR.BenderDefs`) satisfies
`phi u = phi v` iff `v * u⁻¹` centralizes `s`.  Consequently every fibre of `phi` is in
bijection with `X ⊓ C_G(s)`: the fibre of `phi x₀` is sent to `X ⊓ C_G(s)` by
`u ↦ x₀ * u⁻¹`, whose inverse is `c ↦ c⁻¹ * x₀`.

This is the counting input used when `X` has odd order: then `X ⊓ C_G(s)` has odd order
as well, so no fibre of `phi` is trivial.
-/
import Mathlib
import Submission.Work.COPR.BenderDefs

namespace Work.COPR

open Subgroup

/-- Elementary group identity behind the fibre computation: the equality
`a⁻¹ * (s * a * s⁻¹) = b⁻¹ * (s * b * s⁻¹)` is equivalent to `b * a⁻¹` centralizing `s`. -/
lemma inv_conj_mul_eq_iff {G : Type} [Group G] (s a b : G) :
    a⁻¹ * (s * a * s⁻¹) = b⁻¹ * (s * b * s⁻¹) ↔ b * a⁻¹ * s = s * (b * a⁻¹) := by
  constructor
  · intro h
    have h3 : a⁻¹ * s * a = b⁻¹ * s * b := by
      have h2 : a⁻¹ * s * a * s⁻¹ = b⁻¹ * s * b * s⁻¹ := by
        rw [show a⁻¹ * s * a * s⁻¹ = a⁻¹ * (s * a * s⁻¹) from by group,
            show b⁻¹ * s * b * s⁻¹ = b⁻¹ * (s * b * s⁻¹) from by group]
        exact h
      exact mul_right_cancel h2
    calc b * a⁻¹ * s = b * (a⁻¹ * s * a) * b⁻¹ * (b * a⁻¹) := by group
      _ = b * (b⁻¹ * s * b) * b⁻¹ * (b * a⁻¹) := by rw [h3]
      _ = s * (b * a⁻¹) := by group
  · intro h
    have h3 : a⁻¹ * s * a = b⁻¹ * s * b := by
      have h1 : b⁻¹ * (b * a⁻¹ * s) * a = b⁻¹ * (s * (b * a⁻¹)) * a :=
        congrArg (fun t => b⁻¹ * t * a) h
      rw [show b⁻¹ * (b * a⁻¹ * s) * a = a⁻¹ * s * a from by group,
          show b⁻¹ * (s * (b * a⁻¹)) * a = b⁻¹ * s * b from by group] at h1
      exact h1
    rw [show a⁻¹ * (s * a * s⁻¹) = a⁻¹ * s * a * s⁻¹ from by group,
        show b⁻¹ * (s * b * s⁻¹) = b⁻¹ * s * b * s⁻¹ from by group]
    exact congrArg (· * s⁻¹) h3

/-- `phi u = phi v` exactly when `v * u⁻¹` centralizes `s`. -/
lemma phi_eq_iff {G : Type} [Group G] (X : Subgroup G) (s : G)
    (hN : s ∈ Subgroup.normalizer (X : Set G)) (u v : X) :
    phi X s hN u = phi X s hN v ↔ (v : G) * (u : G)⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
  have hraw : phi X s hN u = phi X s hN v ↔
      (u : G)⁻¹ * (s * (u : G) * s⁻¹) = (v : G)⁻¹ * (s * (v : G) * s⁻¹) := by
    constructor
    · intro h
      have := congrArg (Subtype.val) h
      simpa [phi_coe] using this
    · intro h
      ext
      simpa [phi_coe] using h
  rw [hraw, inv_conj_mul_eq_iff s (u : G) (v : G), Subgroup.mem_centralizer_singleton_iff]

theorem fiber_phi_card {G : Type} [Group G] [Finite G] (X : Subgroup G) (s : G)
    (hN : s ∈ Subgroup.normalizer (X : Set G)) (x₀ : X) :
    Nat.card {u : X | Work.COPR.phi X s hN u = Work.COPR.phi X s hN x₀} =
      Nat.card (X ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
  let C : Subgroup G := X ⊓ Subgroup.centralizer ({s} : Set G)
  let f : {u : X // phi X s hN u = phi X s hN x₀} → C := fun u =>
    ⟨(x₀ : G) * (u.1 : G)⁻¹, by
      rw [Subgroup.mem_inf]
      exact ⟨X.mul_mem x₀.2 (X.inv_mem u.1.2), (phi_eq_iff X s hN u.1 x₀).mp u.2⟩⟩
  let g : C → {u : X // phi X s hN u = phi X s hN x₀} := fun c =>
    ⟨⟨(c.1 : G)⁻¹ * (x₀ : G), X.mul_mem (X.inv_mem (Subgroup.mem_inf.mp c.2).1) x₀.2⟩, by
      rw [phi_eq_iff X s hN _ x₀]
      show (x₀ : G) * ((c.1 : G)⁻¹ * (x₀ : G))⁻¹ ∈ Subgroup.centralizer ({s} : Set G)
      have hc : (c.1 : G) ∈ Subgroup.centralizer ({s} : Set G) := (Subgroup.mem_inf.mp c.2).2
      convert hc using 1
      group⟩
  refine Nat.card_congr ⟨f, g, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    apply Subtype.ext
    show ((x₀ : G) * ((u.1 : G))⁻¹)⁻¹ * (x₀ : G) = (u.1 : G)
    group
  · intro c
    apply Subtype.ext
    show (x₀ : G) * (((c.1 : G)⁻¹ * (x₀ : G)))⁻¹ = (c.1 : G)
    group

end Work.COPR
