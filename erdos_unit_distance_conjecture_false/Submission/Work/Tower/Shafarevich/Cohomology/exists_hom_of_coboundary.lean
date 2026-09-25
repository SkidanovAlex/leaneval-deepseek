import Mathlib
import Submission.Work.Tower.Shafarevich.Cohomology.TwistedExt

namespace Work.Tower.Shafarevich.Cohomology

theorem exists_hom_of_coboundary {p : ℕ} {G : Type*} [Group G] {d : ℕ} (κ : G × G → ZMod p)
    (hκ1 : κ (1, 1) = 0) (b : G → ZMod p) (hb : ∀ g h : G, κ (g, h) = b h - b (g * h) + b g)
    (φ : FreeGroup (Fin d) →* G) (τ : FreeGroup (Fin d) → ZMod p) (hτ1 : τ 1 = 0)
    (hτmul : ∀ u v, τ (u * v) = τ u + τ v + κ (φ u, φ v)) :
    ∃ δ : Additive (FreeGroup (Fin d)) →+ ZMod p,
      ∀ w : FreeGroup (Fin d), φ w = 1 → τ w = δ (Additive.ofMul w) := by
  -- `κ` being the coboundary of `b` forces `b 1 = 0` via `κ (1,1) = 0`.
  have hb1 : b 1 = 0 := by
    have h := hb 1 1
    rw [hκ1, mul_one, sub_self, zero_add] at h
    exact h.symm
  -- Correcting `τ` by the coboundary of `b ∘ φ` kills the `κ`-term: `w ↦ τ w + b (φ w)` is
  -- a genuine homomorphism `(FreeGroup (Fin d), *) → (ZMod p, +)`.
  have key : ∀ u v : FreeGroup (Fin d),
      τ (u * v) + b (φ (u * v)) = (τ u + b (φ u)) + (τ v + b (φ v)) := by
    intro u v
    rw [hτmul u v, map_mul φ u v, hb (φ u) (φ v)]
    abel
  refine ⟨{ toFun := fun x : Additive (FreeGroup (Fin d)) => τ x.toMul + b (φ x.toMul)
            map_zero' := by
              show τ 1 + b (φ 1) = 0
              simp [hτ1, map_one, hb1]
            map_add' := by
              intro x y
              exact key x.toMul y.toMul }, ?_⟩
  -- On `ker φ` the correction vanishes because `b 1 = 0`.
  intro w hw
  show τ w = τ w + b (φ w)
  rw [hw, hb1, add_zero]

end Work.Tower.Shafarevich.Cohomology
