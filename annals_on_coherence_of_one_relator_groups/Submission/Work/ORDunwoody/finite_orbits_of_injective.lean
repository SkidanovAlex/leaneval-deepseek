import Mathlib
import Submission.Work.ORDunwoody.finite_orbits_track

namespace Work.ORDunwoody

universe u

/-- **Finiteness of the orbit quotient descends along an injective equivariant map.**  If `G` acts
on `X` and `Y`, if the orbit quotient of `X` is finite and if `f : Y → X` is injective and
`G`-equivariant, then the orbit quotient of `Y` is finite: `f` descends to an injection of the
orbit quotients, since two elements of `Y` lie in the same orbit exactly when their images do. -/
theorem finite_orbits_of_injective {G : Type u} [Group G] {X Y : Type u} [MulAction G X]
    [MulAction G Y] (hX : Finite (MulAction.orbitRel.Quotient G X)) (f : Y → X)
    (hf : Function.Injective f) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    Finite (MulAction.orbitRel.Quotient G Y) := by
  classical
  -- The relation is preserved: two elements of one orbit of `Y` map into one orbit of `X`.
  have hmap : ∀ a b : Y, (MulAction.orbitRel G Y) a b →
      (MulAction.orbitRel G X) (f a) (f b) := by
    intro a b hab
    rw [MulAction.orbitRel_apply] at hab ⊢
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨g, by rw [← heq g b, hg]⟩
  -- Conversely, because `f` is injective, elements with equivalent images are equivalent.
  have hinj : Function.Injective
      (Quotient.map (sa := MulAction.orbitRel G Y) (sb := MulAction.orbitRel G X) f hmap) := by
    intro q₁ q₂ h
    revert h q₂
    refine Quotient.inductionOn q₁ (fun a => ?_)
    intro q₂
    refine Quotient.inductionOn q₂ (fun b => ?_)
    intro h
    rw [Quotient.map_mk, Quotient.map_mk] at h
    rw [Quotient.eq]
    rw [MulAction.orbitRel_apply]
    rw [Quotient.eq] at h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨g, hf (by rw [heq g b, hg])⟩
  exact Finite.of_injective _ hinj

end Work.ORDunwoody
