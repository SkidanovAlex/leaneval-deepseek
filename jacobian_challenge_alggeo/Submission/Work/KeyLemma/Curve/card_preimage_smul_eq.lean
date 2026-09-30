import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.KeyLemma.Curve

/-- Counting the elements of a group acting on a set that land in a subset of the orbit:
if every element of `S` lies in the orbit of `P`, then the preimage of `S` under
`g ↦ g • P` has cardinality `|S| * |Stab P|`. -/
theorem card_preimage_smul_eq {G β : Type*} [Group G] [MulAction G β] [Finite G] [Finite β]
    (P : β) (S : Set β) (hS : ∀ Q ∈ S, Q ∈ MulAction.orbit G P) :
    Nat.card ((fun g : G => g • P) ⁻¹' S)
      = Nat.card S * Nat.card (MulAction.stabilizer G P) := by
  classical
  -- The stabilizer of `P`, and a choice of group element sending `P` to each point of `S`.
  let H : Subgroup G := MulAction.stabilizer G P
  let gch : S → G := fun Q => Classical.choose (MulAction.mem_orbit_iff.mp (hS Q.1 Q.2))
  have hgch : ∀ Q : S, gch Q • P = Q.1 :=
    fun Q => Classical.choose_spec (MulAction.mem_orbit_iff.mp (hS Q.1 Q.2))
  -- The bijection `S × Stab P ≃ g ↦ g • P ⁻¹' S`, `(Q, h) ↦ gch Q * h`.
  let F : S × H → ↥((fun g : G => g • P) ⁻¹' S) := fun x =>
    ⟨gch x.1 * x.2.1, by
      show (gch x.1 * x.2.1) • P ∈ S
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp x.2.2, hgch x.1]
      exact x.1.2⟩
  have hF : Function.Bijective F := by
    constructor
    · -- Injectivity.
      intro x y hxy
      have h1 : gch x.1 * x.2.1 = gch y.1 * y.2.1 := congrArg Subtype.val hxy
      have h2 : x.1.1 = y.1.1 := by
        have hh := congrArg (fun g : G => g • P) h1
        rwa [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp x.2.2,
             MulAction.mem_stabilizer_iff.mp y.2.2, hgch x.1, hgch y.1] at hh
      have hx1 : x.1 = y.1 := Subtype.ext h2
      have h3 : x.2.1 = y.2.1 := by
        rw [hx1] at h1
        exact mul_left_cancel h1
      exact Prod.ext hx1 (Subtype.ext h3)
    · -- Surjectivity.
      intro z
      let Q : S := ⟨z.1 • P, z.2⟩
      have hQ : gch Q • P = z.1 • P := hgch Q
      refine ⟨(Q, ⟨(gch Q)⁻¹ * z.1, ?_⟩), ?_⟩
      · show ((gch Q)⁻¹ * z.1) • P = P
        rw [mul_smul, ← hQ, inv_smul_smul]
      · apply Subtype.ext
        show gch Q * ((gch Q)⁻¹ * z.1) = z.1
        rw [mul_inv_cancel_left]
  let e : S × H ≃ ↥((fun g : G => g • P) ⁻¹' S) := Equiv.ofBijective F hF
  rw [← Nat.card_congr e, Nat.card_prod]

end Work.KeyLemma.Curve
