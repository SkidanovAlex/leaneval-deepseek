import Mathlib
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embeddedness passes to the image under a surjection with central odd kernel

Let `φ : F →* Y` be a surjective homomorphism of finite groups whose kernel has odd order and is
contained in the centre of `F`, and let `K ≤ F` be strongly embedded.  Then `K.map φ` is strongly
embedded in `Y`.

The point is that the extra hypothesis `φ.ker ≤ Z(F)` already forces `φ.ker ≤ K`: the centre of a
finite group lies in every strongly embedded subgroup, since a central element `z ∉ K` would give
`K ⊓ K^z = K` of *odd* order (strong embeddedness), while `|K|` is even.  With `φ.ker ≤ K` the
result is exactly `Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd`.
-/

namespace Work.NormalComplement

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ K` would give `K ⊓ K^z = K` of odd order, contradicting `|K|` even. -/
private theorem center_le_of_isStronglyEmbedded {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) : Subgroup.center G ≤ K := by
  intro z hz
  by_contra hzK
  have hodd := hK.2.2 z hzK
  have hle : K ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) K := by
    intro x hx
    refine ⟨z⁻¹ * x * z, ?_, ?_⟩
    · have hcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hz) x
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hzx]; exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconj : K ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) K = K :=
    inf_eq_left.mpr hle
  rw [hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hK.2.1

theorem isStronglyEmbedded_map_of_central_odd_ker {F Y : Type} [Group F] [Finite F] [Group Y]
    (φ : F →* Y) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card ↥φ.ker))
    (hcent : φ.ker ≤ Subgroup.center F) {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Subgroup.map φ K) :=
  Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφ hodd
    (hcent.trans (center_le_of_isStronglyEmbedded hK)) hK

end Work.NormalComplement
