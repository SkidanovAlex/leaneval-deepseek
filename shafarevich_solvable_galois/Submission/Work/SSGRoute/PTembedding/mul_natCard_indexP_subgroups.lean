import Mathlib
import Submission.Work.SSGRoute.PTembedding.natCard_dual_eq_natCard
import Submission.Work.SSGRoute.PTembedding.submodule_index_p_equiv_projectivization
import Submission.Work.SSGRoute.PTembedding.subgroup_index_p_equiv_addSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Counting the subgroups of index `p` in a commutative group

For a commutative group `G` and a prime `p`, the subgroups of index `p` are exactly the
index-`p` subgroups of the elementary abelian `p`-group `G ⧸ G ^ p` (every index-`p` subgroup
contains the `p`-th powers).  Any such subgroup is the kernel of a nonzero linear functional
on `G ⧸ G ^ p` viewed as a vector space over `𝔽_p`, and two nonzero functionals have the same
kernel iff they differ by a nonzero scalar.  Hence

`(p - 1) * #{M ≤ G : [G : M] = p} = #{G ⧸ G ^ p} - 1`,

where `Nat.card` returns `0` for infinite types (in which case both sides vanish).

The three ingredients are proved in separate files and imported here:

* `natCard_dual_eq_natCard` : `|V*| = |V|` for a `ZMod p`-module `V`;
* `submodule_index_p_equiv_projectivization` : index-`p` submodules of `V` correspond to the
  points of the projectivization of the dual `V*`;
* `subgroup_index_p_equiv_addSubgroup` : the index-`p` subgroups of `G` correspond to the
  index-`p` additive subgroups of `Additive (G ⧸ G ^ p)`.

The cardinality of a projectivization is computed by Mathlib's `Projectivization.card`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTembedding

/-- The core counting identity: the index-`p` subgroups of a commutative group `G` are in
bijection with the points of the projectivization of the `𝔽_p`-dual of `G ⧸ G ^ p`, whose
cardinality is `(|G ⧸ G ^ p| - 1) / (p - 1)` by `Projectivization.card`. -/
theorem mul_natCard_indexP_subgroups (p : ℕ) [Fact p.Prime] (G : Type) [CommGroup G] :
    (p - 1) * Nat.card {M : Subgroup G // M.index = p}
      = Nat.card (G ⧸ (powMonoidHom p : G →* G).range) - 1 := by
  set N : Subgroup G := (powMonoidHom p : G →* G).range with hN
  -- every element of the quotient `G ⧸ G ^ p` has `p`-th power `1`
  have hexp : ∀ q : G ⧸ N, q ^ p = 1 := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨g, (powMonoidHom_apply p g).symm⟩
  -- hence `Additive (G ⧸ G ^ p)` is a module over `𝔽_p = ZMod p`
  have hm0 : Module (ZMod p) (Additive (G ⧸ N)) :=
    AddCommGroup.zmodModule (fun x => by
      exact Additive.toMul.injective (by rw [toMul_nsmul]; simp [hexp]))
  letI := hm0
  -- the three structural equivalences
  have e1 : {M : Subgroup G // M.index = p} ≃
      {K : AddSubgroup (Additive (G ⧸ N)) // K.index = p} :=
    Classical.choice (subgroup_index_p_equiv_addSubgroup p G)
  have e2 : {K : AddSubgroup (Additive (G ⧸ N)) // K.index = p} ≃
      {K : Submodule (ZMod p) (Additive (G ⧸ N)) // K.toAddSubgroup.index = p} :=
    { toFun := fun K => ⟨AddSubgroup.toZModSubmodule p K.1, by
        rw [AddSubgroup.toZModSubmodule_toAddSubgroup]; exact K.2⟩
      invFun := fun K => ⟨K.1.toAddSubgroup, K.2⟩
      left_inv := fun K => Subtype.ext
        (AddSubgroup.toZModSubmodule_toAddSubgroup p K.1)
      right_inv := fun K => Subtype.ext
        (Submodule.toAddSubgroup_toZModSubmodule p K.1) }
  have e3 : {K : Submodule (ZMod p) (Additive (G ⧸ N)) // K.toAddSubgroup.index = p} ≃
      Projectivization (ZMod p) (Module.Dual (ZMod p) (Additive (G ⧸ N))) :=
    Classical.choice (submodule_index_p_equiv_projectivization p (Additive (G ⧸ N)))
  have hNA : Nat.card {M : Subgroup G // M.index = p}
      = Nat.card (Projectivization (ZMod p) (Module.Dual (ZMod p) (Additive (G ⧸ N)))) :=
    Nat.card_congr (e1.trans (e2.trans e3))
  have hMD : Nat.card (Module.Dual (ZMod p) (Additive (G ⧸ N))) = Nat.card (G ⧸ N) :=
    natCard_dual_eq_natCard p (Additive (G ⧸ N))
  have hzk : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  calc (p - 1) * Nat.card {M : Subgroup G // M.index = p}
      = Nat.card {M : Subgroup G // M.index = p} * (p - 1) := Nat.mul_comm _ _
    _ = Nat.card (Projectivization (ZMod p) (Module.Dual (ZMod p) (Additive (G ⧸ N))))
          * (p - 1) := by rw [hNA]
    _ = Nat.card (Projectivization (ZMod p) (Module.Dual (ZMod p) (Additive (G ⧸ N))))
          * (Nat.card (ZMod p) - 1) := by rw [hzk]
    _ = Nat.card (Module.Dual (ZMod p) (Additive (G ⧸ N))) - 1 :=
          (Projectivization.card (ZMod p) (Module.Dual (ZMod p) (Additive (G ⧸ N)))).symm
    _ = Nat.card (G ⧸ N) - 1 := by rw [hMD]
    _ = Nat.card (G ⧸ (powMonoidHom p : G →* G).range) - 1 := by rw [← hN]

end Work.SSGRoute.PTembedding
