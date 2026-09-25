import Mathlib
import Submission.Work.CFT.KochTransfer.Defs

namespace Work.CFT.KochTransfer

/-- The space `Work.CFT.KochTransfer.invariantHoms p π` of additive maps `ker π → 𝔽_p`
which are invariant under conjugation by `G` has `𝔽_p`-dimension at most `k` as soon as
`ker π` is the normal closure of the `k` elements `g i`. -/
theorem finrank_invariantHoms_le {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    (π : G →* Q) (k : ℕ) (g : Fin k → G)
    (hg : π.ker = Subgroup.normalClosure (Set.range g)) :
    Module.finrank (ZMod p) ↥(Work.CFT.KochTransfer.invariantHoms p π) ≤ k := by
  have hgmem : ∀ i, g i ∈ π.ker := fun i => by
    rw [hg]
    exact Subgroup.subset_normalClosure ⟨i, rfl⟩
  -- Evaluation of an invariant hom at the generators.
  let f : ↥(invariantHoms p π) → (Fin k → ZMod p) := fun t i => t ⟨g i, hgmem i⟩
  let ev : invariantHoms p π →ₗ[ZMod p] (Fin k → ZMod p) :=
    { toFun := f
      map_add' := fun a b => by funext i; rfl
      map_smul' := fun c a => by funext i; rfl }
  -- An invariant hom vanishing on all generators vanishes identically: the elements of
  -- `↥π.ker` on which `t` vanishes form a `G`-stable subgroup, hence contain the normal
  -- closure of the generators, which is all of `π.ker`.
  have hzero : ∀ t : invariantHoms p π, (∀ i, t ⟨g i, hgmem i⟩ = 0) → t = 0 := by
    intro t ht
    refine Subtype.ext (funext fun x => ?_)
    have key : t x = 0 := by
      let K : Subgroup ↥π.ker :=
        { carrier := {y | t y = 0}
          one_mem' := invariantHoms_one p π t
          mul_mem' := by
            intro a b ha hb
            change t a = 0 at ha
            change t b = 0 at hb
            change t (a * b) = 0
            rw [invariantHoms_add p π t a b, ha, hb, add_zero]
          inv_mem' := by
            intro a ha
            change t a = 0 at ha
            change t a⁻¹ = 0
            have h : t a + t a⁻¹ = 0 := by
              have h1 : t (a * a⁻¹) = t a + t a⁻¹ := invariantHoms_add p π t a a⁻¹
              rw [mul_inv_cancel, invariantHoms_one p π t] at h1
              exact h1.symm
            rw [ha, zero_add] at h
            exact h }
      have hnc_le : Subgroup.normalClosure (Set.range g) ≤ K.map π.ker.subtype := by
        have h_eq : Subgroup.normalClosure (Set.range g) =
            Subgroup.closure (Group.conjugatesOfSet (Set.range g)) := rfl
        rw [h_eq, Subgroup.closure_le]
        rintro z hz
        obtain ⟨a, ⟨i, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
        rw [isConj_iff] at hconj
        obtain ⟨c, rfl⟩ := hconj
        exact Subgroup.mem_map.mpr ⟨conjKer π c ⟨g i, hgmem i⟩, by
          show t (conjKer π c ⟨g i, hgmem i⟩) = 0
          rw [invariantHoms_conj p π t c ⟨g i, hgmem i⟩]
          exact ht i, rfl⟩
      have hle : π.ker ≤ K.map π.ker.subtype := by
        conv_lhs => rw [hg]
        exact hnc_le
      have hx : (x : G) ∈ K.map π.ker.subtype := hle x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    simpa using key
  have hinj : Function.Injective ev := by
    intro a b hab
    have hsub0 : ev (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hsub : a - b = 0 := hzero (a - b) (fun i => congr_fun hsub0 i)
    exact sub_eq_zero.mp hsub
  calc Module.finrank (ZMod p) ↥(invariantHoms p π)
      = Module.finrank (ZMod p) ↥(LinearMap.range ev) :=
        (LinearEquiv.ofInjective ev hinj).finrank_eq
    _ ≤ Module.finrank (ZMod p) (Fin k → ZMod p) := Submodule.finrank_le _
    _ = k := by rw [Module.finrank_pi, Fintype.card_fin]

end Work.CFT.KochTransfer
