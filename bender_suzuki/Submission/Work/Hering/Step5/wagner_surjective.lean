import Mathlib
import Submission.Work.Hering.Wagner.Defs
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Basic
import Submission.Work.Hering.Step6.actsAsAut
import Submission.Work.Hering.Step5.exists_normalizerMonoidHom_eq_of_conj
import Submission.Work.Hering.Step5.conjNormal_range_doubleTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wagner's proposition applied to a subgroup `U ≤ V = Inv(G) ∪ {1}` of order `8`

Peterfalvi I §1, p. 188 (after A. Wagner).  Let `G` be a finite group of 2-rank `≥ 2` acting
doubly transitively by conjugation on its involutions (`DTInv G`, `HasFourGroup G`) and let
`V = Inv(G) ∪ {1} = invSubgroup hDT h4`, an elementary abelian normal subgroup of `G`
(`Work.Hering.invSubgroup_comm`, `Work.Hering.pow_two_eq_one_of_mem_invSubgroup`,
`Work.Hering.invSubgroup_normal`).  For every subgroup `U ≤ V` with `Nat.card U = 8`, the
conjugation action of the normalizer `N_G(U)` realises every automorphism of `U`:

`Subgroup.normalizerMonoidHom U : N_G(U) →* MulAut U` is surjective.

This is exactly **Wagner's proposition** (`Work.Hering.WagnerProp`) applied to the conjugation
action of `G` on `V`: `V` is a finite abelian group of exponent `2`, its nonidentity elements are
its involutions, so `Gm = (MulAut.conjNormal).range ≤ MulAut V` is doubly transitive on `V \ {1}`
by `hDT`, and `U` is a subgroup of order `8`.  Wagner then produces `g ∈ Gm` inducing any given
automorphism `φ` of `U`; lifting `g` to `g₀ ∈ G` (the range of `MulAut.conjNormal`) the element
`g₀` normalizes `U` and induces `φ`, i.e. `φ` lies in the image of `normalizerMonoidHom U`.

Because `WagnerProp` is universe polymorphic while `V` lives in the universe of `G`, the
hypothesis is first transported to that universe with `Work.Hering.Step6.wagnerProp_univ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.Step5

/-- The value of `Subgroup.normalizerMonoidHom U` on `g : N_G(U)` is conjugation by `g`. -/
theorem normalizerMonoidHom_apply_coe {G : Type*} [Group G] (U : Subgroup G)
    (g : Subgroup.normalizer (U : Set G)) (u : U) :
    ((Subgroup.normalizerMonoidHom U g) u : G) = (g : G) * (u : G) * (g : G)⁻¹ := by
  simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
    MulDistribMulAction.toMulEquiv_apply]
  rfl

theorem wagner_surjective {G : Type*} [Group G] [Finite G] {hDT : DTInv G} {h4 : HasFourGroup G}
    (hWagner : WagnerProp) {U : Subgroup G} (hU : U ≤ invSubgroup hDT h4) (hUcard : Nat.card U = 8) :
    Function.Surjective (Subgroup.normalizerMonoidHom U) := by
  classical
  set V : Subgroup G := invSubgroup hDT h4 with hV
  haveI hVn : V.Normal := by rw [hV]; exact invSubgroup_normal hDT h4
  have hUV : U ≤ V := by intro x hx; rw [hV]; exact hU hx
  -- `V` is an elementary abelian `2`-group
  have hmemV : ∀ x : ↥V, (x : G) ∈ invSubgroup hDT h4 := fun x => by simpa [hV] using x.2
  have habel : ∀ x y : ↥V, x * y = y * x := fun x y =>
    Subtype.ext (invSubgroup_comm hDT h4 (hmemV x) (hmemV y))
  have hexp : ∀ x : ↥V, x * x = 1 := fun x =>
    Subtype.ext (by simpa using pow_two_eq_one_of_mem_invSubgroup hDT h4 (hmemV x))
  -- the image of the conjugation action of `G` on `V` inside `MulAut V`
  let Gm : Subgroup (MulAut ↥V) := (MulAut.conjNormal (H := V)).range
  -- `Gm` is doubly transitive on `V \ {1}`, by `DTInv G` (piece delegated to
  -- `Work.Hering.Step5.conjNormal_range_doubleTransitive`)
  have h2 : ∀ a b c d : ↥V, a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → c ≠ d →
      ∃ g ∈ Gm, g a = c ∧ g b = d :=
    conjNormal_range_doubleTransitive (hDT := hDT) (h4 := h4)
  intro φ
  let U' : Subgroup ↥V := U.subgroupOf V
  let e : U' ≃* U := Subgroup.subgroupOfEquivOfLe hUV
  have hU'card : Nat.card U' = 8 := by rw [Nat.card_congr e.toEquiv, hUcard]
  let φ' : MulAut U' := e.trans (φ.trans e.symm)
  obtain ⟨g, hg, hgprop⟩ :=
    (Work.Hering.Step6.wagnerProp_univ hWagner) habel hexp Gm h2 U' hU'card φ'
  obtain ⟨g0, hg0⟩ := MonoidHom.mem_range.mp
    (show g ∈ (MulAut.conjNormal (H := V)).range from hg)
  -- `g₀` conjugates every element of `U` to `φ` applied to it
  have hconj : ∀ u : U, g0 * (u : G) * g0⁻¹ = (φ u : G) := by
    intro u
    have h1 := hgprop (e.symm u)
    rw [← hg0] at h1
    have h2 := congrArg (fun x : ↥V => (x : G)) h1
    rw [MulAut.conjNormal_apply] at h2
    have hφ'e : φ' (e.symm u) = e.symm (φ u) := by
      simp only [φ', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [hφ'e] at h2
    exact h2
  -- hence `φ` is in the image of `normalizerMonoidHom U` (piece delegated to
  -- `Work.Hering.Step5.exists_normalizerMonoidHom_eq_of_conj`)
  exact exists_normalizerMonoidHom_eq_of_conj hconj

end Work.Hering.Step5
