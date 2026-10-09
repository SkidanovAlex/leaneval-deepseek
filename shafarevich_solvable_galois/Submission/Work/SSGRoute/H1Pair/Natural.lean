/-
# Naturality of the canonical Tate pairing `H₁(G, M) × H¹(G, M^∨) → k`

`Work.SSGRoute.H1Pair.tatePairLin` is the explicit pairing of the bar complex, with computation
rule `tatePairLin M (H1π c) (H1π θ) = ∑_g θ g (c g)` (`tatePairLin_apply_mk`).  As an explicit
formula on the inhomogeneous chains and cochains it is natural in `(G, M)`: for a group
homomorphism `φ : G₁ →* G₂` and an equivariant `F : M₁ ⟶ Rep.res φ M₂` with transpose
`F' : Rep.res φ (M₂^∨) ⟶ M₁^∨`,

`⟨map φ F 1 x, y⟩₂ = ⟨x, map φ F' 1 y⟩₁`.

The naturality of `groupHomology.map` and `groupCohomology.map` on representatives
(`groupHomology.H1π_comp_map_apply`, `groupHomology.coe_mapCycles₁`,
`groupCohomology.H1π_comp_map_apply`, `groupCohomology.coe_mapCocycles₁`) reduces this to the
identity `∑_g θ (φ g) (F (c g)) = ∑_g (F' (θ (φ g))) (c g)`, which is the transpose property of
`F'`.
-/
import Submission.Work.SSGRoute.H1Pair.Pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute.H1Pair

universe u

variable {k : Type u} [CommRing k]

/-! ## Computation of `chainsMap₁` and `cochainsMap₁` -/

/-- The degree-`1` chain map of `groupHomology.chainsMap`, explicitly: it sends
`∑ aᵢ·gᵢ` to `∑ (F aᵢ)·(φ gᵢ)`. -/
theorem chainsMap₁_apply {G₁ G₂ : Type u} [Group G₁] [Group G₂] {M₁ : Rep k G₁}
    {M₂ : Rep k G₂} (φ : G₁ →* G₂) (F : M₁ ⟶ Rep.res φ M₂) (x : G₁ →₀ M₁) :
    ModuleCat.Hom.hom (groupHomology.chainsMap₁ φ F) x
      = (Finsupp.mapDomain φ x).mapRange (Rep.Hom.hom F) (map_zero _) := by
  rw [groupHomology.chainsMap₁]
  rfl

/-- The pairing of the chain `chainsMap₁ φ F x` with a cochain `θ` of `M₂`:
`∑_g θ (φ g) (F (x g))`. -/
theorem pairFun_chainsMap₁ {G₁ G₂ : Type u} [Group G₁] [Group G₂] {M₁ : Rep k G₁}
    {M₂ : Rep k G₂} (φ : G₁ →* G₂) (F : M₁ ⟶ Rep.res φ M₂) (x : G₁ →₀ M₁)
    (θ : G₂ → Module.Dual k M₂) :
    pairFun (ModuleCat.Hom.hom (groupHomology.chainsMap₁ φ F) x) θ
      = x.sum (fun g a => θ (φ g) (Rep.Hom.hom F a)) := by
  rw [chainsMap₁_apply]
  show ((Finsupp.mapDomain φ x).mapRange (Rep.Hom.hom F) (map_zero _)).sum
      (fun i a => θ i a) = _
  rw [Finsupp.sum_mapRange_index (fun a => map_zero (θ a))]
  exact Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp)

/-- The degree-`1` cochain map, explicitly: it sends `θ` to `g ↦ F' (θ (φ g))`. -/
theorem cochainsMap₁_apply {G₁ G₂ : Type u} [Group G₁] [Group G₂] {M₁ : Rep k G₁}
    {M₂ : Rep k G₂} (φ : G₁ →* G₂) (F' : Rep.res φ (contra M₂) ⟶ contra M₁)
    (θ : G₂ → (contra M₂).V) :
    ModuleCat.Hom.hom (groupCohomology.cochainsMap₁ φ F') θ
      = fun g : G₁ => Rep.Hom.hom F' (θ (φ g)) := rfl

/-- The pairing of a chain `c` of `M₁` with the cochain `cochainsMap₁ φ F' θ`:
`∑_g F' (θ (φ g)) (c g)`. -/
theorem pairFun_cochainsMap₁ {G₁ G₂ : Type u} [Group G₁] [Group G₂] {M₁ : Rep k G₁}
    {M₂ : Rep k G₂} (φ : G₁ →* G₂) (F' : Rep.res φ (contra M₂) ⟶ contra M₁)
    (c : G₁ →₀ M₁) (θ : G₂ → (contra M₂).V) :
    pairFun c (ModuleCat.Hom.hom (groupCohomology.cochainsMap₁ φ F') θ)
      = c.sum (fun g a => (Rep.Hom.hom F' (θ (φ g))) a) := by
  rw [cochainsMap₁_apply]
  rfl

/-! ## Naturality -/

/-- **Naturality of the canonical Tate pairing `tatePairLin` in `(G, M)`**, pointwise form: for a
group homomorphism `φ : G₁ →* G₂`, an equivariant `F : M₁ ⟶ Rep.res φ M₂` and its transpose
`F' : Rep.res φ (M₂^∨) ⟶ M₁^∨` (i.e. `F' ψ v = ψ (F v)`), the pairing of the pushed-forward class
`groupHomology.map φ F 1 x` with `y` equals the pairing of `x` with `groupCohomology.map φ F' 1 y`.

Both sides are the evaluation `∑_g θ (φ g) (F c_g)` for representatives `x = H1π c`,
`y = H1π θ`; the proof is the chain-level computation together with the transpose property of
`F'`. -/
theorem tatePairLin_natural {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    (φ : G₁ →* G₂) (M₁ : Rep k G₁) (M₂ : Rep k G₂) (F : M₁ ⟶ Rep.res φ M₂)
    (F' : Rep.res φ (contra M₂) ⟶ contra M₁)
    (hF' : ∀ (ψ : (contra M₂).V) (v : M₁.V), F'.hom ψ v = ψ (F.hom v))
    (x : groupHomology.H1 M₁) (y : groupCohomology.H1 (contra M₂)) :
    tatePairLin M₂ ((groupHomology.map φ F 1).hom x) y
      = tatePairLin M₁ x ((groupCohomology.map φ F' 1).hom y) := by
  revert y
  refine groupHomology.H1_induction_on x fun c => ?_
  intro y
  refine groupCohomology.H1_induction_on y fun θ => ?_
  rw [groupHomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply,
    tatePairLin_apply_mk, tatePairLin_apply_mk, groupHomology.coe_mapCycles₁]
  show pairFun (ModuleCat.Hom.hom (groupHomology.chainsMap₁ φ F) c.1) θ.1
      = pairFun c.1 (ModuleCat.Hom.hom (groupCohomology.cochainsMap₁ φ F') θ.1)
  rw [pairFun_chainsMap₁, pairFun_cochainsMap₁]
  refine Finsupp.sum_congr fun g _ => ?_
  exact (hF' (θ.1 (φ g)) (c.1 g)).symm

end Work.SSGRoute.H1Pair
