import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `Δ`-chain groups and the boundary maps

For a finite `Δ`-complex `K` (`Work.DeltaHomology.DeltaCx`) the `k`-th chain
group is the free `ℤ`-module

`C_k^Δ(K; ℤ) = ∐_{σ : Fin (K.card k)} ℤ`,

with basis elements `chainι K k σ` and boundary `chainD K k = ∑_i (-1)^i d_i`,
the alternating sum of the face maps.

This file contains the *definitions* and the immediately available API
(the boundary on a basis element, `ι_chainD`).  The chain complex itself,
which needs `chainD (n+1) ≫ chainD n = 0`, is assembled in
`Submission/Work/DeltaHomology/Chain.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

/-- The `k`-th `Δ`-chain group `C_k^Δ(K; ℤ)`: the free `ℤ`-module on the
`k`-simplices of `K`.  (An `abbrev` so that it unfolds definitionally to the
coproduct `∐ (fun _ : Fin (K.card k) => ℤ)`.) -/
abbrev DeltaCx.chainX (K : DeltaCx) (k : ℕ) : ModuleCat ℤ :=
  ∐ (fun _ : Fin (K.card k) => Work.Homology.ZMod)

/-- The `k`-simplex `σ` as a basis element `ℤ ⟶ C_k^Δ(K; ℤ)`. -/
abbrev DeltaCx.chainι (K : DeltaCx) (k : ℕ) (σ : Fin (K.card k)) :
    Work.Homology.ZMod ⟶ K.chainX k :=
  Sigma.ι (fun _ : Fin (K.card k) => Work.Homology.ZMod) σ

/-- The `i`-th face map `C_{k+1}^Δ(K) ⟶ C_k^Δ(K)`, induced by `σ ↦ face σ i`. -/
def DeltaCx.faceMap (K : DeltaCx) {k : ℕ} (i : Fin (k + 2)) :
    K.chainX (k + 1) ⟶ K.chainX k :=
  Sigma.desc (fun σ : Fin (K.card (k + 1)) => K.chainι k (K.face σ i))

/-- The boundary `∂_k : C_k^Δ(K) ⟶ C_{k-1}^Δ(K)`, the alternating sum of the
face maps. -/
def DeltaCx.chainD (K : DeltaCx) (k : ℕ) : K.chainX (k + 1) ⟶ K.chainX k :=
  ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.faceMap i

/-- The boundary evaluated on a basis element: `∂ σ = ∑_i (-1)^i d_i σ`. -/
theorem DeltaCx.ι_chainD (K : DeltaCx) (k : ℕ) (σ : Fin (K.card (k + 1))) :
    K.chainι (k + 1) σ ≫ K.chainD k
      = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.chainι k (K.face σ i) := by
  simp only [DeltaCx.chainD, DeltaCx.faceMap, Preadditive.comp_sum, Preadditive.comp_zsmul,
    Limits.Sigma.ι_comp_desc]

/-- `chainD` expressed with the face maps: `∂ = ∑_i (-1)^i d_i`. -/
theorem DeltaCx.chainD_eq_sum (K : DeltaCx) (k : ℕ) :
    K.chainD k = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.faceMap i := rfl

/-- A morphism out of a coproduct of copies of `ℤ` is determined by its values
on the basis elements `chainι σ`. -/
theorem DeltaCx.chainX_hom_ext {K : DeltaCx} {k : ℕ} {T : ModuleCat ℤ}
    {f g : K.chainX k ⟶ T}
    (h : ∀ σ : Fin (K.card k), K.chainι k σ ≫ f = K.chainι k σ ≫ g) : f = g :=
  Limits.Sigma.hom_ext f g fun σ => h σ

/-! ## The chain map induced by a simplicial map -/

/-- On `k`-chains, a simplicial map `f : K ⟶ L` of `Δ`-complexes induces the
morphism `C_k^Δ(K) ⟶ C_k^Δ(L)` sending the basis element `σ` to `f σ`. -/
def DeltaCx.Hom.chainMapFun {K L : DeltaCx} (f : K.Hom L) (k : ℕ) :
    K.chainX k ⟶ L.chainX k :=
  Sigma.desc (fun σ : Fin (K.card k) => L.chainι k (f.map σ))

theorem DeltaCx.Hom.chainMapFun_chainι {K L : DeltaCx} (f : K.Hom L) (k : ℕ)
    (σ : Fin (K.card k)) :
    K.chainι k σ ≫ f.chainMapFun k = L.chainι k (f.map σ) :=
  Limits.Sigma.ι_comp_desc _ σ

/-- `chainMapFun` of the identity simplicial map is the identity. -/
theorem DeltaCx.Hom.chainMapFun_id (K : DeltaCx) (k : ℕ) :
    (Hom.id K).chainMapFun k = 𝟙 (K.chainX k) := by
  simp [DeltaCx.Hom.chainMapFun]

/-- `chainMapFun` is compatible with composition of simplicial maps. -/
theorem DeltaCx.Hom.chainMapFun_comp {K L M : DeltaCx} (f : K.Hom L) (g : L.Hom M) (k : ℕ) :
    (f.comp g).chainMapFun k = f.chainMapFun k ≫ g.chainMapFun k := by
  apply DeltaCx.chainX_hom_ext
  intro σ
  rw [DeltaCx.Hom.chainMapFun_chainι, ← Category.assoc, DeltaCx.Hom.chainMapFun_chainι,
    DeltaCx.Hom.chainMapFun_chainι, DeltaCx.Hom.comp_map]

end

end Work.DeltaHomology
