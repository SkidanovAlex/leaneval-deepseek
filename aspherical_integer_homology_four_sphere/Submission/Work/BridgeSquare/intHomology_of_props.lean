import Mathlib
import Submission.Work.HomologyMV.Main
import Submission.Work.BridgeSquare.mv_homology_of_props

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

open CategoryTheory

noncomputable section

/-- **The homology of `M̂` in the shape of the target theorem, from the "properties" form of the
Mayer–Vietoris data.**

The input is the Mayer–Vietoris long exact sequence `L` of `M̂ = A ∪ B`, together with the
"properties" that the geometry supplies directly:

* `hsurj` — the map `L.d (k,0) : H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` is surjective for `k ≥ 1`
  (this is what forces `L.d (k,1) = 0` and hence `H_k(M̂) ≅ ker (L.d (k-1,0))`);
* `hker` — the kernel of `L.d (k,0)` is the model `kerModel k` for `k ≥ 0`
  (this is `ℤ` exactly in degree `3`, i.e. `H_4(M̂) ≅ ℤ`, and `0` otherwise);
* `h0` — the degree-`0` identification `H_0(M̂) ≅ ℤ`;
* `hX` — the identification of the `X`-slot `L.H (k,2)` with the integral homology of `X`.

The conclusion is `H_k(X) ≅ ℤ` for `k = 0, 4` and `0` otherwise.

The Mayer–Vietoris computation itself is `Work.BridgeSquare.mv_homology_of_props`; the only
remaining step is to compose it with the identification `hX` of the `X`-slot with
`intHomology k X`. -/
theorem intHomology_of_props {X : TopCat} (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅ L.H (k, 0)))
    (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅ L.H (k, 1)))
    (hsurj : ∀ k : ℤ, 1 ≤ k → Function.Surjective (L.d (k, 0)).hom)
    (hker : ∀ k : ℤ, 0 ≤ k → Nonempty ((L.d (k, 0)).hom.ker ≃ₗ[ℤ] ↥(Work.HomologyMV.kerModel k)))
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅ LeanEval.Topology.intHomology k X)
    (h0 : Nonempty (L.H (0, 2) ≅ Work.HomologyMV.Sol 0)) (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k X ≅
      (if k = 0 ∨ k = 4 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e⟩ := mv_homology_of_props L eM eN hsurj hker h0 k
  exact ⟨(hX k).symm ≪≫ e⟩

end

end Work.BridgeSquare
