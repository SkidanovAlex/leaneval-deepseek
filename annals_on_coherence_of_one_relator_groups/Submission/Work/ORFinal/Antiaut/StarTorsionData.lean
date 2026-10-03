/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The antipode of `TorsionData` from the involution, for real coefficient embeddings

`Work.ORBridgeTor.torsionFree_tensor_diagRight` (node N8's Lemma 5.1′ in the *right*-module form,
the input of `Work.ORBridgeTor.hA_of_torsion`) and `Work.ORBridgeTor.hswap_of_jl52` (JL Lemma 5.2)
both consume an antipode

`ι : Work.ORBridgeTor.AntiAut K ↥(L.D ⊤)` with `ι (gElemR K G ↥(L.D ⊤) φ g) = gElemR … g⁻¹`,

where `L : Work.ORTorsion.TorsionData K G U`.  This file produces it from the involution `star` of
`U`, under the three hypotheses

* `hreal : ∀ k, star (algebraMap K U k) = algebraMap K U k` — the coefficient embedding is real
  (for `K = ℚ` and `φK = algebraMap ℚ ℂ` this is `Work.ORFinal.Antiaut.hreal_rat`);
* `hstarD : star` preserves each division closure `L.D H`;
* `hstarGen : star` inverts the group basis.

In the bridge of `Submission/Work/ORBridgeLinnell/`, `hstarD` and `hstarGen` are theorems:
`Work.ORFinal.Antiaut.star_mem_D` (`Antiaut/antiAutOfStar.lean`, delegated child) and
`Work.ORBridgeLinnell.star_gen` (`Bridge.lean`).  Together with
`Work.ORFinal.TorsionData.torsionDataOf` this closes the T2/T5 halves of the JL §5 chain for real
coefficient embeddings.
-/
import Mathlib
import Submission.Work.ORFinal.Antiaut
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORBridgeTor.torsionFree_tensor_diagRight

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u

namespace Work.ORFinal.Antiaut

open Work.ORFlatness

/-- **The antipode of `↥(L.D ⊤)` from the involution `star`**, for a coefficient embedding that
`star` fixes: a `K`-linear anti-automorphism which inverts the group basis. -/
theorem antiAutOfStar_torsionData (K : Type u) [Field K] {G : Type u} [Group G]
    {U : Type u} [Ring U] [StarRing U] [Algebra K U] (L : Work.ORTorsion.TorsionData K G U)
    (hreal : ∀ k : K, star (algebraMap K U k) = algebraMap K U k)
    (hstarD : ∀ (H : Subgroup G) (x : U), x ∈ (L.D H : Set U) → star x ∈ (L.D H : Set U))
    (hstarGen : ∀ g : G, star ((L.gen g : Uˣ) : U) = ↑((L.gen g)⁻¹)) :
    ∃ ι : Work.ORBridgeTor.AntiAut K ↥(L.D ⊤),
      ∀ g : G, ι (Work.ORFlatness.gElemR K G ↥(L.D ⊤)
          (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g)
        = Work.ORFlatness.gElemR K G ↥(L.D ⊤)
          (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g⁻¹ := by
  classical
  have hmem : ∀ x : ↥(L.D ⊤), star (x : U) ∈ (L.D ⊤ : Set U) := fun x => hstarD ⊤ x x.2
  have hsmul : ∀ (c : K) (x : U), star (algebraMap K U c * x) = algebraMap K U c * star x := by
    intro c x
    rw [star_mul, hreal c, Algebra.commutes]
  let e : ↥(L.D ⊤) ≃ₗ[K] ↥(L.D ⊤) :=
    { toFun := fun x => ⟨star (x : U), hmem x⟩
      invFun := fun x => ⟨star (x : U), hmem x⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by
        show star ((x : U) + (y : U)) = star (x : U) + star (y : U)
        rw [star_add])
      map_smul' := fun c x => Subtype.ext (by
        change star (((c : K) • (x : U))) = (c : K) • star (x : U)
        rw [Algebra.smul_def, Algebra.smul_def, hsmul]) }
  refine ⟨⟨e, ?_, ?_⟩, ?_⟩
  · intro a b
    exact Subtype.ext (by
      show star (((a : U)) * (b : U)) = star (b : U) * star (a : U)
      rw [star_mul])
  · exact Subtype.ext (by show star (1 : U) = 1; rw [star_one])
  · intro g
    have h1 : Work.ORFlatness.gElemR K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g = L.genTop g := by
      rw [Work.ORFlatness.gElemR, MonoidAlgebra.lift_single, one_smul]
    have h2 : Work.ORFlatness.gElemR K G ↥(L.D ⊤)
        (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) g⁻¹ = L.genTop g⁻¹ := by
      rw [Work.ORFlatness.gElemR, MonoidAlgebra.lift_single, one_smul]
    rw [h1, h2]
    refine Subtype.ext ?_
    change star ((L.gen g : Uˣ) : U) = ↑(L.gen (g⁻¹))
    rw [map_inv]
    exact hstarGen g

end Work.ORFinal.Antiaut
