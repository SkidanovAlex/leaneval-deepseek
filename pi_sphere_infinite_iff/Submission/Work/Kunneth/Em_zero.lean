import Mathlib
import Submission.Work.Kunneth.EZAWHomotopy
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.EZHom

/-!
# The degree-zero Eilenberg–Zilber defect `Em 0 0 = 0`

`Em p q` is the defect `(ezMap ≫ awMap)(U p q) - U p q` of the `(p,q)`-model
`tMod p q = C_*(Δ[p]) ⊗ C_*(Δ[q])` at the universal element `U p q = σ_p ⊗ τ_q`
(`Submission/Work/Kunneth/EZAWDefs.lean`).  In bidegree `(0,0)` the two shuffle computations are
trivial — the unique `(0,0)`-shuffle has sign `1` and identity coordinates, and in degree `0` the
Alexander–Whitney sum has the single term `p = 0` — so the defect vanishes.

* `Em_ezGen_zero` — the shuffle chain of a pair of vertices is the generator of that pair;
* `Em_ezHom_tpLof_zero` — `ezMap` fixes the generator `σ ⊗ τ` of the `(0,0)`-summand;
* `Em_awHom_genCh_zero` — `awMap` sends the generator of a vertex back to `σ ⊗ τ`;
* `Em_Ezaw_tpLof_zero` — hence `ezMap ≫ awMap` fixes `σ ⊗ τ`;
* `Em_zero` — `Em 0 0 = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The Eilenberg–Zilber shuffle chain of a pair of `0`-simplices is the generator of the pair
(the `(0,0)`-shuffle is unique, has sign `1` and identity coordinates). -/
lemma Em_ezGen_zero (X Y : SSet) (σ : X _⦋0⦌) (τ : Y _⦋0⦌) :
    Work.Cohomology.Crux33.ezGen 0 0 X Y σ τ = genCh (sProd X Y) (σ, τ) := by
  rw [Work.KunnethEZ.ezGen_zero_single_right 0 X Y σ τ,
    EZHom.aHom_zero (Work.KunnethEZ.zSh0 0), EZHom.bHom_zero (Work.KunnethEZ.zSh0 0)]
  simp [Work.KunnethEZ.genP]

/-- The `(0,0)`-component of the Eilenberg–Zilber shuffle map fixes the summand generator
`σ ⊗ τ`. -/
lemma Em_ezHom_tpLof_zero (X Y : SSet) (σ : X _⦋0⦌) (τ : Y _⦋0⦌) :
    (ezHom X Y 0).hom
        (tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = genCh (sProd X Y) (σ, τ) := by
  rw [ezHom_apply_tpLof X Y 0 0 0 rfl, ezSummandLin_tmul_chain, Work.KunnethEZ.ezChain_gen]
  rw [Em_ezGen_zero X Y σ τ]
  rfl

/-- The value of the Alexander–Whitney map on the generator of a vertex of `X ⊗ Y`: in degree `0`
the Alexander–Whitney sum has the single term `p = 0` with both faces the identity. -/
lemma Em_awHom_genCh_zero (X Y : SSet) (σ : X _⦋0⦌) (τ : Y _⦋0⦌) :
    (awHom X Y 0).hom (genCh (sProd X Y) (σ, τ))
      = tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ) := by
  have h := congrArg (fun (g : zz ⟶ (tChain X Y).X 0) => g.hom (1 : ℤ))
    (awHom_gen X Y 0 (σ, τ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, awGen_hom_one X Y 0 (σ, τ)]
  rw [Finset.sum_eq_single_of_mem (⟨0, by omega⟩ : Fin (0+1)) (Finset.mem_univ _)
    (fun b _ hb => absurd (Fin.ext (by have := b.isLt; omega)) hb)]
  rw [show Cohomology.frontFace X ((⟨0, by omega⟩ : Fin (0+1))).val 0 (by omega)
        ((σ,τ) : (sProd X Y) _⦋0⦌).1 = σ from EZHom.frontFace_self (X := X) 0 le_rfl σ,
    show backFaceLE Y (0 - ((⟨0, by omega⟩ : Fin (0+1))).val) 0 (by omega)
        ((σ,τ) : (sProd X Y) _⦋0⦌).2 = τ from EZHom.backFaceLE_self (X := Y) 0 le_rfl τ]
  congr 1

/-- In degree `0` the composite `ezMap ≫ awMap` fixes the generator `σ ⊗ τ` of the `(0,0)`-summand
of `tChain X Y`. -/
lemma Em_Ezaw_tpLof_zero (X Y : SSet) (σ : X _⦋0⦌) (τ : Y _⦋0⦌) :
    EzawLin X Y 0 (tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩
        (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ) := by
  have h1 : EzawLin X Y 0 (tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩
        (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = (awHom X Y 0).hom ((ezHom X Y 0).hom (tpLof (sChain X) (sChain Y) 0 ⟨(0,0), rfl⟩
          (genCh X σ ⊗ₜ[ℤ] genCh Y τ))) := rfl
  rw [h1, Em_ezHom_tpLof_zero X Y σ τ, Em_awHom_genCh_zero X Y σ τ]

theorem Em_zero : Work.Kunneth.Em 0 0 = 0 := by
  rw [Em, sub_eq_zero]
  exact Em_Ezaw_tpLof_zero (SdS 0) (SdS 0) (univS 0) (univS 0)

end

end Work.Kunneth
