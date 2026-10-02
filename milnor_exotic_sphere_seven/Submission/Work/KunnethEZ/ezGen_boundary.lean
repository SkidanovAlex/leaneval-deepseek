import Mathlib
import Submission.Work.KunnethEZ.EZComb
import Submission.Work.KunnethEZ.EZGenX

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The linear Eilenberg–Zilber prism (boundary) identity, in the "raw" `(p,q)`-shuffle form

The proof adapts (and stops short of) the cycle identity `Work.KunnethEZ.ezGen_isCycle_aux` of
`EZGenX.lean`: the partition of the faces of the shuffle cells into `X`-boundary, `Y`-boundary and
interior faces, the cancellation of the interior faces, and the two boundary bijections give
`∂ (ezGen p q σ τ) = Σ_{(T,i)} gX23 (T,i) + Σ_{(U,j)} gY32 (U,j)`; regrouping the product sums gives
the shape used by the chain-level derivation identity.  Here `p = P + 1` and `q = Q + 1`, as in
`EZGenX.lean`.
-/

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.KunnethEZ

open Work.Cohomology.Crux33

noncomputable section

variable {P Q : ℕ}

local notation "p" => P + 1
local notation "q" => Q + 1

theorem ezGen_boundary (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((X ⊗ Y).chainComplex eZR).d (p + q) (p + q - 1)
        (Work.Cohomology.Crux33.ezGen p q X Y σ τ)
      = (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
          (∑ T : Sh23 p q, shufSignN T.1 •
            genP (X.map (aMap23 p q T).op (X.δ i σ)) (Y.map (bMap23 p q T).op τ)))
        + (-1 : ℤ) ^ (p) • (∑ j : Fin (q + 1), (-1 : ℤ) ^ (j : ℕ) •
          (∑ U : Sh32 p q, shufSignN U.1 •
            genP (X.map (aMap32 p q U).op σ) (Y.map (bMap32 p q U).op (Y.δ j τ)))) := by

  classical
  change ((X ⊗ Y).chainComplex eZR).d ((p + q - 1) + 1) (p + q - 1)
      (Work.Cohomology.Crux33.ezGen p q X Y σ τ) = (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
          (∑ T : Sh23 p q, shufSignN T.1 •
            genP (X.map (aMap23 p q T).op (X.δ i σ)) (Y.map (bMap23 p q T).op τ)))
        + (-1 : ℤ) ^ (p) • (∑ j : Fin (q + 1), (-1 : ℤ) ^ (j : ℕ) •
          (∑ U : Sh32 p q, shufSignN U.1 •
            genP (X.map (aMap32 p q U).op σ) (Y.map (bMap32 p q U).op (Y.δ j τ))))
  have hL : ((X ⊗ Y).chainComplex eZR).d ((p + q - 1) + 1) (p + q - 1)
        (Work.Cohomology.Crux33.ezGen p q X Y σ τ)
      = ∑ S : PShuffle p q, ∑ j : Fin ((p + q - 1) + 2), lhsT X Y σ τ (S, j) := by
    rw [ezGen_eq_genP, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_zsmul, d_genP (n := p + q - 1), ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_smul]
    congr 1
    simp only [lhsT]
    erw [map_delta, map_delta]
  rw [hL, ← Fintype.sum_prod_type (f := lhsT X Y σ τ)]
  have hpt : ∀ x : PShuffle p q × Fin ((p + q - 1) + 2), lhsT X Y σ τ x
      = (if IsBX x.1.1 x.2 then lhsT X Y σ τ x else 0)
        + (if IsBY x.1.1 x.2 then lhsT X Y σ τ x else 0)
        + (if IsInt x.1.1 x.2 then lhsT X Y σ τ x else 0) := by
    intro x
    have hnb := not_both_boundary (by omega : 0 < p + q) x.1.1 x.2
    by_cases h1 : IsBX x.1.1 x.2
    · rw [if_pos h1, if_neg (fun h2 => hnb ⟨h1, h2⟩), if_neg (fun h2 => h2.1 h1)]
      abel
    · by_cases h2 : IsBY x.1.1 x.2
      · rw [if_neg h1, if_pos h2, if_neg (fun h3 => h3.2 h2)]
        abel
      · rw [if_neg h1, if_neg h2, if_pos (show IsInt x.1.1 x.2 from ⟨h1, h2⟩)]
        abel
  have hpart :
      (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBX x.1.1 x.2), lhsT X Y σ τ x)
      + (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBY x.1.1 x.2), lhsT X Y σ τ x)
      + (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsInt x.1.1 x.2), lhsT X Y σ τ x)
      = ∑ x : PShuffle p q × Fin ((p + q - 1) + 2), lhsT X Y σ τ x := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => (hpt x).symm)
  rw [hpart.symm]
  have hInt : (∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
      IsInt x.1.1 x.2), lhsT X Y σ τ x) = 0 := by
    refine Finset.sum_involution
      (g := fun x hx => (flipP x.1 x.2 (Finset.mem_filter.mp hx).2, x.2)) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      have hsign : @shufSign (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
          = - @shufSign (P + 1) (Q + 1) x.1.1 := by
        rw [@shufSign_eq_shufSignN (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1,
          @shufSign_eq_shufSignN (P + 1) (Q + 1) x.1.1]
        exact Work.KunnethEZ.shufSignN_flipS x.1.1 x.2 hxI
      have hmap : SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2
          = SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) x.1.1 x.1.2 := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext k
        refine Fin.ext ?_
        show ((SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2) k).val
          = ((SimplexCategory.δ x.2 ≫ @aHom (P + 1) (Q + 1) x.1.1 x.1.2) k).val
        erw [comp_val, comp_val, aHom_val, aHom_val, pA_eq_ANat, pA_eq_ANat, delta_val]
        exact Work.KunnethEZ.ANat_flipS x.1.1 x.2 hxI (delV_ne (j := x.2.val) (k := k.val))
      have hmapb : SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2
          = SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) x.1.1 x.1.2 := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext k
        refine Fin.ext ?_
        show ((SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) (flipP x.1 x.2 hxI).1
            (flipP x.1 x.2 hxI).2) k).val
          = ((SimplexCategory.δ x.2 ≫ @bHom (P + 1) (Q + 1) x.1.1 x.1.2) k).val
        erw [comp_val, comp_val, bHom_val, bHom_val, pB_eq_BNat, pB_eq_BNat, delta_val]
        exact Work.KunnethEZ.BNat_flipS x.1.1 x.2 hxI (delV_ne (j := x.2.val) (k := k.val))
      have hgoal : lhsT X Y σ τ (flipP x.1 x.2 hxI, x.2) = - lhsT X Y σ τ x := by
        simp only [lhsT]
        rw [hmap, hmapb, hsign, neg_mul, neg_zsmul]
      rw [hgoal]
      abel
    · intro x hx _
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      intro hc
      have h1 := congrArg Prod.fst hc
      exact Work.KunnethEZ.flipS_ne x.1.1 x.2 hxI (Subtype.ext_iff.mp h1)
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Work.KunnethEZ.IsInt_flipS x.1.1 x.2 hxI⟩
    · intro x hx
      obtain ⟨-, hxI⟩ := Finset.mem_filter.mp hx
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (Work.KunnethEZ.flipS_flipS x.1.1 x.2 hxI)
      · rfl
  rw [hInt]
  have hBX : (∑ y : Sh23 p q × Fin (p - 1 + 2), gX23 X Y σ τ y)
      = ∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBX x.1.1 x.2), lhsT X Y σ τ x := by
    refine Finset.sum_bij (fun y _ => phiX y) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsBX_SX y.2 y.1⟩
    · intro y₁ _ y₂ _ heq
      exact phiX_inj heq
    · intro z hz
      obtain ⟨-, hzBX⟩ := Finset.mem_filter.mp hz
      exact ⟨(bwdT z.1 z.2 hzBX, bwdI z.1 z.2 hzBX), Finset.mem_univ _, phiX_bwd z.1 z.2 hzBX⟩
    · intro y _
      obtain ⟨T, i⟩ := y
      simp only [gX23, lhsT, phiX]
      erw [aFace_SX i T, map_op_comp (aMap23 p q T) (SimplexCategory.δ i) σ, bFace_SX i T,
        shufSign_SX i T, mul_comm (shufSignN T.1) ((-1 : ℤ) ^ (i : ℕ))]
      rfl
  rw [← hBX]
  have hBY : (∑ y : Sh32 p q × Fin (q - 1 + 2), gY32 X Y σ τ y)
      = ∑ x ∈ Finset.univ.filter (fun x : PShuffle p q × Fin ((p + q - 1) + 2) =>
          IsBY x.1.1 x.2), lhsT X Y σ τ x := by
    refine Finset.sum_bij (fun y _ => phiY y) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsBY_SY y.2 y.1⟩
    · intro y₁ _ y₂ _ heq
      exact phiY_inj heq
    · intro z hz
      obtain ⟨-, hzBY⟩ := Finset.mem_filter.mp hz
      exact ⟨(bwdU z.1 z.2 hzBY, bwdJ z.1 z.2 hzBY), Finset.mem_univ _, phiY_bwd z.1 z.2 hzBY⟩
    · intro y _
      obtain ⟨U, j⟩ := y
      simp only [gY32, lhsT, phiY]
      erw [aFace_SY j U, bFace_SY j U, map_op_comp (bMap32 p q U) (SimplexCategory.δ j) τ,
        shufSign_SY j U, mul_comm (shufSignN U.1) ((-1 : ℤ) ^ (j : ℕ))]
      rfl
  rw [← hBY, add_zero]
  congr 1
  · rw [Fintype.sum_prod_type (f := gX23 X Y σ τ)]
    rw [Finset.sum_comm (f := fun T i => gX23 X Y σ τ (T, i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    simp only [gX23]
    rw [mul_comm, mul_zsmul]
    try rfl
  · rw [Fintype.sum_prod_type (f := gY32 X Y σ τ)]
    rw [Finset.sum_comm (f := fun U j => gY32 X Y σ τ (U, j))]
    rw [← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_zsmul, ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    simp only [gY32]
    rw [mul_zsmul, mul_comm (shufSignN U.1) ((-1 : ℤ) ^ (j : ℕ)), mul_zsmul]
    try rfl

end

end Work.KunnethEZ
