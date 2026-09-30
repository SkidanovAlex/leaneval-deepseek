/-
# `BridgeSquare/fibreLoopIdentA.lean` — the `κ_{v,2}` fibre identity (`A`-case)

For every cusp `v`, the singular `1`-chain `singA v` (the image of the `a`-generator of `H_1(T²)`
under the section `Fn v`, cf. `singA_eq_cChain`) differs from `± Ψ_M(fibreLoopVec v 0)` by a
boundary of a singular `2`-chain of `M̄`.

The proof is assembled from

* the per-cell identity `cellChiA`: `Ψ_M` of the `k`-th unit cube edge cell is (up to a boundary)
  the signed chart chain pair `[cuspCorner1, cuspMid] - [cuspCorner, cuspMid]`;
* the chart algebra `ChartAlgA` (`c1_sub`, `c1_rev`, `c1_deg`), which turns that into
  `- EcA v k` up to a boundary;
* the subdivision of the corner line (`cornerSumA`): `∑_k EcA v k = [DA v, BA v] + ∂`;
* the prism translation (`prismA`): `[0, λ₂] + [DA v, BA v] ∈ ∂`.

Everything is a computation with explicit chart chains; the `ε = ±1` ambiguity is absorbed by the
existentially quantified sign `s`.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreAsmA
import Submission.Work.BridgeSquare.singA_eq_cChain
import Submission.Work.BridgeSquare.FibrePathA
import Submission.Work.BridgeSquare.prism_c1
import Submission.Work.BridgeSquare.cellChiA
import Submission.Work.BridgeSquare.cornerSumA
import Submission.Work.BridgeSquare.prismA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Convexity

attribute [local instance] Convexity.ConvexSpace.ofModule

namespace Work.BridgeSquare

noncomputable section

theorem fibreLoop_expandA (v : Fin 5) :
    fibreLoopVec v 0 = ∑ k : Fin 4, edgeSign v 0 k • evecA v k :=
  fibreLoop_expand v

theorem edgeSign_dummyA (v : Fin 5) (k : Fin 4) (hk : ¬ (k : ℕ) < fibreLen v 0) :
    edgeSign v 0 k = 0 := by
  fin_cases v <;> fin_cases k <;>
    first
      | (exfalso; revert hk; decide)
      | decide

/-! ## §1  Linearity of `Ψ_M` on the fibre loop -/

theorem PsiM_f_fibreLoopA (v : Fin 5) :
    (PsiM.f 1) (fibreLoopVec v 0)
      = ∑ k : Fin 4, edgeSign v 0 k • (PsiM.f 1) (evecA v k) := by
  calc (PsiM.f 1) (fibreLoopVec v 0)
      = (PsiM.f 1) (∑ k : Fin 4, edgeSign v 0 k • evecA v k) :=
        congrArg (PsiM.f 1) (fibreLoop_expandA v)
    _ = ∑ k : Fin 4, (PsiM.f 1) (edgeSign v 0 k • evecA v k) := map_sum _ _ _
    _ = ∑ k : Fin 4, edgeSign v 0 k • (PsiM.f 1) (evecA v k) :=
        Finset.sum_congr rfl fun k _ => map_zsmul _ _ _

/-! ## §2  The per-edge chart algebra -/

theorem E1_sub_E0_A (v : Fin 5) (k : Fin 4) :
    ∃ (W : ↥((singCxFun.obj cMtop).X 2)),
      E1A v k - E0A v k = - EcA v k + (singCxFun.obj cMtop).d 2 1 W := by
  have h_sub : c1 v (cuspMid v k) (cuspCorner1 v k)
      = c1 v (cuspCorner v k) (cuspCorner1 v k)
        + (singCxFun.obj cMtop).d 2 1 (c2 v (cuspCorner v k) (cuspMid v k) (cuspCorner1 v k))
        - c1 v (cuspCorner v k) (cuspMid v k) := by
    have := c1_sub v (cuspCorner v k) (cuspMid v k) (cuspCorner1 v k)
    rw [← this]; abel
  have h_rev : c1 v (cuspCorner1 v k) (cuspMid v k)
      = (singCxFun.obj cMtop).d 2 1 (c2 v (cuspMid v k) (cuspCorner1 v k) (cuspMid v k))
        + c1 v (cuspMid v k) (cuspMid v k) - c1 v (cuspMid v k) (cuspCorner1 v k) := by
    have := c1_rev v (cuspMid v k) (cuspCorner1 v k)
    rw [← this]; abel
  have h_deg : c1 v (cuspMid v k) (cuspMid v k)
      = (singCxFun.obj cMtop).d 2 1 (c2 v (cuspMid v k) (cuspMid v k) (cuspMid v k)) :=
    c1_deg v (cuspMid v k)
  refine ⟨c2 v (cuspMid v k) (cuspCorner1 v k) (cuspMid v k)
    - c2 v (cuspCorner v k) (cuspMid v k) (cuspCorner1 v k)
    + c2 v (cuspMid v k) (cuspMid v k) (cuspMid v k), ?_⟩
  show c1 v (cuspCorner1 v k) (cuspMid v k) - c1 v (cuspCorner v k) (cuspMid v k)
      = - c1 v (cuspCorner v k) (cuspCorner1 v k) + (singCxFun.obj cMtop).d 2 1 _
  rw [h_rev, h_sub, h_deg, map_add, map_sub]
  abel

/-! ## §3  Summing the per-edge algebra -/

theorem E1_sum_E0_A (v : Fin 5) :
    ∃ (W : ↥((singCxFun.obj cMtop).X 2)),
      (∑ k : Fin 4, (if (k : ℕ) < fibreLen v 0 then E1A v k - E0A v k else 0))
        = - EcSumA v + (singCxFun.obj cMtop).d 2 1 W := by
  choose W hW using fun k : Fin 4 => E1_sub_E0_A v k
  refine ⟨∑ k : Fin 4, (if (k : ℕ) < fibreLen v 0 then W k else 0), ?_⟩
  have h1 : ∀ k : Fin 4, (if (k : ℕ) < fibreLen v 0 then E1A v k - E0A v k else 0)
      = (if (k : ℕ) < fibreLen v 0 then (- EcA v k + (singCxFun.obj cMtop).d 2 1 (W k))
          else 0) := by
    intro k; by_cases hk : (k : ℕ) < fibreLen v 0 <;> simp [hk, hW k]
  have h2 : ∀ k : Fin 4, (if (k : ℕ) < fibreLen v 0
        then (- EcA v k + (singCxFun.obj cMtop).d 2 1 (W k)) else 0)
      = -(if (k : ℕ) < fibreLen v 0 then EcA v k else 0)
        + (if (k : ℕ) < fibreLen v 0 then (singCxFun.obj cMtop).d 2 1 (W k) else 0) := by
    intro k; by_cases hk : (k : ℕ) < fibreLen v 0 <;> simp [hk]
  have h3 : (∑ k : Fin 4, (if (k : ℕ) < fibreLen v 0
        then (singCxFun.obj cMtop).d 2 1 (W k) else 0))
      = (singCxFun.obj cMtop).d 2 1 (∑ k : Fin 4, if (k : ℕ) < fibreLen v 0 then W k else 0) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < fibreLen v 0 <;> simp [hk]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, h3]
  rfl

/-! ## §4  The decomposition of `Ψ_M (fibreLoopVec v 0)` -/

theorem PsiM_fibreLoop_decomp (v : Fin 5) :
    ∃ (s : ℤ) (W : ↥((singCxFun.obj cMtop).X 2)),
      (s = 1 ∨ s = -1) ∧
      (PsiM.f 1) (fibreLoopVec v 0)
        = (singCxFun.obj cMtop).d 2 1 W - s • EcSumA v := by
  obtain ⟨s, β, Z, hs, hconst, hcell⟩ := cellChiA v
  obtain ⟨W2, hW2⟩ := E1_sum_E0_A v
  have key : ∀ k : Fin 4, edgeSign v 0 k • (PsiM.f 1) (evecA v k)
      = (if (k : ℕ) < fibreLen v 0 then s else 0) • (E1A v k - E0A v k)
        + (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k) := by
    intro k
    by_cases hk : (k : ℕ) < fibreLen v 0
    · have hc : (PsiM.f 1) (evecA v k)
          = β k • E1A v k - β k • E0A v k + (singCxFun.obj cMtop).d 2 1 (Z k) :=
        hcell k hk
      have hb : edgeSign v 0 k * β k = s := by rw [mul_comm, hconst k, if_pos hk]
      calc edgeSign v 0 k • (PsiM.f 1) (evecA v k)
          = edgeSign v 0 k • (β k • E1A v k - β k • E0A v k
              + (singCxFun.obj cMtop).d 2 1 (Z k)) := congrArg _ hc
        _ = edgeSign v 0 k • (β k • E1A v k) - edgeSign v 0 k • (β k • E0A v k)
              + edgeSign v 0 k • (singCxFun.obj cMtop).d 2 1 (Z k) := by
            rw [zsmul_add, zsmul_sub]
        _ = (edgeSign v 0 k * β k) • E1A v k - (edgeSign v 0 k * β k) • E0A v k
              + (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k) := by
            rw [show edgeSign v 0 k • (β k • E1A v k) = (edgeSign v 0 k * β k) • E1A v k
                from (mul_zsmul (E1A v k) (edgeSign v 0 k) (β k)).symm,
              show edgeSign v 0 k • (β k • E0A v k) = (edgeSign v 0 k * β k) • E0A v k
                from (mul_zsmul (E0A v k) (edgeSign v 0 k) (β k)).symm,
              show edgeSign v 0 k • (singCxFun.obj cMtop).d 2 1 (Z k)
                = (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k)
                from (map_zsmul _ _ _).symm]
        _ = s • E1A v k - s • E0A v k
              + (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k) := by rw [hb]
        _ = s • (E1A v k - E0A v k)
              + (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k) := by
            rw [show s • E1A v k - s • E0A v k = s • (E1A v k - E0A v k)
                from (zsmul_sub (E1A v k) (E0A v k) s).symm]
        _ = (if (k : ℕ) < fibreLen v 0 then s else 0) • (E1A v k - E0A v k)
              + (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k) := by rw [if_pos hk]
    · have hz : edgeSign v 0 k = 0 := edgeSign_dummyA v k hk
      rw [hz, if_neg hk, map_zsmul, zero_zsmul, zero_zsmul, zero_zsmul, add_zero]
  have hs1 : (∑ k : Fin 4, (if (k : ℕ) < fibreLen v 0 then s else 0) • (E1A v k - E0A v k))
      = s • (∑ k : Fin 4, (if (k : ℕ) < fibreLen v 0 then (E1A v k - E0A v k) else 0)) := by
    rw [← Finset.sum_zsmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < fibreLen v 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, zero_zsmul, zsmul_zero]
  have hs3 : (∑ k : Fin 4, (singCxFun.obj cMtop).d 2 1 (edgeSign v 0 k • Z k))
      = (singCxFun.obj cMtop).d 2 1 (∑ k : Fin 4, edgeSign v 0 k • Z k) := by
    rw [map_sum]
  refine ⟨s, s • W2 + ∑ k : Fin 4, edgeSign v 0 k • Z k, hs, ?_⟩
  rw [PsiM_f_fibreLoopA, Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, hs1, hs3,
    hW2]
  rw [zsmul_add,
    show s • (-EcSumA v) = -(s • EcSumA v) from zsmul_neg (EcSumA v) s,
    show s • ((singCxFun.obj cMtop).d 2 1 W2) = (singCxFun.obj cMtop).d 2 1 (s • W2)
      from (map_zsmul _ _ _).symm]
  rw [map_add]
  abel

/-! ## §5  The theorem -/

theorem fibreLoopIdentA (v : Fin 5) :
    ∃ (s : ℤ) (y : ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 2)),
      (s = 1 ∨ s = -1) ∧
      ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
        = Work.BridgeSquare.singA v
          - s • (Work.BridgeSquare.PsiM.f 1) (Work.BridgeSquare.fibreLoopVec v 0) := by
  obtain ⟨s, W, hs, hW⟩ := PsiM_fibreLoop_decomp v
  obtain ⟨W3, hW3⟩ := cornerSumA v
  obtain ⟨W4, hW4⟩ := prismA v
  refine ⟨s, W4 + W3 - s • W, hs, ?_⟩
  have hW3' : (singCxFun.obj cMtop).d 2 1 W3
      = EcSumA v - cChain (v := v) ![DA v, BA v] := by rw [hW3]; abel
  have hs2 : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hs4 : ∀ x : ↥((singCxFun.obj cMtop).X 1), s • (s • x) = x := by
    intro x
    rw [show s • (s • x) = (s * s) • x from (mul_zsmul x s s).symm, hs2, one_zsmul]
  rw [hW, singA_eq_cChain, map_sub, map_add, map_zsmul, ← hW4, hW3']
  rw [show s • ((singCxFun.obj cMtop).d 2 1 W - s • EcSumA v)
      = s • ((singCxFun.obj cMtop).d 2 1 W) - s • (s • EcSumA v) from zsmul_sub _ _ s,
    show s • (s • EcSumA v) = EcSumA v from hs4 (EcSumA v)]
  abel


end

end Work.BridgeSquare
