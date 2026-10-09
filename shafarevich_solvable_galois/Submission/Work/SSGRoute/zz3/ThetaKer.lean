import Mathlib
import Submission.Work.SSGRoute.zz3.Defs
import Submission.Work.SSGRoute.zz3.ThetaKerAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ThetaKer`: the kernel of `θ` on the `Λ`-fixed part

`θ = thetaFun n` sends a function `g : (Fin 3 → XX n) → ZMod 2` to the product in
`Q_{(4,1)} = F(n)/F(n)^{(4,1)}` of the classes of the left-nested commutators `[[x,y],z]` over the
triples `w` with `g w = 1`.  The statement proved here is that `θ` is injective on the fixed points
of the left-nested bracket map `Λ = LamT n`.

The proof produces, for every triple `W`, a `ℤ/2`-valued additive functional `lamCoeff n W` on
`γ₃ = F(n)^{(3)}` (the mod-`2` degree-`3` coefficient of the Magnus image) which vanishes on
`γ₃ ∩ F(n)^{(4,1)}` and satisfies

  `lamCoeff n W (lcF n w) = [w = W] + [w = W∘sw01] + [w = W∘swcyc] + [w = W∘sw02]`.

Feeding `θ(g) = 1` through this functional and using `Λ g = g` gives `g W = 0` for every `W`.
-/

open scoped commutatorElement
open Work.CohomologicalShrinking
open Work.SSGRoute.ZZ3

noncomputable section

namespace Work.SSGRoute.zz3

theorem ThetaKer (n : ℕ) (g : Work.SSGRoute.ZZ3.TT n)
    (hg : Work.SSGRoute.ZZ3.LamT n g = g) (h : Work.SSGRoute.ZZ3.thetaFun n g = 1) :
    g = 0 := by
  classical
  letI : DecidableRel (α := Idx n) WellOrderingRel := Classical.decRel _
  letI : LinearOrder (Idx n) := linearOrderOfSTO WellOrderingRel
  let L : List (Idx n) := (Finset.univ : Finset (Idx n)).sort (· ≤ ·)
  let f : Idx n → FFn n := fun w => (lcF n w) ^ ((g w).val)
  let Y : FFn n := (L.map f).prod
  have hLtf : L.toFinset = Finset.univ := Finset.sort_toFinset _ _
  have htheta : thetaFun n g
      = (L.map (fun w => (mkQ n (lcF n w)) ^ ((g w).val))).prod := rfl
  have hYmk : mkQ n Y = thetaFun n g := by
    have hmap : L.map (fun w => mkQ n (f w))
        = L.map (fun w => (mkQ n (lcF n w)) ^ ((g w).val)) := by
      refine List.map_congr_left ?_
      intro w _
      exact mkQ_pow' n (lcF n w) ((g w).val)
    calc mkQ n Y = mkQ n (L.map f).prod := rfl
      _ = ((L.map f).map (fun x => mkQ n x)).prod := mkQ_listProd n (L.map f)
      _ = (L.map (fun w => mkQ n (f w))).prod := by rw [List.map_map]; rfl
      _ = (L.map (fun w => (mkQ n (lcF n w)) ^ ((g w).val))).prod := by rw [hmap]
      _ = thetaFun n g := htheta.symm
  have hfmem : ∀ x ∈ L.map f, x ∈ Gam3 n := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨w, _hw, rfl⟩
    exact (Gam3 n).pow_mem (lcF_mem_gam3 n w) _
  have hYγ : Y ∈ Gam3 n := Subgroup.list_prod_mem (Gam3 n) (l := L.map f) hfmem
  have hYP4 : Y ∈ pSeries 2 (FFn n) 4 := by
    have hmk1 : mkQ n Y = 1 := by rw [hYmk, h]
    have h1 := (mkQ_eq_one_iff' n Y).mp hmk1
    rw [flowTerm_four_one'] at h1
    exact h1
  have hkey : ∀ W : Idx n, g W = 0 := by
    intro W
    let Ww : FreeMonoid (XX n) := FreeMonoid.ofList (List.ofFn W)
    have hWlen : Ww.length = 3 := by
      rw [show Ww.length = (FreeMonoid.toList Ww).length from rfl, FreeMonoid.toList_ofList]
      simp [List.ofFn_succ, List.ofFn_zero]
    have hzero : lamCoeff n Ww Y = 0 :=
      lamCoeff_eq_zero_of_mem_pSeries4 n Ww hWlen Y hYγ hYP4
    have h1 : lamCoeff n Ww Y
        = (L.map (fun w => lamCoeff n Ww (f w))).sum := by
      have hLmem : ∀ x ∈ L.map f, x ∈ Gam3 n := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨w, _hw, rfl⟩
        exact (Gam3 n).pow_mem (lcF_mem_gam3 n w) _
      have := lamCoeff_listProd n Ww hWlen (L.map f) hLmem
      rw [show Y = (L.map f).prod from rfl, this, List.map_map]
      rfl
    have h2 : (L.map (fun w => lamCoeff n Ww (f w))).sum
        = (L.map (fun w => ((g w).val : ZMod 2) *
            ((if w = W then 1 else 0) + (if w = (fun i => W (sw01 i)) then 1 else 0)
              + (if w = (fun i => W (swcyc i)) then 1 else 0)
              + (if w = (fun i => W (sw02 i)) then 1 else 0)))).sum := by
      apply congrArg List.sum
      refine List.map_congr_left ?_
      intro w _
      rw [lamCoeff_pow n Ww hWlen (lcF n w) (lcF_mem_gam3 n w) ((g w).val), lamCoeff_lc n W w]
    have h3 : (L.map (fun w => ((g w).val : ZMod 2) *
            ((if w = W then 1 else 0) + (if w = (fun i => W (sw01 i)) then 1 else 0)
              + (if w = (fun i => W (swcyc i)) then 1 else 0)
              + (if w = (fun i => W (sw02 i)) then 1 else 0)))).sum
        = ∑ w : Idx n, ((g w).val : ZMod 2) *
            ((if w = W then 1 else 0) + (if w = (fun i => W (sw01 i)) then 1 else 0)
              + (if w = (fun i => W (swcyc i)) then 1 else 0)
              + (if w = (fun i => W (sw02 i)) then 1 else 0)) := by
      have hLnod : L.Nodup := Finset.sort_nodup (Finset.univ : Finset (Idx n)) (· ≤ ·)
      rw [← List.sum_toFinset _ hLnod, hLtf]
    have h4 : (∑ w : Idx n, ((g w).val : ZMod 2) *
            ((if w = W then 1 else 0) + (if w = (fun i => W (sw01 i)) then 1 else 0)
              + (if w = (fun i => W (swcyc i)) then 1 else 0)
              + (if w = (fun i => W (sw02 i)) then 1 else 0)))
        = (g W).val + (g (fun i => W (sw01 i))).val + (g (fun i => W (swcyc i))).val
            + (g (fun i => W (sw02 i))).val := by
      rw [Finset.sum_congr rfl (fun w _ => by rw [mul_add, mul_add, mul_add])]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [sum_mul_ite_eq n (fun w => ((g w).val : ZMod 2)) W,
        sum_mul_ite_eq n (fun w => ((g w).val : ZMod 2)) (fun i => W (sw01 i)),
        sum_mul_ite_eq n (fun w => ((g w).val : ZMod 2)) (fun i => W (swcyc i)),
        sum_mul_ite_eq n (fun w => ((g w).val : ZMod 2)) (fun i => W (sw02 i))]
    have h5 : (g W).val + (g (fun i => W (sw01 i))).val + (g (fun i => W (swcyc i))).val
            + (g (fun i => W (sw02 i))).val
        = g W + g (fun i => W (sw01 i)) + g (fun i => W (swcyc i)) + g (fun i => W (sw02 i)) := by
      rw [ZMod.natCast_zmod_val (g W), ZMod.natCast_zmod_val (g (fun i => W (sw01 i))),
        ZMod.natCast_zmod_val (g (fun i => W (swcyc i))),
        ZMod.natCast_zmod_val (g (fun i => W (sw02 i)))]
    have hLam : g W + g (fun i => W (sw01 i)) + g (fun i => W (swcyc i))
          + g (fun i => W (sw02 i)) = g W := by
      have := congrFun hg W
      rw [LamT_apply] at this
      exact this
    rw [h1, h2, h3, h4, h5, hLam] at hzero
    exact hzero
  funext W
  exact hkey W

end Work.SSGRoute.zz3
