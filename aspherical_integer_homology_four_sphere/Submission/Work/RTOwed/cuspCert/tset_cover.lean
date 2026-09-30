/-
# The truncation set is covered by the five ceiling maps

`Work.RTOwed.cuspCert.tset_cover`: every point of the truncation set `Tset ⊆ M̄` (the image of the
truncation facets of the truncated 24-cell, `Work.FoldInst.Xtrunc`) is the image of a point of `E3`
under one of the five ceiling maps `Work.RTOwed.mbarPt v`.

## The proof

A point of `Tset` is the class of `x₀ = (bit, q)` with `q ∈ Q̄` and `truncSlack w q = 0` for some
ideal vertex `w`.  Let `a` be the cell of the data with `cubeVert a = w` and `cubeBit a = bit`
(`cubeLookup`).  Then

* `x := kleinToX a q ∈ cubeBox a`: the wall identities of `cuspCertWalls` express the six box
  inequalities as wall slacks at `kleinPt a x = q` (`projCert` turns `kleinPt a (kleinToX a q)` into
  `q + truncSlack w q • projV a = q`), and those slacks are nonnegative on `Q̄`;
* the saturation pattern `e : Fin 8` of `x` (the coordinates with `x i = cubeCorner a i + 1`)
  determines the neighbour cell `b = covB a e` of the same cusp and the lattice shift `latOf`:
  `cubeOf v x = b` and `redV v x = z := zOf a e x` (`cubeLookup`), so `mbarPt v x` is the class of
  `(cubeBit b, kleinPt b z)`;
* `covAffine` identifies `covS a e r * kleinPt b z r` with `kleinPt a x r = q r` up to the
  saturated coordinates, where `x i = cubeCorner a i + 1` makes the correction term vanish;
* `covData` gives the copy bit and the identification `covGam a e = ∑_{sat i} typeGen (wallLo b i)`
  of the gluing, which lies in `Ksub` at the class of `z` (`Qbar_act` plus the wall tightness), so
  the classes of `(cubeBit b, kleinPt b z)` and `x₀` agree in `M̄`.

The four table certificates live in the modules `projCert`, `covAffine`, `covData` and `cubeLookup`;
the tables themselves and their meaning are documented in `tsetCoverData`.
-/

import Mathlib
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.cuspCert.tsetCoverData
import Submission.Work.RTOwed.cuspCert.cubeLookup
import Submission.Work.RTOwed.cuspCert.covData
import Submission.Work.RTOwed.cuspCert.projCert
import Submission.Work.RTOwed.cuspCert.covAffine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed.cuspCert

/-! ## Auxiliary lemmas about the tables -/

/-- The sign vector of `toG k` is `k`, for a `±1` vector `k`. -/
theorem signVec_toG_of (k : Fin 4 → ℤ) (h : ∀ i, k i = 1 ∨ k i = -1) :
    Work.FoldInst.signVec (Work.FoldInst.toG k) = k := by
  funext i
  rcases h i with h1 | h1 <;> simp [Work.FoldInst.signVec, Work.FoldInst.toG, h1]

/-- The sign vector of the group element `covGam a e` is the recorded `covS a e`. -/
theorem signVec_covGam (a : Fin 48) (e : Fin 8) :
    Work.FoldInst.signVec (covGam a e).1 = covS a e := by
  have h : ∀ i : Fin 4, covS a e i = (1 : ℤ) ∨ covS a e i = (-1 : ℤ) := by
    intro i
    fin_cases a <;> fin_cases e <;> fin_cases i <;> decide +kernel
  exact signVec_toG_of (covS a e) h

/-- The square of the entries of `covS a e` is `1`. -/
theorem covS_sq (a : Fin 48) (e : Fin 8) (r : Fin 4) : (covS a e r : ℝ) ^ 2 = 1 := by
  have h : covS a e r = (1 : ℤ) ∨ covS a e r = (-1 : ℤ) := by
    fin_cases a <;> fin_cases e <;> fin_cases r <;> decide +kernel
  rcases h with h | h <;> rw [h] <;> norm_num

/-- `satOf` reads back the bits of the encoding `⟨a0 + 2 a1 + 4 a2, _⟩` of a `0/1` pattern. -/
theorem satOf_mk (a0 a1 a2 : ℕ) (h0 : a0 ≤ 1) (h1 : a1 ≤ 1) (h2 : a2 ≤ 1) :
    satOf ⟨a0 + 2 * a1 + 4 * a2, by omega⟩ 0 = (a0 : ℤ) ∧
    satOf ⟨a0 + 2 * a1 + 4 * a2, by omega⟩ 1 = (a1 : ℤ) ∧
    satOf ⟨a0 + 2 * a1 + 4 * a2, by omega⟩ 2 = (a2 : ℤ) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [satOf] <;>
    (interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;> norm_num)

/-- A sum of three elements of `Ksub p` lies in `Ksub p`. -/
theorem sum_three_mem_Ksub (p : Work.FoldInst.E4) (f : Fin 3 → Work.FoldInst.Gg)
    (h : ∀ i, f i ∈ Work.FoldInst.Ksub p) :
    (∑ i : Fin 3, f i) ∈ Work.FoldInst.Ksub p := by
  rw [Fin.sum_univ_three]
  exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (h 0) (h 1)) (h 2)

/-- The sign-change action is an involution. -/
theorem act_self (g : Fin 4 → ZMod 2) (y : Work.FoldInst.E4) :
    Work.FoldInst.act g (Work.FoldInst.act g y) = y := by
  rw [Work.FoldInst.act_add]
  have h : g + g = 0 := by
    funext i
    exact Work.FoldInst.ZMod2_add_self (g i)
  rw [h, Work.FoldInst.act_zero]

/-! ## The cover of the truncation set -/

theorem tset_cover : ∀ y ∈ Work.FoldInst.Tset, ∃ (v : Fin 5) (x : Work.RTOwed.CuspE3),
    Work.RTOwed.mbarPt v x = y := by
  intro y hy
  obtain ⟨x₀, hx₀, hyx₀⟩ := hy
  rw [← hyx₀]
  obtain ⟨w, hw⟩ := hx₀
  obtain ⟨a, hva, hba⟩ := cubeLookup.2.2 w x₀.1
  set q : CuspE4 := x₀.2.1 with hq
  have hQ : q ∈ Work.FoldInst.Qbar := x₀.2.2
  have htr : Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a) q = 0 := by rw [hva]; exact hw
  set K : CuspE3 := Work.RTOwed.kleinToX a q with hK
  have hKproj : Work.RTOwed.kleinPt a K = q := by
    rw [hK, projCert a q, htr, zero_smul, add_zero]
  -- the cube coordinates of `q` lie in the box of `a`
  have hbox : K ∈ Work.RTOwed.cubeBox a := by
    intro i
    refine ⟨?_, ?_⟩
    · have h1 := Work.RTOwed.sideSlack_wallLo a i K
      rw [hKproj] at h1
      have h2 := hQ.1 (Work.RTOwed.wallLo a i)
      linarith
    · have h1 := Work.RTOwed.sideSlack_wallHi a i K
      rw [hKproj] at h1
      have h2 := hQ.1 (Work.RTOwed.wallHi a i)
      linarith
  -- the saturation pattern
  let bnd : Fin 3 → ℕ := fun i => if K i = (Work.Cusp.cubeCorner a i : ℝ) + 1 then 1 else 0
  have hbnd : ∀ i, bnd i ≤ 1 := by intro i; simp only [bnd]; split <;> norm_num
  have hb0 : bnd 0 ≤ 1 := hbnd 0
  have hb1 : bnd 1 ≤ 1 := hbnd 1
  have hb2 : bnd 2 ≤ 1 := hbnd 2
  let e : Fin 8 := ⟨bnd 0 + 2 * bnd 1 + 4 * bnd 2, by omega⟩
  have hsat0 := satOf_mk (bnd 0) (bnd 1) (bnd 2) hb0 hb1 hb2
  have hsat : ∀ i : Fin 3, satOf e i = (bnd i : ℤ) := by
    intro i
    fin_cases i
    · exact hsat0.1
    · exact hsat0.2.1
    · exact hsat0.2.2
  -- the bit of `i` is `1` exactly at the saturated coordinates
  have hbit1 : ∀ i : Fin 3, satOf e i = 1 → K i = (Work.Cusp.cubeCorner a i : ℝ) + 1 := by
    intro i hi
    have h := hsat i
    rw [hi] at h
    simp only [bnd] at h
    split at h
    · assumption
    · norm_num at h
  have hbit0 : ∀ i : Fin 3, satOf e i = 0 → K i ≠ (Work.Cusp.cubeCorner a i : ℝ) + 1 := by
    intro i hi hc
    have h := hsat i
    rw [hi] at h
    simp only [bnd] at h
    rw [if_pos hc] at h
    norm_num at h
  -- the floor of `K` is the corner plus the bit
  have hfloor : ∀ i : Fin 3, ⌊K i⌋ = Work.Cusp.cubeCorner a i + satOf e i := by
    intro i
    have hlo : (Work.Cusp.cubeCorner a i : ℝ) ≤ K i := (hbox i).1
    have hhi : K i ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1 := (hbox i).2
    have hbit : satOf e i = 1 ∨ satOf e i = 0 := by
      have h := hsat i
      simp only [bnd] at h
      split at h
      · left; exact h
      · right; exact h
    rcases hbit with hbit | hbit
    · have hKeq : K i = (Work.Cusp.cubeCorner a i : ℝ) + 1 := hbit1 i hbit
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [hbit]; push_cast; linarith
      · rw [hbit]; push_cast; linarith
    · have hKne : K i ≠ (Work.Cusp.cubeCorner a i : ℝ) + 1 := hbit0 i hbit
      have hlt : K i < (Work.Cusp.cubeCorner a i : ℝ) + 1 := lt_of_le_of_ne hhi hKne
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [hbit]; push_cast; linarith
      · rw [hbit]; push_cast; linarith
  have hfloorV : Work.RTOwed.floorV K = fun i : Fin 3 => Work.Cusp.cubeCorner a i + satOf e i :=
    funext hfloor
  have hcubeOf : Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K = covB a e := by
    show Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a) (Work.RTOwed.floorV K) = covB a e
    rw [hfloorV]
    exact cubeLookup.2.1 a e
  have hredV : Work.RTOwed.redV (Work.Cusp.cubeCusp a) K = zOf a e K := by
    apply PiLp.ext
    intro i
    simp only [Work.RTOwed.redV, zOf, PiLp.toLp_apply]
    rw [hcubeOf, hfloor i, covData.2.1 a e i]
    push_cast
    ring
  -- the affine certificate at `K`
  have hD : ∀ r : Fin 4, (covS a e r : ℝ) *
      Work.RTOwed.kleinPt (covB a e) (zOf a e K) r = Work.RTOwed.kleinPt a K r := by
    intro r
    have h := covAffine a e K r
    have hsum : (∑ i : Fin 3, if satOf e i = 1 then
        ((covC a e r i : ℝ) / 5) * (K i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hh : satOf e i = 1
      · rw [if_pos hh, hbit1 i hh]; ring
      · rw [if_neg hh]
    rw [hsum, sub_eq_zero] at h
    exact h
  have hpt : Work.RTOwed.kleinPt (covB a e) (zOf a e K) = Work.FoldInst.act (covGam a e).1 q := by
    apply PiLp.ext
    intro r
    have h := hD r
    rw [hKproj] at h
    rw [Work.FoldInst.act_apply_apply, signVec_covGam]
    calc Work.RTOwed.kleinPt (covB a e) (zOf a e K) r
        = (covS a e r : ℝ) ^ 2 * Work.RTOwed.kleinPt (covB a e) (zOf a e K) r := by
          rw [covS_sq]; ring
      _ = (covS a e r : ℝ) *
            ((covS a e r : ℝ) * Work.RTOwed.kleinPt (covB a e) (zOf a e K) r) := by ring
      _ = (covS a e r : ℝ) * q r := by rw [h]
  have hmem : Work.RTOwed.kleinPt (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K)
      (Work.RTOwed.redV (Work.Cusp.cubeCusp a) K) ∈ Work.FoldInst.Qbar := by
    rw [hcubeOf, hredV, hpt]
    exact (Work.FoldInst.Qbar_act (covGam a e).1 q).mpr hQ
  -- the group element is in the identification group
  have hterm : ∀ i : Fin 3, (if satOf e i = 1 then Work.FoldInst.typeGen
      (Work.FoldInst.sideTypeIdx (Work.RTOwed.wallLo (covB a e) i)) else 0) ∈
      Work.FoldInst.Ksub (Work.RTOwed.kleinPt (covB a e) (zOf a e K)) := by
    intro i
    by_cases hh : satOf e i = 1
    · rw [if_pos hh]
      have htight : Work.FoldInst.sideSlack (Work.RTOwed.wallLo (covB a e) i)
          (Work.RTOwed.kleinPt (covB a e) (zOf a e K)) = 0 := by
        rw [Work.RTOwed.sideSlack_wallLo]
        have hz0 : zOf a e K i = (Work.Cusp.cubeCorner (covB a e) i : ℝ) := by
          simp only [zOf, PiLp.toLp_apply]
          rw [covData.2.1 a e i, hbit1 i hh, hh]
          push_cast
          ring
        rw [hz0]; ring
      exact AddSubgroup.subset_closure ⟨Work.RTOwed.wallLo (covB a e) i, htight, rfl⟩
    · rw [if_neg hh]
      exact AddSubgroup.zero_mem _
  have hKsub : covGam a e ∈ Work.FoldInst.Ksub (Work.RTOwed.kleinPt (covB a e) (zOf a e K)) := by
    rw [covData.2.2.2 a e]
    exact sum_three_mem_Ksub _ _ hterm
  have hKsub' : covGam a e ∈ Work.FoldInst.Ksub (Work.RTOwed.kleinPt
      (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K) (Work.RTOwed.redV (Work.Cusp.cubeCusp a) K)) := by
    rw [hcubeOf, hredV]
    exact hKsub
  have hact : Work.FoldInst.actX (covGam a e)
      (Work.RTOwed.xbarOf (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K)
        (Work.RTOwed.kleinPt (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K)
          (Work.RTOwed.redV (Work.Cusp.cubeCusp a) K)) hmem) = x₀ := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [Work.FoldInst.actX_fst]
      show Work.RTOwed.cubeBit (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K) +
        (covGam a e).2 = x₀.1
      rw [hcubeOf]
      show Work.RTOwed.cubeBit (covB a e) + (covF a e : ZMod 2) = x₀.1
      rw [covData.2.2.1, hba]
    · rw [Work.FoldInst.actX_snd]
      show Work.FoldInst.act (covGam a e).1 (Work.RTOwed.kleinPt
        (Work.RTOwed.cubeOf (Work.Cusp.cubeCusp a) K)
        (Work.RTOwed.redV (Work.Cusp.cubeCusp a) K)) = x₀.2.1
      rw [hcubeOf, hredV, hpt, act_self]
  refine ⟨Work.Cusp.cubeCusp a, K, ?_⟩
  show Work.FoldInst.mk (Work.RTOwed.cuspPtX (Work.Cusp.cubeCusp a) K) = Work.FoldInst.mk x₀
  rw [Work.RTOwed.cuspPtX_of_mem (Work.Cusp.cubeCusp a) K hmem]
  exact Quotient.sound ⟨covGam a e, hKsub', hact⟩

end Work.RTOwed.cuspCert
