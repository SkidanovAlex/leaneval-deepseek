import Mathlib
import Submission.Work.Kunneth.exists_splitting_transparent
import Submission.Work.Kunneth.flatKunneth_exists
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.KunnethCross
import Submission.Work.Kunneth.CrossGen
import Submission.Work.Kunneth.homology_tpC_homSum
import Submission.Work.Kunneth.tpMap_homotopy

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Künneth isomorphism in its cross-product form

`Work.Kunneth.flatKunneth_exists` computes `H_n (C ⊗_ℤ M)` for a flat family `M`, and
`Work.Kunneth.exists_splitting_transparent` splits a complex `D` of projectives with projective
homology onto its homology complex `homSum D` by maps `π : D ⟶ homSum D`, `ι : homSum D ⟶ D`
with `ι ≫ π = 𝟙`, `π ≫ ι ≃ 𝟙` and `π` transparent on cycles.

This module assembles the two into the Künneth isomorphism for the tensor product of two
complexes:

`H_n (C ⊗ D) ≅ ⨁_{p+q=n} H_p(C) ⊗ H_q(D)`

*with its value rule*: on the class of the shuffle chain `u ⊗ v` of two cycles the isomorphism is
the cross product, i.e. the class of `u ⊗ v` in `H_n (C ⊗ D)`.

The isomorphism is the composite

`(⨁ H_p(C) ⊗ H_q(D)) --E.symm--> H_n (C ⊗ homSum D) --(myIso).symm--> H_n (C ⊗ D)`

where `E` is the flat Künneth isomorphism (`M q = D.homology q` is flat, being projective) and
`myIso` is the isomorphism induced by `tpMap 𝟙 π` (whose inverse is `tpMap 𝟙 ι`, by
`Work.Kunneth.tpMap_homotopy` and the splitting identities).

## Main result

* `Work.Kunneth.kunnethCrossExistence` — the Künneth isomorphism in cross-product form, with the
  value rule on the summand generators `[u] ⊗ [v]`.
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Künneth isomorphism of the cross product.**  For chain complexes `C`, `D` of
`ℤ`-modules with `D` projective in each degree and with projective homology, the cross product
`⨁_{p+q=n} H_p(C) ⊗ H_q(D) → H_n(C ⊗ D)` is an isomorphism.  Concretely: there is an isomorphism
`e` from `⨁_{p+q=n} H_p(C) ⊗ H_q(D)` to `H_n (C ⊗ D)` which on the summand generator
`[u] ⊗ [v]` (the class of a cycle `u` of `C` in degree `p` and a cycle `v` of `D` in degree `q`,
`p + q = n`) is the class of the shuffle chain `u ⊗ v` of `tpC C D`. -/
theorem kunnethCrossExistence (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ∃ e : (Work.Kunneth.tpC (Work.Kunneth.homSum C) (Work.Kunneth.homSum D)).X n ≅
        (Work.Kunneth.tpC C D).homology n,
      ∀ (p q : ℕ) (hpq : p + q = n) (u : ↥(C.cycles p)) (v : ↥(D.cycles q)),
        e.hom.hom (Work.Kunneth.crossSummandLof C D n p q hpq
            ((C.homologyπ p).hom u ⊗ₜ[ℤ] (D.homologyπ q).hom v))
          = ((Work.Kunneth.tpC C D).homologyπ n).hom
              (Work.Kunneth.crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v)) := by
  classical
  -- the family `M q = H_q(D)` is flat, being projective
  let M : ℕ → ModuleCat ℤ := fun q => D.homology q
  -- the transparent splitting of `D` onto its homology complex `sumShift M = homSum D`
  obtain ⟨π₀, ι₀, hιπ₀, ⟨Hh₀⟩, hπval₀⟩ := exists_splitting_transparent D hD hH
  let π : D ⟶ sumShift M := π₀
  let ι : sumShift M ⟶ D := ι₀
  have hιπ : ι ≫ π = 𝟙 (sumShift M) := hιπ₀
  have Hh : Homotopy (π ≫ ι) (𝟙 D) := Hh₀
  have hπval : ∀ (q : ℕ) (v : ↥(D.cycles q)),
      (π.f q).hom ((D.iCycles q).hom v) = (D.homologyπ q).hom v := hπval₀
  -- the flat Künneth isomorphism
  obtain ⟨E, hE⟩ := flatKunneth_exists C M (fun q => Module.Flat.of_projective) n
  -- `tpMap 𝟙 π` is an isomorphism on homology, with inverse induced by `tpMap 𝟙 ι`
  have h1 : homologyMap (tpMap C C D (sumShift M) (𝟙 C) π) n ≫
      homologyMap (tpMap C C (sumShift M) D (𝟙 C) ι) n = 𝟙 ((tpC C D).homology n) := by
    rw [← homologyMap_comp]
    have hcmp : tpMap C C D (sumShift M) (𝟙 C) π ≫ tpMap C C (sumShift M) D (𝟙 C) ι
        = tpMap C C D D (𝟙 C) (π ≫ ι) := by
      rw [tpMap_comp]
      simp
    rw [hcmp]
    obtain ⟨Ht⟩ := tpMap_homotopy C C D D (𝟙 C) (𝟙 C) (π ≫ ι) (𝟙 D) (Homotopy.refl _) Hh
    rw [Homotopy.homologyMap_eq Ht n]
    rw [show tpMap C C D D (𝟙 C) (𝟙 D) = 𝟙 (tpC C D) from tpMap_id C D]
    exact homologyMap_id (tpC C D) n
  have h2 : homologyMap (tpMap C C (sumShift M) D (𝟙 C) ι) n ≫
      homologyMap (tpMap C C D (sumShift M) (𝟙 C) π) n = 𝟙 ((tpC C (sumShift M)).homology n) := by
    rw [← homologyMap_comp]
    have hcmp : tpMap C C (sumShift M) D (𝟙 C) ι ≫ tpMap C C D (sumShift M) (𝟙 C) π
        = tpMap C C (sumShift M) (sumShift M) (𝟙 C) (𝟙 (sumShift M)) := by
      rw [tpMap_comp, hιπ]
      simp
    rw [hcmp, tpMap_id]
    exact homologyMap_id _ n
  let fwd : (tpC C D).homology n ⟶ (tpC C (sumShift M)).homology n :=
    homologyMap (tpMap C C D (sumShift M) (𝟙 C) π) n
  let bwd : (tpC C (sumShift M)).homology n ⟶ (tpC C D).homology n :=
    homologyMap (tpMap C C (sumShift M) D (𝟙 C) ι) n
  let myIso : (tpC C D).homology n ≅ (tpC C (sumShift M)).homology n := Iso.mk fwd bwd h1 h2
  refine ⟨E.symm ≪≫ myIso.symm, ?_⟩
  intro p q hpq u v
  -- the summand generator, its cycle and the target class
  set m : ↥((sumShift M).X q) := (D.homologyπ q).hom v with hm
  set Z : ↥((homTens C M).cycles n) := cycleOf (homTens C M) n (flatGen C M n p q hpq u m) with hZ
  set x : ↥((tpC (sumShift (fun p => C.homology p)) (sumShift M)).X n) :=
    crossSummandLof C D n p q hpq ((C.homologyπ p).hom u ⊗ₜ[ℤ] m) with hxel
  set rhs : ↥((tpC C D).homology n) :=
    ((tpC C D).homologyπ n).hom (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v)) with hrhs
  have hx : x = flatHT C M n p q hpq u m := by
    rw [hxel]; unfold flatHT; rfl
  -- the value rule of the flat Künneth isomorphism, and the inverse of `E`
  have hEz : E.hom.hom ((homTens C M).homologyπ n Z) = x := (hE p q hpq u m).trans hx.symm
  have hEx : (E.symm.hom).hom x = (homTens C M).homologyπ n Z := by
    rw [← hEz]; exact homIso_inv_apply E _
  -- the composite, on the element
  change (myIso.symm.hom).hom ((E.symm.hom).hom x) = rhs
  rw [hEx]
  change (homologyMap (tpMap C C (sumShift M) D (𝟙 C) ι) n).hom ((homTens C M).homologyπ n Z) = rhs
  rw [homologyMap_apply_homologyπ]
  -- the underlying chains of the two cycles
  have hZ₁ : ((tpC C D).iCycles n).hom (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v))
      = tpLof C D n ⟨(p,q),hpq⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] (D.iCycles q).hom v) := by
    rw [iCycles_crossCycTens, crossCycleMap_tmul]
  have hZ₂ : ((tpC C D).iCycles n).hom
        ((cyclesMap (tpMap C C (sumShift M) D (𝟙 C) ι) n).hom Z)
      = tpLof C D n ⟨(p,q),hpq⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] (ι.f q).hom m) := by
    rw [iCycles_cyclesMap]
    have h1' : ((tpC C (sumShift M)).iCycles n).hom Z = flatElem C M n p q hpq u m := by
      rw [hZ, iCycles_cycleOf, flatGen_val]
    rw [h1']
    unfold flatElem
    rw [tpMap_tmul]
    simp
  -- their difference is the shuffle chain of `u` and `iCycles v - ι [v]`
  have hdiff : ((tpC C D).iCycles n).hom (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v))
      - ((tpC C D).iCycles n).hom ((cyclesMap (tpMap C C (sumShift M) D (𝟙 C) ι) n).hom Z)
      = tpLof C D n ⟨(p,q),hpq⟩
          ((C.iCycles p).hom u ⊗ₜ[ℤ] ((D.iCycles q).hom v - (ι.f q).hom m)) := by
    rw [hZ₁, hZ₂, TensorProduct.tmul_sub, map_sub]
    try rfl
  -- `iCycles v` and `ι [v]` differ by a boundary, by the splitting homotopy
  obtain ⟨w, hw⟩ : ∃ w : ↥(D.X (q+1)),
      (D.d (q+1) q).hom w = (D.iCycles q).hom v - (ι.f q).hom m := by
    refine ⟨-((Hh.hom q (q+1)).hom ((D.iCycles q).hom v)), ?_⟩
    have hcomm := Homotopy_comm_apply' Hh q ((D.iCycles q).hom v)
    have hdx : (D.d q (q-1)).hom ((D.iCycles q).hom v) = 0 := d_iCycles D q v
    have hpi : ((π ≫ ι).f q).hom ((D.iCycles q).hom v) = (ι.f q).hom m := by
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hπval q v, hm]
    rw [hdx, hpi] at hcomm
    simp only [map_zero, add_zero] at hcomm
    rw [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] at hcomm
    rw [map_neg]
    have h2' : (D.d (q+1) q).hom ((Hh.hom q (q+1)).hom ((D.iCycles q).hom v))
        = (ι.f q).hom m - (D.iCycles q).hom v := by
      rw [hcomm]; abel
    rw [h2']; abel
  -- Koszul: the difference of the chains is a boundary of `tpC C D`
  have hpq1 : p + (q+1) = n+1 := by omega
  have htpd : tpLof C D n ⟨(p,q),hpq⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] (D.d (q+1) q).hom w)
      = (-1:ℤ)^p • tpD C D n
          (tpLof C D (n+1) ⟨(p,q+1), hpq1⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] w)) := by
    have h := tpLof_tmul_d_eq_smul_tpD C D n ⟨(p,q+1), hpq1⟩ (Nat.le_add_left 1 q)
      ((C.iCycles p).hom u) w (d_iCycles C p u)
    simpa using h
  have hbdry : ((tpC C D).iCycles n).hom (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v))
      - ((tpC C D).iCycles n).hom ((cyclesMap (tpMap C C (sumShift M) D (𝟙 C) ι) n).hom Z)
      = ((tpC C D).d (n+1) n).hom
          ((-1:ℤ)^p • tpLof C D (n+1) ⟨(p,q+1), hpq1⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] w)) := by
    rw [hdiff, ← hw, htpd, tpC_d C D n]
    exact (map_zsmul (tpD C D n) ((-1 : ℤ)^p)
      (tpLof C D (n+1) ⟨(p,q+1), hpq1⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] w))).symm
  -- two cycles with the same class have the same homology class
  exact (homologyπ_eq_of_sub_eq_d (tpC C D) n (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v))
      ((cyclesMap (tpMap C C (sumShift M) D (𝟙 C) ι) n).hom Z)
      ((-1:ℤ)^p • tpLof C D (n+1) ⟨(p,q+1), hpq1⟩ ((C.iCycles p).hom u ⊗ₜ[ℤ] w)) hbdry).symm

end

end Work.Kunneth
