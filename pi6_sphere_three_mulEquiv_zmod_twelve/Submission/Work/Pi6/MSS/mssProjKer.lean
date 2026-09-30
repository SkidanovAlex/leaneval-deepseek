import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The kernel of the projection `ker d_r → E_{r+1}` of the concrete Serre spectral sequence

This file proves `Work.Pi6.MSS.mssProjKer`, the `proj_ker` clause of the interface
`Work.Pi6.CohSS` for the concrete multiplicative cohomological Serre spectral sequence
`Work.Pi6.MSS.mssD`/`mssE`/`mssProj` of a filtered cochain complex with a product
`W : Work.Pi6.MSS.CohFilt 𝕜`:

the kernel of the projection `ker d_r^{a} → E_{r+1}^{a}` is the image of the incoming differential
`d_r : E_r^{a - (r, 1-r)} → E_r^{a}`.

The proof is a case analysis on the bidegree `a = (a.1, a.2)`.

* If `a` is off the first quadrant (`¬ Enn a`) then `E_r^{a}` is a subsingleton
  (`subsingleton_mssE`) and both sides of the equivalence hold trivially.
* If `a` is in the first quadrant but `a - vr r` is not, then `EI a < r` and the incoming
  differential vanishes; both sides degenerate to `x = 0`, using
  `pd_proj_injective_low` for the left-hand side.
* In the honest case (`Enn a` and `Enn (a - vr r)`) the statement is the concrete page lemma
  `pd_proj_ker` of `Submission/Work/Pi6/MSS/pagesData.lean`, after identifying the
  bidegree-indexed differential `mssD` with `pD` up to the index casts (`mssD_eq_pD`).
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Transport lemmas for the bidegree-indexed pages -/

/-- The index cast `eqToHom` of the bidegree-indexed differentials is the composite of the cast of
the concrete pages `pEcast` and the `eqToHom` of the bidegree.

This is the comparison between the two ways of composing the casts
`pEraw r (EI (a - vr r) + r) (EN (a - vr r) + 1) → pEraw r (EI a) (EN a)`:
first to the bidegree `(a - vr r) + vr r` (which is `a` only up to a propositional equality) and
then along that equality, or directly along `hs`/`hn`.  All these casts are `Eq.rec`s along
equalities of the same pair of types, so the comparison is proof irrelevance of the equalities. -/
lemma keyCast_mor (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) (a : ℤ × ℤ)
    (ha : Enn (a - vr r)) (hb : Enn ((a - vr r) + vr r))
    (h : a = (a - vr r) + vr r)
    (hs : EI (a - vr r) + r = EI a) (hn : EN (a - vr r) + 1 = EN a) :
    (pEcast 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha)).hom ≫
        CategoryTheory.eqToHom (congrArg (mssE 𝕜 W r) h.symm)
      = (pEcast 𝕜 W r hs hn).hom := by
  set q₂ : pEraw 𝕜 W r (EI (a - vr r) + r) (EN (a - vr r) + 1)
        = pEraw 𝕜 W r (EI ((a - vr r) + vr r)) (EN ((a - vr r) + vr r)) :=
    (show pEraw 𝕜 W r (EI (a - vr r) + r) (EN (a - vr r) + 1)
        = pEraw 𝕜 W r (EI ((a - vr r) + vr r)) (EN ((a - vr r) + vr r)) from by
      rw [EI_add_vr r ha hb, EN_add_vr r ha])
  have hp₂ : (pEcast 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha)).hom
      = CategoryTheory.eqToHom q₂ := by
    rw [pEcast, CategoryTheory.eqToIso.hom]
  rw [hp₂, CategoryTheory.eqToHom_trans]
  congr 1

/-- **The bidegree-indexed differential is the concrete differential up to the index cast.**
In the honest case the incoming differential `mssD r (a - vr r) a` is the concrete page
differential `pD r (EI (a - vr r)) (EN (a - vr r))` composed with the cast `pEcast hs hn`. -/
lemma mssD_eq_pD (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r : ℕ) (a : ℤ × ℤ)
    (ha : Enn (a - vr r)) (hb : Enn a)
    (hs : EI (a - vr r) + r = EI a) (hn : EN (a - vr r) + 1 = EN a) :
    mssD 𝕜 W r (a - vr r) a
      = pD 𝕜 W r (EI (a - vr r)) (EN (a - vr r)) ≫ (pEcast 𝕜 W r hs hn).hom := by
  have h : a = (a - vr r) + vr r := (sub_add_cancel a (vr r)).symm
  have hb' : Enn ((a - vr r) + vr r) := by rw [← h]; exact hb
  rw [mssD, dite_eq_left h, mssDMain_pos 𝕜 W r ha hb', mssDStep, Category.assoc]
  congr 1
  exact keyCast_mor 𝕜 W r a ha hb' h hs hn

/-- `(a - vr r) + r = a` in the filtration degree. -/
lemma EI_sub_vr_add (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a - vr r)) :
    EI (a - vr r) + r = EI a := by
  have h := EI_sub_vr r ha hb
  have h2 : r ≤ EI a := by
    have h3 := hb.1; rw [fst_sub_vr] at h3
    rw [Enn_of_nonneg ha]
    exact (Int.le_toNat ha.1).mpr (by linarith)
  omega

/-- `(a - vr r) + 1 = a` in the total degree. -/
lemma EN_sub_vr_add (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a - vr r)) :
    EN (a - vr r) + 1 = EN a := by
  have h := EN_sub_vr r ha hb
  have h2 : 1 ≤ EN a := by
    rw [EN_of_nonneg ha]
    have h3 : (1 : ℤ) ≤ a.1 + a.2 := by
      have h4 := sub_vr_sum a r
      have h5 := hb.1
      have h6 := hb.2
      linarith
    exact (Int.le_toNat (by linarith [ha.1, ha.2])).mpr (by exact_mod_cast h3)
  omega

/-! ## The projection `ker d_r → E_{r+1}` -/

theorem mssProjKer (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (r : ℕ) (a : ℤ × ℤ)
    (hr : 2 ≤ r) (x : ↥(LinearMap.ker (Work.Pi6.MSS.mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom)) :
    Work.Pi6.MSS.mssProj 𝕜 W r a x = 0
      ↔ (x : Work.Pi6.MSS.mssE 𝕜 W r a)
          ∈ LinearMap.range (Work.Pi6.MSS.mssD 𝕜 W r (a - Work.Pi6.vr r) a).hom := by
  have hL : mssProj 𝕜 W r a x = pd_proj 𝕜 W r (EI a) (EN a)
      ⟨x.1, mssProjAux_mem 𝕜 W r hr a (mssKerIncl 𝕜 W r a x)⟩ := by
    rw [mssProj, dite_eq_left hr]; rfl
  by_cases ha : Enn a
  · by_cases ha' : Enn (a - vr r)
    · -- honest case: `pd_proj_ker` for the concrete pages
      have hs : EI (a - vr r) + r = EI a := EI_sub_vr_add r ha ha'
      have hn : EN (a - vr r) + 1 = EN a := EN_sub_vr_add r ha ha'
      have hRange : (x.1 : mssE 𝕜 W r a) ∈
          LinearMap.range (mssD 𝕜 W r (a - vr r) a).hom ↔
          ∃ w : pEraw 𝕜 W r (EI (a - vr r)) (EN (a - vr r)),
            (pEcast 𝕜 W r hs hn).hom
              ((pD 𝕜 W r (EI (a - vr r)) (EN (a - vr r))).hom w) = x.1 := by
        rw [mssD_eq_pD 𝕜 W r a ha' ha hs hn]
        simp only [ModuleCat.hom_comp, LinearMap.mem_range, LinearMap.comp_apply]
      rw [hL, hRange]
      exact pd_proj_ker r (EI a) (EN a) hr (EI (a - vr r)) (EN (a - vr r)) hs hn _
    · -- `a` in the first quadrant but `a - vr r` not: the incoming differential is zero
      have hEIltr : EI a < r := by
        have h1 : (a - vr r).2 = a.2 + (r : ℤ) - 1 := by rw [snd_sub_vr]; ring
        have h2 : ¬ (a - vr r).2 < 0 := by rw [h1]; linarith [ha.2]
        have h3 : (a - vr r).1 < 0 := by
          rcases lt_or_ge (a - vr r).1 0 with h | h
          · exact h
          · exact absurd ⟨h, not_lt.mp h2⟩ ha'
        rw [fst_sub_vr] at h3
        rw [Enn_of_nonneg ha]
        have h4 : ((a.1.toNat : ℤ)) = a.1 := Int.toNat_of_nonneg ha.1
        omega
      have hL0 : mssProj 𝕜 W r a x = 0 ↔ (x.1 : mssE 𝕜 W r a) = 0 := by
        rw [hL, ← map_zero (pd_proj 𝕜 W r (EI a) (EN a)),
            (pd_proj_injective_low 𝕜 W r (EI a) (EN a) hr hEIltr).eq_iff]
        exact Subtype.ext_iff
      have hR0 : (x.1 : mssE 𝕜 W r a) ∈ LinearMap.range (mssD 𝕜 W r (a - vr r) a).hom
          ↔ (x.1 : mssE 𝕜 W r a) = 0 := by
        have hm : mssD 𝕜 W r (a - vr r) a = 0 := by
          have h : a = (a - vr r) + vr r := (sub_add_cancel a (vr r)).symm
          rw [mssD, dite_eq_left h, mssDMain_neg 𝕜 W r ha']
          simp
        rw [hm]
        simp
      rw [hL0, hR0]
  · -- off the first quadrant: the page is a subsingleton and both sides hold
    have hsub1 : Subsingleton (mssE 𝕜 W r a) := subsingleton_mssE 𝕜 W r ha
    have hsub2 : Subsingleton (mssE 𝕜 W (r + 1) a) := subsingleton_mssE 𝕜 W (r + 1) ha
    have hx0 : (x : mssE 𝕜 W r a) = 0 := hsub1.elim _ _
    constructor
    · intro _
      rw [hx0]
      exact zero_mem _
    · intro _
      exact hsub2.elim _ _

end

end Work.Pi6.MSS
