import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FieldTheory

open Polynomial

/-- In a domain of exponential characteristic `q`, the `q ^ m`-th power map on polynomials
is injective. -/
private lemma pow_expChar_pow_injective_poly {E : Type*} [Field E] (q m : ℕ) [ExpChar E q] :
    Function.Injective (fun x : Polynomial E => x ^ q ^ m) := by
  haveI : ExpChar (Polynomial E) q :=
    expChar_of_injective_algebraMap (Polynomial.C_injective (R := E)) q
  intro a b hab
  have hab' : a ^ q ^ m = b ^ q ^ m := hab
  have h1 := sub_pow_expChar_pow a b m (p := q)
  rw [hab', sub_self] at h1
  exact sub_eq_zero.mp ((pow_eq_zero_iff (expChar_pow_pos E q m).ne').mp h1)

theorem separable_perfectClosure_of_normal {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Normal F E] : Algebra.IsSeparable ↥(perfectClosure F E) E := by
  classical
  refine ⟨fun x => ?_⟩
  set q := ringExpChar F with hqdef
  haveI hFq : ExpChar F q := hqdef.symm ▸ ringExpChar.expChar F
  haveI hEq : ExpChar E q :=
    hqdef.symm ▸ expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
  set f : Polynomial F := minpoly F x with hfdef
  set fE : Polynomial E := f.map (algebraMap F E) with hfEdef
  have hxint : IsIntegral F x := IsIntegral.of_finite F x
  have hfmonic : f.Monic := minpoly.monic hxint
  have hfirred : Irreducible f := minpoly.irreducible hxint
  have hfEmonic : fE.Monic := hfmonic.map _
  have hfEsplits : fE.Splits := (inferInstance : Normal F E).splits' x
  -- separable contraction of the minimal polynomial
  set g : Polynomial F := (hfirred.hasSeparableContraction q).contraction with hgdef
  have hgsep : g.Separable := by
    rw [hgdef]; exact (hfirred.hasSeparableContraction q).isSeparableContraction.1
  obtain ⟨m, hgm⟩ := (hfirred.hasSeparableContraction q).isSeparableContraction.2
  have hgm' : Polynomial.expand F (q ^ m) g = f := by rw [hgdef]; exact hgm
  set gE : Polynomial E := g.map (algebraMap F E) with hgEdef
  have hgmE : Polynomial.expand E (q ^ m) gE = fE := by
    rw [hgEdef, ← Polynomial.map_expand, hgm', hfEdef]
  have hgEsep : gE.Separable := by
    rw [hgEdef]; exact Polynomial.Separable.map (f := algebraMap F E) hgsep
  have hgEmonic : gE.Monic := by
    rw [hgEdef]
    have h1 : (Polynomial.expand F (q ^ m) g).Monic := by rw [hgm']; exact hfmonic
    exact Polynomial.Monic.map (algebraMap F E) ((Polynomial.monic_expand_iff (expChar_pow_pos F q m)).mp h1)
  -- the "distinct root" polynomial of fE over E
  set S : Finset E := fE.roots.toFinset with hSdef
  set h : Polynomial E := ∏ r ∈ S, (Polynomial.X - Polynomial.C r) with hhdef
  have hsep : h.Separable := by
    rw [hhdef]
    exact (Polynomial.separable_prod_X_sub_C_iff' (f := fun r : E => r) (s := S)).mpr
      (fun a _ b _ hab => hab)
  -- multiplicities: every root of fE has multiplicity q ^ m
  have hScount : ∀ a, Multiset.count a S.val = if a ∈ S then 1 else 0 := by
    intro a
    have hSv : S.val = fE.roots.dedup := by rw [hSdef, Multiset.toFinset_val]
    rw [hSv, Multiset.count_dedup]
    by_cases hmem : a ∈ S
    · rw [if_pos (by rw [hSdef, Multiset.mem_toFinset] at hmem; exact hmem), if_pos hmem]
    · rw [if_neg (by rw [hSdef, Multiset.mem_toFinset] at hmem; exact hmem), if_neg hmem]
  have hroots : fE.roots = q ^ m • S.val := by
    refine Multiset.ext' (fun a => ?_)
    rw [Multiset.count_nsmul, hScount, Polynomial.count_roots, ← hgmE,
      Polynomial.rootMultiplicity_expand_pow]
    congr 1
    by_cases ha : a ∈ fE.roots
    · rw [if_pos (by rw [hSdef, Multiset.mem_toFinset]; exact ha)]
      have hroot : gE.IsRoot (a ^ q ^ m) := by
        have h1 : fE.IsRoot a := (Polynomial.mem_roots'.mp ha).2
        rw [Polynomial.IsRoot.def] at h1
        rw [Polynomial.IsRoot.def, ← Polynomial.expand_eval, hgmE]
        exact h1
      have hpos : 0 < gE.rootMultiplicity (a ^ q ^ m) :=
        (Polynomial.rootMultiplicity_pos hgEmonic.ne_zero).mpr hroot
      exact le_antisymm (Polynomial.rootMultiplicity_le_one_of_separable hgEsep _) hpos
    · rw [if_neg (by rw [hSdef, Multiset.mem_toFinset]; exact ha)]
      have hnr : ¬ gE.IsRoot (a ^ q ^ m) := by
        intro hc
        refine ha (Polynomial.mem_roots'.mpr ⟨hfEmonic.ne_zero, ?_⟩)
        rw [Polynomial.IsRoot.def]
        rw [Polynomial.IsRoot.def, ← Polynomial.expand_eval, hgmE] at hc
        exact hc
      exact Polynomial.rootMultiplicity_eq_zero hnr
  -- h ^ q ^ m = fE
  have hfEprod : fE = (Multiset.map (fun a => Polynomial.X - Polynomial.C a) fE.roots).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hfEmonic
      (Polynomial.splits_iff_card_roots.mp hfEsplits)).symm
  have hprod : h = (Multiset.map (fun a => Polynomial.X - Polynomial.C a) S.val).prod := by
    rw [hhdef, Finset.prod_eq_multiset_prod]
  have key : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) fE.roots).prod
      = h ^ q ^ m := by
    rw [hprod, hroots, Multiset.map_nsmul, Multiset.prod_nsmul]
  have hpow : h ^ q ^ m = fE := by
    rw [← key]; exact hfEprod.symm
  -- coefficients of h lie in the perfect closure
  have hiter : Polynomial.map (iterateFrobenius E q m) h = gE := by
    have h1 : Polynomial.map (iterateFrobenius E q m) (h ^ q ^ m)
        = Polynomial.map (iterateFrobenius E q m) fE := by rw [hpow]
    rw [Polynomial.map_pow, ← hgmE, Polynomial.map_iterateFrobenius_expand] at h1
    exact pow_expChar_pow_injective_poly q m h1
  have hmem : ∀ n, h.coeff n ∈ perfectClosure F E := by
    intro n
    rw [mem_perfectClosure_iff_pow_mem q]
    refine ⟨m, ?_⟩
    have hcoeff : h.coeff n ^ q ^ m = algebraMap F E (g.coeff n) := by
      rw [← iterateFrobenius_def, ← Polynomial.coeff_map, hiter, hgEdef, Polynomial.coeff_map]
    exact ⟨g.coeff n, hcoeff.symm⟩
  -- lift h to a polynomial over the perfect closure
  set hP : Polynomial ↥(perfectClosure F E) :=
    ∑ n ∈ h.support,
      Polynomial.C (⟨h.coeff n, hmem n⟩ : ↥(perfectClosure F E)) * Polynomial.X ^ n
    with hPdef
  have hPmap : Polynomial.map (algebraMap ↥(perfectClosure F E) E) hP = h := by
    rw [hPdef, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      IntermediateField.algebraMap_apply]
    simpa only [Polynomial.sum_def] using Polynomial.sum_C_mul_X_pow_eq h
  have hPsep : hP.Separable := by
    rw [← Polynomial.separable_map (algebraMap ↥(perfectClosure F E) E), hPmap]
    exact hsep
  have hxS : x ∈ S := by
    rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hfEmonic.ne_zero, ?_⟩
    rw [Polynomial.IsRoot.def, hfEdef, Polynomial.eval_map]
    simpa [Polynomial.aeval_def] using minpoly.aeval F x
  have heval : Polynomial.eval x h = 0 := by
    rw [hhdef, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero hxS (by simp)
  have haeval : Polynomial.aeval x hP = 0 := by
    rw [← Polynomial.aeval_map_algebraMap E x hP, hPmap]
    simpa [Polynomial.aeval_def] using heval
  exact Polynomial.Separable.of_dvd hPsep (minpoly.dvd ↥(perfectClosure F E) x haeval)

end Work.FieldTheory
