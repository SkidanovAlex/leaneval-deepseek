import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.g1plus_iota
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "sum of the local values" decomposition of a globally paired class

This module supplies the *additive* half of the comparison "`χ ∘ pairK` = `Σ_v pair_v`" that the
counting lane and the design (`DESIGN_EXT.md` §2, `E9_STATUS.md` leg 2 + (a)) use in the annihilator
step, and that `Work.SSGRoute.PT.extLoc_yonedaPair`'s docstring describes as

> Reading the primitive square `extLoc_yonedaPair` place by place turns "the local components of a
> globally paired class" into "the sum of the local values", and this `glue`
> (`PT.exists_glue_extLoc`) is what lets a consumer write a class as the sum of its glued
> single-place components (the `Σ_v ι_v` of `DESIGN_EXT.md` §2), hence compare `χ ∘ pairK` with
> `Σ_v pair_v` in the annihilator step of the design's assembly bullet 2.

## What is proved here

Fix a number field `k`, a finite Galois `K/k`, a finite `𝔽_p[Gal(K/k)]`-module `M`, and a set `R` of
places of `K` meeting each `Gal(K/k)`-orbit exactly once (`hR` — the transversal of
`PT.ext_idele_shapiro` / `Work.SSGRoute.extIdele_localisation_injective`).

* `extLoc_sum`, `extLoc_neg`, `extLoc_sub` — additivity of the localisation, in the form needed to
  localise a *finite* sum.
* `eq_zero_of_extLoc_eq_zero_on_transversal` — a class of `H²(G, 𝕀_K)` vanishing at the places of
  `R` is `0` (the injectivity of the idèle localisation
  `Work.SSGRoute.extIdele_localisation_injective`, propagated along the conjugates of the
  representatives by `Work.SSGRoute.e9c_extLoc_conj_zero`).
* `eq_sum_iotaLift_of_extLoc_eq` — **the decomposition**: a class of `H²(G, 𝕀_K)` whose component
  family `a` is *finitely supported* is the sum of the orbit-insertions `ι_v (a v)`
  (`PT.iotaLift`, `PT.g1plus_iota.lean`).  This is the `Σ_v ι_v` identity of the design.
* `yonedaPair_eq_sum_iotaLift` — the same for a globally paired class:
  `z ⌣ h = Σ_{v ∈ T} ι_v ((z ⌣ h)_v)`, i.e. **a globally paired class is the sum of its local
  pairings placed at their orbits** — the additive form of "the sum of the local values".
* `extToClasses_sum`, `extToClasses_yonedaPair`, `pairK_eq_sum_iotaLift` — the class-formation images
  of the two sides, so that a coherent invariant `χ` (`PT.pt_coherent_pTorsion_invariant`) can be
  applied to both.

As everywhere in this comparison, the *finiteness* of the sum outside `T` is the vanishing of the
local pairings of the **unramified** components, which is clause (6) of the canonical local pairing
(`horth` of `G1⁺`; `PT.Pipeline.cupFam_clause6` for the cup family).  That vanishing is taken here
as the hypothesis `hT`; it is the only extra input.
-/

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

section Additivity

variable {M : Rep.{0} Coeff (K ≃ₐ[k] K)}

/-- `extLoc` is additive over finite sums (localisation is additive, `PT.extLoc_add`). -/
theorem extLoc_sum {r : ℕ} (w : NK.GlobalCFT.Place K) {ι : Type} (s : Finset ι)
    (f : ι → Abelian.Ext.{0} M (idelesK k K) r) :
    extLoc (k := k) w (∑ i ∈ s, f i) = ∑ i ∈ s, extLoc (k := k) w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [extLoc_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, extLoc_add, ih]

/-- The negative of a localisation is the localisation of the negative. -/
theorem extLoc_neg {r : ℕ} (w : NK.GlobalCFT.Place K)
    (x : Abelian.Ext.{0} M (idelesK k K) r) :
    extLoc (k := k) w (-x) = -extLoc (k := k) w x := by
  have h := extLoc_add (k := k) (K := K) w (-x) x
  rw [neg_add_cancel, extLoc_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Localisation is compatible with subtraction. -/
theorem extLoc_sub {r : ℕ} (w : NK.GlobalCFT.Place K)
    (x y : Abelian.Ext.{0} M (idelesK k K) r) :
    extLoc (k := k) w (x - y) = extLoc (k := k) w x - extLoc (k := k) w y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, extLoc_add, extLoc_neg]

end Additivity

section Transversal

/-- A place of a transversal `R` conjugate to another place of `R` *is* that place (two places of a
transversal lying in the same `Gal(K/k)`-orbit coincide). -/
theorem eq_of_smul_eq_of_mem_transversal (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    {v w : R} (σ : K ≃ₐ[k] K) (hσ : σ • w.1 = v.1) : v = w := by
  obtain ⟨w', _hP, huniq⟩ := hR w.1
  exact (huniq v ⟨σ, hσ⟩).trans (huniq w ⟨1, one_smul _ _⟩).symm

/-- **A class of `H²(G, 𝕀_K)` vanishing at the places of a transversal is zero.**  This is the
injectivity of the idèle localisation `Work.SSGRoute.extIdele_localisation_injective`, transported
from the representatives to all places by the conjugation of local vanishing
(`Work.SSGRoute.e9c_extLoc_conj_zero`). -/
theorem eq_zero_of_extLoc_eq_zero_on_transversal (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    {y : extH (idelesK k K) 2}
    (h : ∀ w : R, extLoc (k := k) w.1 y = 0) : y = 0 := by
  classical
  refine Work.SSGRoute.extIdele_localisation_injective k K y (fun v => ?_)
  rw [Work.SSGRoute.extRes_eq_extHRestrict (D := decompK (k := k) v) y]
  change extLoc (k := k) v y = 0
  obtain ⟨w', hP, _huniq⟩ := hR v
  obtain ⟨σ, hσ⟩ := hP
  have hv : σ⁻¹ • w'.1 = v := by rw [← hσ]; simp
  rw [← hv]
  exact Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := K) y σ⁻¹ w'.1 (h w')

end Transversal

section Decomposition

/-- **The decomposition of a class with finitely supported components.**  Let `x ∈ H²(G, 𝕀_K)`
vanish at every place of the transversal `R` outside a finite set `T ⊆ R`.  Then `x` is the
(finite) sum of the orbit-insertions `ι_v` of its own local components:

  `x = Σ_{v ∈ T} ι_v (x_v)`.

This is the `Σ_v ι_v` identity of `DESIGN_EXT.md` §2: the class carried by a finitely supported
family of local components *is* the sum of the single-place classes placed at their orbits. -/
theorem eq_sum_iotaLift_of_extLoc_eq_zero_off (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (x : extH (idelesK k K) 2) (T : Finset R)
    (hT : ∀ w : R, w ∉ T → extLoc (k := k) w.1 x = 0) :
    x = ∑ w ∈ T, iotaLift (k := k) (L := K) w.1 (extLoc (k := k) w.1 x) := by
  classical
  have hzero : ∀ w : R, extLoc (k := k) w.1
      (x - ∑ v ∈ T, iotaLift (k := k) (L := K) v.1 (extLoc (k := k) v.1 x)) = 0 := by
    intro w
    have h1 : extLoc (k := k) w.1
        (x - ∑ v ∈ T, iotaLift (k := k) (L := K) v.1 (extLoc (k := k) v.1 x))
        = extLoc (k := k) w.1 x - ∑ v ∈ T, extLoc (k := k) w.1
            (iotaLift (k := k) (L := K) v.1 (extLoc (k := k) v.1 x)) := by
      rw [extLoc_sub, extLoc_sum]
    rw [h1]
    by_cases hw : w ∈ T
    · have hsum : (∑ v ∈ T, extLoc (k := k) w.1
          (iotaLift (k := k) (L := K) v.1 (extLoc (k := k) v.1 x)))
          = extLoc (k := k) w.1 x := by
        refine (Finset.sum_eq_single w ?_ ?_).trans
          (iotaLift_spec (k := k) (L := K) w.1 (extLoc (k := k) w.1 x)).1
        · intro b _ hbw
          refine (iotaLift_spec (k := k) (L := K) b.1 (extLoc (k := k) b.1 x)).2 w.1
            (fun σ hσ => ?_)
          exact hbw (eq_of_smul_eq_of_mem_transversal R hR σ hσ).symm
        · intro h; exact absurd hw h
      rw [hsum, sub_self]
    · have hsum : (∑ v ∈ T, extLoc (k := k) w.1
          (iotaLift (k := k) (L := K) v.1 (extLoc (k := k) v.1 x))) = 0 :=
        Finset.sum_eq_zero (fun b hb => by
          refine (iotaLift_spec (k := k) (L := K) b.1 (extLoc (k := k) b.1 x)).2 w.1
            (fun σ hσ => ?_)
          exact hw ((eq_of_smul_eq_of_mem_transversal R hR σ hσ).symm ▸ hb))
      rw [hsum, hT w hw, sub_zero]
  exact sub_eq_zero.mp (eq_zero_of_extLoc_eq_zero_on_transversal R hR hzero)

/-- **The sum of the local values of a globally paired class.**  For `z ∈ Ext¹_G(M, 𝕀_K)` and
`h ∈ H¹(G, M)`, if the local pairings `(z ⌣ h)_v` vanish outside a finite set `T` of representatives,
then the globally paired class `z ⌣ h` is the sum of the orbit-insertions of its local pairings:

  `z ⌣ h = Σ_{v ∈ T} ι_v ((z ⌣ h)_v)`.

The local pairings `(z ⌣ h)_v = yonedaPair (extLoc v z) (extHRestrict D_v h)` are the `v`-components
of `z ⌣ h` by the proved `PT.extLoc_yonedaPair`; the vanishing outside `T` is clause (6) of the
canonical local pairing (`horth` of `G1⁺`; `PT.Pipeline.cupFam_clause6` for the cup family) at the
places where both local classes are unramified. -/
theorem yonedaPair_eq_sum_iotaLift {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (z : Abelian.Ext.{0} M (idelesK k K) 1) (h : extH M 1)
    (T : Finset R)
    (hT : ∀ w : R, w ∉ T →
      yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h) = 0) :
    yonedaPair z h = ∑ w ∈ T, iotaLift (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h)) := by
  classical
  rw [eq_sum_iotaLift_of_extLoc_eq_zero_off R hR (yonedaPair z h) T (fun w hw => by
    rw [extLoc_yonedaPair]; exact hT w hw)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [extLoc_yonedaPair]

/-- The class-formation image of a finite sum is the sum of the images. -/
theorem extToClasses_sum {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {ι : Type} {r : ℕ} (s : Finset ι)
    (f : ι → Abelian.Ext.{0} M (idelesK k K) r) :
    extToClasses (∑ i ∈ s, f i) = ∑ i ∈ s, extToClasses (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [extToClasses_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, extToClasses_add, ih]

/-- The class-formation image of a globally paired class is the Yoneda product of the images
(functoriality of `pairK = yonedaPair` under the coefficient map `𝕀_K → C_K`). -/
theorem extToClasses_yonedaPair {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (z : Abelian.Ext.{0} M (idelesK k K) 1) (h : extH M 1) :
    pairK (extToClasses z) h = extToClasses (yonedaPair z h) := by
  simp only [pairK, extToClasses]
  rw [yonedaPair_comp z (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) h]

/-- **The `C_K`-valued form of the sum of the local values**: the globally paired class
`pairK (extToClasses z) h` is the sum of the orbit-insertions `ι_v` of the local pairings. -/
theorem pairK_eq_sum_iotaLift {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (z : Abelian.Ext.{0} M (idelesK k K) 1) (h : extH M 1)
    (T : Finset R)
    (hT : ∀ w : R, w ∉ T →
      yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h) = 0) :
    pairK (extToClasses z) h = ∑ w ∈ T, iota (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h)) := by
  classical
  rw [extToClasses_yonedaPair z h, yonedaPair_eq_sum_iotaLift R hR z h T hT, extToClasses_sum]
  exact Finset.sum_congr rfl (fun w _ => rfl)

/-- **Additivity of an invariant along a finite sum.**  If `χ` is additive on `p`-torsion (the two
clauses of the first component of `PT.pt_coherent_pTorsion_invariant`) and every value of `f` is
`p`-torsion, then `χ` of the finite sum is the sum of the `χ`-values.  (The lemma also produces the
`p`-torsion of the intermediate sums, which is what makes the induction go through.) -/
theorem chi_finset_sum (p : ℕ) {ι : Type}
    (χ : extH (classesK k K) 2 → ZMod p)
    (hχadd : ∀ u v : extH (classesK k K) 2, p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (s : Finset ι) (f : ι → extH (classesK k K) 2) (hp : ∀ i ∈ s, p • f i = 0) :
    χ (∑ i ∈ s, f i) = ∑ i ∈ s, χ (f i) := by
  classical
  have hχ0 : χ 0 = 0 := by
    have h : χ 0 = χ 0 + χ 0 := by simpa using hχadd 0 0 (by simp) (by simp)
    have h2 := congrArg (fun x => x - χ 0) h
    simpa using h2.symm
  have key : ∀ s : Finset ι, (∀ i ∈ s, p • f i = 0) →
      p • (∑ i ∈ s, f i) = 0 ∧ χ (∑ i ∈ s, f i) = ∑ i ∈ s, χ (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨by simp, by simp [hχ0]⟩
    | insert a s ha ih =>
        intro hs
        have hs' : ∀ i ∈ s, p • f i = 0 := fun i hi => hs i (Finset.mem_insert_of_mem hi)
        obtain ⟨hsum, hchi⟩ := ih hs'
        have ha' : p • f a = 0 := hs a (Finset.mem_insert_self a s)
        refine ⟨?_, ?_⟩
        · rw [Finset.sum_insert ha, nsmul_add, ha', hsum, add_zero]
        · rw [Finset.sum_insert ha, Finset.sum_insert ha,
            hχadd _ _ ha' hsum, hchi]
  exact (key s hp).2

/-- **The sum of the local invariants of a globally paired class.**  Composing the class-level
decomposition `PT.pairK_eq_sum_iotaLift` with the additivity of a coherent invariant `χ`
(`PT.pt_coherent_pTorsion_invariant`) gives the identity

  `χ (pairK (extToClasses z) h) = Σ_{v ∈ T} χ (ι_v ((z ⌣ h)_v))`

used in the annihilator step ("the global value of a pair is the sum of its local values").  The
hypotheses `hT` are the vanishing of the local pairings of the unramified components (clause (6) of
the canonical local pairing) and `hp` is the `p`-torsion-ness of the local values. -/
theorem chi_pairK_eq_sum_iota (p : ℕ) {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (χ : extH (classesK k K) 2 → ZMod p)
    (hχadd : ∀ u v : extH (classesK k K) 2, p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (z : Abelian.Ext.{0} M (idelesK k K) 1) (h : extH M 1)
    (T : Finset R)
    (hT : ∀ w : R, w ∉ T →
      yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h) = 0)
    (hp : ∀ w : R, p • iota (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h)) = 0) :
    χ (pairK (extToClasses z) h) = ∑ w ∈ T, χ (iota (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 z) (extHRestrict (decompK (k := k) w.1) h))) := by
  classical
  rw [pairK_eq_sum_iotaLift R hR z h T hT]
  exact chi_finset_sum p χ hχadd T _ (fun w _ => hp w)

/-- `χ 0 = 0` for an invariant additive on `p`-torsion. -/
theorem chi_zero_of_additive (p : ℕ) (χ : extH (classesK k K) 2 → ZMod p)
    (hχadd : ∀ u v : extH (classesK k K) 2, p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v) :
    χ 0 = 0 := by
  have h : χ 0 = χ 0 + χ 0 := by simpa using hχadd 0 0 (by simp) (by simp)
  have h2 := congrArg (fun x => x - χ 0) h
  simpa using h2.symm

/-- **Reciprocity ("the sum of the local values of a global pair is zero") in the form the design
uses.**  If `z` is the localisation of a `Kˣ`-valued class (`z = extToIdeles z₀`), then the global
paired class in `H²(G, C_K)` is `0` (`PT.pairK_extToClasses_extToIdeles_zero`, the exactness
`Kˣ → 𝕀_K → C_K`), so by `PT.chi_pairK_eq_sum_iota` the sum of the `χ`-values of the local pairings,
placed at their orbits by `ι_v`, vanishes:

  `Σ_{v ∈ T} χ (ι_v ((z ⌣ h)_v)) = 0`.

This is the reciprocity clause of the canonical local pairing, *derived* from clause (6)
(`hT`, the vanishing of the local pairings at the unramified places) and the class formation — no
further arithmetic. -/
theorem sum_chi_iota_eq_zero_of_extToIdeles (p : ℕ) {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (χ : extH (classesK k K) 2 → ZMod p)
    (hχadd : ∀ u v : extH (classesK k K) 2, p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (z : Abelian.Ext.{0} M (unitsK k K) 1) (h : extH M 1)
    (T : Finset R)
    (hT : ∀ w : R, w ∉ T → yonedaPair (extLoc (k := k) w.1 (extToIdeles z))
      (extHRestrict (decompK (k := k) w.1) h) = 0)
    (hp : ∀ w : R, p • iota (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 (extToIdeles z))
        (extHRestrict (decompK (k := k) w.1) h)) = 0) :
    ∑ w ∈ T, χ (iota (k := k) (L := K) w.1
      (yonedaPair (extLoc (k := k) w.1 (extToIdeles z))
        (extHRestrict (decompK (k := k) w.1) h))) = 0 := by
  classical
  rw [← chi_pairK_eq_sum_iota p χ hχadd R hR (extToIdeles z) h T hT hp,
    pairK_extToClasses_extToIdeles_zero]
  exact chi_zero_of_additive p χ hχadd

end Decomposition

end

end Work.SSGRoute.PT
