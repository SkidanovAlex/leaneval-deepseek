import Mathlib
import Submission.Work.KeyLemma.Curve.BranchSum.Core
import Submission.Work.KeyLemma.Curve.card_branches_fixed
import Submission.Work.CurveBasics.Order.sum_ord_pos_eq_finrank_general
import Submission.Work.Charts.place_degree_eq_one_of_isAlgClosed
import Submission.Work.KeyLemma.Place.exists_point_of_degree_one
import Submission.Work.KeyLemma.Curve.BranchSumF.transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve.BranchSum

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

universe u

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

/-- The numbers of indices mapping to each `b ∈ S` add up to the total number of indices,
provided every value of `f` lies in `S`. -/
private lemma card_fiber_sum {J β : Type*} [Fintype J] [DecidableEq β]
    (f : J → β) (S : Finset β) (hS : ∀ i, f i ∈ S) :
    ∑ b ∈ S, ((Finset.univ.filter (fun i => f i = b)).card : ℤ) = (Fintype.card J : ℤ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset J)) (t := S) (f := f)
    (fun i _ => hS i)
  rw [Finset.card_univ] at h
  have h' : (∑ b ∈ S, (Finset.univ.filter (fun i => f i = b)).card) = Fintype.card J := h.symm
  rw [← Nat.cast_sum, h']

/-- If `c`, `o : β → ℤ` have the same total sum over `S`, respectively `Z ⊆ S`, if `c` is
non-negative and `o` is bounded above by `c` on `Z`, then `c = o` on `Z` and `c` vanishes
on `S \ Z`. -/
private lemma finset_combination {β : Type*} [DecidableEq β]
    (c o : β → ℤ) (Z S : Finset β) (T : ℤ) (hZS : Z ⊆ S)
    (hsumS : ∑ b ∈ S, c b = T) (hsumZ : ∑ b ∈ Z, o b = T)
    (hc0 : ∀ b, 0 ≤ c b) (hle : ∀ b ∈ Z, o b ≤ c b) :
    (∀ b ∈ Z, c b = o b) ∧ (∀ b ∈ S \ Z, c b = 0) := by
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hZS (fun b _ _ => hc0 b)
  have h1' : ∑ b ∈ Z, c b ≤ T := by rwa [hsumS] at h1
  have h2 : ∑ b ∈ Z, o b ≤ ∑ b ∈ Z, c b := Finset.sum_le_sum (fun b hb => hle b hb)
  have hle1 : ∑ b ∈ Z, c b ≤ ∑ b ∈ Z, o b := h1'.trans (le_of_eq hsumZ.symm)
  have hEq : ∑ b ∈ Z, c b = ∑ b ∈ Z, o b := le_antisymm hle1 h2
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact ((Finset.sum_eq_sum_iff_of_le (fun b hb => hle b hb)).mp hEq.symm b hb).symm
  · have hsd := Finset.sum_sdiff hZS (f := c)
    have h0 : ∑ b ∈ S \ Z, c b = 0 := by linarith [hsd, hsumS, hEq, hsumZ]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hc0 b)).mp h0 b hb

theorem multiset_eq_posPart {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (hht : Transcendental k h)
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [algK : Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N]
    [algE : Algebra ↥C.functionField N]
    [finKN : FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥(Work.CurveBasics.Curve.ordBase C h) N]
    [IsScalarTower ↥(Work.CurveBasics.Curve.ordBase C h)
      ↥(Work.KeyLemma.Curve.baseField C h) N]
    (hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField))
    (hAE : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField))
    [IsFractionRing ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N]
    (P : Ideal ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)) [P.IsPrime]
    [P.LiesOver (Work.CurveBasics.Curve.ordIdeal C h)]
    (Qσ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) → C.Place)
    (hQσ : ∀ (σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N)
      (Q : C.Place) (hQ : 0 < C.ordAt h Q),
      (∀ x ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le, ∃ c ∈ P,
        algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N c
          = σ (algebraMap ↥(C.ordClosure h) ↥C.functionField x)) → Qσ σ = Q) :
    (∑ σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N,
        Finsupp.single (Qσ σ) 1) = posPart C h := by
  -- canonical `SMul` structures (they shadow the ambient `IntermediateField` ones)
  letI hSMK : SMul ↥(Work.KeyLemma.Curve.baseField C h) N :=
    Algebra.toSMul (R := ↥(Work.KeyLemma.Curve.baseField C h)) (A := N)
  letI hSMA : SMul ↥(Work.CurveBasics.Curve.ordBase C h) N :=
    Algebra.toSMul (R := ↥(Work.CurveBasics.Curve.ordBase C h)) (A := N)
  letI hSMAK : SMul ↥(Work.CurveBasics.Curve.ordBase C h)
      ↥(Work.KeyLemma.Curve.baseField C h) :=
    Algebra.toSMul (R := ↥(Work.CurveBasics.Curve.ordBase C h))
      (A := ↥(Work.KeyLemma.Curve.baseField C h))
  haveI hSTAKcan : IsScalarTower ↥(Work.CurveBasics.Curve.ordBase C h)
      ↥(Work.KeyLemma.Curve.baseField C h) N :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [hAE, hKE, RingHom.comp_apply, RingHom.comp_apply]
      exact congrArg (algebraMap ↥C.functionField N)
        (Work.KeyLemma.Curve.algebraMap_ordBase_baseField k C h x))
  haveI hFDcan : @FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N _ _
      (@Algebra.toModule ↥(Work.KeyLemma.Curve.baseField C h) N _ _ algK) :=
    Work.KeyLemma.Curve.BranchSum.finiteDimensional_canon
      (k := k) (L := ↥C.functionField) (akL := inferInstance)
      (K := Work.KeyLemma.Curve.baseField C h) (algK := algK) (algL := algE)
      (hKE := hKE) (finKN := finKN)
  classical
  haveI hSMord : SMul ↥(Work.CurveBasics.Curve.ordBase C h)
      ↥(Work.KeyLemma.Curve.baseField C h) := Algebra.toSMul
  let Z : Finset C.Place := (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q)
  have hZdef : Z = (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q) := rfl
  let cf : C.Place → ℤ := fun Q => ((Finset.univ.filter (fun σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) => Qσ σ = Q)).card : ℤ)
  let S : Finset C.Place := Finset.univ.image Qσ ∪ Z
  have hLHS : ∀ Q : C.Place, (∑ σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N), Finsupp.single (Qσ σ) 1) Q = cf Q := by
    intro Q
    simp only [cf]
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_boole]
  have hS : ∀ σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N), Qσ σ ∈ S := by
    intro σ
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨σ, rfl⟩
  have hZS : Z ⊆ S := by
    intro Q hQ
    simp only [S, Finset.mem_union]
    exact Or.inr hQ
  have hc0 : ∀ Q : C.Place, 0 ≤ cf Q := by
    intro Q
    simp only [cf]
    exact Int.natCast_nonneg _
  have hcountZ : ∑ Q ∈ Z, C.ordAt h Q = (Fintype.card (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) : ℤ) := by
    have hgen := Work.CurveBasics.Order.sum_ord_pos_eq_finrank_general C h hht
    have hres : ∀ Q : C.Place, C.hom.residueDegree Q.point = 1 :=
      fun Q => Work.Charts.place_degree_eq_one_of_isAlgClosed C Q
    have hZ1 :
        ∑ Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q),
            C.ordAt h Q * (C.hom.residueDegree Q.point : ℤ)
          = ∑ Q ∈ (C.finite_support_ordAt h).toFinset.filter (fun Q => 0 < C.ordAt h Q),
            C.ordAt h Q := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [hres Q]
      ring
    rw [hZ1] at hgen
    rw [← hZdef] at hgen
    rw [hgen]
    have hfin := Work.KeyLemma.Curve.card_algHom_functionField C h hKE
    rw [← Nat.card_eq_fintype_card]
    rw [← hfin]
  have hlower : ∀ Q ∈ Z, C.ordAt h Q ≤ cf Q := by
    intro Q hQZ
    have hQpos : 0 < C.ordAt h Q := by
      have h2 := hQZ
      simp only [Z, Finset.mem_filter] at h2
      exact h2.2
    let p : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) → Prop := fun σ => ∀ x ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQpos.le,
      ∃ c ∈ P, algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N c
        = σ (algebraMap ↥(C.ordClosure h) ↥C.functionField x)
    have hbf := Work.KeyLemma.Curve.card_branches_fixed (C := C) (h := h) (hh := hht)
      (N := N) (hKE := hKE) (hAE := hAE) (P := P) (Q := Q) (hQ := hQpos)
    have hXcard : (Finset.univ.filter p).card = (C.ordAt h Q).toNat := by
      rw [← Fintype.card_subtype (p := p), ← Nat.card_eq_fintype_card]
      exact hbf
    have hsub : (Finset.univ.filter p).card
        ≤ (Finset.univ.filter (fun σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) => Qσ σ = Q)).card := by
      apply Finset.card_le_card
      intro σ hσ
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ σ, hQσ σ Q hQpos (Finset.mem_filter.mp hσ).2⟩
    have hstep : (C.ordAt h Q).toNat
        ≤ (Finset.univ.filter (fun σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) => Qσ σ = Q)).card := hXcard ▸ hsub
    simp only [cf]
    rw [← Int.toNat_of_nonneg hQpos.le]
    exact_mod_cast hstep
  have hoS : ∑ Q ∈ S, cf Q = (Fintype.card (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) : ℤ) := card_fiber_sum Qσ S hS
  obtain ⟨hkeyZ, hkeyS⟩ := finset_combination cf (fun Q => C.ordAt h Q) Z S (Fintype.card (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N))
    hZS hoS hcountZ hc0 hlower
  have hc : ∀ Q : C.Place, cf Q = posPart C h Q := by
    intro Q
    by_cases hQZ : Q ∈ Z
    · have hQpos : 0 < C.ordAt h Q := by
        have h2 := hQZ
        simp only [Z, Finset.mem_filter] at h2
        exact h2.2
      have h1 : cf Q = C.ordAt h Q := hkeyZ Q hQZ
      rw [h1, posPart_apply, max_eq_left hQpos.le]
    · have hord : C.ordAt h Q ≤ 0 := by
        by_contra hcon
        rw [not_le] at hcon
        exact hQZ (by
          rw [hZdef, Finset.mem_filter]
          refine ⟨?_, hcon⟩
          rw [Set.Finite.mem_toFinset]
          exact Function.mem_support.mpr (ne_of_gt hcon))
      have hcQ : cf Q = 0 := by
        by_cases hQS : Q ∈ S
        · exact hkeyS Q (Finset.mem_sdiff.mpr ⟨hQS, hQZ⟩)
        · simp only [cf]
          have hempty : Finset.univ.filter (fun σ : (↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N) => Qσ σ = Q) = ∅ :=
            Finset.filter_false_of_mem (fun σ _ hσ => hQS (hσ ▸ hS σ))
          rw [hempty]
          simp
      rw [hcQ, posPart_apply, max_eq_right hord]
  ext Q
  exact (hLHS Q).trans (hc Q)

end

end Work.KeyLemma.Curve.BranchSum
