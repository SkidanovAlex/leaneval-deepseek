import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.exists_chartTensorFibrePoint
import Submission.Work.SpecLin.Alt.fg_ker_tensorLift
import Submission.Work.SpecLin.Alt.inf_ker_eq_mul
import Submission.Work.SpecLin.Alt.exists_chartTensorRedMap_surjective_ker
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart
import Submission.Work.SpecLin.Core.section_prime_sup_fibre_quot
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Alt

open Work.CurveBasics in
/-- The valuation subring of a place of a curve is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_valuationSubring {k : Type _} [Field k]
    {C : Work.CurveBasics.Curve k} (Q : C.Place) :
    IsDiscreteValuationRing ↥(Q.valuationSubring) := by
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  change IsDiscreteValuationRing
    ↥(IsDedekindDomain.HeightOneSpectrum.valuation (↥(C.functionField))
      (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point))).valuationSubring
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
      (K := ↥(C.functionField)))

theorem exists_mem_sectionPrime_span_map_eq {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (N : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) [N.IsMaximal]
    (hPN : Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W <= N) :
    exists f : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
      f ∈ Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW s hs) ∧
      f ∉ Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W ∧
      (Work.SpecLin.Core.sectionPrime R W (Work.SpecLin.Core.rgMap R W hW s hs)).map
          (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N))
        = Ideal.span (singleton (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
            (Localization.AtPrime N) f)) := by
  classical
  set φ : Γ(C.left, W) →ₐ[K] R := Work.SpecLin.Core.rgMap R W hW s hs with hφ
  set I : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    Work.SpecLin.Core.sectionPrime R W φ with hI
  set P : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W with hP
  -- the ideal `I ⊔ P` is maximal
  have hIPmax : (I ⊔ P).IsMaximal := by
    rw [hI, hP]
    have hκ : IsField (IsLocalRing.ResidueField R) := Field.toIsField (IsLocalRing.ResidueField R)
    have hq := Work.SpecLin.Core.section_prime_sup_fibre_quot (A := Γ(C.left, W)) φ
    have hf : IsField (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W ⧸
        (Work.SpecLin.Core.sectionPrime R W φ ⊔
          Work.SpecLin.Core.chartFibrePrime (K := K) (C := C) R W)) :=
      (MulEquiv.isField_congr hq.toMulEquiv).mpr hκ
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hf
  -- `I` is finitely generated (delegated: `Work.SpecLin.Alt.fg_ker_tensorLift`)
  haveI hft : Algebra.FiniteType K Γ(C.left, W) :=
    Work.CurveBasics.BaseChange.finiteType_sections C W hW
  have hIfg : I.FG := by
    rw [hI]
    exact Work.SpecLin.Alt.fg_ker_tensorLift φ
  -- `I ⊓ P = P * I` (delegated: `Work.SpecLin.Alt.inf_ker_eq_mul`)
  have hD2 : I ⊓ P = P * I := by
    rw [hI, hP]
    exact Work.SpecLin.Alt.inf_ker_eq_mul φ (IsLocalRing.maximalIdeal R)
  by_cases hIN : I ≤ N
  · -- ## Case B: `I ≤ N`
    have hNs : N = I ⊔ P :=
      (hIPmax.eq_of_le (Ideal.IsMaximal.ne_top ‹N.IsMaximal›) (sup_le hIN hPN)).symm
    obtain ⟨z, _hzmem, hz⟩ := Work.SpecLin.Alt.exists_chartTensorFibrePoint R W hW N hPN
    set O := Localization.AtPrime N with hO
    haveI hNprime : N.IsPrime := ‹N.IsMaximal›.isPrime
    haveI hOlr : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O N
    set Q : Ideal O := P.map (algebraMap _ O) with hQ
    set I' : Ideal O := I.map (algebraMap _ O) with hI'
    -- the surjection `B_N ↠ 𝒪_z` with kernel `P·B_N` (delegated)
    obtain ⟨ρV, hsurj, hker⟩ : ∃ ρV : O →+* ↥(z.valuationSubring),
        Function.Surjective ρV ∧ RingHom.ker ρV = Q :=
      Work.SpecLin.Alt.exists_chartTensorRedMap_surjective_ker R W hW N hPN z hz
    haveI hDVRz : IsDiscreteValuationRing ↥(z.valuationSubring) :=
      isDiscreteValuationRing_valuationSubring z
    -- `I' ⊔ Q` is the maximal ideal of `O`
    have hmapN : N.map (algebraMap _ O) = IsLocalRing.maximalIdeal O :=
      IsLocalization.AtPrime.map_eq_maximalIdeal N O
    have hI'Q : I' ⊔ Q = IsLocalRing.maximalIdeal O := by
      have h1 : I' ⊔ Q = Ideal.map (algebraMap _ O) N := by
        rw [hI', hQ, ← Ideal.map_sup, ← hNs]
      rw [h1, hmapN]
    -- the maximal ideal of the local ring `↥(z.valuationSubring)` is principal
    obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal
      (IsLocalRing.maximalIdeal ↥(z.valuationSubring))
    -- `ρV` maps the maximal ideal of `O` onto that of `↥(z.valuationSubring)`, and kills `Q`
    have hmapmax : Ideal.map ρV (IsLocalRing.maximalIdeal O)
        = IsLocalRing.maximalIdeal ↥(z.valuationSubring) :=
      IsLocalRing.map_maximalIdeal_of_surjective ρV hsurj
    have hmapQ : Ideal.map ρV Q = ⊥ := by
      rw [← hker, Ideal.map_eq_bot_iff_le_ker]
    have hmapI' : IsLocalRing.maximalIdeal ↥(z.valuationSubring) = Ideal.map ρV I' := by
      rw [← hmapmax, ← hI'Q, Ideal.map_sup, hmapQ, sup_bot_eq]
    have hπmem : π ∈ Ideal.map ρV I' := by
      rw [← hmapI', hπ]
      exact Ideal.mem_span_singleton_self π
    obtain ⟨x, hxI', hxπ⟩ := (Ideal.mem_map_iff_of_surjective ρV hsurj).mp hπmem
    -- the transversality `I' ⊓ Q = Q * I'` and Nakayama
    have hIQ : I' ⊓ Q = Q * I' := by
      have h1 := IsLocalization.map_inf (R := _) N.primeCompl O I P
      rw [hD2, Ideal.map_mul] at h1
      exact h1.symm
    have hI'fg : I'.FG := by rw [hI']; exact hIfg.map _
    have hle : I' ≤ Ideal.span {x} ⊔ Q * I' := by
      intro i hi
      have hmi : ρV i ∈ IsLocalRing.maximalIdeal ↥(z.valuationSubring) := by
        rw [hmapI']
        exact Ideal.mem_map_of_mem _ hi
      rw [hπ, ← hxπ] at hmi
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (x := ρV i) (y := ρV x)).mp hmi
      obtain ⟨o, ho⟩ := hsurj c
      have hsub : i - o * x ∈ Q := by
        rw [← hker, RingHom.mem_ker, map_sub, map_mul, ho, hc, sub_self]
      have hmem : i - o * x ∈ I' ⊓ Q :=
        ⟨I'.sub_mem hi (I'.mul_mem_left o hxI'), hsub⟩
      rw [hIQ] at hmem
      exact Submodule.mem_sup.mpr ⟨o * x, Ideal.mem_span_singleton'.mpr ⟨o, rfl⟩,
        i - o * x, hmem, by ring⟩
    rw [← Ideal.smul_eq_mul] at hle
    have hspanI' : I' ≤ Ideal.span {x} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot hI'fg ?_ hle
      exact le_trans (le_sup_right : Q ≤ I' ⊔ Q) (by
        rw [hI'Q]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have hI'eq : I' = Ideal.span {x} :=
      le_antisymm hspanI' (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxI'))
    -- lift `x` to an element of `I`
    obtain ⟨⟨a, s0⟩, hsa⟩ := IsLocalization.surj (N.primeCompl) x
    have ha_mem : algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) O a
        ∈ Ideal.map (algebraMap (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) O) I := by
      rw [← hsa]
      exact Ideal.mul_mem_right _ _ (hI' ▸ hxI')
    obtain ⟨s', hs'mem, hs'a⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (M := N.primeCompl) (S := O) I a).mp ha_mem
    have hunit : IsUnit (algebraMap _ O s' * algebraMap _ O (s0 : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) : O) :=
      IsUnit.mul (IsLocalization.map_units (M := N.primeCompl) O ⟨s', hs'mem⟩)
        (IsLocalization.map_units (M := N.primeCompl) O s0)
    have hgen : algebraMap _ O (s' * a) = x * (algebraMap _ O s' * algebraMap _ O (s0 : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) := by
      rw [map_mul, ← hsa]
      ring
    have hspan_eq : Ideal.span {algebraMap _ O (s' * a)} = Ideal.span {x} := by
      rw [hgen]
      exact Ideal.span_singleton_mul_right_unit hunit x
    refine ⟨s' * a, hs'a, ?_, ?_⟩
    · -- `f ∉ P`
      intro hfP
      have hmemQ : algebraMap _ O (s' * a) ∈ Q := Ideal.mem_map_of_mem _ hfP
      have hleQ : Ideal.span {algebraMap _ O (s' * a)} ≤ Q :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemQ)
      have hI'Qle : I' ≤ Q := by rw [hI'eq, ← hspan_eq]; exact hleQ
      have hbot : IsLocalRing.maximalIdeal ↥(z.valuationSubring) = ⊥ := by
        rw [← hmapmax, ← hI'Q, sup_eq_right.mpr hI'Qle]
        exact hmapQ
      exact IsDiscreteValuationRing.not_a_field' hbot
    · rw [hI'eq, ← hspan_eq]
  · -- ## Case A: `I ⊄ N`
    obtain ⟨f, hfI, hfN⟩ : ∃ x ∈ I, x ∉ N := by
      by_contra h
      push_neg at h
      exact hIN fun x hx => h x hx
    refine ⟨f, hfI, fun hfP => hfN (hPN hfP), ?_⟩
    haveI hNprime : N.IsPrime := ‹N.IsMaximal›.isPrime
    have hunit : IsUnit (algebraMap _ (Localization.AtPrime N) f) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime N) N f,
        Ideal.mem_primeCompl_iff]
      exact hfN
    have hspan : Ideal.span {algebraMap _ (Localization.AtPrime N) f} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hunit
    have hmap : I.map (algebraMap _ (Localization.AtPrime N)) = ⊤ := by
      have h1 : algebraMap _ (Localization.AtPrime N) f ∈
          I.map (algebraMap _ (Localization.AtPrime N)) := Ideal.mem_map_of_mem _ hfI
      have h2 : Ideal.span {algebraMap _ (Localization.AtPrime N) f} ≤
          I.map (algebraMap _ (Localization.AtPrime N)) :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1)
      rw [hspan] at h2
      exact top_le_iff.mp h2
    rw [hmap, hspan]

end Work.SpecLin.Alt
