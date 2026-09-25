import Mathlib.LinearAlgebra.FreeAlgebra

noncomputable section

namespace Commons.GroupTheory.ProPGroup

def freeAlgebraCongr {K ι ι' : Type*} [Field K] (eι : ι ≃ ι') :
    FreeAlgebra K ι ≃ₐ[K] FreeAlgebra K ι' :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := ι)).trans
    ((MonoidAlgebra.domCongr K K (FreeMonoid.freeMonoidCongr eι)).trans
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := ι')).symm)

theorem freeAlgebraCongr_basis {K ι ι' : Type*} [Field K] (eι : ι ≃ ι') (w : FreeMonoid ι) :
    freeAlgebraCongr eι (FreeAlgebra.basisFreeMonoid K ι w) =
      FreeAlgebra.basisFreeMonoid K ι' (FreeMonoid.freeMonoidCongr eι w) := by
  simp [freeAlgebraCongr, FreeAlgebra.basisFreeMonoid, MonoidAlgebra.domCongr,
    MonoidAlgebra.mapDomainRingEquiv]

def degreeSubmodule (K ι : Type*) [Field K] (n : ℕ) : Submodule K (FreeAlgebra K ι) :=
  Submodule.span K {x | ∃ w : FreeMonoid ι,
    (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}

lemma freeAlgebraCongr_degreeSet {K ι ι' : Type*} [Field K] (eι : ι ≃ ι') (n : ℕ) :
    (freeAlgebraCongr eι : FreeAlgebra K ι → FreeAlgebra K ι') ''
      {x | ∃ w : FreeMonoid ι,
        (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w} =
      {x | ∃ w : FreeMonoid ι',
        (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι' w} := by
  ext x
  constructor
  · rintro ⟨y, ⟨w, hlen, rfl⟩, rfl⟩
    refine ⟨FreeMonoid.freeMonoidCongr eι w, ?_, ?_⟩
    · change (FreeMonoid.toList (FreeMonoid.map eι w)).length = n
      rw [FreeMonoid.toList_map, List.length_map]
      exact hlen
    · exact freeAlgebraCongr_basis eι w
  · rintro ⟨w', hlen, rfl⟩
    refine ⟨FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.freeMonoidCongr eι.symm w'), ?_, ?_⟩
    · refine ⟨FreeMonoid.freeMonoidCongr eι.symm w', ?_, rfl⟩
      change (FreeMonoid.toList (FreeMonoid.map eι.symm w')).length = n
      rw [FreeMonoid.toList_map, List.length_map]
      exact hlen
    · rw [freeAlgebraCongr_basis]
      congr 1
      exact (FreeMonoid.freeMonoidCongr eι).apply_symm_apply w'

lemma freeAlgebraCongr_map_degreeSubmodule {K ι ι' : Type*} [Field K] (eι : ι ≃ ι') (n : ℕ) :
    Submodule.map (freeAlgebraCongr eι).toLinearEquiv.toLinearMap (degreeSubmodule K ι n) =
      degreeSubmodule K ι' n := by
  rw [degreeSubmodule, Submodule.map_span]
  change Submodule.span K
      ((freeAlgebraCongr eι : FreeAlgebra K ι → FreeAlgebra K ι') ''
        {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}) =
    degreeSubmodule K ι' n
  rw [freeAlgebraCongr_degreeSet, degreeSubmodule]

def twoSidedSpan (K ι σ : Type*) [Field K] (rel : σ → FreeAlgebra K ι) :
    Submodule K (FreeAlgebra K ι) :=
  Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
    x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}

lemma freeAlgebraCongr_twoSidedSet {K ι ι' σ σ' : Type*} [Field K] (eι : ι ≃ ι') (eσ : σ ≃ σ')
    (rel : σ → FreeAlgebra K ι) :
    (freeAlgebraCongr eι : FreeAlgebra K ι → FreeAlgebra K ι') ''
      {x | ∃ (r : σ) (v w : FreeMonoid ι),
        x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w} =
      {x | ∃ (r : σ') (v w : FreeMonoid ι'),
        x = FreeAlgebra.basisFreeMonoid K ι' v *
          (fun s => freeAlgebraCongr eι (rel (eσ.symm s))) r *
          FreeAlgebra.basisFreeMonoid K ι' w} := by
  ext x
  constructor
  · rintro ⟨y, ⟨r, v, w, rfl⟩, rfl⟩
    refine ⟨eσ r, FreeMonoid.freeMonoidCongr eι v, FreeMonoid.freeMonoidCongr eι w, ?_⟩
    simp [freeAlgebraCongr_basis, mul_assoc]
  · rintro ⟨r', v', w', rfl⟩
    refine ⟨FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.freeMonoidCongr eι.symm v') *
        rel (eσ.symm r') * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.freeMonoidCongr eι.symm w'),
      ?_, ?_⟩
    · refine ⟨eσ.symm r', FreeMonoid.freeMonoidCongr eι.symm v',
        FreeMonoid.freeMonoidCongr eι.symm w', rfl⟩
    · simp [map_mul, freeAlgebraCongr_basis, mul_assoc, FreeMonoid.freeMonoidCongr]

lemma freeAlgebraCongr_map_twoSidedSpan {K ι ι' σ σ' : Type*} [Field K] (eι : ι ≃ ι') (eσ : σ ≃ σ')
    (rel : σ → FreeAlgebra K ι) :
    Submodule.map (freeAlgebraCongr eι).toLinearEquiv.toLinearMap (twoSidedSpan K ι σ rel) =
      twoSidedSpan K ι' σ' (fun s => freeAlgebraCongr eι (rel (eσ.symm s))) := by
  rw [twoSidedSpan, Submodule.map_span]
  change Submodule.span K
      ((freeAlgebraCongr eι : FreeAlgebra K ι → FreeAlgebra K ι') ''
        {x | ∃ (r : σ) (v w : FreeMonoid ι),
          x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}) =
    twoSidedSpan K ι' σ' (fun s => freeAlgebraCongr eι (rel (eσ.symm s)))
  rw [freeAlgebraCongr_twoSidedSet, twoSidedSpan]

lemma finrank_map_mkQ_congr {K M M' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M']
    (e : M ≃ₗ[K] M') (P : Submodule K M) (P' : Submodule K M')
    (hP : Submodule.map e.toLinearMap P = P')
    (D : Submodule K M) (D' : Submodule K M')
    (hD : Submodule.map e.toLinearMap D = D') :
    Module.finrank K (Submodule.map P'.mkQ D') =
      Module.finrank K (Submodule.map P.mkQ D) := by
  let Qe : (M ⧸ P) ≃ₗ[K] M' ⧸ P' := Submodule.Quotient.equiv P P' e hP
  have hcomm : Qe.toLinearMap.comp P.mkQ = P'.mkQ.comp e.toLinearMap := by
    change (Submodule.mapQ P P' e.toLinearMap (Submodule.map_le_iff_le_comap.mp hP.le)).comp P.mkQ = P'.mkQ.comp e.toLinearMap
    rw [Submodule.mapQ_mkQ]
  have hmap : Submodule.map Qe.toLinearMap (Submodule.map P.mkQ D) = Submodule.map P'.mkQ D' := by
    rw [← Submodule.map_comp, hcomm, Submodule.map_comp, hD]
  rw [← hmap]
  exact LinearEquiv.finrank_map_eq Qe (Submodule.map P.mkQ D)

theorem freeAlgebraData_congr
    {K ι ι' σ σ' : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    [Fintype ι'] [DecidableEq ι'] [Fintype σ'] [DecidableEq σ']
    (eι : ι ≃ ι') (eσ : σ ≃ σ')
    (hpos : 0 < Fintype.card ι)
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      degreeSubmodule (degRel r))
    (hfin : ∀ᶠ n : ℕ in Filter.atTop,
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      let twoSidedSpan : (σ → FreeAlgebra K ι) → Submodule K (FreeAlgebra K ι) := fun r0 =>
        Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
          x = FreeAlgebra.basisFreeMonoid K ι v * r0 r * FreeAlgebra.basisFreeMonoid K ι w}
      Module.finrank K
        (Submodule.map (Submodule.mkQ (twoSidedSpan rel)) (degreeSubmodule n)) = 0) :
    ∃ (degRel' : σ' → ℕ) (rel' : σ' → FreeAlgebra K ι'),
      0 < Fintype.card ι' ∧
      (∀ r, 2 ≤ degRel' r) ∧
      (∀ r, rel' r ∈
        let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι') := fun n =>
          Submodule.span K {x | ∃ w : FreeMonoid ι',
            (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι' w}
        degreeSubmodule (degRel' r)) ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι') := fun n =>
          Submodule.span K {x | ∃ w : FreeMonoid ι',
            (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι' w}
        let twoSidedSpan : (σ' → FreeAlgebra K ι') → Submodule K (FreeAlgebra K ι') := fun r0 =>
          Submodule.span K {x | ∃ (r : σ') (v w : FreeMonoid ι'),
            x = FreeAlgebra.basisFreeMonoid K ι' v * r0 r * FreeAlgebra.basisFreeMonoid K ι' w}
        Module.finrank K
          (Submodule.map (Submodule.mkQ (twoSidedSpan rel')) (degreeSubmodule n)) = 0) := by
  refine ⟨fun r => degRel (eσ.symm r), fun r => freeAlgebraCongr eι (rel (eσ.symm r)), ?_, ?_, ?_, ?_⟩
  · rw [← Fintype.card_congr eι]
    exact hpos
  · intro r
    exact hdeg (eσ.symm r)
  · intro r
    have hhom' := hhom (eσ.symm r)
    change rel (eσ.symm r) ∈ degreeSubmodule K ι (degRel (eσ.symm r)) at hhom'
    have hmaple : Submodule.map (freeAlgebraCongr eι).toLinearEquiv.toLinearMap
        (degreeSubmodule K ι (degRel (eσ.symm r))) = degreeSubmodule K ι' (degRel (eσ.symm r)) :=
      freeAlgebraCongr_map_degreeSubmodule eι (degRel (eσ.symm r))
    change (freeAlgebraCongr eι) (rel (eσ.symm r)) ∈ degreeSubmodule K ι' (degRel (eσ.symm r))
    rw [← hmaple]
    exact Submodule.mem_map_of_mem hhom'
  · refine Filter.Eventually.mono hfin ?_
    intro n hn
    change Module.finrank K (Submodule.map (Submodule.mkQ (twoSidedSpan K ι σ rel))
      (degreeSubmodule K ι n)) = 0 at hn
    change Module.finrank K (Submodule.map (Submodule.mkQ
      (twoSidedSpan K ι' σ' (fun s => freeAlgebraCongr eι (rel (eσ.symm s)))))
      (degreeSubmodule K ι' n)) = 0
    rw [finrank_map_mkQ_congr ((freeAlgebraCongr eι).toLinearEquiv) (twoSidedSpan K ι σ rel)
        (twoSidedSpan K ι' σ' (fun s => freeAlgebraCongr eι (rel (eσ.symm s))))
        (freeAlgebraCongr_map_twoSidedSpan eι eσ rel) (degreeSubmodule K ι n)
        (degreeSubmodule K ι' n) (freeAlgebraCongr_map_degreeSubmodule eι n)]
    exact hn

end Commons.GroupTheory.ProPGroup