/-
Area DSCOH — self-contained copies of the pieces of the vanishing proof.

The two lemmas below are copies of `Work.DSCOH.simplex_cech_lift_level` and
`Work.DSCOH.exists_boundary_of_coeffs`, re-based on the self-contained finset lemmas
`Work.DSCOH.dsSummandRelation` and `Work.DSCOH.dsAttachSdiffMem` instead of on the older
stubs `summand_relation` and `sum_attach_zsmul_ite_eq_sum_sdiff_mem` (both of which were later
discharged as second names of those lemmas).
They are used by `Work.DSCOH.chartCechShift_exact`.
-/
import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.simplexCechLiftAux
import Submission.Work.DSCOH.boundary_coeffs_aux
import Submission.Work.DSCOH.dsSummandRelation
import Submission.Work.DSCOH.dsAttachSdiffMem

open Finset
open scoped BigOperators

namespace Work.DSCOH

theorem dsSimplexCechLiftLevel {A : Type*} [CommRing A] {V : Type*} [LinearOrder V] [Fintype V]
    [DecidableEq V] (Z : Finset V) (m : ℕ) (hm : Z.card + 1 ≤ m) :
    ∃ L : ({S : Finset V // Z ⊆ S ∧ S.card = m} → A) →ₗ[A]
          ({U : Finset V // Z ⊆ U ∧ U.card + 1 = m} → A),
      ∀ c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A,
        (∀ T : {T : Finset V // Z ⊆ T ∧ T.card = m + 1},
          ∑ i ∈ (T.1 \ Z).attach,
            ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i.1)).card)) •
              c ⟨T.1.erase i.1,
                (fun j hj => Finset.mem_erase.mpr ⟨fun hji => (Finset.mem_sdiff.mp i.2).2 (hji ▸ hj),
                  T.2.1 hj⟩),
                (by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega)⟩ = 0) →
        ∀ T : {T : Finset V // Z ⊆ T ∧ T.card = m},
          ∑ i ∈ (T.1 \ Z).attach,
            ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i.1)).card)) •
              L c ⟨T.1.erase i.1,
                (fun j hj => Finset.mem_erase.mpr ⟨fun hji => (Finset.mem_sdiff.mp i.2).2 (hji ▸ hj),
                  T.2.1 hj⟩),
                (by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega)⟩ = c T := by
  classical
  by_cases hne : ((Finset.univ : Finset V) \ Z).Nonempty
  · -- Cone case: `a` is the least element of `V \ Z`.
    set a : V := ((Finset.univ : Finset V) \ Z).min' hne with ha_def
    have ha_mem : a ∈ (Finset.univ : Finset V) \ Z := Finset.min'_mem _ hne
    have haZ : a ∉ Z := (Finset.mem_sdiff.mp ha_mem).2
    have ha_le : ∀ x, x ∉ Z → a ≤ x := fun x hx =>
      Finset.min'_le ((Finset.univ : Finset V) \ Z) x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩)
    have hmin : ∀ x, x < a → x ∈ Z := fun x hx => by
      by_contra hxZ
      exact absurd (ha_le x hxZ) (not_le.mpr hx)
    set z0 : ℕ := (Z.filter (fun x => x < a)).card with hz0
    refine ⟨apexL (A := A) Z m a z0, ?_⟩
    intro c hc T
    have hconv : (∑ i ∈ (T.1 \ Z).attach,
        ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i.1)).card)) •
          apexL (A := A) Z m a z0 c ⟨T.1.erase i.1,
            (fun j hj => Finset.mem_erase.mpr ⟨fun hji => (Finset.mem_sdiff.mp i.2).2 (hji ▸ hj),
              T.2.1 hj⟩),
            (by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega)⟩)
        = ∑ i ∈ T.1 \ Z, summandG (A := A) Z m a z0 c T i := by
      rw [show (∑ i ∈ T.1 \ Z, summandG (A := A) Z m a z0 c T i)
            = ∑ i ∈ (T.1 \ Z).attach, summandG (A := A) Z m a z0 c T i.1
          from (Finset.sum_attach (T.1 \ Z) (summandG (A := A) Z m a z0 c T)).symm]
      apply Finset.sum_congr rfl
      intro i _
      rw [summandG_eq Z m a z0 c T i.1 i.2]
      congr 1
    rw [hconv]
    by_cases haT : a ∈ T.1
    · -- Case `a ∈ T`: only the `a`-term survives.
      have ha_in : a ∈ T.1 \ Z := Finset.mem_sdiff.mpr ⟨haT, haZ⟩
      have h1 : ∀ b ∈ T.1 \ Z, b ≠ a → summandG (A := A) Z m a z0 c T b = 0 := by
        intro b hb hne'
        rw [summandG_eq Z m a z0 c T b hb]
        have hmem : a ∈ (mkEraseIdx Z m T b hb).1 := by
          rw [mkEraseIdx_val]
          exact Finset.mem_erase.mpr ⟨Ne.symm hne', haT⟩
        rw [apexL_apply_of_mem hmem, smul_zero]
      have h2 : a ∉ T.1 \ Z → summandG (A := A) Z m a z0 c T a = 0 := fun h => absurd ha_in h
      rw [Finset.sum_eq_single (s := T.1 \ Z) (f := summandG (A := A) Z m a z0 c T) a h1 h2]
      rw [summandG_eq Z m a z0 c T a ha_in]
      have hnotmem : a ∉ (mkEraseIdx Z m T a ha_in).1 := by
        rw [mkEraseIdx_val]; exact Finset.notMem_erase a T.1
      rw [apexL_apply_of_not_mem hnotmem]
      have hsign : (T.1.filter (fun x => x < a)).card = z0 := by
        rw [card_filter_lt_eq_of_lt_imp_mem T.2.1 hmin, hz0]
      have hAug : augIdx Z m a (mkEraseIdx Z m T a ha_in) hnotmem = T := by
        apply Subtype.ext
        rw [augIdx_val, mkEraseIdx_val, Finset.union_singleton, Finset.insert_erase haT]
      rw [hsign, hAug, negOne_pow_smul_self]
    · -- Case `a ∉ T`: use the cocycle relation at `T ∪ {a}`.
      let T' : {T : Finset V // Z ⊆ T ∧ T.card = m + 1} :=
        ⟨T.1 ∪ {a}, fun j hj => Finset.mem_union.mpr (Or.inl (T.2.1 hj)),
         by rw [Finset.union_singleton, Finset.card_insert_of_notMem haT, T.2.2]⟩
      have hT'val : T'.1 = T.1 ∪ {a} := rfl
      have hT'ins : T'.1 = insert a T.1 := by rw [hT'val, Finset.union_singleton]
      have hsdiff : T'.1 \ Z = insert a (T.1 \ Z) := by
        rw [hT'ins]
        apply Finset.Subset.antisymm
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          obtain ⟨hxins, hxZ⟩ := hx
          rw [Finset.mem_insert] at hxins
          rw [Finset.mem_insert]
          rcases hxins with hxa | hxT
          · exact Or.inl hxa
          · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxZ⟩)
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_sdiff] at hx
          rw [Finset.mem_sdiff, Finset.mem_insert]
          rcases hx with hxa | ⟨hxT, hxZ⟩
          · exact ⟨Or.inl hxa, by rw [hxa]; exact haZ⟩
          · exact ⟨Or.inr hxT, hxZ⟩
      have ha_notin : a ∉ T.1 \ Z := by
        rw [Finset.mem_sdiff]; exact fun h => haT h.1
      have hH0 : ∑ j ∈ T'.1 \ Z, summandH (A := A) Z m c T' j = 0 := by
        rw [show (∑ j ∈ T'.1 \ Z, summandH (A := A) Z m c T' j)
              = ∑ j ∈ (T'.1 \ Z).attach, summandH (A := A) Z m c T' j.1
            from (Finset.sum_attach (T'.1 \ Z) (summandH (A := A) Z m c T')).symm]
        rw [← hc T']
        apply Finset.sum_congr rfl
        intro j _
        rw [summandH_eq Z m c T' j.1 j.2]
        congr 1
      have hsplit : ∑ j ∈ T'.1 \ Z, summandH (A := A) Z m c T' j
          = summandH (A := A) Z m c T' a + ∑ j ∈ T.1 \ Z, summandH (A := A) Z m c T' j := by
        rw [hsdiff, Finset.sum_insert ha_notin]
      have hsumH : ∑ j ∈ T.1 \ Z, summandH (A := A) Z m c T' j
          = - summandH (A := A) Z m c T' a := by
        have h3 : summandH (A := A) Z m c T' a
            + ∑ j ∈ T.1 \ Z, summandH (A := A) Z m c T' j = 0 := by
          rw [← hsplit]; exact hH0
        linear_combination h3
      have hfa : summandH (A := A) Z m c T' a = ((-1 : ℤ) ^ z0) • c T := by
        have ha_in' : a ∈ T'.1 \ Z := by
          rw [Finset.mem_sdiff]
          exact ⟨by rw [hT'val]; exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)), haZ⟩
        rw [summandH_eq Z m c T' a ha_in']
        have hsign : (T'.1.filter (fun x => x < a)).card = z0 := by
          rw [card_filter_lt_eq_of_lt_imp_mem T'.2.1 hmin, hz0]
        have hAug : mkEraseIdxH Z m T' a ha_in' = T := by
          apply Subtype.ext
          rw [mkEraseIdxH_val, hT'ins, Finset.erase_insert haT]
        rw [hsign, hAug]
      have hpoint : ∀ i ∈ T.1 \ Z,
          summandG (A := A) Z m a z0 c T i = (-((-1 : ℤ) ^ z0)) • summandH (A := A) Z m c T' i :=
        fun i hi => dsSummandRelation Z m a z0 c T T' haT ha_le hT'val i hi
      have hGsum : ∑ i ∈ T.1 \ Z, summandG (A := A) Z m a z0 c T i
          = (-((-1 : ℤ) ^ z0)) • ∑ i ∈ T.1 \ Z, summandH (A := A) Z m c T' i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i hi => hpoint i hi)
      rw [hGsum, hsumH, hfa, neg_smul, smul_neg, neg_neg, negOne_pow_smul_self]
  · -- Degenerate case: `Z = univ`, so there are no level-`m` indices at all.
    refine ⟨0, ?_⟩
    intro c hc T
    exfalso
    have hsub : (Finset.univ : Finset V) ⊆ Z := by
      intro x hx
      by_contra hxZ
      exact hne ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxZ⟩⟩
    have h1 : T.1.card ≤ Z.card := Finset.card_le_card (fun x _ => hsub (Finset.mem_univ x))
    have h2 : Z.card + 1 ≤ T.1.card := by rw [T.2.2]; exact hm
    omega


theorem dsExistsBoundaryOfCoeffs {A : Type*} [CommRing A] {n : ℕ} {d : ℕ} (q : ℕ)
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ))
    (hN0 : ∀ (β : Fin n → ℤ), β ∉ F →
      ∀ (U : Finset (Fin n)) (hU : Zset β ⊆ U) (hc : U.card + 1 = q + 2), N β ⟨U, hU, hc⟩ = 0)
    (hNdeg : ∀ (β : Fin n → ℤ), β ∈ F → (∑ i, β i) = -(d : ℤ)) :
    ∃ b : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q,
      (∀ (U : Finset (Fin n)) (hU : U.card = q + 1) (β : Fin n → ℤ) (hβ : Zset β ⊆ U),
        ((B U).repr (cechCoeff b U hU)) ⟨β, (Zset_subset_iff U β).mp hβ⟩ =
          N β ⟨U, hβ, by omega⟩) ∧
      (∀ (T : Finset (Fin n)) (hT : T.card = q + 1 + 1) (β : Fin n → ℤ) (hβ : Zset β ⊆ T),
        ((B T).repr
          ((cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q b)
            ⟨T, by omega⟩).1) ⟨β, (Zset_subset_iff T β).mp hβ⟩ =
          ∑ i ∈ T.attach, ((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
            (if h : ∀ j, j ∉ T.erase i.1 → 0 ≤ β j
              then N β ⟨T.erase i.1, (Zset_subset_iff (T.erase i.1) β).mpr h, by
                rw [Finset.card_erase_of_mem i.2]; omega⟩
              else 0)) ∧
      (∀ (T : Finset (Fin n)) (hT : T.card = q + 1 + 1) (β : Fin n → ℤ) (hβ : Zset β ⊆ T),
        ((B T).repr
          ((cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q b)
            ⟨T, by omega⟩).1) ⟨β, (Zset_subset_iff T β).mp hβ⟩ =
          ∑ i ∈ (T \ Zset β).attach, ((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
            N β ⟨T.erase i.1,
              (Zset_subset_iff (T.erase i.1) β).mpr
                (Zset_index_erase hβ (Finset.mem_sdiff.mp i.2).1
                  (Finset.mem_sdiff.mp i.2).2),
              by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega⟩) := by
  refine ⟨bCech B N F hB3 hNdeg, ?_, ?_, ?_⟩
  · intro U hU β hβ
    exact bCech_coeff B N F hB3 hNdeg hN0 U hU β hβ
  · intro T hT β hβ
    exact diff_coeff_eq B hB2 N F hB3 hNdeg hN0 T hT β hβ
  · intro T hT β hβ
    refine (diff_coeff_eq B hB2 N F hB3 hNdeg hN0 T hT β hβ).trans ?_
    refine dsAttachSdiffMem (T := T) (Z := Zset β)
      (P := fun i => ∀ j, j ∉ T.erase i → 0 ≤ β j)
      (s := fun i => (-1 : ℤ) ^ ((T.filter (fun x => x < i)).card))
      (v := fun i hiT h => N β ⟨T.erase i, (Zset_subset_iff (T.erase i) β).mpr h,
        by rw [Finset.card_erase_of_mem hiT]; omega⟩)
      (w := fun i hiT hiZ => N β ⟨T.erase i, (Zset_subset_iff (T.erase i) β).mpr
        (Zset_index_erase hβ hiT hiZ), by rw [Finset.card_erase_of_mem hiT]; omega⟩)
      ?_ ?_ ?_
    · intro i hiT hiZ h
      rw [mem_Zset] at hiZ
      exact absurd (h i (by simp)) (by omega)
    · intro i hiT hiZ
      exact Zset_index_erase hβ hiT hiZ
    · intro i hiT hiZ h
      exact congrArg (N β) (Subtype.ext rfl)


end Work.DSCOH
