import Mathlib.Analysis.Normed.Order.Lattice

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Topology.Charts

/-- **The iii-a bridge (coordinate-set structure)**: let `ST := {t : ℝ //
t ∈ Ioo 0 1}` (the open unit interval), `U` an OPEN set with an arc chart
`ψ : ST ≃ₜ {x : X // x ∈ U}`, and `P` a set with an arc chart
`κ : ST ≃ₜ {x : X // x ∈ P}`.  Let `A := chartCoercion ψ '' {t : ST | (t :
ℝ) ∈ Ioo p c₀}` be the chart-arc of the strip `(p,c₀)` (its
ψ-images), contained in `P` (`hAsub`), with the strip meeting the unit
interval (`hne`).  Then the κ-COORDINATE SET of `A`,
`T := val '' {r : ST | ((κ r : {x : X // x ∈ P}) : X) ∈ A}` (where
`val` is the value map `ST → ℝ`), is an OPEN PRECONNECTED NONEMPTY
subset of `(0,1)`:
`IsOpen T ∧ IsPreconnected T ∧ T.Nonempty`.

Proof outline: (1) `A` is open in `X` (the chart-arc of an open interval:
coordinate strip open in `ST`, `ψ` a homeo, and the subtype embedding of
the OPEN `U` is an open map — `hUopen`); (2) `A` is preconnected (the
coordinate strip `{t : ST | (t : ℝ) ∈ Ioo p c₀}` is preconnected — its
value image `Ioo p c₀ ∩ Ioo 0 1` is an interval — and the continuous
chart coercion preserves preconnectedness); (3) `A` is nonempty
(`hne`); (4) the κ-preimage set `B := {r : ST | ((κ r : {x : X // x ∈ P})
: X) ∈ A}` is open in `ST` (it equals `κ ⁻¹' (val ⁻¹' A)` where
`val : {x // x ∈ P} → X`, both continuous, `A` open in `X`) and is
homeomorphic to `A` via `κ` (hence preconnected), and nonempty when `A`
is nonempty (with `hAsub` giving `A ⊆ P` so `κ`-coordinates of `A`-points
exist); (5) `T = val '' B`: the value map `val : ST → (0,1)` is a
homeomorphism onto its image, so `T` is open in `(0,1)` (open in ℝ: `B`
open in `ST` means `B = val ⁻¹' O` for some open `O ⊆ ℝ`, and
`val '' B = O ∩ Ioo 0 1`), preconnected (image of preconnected), and
nonempty. -/

theorem coordSet_open_preconnected_nonempty {X : Type*} [TopologicalSpace X]
    (P U : Set X) (hUopen : IsOpen U)
    (κ : {t : ℝ // t ∈ Set.Ioo 0 1} ≃ₜ {x : X // x ∈ P})
    (ψ : {t : ℝ // t ∈ Set.Ioo 0 1} ≃ₜ {x : X // x ∈ U})
    (p c₀ : ℝ) (hne : (Set.Ioo p c₀ ∩ Set.Ioo 0 1).Nonempty)
    (hAsub : (fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => ((ψ t : {x : X // x ∈ U}) : X)) ''
      {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo p c₀} ⊆ P) :
    let T : Set ℝ := ((↑) : {t : ℝ // t ∈ Set.Ioo 0 1} → ℝ) ''
      {r : {t : ℝ // t ∈ Set.Ioo 0 1} | ((κ r : {x : X // x ∈ P}) : X) ∈
        (fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => ((ψ t : {x : X // x ∈ U}) : X)) ''
          {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo p c₀}}
    IsOpen T ∧ IsPreconnected T ∧ T.Nonempty := by
  let v : {t : ℝ // t ∈ Set.Ioo 0 1} → ℝ := Subtype.val
  let fψ : {t : ℝ // t ∈ Set.Ioo 0 1} → X := fun t => ((ψ t : {x : X // x ∈ U}) : X)
  let fκ : {t : ℝ // t ∈ Set.Ioo 0 1} → X := fun r => ((κ r : {x : X // x ∈ P}) : X)
  let S : Set {t : ℝ // t ∈ Set.Ioo 0 1} := {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo p c₀}
  let A : Set X := fψ '' S
  let valU : {x : X // x ∈ U} → X := Subtype.val
  let valP : {x : X // x ∈ P} → X := Subtype.val
  let A'' : Set {x : X // x ∈ P} := valP ⁻¹' A
  let B : Set {t : ℝ // t ∈ Set.Ioo 0 1} := fκ ⁻¹' A
  change IsOpen (v '' B) ∧ IsPreconnected (v '' B) ∧ (v '' B).Nonempty
  -- continuous maps
  have hv_cont : Continuous v := continuous_subtype_val
  have hfψ_cont : Continuous fψ := by
    dsimp [fψ]
    exact continuous_subtype_val.comp ψ.continuous
  have hfκ_cont : Continuous fκ := by
    dsimp [fκ]
    exact continuous_subtype_val.comp κ.continuous
  -- S open in ST
  have hS_open : IsOpen S := by
    rw [show S = v ⁻¹' (Set.Ioo p c₀) by
      ext t
      simp [S, v]]
    exact hv_cont.isOpen_preimage (Set.Ioo p c₀) isOpen_Ioo
  -- S nonempty
  have hS_ne : S.Nonempty := by
    rcases hne with ⟨x, hx⟩
    refine ⟨⟨x, hx.2⟩, ?_⟩
    simpa [S] using hx.1
  -- S preconnected (ST ≅ its value interval in ℝ)
  have hS_pre : IsPreconnected S := by
    have hv_ind : Topology.IsInducing v := by
      simpa [v] using (Topology.IsInducing.subtypeVal (Y := ℝ) (t := Set.Ioo 0 1))
    have hIm : v '' S = Set.Ioo p c₀ ∩ Set.Ioo 0 1 := by
      ext x
      constructor
      · rintro ⟨t, htS, rfl⟩
        exact ⟨htS, t.2⟩
      · rintro ⟨hxpc, hx01⟩
        refine ⟨⟨x, hx01⟩, ?_, rfl⟩
        change x ∈ Set.Ioo p c₀
        exact hxpc
    have hIm_pre : IsPreconnected (v '' S) := by
      rw [hIm]
      exact (isPreconnected_iff_ordConnected).2
        (Set.OrdConnected.inter Set.ordConnected_Ioo Set.ordConnected_Ioo)
    exact (hv_ind.isPreconnected_image (s := S)).mp hIm_pre
  -- A = valU '' (ψ '' S)
  have hA_image : A = valU '' (⇑ψ '' S) := by
    change (valU ∘ ⇑ψ) '' S = valU '' (⇑ψ '' S)
    exact Set.image_comp valU ⇑ψ S
  -- A open in X
  have hψS_open : IsOpen (⇑ψ '' S) := by
    exact Homeomorph.isOpenMap ψ S hS_open
  have hA_open : IsOpen A := by
    rw [hA_image]
    exact (IsOpen.isOpenMap_subtype_val hUopen) (⇑ψ '' S) hψS_open
  -- A preconnected
  have hA_pre : IsPreconnected A := by
    simpa [A] using IsPreconnected.image hS_pre fψ hfψ_cont.continuousOn
  -- A nonempty
  have hA_ne : A.Nonempty := by
    simpa [A] using (Set.image_nonempty (f := fψ) (s := S)).2 hS_ne
  -- A ⊆ P
  have hAP : A ⊆ P := by
    exact hAsub
  -- valP open-preimage-A'' = A, A'' preconnected
  have hvalP_ind : Topology.IsInducing valP := by
    simpa [valP] using (Topology.IsInducing.subtypeVal (Y := X) (t := P))
  have hA''_image : valP '' A'' = A := by
    dsimp [A'']
    rw [Set.image_preimage_eq_inter_range]
    rw [show range valP = P by simpa [valP] using (Subtype.range_val (α := X) (s := P))]
    exact Set.inter_eq_left.mpr hAP
  have hA''_pre : IsPreconnected A'' := by
    exact ((hvalP_ind.isPreconnected_image (s := A'')).mp) (by simpa [hA''_image] using hA_pre)
  have hA''_ne : A''.Nonempty := by
    rcases hA_ne with ⟨x, hxA⟩
    refine ⟨⟨x, hAP hxA⟩, ?_⟩
    simpa [A''] using hxA
  -- B = κ ⁻¹' A'' and B = κ.symm '' A''
  have hB_eq : B = ⇑κ ⁻¹' A'' := by
    ext r
    change (fun a : {x : X // x ∈ P} => (a : X)) (⇑κ r) ∈ A ↔ valP (⇑κ r) ∈ A
    rfl
  have hB_eq' : B = ⇑κ.symm '' A'' := by
    ext r
    constructor
    · intro hr
      refine ⟨⇑κ r, ?_, ?_⟩
      · simpa [hB_eq] using hr
      · rw [κ.symm_apply_apply]
    · rintro ⟨y, hyA'', hyr⟩
      have hκr : ⇑κ r = y := by
        rw [← hyr]
        exact κ.apply_symm_apply y
      rw [hB_eq]
      simp [A'']
      rw [hκr]
      exact hyA''
  -- B open, preconnected, nonempty
  have hB_open : IsOpen B := by
    change IsOpen (fκ ⁻¹' A)
    exact hfκ_cont.isOpen_preimage A hA_open
  have hB_pre : IsPreconnected B := by
    rw [hB_eq']
    exact IsPreconnected.image hA''_pre ⇑κ.symm κ.symm.continuous.continuousOn
  have hB_ne : B.Nonempty := by
    rw [hB_eq']
    exact (Set.image_nonempty (f := ⇑κ.symm) (s := A'')).2 hA''_ne
  -- T = v '' B : open, preconnected, nonempty in ℝ
  have hv_ind : Topology.IsInducing v := by
    simpa [v] using (Topology.IsInducing.subtypeVal (Y := ℝ) (t := Set.Ioo 0 1))
  have hT_open : IsOpen (v '' B) := by
    rcases (hv_ind.isOpen_iff (s := B)).mp hB_open with ⟨O, hO_open, hO_eq⟩
    rw [← hO_eq]
    rw [Set.image_preimage_eq_inter_range]
    refine IsOpen.inter hO_open ?_
    rw [show range v = Set.Ioo 0 1 by simpa [v] using (Subtype.range_val (α := ℝ) (s := Set.Ioo 0 1))]
    exact isOpen_Ioo
  have hT_pre : IsPreconnected (v '' B) :=
    IsPreconnected.image hB_pre v hv_cont.continuousOn
  have hT_ne : (v '' B).Nonempty := Set.Nonempty.image v hB_ne
  exact ⟨hT_open, hT_pre, hT_ne⟩

end Commons.Topology.Charts