import Mathlib.Analysis.Normed.Order.Lattice

open Set Filter Metric
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

namespace ArcBranchRight

/-- The open unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

/-- The open interval `(c₀,1)` as a type (the branch reparametrisation domain). -/
abbrev Dom (c₀ : ℝ) : Type := {s : ℝ // s ∈ Set.Ioo c₀ 1}

/-- The real coordinate range of a branch reparametrisation `f`. -/
def Rval {c₀ : ℝ} (f : Dom c₀ → ORI) : Set ℝ := {w : ℝ | ∃ s : Dom c₀, (f s : ℝ) = w}

/-- The coordinate-value map of `f` is continuous. -/
lemma fval_cont {c₀ : ℝ} {f : Dom c₀ → ORI} (hf_cont : Continuous f) :
    Continuous (fun s : Dom c₀ => (f s : ℝ)) :=
  continuous_subtype_val.comp hf_cont

/-- The coordinate-value map of an injective `f` is injective. -/
lemma fval_inj {c₀ : ℝ} {f : Dom c₀ → ORI} (hf_inj : Function.Injective f) :
    Function.Injective (fun s : Dom c₀ => (f s : ℝ)) := by
  intro s t h
  apply hf_inj
  apply Subtype.ext
  exact h

/-- The real extension of the coordinate map of `f` (arbitrary outside `(c₀,1)`). -/
def fExt {c₀ : ℝ} (f : Dom c₀ → ORI) (r : ℝ) : ℝ :=
  if hr : r ∈ Set.Ioo c₀ 1 then (f ⟨r, hr⟩ : ℝ) else 0

lemma fExt_of_mem {c₀ : ℝ} (f : Dom c₀ → ORI) {r : ℝ} (hr : r ∈ Set.Ioo c₀ 1) :
    fExt f r = (f ⟨r, hr⟩ : ℝ) := by
  simp [fExt, hr]

lemma fExt_contOn {c₀ : ℝ} {f : Dom c₀ → ORI} (hf_cont : Continuous f) :
    ContinuousOn (fExt f) (Set.Ioo c₀ 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hagree : (Set.Ioo c₀ 1).domRestrict (fExt f) =
      (fun s : Dom c₀ => (f s : ℝ)) := by
    funext s
    exact fExt_of_mem f s.2
  rw [hagree]
  exact fval_cont hf_cont

lemma fExt_injOn {c₀ : ℝ} {f : Dom c₀ → ORI} (hf_inj : Function.Injective f) :
    Set.InjOn (fExt f) (Set.Ioo c₀ 1) := by
  intro x hx y hy hxy
  unfold fExt at hxy
  rw [dif_pos hx, dif_pos hy] at hxy
  have hsub : (⟨x, hx⟩ : Dom c₀) = ⟨y, hy⟩ := hf_inj (Subtype.ext hxy)
  exact congrArg Subtype.val hsub

/-- A continuous injective branch reparametrisation is strictly monotone
(increasing or decreasing) in its coordinate values. -/
lemma fval_mono_or_anti {c₀ : ℝ} {f : Dom c₀ → ORI} (hc₀₁ : c₀ < 1)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    (∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f s : ℝ) < (f t : ℝ)) ∨
    (∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f t : ℝ) < (f s : ℝ)) := by
  have hmonoOr : StrictMonoOn (fExt f) (Set.Ioo c₀ 1) ∨
      StrictAntiOn (fExt f) (Set.Ioo c₀ 1) :=
    ContinuousOn.strictMonoOn_of_injOn_Ioo (α := ℝ) (δ := ℝ) hc₀₁
      (fExt_contOn hf_cont) (fExt_injOn hf_inj)
  rcases hmonoOr with hmono | hanti
  · left
    intro s t hs
    have hfs : (s : ℝ) ∈ Set.Ioo c₀ 1 := s.2
    have hft : (t : ℝ) ∈ Set.Ioo c₀ 1 := t.2
    have hlt : fExt f (s : ℝ) < fExt f (t : ℝ) := hmono hfs hft hs
    simpa [fExt] using hlt
  · right
    intro s t hs
    have hfs : (s : ℝ) ∈ Set.Ioo c₀ 1 := s.2
    have hft : (t : ℝ) ∈ Set.Ioo c₀ 1 := t.2
    have hlt : fExt f (t : ℝ) < fExt f (s : ℝ) := hanti hfs hft hs
    simpa [fExt] using hlt

/-- The range is a subset of the unit interval. -/
lemma Rval_subset_unit {c₀ : ℝ} (f : Dom c₀ → ORI) : Rval f ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro w hw
  rcases hw with ⟨s, rfl⟩
  exact (f s : ORI).2

/-- The range is nonempty (the domain is nonempty since `c₀ < 1`). -/
lemma Rval_nonempty {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1) : (Rval f).Nonempty := by
  rcases nonempty_Ioo_subtype (α := ℝ) hc₀₁ with ⟨s₀⟩
  exact ⟨(f s₀ : ℝ), s₀, rfl⟩

/-- The range is bounded below (by 0) and above (by 1). -/
lemma Rval_bddBelow {c₀ : ℝ} (f : Dom c₀ → ORI) : BddBelow (Rval f) := by
  refine ⟨0, ?_⟩
  intro w hw
  exact le_of_lt (Rval_subset_unit f hw).1

lemma Rval_bddAbove {c₀ : ℝ} (f : Dom c₀ → ORI) : BddAbove (Rval f) := by
  refine ⟨1, ?_⟩
  intro w hw
  exact le_of_lt (Rval_subset_unit f hw).2

/-- The range is the image of the open interval `(c₀,1)` under the real
extension, hence preconnected. -/
lemma Rval_preconnected {c₀ : ℝ} (f : Dom c₀ → ORI) (hf_cont : Continuous f) :
    IsPreconnected (Rval f) := by
  have hIm : (fExt f) '' Set.Ioo c₀ 1 = Rval f := by
    ext w
    constructor
    · rintro ⟨r, hr, hw⟩
      refine ⟨⟨r, hr⟩, ?_⟩
      simpa [fExt, hr] using hw
    · rintro ⟨s, hw⟩
      refine ⟨(s : ℝ), s.2, ?_⟩
      simpa [fExt, s.2] using hw
  have hpc : IsPreconnected ((fExt f) '' Set.Ioo c₀ 1) :=
    IsPreconnected.image (isPreconnected_Ioo (a := c₀) (b := 1)) (fExt f)
      (fExt_contOn hf_cont)
  simpa [hIm] using hpc

/-- The range is order-connected (an interval). -/
lemma Rval_ordConnected {c₀ : ℝ} (f : Dom c₀ → ORI) (hf_cont : Continuous f) :
    (Rval f).OrdConnected :=
  (Rval_preconnected f hf_cont).ordConnected

/-- The coordinate value at any point lies in the range. -/
lemma fval_mem_Rval {c₀ : ℝ} (f : Dom c₀ → ORI) (s : Dom c₀) : (f s : ℝ) ∈ Rval f :=
  ⟨s, rfl⟩

/-- The infimum of the range is nonnegative. -/
lemma inf_Rval_nonneg {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1) : 0 ≤ sInf (Rval f) := by
  apply le_csInf (Rval_nonempty f hc₀₁)
  intro b hb
  exact le_of_lt (Rval_subset_unit f hb).1

/-- The infimum of the range is strictly below 1. -/
lemma inf_Rval_lt_one {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1) : sInf (Rval f) < 1 := by
  rcases Rval_nonempty f hc₀₁ with ⟨w, hw⟩
  have h1 : sInf (Rval f) ≤ w := csInf_le (Rval_bddBelow f) hw
  exact lt_of_le_of_lt h1 (Rval_subset_unit f hw).2

/-- The supremum of the range is strictly positive. -/
lemma sup_Rval_gt_zero {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1) : 0 < sSup (Rval f) := by
  rcases Rval_nonempty f hc₀₁ with ⟨w, hw⟩
  have h1 : w ≤ sSup (Rval f) := le_csSup (Rval_bddAbove f) hw
  exact lt_of_lt_of_le (Rval_subset_unit f hw).1 h1

/-- The supremum of the range is at most 1. -/
lemma sup_Rval_le_one {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1) : sSup (Rval f) ≤ 1 := by
  apply csSup_le (Rval_nonempty f hc₀₁)
  intro b hb
  exact le_of_lt (Rval_subset_unit f hb).2

/-- The infimum is a lower bound of every element of the range. -/
lemma inf_le_elem {c₀ : ℝ} (f : Dom c₀ → ORI) (s : Dom c₀) : sInf (Rval f) ≤ (f s : ℝ) :=
  csInf_le (Rval_bddBelow f) (fval_mem_Rval f s)

/-- The supremum is an upper bound of every element of the range. -/
lemma sup_ge_elem {c₀ : ℝ} (f : Dom c₀ → ORI) (s : Dom c₀) : (f s : ℝ) ≤ sSup (Rval f) :=
  le_csSup (Rval_bddAbove f) (fval_mem_Rval f s)

/-- If `f` is increasing, every initial prefix is eventually inside
`(inf R - η, inf R + η)`. -/
lemma inf_pref_of_increasing {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1)
    (hinc : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f s : ℝ) < (f t : ℝ)) :
    ∀ η : ℝ, 0 < η → ∃ u : Dom c₀, ∀ s : Dom c₀, (s : ℝ) < (u : ℝ) →
      (f s : ℝ) ∈ Set.Ioo (sInf (Rval f) - η) (sInf (Rval f) + η) := by
  intro η hη
  have hLlt : sInf (Rval f) < sInf (Rval f) + η := by linarith
  rcases exists_lt_of_csInf_lt (Rval_nonempty f hc₀₁) hLlt with ⟨w, hwR, hwlt⟩
  rcases hwR with ⟨u, hfu⟩
  refine ⟨u, ?_⟩
  intro s hs
  constructor
  · have hle : sInf (Rval f) ≤ (f s : ℝ) := inf_le_elem f s
    exact lt_of_lt_of_le (by linarith) hle
  · have hfs : (f s : ℝ) < (f u : ℝ) := hinc hs
    linarith

/-- If `f` is decreasing, every initial prefix is eventually inside
`(sup R - η, sup R + η)`. -/
lemma sup_pref_of_decreasing {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1)
    (hdec : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f t : ℝ) < (f s : ℝ)) :
    ∀ η : ℝ, 0 < η → ∃ u : Dom c₀, ∀ s : Dom c₀, (s : ℝ) < (u : ℝ) →
      (f s : ℝ) ∈ Set.Ioo (sSup (Rval f) - η) (sSup (Rval f) + η) := by
  intro η hη
  have hSgt : sSup (Rval f) - η < sSup (Rval f) := by linarith
  rcases exists_lt_of_lt_csSup (Rval_nonempty f hc₀₁) hSgt with ⟨w, hwR, hwgt⟩
  rcases hwR with ⟨u, hfu⟩
  refine ⟨u, ?_⟩
  intro s hs
  constructor
  · have hfs : (f u : ℝ) < (f s : ℝ) := hdec hs
    linarith
  · have hle : (f s : ℝ) ≤ sSup (Rval f) := sup_ge_elem f s
    exact lt_of_le_of_lt hle (by linarith)

/-! ### Topological part -- closures and arc continuity -/

/-- In a Hausdorff space, a point lying in the closure of every open
neighbourhood of `p` equals `p`. -/
lemma eq_of_mem_closure_all_open {X : Type*} [TopologicalSpace X] [T2Space X] {q p : X}
    (h : ∀ V : Set X, IsOpen V → p ∈ V → q ∈ closure V) : q = p := by
  by_contra hne
  rcases t2_separation hne with ⟨U, V, hUo, hVo, hqU, hpV, hdisj⟩
  have hqcl : q ∈ closure V := h V hVo hpV
  have hUV : (U ∩ V).Nonempty := (mem_closure_iff.mp hqcl) U hUo hqU
  rcases hUV with ⟨w, hwU, hwV⟩
  exact (Set.disjoint_left.mp hdisj) hwU hwV

/-- Continuity at an interior coordinate: an open neighbourhood of the arc
point at coordinate `ℓ ∈ (0,1)` pulls back to a two-sided coordinate
interval `(ℓ-η, ℓ+η)`. -/
lemma arc_maps_interval_into {X : Type*} [TopologicalSpace X] {a : ORI → X}
    (ha_cont : Continuous a) {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1)
    {V : Set X} (hV : IsOpen V) (hmem : a ⟨ℓ, ⟨hℓ0, hℓ1⟩⟩ ∈ V) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ORI, (t : ℝ) ∈ Set.Ioo (ℓ - η) (ℓ + η) → a t ∈ V := by
  have hpre : IsOpen (a ⁻¹' V) := hV.preimage ha_cont
  have hmem' : ⟨ℓ, ⟨hℓ0, hℓ1⟩⟩ ∈ a ⁻¹' V := hmem
  let valT : ORI → ℝ := fun t => (t : ℝ)
  have hopenmap : IsOpenMap valT := by
    simpa [valT] using (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).isOpenMap_subtype_val
  have hIm : IsOpen (valT '' (a ⁻¹' V)) := hopenmap (a ⁻¹' V) hpre
  have hImMem : ℓ ∈ valT '' (a ⁻¹' V) := ⟨⟨ℓ, ⟨hℓ0, hℓ1⟩⟩, hmem', rfl⟩
  have hnhds : valT '' (a ⁻¹' V) ∈ 𝓝 ℓ := hIm.mem_nhds hImMem
  rcases (nhds_basis_Ioo_pos ℓ).mem_iff.mp hnhds with ⟨η, hη, hsub⟩
  refine ⟨η, hη, ?_⟩
  intro t ht
  have htIm : (t : ℝ) ∈ valT '' (a ⁻¹' V) := hsub ht
  rcases htIm with ⟨t', ht'pre, htEq⟩
  have ht' : t' = t := Subtype.val_injective htEq
  subst t'
  exact ht'pre

/-- If the branch prefixes `f(s)` for `s < u` eventually lie in any
two-sided coordinate interval around an interior coordinate `ℓ`, then `z`
is the arc point at `ℓ` (the prefixes accumulate there). -/
lemma z_eq_point {X : Type*} [TopologicalSpace X] [T2Space X]
    {a : ORI → X} (ha_cont : Continuous a) {c₀ : ℝ} {f : Dom c₀ → ORI}
    {z : X} (hzcl : ∀ u : Dom c₀,
        z ∈ closure (a '' (f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)})))
    {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hpref : ∀ η : ℝ, 0 < η → ∃ u : Dom c₀, ∀ s : Dom c₀, (s : ℝ) < (u : ℝ) →
      (f s : ℝ) ∈ Set.Ioo (ℓ - η) (ℓ + η)) :
    z = a ⟨ℓ, ⟨hℓ0, hℓ1⟩⟩ := by
  apply eq_of_mem_closure_all_open (p := a ⟨ℓ, ⟨hℓ0, hℓ1⟩⟩)
  intro V hV hmem
  rcases arc_maps_interval_into (a := a) ha_cont hℓ0 hℓ1 hV hmem with ⟨η, hη, hinto⟩
  rcases hpref η hη with ⟨u, hu⟩
  have hsub1 : f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)} ⊆
      {t : ORI | (t : ℝ) ∈ Set.Ioo (ℓ - η) (ℓ + η)} := by
    rw [Set.image_subset_iff]
    intro s hs
    exact hu s hs
  have hsub2 : a '' {t : ORI | (t : ℝ) ∈ Set.Ioo (ℓ - η) (ℓ + η)} ⊆ V := by
    rw [Set.image_subset_iff]
    intro t ht
    exact hinto t ht
  have hzcl1 : z ∈ closure (a '' {t : ORI | (t : ℝ) ∈ Set.Ioo (ℓ - η) (ℓ + η)}) :=
    closure_mono (Set.image_mono hsub1) (hzcl u)
  exact closure_mono hsub2 hzcl1

/-- In the increasing case the infimum of the range cannot be positive. -/
lemma increasing_inf_not_pos {X : Type*} [TopologicalSpace X] [T2Space X]
    {a : ORI → X} (ha_cont : Continuous a) {c₀ : ℝ} (hc₀₁ : c₀ < 1)
    {z : X} (hz_out : z ∉ Set.range a) (f : Dom c₀ → ORI)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : Dom c₀, z ∈ closure (a '' (f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)})))
    (hinc : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f s : ℝ) < (f t : ℝ))
    (hpos : 0 < sInf (Rval f)) : False := by
  have hL1 : sInf (Rval f) < 1 := inf_Rval_lt_one f hc₀₁
  have hzeq : z = a ⟨sInf (Rval f), ⟨hpos, hL1⟩⟩ :=
    z_eq_point (a := a) ha_cont (f := f) (hzcl := hzcl) (ℓ := sInf (Rval f)) hpos hL1
      (inf_pref_of_increasing f hc₀₁ hinc)
  exact hz_out ⟨⟨sInf (Rval f), ⟨hpos, hL1⟩⟩, hzeq.symm⟩

/-- In the decreasing case the supremum of the range cannot be below 1. -/
lemma decreasing_sup_not_lt_one {X : Type*} [TopologicalSpace X] [T2Space X]
    {a : ORI → X} (ha_cont : Continuous a) {c₀ : ℝ} (hc₀₁ : c₀ < 1)
    {z : X} (hz_out : z ∉ Set.range a) (f : Dom c₀ → ORI)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : Dom c₀, z ∈ closure (a '' (f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)})))
    (hdec : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f t : ℝ) < (f s : ℝ))
    (hlt : sSup (Rval f) < 1) : False := by
  have hS0 : 0 < sSup (Rval f) := sup_Rval_gt_zero f hc₀₁
  have hzeq : z = a ⟨sSup (Rval f), ⟨hS0, hlt⟩⟩ :=
    z_eq_point (a := a) ha_cont (f := f) (hzcl := hzcl) (ℓ := sSup (Rval f)) hS0 hlt
      (sup_pref_of_decreasing f hc₀₁ hdec)
  exact hz_out ⟨⟨sSup (Rval f), ⟨hS0, hlt⟩⟩, hzeq.symm⟩

/-- If the infimum of the range is zero then the range covers a whole
initial real segment `(0, δ)` (Branch 2). -/
lemma branch2_of_inf_zero {c₀ : ℝ} (f : Dom c₀ → ORI) (hc₀₁ : c₀ < 1)
    (hf_cont : Continuous f) (hL0 : sInf (Rval f) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∃ s : Dom c₀, (f s : ℝ) = t := by
  rcases Rval_nonempty f hc₀₁ with ⟨w, hwR⟩
  refine ⟨w, (Rval_subset_unit f hwR).1, ?_⟩
  intro t ht0 htw
  have hLt : sInf (Rval f) < t := by rw [hL0]; exact ht0
  rcases exists_lt_of_csInf_lt (Rval_nonempty f hc₀₁) hLt with ⟨v, hvR, hvt⟩
  have htwIcc : t ∈ Set.Icc v w := by
    constructor <;> linarith
  have hsub : Set.Icc v w ⊆ Rval f := (Rval_ordConnected f hf_cont).out' hvR hwR
  have htR : t ∈ Rval f := hsub htwIcc
  rcases htR with ⟨s, hfs⟩
  exact ⟨s, hfs⟩

/-- If `f` is increasing then Branch 2 holds. -/
lemma branch2_of_increasing {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : ORI → X) (ha_cont : Continuous a) {c₀ : ℝ} (hc₀₁ : c₀ < 1)
    (z : X) (hz_out : z ∉ Set.range a) (f : Dom c₀ → ORI)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : Dom c₀, z ∈ closure (a '' (f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)})))
    (hinc : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f s : ℝ) < (f t : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∃ s : Dom c₀, (f s : ℝ) = t := by
  have hL0 : sInf (Rval f) = 0 := by
    apply le_antisymm
    · exact le_of_not_gt
        (fun hpos => increasing_inf_not_pos ha_cont hc₀₁ hz_out f hf_cont hf_inj hzcl hinc hpos)
    · exact inf_Rval_nonneg f hc₀₁
  exact branch2_of_inf_zero f hc₀₁ hf_cont hL0

/-- If `f` is decreasing then Branch 1 holds. -/
lemma branch1_of_decreasing {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : ORI → X) (ha_cont : Continuous a) {c₀ : ℝ} (hc₀₁ : c₀ < 1)
    (z : X) (hz_out : z ∉ Set.range a) (f : Dom c₀ → ORI)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : Dom c₀, z ∈ closure (a '' (f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)})))
    (hdec : ∀ ⦃s t : Dom c₀⦄, (s : ℝ) < (t : ℝ) → (f t : ℝ) < (f s : ℝ)) :
    ∀ b : ℝ, 0 < b → b < 1 → z ∈ closure (a '' {t : ORI | b < (t : ℝ)}) := by
  have hS1 : sSup (Rval f) = 1 := by
    apply le_antisymm
    · exact sup_Rval_le_one f hc₀₁
    · exact le_of_not_gt
        (fun hlt => decreasing_sup_not_lt_one ha_cont hc₀₁ hz_out f hf_cont hf_inj hzcl hdec hlt)
  intro b hb0 hb1
  have hbS : b < sSup (Rval f) := by rwa [hS1]
  rcases exists_lt_of_lt_csSup (Rval_nonempty f hc₀₁) hbS with ⟨w, hwR, hbw⟩
  rcases hwR with ⟨u, hfu⟩
  have hsub1 : f '' {s : Dom c₀ | (s : ℝ) < (u : ℝ)} ⊆ {t : ORI | b < (t : ℝ)} := by
    rw [Set.image_subset_iff]
    intro s hs
    have hgt : (f u : ℝ) < (f s : ℝ) := hdec hs
    have hb : b < (f s : ℝ) := by linarith
    exact hb
  exact closure_mono (Set.image_mono hsub1) (hzcl u)

end ArcBranchRight


/-- **Arc branch right dichotomy.**  An open arc `a : (0,1) → X` of a
Hausdorff space, a point `z` outside its image, and a continuous injective
right-branch reparametrisation `f : (c₀,1) → (0,1)` whose every initial
prefix `{s < u}` accumulates (under `a ∘ f`) at `z`: then either `z` lies
in the closure of every right terminal segment of `a` (right-end
attraction, Branch 1), or the coordinate range of `f` contains a whole
initial real segment `(0,δ)` (Branch 2).

Proof: a continuous injective `f` is strictly monotone.  If `f` is
increasing, the prefixes lie just above the infimum `L` of its range; if
`L > 0` the closure condition forces `z = a(L) ∈ range a`,
contradiction, so `L = 0` and the (interval-like) range covers `(0,δ)`
(Branch 2).  If `f` is decreasing, its prefixes lie just below the
supremum `S`; if `S < 1` the same argument gives `z = a(S) ∈ range a`,
contradiction, so `S = 1`, and every terminal segment `(b,1)` contains a
whole prefix, giving right-end attraction (Branch 1). -/
theorem arc_branch_right_dichotomy {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → X)
    (ha_cont : Continuous a)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (z : X) (hz_out : z ∉ Set.range a)
    (f : {s : ℝ // s ∈ Set.Ioo c₀ 1} → {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1})
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    (hzcl : ∀ u : {s : ℝ // s ∈ Set.Ioo c₀ 1},
        z ∈ closure (a '' (f '' {t : {s : ℝ // s ∈ Set.Ioo c₀ 1} | (t : ℝ) < (u : ℝ)}))) :
    (∀ b : ℝ, 0 < b → b < 1 →
      z ∈ closure (a '' {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | b < (t : ℝ)})) ∨
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∃ s : {s : ℝ // s ∈ Set.Ioo c₀ 1}, (f s : ℝ) = t) := by
  classical
  rcases ArcBranchRight.fval_mono_or_anti (f := f) hc₀₁ hf_cont hf_inj with hinc | hdec
  · right
    exact ArcBranchRight.branch2_of_increasing a ha_cont hc₀₁ z hz_out f hf_cont hf_inj
      hzcl hinc
  · left
    exact ArcBranchRight.branch1_of_decreasing a ha_cont hc₀₁ z hz_out f hf_cont hf_inj
      hzcl hdec

end Commons.Topology.OneManifold