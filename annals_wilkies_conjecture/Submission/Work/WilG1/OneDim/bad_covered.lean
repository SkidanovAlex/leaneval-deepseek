import Mathlib
import Submission.Work.WilG1.OneDim.Defs

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilG1.OneDim

open Work.WilG1

/-! # Covering the non-differentiability set

We prove that a point at which `g : ℝ → ℝ` fails to be differentiable is either a point of
oscillation (with a rational level `q`), a point where the two-sided difference quotient tends
to `±∞`, or a corner (a strict local extremum of `g - q·x` for a rational `q`).

The proof is a case analysis on the one-sided limits (in `EReal`) of the difference quotient
`dq g x`.  The key analytic ingredient is `oscill_or_tendsto` below: if `u : α → ℝ` does *not*
oscillate around any rational level along a filter `f`, then `u` has a limit in `EReal` along `f`.
-/

/-! ## Filter descriptions of the one-sided neighbourhoods -/

lemma eventually_nhdsGT_iff {P : ℝ → Prop} {x : ℝ} :
    (∀ᶠ y in 𝓝[>] x, P y) ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → P y := by
  rw [(nhdsGT_basis x).eventually_iff]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b - x, sub_pos.mpr hb,
      fun y hy1 hy2 => h (show y ∈ Set.Ioo x b from ⟨hy1, by linarith⟩)⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨x + δ, by linarith, fun y hy => h y hy.1 (by linarith [hy.2])⟩

lemma eventually_nhdsLT_iff {P : ℝ → Prop} {x : ℝ} :
    (∀ᶠ y in 𝓝[<] x, P y) ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → P y := by
  rw [(nhdsLT_basis x).eventually_iff]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨x - b, sub_pos.mpr hb,
      fun y hy1 hy2 => h (show y ∈ Set.Ioo b x from ⟨by linarith [hy1], hy2⟩)⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨x - δ, by linarith, fun y hy => h y (by linarith [hy.1]) hy.2⟩

lemma frequently_nhdsGT_iff {P : ℝ → Prop} {x : ℝ} :
    (∃ᶠ y in 𝓝[>] x, P y) ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ P y := by
  rw [(nhdsGT_basis x).frequently_iff]
  constructor
  · intro h δ hδ
    rcases h (x + δ) (by linarith) with ⟨y, hy, hPy⟩
    exact ⟨y, hy.1, by linarith [hy.2], hPy⟩
  · rintro h b hb
    rcases h (b - x) (sub_pos.mpr hb) with ⟨y, hy1, hy2, hPy⟩
    exact ⟨y, ⟨hy1, by linarith⟩, hPy⟩

lemma frequently_nhdsLT_iff {P : ℝ → Prop} {x : ℝ} :
    (∃ᶠ y in 𝓝[<] x, P y) ↔ ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ P y := by
  rw [(nhdsLT_basis x).frequently_iff]
  constructor
  · intro h δ hδ
    rcases h (x - δ) (by linarith) with ⟨y, hy, hPy⟩
    exact ⟨y, by linarith [hy.1], hy.2, hPy⟩
  · rintro h b hb
    rcases h (x - b) (sub_pos.mpr hb) with ⟨y, hy1, hy2, hPy⟩
    exact ⟨y, ⟨by linarith, hy2⟩, hPy⟩

/-! ## Translating the sets of `Defs.lean` into filter statements -/

lemma mem_oscR_iff_freq {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ oscR g q ↔ (∃ᶠ y in 𝓝[>] x, q < dq g x y) ∧ (∃ᶠ y in 𝓝[>] x, dq g x y < q) := by
  rw [oscR, Set.mem_ofPred_eq, frequently_nhdsGT_iff, frequently_nhdsGT_iff]

lemma mem_oscL_iff_freq {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ oscL g q ↔ (∃ᶠ y in 𝓝[<] x, q < dq g x y) ∧ (∃ᶠ y in 𝓝[<] x, dq g x y < q) := by
  rw [oscL, Set.mem_ofPred_eq, frequently_nhdsLT_iff, frequently_nhdsLT_iff]

lemma mem_cornerMax_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ cornerMax g q ↔ (∀ᶠ y in 𝓝[>] x, dq g x y < q) ∧ (∀ᶠ y in 𝓝[<] x, q < dq g x y) := by
  rw [cornerMax, Set.mem_ofPred_eq, eventually_nhdsGT_iff, eventually_nhdsLT_iff]
  constructor
  · rintro ⟨⟨δ1, hδ1, h1⟩, ⟨δ2, hδ2, h2⟩⟩
    exact ⟨⟨δ1, hδ1, fun y hy1 hy2 => (div_lt_iff₀ (by linarith)).2 (h1 y hy1 hy2)⟩,
           ⟨δ2, hδ2, fun y hy1 hy2 => (lt_div_iff_of_neg (by linarith)).2 (h2 y hy1 hy2)⟩⟩
  · rintro ⟨⟨δ1, hδ1, h1⟩, ⟨δ2, hδ2, h2⟩⟩
    exact ⟨⟨δ1, hδ1, fun y hy1 hy2 => (div_lt_iff₀ (by linarith)).1 (h1 y hy1 hy2)⟩,
           ⟨δ2, hδ2, fun y hy1 hy2 => (lt_div_iff_of_neg (by linarith)).1 (h2 y hy1 hy2)⟩⟩

lemma mem_cornerMin_iff {g : ℝ → ℝ} {q x : ℝ} :
    x ∈ cornerMin g q ↔ (∀ᶠ y in 𝓝[>] x, q < dq g x y) ∧ (∀ᶠ y in 𝓝[<] x, dq g x y < q) := by
  rw [cornerMin, Set.mem_ofPred_eq, eventually_nhdsGT_iff, eventually_nhdsLT_iff]
  constructor
  · rintro ⟨⟨δ1, hδ1, h1⟩, ⟨δ2, hδ2, h2⟩⟩
    exact ⟨⟨δ1, hδ1, fun y hy1 hy2 => (lt_div_iff₀ (by linarith)).2 (h1 y hy1 hy2)⟩,
           ⟨δ2, hδ2, fun y hy1 hy2 => (div_lt_iff_of_neg (by linarith)).2 (h2 y hy1 hy2)⟩⟩
  · rintro ⟨⟨δ1, hδ1, h1⟩, ⟨δ2, hδ2, h2⟩⟩
    exact ⟨⟨δ1, hδ1, fun y hy1 hy2 => (lt_div_iff₀ (by linarith)).1 (h1 y hy1 hy2)⟩,
           ⟨δ2, hδ2, fun y hy1 hy2 => (div_lt_iff_of_neg (by linarith)).1 (h2 y hy1 hy2)⟩⟩

/-! ## The one-sided limits of the difference quotient -/

/-- If `u` does not oscillate around any rational level along `f`, then `u` tends to a limit in
the extended reals along `f`. -/
lemma oscill_or_tendsto {α : Type*} (f : Filter α) (u : α → ℝ) :
    (∃ q : ℚ, (∃ᶠ a in f, (q : ℝ) < u a) ∧ (∃ᶠ a in f, u a < (q : ℝ)))
    ∨ (∃ c : EReal, Filter.Tendsto (fun a => (u a : EReal)) f (nhds c)) := by
  by_cases hosc : ∃ q : ℚ, (∃ᶠ a in f, (q : ℝ) < u a) ∧ (∃ᶠ a in f, u a < (q : ℝ))
  · exact Or.inl hosc
  right
  have hAB : ∀ q : ℚ, (∀ᶠ a in f, u a ≤ (q : ℝ)) ∨ (∀ᶠ a in f, (q : ℝ) ≤ u a) := by
    intro q
    rcases not_and_or.mp (fun hq => hosc ⟨q, hq⟩) with h | h
    · left
      rw [not_frequently] at h
      exact h.mono (fun a ha => not_lt.mp ha)
    · right
      rw [not_frequently] at h
      exact h.mono (fun a ha => not_lt.mp ha)
  let S : Set EReal := {c | ∃ q : ℚ, (∀ᶠ a in f, u a ≤ (q : ℝ)) ∧ c = ((q : ℝ) : EReal)}
  have hS : ∀ q : ℚ, (∀ᶠ a in f, u a ≤ (q : ℝ)) → ((q : ℝ) : EReal) ∈ S :=
    fun q hq => ⟨q, hq, rfl⟩
  have F2 : ∀ q : ℚ, sInf S < ((q : ℝ) : EReal) → (∀ᶠ a in f, u a ≤ (q : ℝ)) := by
    intro q hq
    by_contra hnot
    have hle : ((q : ℝ) : EReal) ≤ sInf S := by
      apply le_sInf
      intro c hc
      rcases hc with ⟨r, hr, rfl⟩
      have hqr : (q : ℝ) ≤ (r : ℝ) := by
        by_contra hlt
        rw [not_le] at hlt
        exact hnot (by filter_upwards [hr] with a ha; exact le_trans ha (le_of_lt hlt))
      exact EReal.coe_le_coe_iff.mpr hqr
    exact absurd hle (not_le_of_gt hq)
  refine ⟨sInf S, ?_⟩
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨r, hbr, hrs⟩ := EReal.lt_iff_exists_rat_btwn.mp hb
    have hnr : ¬ (∀ᶠ a in f, u a ≤ (r : ℝ)) :=
      fun h => absurd (sInf_le (hS r h)) (not_le_of_gt hrs)
    have hBr : (∀ᶠ a in f, (r : ℝ) ≤ u a) := by
      rcases hAB r with h | h
      · exact absurd h hnr
      · exact h
    filter_upwards [hBr] with a ha
    exact lt_of_lt_of_le hbr (EReal.coe_le_coe_iff.mpr ha)
  · intro b hb
    obtain ⟨r, hcr, hrb⟩ := EReal.lt_iff_exists_rat_btwn.mp hb
    have hAr := F2 r hcr
    filter_upwards [hAr] with a ha
    exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr ha) hrb

/-- A one-sided limit bounds the difference quotient from above/below eventually. -/
lemma Rhi_of_tendsto {g : ℝ → ℝ} {x : ℝ} {cr : EReal}
    (h : Filter.Tendsto (fun y => (dq g x y : EReal)) (𝓝[>] x) (nhds cr)) :
    ∀ q : ℝ, (q : EReal) < cr → ∀ᶠ y in 𝓝[>] x, q < dq g x y := by
  intro q hq
  filter_upwards [h.eventually (isOpen_Ioi.mem_nhds hq)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

lemma Rlo_of_tendsto {g : ℝ → ℝ} {x : ℝ} {cr : EReal}
    (h : Filter.Tendsto (fun y => (dq g x y : EReal)) (𝓝[>] x) (nhds cr)) :
    ∀ q : ℝ, cr < (q : EReal) → ∀ᶠ y in 𝓝[>] x, dq g x y < q := by
  intro q hq
  filter_upwards [h.eventually (isOpen_Iio.mem_nhds hq)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

lemma Lhi_of_tendsto {g : ℝ → ℝ} {x : ℝ} {cl : EReal}
    (h : Filter.Tendsto (fun y => (dq g x y : EReal)) (𝓝[<] x) (nhds cl)) :
    ∀ q : ℝ, (q : EReal) < cl → ∀ᶠ y in 𝓝[<] x, q < dq g x y := by
  intro q hq
  filter_upwards [h.eventually (isOpen_Ioi.mem_nhds hq)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

lemma Llo_of_tendsto {g : ℝ → ℝ} {x : ℝ} {cl : EReal}
    (h : Filter.Tendsto (fun y => (dq g x y : EReal)) (𝓝[<] x) (nhds cl)) :
    ∀ q : ℝ, cl < (q : EReal) → ∀ᶠ y in 𝓝[<] x, dq g x y < q := by
  intro q hq
  filter_upwards [h.eventually (isOpen_Iio.mem_nhds hq)] with y hy
  exact EReal.coe_lt_coe_iff.mp hy

/-! ## The infinite-derivative sets -/

lemma mem_infDeriv_one {g : ℝ → ℝ} {x : ℝ}
    (hR : ∀ M : ℝ, ∀ᶠ y in 𝓝[>] x, M < dq g x y)
    (hL : ∀ M : ℝ, ∀ᶠ y in 𝓝[<] x, M < dq g x y) : x ∈ infDeriv g 1 := by
  intro M hM
  rcases eventually_nhdsGT_iff.mp (hR M) with ⟨δ1, hδ1, h1⟩
  rcases eventually_nhdsLT_iff.mp (hL M) with ⟨δ2, hδ2, h2⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hyne hy => ?_⟩
  have hM' : M < dq g x y := by
    rw [abs_lt] at hy
    rcases lt_or_gt_of_ne hyne.symm with hxy | hyx
    · exact h1 y hxy (by linarith [min_le_left δ1 δ2, hy.2])
    · exact h2 y (by linarith [min_le_right δ1 δ2, hy.1]) hyx
  simpa using hM'

lemma mem_infDeriv_neg_one {g : ℝ → ℝ} {x : ℝ}
    (hR : ∀ M : ℝ, ∀ᶠ y in 𝓝[>] x, dq g x y < M)
    (hL : ∀ M : ℝ, ∀ᶠ y in 𝓝[<] x, dq g x y < M) : x ∈ infDeriv g (-1) := by
  intro M hM
  rcases eventually_nhdsGT_iff.mp (hR (-M)) with ⟨δ1, hδ1, h1⟩
  rcases eventually_nhdsLT_iff.mp (hL (-M)) with ⟨δ2, hδ2, h2⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hyne hy => ?_⟩
  have hM' : dq g x y < -M := by
    rw [abs_lt] at hy
    rcases lt_or_gt_of_ne hyne.symm with hxy | hyx
    · exact h1 y hxy (by linarith [min_le_left δ1 δ2, hy.2])
    · exact h2 y (by linarith [min_le_right δ1 δ2, hy.1]) hyx
  have := neg_lt_neg hM'
  simpa using this

/-- The slope of `g` at `x` is the difference quotient `dq g x`. -/
private lemma slope_eq_dq (g : ℝ → ℝ) (x : ℝ) : slope g x = dq g x :=
  funext fun y => by rw [slope_def_field, dq]

theorem bad_covered {g : ℝ → ℝ} {x : ℝ} (hbad : x ∈ Work.WilG1.badSet g) :
    (∃ q : ℚ, x ∈ Work.WilG1.oscR g (q : ℝ) ∨ x ∈ Work.WilG1.oscL g (q : ℝ))
    ∨ x ∈ Work.WilG1.infDeriv g 1 ∨ x ∈ Work.WilG1.infDeriv g (-1)
    ∨ (∃ q : ℚ, x ∈ Work.WilG1.cornerMax g (q : ℝ) ∨ x ∈ Work.WilG1.cornerMin g (q : ℝ)) := by
  have hnd : ¬ DifferentiableAt ℝ g x := hbad
  rcases oscill_or_tendsto (𝓝[>] x) (dq g x) with ⟨q, hq1, hq2⟩ | ⟨cr, hcr⟩
  · exact Or.inl ⟨q, Or.inl (mem_oscR_iff_freq.mpr ⟨hq1, hq2⟩)⟩
  rcases oscill_or_tendsto (𝓝[<] x) (dq g x) with ⟨q, hq1, hq2⟩ | ⟨cl, hcl⟩
  · exact Or.inl ⟨q, Or.inr (mem_oscL_iff_freq.mpr ⟨hq1, hq2⟩)⟩
  have hRhi : ∀ q : ℝ, (q : EReal) < cr → ∀ᶠ y in 𝓝[>] x, q < dq g x y := Rhi_of_tendsto hcr
  have hRlo : ∀ q : ℝ, cr < (q : EReal) → ∀ᶠ y in 𝓝[>] x, dq g x y < q := Rlo_of_tendsto hcr
  have hLhi : ∀ q : ℝ, (q : EReal) < cl → ∀ᶠ y in 𝓝[<] x, q < dq g x y := Lhi_of_tendsto hcl
  have hLlo : ∀ q : ℝ, cl < (q : EReal) → ∀ᶠ y in 𝓝[<] x, dq g x y < q := Llo_of_tendsto hcl
  have trich : ∀ a : EReal, a = ⊤ ∨ a = ⊥ ∨ ∃ c : ℝ, a = (c : EReal) := by
    intro a
    rcases eq_or_ne a ⊤ with h | h
    · exact Or.inl h
    rcases eq_or_ne a ⊥ with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨a.toReal, (EReal.coe_toReal h h2).symm⟩)
  rcases trich cr with hcrT | hcrB | ⟨Lr, hcrL⟩
  · -- cr = ⊤
    subst hcrT
    have hRhi' : ∀ q : ℝ, ∀ᶠ y in 𝓝[>] x, q < dq g x y := fun q => hRhi q (EReal.coe_lt_top q)
    rcases trich cl with hclT | hclB | ⟨Ll, hclL⟩
    · subst hclT
      have hLhi' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, q < dq g x y := fun q => hLhi q (EReal.coe_lt_top q)
      exact Or.inr (Or.inl (mem_infDeriv_one hRhi' hLhi'))
    · subst hclB
      have hLlo' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, dq g x y < q := fun q => hLlo q (EReal.bot_lt_coe q)
      exact Or.inr (Or.inr (Or.inr ⟨(0 : ℚ),
        Or.inr (mem_cornerMin_iff.mpr ⟨hRhi' ((0 : ℚ) : ℝ), hLlo' ((0 : ℚ) : ℝ)⟩)⟩))
    · subst hclL
      obtain ⟨r, hr⟩ := exists_rat_gt Ll
      exact Or.inr (Or.inr (Or.inr ⟨r,
        Or.inr (mem_cornerMin_iff.mpr ⟨hRhi' r, hLlo r (EReal.coe_lt_coe_iff.mpr hr)⟩)⟩))
  · -- cr = ⊥
    subst hcrB
    have hRlo' : ∀ q : ℝ, ∀ᶠ y in 𝓝[>] x, dq g x y < q := fun q => hRlo q (EReal.bot_lt_coe q)
    rcases trich cl with hclT | hclB | ⟨Ll, hclL⟩
    · subst hclT
      have hLhi' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, q < dq g x y := fun q => hLhi q (EReal.coe_lt_top q)
      exact Or.inr (Or.inr (Or.inr ⟨(0 : ℚ),
        Or.inl (mem_cornerMax_iff.mpr ⟨hRlo' ((0 : ℚ) : ℝ), hLhi' ((0 : ℚ) : ℝ)⟩)⟩))
    · subst hclB
      have hLlo' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, dq g x y < q := fun q => hLlo q (EReal.bot_lt_coe q)
      exact Or.inr (Or.inr (Or.inl (mem_infDeriv_neg_one hRlo' hLlo')))
    · subst hclL
      obtain ⟨r, hr⟩ := exists_rat_lt Ll
      exact Or.inr (Or.inr (Or.inr ⟨r,
        Or.inl (mem_cornerMax_iff.mpr ⟨hRlo' r, hLhi r (EReal.coe_lt_coe_iff.mpr hr)⟩)⟩))
  · -- cr = (Lr : ℝ)
    subst hcrL
    rcases trich cl with hclT | hclB | ⟨Ll, hclL⟩
    · subst hclT
      have hLhi' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, q < dq g x y := fun q => hLhi q (EReal.coe_lt_top q)
      obtain ⟨r, hr⟩ := exists_rat_gt Lr
      exact Or.inr (Or.inr (Or.inr ⟨r,
        Or.inl (mem_cornerMax_iff.mpr ⟨hRlo r (EReal.coe_lt_coe_iff.mpr hr), hLhi' r⟩)⟩))
    · subst hclB
      have hLlo' : ∀ q : ℝ, ∀ᶠ y in 𝓝[<] x, dq g x y < q := fun q => hLlo q (EReal.bot_lt_coe q)
      obtain ⟨r, hr⟩ := exists_rat_lt Lr
      exact Or.inr (Or.inr (Or.inr ⟨r,
        Or.inr (mem_cornerMin_iff.mpr ⟨hRhi r (EReal.coe_lt_coe_iff.mpr hr), hLlo' r⟩)⟩))
    · subst hclL
      rcases lt_trichotomy Lr Ll with hlt | heq | hgt
      · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
        exact Or.inr (Or.inr (Or.inr ⟨r,
          Or.inl (mem_cornerMax_iff.mpr ⟨hRlo r (EReal.coe_lt_coe_iff.mpr hr1),
            hLhi r (EReal.coe_lt_coe_iff.mpr hr2)⟩)⟩))
      · subst heq
        have hR2 : Filter.Tendsto (fun y => dq g x y) (𝓝[>] x) (𝓝 Lr) := EReal.tendsto_coe.mp hcr
        have hL2 : Filter.Tendsto (fun y => dq g x y) (𝓝[<] x) (𝓝 Lr) := EReal.tendsto_coe.mp hcl
        have ht : Filter.Tendsto (slope g x) (𝓝[≠] x) (𝓝 Lr) := by
          rw [slope_eq_dq, ← nhdsLT_sup_nhdsGT]
          exact tendsto_sup.mpr ⟨hL2, hR2⟩
        exact absurd ((hasDerivAt_iff_tendsto_slope.mpr ht).differentiableAt) hnd
      · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hgt
        exact Or.inr (Or.inr (Or.inr ⟨r,
          Or.inr (mem_cornerMin_iff.mpr ⟨hRhi r (EReal.coe_lt_coe_iff.mpr hr2),
            hLlo r (EReal.coe_lt_coe_iff.mpr hr1)⟩)⟩))

end Work.WilG1.OneDim
