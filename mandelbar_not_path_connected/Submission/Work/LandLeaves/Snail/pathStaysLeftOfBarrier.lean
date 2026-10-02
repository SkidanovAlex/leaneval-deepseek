import Mathlib
import Submission.Work.LandLeaves.Snail.rightCrossDefs
import Submission.Commons.Topology.Jordan.crossing_lemma_rect

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The path stays strictly left of the barrier

Companion file for `Work.LandLeaves.Snail.pathStaysLeftOfBarrier`; it contains the weakened
hypothesis version of the planar separation theorem for paths (`path_re_lt_of_mem_region_h`,
adapted from `Submission/Work/LandLeaves/Snail/component_re_lt.lean` so that only the height
growth of `F` is assumed, not the full drift bound) and the main theorem.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

/-- **The barrier fibre at height `(P t₀).im + 1` is bounded below by `M`.**

This is where the band hypothesis `hM` is used: the leftmost point of the barrier at that height
exists (`exists_barrier_min`) and is `≥ M`; since every barrier point there has real part `< X₁`,
we also get `M < X₁`. -/
lemma fibre_re_ge_h {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h) :
    M < X₁ ∧ ∀ W ∈ pathTail P t₀, W.im = (P t₀).im + 1 → M ≤ W.re := by
  have hT : T ≤ t₀ := by linarith
  have hband : (P t₀).im + 1 ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)) :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  obtain ⟨W₀, hW₀mem, -, hW₀re, hW₀min⟩ :=
    exists_barrier_min (F := F) (P := P) (c := c) (T := T) (X₀ := X₁) (t₀ := t₀)
      (h := (P t₀).im + 1) hc_im hPc hT hheight hPinv hPt (by linarith)
  have hleft : M ≤ leftCross P t₀ ((P t₀).im + 1) := hM _ hband
  have hW₀lt : W₀.re < X₁ := by
    rw [pathTail] at hW₀mem
    obtain ⟨u, hu, rfl⟩ := hW₀mem
    exact hPt u hu
  refine ⟨lt_of_le_of_lt (hleft.trans_eq hW₀re.symm) hW₀lt, ?_⟩
  intro W hW hWim
  exact (hleft.trans_eq hW₀re.symm).trans (hW₀min W hW hWim)

/-- **Path form of the separation.**  No path inside `{re < X ∧ (P t₀).im < im} \ pathTail P t₀`
starting at the base point `⟨M - 1, (P t₀).im + 1⟩` can reach a point of real part `≥ X₁`. -/
theorem path_re_lt_of_mem_region_h {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h)
    {Z : ℂ} (γ : Path ⟨M - 1, (P t₀).im + 1⟩ Z)
    (hγ : ∀ t : unitInterval, γ t ∈ {W : ℂ | W.re < X ∧ (P t₀).im < W.im} \ pathTail P t₀) :
    Z.re < X₁ := by
  classical
  obtain ⟨hMX₁, hfib⟩ :=
    fibre_re_ge_h (F := F) (X := X) (X₁ := X₁) (c := c) (P := P) (T := T) (t₀ := t₀) (M := M)
      hc_im hX₁X hheight hPc htT hPinv hPt hM
  have hγR : ∀ t : unitInterval,
      γ t ∈ {W : ℂ | W.re < X ∧ (P t₀).im < W.im} \ pathTail P t₀ := hγ
  by_contra hcon
  push Not at hcon
  have hT : T ≤ t₀ := by linarith
  -- ## a time at which the barrier reaches any prescribed height
  have him_unbdd : ∀ H : ℝ, (P t₀).im < H → ∃ t : ℝ, t₀ ≤ t ∧ (P t).im = H := by
    intro H hH
    obtain ⟨m, hm1, hm2⟩ :=
      im_lower_bound_linear (F := F) (P := P) (c := c) (T := T) (X₀ := X₁) (t₀ := t₀)
        hc_im hheight hPinv hPc hT hPt
    have hm_le : m ≤ (P t₀).im := hm1 t₀ ⟨le_rfl, by linarith⟩
    have hc2 : 0 < c.im / 2 := by linarith
    set s : ℝ := t₀ + 1 + (H - m) / (c.im / 2) with hs
    have hst : t₀ ≤ s := by
      rw [hs]
      have hpos : 0 < (H - m) / (c.im / 2) := div_pos (by linarith) hc2
      linarith
    have hHs : H ≤ (P s).im := by
      have h1 := hm2 s hst
      have h2 : (s - t₀ - 1) * (c.im / 2) = H - m := by
        rw [hs]
        field_simp
        ring
      rw [h2] at h1
      linarith
    have hcont : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc t₀ s) := by
      have h1 : ContinuousOn P (Set.Icc t₀ s) := hPc.mono (fun t ht => le_trans hT ht.1)
      simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn h1
    have hmem : H ∈ Set.Icc ((fun t : ℝ => (P t).im) t₀) ((fun t : ℝ => (P t).im) s) :=
      ⟨le_of_lt hH, hHs⟩
    obtain ⟨t, ht, hteq⟩ := (intermediate_value_Icc hst hcont) hmem
    exact ⟨t, ht.1, hteq⟩
  -- ## the maximal height of the path
  haveI : CompactSpace unitInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hcontγ : ContinuousOn (fun t : unitInterval => (γ t).im) Set.univ :=
    (Complex.continuous_im.comp γ.continuous).continuousOn
  obtain ⟨tmax, -, htmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcontγ
  set Hh : ℝ := (γ tmax).im with hHh
  have hHh_le : ∀ t : unitInterval, (γ t).im ≤ Hh := fun t => htmax (Set.mem_univ t)
  have hHh_leR : ∀ t : unitInterval, (γ t).im ≤ Hh := hHh_le
  have hHh_gt : (P t₀).im < Hh := by
    have h1 : (γ (0 : unitInterval)).im = (P t₀).im + 1 := by rw [γ.source]
    calc (P t₀).im < (P t₀).im + 1 := by linarith
      _ = (γ 0).im := h1.symm
      _ ≤ Hh := hHh_leR 0
  have hHh_ge : (P t₀).im + 1 ≤ Hh := by
    have h1 : (γ (0 : unitInterval)).im = (P t₀).im + 1 := by rw [γ.source]
    rw [← h1]
    exact hHh_leR 0
  -- ## the first time the barrier reaches the height `Hh`
  have hpre_closed : ∀ y : ℝ, IsClosed ({t : ℝ | (P t).im = y} ∩ Set.Ici T) := by
    intro y
    have h1 : ContinuousOn (fun t : ℝ => (P t).im) (Set.Ici T) := by
      simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn hPc
    have h2 : IsClosed (Set.Ici T ∩ (fun t : ℝ => (P t).im) ⁻¹' ({y} : Set ℝ)) :=
      h1.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
    convert h2 using 1
    ext t
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  set Tset : Set ℝ := {t : ℝ | t₀ ≤ t ∧ (P t).im = Hh} with hTset
  have hTset_closed : IsClosed Tset := by
    have h1 : Tset = Set.Ici t₀ ∩ ({t : ℝ | (P t).im = Hh} ∩ Set.Ici T) := by
      ext t
      constructor
      · rintro ⟨ht, hh⟩; exact ⟨ht, hh, le_trans hT ht⟩
      · rintro ⟨ht, hh, -⟩; exact ⟨ht, hh⟩
    rw [h1]
    exact isClosed_Ici.inter (hpre_closed Hh)
  obtain ⟨tH, htHge, htHh⟩ := him_unbdd Hh hHh_gt
  have hTset_ne : Tset.Nonempty := ⟨tH, htHge, htHh⟩
  have hTset_bdd : BddBelow Tset := ⟨t₀, fun x hx => hx.1⟩
  set ts : ℝ := sInf Tset with hts
  have hts_mem : ts ∈ Tset := hTset_closed.csInf_mem hTset_ne hTset_bdd
  have hts_ge : t₀ ≤ ts := hts_mem.1
  have hts_H : (P ts).im = Hh := hts_mem.2
  have hts_le : ∀ t ∈ Tset, ts ≤ t := fun t ht => csInf_le hTset_bdd ht
  have hts_first : ∀ t : ℝ, t₀ ≤ t → t < ts → (P t).im < Hh := by
    intro t htge htlt
    rcases lt_trichotomy (P t).im Hh with h | h | h
    · exact h
    · exact absurd (hts_le t ⟨htge, h⟩) (not_le.mpr htlt)
    · exfalso
      have hcont : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t₀ t) := by
        have h1 : ContinuousOn P (Set.Icc t₀ t) := hPc.mono (fun u hu => le_trans hT hu.1)
        simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn h1
      have hmem : Hh ∈ Set.Icc ((fun u : ℝ => (P u).im) t₀) ((fun u : ℝ => (P u).im) t) :=
        ⟨le_of_lt hHh_gt, le_of_lt h⟩
      obtain ⟨u, hu, hueq⟩ := (intermediate_value_Icc htge hcont) hmem
      have := hts_le u ⟨hu.1, hueq⟩
      linarith [hu.2]
  -- ## the excursion of the barrier containing `ts`
  set Zset : Set ℝ := {t : ℝ | t ∈ Set.Icc t₀ ts ∧ (P t).im = (P t₀).im} with hZset
  have hZset_closed : IsClosed Zset := by
    have h1 : Zset = Set.Icc t₀ ts ∩ ({t : ℝ | (P t).im = (P t₀).im} ∩ Set.Ici T) := by
      ext t
      constructor
      · rintro ⟨ht, hh⟩; exact ⟨ht, hh, le_trans hT ht.1⟩
      · rintro ⟨ht, hh, -⟩; exact ⟨ht, hh⟩
    rw [h1]
    exact isClosed_Icc.inter (hpre_closed ((P t₀).im))
  have hZset_comp : IsCompact Zset :=
    isCompact_Icc.of_isClosed_subset hZset_closed (fun t ht => ht.1)
  have hZset_ne : Zset.Nonempty := ⟨t₀, ⟨le_rfl, hts_ge⟩, rfl⟩
  obtain ⟨as, has_mem, has_max⟩ := hZset_comp.exists_isMaxOn hZset_ne continuousOn_id
  have has_ge : t₀ ≤ as := has_mem.1.1
  have has_le : as ≤ ts := has_mem.1.2
  have has_im : (P as).im = (P t₀).im := has_mem.2
  have has_gt : ∀ t : ℝ, as < t → t ≤ ts → (P t₀).im < (P t).im := by
    intro t hat htle
    rcases lt_trichotomy (P t).im (P t₀).im with h | h | h
    · exfalso
      have hcont : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t ts) := by
        have h1 : ContinuousOn P (Set.Icc t ts) :=
          hPc.mono (fun u hu => le_trans hT (le_trans (by linarith [hat, has_ge]) hu.1))
        simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn h1
      have hmem : (P t₀).im ∈ Set.Icc ((fun u : ℝ => (P u).im) t) ((fun u : ℝ => (P u).im) ts) :=
        ⟨le_of_lt h, by change (P t₀).im ≤ (P ts).im; rw [hts_H]; exact le_of_lt hHh_gt⟩
      obtain ⟨u, hu, hueq⟩ := (intermediate_value_Icc htle hcont) hmem
      have huZ : u ∈ Zset :=
        ⟨⟨le_trans has_ge (le_of_lt (lt_of_lt_of_le hat hu.1)), hu.2⟩, hueq⟩
      have hu_as : u ≤ as := by simpa using has_max huZ
      linarith [hu.1, hat]
    · exfalso
      have htZ : t ∈ Zset := ⟨⟨le_trans has_ge (le_of_lt hat), htle⟩, h⟩
      have ht_as : t ≤ as := by simpa using has_max htZ
      linarith
    · exact h
  -- ## a lower bound for the real part along the barrier arc `[as, ts]`
  obtain ⟨rmin, hrmin⟩ : ∃ rmin : ℝ, ∀ t ∈ Set.Icc as ts, rmin ≤ (P t).re := by
    have hcont : ContinuousOn (fun t : ℝ => (P t).re) (Set.Icc as ts) := by
      have h1 : ContinuousOn P (Set.Icc as ts) :=
        hPc.mono (fun t ht => le_trans hT (le_trans has_ge ht.1))
      simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn h1
    obtain ⟨x, -, hxmin⟩ := isCompact_Icc.exists_isMinOn ⟨as, le_rfl, has_le⟩ hcont
    exact ⟨(P x).re, fun t ht => hxmin ht⟩
  -- ## a lower bound for the real part along the path
  obtain ⟨rminγ, hrminγ⟩ : ∃ rminγ : ℝ, ∀ t : unitInterval, rminγ ≤ (γ t).re := by
    have hcont : ContinuousOn (fun t : unitInterval => (γ t).re) Set.univ :=
      (Complex.continuous_re.comp γ.continuous).continuousOn
    obtain ⟨x, -, hxmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hcont
    exact ⟨(γ x).re, fun t => hxmin (Set.mem_univ t)⟩
  have hrminγR : ∀ t : unitInterval, rminγ ≤ (γ t).re := hrminγ
  -- ## the two endpoints of the extended path
  set a0 : ℝ := min (M - 2) (min (rmin - 1) (rminγ - 1)) with ha0
  have ha0_le_M : a0 ≤ M - 2 := by rw [ha0]; exact min_le_left _ _
  have ha0_le_r : a0 ≤ rmin - 1 := by
    rw [ha0]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ha0_le_γ : a0 ≤ rminγ - 1 := by
    rw [ha0]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have ha0_lt_z : a0 < M - 1 := by linarith
  have ha0_lt_X : a0 < X := by linarith
  set A : ℂ := ⟨a0, (P t₀).im + 1⟩ with hA
  set B : ℂ := ⟨X, Z.im⟩ with hB
  let p1 : Path A (⟨M - 1, (P t₀).im + 1⟩ : ℂ) :=
    Path.segment A (⟨M - 1, (P t₀).im + 1⟩ : ℂ)
  let p3 : Path Z B := Path.segment Z B
  -- the three pieces of the extended path, and their mutual bounds
  have hp1 : ∀ w ∈ Set.range p1, w.re ∈ Set.Icc a0 (M - 1) ∧ w.im = (P t₀).im + 1 := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    have hre : (p1 u).re = a0 + (u : ℝ) * (M - 1 - a0) := by
      show (Path.segment A (⟨M - 1, (P t₀).im + 1⟩ : ℂ) u).re = a0 + (u : ℝ) * (M - 1 - a0)
      rw [Path.segment_apply, AffineMap.lineMap_apply]
      simp [Complex.add_re, Complex.mul_re]
      ring
    have him : (p1 u).im = (P t₀).im + 1 := by
      show (Path.segment A (⟨M - 1, (P t₀).im + 1⟩ : ℂ) u).im = (P t₀).im + 1
      rw [Path.segment_apply, AffineMap.lineMap_apply]
      simp [Complex.add_im, Complex.mul_im, hA]
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    refine ⟨⟨?_, ?_⟩, him⟩
    · rw [hre]; nlinarith
    · rw [hre]; nlinarith
  have hp3 : ∀ w ∈ Set.range p3, Z.re ≤ w.re ∧ w.re ≤ X ∧ w.im = Z.im := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    have hre : (p3 u).re = Z.re + (u : ℝ) * (X - Z.re) := by
      show (Path.segment Z B u).re = Z.re + (u : ℝ) * (X - Z.re)
      rw [Path.segment_apply, AffineMap.lineMap_apply]
      simp [Complex.add_re, Complex.mul_re]
      ring
    have him : (p3 u).im = Z.im := by
      show (Path.segment Z B u).im = Z.im
      rw [Path.segment_apply, AffineMap.lineMap_apply]
      simp [Complex.add_im, Complex.mul_im, hB]
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    have hZX : Z.re < X := by
      have h := (hγR 1).1.1
      rw [γ.target] at h
      exact h
    refine ⟨?_, ?_, him⟩
    · rw [hre]; nlinarith
    · rw [hre]; nlinarith
  have hZbnds : (P t₀).im < Z.im ∧ Z.im ≤ Hh := by
    have h1 := (hγR 1).1.2
    rw [γ.target] at h1
    have h2 := hHh_leR 1
    rw [γ.target] at h2
    exact ⟨h1, h2⟩
  have hp2 : ∀ w ∈ Set.range γ, w.re ∈ Set.Icc a0 X ∧ w.im ∈ Set.Icc ((P t₀).im) Hh := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    have h1 := hγR u
    exact ⟨⟨by linarith [hrminγR u, ha0_le_γ], le_of_lt h1.1.1⟩,
      ⟨le_of_lt h1.1.2, hHh_leR u⟩⟩
  -- ## the crossing lemma
  have hmain : ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      ((p1.trans γ).trans p3).extend s = P (min ts (max as (as + ((t + 1) / 2) * (ts - as)))) := by
    set ua : ℝ → ℝ := fun t => min ts (max as (as + ((t + 1) / 2) * (ts - as))) with hua
    have hua_cont : Continuous ua := by rw [hua]; fun_prop
    have hua_mem : ∀ t : ℝ, ua t ∈ Set.Icc as ts := by
      intro t
      rw [hua]
      exact ⟨le_min has_le (le_max_left _ _), min_le_left _ _⟩
    have hPcont : ContinuousOn P (Set.Icc as ts) :=
      hPc.mono (fun t ht => le_trans hT (le_trans has_ge ht.1))
    have hv_cont : Continuous (fun t : ℝ => P (ua t)) := by
      have h1 := hPcont.comp_continuous hua_cont hua_mem
      simpa [Function.comp_def] using h1
    let v : C(ℝ, ℂ) := ⟨fun t : ℝ => P (ua t), hv_cont⟩
    let h : C(ℝ, ℂ) := ((p1.trans γ).trans p3).extend
    have hua_neg : ua (-1) = as := by
      rw [hua]
      show min ts (max as (as + ((-1 : ℝ) + 1) / 2 * (ts - as))) = as
      have h1 : as + ((-1 : ℝ) + 1) / 2 * (ts - as) = as := by ring
      rw [h1, max_self, min_eq_right has_le]
    have hua_one : ua 1 = ts := by
      rw [hua]
      show min ts (max as (as + ((1 : ℝ) + 1) / 2 * (ts - as))) = ts
      have h1 : as + ((1 : ℝ) + 1) / 2 * (ts - as) = ts := by ring
      rw [h1, max_eq_right has_le, min_self]
    have hv_cond : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (v t).re ∈ Set.Icc a0 X ∧ (v t).im ∈ Set.Icc ((P t₀).im) Hh := by
      intro t ht
      have vf : v t = P (ua t) := rfl
      rw [vf]
      have hmem := hua_mem t
      have hlt : (P (ua t)).re < X₁ := hPt _ (le_trans has_ge hmem.1)
      have hge : rmin ≤ (P (ua t)).re := hrmin _ hmem
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact le_trans ha0_le_r (by linarith)
      · exact (le_of_lt hlt).trans hX₁X.le
      · rcases eq_or_lt_of_le hmem.1 with h | h
        · rw [← h]; exact le_of_eq has_im.symm
        · exact le_of_lt (has_gt _ h hmem.2)
      · rcases eq_or_lt_of_le hmem.2 with h | h
        · rw [h]; exact le_of_eq hts_H
        · exact le_of_lt (hts_first _ (le_trans has_ge hmem.1) h)
    have hrange : Set.range h = Set.range p1 ∪ Set.range γ ∪ Set.range p3 := by
      have e1 : Set.range h = Set.range (((p1.trans γ).trans p3).extend) := rfl
      rw [e1, Path.extend_range, Path.trans_range, Path.trans_range]
    have hh_cond : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (h t).re ∈ Set.Icc a0 X ∧ (h t).im ∈ Set.Icc ((P t₀).im) Hh := by
      intro t ht
      have hmem : h t ∈ Set.range p1 ∪ Set.range γ ∪ Set.range p3 := by
        rw [← hrange]
        exact ⟨t, rfl⟩
      rcases hmem with (h1 | h2) | h3
      · have h1' := hp1 _ h1
        refine ⟨⟨h1'.1.1, h1'.1.2.trans (by linarith [hMX₁, hX₁X])⟩, ?_, ?_⟩
        · linarith [h1'.2]
        · linarith [h1'.2, hHh_ge]
      · exact hp2 _ h2
      · have h3' := hp3 _ h3
        refine ⟨⟨by linarith [h3'.1, hcon, hMX₁, ha0_lt_z], h3'.2.1⟩, ?_, ?_⟩
        · rw [h3'.2.2]; exact le_of_lt hZbnds.1
        · rw [h3'.2.2]; exact hZbnds.2
    have h_left : (h (-1)).re = a0 := by
      have h1 : h (-1) = A := Path.extend_of_le_zero _ (by norm_num)
      rw [h1]
    have h_right : (h 1).re = X := by
      have h1 : h 1 = B := Path.extend_one _
      rw [h1]
    have hv_left : (v (-1)).im = (P t₀).im := by
      have h1 : (v (-1)) = P as := congrArg (fun x : ℝ => P x) hua_neg
      rw [h1, has_im]
    have hv_right : (v 1).im = Hh := by
      have h1 : (v 1) = P ts := congrArg (fun x : ℝ => P x) hua_one
      rw [h1, hts_H]
    obtain ⟨s, hs, t, ht, hst⟩ :=
      Commons.Topology.Jordan.crossing_lemma_rect (a := a0) (b := X) (c := (P t₀).im) (d := Hh)
        h v hh_cond hv_cond h_left h_right hv_left hv_right
    exact ⟨s, hs, t, ht, hst⟩
  obtain ⟨s, hs, t, ht, hst⟩ := hmain
  -- ## the meeting point is a point of the barrier and of the extended path
  have hmem_p : ((p1.trans γ).trans p3).extend s ∈ Set.range p1 ∪ Set.range γ ∪ Set.range p3 := by
    have e1 : ((p1.trans γ).trans p3).extend s ∈ Set.range (((p1.trans γ).trans p3).extend) :=
      ⟨s, rfl⟩
    rw [Path.extend_range] at e1
    rwa [Path.trans_range, Path.trans_range] at e1
  have harg_ge : t₀ ≤ min ts (max as (as + ((t + 1) / 2) * (ts - as))) :=
    le_trans has_ge (le_min has_le (le_max_left _ _))
  have hins : ((p1.trans γ).trans p3).extend s ∈ pathTail P t₀ := by
    rw [hst]
    exact ⟨_, harg_ge, rfl⟩
  rcases hmem_p with (h1 | h2) | h3
  · obtain ⟨u, hu⟩ := h1
    have h1' := hp1 _ ⟨u, rfl⟩
    have himeq : (((p1.trans γ).trans p3).extend s).im = (P t₀).im + 1 := by
      rw [← hu]; exact h1'.2
    have hMle : M ≤ (((p1.trans γ).trans p3).extend s).re := hfib _ hins himeq
    have hleM : (((p1.trans γ).trans p3).extend s).re ≤ M - 1 := by
      rw [← hu]; exact h1'.1.2
    linarith
  · obtain ⟨u, hu⟩ := h2
    exact (hγR u).2 (by rw [hu]; exact hins)
  · obtain ⟨u, hu⟩ := h3
    have h3' := hp3 _ ⟨u, rfl⟩
    have hre : X₁ ≤ (((p1.trans γ).trans p3).extend s).re := by
      rw [← hu]; linarith [h3'.1, hcon]
    rw [pathTail] at hins
    obtain ⟨u', hu', hueq⟩ := hins
    have hlt : (P u').re < X₁ := hPt u' hu'
    rw [hueq] at hlt
    linarith
/-- **The path stays strictly left of the barrier.**

Let `P` be a snail path (`F (P t) = P (t + 1)`, with `F` raising the imaginary part by `c.im / 2`
on the deep left half plane `{re < X₁}`, and `(P t).re < X₁` for `t ≥ t₀`), and let `M` bound the
leftmost real part of the barrier `pathTail P t₀ = P '' [t₀, ∞)` from below on the height band
`[(P t₀).im, (P t₀).im + 2π + 1]` (`hM`).  Then any continuous path `α` on `[0,1]` which starts at
the deep-left base point `⟨M - 1, (P t₀).im + 1⟩` and stays inside
`{re < X ∧ (P t₀).im < im} \ pathTail P t₀` has, at every time `s`, a barrier point of its own
height strictly to its right: `(α s).re < rightCross P t₀ (α s).im`.

The proof has two steps.

* `hsep`: the path stays in the half plane `{re < X₁}` — the planar separation theorem for paths
  (`path_re_lt_of_mem_region_h`, proved in this file by Maehara's crossing lemma).
* For a point `Z` of the region with `Z.re < X₁`: if no barrier point at the height `Z.im` lay to
  the right of `Z`, then the whole horizontal segment from `Z` to `⟨x, Z.im⟩` (with
  `X₁ < x < X`) would stay in the region, and appending it to `α` would produce a path from the
  base point to a point of real part `x > X₁`, contradicting the separation theorem. -/
theorem pathStaysLeftOfBarrier {F : ℂ → ℂ} {X X₁ : ℝ} {c : ℂ} {P : ℝ → ℂ} {T t₀ M : ℝ}
    (hc_im : 0 < c.im) (hX₁X : X₁ < X)
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T + 1 ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₁ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₁)
    (hM : ∀ h ∈ Set.Icc ((P t₀).im) ((P t₀).im + (2 * Real.pi + 1)), M ≤ leftCross P t₀ h)
    {α : ℝ → ℂ} (hα : ContinuousOn α (Set.Icc 0 1))
    (hα0 : α 0 = ⟨M - 1, (P t₀).im + 1⟩)
    (hαG : ∀ s ∈ Set.Icc 0 1,
      α s ∈ ({Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im} \ pathTail P t₀)) :
    ∀ s ∈ Set.Icc 0 1, (α s).re < rightCross P t₀ (α s).im := by
  have hT : T ≤ t₀ := by linarith
  -- ## Step 1: the whole path stays in the half plane `{re < X₁}` (the planar separation theorem)
  have hsep : ∀ u ∈ Set.Icc (0 : ℝ) 1, (α u).re < X₁ := by
    intro u hu
    have hrep : ∀ v : unitInterval, (v : ℝ) * u ∈ Set.Icc (0 : ℝ) 1 := fun v =>
      ⟨mul_nonneg v.2.1 hu.1, by nlinarith [v.2.1, v.2.2, hu.1, hu.2]⟩
    refine path_re_lt_of_mem_region_h (hc_im := hc_im) (hX₁X := hX₁X) (hheight := hheight)
      (hPc := hPc) (htT := htT) (hPinv := hPinv) (hPt := hPt) (hM := hM)
      (Path.mk ⟨fun v : unitInterval => α ((v : ℝ) * u), hα.comp_continuous
        (continuous_subtype_val.mul continuous_const) hrep⟩ (by simpa using hα0) (by simp)) ?_
    intro v
    exact hαG _ (hrep v)
  intro s hs
  have hZs : (α s).re < X₁ := hsep s hs
  have hZG : α s ∈ ({Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im} \ pathTail P t₀) := hαG s hs
  have hYlt : (P t₀).im < (α s).im := hZG.1.2
  have hB : ∀ W ∈ pathTail P t₀, W.re ≤ X₁ := fun W hW => le_of_lt (pathTail_re_lt hPt W hW)
  have hFib : (barrierFibre P t₀ (α s).im).Nonempty :=
    barrierFibre_nonempty hc_im hPc hT hheight hPinv hPt (le_of_lt hYlt)
  rw [lt_rightCross_iff hB hFib]
  -- ## Step 2: a barrier point of the same height lies strictly to the right of `α s`
  by_contra hcon
  have hconW : ∀ W : ℂ, W ∈ pathTail P t₀ → W.im = (α s).im → W.re ≤ (α s).re := by
    intro W hW him
    by_contra hlt
    exact hcon ⟨W, hW, him, lt_of_not_ge hlt⟩
  -- a real number strictly between `max X₁ (α s).re` and `X`
  obtain ⟨x, hX₁x, hxX⟩ : ∃ x : ℝ, X₁ < x ∧ x < X := ⟨(X₁ + X) / 2, by linarith, by linarith⟩
  have hZx : (α s).re < x := lt_of_lt_of_le hZs (le_of_lt hX₁x)
  -- ## the path `α` up to time `s`, followed by the horizontal segment to `⟨x, (α s).im⟩`
  have hrep : ∀ v : unitInterval, (v : ℝ) * s ∈ Set.Icc (0 : ℝ) 1 := fun v =>
    ⟨mul_nonneg v.2.1 hs.1, by nlinarith [v.2.1, v.2.2, hs.1, hs.2]⟩
  let hp1 : Path (⟨M - 1, (P t₀).im + 1⟩ : ℂ) (α s) :=
    Path.mk ⟨fun v : unitInterval => α ((v : ℝ) * s), hα.comp_continuous
        (continuous_subtype_val.mul continuous_const) hrep⟩ (by simpa using hα0) (by simp)
  have hp1f : ∀ v : unitInterval, hp1 v = α ((v : ℝ) * s) := fun v => rfl
  let hp2 : Path (α s) (⟨x, (α s).im⟩ : ℂ) := Path.segment _ _
  have hp2f : ∀ v : unitInterval, hp2 v = Path.segment (α s) (⟨x, (α s).im⟩ : ℂ) v :=
    fun v => rfl
  let hp : Path (⟨M - 1, (P t₀).im + 1⟩ : ℂ) (⟨x, (α s).im⟩ : ℂ) := hp1.trans hp2
  have hxp : (⟨x, (α s).im⟩ : ℂ).re < X₁ := by
    refine path_re_lt_of_mem_region_h (hc_im := hc_im) (hX₁X := hX₁X) (hheight := hheight)
      (hPc := hPc) (htT := htT) (hPinv := hPinv) (hPt := hPt) (hM := hM) hp ?_
    intro v
    have hv : hp v ∈ Set.range ⇑hp1 ∪ Set.range ⇑hp2 := by
      rw [← Path.trans_range hp1 hp2]
      exact ⟨v, rfl⟩
    rcases hv with hv | hv
    · obtain ⟨u, hu⟩ := hv
      rw [← hu, hp1f u]
      exact hαG _ (hrep u)
    · obtain ⟨u, hu⟩ := hv
      have hre : (hp2 u).re = (α s).re + (u : ℝ) * (x - (α s).re) := by
        rw [hp2f u, Path.segment_apply, AffineMap.lineMap_apply]
        simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
        ring
      have him : (hp2 u).im = (α s).im := by
        rw [hp2f u, Path.segment_apply, AffineMap.lineMap_apply]
        simp [Complex.add_im, Complex.mul_im, Complex.sub_im]
      have hmemG : hp2 u ∈ ({Z : ℂ | Z.re < X ∧ (P t₀).im < Z.im} \ pathTail P t₀) := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hre]; nlinarith [u.2.1, u.2.2, hZx, hxX]
        · rw [him]; exact hYlt
        · intro hmem'
          have hle := hconW _ hmem' him
          have hge : (α s).re ≤ (hp2 u).re := by rw [hre]; nlinarith [u.2.1, hZx]
          have heq : (hp2 u).re = (α s).re := le_antisymm hle hge
          have hu0 : (u : ℝ) = 0 := by
            have h1 : (u : ℝ) * (x - (α s).re) = 0 := by rw [hre] at heq; linarith
            rcases mul_eq_zero.mp h1 with h2 | h2
            · exact h2
            · exact absurd h2 (by linarith [hZx])
          have hsame : hp2 u = (α s) := by
            apply Complex.ext
            · rw [hre, hu0]; ring
            · rw [him]
          rw [hsame] at hmem'
          exact hZG.2 hmem'
      simpa only [hu] using hmemG
  have hxp' : x < X₁ := hxp
  linarith

end Work.LandLeaves.Snail
