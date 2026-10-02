import Mathlib
import Submission.Work.LandLeaves.OrderPreservingCore

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Combinatorial core for `same_period_aux`

Let `T ⊆ ℝ` be a set of angles considered modulo `1`, `σ = sg k : ψ ↦ Int.fract (4^k ψ)` the
`(2k)`-th iterate of the doubling map, which is order preserving (`ccBet`) and injective mod `1`
on `T`.  This file isolates the pure *finite combinatorial* content: if `O ⊆ [0,1)` is a finite
`σ`-invariant set on which `σ` acts as an order-preserving bijection, then *every* order-preserving
bijection of `O` that fixes one point fixes all of `O`; in particular all `σ`-periodic points of
`O` have the same minimal period.

The tool is the cyclic successor `csucc` of a finite subset of `[0,1)`: the next element in the
counterclockwise (= wrap-around linear) order.  It is a single cycle on `O`, and it commutes with
every `ccBet`-preserving bijection.
-/

noncomputable section

open Classical

namespace Work.LandLeaves

/-! ## `ccBet` versus the linear order on `[0,1)` -/

/-- `Int.fract (x - u) = x - u` when `u ≤ x < 1`, `u ≥ 0`. -/
lemma fract_sub_eq_of_mem {u x : ℝ} (hu : 0 ≤ u) (hx : x < 1) (hxu : u ≤ x) :
    Int.fract (x - u) = x - u := by
  rw [Int.fract_eq_self]; exact ⟨by linarith, by linarith⟩

/-- `Int.fract (x - u) = x - u + 1` when `0 ≤ x < u < 1`. -/
lemma fract_sub_eq_add_one {u x : ℝ} (hx : 0 ≤ x) (hu : u < 1) (hxu : x < u) :
    Int.fract (x - u) = x - u + 1 := by
  have h1 : Int.fract (x - u) = Int.fract (x - u + 1) := by
    rw [Int.fract_eq_fract]; exact ⟨-1, by push_cast; ring⟩
  rw [h1, Int.fract_eq_self]; exact ⟨by linarith, by linarith⟩

/-- **Non-wrapping form of `ccBet`.** -/
theorem ccBet_iff_lt {u v x : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1)
    (hx : x ∈ Set.Ico 0 1) (huv : u < v) : ccBet u v x ↔ u < x ∧ x < v := by
  unfold ccBet
  have hvu : Int.fract (v - u) = v - u :=
    fract_sub_eq_of_mem hu.1 hv.2 huv.le
  rw [hvu]
  constructor
  · rintro ⟨h0, hlt⟩
    rcases lt_trichotomy u x with h | h | h
    · rw [fract_sub_eq_of_mem (u:=u) (x:=x) hu.1 hx.2 h.le] at h0 hlt
      exact ⟨h, by linarith⟩
    · rw [h, sub_self] at h0; simp at h0
    · rw [fract_sub_eq_add_one (u:=u) (x:=x) hx.1 hu.2 h] at h0 hlt
      linarith [hlt, hv.2, hx.1]
  · rintro ⟨hux, hxv⟩
    rw [fract_sub_eq_of_mem (u:=u) (x:=x) hu.1 hx.2 hux.le]
    exact ⟨by linarith, by linarith⟩

/-- **Wrapping form of `ccBet`.** -/
theorem ccBet_iff_gt {u v x : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1)
    (hx : x ∈ Set.Ico 0 1) (hvu : v < u) : ccBet u v x ↔ u < x ∨ x < v := by
  unfold ccBet
  have hvu' : Int.fract (v - u) = v - u + 1 :=
    fract_sub_eq_add_one (u:=u) (x:=v) hv.1 hu.2 hvu
  rw [hvu']
  constructor
  · rintro ⟨h0, hlt⟩
    rcases lt_trichotomy u x with h | h | h
    · exact Or.inl h
    · rw [h, sub_self] at h0; simp at h0
    · rw [fract_sub_eq_add_one (u:=u) (x:=x) hx.1 hu.2 h] at hlt
      exact Or.inr (by linarith)
  · rintro (h | h)
    · rw [fract_sub_eq_of_mem (u:=u) (x:=x) hu.1 hx.2 h.le]
      constructor <;> linarith [hx.1, hx.2, hu.1, hu.2, hv.1, hv.2]
    · rw [fract_sub_eq_add_one (u:=u) (x:=x) hx.1 hu.2 (lt_trans h hvu)]
      constructor <;> linarith [hx.1, hx.2, hu.1, hu.2, hv.1, hv.2, h]

/-- `ccBet` is asymmetric: for points of `[0,1)` both `ccBet u v x` and `ccBet v u x` never hold
simultaneously. -/
theorem ccBet_not_and_swap {u v x : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1)
    (hx : x ∈ Set.Ico 0 1) : ¬ (ccBet u v x ∧ ccBet v u x) := by
  rintro ⟨h1, h2⟩
  rcases lt_trichotomy u v with huv | huv | hvu
  · rw [ccBet_iff_lt hu hv hx huv] at h1
    rw [ccBet_iff_gt hv hu hx huv] at h2
    rcases h2 with h2 | h2 <;> linarith [h1.1, h1.2]
  · subst huv; unfold ccBet at h1; rw [sub_self] at h1; simp at h1
    linarith [Int.fract_nonneg (x - u), h1.2]
  · rw [ccBet_iff_gt hu hv hx hvu] at h1
    rw [ccBet_iff_lt hv hu hx hvu] at h2
    rcases h1 with h1 | h1 <;> linarith [h2.1, h2.2]

/-- For three distinct points of `[0,1)`, one of the two cyclic orderings holds. -/
theorem ccBet_or_swap {u v x : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1)
    (hx : x ∈ Set.Ico 0 1) (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x) :
    ccBet u v x ∨ ccBet v u x := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · rcases lt_trichotomy x u with hxu | hxu | hux'
    · right; rw [ccBet_iff_gt hv hu hx hlt]; exact Or.inr hxu
    · exact absurd hxu.symm hux
    · rcases lt_trichotomy x v with hxv | hxv | hvx'
      · left; rw [ccBet_iff_lt hu hv hx hlt]; exact ⟨hux', hxv⟩
      · exact absurd hxv.symm hvx
      · right; rw [ccBet_iff_gt hv hu hx hlt]; exact Or.inl hvx'
  · exact absurd heq huv
  · rcases lt_trichotomy x v with hxv | hxv | hvx'
    · left; rw [ccBet_iff_gt hu hv hx hgt]; exact Or.inr hxv
    · exact absurd hxv.symm hvx
    · rcases lt_trichotomy x u with hxu | hxu | hux'
      · right; rw [ccBet_iff_lt hv hu hx hgt]; exact ⟨hvx', hxu⟩
      · exact absurd hxu.symm hux
      · left; rw [ccBet_iff_gt hu hv hx hgt]; exact Or.inl hux'

/-! ## The cyclic successor of a finite subset of `[0,1)` -/

/-- The counterclockwise successor of `u` in the finite set `s`: the least element of `s` larger
than `u`, and the least element of `s` (wrap-around) if there is none. -/
noncomputable def csucc (s : Finset ℝ) (u : ℝ) : ℝ :=
  if h : (s.filter (fun v => u < v)).Nonempty then (s.filter (fun v => u < v)).min' h
  else if h2 : s.Nonempty then s.min' h2 else u

lemma csucc_mem {s : Finset ℝ} (hne : s.Nonempty) {u : ℝ} (hus : u ∈ s) : csucc s u ∈ s := by
  unfold csucc
  by_cases h : (s.filter (fun v => u < v)).Nonempty
  · rw [dif_pos h]; exact (Finset.mem_filter.mp ((s.filter (fun v => u < v)).min'_mem h)).1
  · rw [dif_neg h]
    by_cases h2 : s.Nonempty
    · rw [dif_pos h2]; exact s.min'_mem h2
    · exfalso; exact absurd hne h2

lemma csucc_gt {s : Finset ℝ} {u : ℝ} (h : (s.filter (fun v => u < v)).Nonempty) :
    u < csucc s u := by
  unfold csucc; rw [dif_pos h]
  exact (Finset.mem_filter.mp ((s.filter (fun v => u < v)).min'_mem h)).2

lemma csucc_le_of_mem {s : Finset ℝ} {u w : ℝ}
    (h : (s.filter (fun v => u < v)).Nonempty) (hws : w ∈ s) (huw : u < w) :
    csucc s u ≤ w := by
  unfold csucc; rw [dif_pos h]
  exact Finset.min'_le _ w (Finset.mem_filter.mpr ⟨hws, huw⟩)

lemma csucc_eq_min_of_not {s : Finset ℝ} (hne : s.Nonempty) {u : ℝ}
    (h : ¬ (s.filter (fun v => u < v)).Nonempty) : csucc s u = s.min' hne := by
  unfold csucc; rw [dif_neg h, dif_pos hne]

/-- The successor of `u` has nothing strictly counterclockwise between it and `u`. -/
lemma csucc_no_between {s : Finset ℝ} (hne : s.Nonempty) (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1)
    {u : ℝ} (hus : u ∈ s) : ∀ x ∈ s, ¬ ccBet u (csucc s u) x := by
  have hu01 := hs01 u hus
  have hv01 : csucc s u ∈ Set.Ico 0 1 := hs01 _ (csucc_mem hne hus)
  intro x hxs
  have hx01 := hs01 x hxs
  by_cases h : (s.filter (fun v => u < v)).Nonempty
  · have hgt : u < csucc s u := csucc_gt h
    rw [ccBet_iff_lt hu01 hv01 hx01 hgt]
    rintro ⟨hux, hxv⟩
    exact absurd (csucc_le_of_mem h hxs hux) (not_le.mpr hxv)
  · have hle : csucc s u ≤ u := by
      rw [csucc_eq_min_of_not hne h]; exact Finset.min'_le _ _ hus
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [ccBet_iff_gt hu01 hv01 hx01 hlt]
      rintro (hux | hxv)
      · exact h ⟨x, Finset.mem_filter.mpr ⟨hxs, hux⟩⟩
      · exact absurd hxv (not_lt.mpr (by
          rw [csucc_eq_min_of_not hne h]; exact Finset.min'_le _ _ hxs))
    · rw [heq]; intro hc; unfold ccBet at hc; rw [sub_self] at hc; simp at hc
      linarith [Int.fract_nonneg (x - u), hc.2]

/-- Uniqueness of the successor, among elements distinct from `u`. -/
lemma csucc_unique {s : Finset ℝ} (hne : s.Nonempty) (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1)
    {u : ℝ} (hus : u ∈ s) {w : ℝ} (hws : w ∈ s) (hwu : w ≠ u)
    (h : ∀ x ∈ s, ¬ ccBet u w x) : w = csucc s u := by
  have hu01 := hs01 u hus
  have hw01 := hs01 w hws
  have hv01 : csucc s u ∈ Set.Ico 0 1 := hs01 _ (csucc_mem hne hus)
  have hvc : csucc s u ∈ s := csucc_mem hne hus
  by_cases hlt : (s.filter (fun v => u < v)).Nonempty
  · have hgt : u < csucc s u := csucc_gt hlt
    rcases lt_trichotomy w u with hwu' | heq | huw
    · exact absurd (by rw [ccBet_iff_gt hu01 hw01 hv01 hwu']; exact Or.inl hgt) (h _ hvc)
    · exact absurd heq hwu
    · have hle : csucc s u ≤ w := csucc_le_of_mem hlt hws huw
      rcases lt_or_eq_of_le hle with hlt2 | heq2
      · exact absurd (by rw [ccBet_iff_lt hu01 hw01 hv01 huw]; exact ⟨hgt, hlt2⟩) (h _ hvc)
      · exact heq2.symm
  · have hwu' : w < u := by
      rcases lt_trichotomy w u with h' | h' | h'
      · exact h'
      · exact absurd h' hwu
      · exact absurd h' (fun huw => hlt ⟨w, Finset.mem_filter.mpr ⟨hws, huw⟩⟩)
    have hle2 : csucc s u ≤ w := by
      rw [csucc_eq_min_of_not hne hlt]; exact Finset.min'_le _ _ hws
    rcases lt_or_eq_of_le hle2 with hlt2 | heq2
    · exact absurd (by rw [ccBet_iff_gt hu01 hw01 hv01 hwu']; exact Or.inr hlt2) (h _ hvc)
    · exact heq2.symm

/-! ## `csucc` reaches every point (it is a single cycle) -/

/-- From `u` the successor iteration reaches every point of `s` that lies above `u`. -/
lemma csucc_reach_of_lt {s : Finset ℝ} (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1)
    {u v : ℝ} (hus : u ∈ s) (hvs : v ∈ s) (huv : u < v) :
    ∃ k : ℕ, (csucc s)^[k] u = v := by
  suffices key : ∀ N : ℕ, ∀ u v : ℝ, u ∈ s → v ∈ s → u < v →
      (s.filter (fun w => u < w ∧ w < v)).card = N →
      ∃ k : ℕ, (csucc s)^[k] u = v by
    exact key _ u v hus hvs huv rfl
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro u v hus hvs huv hcard
    have hne : s.Nonempty := ⟨u, hus⟩
    have hlt : (s.filter (fun w => u < w)).Nonempty :=
      ⟨v, Finset.mem_filter.mpr ⟨hvs, huv⟩⟩
    have hc : csucc s u ∈ s := csucc_mem hne hus
    have hug : u < csucc s u := csucc_gt hlt
    have hcv : csucc s u ≤ v := csucc_le_of_mem hlt hvs huv
    rcases lt_or_eq_of_le hcv with hltv | heqv
    · have hsub : s.filter (fun w => csucc s u < w ∧ w < v) ⊆
          s.filter (fun w => u < w ∧ w < v) := by
        intro w hw
        simp only [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, lt_trans hug hw.2.1, hw.2.2⟩
      have hstrict : s.filter (fun w => csucc s u < w ∧ w < v) ⊂
          s.filter (fun w => u < w ∧ w < v) :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨csucc s u, by
            simp only [Finset.mem_filter]; exact ⟨hc, hug, hltv⟩, by
            rw [Finset.mem_filter]; rintro ⟨-, h, -⟩; exact lt_irrefl _ h⟩
      have hcardlt : (s.filter (fun w => csucc s u < w ∧ w < v)).card < N := by
        rw [← hcard]; exact Finset.card_lt_card hstrict
      obtain ⟨k, hk⟩ := ih _ hcardlt (csucc s u) v hc hvs hltv rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk]⟩
    · exact ⟨1, by rw [Function.iterate_one, heqv]⟩

/-- The successor of the maximal element is the minimal element (wrap-around). -/
lemma csucc_max_eq_min {s : Finset ℝ} (hne : s.Nonempty) :
    csucc s (s.max' hne) = s.min' hne := by
  have hemp : ¬ (s.filter (fun w => s.max' hne < w)).Nonempty := by
    rw [Finset.filter_nonempty_iff]; rintro ⟨w, hw, hlt⟩
    exact absurd hlt (not_lt.mpr (s.le_max' w hw))
  rw [csucc_eq_min_of_not hne hemp]

/-- `csucc` is a single cycle on `s`: its iterates reach every point from every point. -/
lemma csucc_orbit {s : Finset ℝ} (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1)
    {u v : ℝ} (hus : u ∈ s) (hvs : v ∈ s) :
    ∃ k : ℕ, (csucc s)^[k] u = v := by
  have hne : s.Nonempty := ⟨u, hus⟩
  have hreachM : ∃ k, (csucc s)^[k] u = s.max' hne := by
    rcases lt_or_eq_of_le (s.le_max' u hus) with hlt | heq
    · exact csucc_reach_of_lt hs01 hus (s.max'_mem hne) hlt
    · exact ⟨0, by rw [Function.iterate_zero]; exact heq⟩
  obtain ⟨kM, hkM⟩ := hreachM
  have hmaxmin : csucc s (s.max' hne) = s.min' hne := csucc_max_eq_min hne
  have hreachv : ∃ k, (csucc s)^[k] (s.min' hne) = v := by
    rcases lt_or_eq_of_le (s.min'_le v hvs) with hlt | heq
    · exact csucc_reach_of_lt hs01 (s.min'_mem hne) hvs hlt
    · exact ⟨0, by rw [Function.iterate_zero]; exact heq⟩
  obtain ⟨kv, hkv⟩ := hreachv
  exact ⟨kv + 1 + kM, by
    rw [Function.iterate_add_apply, hkM, Function.iterate_succ_apply, hmaxmin, hkv]⟩

/-! ## `csucc` commutes with every order-preserving bijection, and fixed points are global -/

/-- If `s` has at least two points then the successor of `u` is different from `u`. -/
lemma csucc_ne_self {s : Finset ℝ} (h2 : 2 ≤ s.card) {u : ℝ} (hus : u ∈ s) :
    csucc s u ≠ u := by
  have hne : s.Nonempty := ⟨u, hus⟩
  by_cases h : (s.filter (fun v => u < v)).Nonempty
  · exact ne_of_gt (csucc_gt h)
  · have hmin : csucc s u = s.min' hne := csucc_eq_min_of_not hne h
    intro heq
    have hsub : s ⊆ {u} := by
      intro w hw
      rw [Finset.mem_singleton]
      rcases lt_trichotomy w u with h' | h' | h'
      · have hle : s.min' hne ≤ w := Finset.min'_le _ _ hw
        rw [← hmin, heq] at hle
        exact absurd hle (not_le.mpr h')
      · exact h'
      · exact absurd h' (fun huw => h ⟨w, Finset.mem_filter.mpr ⟨hw, huw⟩⟩)
    have hcard : s.card ≤ 1 := by
      calc s.card ≤ ({u} : Finset ℝ).card := Finset.card_le_card hsub
        _ = 1 := by simp
    omega

/-- **`csucc` commutes with an order-preserving bijection** `h` of `s`. -/
lemma csucc_commute {s : Finset ℝ} (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1) (h2 : 2 ≤ s.card)
    {h : ℝ → ℝ} (hmem : ∀ x ∈ s, h x ∈ s)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, h x = h y → x = y)
    (hord : ∀ a ∈ s, ∀ b ∈ s, ∀ x ∈ s, ccBet a b x → ccBet (h a) (h b) (h x))
    {u : ℝ} (hus : u ∈ s) : h (csucc s u) = csucc s (h u) := by
  have hne : s.Nonempty := ⟨u, hus⟩
  have hcu : csucc s u ∈ s := csucc_mem hne hus
  have hhu : h u ∈ s := hmem u hus
  have hhcu : h (csucc s u) ∈ s := hmem _ hcu
  -- `h` restricted to the finite set `s` is a bijection
  have hsurj : ∀ y ∈ s, ∃ y' ∈ s, h y' = y := by
    let g : s → s := fun z => ⟨h z, hmem z z.2⟩
    have hginj : Function.Injective g := by
      intro z₁ z₂ hz
      exact Subtype.ext (hinj z₁ z₁.2 z₂ z₂.2 (by simpa [g] using congrArg Subtype.val hz))
    have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hginj
    intro y hy
    obtain ⟨z, hz⟩ := hgsurj ⟨y, hy⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  have hnu : csucc s u ≠ u := csucc_ne_self h2 hus
  -- nothing is strictly counterclockwise between `h u` and `h (csucc s u)`
  have hkey : ∀ x ∈ s, ¬ ccBet (h u) (h (csucc s u)) x := by
    intro x hxs hbet
    obtain ⟨y, hys, hyx⟩ := hsurj x hxs
    have hx_ne_hu : x ≠ h u := by
      intro heq; rw [heq] at hbet; unfold ccBet at hbet; rw [sub_self] at hbet
      simp at hbet
    have hx_ne_hv : x ≠ h (csucc s u) := by
      intro heq; rw [heq] at hbet; exact absurd hbet.2 (lt_irrefl _)
    have hy_u : y ≠ u := by intro hyu; exact hx_ne_hu (by rw [← hyx, hyu])
    have hy_v : y ≠ csucc s u := by
      intro hyv; exact hx_ne_hv (by rw [← hyx, hyv])
    have hnot : ¬ ccBet u (csucc s u) y := csucc_no_between hne hs01 hus y hys
    rcases ccBet_or_swap (hs01 u hus) (hs01 (csucc s u) hcu) (hs01 y hys)
        (Ne.symm hnu) (Ne.symm hy_u) (Ne.symm hy_v) with h' | h'
    · exact hnot h'
    · have hh := hord (csucc s u) hcu u hus y hys h'
      rw [hyx] at hh
      exact ccBet_not_and_swap (hs01 (h u) hhu) (hs01 (h (csucc s u)) hhcu) (hs01 x hxs)
        ⟨hbet, hh⟩
  have hw_ne : h (csucc s u) ≠ h u := by
    intro heq; exact hnu (hinj _ hcu u hus heq)
  exact csucc_unique hne hs01 hhu hhcu hw_ne hkey

/-- **An order-preserving bijection of `s` that fixes one point fixes all of `s`.** -/
lemma fixed_point_id {s : Finset ℝ} (hs01 : ∀ x ∈ s, x ∈ Set.Ico 0 1)
    {h : ℝ → ℝ} (hmem : ∀ x ∈ s, h x ∈ s)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, h x = h y → x = y)
    (hord : ∀ a ∈ s, ∀ b ∈ s, ∀ x ∈ s, ccBet a b x → ccBet (h a) (h b) (h x))
    {a : ℝ} (has : a ∈ s) (hfix : h a = a) : ∀ x ∈ s, h x = x := by
  intro x hxs
  by_cases h2 : 2 ≤ s.card
  · have hne : s.Nonempty := ⟨a, has⟩
    have hmema : ∀ k : ℕ, (csucc s)^[k] a ∈ s := by
      intro k
      induction k with
      | zero => rw [Function.iterate_zero_apply]; exact has
      | succ k ih => rw [Function.iterate_succ_apply']; exact csucc_mem hne ih
    have hiter : ∀ k : ℕ, h ((csucc s)^[k] a) = (csucc s)^[k] a := by
      intro k
      induction k with
      | zero => rw [Function.iterate_zero_apply]; exact hfix
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        rw [csucc_commute hs01 h2 hmem hinj hord (hmema k), ih]
    obtain ⟨k, hk⟩ := csucc_orbit hs01 has hxs
    rw [← hk]
    exact hiter k
  · have hcard1 : s.card ≤ 1 := by omega
    have hxa : x = a := (Finset.card_le_one.mp hcard1) x hxs a has
    rw [hxa, hfix]

end Work.LandLeaves
