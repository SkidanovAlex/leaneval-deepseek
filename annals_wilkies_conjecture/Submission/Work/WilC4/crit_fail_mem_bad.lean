/-
  WilC4/crit_fail_mem_bad : failure of continuity at a point of an interval on which the fibre is
  everywhere defined forces the point into `Bad`.

  Setting: `Y ⊆ ℝ^{k+2}` is `∅`-definable in `LRc` and functional (at most one value at each
  `(c,x)`); `hD` says the fibre at `c` is defined on all of `(a,b)`; `hfail` is the negation of
  the ε-δ continuity of the fibre map at the interior point `x ∈ (a,b)`.

  Conclusion: `Fin.cons x c ∈ Bad Y` (one of the four one-sided uniform jump conditions of
  `CritDefs`).

  The mathematical content is the o-minimal monotonicity theorem for the *fibre* `Cfib Y c`:
  since `LRc` names every real as a constant, `Cfib Y c` is again `∅`-definable
  (`cfib_definable`), so `monoOn_main`/`monoBnd_finite` give a one-sided monotonicity modulus
  around `x` (`crit_mono_onesided_aux`).  A monotone function that is not continuous at `x` has a
  one-sided limit different from `f x`, which is exactly a one-sided uniform jump
  (`crit_jump_right`/`crit_jump_left`), and the failure of ε-δ continuity produces such an
  accumulation on one side (`crit_fail_accum_aux`).
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.UnifDefs
import Submission.Work.WilC4.CritFibreDefinable
import Submission.Work.WilC4.mono_real

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The one-sided jump lemmas (pure order theory) -/

/-- If a function monotone on `(x, x + δ₀)` has values at distance `≥ ε₀` from `f x` arbitrarily
close to the right of `x`, then all its values on a right neighbourhood of `x` are uniformly
above, or uniformly below, `f x`. -/
theorem crit_jump_right {f : ℝ → ℝ} {y₀ ε₀ x δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hmono : (∀ s t : ℝ, x < s → s < t → t < x + δ₀ → f s ≤ f t) ∨
             (∀ s t : ℝ, x < s → s < t → t < x + δ₀ → f t ≤ f s))
    (hRF : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x < t ∧ t < x + δ ∧ (y₀ + ε₀ ≤ f t ∨ f t ≤ y₀ - ε₀)) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x < t → t < x + δ → y₀ + ε₀ ≤ f t) ∨
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x < t → t < x + δ → f t ≤ y₀ - ε₀) := by
  rcases hmono with hinc | hdec
  · by_cases hD : ∃ t : ℝ, x < t ∧ t < x + δ₀ ∧ f t ≤ y₀ - ε₀
    · obtain ⟨t, hxt, htδ, htD⟩ := hD
      refine Or.inr ⟨t - x, by linarith, fun s hxs hst => ?_⟩
      have hst' : s < t := by linarith
      exact le_trans (hinc s t hxs hst' htδ) htD
    · refine Or.inl ⟨δ₀, hδ₀, fun t hxt htδ => ?_⟩
      obtain ⟨t', hxt', ht't, ht'U⟩ := hRF (t - x) (by linarith)
      have ht't' : t' < t := by linarith
      rcases ht'U with h | h
      · exact le_trans h (hinc t' t hxt' ht't' htδ)
      · exact absurd ⟨t', hxt', lt_trans ht't' htδ, h⟩ hD
  · by_cases hU : ∃ t : ℝ, x < t ∧ t < x + δ₀ ∧ y₀ + ε₀ ≤ f t
    · obtain ⟨t, hxt, htδ, htU⟩ := hU
      refine Or.inl ⟨t - x, by linarith, fun s hxs hst => ?_⟩
      have hst' : s < t := by linarith
      exact le_trans htU (hdec s t hxs hst' htδ)
    · refine Or.inr ⟨δ₀, hδ₀, fun t hxt htδ => ?_⟩
      obtain ⟨t', hxt', ht't, ht'U⟩ := hRF (t - x) (by linarith)
      have ht't' : t' < t := by linarith
      rcases ht'U with h | h
      · exact absurd ⟨t', hxt', lt_trans ht't' htδ, h⟩ hU
      · exact le_trans (hdec t' t hxt' ht't' htδ) h

/-- Mirror of `crit_jump_right` on the left. -/
theorem crit_jump_left {f : ℝ → ℝ} {y₀ ε₀ x δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hmono : (∀ s t : ℝ, x - δ₀ < s → s < t → t < x → f s ≤ f t) ∨
             (∀ s t : ℝ, x - δ₀ < s → s < t → t < x → f t ≤ f s))
    (hLF : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x - δ < t ∧ t < x ∧ (y₀ + ε₀ ≤ f t ∨ f t ≤ y₀ - ε₀)) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x - δ < t → t < x → y₀ + ε₀ ≤ f t) ∨
    (∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, x - δ < t → t < x → f t ≤ y₀ - ε₀) := by
  rcases hmono with hinc | hdec
  · by_cases hU : ∃ t : ℝ, x - δ₀ < t ∧ t < x ∧ y₀ + ε₀ ≤ f t
    · obtain ⟨t, htδ, htx, htU⟩ := hU
      refine Or.inl ⟨x - t, by linarith, fun s hxs hsx => ?_⟩
      have hts : t < s := by linarith
      exact le_trans htU (hinc t s htδ hts hsx)
    · refine Or.inr ⟨δ₀, hδ₀, fun s hsδ hsx => ?_⟩
      obtain ⟨t, hst, htx, htUD⟩ := hLF (x - s) (by linarith)
      have hst' : s < t := by linarith
      have hsδ' : x - δ₀ < t := by linarith
      rcases htUD with h | h
      · exact absurd ⟨t, hsδ', htx, h⟩ hU
      · exact le_trans (hinc s t hsδ hst' htx) h
  · by_cases hD : ∃ t : ℝ, x - δ₀ < t ∧ t < x ∧ f t ≤ y₀ - ε₀
    · obtain ⟨t, htδ, htx, htD⟩ := hD
      refine Or.inr ⟨x - t, by linarith, fun s hxs hsx => ?_⟩
      have hts : t < s := by linarith
      exact le_trans (hdec t s htδ hts hsx) htD
    · refine Or.inl ⟨δ₀, hδ₀, fun s hsδ hsx => ?_⟩
      obtain ⟨t, hst, htx, htUD⟩ := hLF (x - s) (by linarith)
      have hst' : s < t := by linarith
      have hsδ' : x - δ₀ < t := by linarith
      rcases htUD with h | h
      · exact le_trans h (hdec s t hsδ hst' htx)
      · exact absurd ⟨t, hsδ', htx, h⟩ hD

/-! ## 2. One-sided monotonicity of the fibre -/

/-- **One-sided monotonicity of the fibre.**  For a `∅`-definable functional family `Y` and a real
parameter tuple `c`, there is `δ₀ > 0` such that the fibre `Cfib Y c` is monotone (one of the two
directions, independently on each side) on `(x, x + δ₀)` and on `(x - δ₀, x)`.

This is the o-minimal monotonicity theorem applied to the fibre: `Cfib Y c` is `∅`-definable
(`cfib_definable`) and its exceptional set `MonoBnd (Cfib Y c)` is finite (`monoBnd_finite`), so
each of the two punctured one-sided neighbourhoods of `x` can be chosen to avoid it. -/
theorem crit_mono_onesided_aux {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    {c : Fin k → ℝ} {x : ℝ} :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ((∀ s t y₁ y₂ : ℝ, x < s → s < t → t < x + δ₀ → CGr Y c s y₁ → CGr Y c t y₂ → y₁ ≤ y₂) ∨
       (∀ s t y₁ y₂ : ℝ, x < s → s < t → t < x + δ₀ → CGr Y c s y₁ → CGr Y c t y₂ → y₂ ≤ y₁)) ∧
      ((∀ s t y₁ y₂ : ℝ, x - δ₀ < s → s < t → t < x → CGr Y c s y₁ → CGr Y c t y₂ → y₁ ≤ y₂) ∨
       (∀ s t y₁ y₂ : ℝ, x - δ₀ < s → s < t → t < x → CGr Y c s y₁ → CGr Y c t y₂ → y₂ ≤ y₁)) := by
  classical
  have hYc : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Cfib Y c) := cfib_definable hY c
  have hfun' : ∀ a y y' : ℝ, ![a, y] ∈ Cfib Y c → ![a, y'] ∈ Cfib Y c → y = y' := by
    intro a y y' hy hy'
    exact hfun c a y y' ((mem_cfib_cons).mp hy) ((mem_cfib_cons).mp hy')
  obtain ⟨hDomD, hLAD, hHAD⟩ := monoDefinable_basic hYc
  have hWD := monoDefinable_W hYc
  obtain ⟨hLmD, hHmD, hLpD, hHpD⟩ := monoDefinable_germs hYc
  have hfin : (MonoBnd (Cfib Y c)).Finite := monoBnd_finite hOM hDomD hWD hLmD hHmD hLpD hHpD
  have hfin' : (MonoBnd (Cfib Y c) \ {x}).Finite := hfin.subset Set.sdiff_subset
  have hxnot : x ∉ MonoBnd (Cfib Y c) \ {x} := by simp
  obtain ⟨δb, hδb, hδbsub⟩ :=
    Metric.mem_nhds_iff.mp (hfin'.isClosed.isOpen_compl.mem_nhds hxnot)
  have hnotB : ∀ t : ℝ, |t - x| < δb → t ≠ x → t ∉ MonoBnd (Cfib Y c) := by
    intro t ht hne hmem
    have hb : t ∈ Metric.ball x δb := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
    exact hδbsub hb ⟨hmem, hne⟩
  refine ⟨δb, hδb, ?_, ?_⟩
  · have havb : ∀ z ∈ Set.Ioo x (x + δb), z ∉ MonoBnd (Cfib Y c) := by
      intro z hz
      refine hnotB z ?_ (by linarith [hz.1])
      rw [abs_lt]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rcases monoOn_main (Y := Cfib Y c) hYc hfun' hOM (by linarith : x < x + δb) havb with h | h
    · left
      intro s t y₁ y₂ hxs hst htδ hy₁ hy₂
      exact (mem_MonoIncOn (Y := Cfib Y c) (a := x) (b := x + δb)).mp h s t y₁ y₂ hxs hst htδ
        ((mem_cfib_cons).mpr hy₁) ((mem_cfib_cons).mpr hy₂)
    · right
      intro s t y₁ y₂ hxs hst htδ hy₁ hy₂
      exact (mem_MonoDecOn (Y := Cfib Y c) (a := x) (b := x + δb)).mp h s t y₁ y₂ hxs hst htδ
        ((mem_cfib_cons).mpr hy₁) ((mem_cfib_cons).mpr hy₂)
  · have havb : ∀ z ∈ Set.Ioo (x - δb) x, z ∉ MonoBnd (Cfib Y c) := by
      intro z hz
      refine hnotB z ?_ (by linarith [hz.2])
      rw [abs_lt]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rcases monoOn_main (Y := Cfib Y c) hYc hfun' hOM (by linarith : x - δb < x) havb with h | h
    · left
      intro s t y₁ y₂ hsδ hst htx hy₁ hy₂
      exact (mem_MonoIncOn (Y := Cfib Y c) (a := x - δb) (b := x)).mp h s t y₁ y₂ hsδ hst htx
        ((mem_cfib_cons).mpr hy₁) ((mem_cfib_cons).mpr hy₂)
    · right
      intro s t y₁ y₂ hsδ hst htx hy₁ hy₂
      exact (mem_MonoDecOn (Y := Cfib Y c) (a := x - δb) (b := x)).mp h s t y₁ y₂ hsδ hst htx
        ((mem_cfib_cons).mpr hy₁) ((mem_cfib_cons).mpr hy₂)

/-! ## 3. From failure of continuity to a one-sided accumulation -/

/-- **Failure of continuity gives one-sided accumulation.**  If the fibre map of `Y` at `c` is
defined on `(a,b)` and is not ε-δ continuous at the interior point `x ∈ (a,b)`, then on one side of
`x` there are points of `(a,b)` with values at distance at least some fixed `ε₀ > 0` from the value
`y₀` at `x`, arbitrarily close to `x`. -/
theorem crit_fail_accum_aux {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    {c : Fin k → ℝ} {a b x : ℝ} (hax : a < x) (hxb : x < b)
    (hD : ∀ z ∈ Set.Ioo a b, z ∈ DomFib Y c)
    (hfail : ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y y' : ℝ,
      |x' - x| < δ → CGr Y c x y → CGr Y c x' y' → |y' - y| < ε))
    {y₀ : ℝ} (hy₀ : CGr Y c x y₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ δ : ℝ, 0 < δ → ∃ t ∈ Set.Ioo a b, x < t ∧ t < x + δ ∧
          ∃ w : ℝ, CGr Y c t w ∧ (y₀ + ε₀ ≤ w ∨ w ≤ y₀ - ε₀)) ∨
       (∀ δ : ℝ, 0 < δ → ∃ t ∈ Set.Ioo a b, x - δ < t ∧ t < x ∧
          ∃ w : ℝ, CGr Y c t w ∧ (y₀ + ε₀ ≤ w ∨ w ≤ y₀ - ε₀))) := by
  classical
  -- Replace `y` by the value `y₀` at `x` in the continuity condition.
  have key : (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y y' : ℝ,
        |x' - x| < δ → CGr Y c x y → CGr Y c x' y' → |y' - y| < ε)
      ↔ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y' : ℝ,
        |x' - x| < δ → CGr Y c x' y' → |y' - y₀| < ε) := by
    constructor
    · intro h ε hε
      obtain ⟨δ, hδ, hh⟩ := h ε hε
      exact ⟨δ, hδ, fun x' hx' y' hx'δ hy' => hh x' hx' y₀ y' hx'δ hy₀ hy'⟩
    · intro h ε hε
      obtain ⟨δ, hδ, hh⟩ := h ε hε
      refine ⟨δ, hδ, fun x' hx' y y' hx'δ hy hy' => ?_⟩
      have hyy : y = y₀ := hfun c x y y₀ hy hy₀
      rw [hyy]
      exact hh x' hx' y' hx'δ hy'
  have hfail' : ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y' : ℝ,
        |x' - x| < δ → CGr Y c x' y' → |y' - y₀| < ε) := fun h => hfail (key.mpr h)
  -- Negate it; by contradiction, so that no normal form of the negation is needed.
  have hraw : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ δ : ℝ, 0 < δ → ∃ x' ∈ Set.Ioo a b, ∃ y' : ℝ,
      |x' - x| < δ ∧ CGr Y c x' y' ∧ ε₁ ≤ |y' - y₀| := by
    by_contra hc
    apply hfail'
    intro ε hε
    by_contra hd
    refine hc ⟨ε, hε, fun δ hδ => ?_⟩
    by_contra hd2
    refine hd ⟨δ, hδ, fun x' hx' y' hx'δ hy' => ?_⟩
    by_contra hlt
    exact hd2 ⟨x', hx', y', hx'δ, hy', not_lt.mp hlt⟩
  obtain ⟨ε₀, hε₀, hraw'⟩ := hraw
  refine ⟨ε₀, hε₀, ?_⟩
  by_cases hR : ∀ δ : ℝ, 0 < δ → ∃ t ∈ Set.Ioo a b, x < t ∧ t < x + δ ∧
      ∃ w : ℝ, CGr Y c t w ∧ (y₀ + ε₀ ≤ w ∨ w ≤ y₀ - ε₀)
  · exact Or.inl hR
  · refine Or.inr ?_
    obtain ⟨δ₁, hδ₁⟩ := not_forall.mp hR
    have hδ₁' : 0 < δ₁ := (not_imp.mp hδ₁).1
    have hQ : ¬ (∃ t ∈ Set.Ioo a b, x < t ∧ t < x + δ₁ ∧
        ∃ w : ℝ, CGr Y c t w ∧ (y₀ + ε₀ ≤ w ∨ w ≤ y₀ - ε₀)) := (not_imp.mp hδ₁).2
    intro δ hδ
    have hδ' : 0 < min δ δ₁ := lt_min hδ hδ₁'
    obtain ⟨x', hx'mem, y', hx'δ, hx'y', hy'dist⟩ := hraw' (min δ δ₁) hδ'
    have hx'δ' : -(min δ δ₁) < x' - x ∧ x' - x < min δ δ₁ := abs_lt.mp hx'δ
    have habs : y₀ + ε₀ ≤ y' ∨ y' ≤ y₀ - ε₀ := by
      by_cases h : y₀ ≤ y'
      · left
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y' - y₀)] at hy'dist
        linarith
      · right
        have h' : y' < y₀ := not_le.mp h
        rw [abs_of_neg (by linarith : y' - y₀ < 0)] at hy'dist
        linarith
    have hxne : x' ≠ x := by
      intro hxx
      have : y' = y₀ := hfun c x y' y₀ (hxx ▸ hx'y') hy₀
      rw [this] at hy'dist
      simp at hy'dist
      linarith
    rcases lt_or_gt_of_ne hxne with hlt | hgt
    · exact ⟨x', hx'mem, by linarith [hx'δ'.1, min_le_left δ δ₁], hlt, y', hx'y', habs⟩
    · exact absurd ⟨x', hx'mem, hgt, by linarith [hx'δ'.2, min_le_right δ δ₁], y', hx'y', habs⟩ hQ

/-! ## 4. The target -/

theorem crit_fail_mem_bad {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), CGr Y c x y → CGr Y c x y' → y = y')
    {c : Fin k → ℝ} {a b x : ℝ} (hax : a < x) (hxb : x < b)
    (hD : ∀ z ∈ Set.Ioo a b, z ∈ DomFib Y c)
    (hfail : ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b, ∀ y y' : ℝ,
      |x' - x| < δ → CGr Y c x y → CGr Y c x' y' → |y' - y| < ε)) :
    Fin.cons x c ∈ Bad Y := by
  classical
  have hxmem : x ∈ Set.Ioo a b := ⟨hax, hxb⟩
  have hD' : ∀ t (ht : t ∈ Set.Ioo a b), ∃ y : ℝ, CGr Y c t y := fun t ht => by
    simpa only [DomFib, Set.mem_setOf_eq] using hD t ht
  obtain ⟨y₀, hy₀⟩ := hD' x hxmem
  let f : ℝ → ℝ := fun t => if ht : t ∈ Set.Ioo a b then Classical.choose (hD' t ht) else 0
  have hfmem : ∀ t (ht : t ∈ Set.Ioo a b), CGr Y c t (f t) := by
    intro t ht
    have h1 : f t = Classical.choose (hD' t ht) := dif_pos ht
    rw [h1]
    exact Classical.choose_spec (hD' t ht)
  have huniq : ∀ t (ht : t ∈ Set.Ioo a b) {w : ℝ}, CGr Y c t w → w = f t := fun t ht w hw =>
    hfun c t w (f t) hw (hfmem t ht)
  -- the fibre is defined on a neighbourhood of `x`
  have hIntDom : IntDom Y c x := by
    refine ⟨min (x - a) (b - x), lt_min (by linarith) (by linarith), fun t ht1 ht2 => ?_⟩
    have htmem : t ∈ Set.Ioo a b :=
      ⟨by linarith [min_le_left (x - a) (b - x)],
       by linarith [min_le_right (x - a) (b - x)]⟩
    exact ⟨f t, hfmem t htmem⟩
  -- the two inputs
  obtain ⟨δ₁, hδ₁, hmonoR, hmonoL⟩ := crit_mono_onesided_aux hOM Y hY hfun (c := c) (x := x)
  obtain ⟨ε₀, hε₀, hacc⟩ := crit_fail_accum_aux Y hfun hax hxb hD hfail hy₀
  -- shrink `δ₁` so that the right and left neighbourhoods lie in `(a,b)`
  set δm : ℝ := min δ₁ (min (x - a) (b - x)) with hδmdef
  have hδmpos : 0 < δm := by
    rw [hδmdef]; exact lt_min hδ₁ (lt_min (by linarith) (by linarith))
  have hδm1 : δm ≤ δ₁ := by rw [hδmdef]; exact min_le_left _ _
  have hδma : δm ≤ x - a := by
    rw [hδmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδmb : δm ≤ b - x := by
    rw [hδmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hIooR : Set.Ioo x (x + δm) ⊆ Set.Ioo a b := by
    intro t ht
    exact ⟨by linarith [ht.1, hδma], by linarith [ht.2, hδmb]⟩
  have hIooL : Set.Ioo (x - δm) x ⊆ Set.Ioo a b := by
    intro t ht
    exact ⟨by linarith [ht.1, hδma], by linarith [ht.2, hxb]⟩
  have hmonoR' : (∀ s t : ℝ, x < s → s < t → t < x + δm → f s ≤ f t) ∨
      (∀ s t : ℝ, x < s → s < t → t < x + δm → f t ≤ f s) := by
    rcases hmonoR with h | h
    · left
      intro s t hxs hst htδ
      exact h s t (f s) (f t) hxs hst (by linarith [htδ, hδm1])
        (hfmem s (hIooR ⟨hxs, lt_trans hst htδ⟩)) (hfmem t (hIooR ⟨lt_trans hxs hst, htδ⟩))
    · right
      intro s t hxs hst htδ
      exact h s t (f s) (f t) hxs hst (by linarith [htδ, hδm1])
        (hfmem s (hIooR ⟨hxs, lt_trans hst htδ⟩)) (hfmem t (hIooR ⟨lt_trans hxs hst, htδ⟩))
  have hmonoL' : (∀ s t : ℝ, x - δm < s → s < t → t < x → f s ≤ f t) ∨
      (∀ s t : ℝ, x - δm < s → s < t → t < x → f t ≤ f s) := by
    rcases hmonoL with h | h
    · left
      intro s t hsδ hst htx
      exact h s t (f s) (f t) (by linarith [hsδ, hδm1]) hst htx
        (hfmem s (hIooL ⟨hsδ, lt_trans hst htx⟩)) (hfmem t (hIooL ⟨lt_trans hsδ hst, htx⟩))
    · right
      intro s t hsδ hst htx
      exact h s t (f s) (f t) (by linarith [hsδ, hδm1]) hst htx
        (hfmem s (hIooL ⟨hsδ, lt_trans hst htx⟩)) (hfmem t (hIooL ⟨lt_trans hsδ hst, htx⟩))
  rcases hacc with hRA | hLA
  · -- a right accumulation
    have hRF : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x < t ∧ t < x + δ ∧
        (y₀ + ε₀ ≤ f t ∨ f t ≤ y₀ - ε₀) := by
      intro δ hδ
      obtain ⟨t, htmem, hxt, htδ, w, hw, hwbad⟩ := hRA δ hδ
      refine ⟨t, hxt, htδ, ?_⟩
      have hwt : w = f t := huniq t htmem hw
      rcases hwbad with h | h
      · exact Or.inl (by rwa [hwt] at h)
      · exact Or.inr (by rwa [hwt] at h)
    rcases crit_jump_right hδmpos hmonoR' hRF with ⟨δ, hδ, hU⟩ | ⟨δ, hδ, hU⟩
    · show Fin.cons x c ∈ BadRU Y ∪ BadRD Y ∪ BadLU Y ∪ BadLD Y
      refine Or.inl (Or.inl (Or.inl ?_))
      simp only [BadRU, tup_cons, Fin.cons_zero, Set.mem_setOf_eq]
      refine ⟨hIntDom, ε₀, min δ δm, y₀, hε₀, lt_min hδ hδmpos, hy₀, ?_⟩
      intro t hxt htδ' w hw
      have htmem : t ∈ Set.Ioo a b :=
        hIooR ⟨hxt, lt_of_lt_of_le htδ' (by linarith [min_le_right δ δm])⟩
      have hwt : w = f t := huniq t htmem hw
      rw [hwt]
      exact hU t hxt (lt_of_lt_of_le htδ' (by linarith [min_le_left δ δm]))
    · show Fin.cons x c ∈ BadRU Y ∪ BadRD Y ∪ BadLU Y ∪ BadLD Y
      refine Or.inl (Or.inl (Or.inr ?_))
      simp only [BadRD, tup_cons, Fin.cons_zero, Set.mem_setOf_eq]
      refine ⟨hIntDom, ε₀, min δ δm, y₀, hε₀, lt_min hδ hδmpos, hy₀, ?_⟩
      intro t hxt htδ' w hw
      have htmem : t ∈ Set.Ioo a b :=
        hIooR ⟨hxt, lt_of_lt_of_le htδ' (by linarith [min_le_right δ δm])⟩
      have hwt : w = f t := huniq t htmem hw
      rw [hwt]
      linarith [hU t hxt (lt_of_lt_of_le htδ' (by linarith [min_le_left δ δm]))]
  · -- a left accumulation
    have hLF : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, x - δ < t ∧ t < x ∧
        (y₀ + ε₀ ≤ f t ∨ f t ≤ y₀ - ε₀) := by
      intro δ hδ
      obtain ⟨t, htmem, htδ, htx, w, hw, hwbad⟩ := hLA δ hδ
      refine ⟨t, htδ, htx, ?_⟩
      have hwt : w = f t := huniq t htmem hw
      rcases hwbad with h | h
      · exact Or.inl (by rwa [hwt] at h)
      · exact Or.inr (by rwa [hwt] at h)
    rcases crit_jump_left hδmpos hmonoL' hLF with ⟨δ, hδ, hU⟩ | ⟨δ, hδ, hU⟩
    · show Fin.cons x c ∈ BadRU Y ∪ BadRD Y ∪ BadLU Y ∪ BadLD Y
      refine Or.inl (Or.inr ?_)
      simp only [BadLU, tup_cons, Fin.cons_zero, Set.mem_setOf_eq]
      refine ⟨hIntDom, ε₀, min δ δm, y₀, hε₀, lt_min hδ hδmpos, hy₀, ?_⟩
      intro t htδ' htx w hw
      have htmem : t ∈ Set.Ioo a b :=
        hIooL ⟨lt_of_le_of_lt (by linarith [min_le_right δ δm]) htδ', htx⟩
      have hwt : w = f t := huniq t htmem hw
      rw [hwt]
      exact hU t (lt_of_le_of_lt (by linarith [min_le_left δ δm]) htδ') htx
    · show Fin.cons x c ∈ BadRU Y ∪ BadRD Y ∪ BadLU Y ∪ BadLD Y
      have hLD : Fin.cons x c ∈ BadLD Y := by
        simp only [BadLD, tup_cons, Fin.cons_zero, Set.mem_setOf_eq]
        refine ⟨hIntDom, ε₀, min δ δm, y₀, hε₀, lt_min hδ hδmpos, hy₀, ?_⟩
        intro t htδ' htx w hw
        have htmem : t ∈ Set.Ioo a b :=
          hIooL ⟨lt_of_le_of_lt (by linarith [min_le_right δ δm]) htδ', htx⟩
        have hwt : w = f t := huniq t htmem hw
        rw [hwt]
        linarith [hU t (lt_of_le_of_lt (by linarith [min_le_left δ δm]) htδ') htx]
      exact Set.mem_union_right (BadRU Y ∪ BadRD Y ∪ BadLU Y) hLD

end Work.WilC4
