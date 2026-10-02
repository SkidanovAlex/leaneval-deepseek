import Mathlib
import Submission.Work.LandLeaves.Snail.barrierDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The tail of the snail path is closed

For `F`, `P`, `c`, `T`, `X₀`, `t₀` as in `barrierDefs`, the *barrier* `pathTail P t₀ = P '' Ici t₀`
is closed in `ℂ`.

The mechanism: the height along the tail grows at least linearly
(`path_height_growth`: `(P r).im + n * (c.im/2) ≤ (P (r + n)).im`), hence `(P t).im → +∞`.
Since the map `t ↦ (P t).im` is continuous on the compact interval `[t₀, t₀+1]`, we get the
concrete lower bound `(P t).im ≥ A + (t - t₀ - 1) * (c.im/2)` for `t ≥ t₀`.

Consequently a sequence in the image which converges in `ℂ` must have *bounded* parameters:
the real part of the limit is finite, while the heights of far-away points of the tail are
large.  A convergent subsequence of the parameters then gives the limit as `P a` with
`a ≥ t₀`, by continuity of `P` on `Ici T`.
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

/-- **The height along the tail of the path tends to `+∞`.**

This is the analytic content of `pathTail_isClosed`: the tail of the snail path leaves every
horizontal strip, at least linearly in time. -/
theorem tendsto_im_atTop_of_path {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀) :
    Tendsto (fun t : ℝ => (P t).im) atTop atTop := by
  have hk : 0 < c.im / 2 := by linarith
  have hIcc : Set.Icc t₀ (t₀ + 1) ⊆ Set.Ici T := fun x hx => le_trans htT hx.1
  have hcont : ContinuousOn (fun t : ℝ => (P t).im) (Set.Icc t₀ (t₀ + 1)) :=
    Complex.continuous_im.comp_continuousOn (hPc.mono hIcc)
  have hne : (Set.Icc t₀ (t₀ + 1)).Nonempty := ⟨t₀, le_rfl, by linarith⟩
  -- `A` is a lower bound for the height of `P` on the first unit interval `[t₀, t₀+1]`.
  obtain ⟨r₀, _hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  set A : ℝ := (P r₀).im with hA
  have hAbound : ∀ r ∈ Set.Icc t₀ (t₀ + 1), A ≤ (P r).im := fun r hr => hmin hr
  -- The linear lower bound for the height.
  have key : ∀ t : ℝ, t₀ ≤ t → A + (t - t₀ - 1) * (c.im / 2) ≤ (P t).im := by
    intro t ht
    have ht0 : 0 ≤ t - t₀ := by linarith
    set n : ℕ := Nat.floor (t - t₀) with hn
    have hle : (n : ℝ) ≤ t - t₀ := Nat.floor_le ht0
    have hlt : t - t₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - t₀)
    set r : ℝ := t - (n : ℝ) with hr
    have hrIcc : r ∈ Set.Icc t₀ (t₀ + 1) := by
      constructor
      · show t₀ ≤ t - (n : ℝ); linarith
      · show t - (n : ℝ) ≤ t₀ + 1; linarith
    have hrt : r + (n : ℝ) = t := by simp [hr]
    have hgrow := path_height_growth (F := F) (P := P) (c := c) hheight hPinv htT hPt hrIcc.1 n
    rw [hrt] at hgrow
    have hAr : A ≤ (P r).im := hAbound r hrIcc
    have h2 : t - t₀ - 1 ≤ (n : ℝ) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hk)
    linarith
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max t₀ (t₀ + 1 + (b - A) / (c.im / 2)), fun t ht => ?_⟩
  have ht' : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have hbig : t₀ + 1 + (b - A) / (c.im / 2) ≤ t := le_trans (le_max_right _ _) ht
  have h2 : b ≤ A + (t - t₀ - 1) * (c.im / 2) := by
    have h3 : (b - A) / (c.im / 2) ≤ t - t₀ - 1 := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hk)
    rw [div_mul_cancel₀ _ (ne_of_gt hk)] at h4
    linarith
  linarith [key t ht']

theorem pathTail_isClosed {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀) :
    IsClosed (Work.LandLeaves.Snail.pathTail P t₀) := by
  rw [← closure_subset_iff_isClosed]
  intro W hW
  rw [pathTail] at hW ⊢
  -- Write `W` as a limit of a sequence in the image.
  rw [mem_closure_iff_seq_limit] at hW
  obtain ⟨u, hu_mem, hu_tend⟩ := hW
  choose t htge ht_eq using fun n => (Set.mem_image P (Set.Ici t₀) (u n)).mp (hu_mem n)
  -- The heights of the sequence tend to `im W` while far-away parameter values give large
  -- heights; hence the parameters `t n` are bounded.
  have him : Tendsto (fun s : ℝ => (P s).im) atTop atTop :=
    tendsto_im_atTop_of_path hc_im hPc htT hheight hPinv hPt
  have huseq : Tendsto (fun n => (P (t n)).im) atTop (𝓝 W.im) := by
    have h1 : Tendsto (Complex.im ∘ u) atTop (𝓝 (Complex.im W)) :=
      (Complex.continuous_im.tendsto W).comp hu_tend
    have h2 : (fun n => (P (t n)).im) = Complex.im ∘ u := by
      funext n; rw [Function.comp_apply, ht_eq n]
    rw [h2]; exact h1
  have hEv : ∀ᶠ s : ℝ in atTop, |W.im| + 1 ≤ (P s).im :=
    him.eventually (mem_atTop (|W.im| + 1))
  rw [eventually_atTop] at hEv
  obtain ⟨S, hS⟩ := hEv
  have hEv2 : ∀ᶠ n in atTop, t n < S := by
    have hlt : W.im < |W.im| + 1 := by have := le_abs_self W.im; linarith
    filter_upwards [huseq.eventually (eventually_lt_nhds hlt)] with n hn
    by_contra hc
    rw [not_lt] at hc
    exact absurd (hS (t n) hc) (not_le.mpr hn)
  rw [eventually_atTop] at hEv2
  obtain ⟨N, hN⟩ := hEv2
  have hne' : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  set M : ℝ := max S ((Finset.range (N + 1)).sup' hne' t) with hM
  have hbound : ∀ n, t n ≤ M := by
    intro n
    rcases lt_or_ge n (N + 1) with hn | hn
    · have h : t n ≤ (Finset.range (N + 1)).sup' hne' t :=
        Finset.le_sup' t (Finset.mem_range.mpr hn)
      exact le_trans h (le_max_right _ _)
    · exact le_trans (le_of_lt (hN n (by omega))) (le_max_left _ _)
  -- Extract a convergent subsequence of the parameters.
  obtain ⟨a, ha_mem, φ, hφmono, hφtend⟩ :=
    IsCompact.tendsto_subseq (s := Set.Icc t₀ M) (x := t) isCompact_Icc
      (fun n => ⟨htge n, hbound n⟩)
  have haIci : a ∈ Set.Ici T := le_trans htT ha_mem.1
  have hcontAt : ContinuousWithinAt P (Set.Ici T) a := hPc a haIci
  have hPsub : Tendsto (fun n => P ((t ∘ φ) n)) atTop (𝓝 (P a)) := by
    have h1 : Tendsto (t ∘ φ) atTop (𝓝[Set.Ici T] a) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hφtend, Eventually.of_forall fun n => le_trans htT (htge (φ n))⟩
    exact hcontAt.tendsto.comp h1
  have hWsub : Tendsto (fun n => P ((t ∘ φ) n)) atTop (𝓝 W) := by
    have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have h1 : Tendsto (fun n => u (φ n)) atTop (𝓝 W) := hu_tend.comp hφtop
    have h2 : (fun n => P ((t ∘ φ) n)) = fun n => u (φ n) := by
      funext n; rw [Function.comp_apply, ht_eq (φ n)]
    rw [h2]; exact h1
  have hWa : W = P a := tendsto_nhds_unique hWsub hPsub
  exact ⟨a, ha_mem.1, hWa.symm⟩

end Work.LandLeaves.Snail
