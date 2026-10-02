/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower.PsiData
import Submission.Work.FatouCoord.Repelling.near_translation_mod
import Submission.Work.FatouCoord.Estimate.wMap_re_growth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The extended conjugacy `rV` escapes to infinity along large imaginary parts

Let `V` be a chart conjugacy on a left half plane (`V (w+1) = wMap f (V w)`, `V w ≈ w`),
extended to `rV f V R` on all of `ℂ` by the standard representative trick (`PsiData.lean`).
We show that for `w` with `|Im w|` large enough, the norm of `rV f V R (w + n)` tends to
infinity: `‖rV f V R (w + n)‖ → ∞`.

The proof has three ingredients.

* **Escape past a right half plane** (`orbit_tendsto_atTop_of_re_ge`): if `Re x` is large
  enough then `Re ((wMap f)^[k] x)` keeps growing by `1/2` per step (`Estimate.wMap_re_growth`),
  hence `‖(wMap f)^[k] x‖ → ∞`.
* **Getting to such a half plane** (`im_large_iterate_re_ge`): if `|Im x|` is large and `x` is
  not too far to the left of the imaginary axis, then some iterate of `x` has large real part.
  On the way, `Re` grows by `1/2` per step while `|Im|` decreases by at most `K / ‖x‖ ≤ K / L`
  per step, so over the `≈ 2|Re x|` steps needed the imaginary part remains comparable to
  `|Im x|`, keeping the near-translation estimate (`Repelling.near_translation_mod`) applicable.
* **Tracking back to `rV`**: the hypothesis `‖V u - u‖ ≤ ‖u‖ / 2` on the *whole* left half
  plane, together with `V (u+1) = wMap f (V u)`, says that the orbit of `V u` tracks the
  translation `u + k` within a factor `2` as long as `Re (u+k) < -R`.  So any point `w` of the
  left half plane can be followed forward until it reaches the fundamental strip
  `-R-1 ≤ Re < -R`; there the tracking bound turns into the concrete bounds
  `Re (V u) ≥ -|Im (V u)| - 2(R+2)`, `|Im (V u)| ≥ (|Im u| - (R+2))/2` that the second
  ingredient needs.  For `Re w ≥ -R` one instead goes backwards to the strip using the
  representative appearing in the definition of `rV`.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

set_option linter.unusedVariables false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## Escaping orbits of `wMap f` -/

/-- If `Re x` is past a large level `L`, the whole forward orbit of `x` under `wMap f` has
norms tending to infinity: the real part grows by `1/2` at every step and the norm dominates
the real part. -/
theorem orbit_tendsto_atTop_of_re_ge (hb : ParabolicBounds f h a r A A') :
    ∃ L : ℝ, 0 < L ∧ 4 ≤ L ∧ 1 / r < L ∧
      ∀ x : ℂ, L ≤ x.re → Filter.Tendsto (fun n : ℕ => ‖(wMap f)^[n] x‖) Filter.atTop Filter.atTop := by
  obtain ⟨N, hNpos, hNr, hgrowth⟩ := Estimate.wMap_re_growth hb
  have hNle : N ≤ max N 4 := le_max_left _ _
  have h4le : (4:ℝ) ≤ max N 4 := le_max_right _ _
  refine ⟨max N 4 + 1, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  have hxN : N < x.re := by linarith
  rw [Filter.tendsto_atTop]
  intro b
  refine Filter.eventually_atTop.2 ⟨Nat.ceil (2 * (b - (max N 4 + 1))) + 1, ?_⟩
  intro k hk
  have hn : 2 * (b - (max N 4 + 1)) ≤ (k : ℝ) := by
    have h1 : 2 * (b - (max N 4 + 1)) ≤ ((Nat.ceil (2 * (b - (max N 4 + 1))) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((Nat.ceil (2 * (b - (max N 4 + 1))) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk
    push_cast at h2
    linarith
  have hre : (max N 4 + 1) + (k : ℝ) / 2 ≤ ((wMap f)^[k] x).re := by
    have := hgrowth x hxN k
    linarith
  have hnorm : ((wMap f)^[k] x).re ≤ ‖(wMap f)^[k] x‖ := Complex.re_le_norm _
  linarith

/-- **A tail of a sequence escaping to `+∞` escapes itself.** -/
private lemma tendsto_atTop_of_tail {u : ℕ → ℝ} {m : ℕ}
    (h : Filter.Tendsto (fun k : ℕ => u (k + m)) Filter.atTop Filter.atTop) :
    Filter.Tendsto u Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop] at h ⊢
  intro b
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (h b)
  refine Filter.eventually_atTop.2 ⟨K + m, fun n hn => ?_⟩
  have hm : m ≤ n := by omega
  have h1 : K ≤ n - m := by omega
  have h2 : n - m + m = n := Nat.sub_add_cancel hm
  have := hK (n - m) h1
  rwa [h2] at this

/-- **Getting past a large real level from a large imaginary part.**  If `|Im x|` is large and
`Re x` is not too far to the left of the imaginary axis, then some iterate of `x` under `wMap f`
has real part at least `L`. -/
theorem im_large_iterate_re_ge (hb : ParabolicBounds f h a r A A') {L C : ℝ}
    (hL4 : 4 ≤ L) (hLr : 1 / r < L) (hL8 : 8 * (Estimate.Ksub A a + 1) ≤ L) :
    ∃ T : ℝ, 0 < T ∧ ∀ x : ℂ, T < |x.im| → -|x.im| - C ≤ x.re →
      ∃ n : ℕ, L ≤ ((wMap f)^[n] x).re := by
  have hK0 : 0 ≤ Estimate.Ksub A a := Estimate.Ksub_nonneg hb.hA a
  have hKle : Estimate.Ksub A a ≤ Estimate.Ksub A a + 1 := by linarith
  have hLpos : 0 < L := by linarith
  have hKL : (Estimate.Ksub A a + 1) / L ≤ 1 / 8 := by
    rw [div_le_iff₀ hLpos]; linarith
  have h2Lle : 2 * L ≤ max (2 * L) (L + C + 1) := le_max_left _ _
  have hLCle : L + C + 1 ≤ max (2 * L) (L + C + 1) := le_max_right _ _
  refine ⟨max (2 * L) (L + C + 1) + 1, by linarith, ?_⟩
  intro x hz hC
  set z : ℝ := |x.im| with hzdef
  set y : ℝ := x.re with hydef
  have hz2L : 2 * L ≤ z := by rw [hzdef]; linarith
  have hzLC : L + C + 1 < z := by rw [hzdef]; linarith
  have hyz : -z - C ≤ y := by rw [hydef, hzdef]; linarith
  set n : ℕ := Nat.ceil (2 * (L - y)) with hndef
  have hn_ge : 2 * (L - y) ≤ (n : ℝ) := by rw [hndef]; exact Nat.le_ceil _
  have hn_le : (n : ℝ) ≤ 4 * z := by
    by_cases h : 0 ≤ 2 * (L - y)
    · have hc : (n : ℝ) < 2 * (L - y) + 1 := by
        rw [hndef]; exact Nat.ceil_lt_add_one h
      linarith
    · have h0 : n = 0 := by rw [hndef]; exact Nat.ceil_eq_zero.mpr (by linarith)
      rw [h0]; push_cast; linarith
  have hnK : (n : ℝ) * ((Estimate.Ksub A a + 1) / L) ≤ z / 2 := by
    have h1 : (n : ℝ) * ((Estimate.Ksub A a + 1) / L)
        ≤ (4 * z) * ((Estimate.Ksub A a + 1) / L) :=
      mul_le_mul_of_nonneg_right hn_le (by positivity)
    have h2 : (4 * z) * ((Estimate.Ksub A a + 1) / L) ≤ (4 * z) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hKL (by linarith)
    linarith
  have hmain : ∀ k : ℕ, k ≤ n →
      y + (k : ℝ) / 2 ≤ ((wMap f)^[k] x).re ∧
      z - (k : ℝ) * ((Estimate.Ksub A a + 1) / L) ≤ |((wMap f)^[k] x).im| := by
    intro k
    induction k with
    | zero =>
      intro _
      constructor
      · simpa [hydef] using le_refl (x.re)
      · simpa [hzdef] using le_refl (|x.im|)
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨ihre, ihim⟩ := ih hkn
      have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have himk : z / 2 ≤ |((wMap f)^[k] x).im| := by
        have h2 : (k : ℝ) * ((Estimate.Ksub A a + 1) / L) ≤ z / 2 :=
          le_trans (mul_le_mul_of_nonneg_right hkR (by positivity)) hnK
        linarith
      have hnormk : L ≤ ‖(wMap f)^[k] x‖ := by
        have := Complex.abs_im_le_norm ((wMap f)^[k] x)
        linarith
      have hsub := Repelling.near_translation_mod hb (x := (wMap f)^[k] x)
        (lt_of_lt_of_le hLr hnormk) (le_trans hL4 hnormk)
      have hb1 : ‖wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1‖
          ≤ (Estimate.Ksub A a + 1) / L := by
        have h3 : Estimate.Ksub A a / ‖(wMap f)^[k] x‖ ≤ Estimate.Ksub A a / L :=
          div_le_div_of_nonneg_left hK0 hLpos hnormk
        have h4 : Estimate.Ksub A a / L ≤ (Estimate.Ksub A a + 1) / L :=
          div_le_div_of_nonneg_right hKle hLpos.le
        linarith
      have hre_step : ((wMap f)^[k] x).re + 1 / 2 ≤ (wMap f ((wMap f)^[k] x)).re := by
        have h2 : -((Estimate.Ksub A a + 1) / L)
            ≤ (wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1).re := by
          have ha := Complex.abs_re_le_norm (wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1)
          have h3 := (abs_le.mp (le_trans ha hb1)).1
          linarith
        have hsplit : (wMap f ((wMap f)^[k] x)).re
            = ((wMap f)^[k] x).re + 1
              + (wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1).re := by
          simp only [Complex.sub_re, Complex.one_re]; ring
        rw [hsplit]
        linarith [hKL]
      have hdpos : 0 < (Estimate.Ksub A a + 1) / L := div_pos (by linarith) hLpos
      have him_step : |((wMap f)^[k] x).im| - (Estimate.Ksub A a + 1) / L
          ≤ |(wMap f ((wMap f)^[k] x)).im| := by
        have h4 : |(wMap f ((wMap f)^[k] x)).im - ((wMap f)^[k] x).im|
            = |(wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1).im| := by
          congr 1
          simp only [Complex.sub_im, Complex.one_im]
          ring
        have h5 : |(wMap f ((wMap f)^[k] x) - ((wMap f)^[k] x) - 1).im|
            ≤ (Estimate.Ksub A a + 1) / L := le_trans (Complex.abs_im_le_norm _) hb1
        have h6 := abs_sub_abs_le_abs_sub (((wMap f)^[k] x).im) ((wMap f ((wMap f)^[k] x)).im)
        rw [abs_sub_comm (((wMap f)^[k] x).im) ((wMap f ((wMap f)^[k] x)).im)] at h6
        rw [h4] at h6
        linarith
      rw [Function.iterate_succ_apply']
      push_cast
      have hid : ((k : ℝ) + 1) * ((Estimate.Ksub A a + 1) / L)
          = (k : ℝ) * ((Estimate.Ksub A a + 1) / L) + (Estimate.Ksub A a + 1) / L := by ring
      constructor
      · linarith
      · linarith [hid]
  exact ⟨n, by have := (hmain n le_rfl).1; linarith [hn_ge]⟩

/-- Combining the two previous results: an orbit starting at a point with large imaginary part
which is not too far to the left escapes to infinity. -/
private theorem orbit_tendsto_of_bounds {L1 L C TD : ℝ}
    (hL1esc : ∀ x : ℂ, L1 ≤ x.re →
      Filter.Tendsto (fun n : ℕ => ‖(wMap f)^[n] x‖) Filter.atTop Filter.atTop)
    (hL1L : L1 ≤ L)
    (hTD : ∀ x : ℂ, TD < |x.im| → -|x.im| - C ≤ x.re → ∃ n : ℕ, L ≤ ((wMap f)^[n] x).re) :
    ∀ x : ℂ, TD < |x.im| → -|x.im| - C ≤ x.re →
      Filter.Tendsto (fun n : ℕ => ‖(wMap f)^[n] x‖) Filter.atTop Filter.atTop := by
  intro x hIm hC
  obtain ⟨n₀, hn₀⟩ := hTD x hIm hC
  have hstep : Filter.Tendsto (fun k : ℕ => ‖(wMap f)^[k] ((wMap f)^[n₀] x)‖)
      Filter.atTop Filter.atTop := hL1esc _ (le_trans hL1L hn₀)
  have hshift : Filter.Tendsto (fun k : ℕ => ‖(wMap f)^[k + n₀] x‖) Filter.atTop Filter.atTop := by
    simpa only [Function.iterate_add_apply] using hstep
  exact tendsto_atTop_of_tail hshift

/-! ## The shift relation for `rV` and the bounds for `V` on the fundamental strip -/

/-- The extended conjugacy is equivariant for the unit translation: `rV (w+n) = wMap^[n] (rV w)`. -/
theorem rV_add_nat {V : ℂ → ℂ} {R : ℝ}
    (hVshift : ∀ u : ℂ, u.re < -R → V (u+1) = wMap f (V u)) (w : ℂ) (n : ℕ) :
    rV f V R (w + n) = (wMap f)^[n] (rV f V R w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : w + ((n+1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    rw [h1, rV_shift hVshift, ih, Function.iterate_succ_apply']

/-- **Bounds for `V u` on the fundamental strip.**  If `Re u < -R` and `|Re u| ≤ R + 2`, then
`V u` is comparable to `u`: its real part stays above `-|Im (V u)| - 2(R+2)`, and `|Im (V u)|`
is at least `(|Im u| - 2(R+2))/2`. -/
private theorem norm_bounds_V {V : ℂ → ℂ} {R : ℝ}
    (hVbd : ∀ u : ℂ, u.re < -R → ‖V u - u‖ ≤ (1/2) * ‖u‖) (hR2 : 0 ≤ R + 2) {u : ℂ}
    (huR : u.re < -R) (hu : |u.re| ≤ R + 2) :
    |(V u).re| ≤ |(V u).im| + 2 * (R + 2) ∧ |u.im| ≤ 2 * |(V u).im| + 2 * (R + 2) := by
  have hb := hVbd u huR
  have hδ : ‖V u - u‖ ≤ ‖u‖ / 2 := by linarith
  have hnorm : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
  have hre : |(V u).re - u.re| ≤ ‖u‖ / 2 := by
    have := Complex.abs_re_le_norm (V u - u)
    simpa using le_trans this hδ
  have him : |(V u).im - u.im| ≤ ‖u‖ / 2 := by
    have := Complex.abs_im_le_norm (V u - u)
    simpa using le_trans this hδ
  have h1 : |(V u).re| ≤ |u.re| + ‖u‖ / 2 := by
    calc |(V u).re| ≤ |u.re| + |(V u).re - u.re| := by
          have := abs_add_le u.re ((V u).re - u.re)
          rw [show u.re + ((V u).re - u.re) = (V u).re by ring] at this
          exact this
      _ ≤ |u.re| + ‖u‖ / 2 := by linarith
  have h2 : |u.im| ≤ |(V u).im| + ‖u‖ / 2 := by
    have := abs_sub_abs_le_abs_sub u.im (V u).im
    have habs : |u.im - (V u).im| ≤ ‖u‖ / 2 := by
      rw [abs_sub_comm]; exact him
    linarith
  have h3 : |(V u).im| ≥ (|u.im| - |u.re|) / 2 := by linarith [hnorm]
  constructor
  · linarith [h1, h3, hu, hnorm]
  · linarith [h2, hu, hnorm, hR2]

/-! ## The main theorem -/

theorem rV_tendsto_atTop {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    {R : ℝ} (hRpos : 0 < R) (hRr : 1 / r < R) (V : ℂ → ℂ)
    (hVshift : ∀ w : ℂ, w.re < -R → V (w+1) = Work.FatouCoord.wMap f (V w))
    (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1/2) * ‖w‖) :
    ∃ T : ℝ, 0 < T ∧ ∀ w : ℂ, T < |w.im| →
      Filter.Tendsto (fun n : ℕ => ‖Work.FatouCoord.Flower.rV f V R (w + n)‖) Filter.atTop Filter.atTop := by
  obtain ⟨L1, hL1pos, hL14, hL1r, hL1esc⟩ := orbit_tendsto_atTop_of_re_ge (f := f) (h := h) (a := a) (r := r) hb
  set L : ℝ := max L1 (8 * (Estimate.Ksub A a + 1)) with hLdef
  have hL4 : 4 ≤ L := le_trans hL14 (le_max_left _ _)
  have hLr : 1 / r < L := lt_of_lt_of_le hL1r (le_max_left _ _)
  have hL8 : 8 * (Estimate.Ksub A a + 1) ≤ L := le_max_right _ _
  have hL1L : L1 ≤ L := le_max_left _ _
  obtain ⟨TD, hTDpos, hTD⟩ := im_large_iterate_re_ge (f := f) (h := h) (a := a) (r := r) hb hL4 hLr hL8
  have hTpos : (0:ℝ) < 2 * TD + 2 * (R + 2) + 1 := by linarith
  refine ⟨2 * TD + 2 * (R + 2) + 1, hTpos, ?_⟩
  intro w hwIm
  have hgoal : Filter.Tendsto (fun n : ℕ => ‖(wMap f)^[n] (rV f V R w)‖) Filter.atTop Filter.atTop := by
    by_cases hre : -R ≤ w.re
    · -- `w` lies to the right of the fundamental strip: go backwards to it at once
      set m : ℕ := EntireRepelling.rIdx R w with hmdef
      set u : ℂ := w - (m : ℂ) with hudef
      have huR : u.re < -R := by
        rw [hudef, hmdef]
        exact EntireRepelling.rIdx_spec R w
      have hu_lo : -R - 2 < u.re := by
        have hx : (0:ℝ) ≤ w.re + R := by linarith
        have hceil : ((Nat.ceil (w.re + R) : ℕ) : ℝ) < w.re + R + 1 := Nat.ceil_lt_add_one hx
        have hcast : ((EntireRepelling.rIdx R w : ℕ) : ℝ)
            = ((Nat.ceil (w.re + R) : ℕ) : ℝ) + 1 := by
          simp [EntireRepelling.rIdx]
        rw [hudef, hmdef, Complex.sub_re, Complex.natCast_re, hcast]
        linarith
      have hure : |u.re| ≤ R + 2 := by
        rw [abs_le]; constructor <;> linarith
      have himu : u.im = w.im := by rw [hudef]; simp
      obtain ⟨hVre, hVim⟩ := norm_bounds_V (V := V) hVbd (by linarith) huR hure
      have hImx : TD < |(V u).im| := by
        rw [himu] at hVim
        have h2 : 2 * TD + 2 * (R + 2) < |w.im| := by linarith
        linarith
      have hCx : -|(V u).im| - 2 * (R + 2) ≤ (V u).re := by
        have := (abs_le.mp hVre).1
        linarith
      have hxesc := orbit_tendsto_of_bounds hL1esc hL1L hTD (V u) hImx hCx
      have hy : rV f V R w = (wMap f)^[m] (V u) := by
        rw [hudef, hmdef]; rfl
      rw [hy]
      have hshift2 : (fun n : ℕ => ‖(wMap f)^[n] ((wMap f)^[m] (V u))‖)
          = (fun n : ℕ => ‖(wMap f)^[n + m] (V u)‖) := by
        funext n; rw [Function.iterate_add_apply]
      rw [hshift2]
      exact hxesc.comp (tendsto_add_atTop_nat m)
    · -- `w` lies in the left half plane: track the orbit forward to the fundamental strip
      have hlt : w.re < -R := lt_of_not_ge hre
      set x0 : ℝ := -R - w.re with hx0def
      have hx0pos : 0 < x0 := by rw [hx0def]; linarith
      set m : ℕ := Nat.ceil x0 - 1 with hmdef
      have hceilpos : 0 < Nat.ceil x0 := by
        have h1 : (0:ℝ) < ((Nat.ceil x0 : ℕ) : ℝ) := lt_of_lt_of_le hx0pos (Nat.le_ceil x0)
        exact_mod_cast h1
      have hmcast : ((m : ℕ) : ℝ) = ((Nat.ceil x0 : ℕ) : ℝ) - 1 := by
        rw [hmdef, Nat.cast_sub (show 1 ≤ Nat.ceil x0 from hceilpos), Nat.cast_one]
      have hm_lt : (m : ℝ) < x0 := by
        have hceil : ((Nat.ceil x0 : ℕ) : ℝ) < x0 + 1 := Nat.ceil_lt_add_one hx0pos.le
        rw [hmcast]; linarith
      have hm_ge : x0 - 1 ≤ (m : ℝ) := by
        have hceil : x0 ≤ ((Nat.ceil x0 : ℕ) : ℝ) := Nat.le_ceil x0
        rw [hmcast]; linarith
      set v : ℂ := w + (m : ℂ) with hvdef
      have hvR : v.re < -R := by
        rw [hvdef, Complex.add_re, Complex.natCast_re]
        rw [hx0def] at hm_lt; linarith
      have hv_lo : -R - 1 ≤ v.re := by
        rw [hvdef, Complex.add_re, Complex.natCast_re]
        rw [hx0def] at hm_ge; linarith
      have hvre : |v.re| ≤ R + 2 := by
        rw [abs_le]; constructor <;> linarith
      have himv : v.im = w.im := by rw [hvdef]; simp
      obtain ⟨hVre, hVim⟩ := norm_bounds_V (V := V) hVbd (by linarith) hvR hvre
      have hImx : TD < |(V v).im| := by
        rw [himv] at hVim
        have h2 : 2 * TD + 2 * (R + 2) < |w.im| := by linarith
        linarith
      have hCx : -|(V v).im| - 2 * (R + 2) ≤ (V v).re := by
        have := (abs_le.mp hVre).1
        linarith
      have hxesc := orbit_tendsto_of_bounds hL1esc hL1L hTD (V v) hImx hCx
      have hxrel : V v = (wMap f)^[m] (rV f V R w) := by
        have h1 : rV f V R v = (wMap f)^[m] (rV f V R w) := by
          have h2 := rV_add_nat (V := V) (R := R) hVshift w m
          rw [hvdef]; exact h2
        have h3 : rV f V R v = V v := rV_eq_of_re_lt hVshift hvR
        rw [← h3]; exact h1
      apply tendsto_atTop_of_tail (m := m)
      have hshift2 : (fun k : ℕ => ‖(wMap f)^[k + m] (rV f V R w)‖)
          = (fun k : ℕ => ‖(wMap f)^[k] (V v)‖) := by
        funext k
        rw [hxrel, ← Function.iterate_add_apply]
      rw [hshift2]
      exact hxesc
  have h1 : (fun n : ℕ => ‖rV f V R (w + n)‖) = (fun n : ℕ => ‖(wMap f)^[n] (rV f V R w)‖) := by
    funext n
    rw [rV_add_nat hVshift w n]
  rw [h1]
  exact hgoal

end

end Work.FatouCoord.Flower
