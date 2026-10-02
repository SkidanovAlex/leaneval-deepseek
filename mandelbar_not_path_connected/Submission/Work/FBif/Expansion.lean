/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the normalised local expansion and HS's estimate (FBif, part 2)

This module contains

* `Work.FBif.normIter` — the *normalised* perturbed fifth iterate
  `u ↦ (f_ε^5 (z₁ + s u) − z₁)/s` in the coordinate in which the conjugate-linear part of
  `f_ε^5` at `z₁` is `1`;
* `Work.FBif.HSExpansion c z₁ q A` — Hubbard–Schleicher's explicit estimate: on a fixed disc
  the normalised iterate is a *fixed* quadratic map `ū + A ū²` up to an error of size
  `C(ε+‖u‖)‖u‖² + c₂ ε² ‖u‖`, and the normalised constant term
  `g_ε(0) = (f_ε^5 z₁ − z₁)/s` is `c₁ε`-large with `O(ε²)` imaginary part;
* `Work.FBif.HSEstimate.of_expansion` — the derivation of `HSEstimate` from `HSExpansion`,
  using the real-analysis lemma `Work.FBif.LocalBound` (proved in `FBif.HSLocalBound`).

The condition `HSExpansion` is exactly the "HS estimate" of Hubbard–Schleicher's Lemma 3.4:
with `q` vanishing to second order on the parabolic cycle (except at `T⁴ z₁`, where it is `≠ 0`)
the perturbation of the fifth iterate is `ε + O(ε²) + O(‖w‖²)`, and the case analysis of
HS (near the real axis the real part is *increased* by `ε`; off it the conjugate-linear part
forces `y = O(‖u‖²)`) shows that the fifth iterate has no fixed point near `z₁`.
-/
import Submission.Work.FBif.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The **normalised perturbed fifth iterate**
`g_ε(u) = (f_ε^5 (z₁ + s u) − z₁)/s`, where `f_ε = perturb c q ε`.  Fixing points of `f_ε^5`
on `z₁ + s • ball 0 r` correspond to fixed points of `g_ε` on `ball 0 r`. -/
def normIter (c : ℂ) (q : ℂ → ℂ) (z₁ s : ℂ) (ε : ℝ) (u : ℂ) : ℂ :=
  (((perturb c q ε)^[5]) (z₁ + s * u) - z₁) / s

theorem normIter_zero (c : ℂ) (q : ℂ → ℂ) (z₁ s : ℂ) (ε : ℝ) :
    normIter c q z₁ s ε 0 = (((perturb c q ε)^[5]) z₁ - z₁) / s := by
  simp [normIter]

/-- The `z₁ + s u` substitution: a fixed point of `f_ε^5` at `z₁ + s u` is a fixed point of
`normIter`. -/
theorem normIter_eq_iff (c : ℂ) (q : ℂ → ℂ) (z₁ s : ℂ) (ε : ℝ) (u : ℂ) (hs : s ≠ 0) :
    normIter c q z₁ s ε u = u ↔ ((perturb c q ε)^[5]) (z₁ + s * u) = z₁ + s * u := by
  constructor
  · intro h
    have hmul : normIter c q z₁ s ε u * s = u * s := by rw [h]
    rw [normIter, div_mul_cancel₀ _ hs] at hmul
    have hX : ((perturb c q ε)^[5]) (z₁ + s * u) = u * s + z₁ := by rw [← hmul]; ring
    rw [hX]; ring
  · intro h
    rw [normIter, h, add_sub_cancel_left, mul_div_cancel_left₀ u hs]

/-! ## The normalised expansion -/

/-- **Hubbard–Schleicher's normalised expansion of the perturbed fifth iterate.**  There is a
unit complex number `s` (a square root of the conjugate-linear multiplier of `T_c^5` at `z₁`)
in which the coordinate `z = z₁ + s u` puts the map in the normalised form `ū + A ū²`, and on a
fixed disc the normalised iterate `g_ε = normIter c q z₁ s ε` has

* constant term `g_ε(0)` with `Re g_ε(0) ≥ c₁ ε` and `|Im g_ε(0)| ≤ c₂ ε²`;
* error `‖g_ε(u) − g_ε(0) − (ū + A ū²)‖ ≤ C (ε + ‖u‖) ‖u‖² + c₂ ε² ‖u‖`.

This is a `Prop`-valued existential so that it can be used as a hypothesis of a theorem. -/
def HSExpansion (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ) (A : ℂ) : Prop :=
  ∃ s : ℂ, ‖s‖ = 1 ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ c₂ : ℝ, 0 ≤ c₂ ∧
          ∃ c₁ : ℝ, 0 < c₁ ∧
            ∃ ε₀ : ℝ, 0 < ε₀ ∧
              (∀ ε : ℝ, 0 < ε → ε < ε₀ → c₁ * ε ≤ (normIter c q z₁ s ε 0).re) ∧
              (∀ ε : ℝ, 0 < ε → ε < ε₀ → |(normIter c q z₁ s ε 0).im| ≤ c₂ * ε ^ 2) ∧
              (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u : ℂ, ‖u‖ ≤ δ →
                ‖normIter c q z₁ s ε u - normIter c q z₁ s ε 0 - (star u + A * (star u) ^ 2)‖ ≤
                  C * (ε + ‖u‖) * ‖u‖ ^ 2 + c₂ * ε ^ 2 * ‖u‖)

/-! ## HS's estimate from the expansion -/

/-- **The local real-analysis estimate** (Hubbard–Schleicher Lemma 3.4).  If `A` has positive
real part then there are `δ, c₀ > 0` and `K > 0` such that whenever
`ū + A ū² + α + e(u) = u` holds at a point `u` with `‖u‖ ≤ δ` and
`‖e u‖ ≤ c₀‖u‖² + β‖u‖`, then `Re α ≤ K (β + |Im α|)`.

The proof is the case analysis of HS: near the real axis the real part is increased by
`Re α` (`Re(A ū²) ≥ (Re A)/3 ‖u‖²` on `|Im u| ≤ 8‖A‖ (Re u)²`), while off it the conjugate-linear
part `ū` forces `|Im u| = O(β + |Im α|)` and then the real part forces `Re α = O(β + |Im α|)`.
The proof is `Work.FBif.hsLocal_bound` in `FBif.HSLocalBound`. -/
def LocalBound (A : ℂ) : Prop :=
  ∃ δ > 0, ∃ c₀ > 0, ∃ K > 0, ∀ (e : ℂ → ℂ) (α : ℂ) (β : ℝ) (u : ℂ), 0 ≤ β → β ≤ 1 →
    ‖u‖ ≤ δ → ‖e u‖ ≤ c₀ * ‖u‖ ^ 2 + β * ‖u‖ →
    star u + A * (star u) ^ 2 + α + e u = u → α.re ≤ K * (β + |α.im|)

/-- **HS's estimate from the normalised expansion.** -/
theorem HSEstimate.of_expansion {c z₁ : ℂ} {q : ℂ → ℂ} {A : ℂ} (hloc : LocalBound A)
    (h : HSExpansion c z₁ q A) : HSEstimate c z₁ q := by
  obtain ⟨δ₀, hδ₀, c₀, hc₀, K, hK, hbound⟩ := hloc
  obtain ⟨s, hs, δ, hδ, C, hC, c₂, hc₂, c₁, hc₁, ε₀, hε₀, hzre, hzim, herr⟩ := h
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hs; norm_num at hs
  -- the working radius: the same for every small `ε`
  set δ' : ℝ := min δ₀ (min δ (c₀ / (4 * (C + 1)))) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ₀ (lt_min hδ (by positivity))
  have hδ'₀ : δ' ≤ δ₀ := min_le_left _ _
  have hδ'δ : δ' ≤ δ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ'c : δ' ≤ c₀ / (4 * (C + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the range of `ε`
  set A₂ : ℝ := 1 / (c₂ + 1) with hA₂def
  set A₃ : ℝ := 1 / (C + 1) with hA₃def
  set A₄ : ℝ := c₀ / (4 * (C + 1)) with hA₄def
  set A₅ : ℝ := c₁ / (2 * K * (c₂ + 1)) with hA₅def
  have hA₂pos : 0 < A₂ := by rw [hA₂def]; positivity
  have hA₃pos : 0 < A₃ := by rw [hA₃def]; positivity
  have hA₄pos : 0 < A₄ := by rw [hA₄def]; positivity
  have hA₅pos : 0 < A₅ := by rw [hA₅def]; positivity
  set ε₁ : ℝ := min ε₀ (min A₂ (min A₃ (min A₄ A₅))) with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min hε₀ (lt_min hA₂pos (lt_min hA₃pos (lt_min hA₄pos hA₅pos)))
  have hε₀le : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hA₂le : ε₁ ≤ A₂ := by
    rw [hε₁def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hA₃le : ε₁ ≤ A₃ := by
    rw [hε₁def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hA₄le : ε₁ ≤ A₄ := by
    rw [hε₁def]
    exact le_trans (le_trans (min_le_right ε₀ (min A₂ (min A₃ (min A₄ A₅))))
        (min_le_right A₂ (min A₃ (min A₄ A₅))))
      (le_trans (min_le_right A₃ (min A₄ A₅)) (min_le_left A₄ A₅))
  have hA₅le : ε₁ ≤ A₅ := by
    rw [hε₁def]
    exact le_trans (le_trans (min_le_right ε₀ (min A₂ (min A₃ (min A₄ A₅))))
        (min_le_right A₂ (min A₃ (min A₄ A₅))))
      (le_trans (min_le_right A₃ (min A₄ A₅)) (min_le_right A₄ A₅))
  refine ⟨δ', hδ'pos, ε₁, hε₁pos, fun ε hε hεε₁ => ?_⟩
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεε₁ hε₀le
  have hεA₂ : ε < A₂ := lt_of_lt_of_le hεε₁ hA₂le
  have hεA₃ : ε < A₃ := lt_of_lt_of_le hεε₁ hA₃le
  have hεA₄ : ε < A₄ := lt_of_lt_of_le hεε₁ hA₄le
  have hεA₅ : ε < A₅ := lt_of_lt_of_le hεε₁ hA₅le
  -- β = c₂ ε² is at most 1
  have hβ0 : 0 ≤ c₂ * ε ^ 2 := mul_nonneg hc₂ (sq_nonneg _)
  have hβ1 : c₂ * ε ^ 2 ≤ 1 := by
    rw [hA₂def] at hεA₂
    have h1 : ε ^ 2 < 1 / (c₂ + 1) ^ 2 := by
      have hp := pow_lt_pow_left₀ hεA₂ (le_of_lt hε) (by norm_num : (2:ℕ) ≠ 0)
      rwa [div_pow, one_pow] at hp
    have h2 : c₂ * (1 / (c₂ + 1) ^ 2) ≤ 1 := by
      rw [mul_one_div, div_le_one (pow_pos (by linarith : (0:ℝ) < c₂ + 1) 2)]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left h1.le hc₂) h2
  -- the quadratic coefficient `C (ε + ‖u‖)` is at most `c₀` on the working ball
  have hCc : C / (C + 1) ≤ 1 := by
    rw [div_le_one (by linarith : (0:ℝ) < C + 1)]; linarith
  have hCε : C * ε ≤ c₀ / 4 := by
    rw [hA₄def] at hεA₄
    have hlt : C * ε ≤ C * (c₀ / (4 * (C + 1))) := mul_le_mul_of_nonneg_left hεA₄.le hC
    have heq : C * (c₀ / (4 * (C + 1))) = c₀ / 4 * (C / (C + 1)) := by field_simp
    rw [heq] at hlt
    have h2 : c₀ / 4 * (C / (C + 1)) ≤ c₀ / 4 := by
      have h3 : c₀ / 4 * (C / (C + 1)) ≤ c₀ / 4 * 1 :=
        mul_le_mul_of_nonneg_left hCc (le_of_lt (by linarith [hc₀] : (0:ℝ) < c₀ / 4))
      simpa using h3
    exact le_trans hlt h2
  have hCv : ∀ v : ℂ, ‖v‖ ≤ δ' → C * ‖v‖ ≤ c₀ / 4 := by
    intro v hv
    have hvc : ‖v‖ ≤ c₀ / (4 * (C + 1)) := le_trans hv hδ'c
    have hlt : C * ‖v‖ ≤ C * (c₀ / (4 * (C + 1))) := mul_le_mul_of_nonneg_left hvc hC
    have heq : C * (c₀ / (4 * (C + 1))) = c₀ / 4 * (C / (C + 1)) := by field_simp
    rw [heq] at hlt
    have h2 : c₀ / 4 * (C / (C + 1)) ≤ c₀ / 4 := by
      have h3 : c₀ / 4 * (C / (C + 1)) ≤ c₀ / 4 * 1 :=
        mul_le_mul_of_nonneg_left hCc (le_of_lt (by linarith [hc₀] : (0:ℝ) < c₀ / 4))
      simpa using h3
    exact le_trans hlt h2
  intro z hz
  set u : ℂ := (z - z₁) / s with hudef
  have hzu : z₁ + s * u = z := by rw [hudef]; field_simp; ring
  have hunorm : ‖u‖ = ‖z - z₁‖ := by rw [hudef, norm_div, hs, div_one]
  intro hfix
  have huδ' : ‖u‖ < δ' := by rw [hunorm, ← dist_eq_norm]; exact hz
  have huδ₀ : ‖u‖ ≤ δ₀ := le_of_lt (lt_of_lt_of_le huδ' hδ'₀)
  have huin : ‖u‖ ≤ δ := le_of_lt (lt_of_lt_of_le huδ' hδ'δ)
  have hfix' : normIter c q z₁ s ε u = u := by
    rw [normIter_eq_iff c q z₁ s ε u hs0, hzu]; exact hfix
  -- the pointwise error bound at `u`
  have herru : ‖normIter c q z₁ s ε u - normIter c q z₁ s ε 0 - (star u + A * (star u) ^ 2)‖
      ≤ c₀ * ‖u‖ ^ 2 + c₂ * ε ^ 2 * ‖u‖ := by
    have h1 := herr ε hε hεε₀ u huin
    have h2 : C * (ε + ‖u‖) * ‖u‖ ^ 2 ≤ c₀ * ‖u‖ ^ 2 := by
      have h3 : C * ε + C * ‖u‖ ≤ c₀ / 4 + c₀ / 4 := by
        have := hCv u (le_of_lt huδ'); linarith
      nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
    linarith
  have hα := hbound
    (fun v : ℂ => normIter c q z₁ s ε v - normIter c q z₁ s ε 0 - (star v + A * (star v) ^ 2))
    (normIter c q z₁ s ε 0) (c₂ * ε ^ 2) u hβ0 hβ1 huδ₀ herru (by rw [hfix']; ring)
  -- but the expansion forces the opposite inequality
  have hα' : K * (c₂ * ε ^ 2 + |(normIter c q z₁ s ε 0).im|) <
      (normIter c q z₁ s ε 0).re := by
    have h1 : |(normIter c q z₁ s ε 0).im| ≤ c₂ * ε ^ 2 := hzim ε hε hεε₀
    have h2 : c₂ * ε ^ 2 + |(normIter c q z₁ s ε 0).im| ≤ 2 * (c₂ * ε ^ 2) := by linarith
    have h3 : K * (2 * (c₂ * ε ^ 2)) < c₁ * ε := by
      rw [hA₅def] at hεA₅
      have hden : 0 < 2 * K * (c₂ + 1) := by positivity
      have hlt : ε * (2 * K * (c₂ + 1)) < (c₁ / (2 * K * (c₂ + 1))) * (2 * K * (c₂ + 1)) :=
        mul_lt_mul_of_pos_right hεA₅ hden
      rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hlt
      have hle : 2 * K * c₂ * ε ≤ ε * (2 * K * (c₂ + 1)) := by nlinarith
      nlinarith
    have h4 : c₁ * ε ≤ (normIter c q z₁ s ε 0).re := hzre ε hε hεε₀
    calc K * (c₂ * ε ^ 2 + |(normIter c q z₁ s ε 0).im|)
        ≤ K * (2 * (c₂ * ε ^ 2)) := mul_le_mul_of_nonneg_left h2 hK.le
      _ < c₁ * ε := h3
      _ ≤ (normIter c q z₁ s ε 0).re := h4
  exact absurd hα (not_le.mpr hα')

end Work.FBif

end
