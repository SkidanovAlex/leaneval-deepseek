import Mathlib

/-!
# Positivity of the angular-velocity numerator of a chord-concave profile

`Work.Drive.Generic.angVelNum_pos_of_chordConcave`: if `H` is concave *in the chord coordinate*
`X` (i.e. the graph of `H` over `X` lies above every chord, hypothesis `hchord`), `X` is strictly
increasing with positive derivative, and the centre `(xc, yc)` has `xc = X ξ₀` and `yc < H ξ₀`,
then the angular-velocity numerator of the graph `ξ ↦ (X ξ, H ξ)` about `(xc, yc)` is positive:

`0 < (H ξ - yc) * deriv X ξ - (X ξ - xc) * deriv H ξ`  for every interior `ξ`.

Equivalently, the centre lies strictly below the tangent line of the (concave) profile at `ξ`, and
the graph point at `ξ` rotates about the centre with a definite sign.

## Proof

Let `c` be the affine function whose graph is the chord through `(X ξ₀, H ξ₀)` and `(X ξ, H ξ)`.
Chord concavity says `1 ≥ 0` on the interval between `ξ₀` and `ξ`, with equality at both endpoints;
hence `ξ` is a one-sided minimum of `η ↦ H η - c (X η)`, and the one-sided derivative there is
therefore `≤ 0`.  The corresponding derivative is `(X ξ - X ξ₀) * deriv H ξ - (H ξ - H ξ₀) *
deriv X ξ`, whose sign relative to `X ξ - X ξ₀` is exactly the sign of the angular-velocity
numerator; the two cases `ξ₀ < ξ` and `ξ < ξ₀` differ only in which side the minimum lies.
-/

open scoped Topology

namespace Work.Drive.Generic

/-- One-sided Fermat: if `f` is differentiable at `x` and `f x ≤ f y` on a left neighbourhood of
`x`, then `deriv f x ≤ 0`. -/
private lemma deriv_nonpos_of_eventually_ge {f : ℝ → ℝ} {c x : ℝ} (h : HasDerivAt f c x)
    (hge : ∀ᶠ y in 𝓝[<] x, f x ≤ f y) : c ≤ 0 := by
  have hlim : Filter.Tendsto (slope f x) (𝓝[<] x) (𝓝 c) :=
    h.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin, hge] with y hy hyge
  have hyx : y < x := hy
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- One-sided Fermat: if `f` is differentiable at `x` and `f y ≤ f x` on a right neighbourhood of
`x`, then `deriv f x ≤ 0`. -/
private lemma deriv_nonpos_of_eventually_le {f : ℝ → ℝ} {c x : ℝ} (h : HasDerivAt f c x)
    (hle : ∀ᶠ y in 𝓝[>] x, f y ≤ f x) : c ≤ 0 := by
  have hlim : Filter.Tendsto (slope f x) (𝓝[>] x) (𝓝 c) :=
    h.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin, hle] with y hy hyle
  have hyx : x < y := hy
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem angVelNum_pos_of_chordConcave {H X : ℝ → ℝ} {a b xc yc ξ₀ : ℝ} (hab : a < b)
    (hXmono : StrictMonoOn X (Set.Icc a b))
    (hxpos : ∀ ξ ∈ Set.Ioo a b, 0 < deriv X ξ)
    (hHdiff : ∀ ξ ∈ Set.Ioo a b, DifferentiableAt ℝ H ξ)
    (hchord : ∀ ξ₁ ∈ Set.Icc a b, ∀ ξ₂ ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc a b, X ξ = t * X ξ₁ + (1 - t) * X ξ₂ →
        t * H ξ₁ + (1 - t) * H ξ₂ ≤ H ξ)
    (hξ₀ : ξ₀ ∈ Set.Ioo a b) (hyc : yc < H ξ₀) (hxc : xc = X ξ₀) :
    ∀ ξ ∈ Set.Ioo a b, 0 < (H ξ - yc) * deriv X ξ - (X ξ - xc) * deriv H ξ := by
  subst hxc
  intro ξ hξ
  have hξI : ξ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hξ
  have hξ₀I : ξ₀ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hξ₀
  have hX' : 0 < deriv X ξ := hxpos ξ hξ
  have hXd : DifferentiableAt ℝ X ξ := by
    by_contra hc
    rw [deriv_zero_of_not_differentiableAt hc] at hX'
    exact lt_irrefl 0 hX'
  have hHd : DifferentiableAt ℝ H ξ := hHdiff ξ hξ
  have hpos : 0 < (H ξ₀ - yc) * deriv X ξ := mul_pos (by linarith) hX'
  rcases lt_trichotomy ξ₀ ξ with hlt | heq | hgt
  · -- case A : `ξ₀ < ξ`, so `ξ` is a one-sided minimum of the chord defect from the left
    have hEpos : 0 < X ξ - X ξ₀ := sub_pos.mpr (hXmono hξ₀I hξI hlt)
    have hEne : X ξ - X ξ₀ ≠ 0 := ne_of_gt hEpos
    have hpt : ∀ η ∈ Set.Ioo ξ₀ ξ,
        (X ξ - X ξ₀) * H ξ - (H ξ - H ξ₀) * X ξ
          ≤ (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η := by
      intro η hη
      have hηI : η ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ⟨hξ₀.1.trans hη.1, hη.2.trans hξ.2⟩
      let s : ℝ := (H ξ - H ξ₀) / (X ξ - X ξ₀)
      have hsE : (X ξ - X ξ₀) * s = H ξ - H ξ₀ := by
        simp only [s]; field_simp
      set t : ℝ := (X η - X ξ₀) / (X ξ - X ξ₀) with htdef
      have htmem : t ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨?_, ?_⟩
        · simp only [htdef]
          exact div_nonneg (by linarith [hXmono hξ₀I hηI hη.1]) hEpos.le
        · simp only [htdef]
          rw [div_le_one hEpos]
          linarith [hXmono hηI hξI hη.2]
      have hXeq : X η = t * X ξ + (1 - t) * X ξ₀ := by
        simp only [htdef]; field_simp; ring
      have hc := hchord ξ hξI ξ₀ hξ₀I t htmem η hηI hXeq
      have hteq : t * H ξ + (1 - t) * H ξ₀ = H ξ₀ + s * (X η - X ξ₀) := by
        simp only [htdef, s]; field_simp; ring
      have hconcl : H ξ₀ + s * (X η - X ξ₀) ≤ H η := by rw [← hteq]; exact hc
      have hmul := mul_le_mul_of_nonneg_left hconcl hEpos.le
      have h2 : (X ξ - X ξ₀) * (H ξ₀ + s * (X η - X ξ₀))
          = (X ξ - X ξ₀) * H ξ₀ + (H ξ - H ξ₀) * (X η - X ξ₀) := by
        rw [mul_add, ← mul_assoc, hsE]
      rw [h2] at hmul
      have hring : (X ξ - X ξ₀) * H ξ - (H ξ - H ξ₀) * X ξ
          = (X ξ - X ξ₀) * H ξ₀ - (H ξ - H ξ₀) * X ξ₀ := by ring
      linarith
    have hge : ∀ᶠ η in 𝓝[<] ξ,
        (X ξ - X ξ₀) * H ξ - (H ξ - H ξ₀) * X ξ
          ≤ (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioo_mem_nhds hlt (lt_add_one ξ)] with η hη hlt2
      exact hpt η ⟨hη.1, hlt2⟩
    have hVd : HasDerivAt (fun η => (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η)
        ((X ξ - X ξ₀) * deriv H ξ - (H ξ - H ξ₀) * deriv X ξ) ξ :=
      (hHd.hasDerivAt.const_mul _).sub (hXd.hasDerivAt.const_mul _)
    have hkey : (X ξ - X ξ₀) * deriv H ξ - (H ξ - H ξ₀) * deriv X ξ ≤ 0 :=
      deriv_nonpos_of_eventually_ge hVd hge
    nlinarith [hkey, hpos]
  · -- the centre sits on the graph over `ξ = ξ₀`
    subst heq
    rw [sub_self, zero_mul, sub_zero]
    exact hpos
  · -- case B : `ξ < ξ₀`, so `ξ` is a one-sided maximum of the chord defect on the right
    have hEneg : X ξ - X ξ₀ < 0 := sub_neg.mpr (hXmono hξI hξ₀I hgt)
    have hEne : X ξ - X ξ₀ ≠ 0 := ne_of_lt hEneg
    have hpt : ∀ η ∈ Set.Ioo ξ ξ₀,
        (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η
          ≤ (X ξ - X ξ₀) * H ξ₀ - (H ξ - H ξ₀) * X ξ₀ := by
      intro η hη
      have hηI : η ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ⟨hξ.1.trans hη.1, hη.2.trans hξ₀.2⟩
      let s : ℝ := (H ξ - H ξ₀) / (X ξ - X ξ₀)
      have hsE : (X ξ - X ξ₀) * s = H ξ - H ξ₀ := by
        simp only [s]; field_simp
      set t : ℝ := (X η - X ξ₀) / (X ξ - X ξ₀) with htdef
      have htmem : t ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨?_, ?_⟩
        · simp only [htdef]
          exact div_nonneg_of_nonpos (by linarith [hXmono hηI hξ₀I hη.2]) hEneg.le
        · simp only [htdef]
          rw [div_le_one_of_neg hEneg]
          linarith [(hXmono hξI hηI hη.1).le]
      have hXeq : X η = t * X ξ + (1 - t) * X ξ₀ := by
        simp only [htdef]; field_simp; ring
      have hc := hchord ξ hξI ξ₀ hξ₀I t htmem η hηI hXeq
      have hteq : t * H ξ + (1 - t) * H ξ₀ = H ξ₀ + s * (X η - X ξ₀) := by
        simp only [htdef, s]; field_simp; ring
      have hconcl : H ξ₀ + s * (X η - X ξ₀) ≤ H η := by rw [← hteq]; exact hc
      have hmul := mul_le_mul_of_nonpos_left hconcl hEneg.le
      have h2 : (X ξ - X ξ₀) * (H ξ₀ + s * (X η - X ξ₀))
          = (X ξ - X ξ₀) * H ξ₀ + (H ξ - H ξ₀) * (X η - X ξ₀) := by
        rw [mul_add, ← mul_assoc, hsE]
      rw [h2] at hmul
      linarith
    have hle : ∀ᶠ η in 𝓝[>] ξ,
        (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η
          ≤ (X ξ - X ξ₀) * H ξ - (H ξ - H ξ₀) * X ξ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [show Set.Ioo (ξ - 1) ξ₀ ∈ 𝓝 ξ from Ioo_mem_nhds (by linarith) hgt]
        with η hη hgt2
      have h := hpt η ⟨hgt2, hη.2⟩
      have hring : (X ξ - X ξ₀) * H ξ - (H ξ - H ξ₀) * X ξ
          = (X ξ - X ξ₀) * H ξ₀ - (H ξ - H ξ₀) * X ξ₀ := by ring
      linarith
    have hVd : HasDerivAt (fun η => (X ξ - X ξ₀) * H η - (H ξ - H ξ₀) * X η)
        ((X ξ - X ξ₀) * deriv H ξ - (H ξ - H ξ₀) * deriv X ξ) ξ :=
      (hHd.hasDerivAt.const_mul _).sub (hXd.hasDerivAt.const_mul _)
    have hkey : (X ξ - X ξ₀) * deriv H ξ - (H ξ - H ξ₀) * deriv X ξ ≤ 0 :=
      deriv_nonpos_of_eventually_le hVd hle
    nlinarith [hkey, hpos]

end Work.Drive.Generic
