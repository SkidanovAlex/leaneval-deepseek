import Mathlib
-- The statement needs only Mathlib; the original file imported `lensShape` for context, but the
-- proof below is self-contained in the `x`/`H` API.  Keeping the dependency out of the import
-- list makes this concrete lemma buildable independently of the (still evolving) sweep files.

/-!
# Concavity of `H` in the chord coordinate `x`

If `x : ℝ → ℝ` is `C²`, strictly increasing on `[0,1]` with `x' > 0` in the interior, and
`H : ℝ → ℝ` is `C²`, and the "curvature" of the graph `ξ ↦ (x ξ, H ξ)` against the vertical
direction is nonpositive,

    deriv (deriv H) ξ * deriv x ξ - deriv H ξ * deriv (deriv x) ξ ≤ 0     (0 < ξ < 1),

then `H` is concave *in the coordinate* `x`: for `ξ₁, ξ₂, ξ ∈ [0,1]` and `t ∈ [0,1]` with
`x ξ = t x ξ₁ + (1-t) x ξ₂`, one has `t H ξ₁ + (1-t) H ξ₂ ≤ H ξ`.

Equivalently, with `p := deriv H / deriv x`, the hypothesis says `p` is nonincreasing, so the
graph `u ↦ H (x⁻¹ u)` has a nonincreasing derivative and is concave.  The proof below avoids
naming `x⁻¹`: it uses the chord function

    chordFn x H ξ₁ ξ₂ ξ = (H ξ - H ξ₁) (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) (x ξ - x ξ₁),

whose derivative is `(x ξ₂ - x ξ₁) (deriv x ξ) (p ξ - p c)` for the point `c` produced by
Rolle's theorem, hence is nonnegative to the left of `c` and nonpositive to the right.

This is the `H'' x' - H' x'' ≤ 0` ⟹ concavity-in-the-chord-coordinate brick of the low end of
the sweep (see `Submission/Work/Drive/lensShape.lean`).
-/

noncomputable section

namespace Work.Drive

/-- The chord-referenced difference of the pair `(x, H)`: its sign at `ξ` is the statement that
`(x ξ, H ξ)` lies above the chord through `(x ξ₁, H ξ₁)` and `(x ξ₂, H ξ₂)`. -/
def chordFn (x H : ℝ → ℝ) (ξ₁ ξ₂ : ℝ) : ℝ → ℝ :=
  fun ξ => (H ξ - H ξ₁) * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * (x ξ - x ξ₁)

lemma deriv_chordFn {x H : ℝ → ℝ} {ξ₁ ξ₂ ξ : ℝ}
    (hxd : DifferentiableAt ℝ x ξ) (hHd : DifferentiableAt ℝ H ξ) :
    deriv (chordFn x H ξ₁ ξ₂) ξ
      = deriv H ξ * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * deriv x ξ := by
  have h1 : HasDerivAt (fun ξ' => H ξ' - H ξ₁) (deriv H ξ) ξ := hHd.hasDerivAt.sub_const _
  have h2 : HasDerivAt (fun ξ' => (H ξ' - H ξ₁) * (x ξ₂ - x ξ₁))
      (deriv H ξ * (x ξ₂ - x ξ₁)) ξ := h1.mul_const _
  have h3 : HasDerivAt (fun ξ' => x ξ' - x ξ₁) (deriv x ξ) ξ := hxd.hasDerivAt.sub_const _
  have h4 : HasDerivAt (fun ξ' => (H ξ₂ - H ξ₁) * (x ξ' - x ξ₁))
      ((H ξ₂ - H ξ₁) * deriv x ξ) ξ := h3.const_mul _
  have hfun : chordFn x H ξ₁ ξ₂
      = fun ξ' => (H ξ' - H ξ₁) * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * (x ξ' - x ξ₁) := rfl
  rw [hfun]
  exact (h2.sub h4).deriv

lemma continuousOn_chordFn {x H : ℝ → ℝ} {a b ξ₁ ξ₂ : ℝ}
    (hx : ContinuousOn x (Set.Icc a b)) (hH : ContinuousOn H (Set.Icc a b)) :
    ContinuousOn (chordFn x H ξ₁ ξ₂) (Set.Icc a b) := by
  unfold chordFn
  exact ((hH.sub continuousOn_const).mul continuousOn_const).sub
    (continuousOn_const.mul (hx.sub continuousOn_const))

lemma differentiableOn_chordFn {x H : ℝ → ℝ} {s : Set ℝ} {ξ₁ ξ₂ : ℝ}
    (hx : DifferentiableOn ℝ x s) (hH : DifferentiableOn ℝ H s) :
    DifferentiableOn ℝ (chordFn x H ξ₁ ξ₂) s := by
  unfold chordFn
  exact ((hH.sub (differentiableOn_const _)).mul_const _).sub
    ((differentiableOn_const _).mul (hx.sub (differentiableOn_const _)))

/-- **The logarithmic-derivative ratio `deriv H / deriv x` is nonincreasing.**  This is the
hypothesis `H'' x' - H' x'' ≤ 0` rewritten via the quotient rule. -/
lemma antitoneOn_deriv_div {x H : ℝ → ℝ}
    (hx : ContDiffOn ℝ 2 x (Set.Icc (0 : ℝ) 1)) (hH : ContDiffOn ℝ 2 H (Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv x ξ)
    (hcurv : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv H) ξ * deriv x ξ - deriv H ξ * deriv (deriv x) ξ ≤ 0) :
    AntitoneOn (fun ξ => deriv H ξ / deriv x ξ) (Set.Ioo (0 : ℝ) 1) := by
  have hxo : ContDiffOn ℝ 2 x (Set.Ioo (0:ℝ) 1) := hx.mono Set.Ioo_subset_Icc_self
  have hHo : ContDiffOn ℝ 2 H (Set.Ioo (0:ℝ) 1) := hH.mono Set.Ioo_subset_Icc_self
  have hxd : DifferentiableOn ℝ (deriv x) (Set.Ioo (0:ℝ) 1) :=
    (hxo.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn (by norm_num)
  have hHd : DifferentiableOn ℝ (deriv H) (Set.Ioo (0:ℝ) 1) :=
    (hHo.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn (by norm_num)
  have hne : ∀ ξ ∈ Set.Ioo (0:ℝ) 1, deriv x ξ ≠ 0 := fun ξ hξ => ne_of_gt (hxpos ξ hξ)
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 1) ?_ ?_ ?_
  · exact (DifferentiableOn.div (c := deriv H) (d := deriv x) hHd hxd hne).continuousOn
  · rw [interior_Ioo]
    exact DifferentiableOn.div (c := deriv H) (d := deriv x) hHd hxd hne
  · intro ξ hξ
    rw [interior_Ioo] at hξ
    have h := deriv_div (c := deriv H) (d := deriv x)
      (hHd.differentiableAt (isOpen_Ioo.mem_nhds hξ))
      (hxd.differentiableAt (isOpen_Ioo.mem_nhds hξ)) (hne ξ hξ)
    change deriv (deriv H / deriv x) ξ ≤ 0
    rw [h]
    exact div_nonpos_of_nonpos_of_nonneg (hcurv ξ hξ) (sq_nonneg _)

/-- **The chord function is nonnegative.**  This is the main case of the theorem, stated for
parameters with `ξ₁ < ξ₂` and the chord slope (`p c`) supplied by Rolle's theorem. -/
lemma chord_le_of_lt_chord {x H : ℝ → ℝ} (hxmono : StrictMonoOn x (Set.Icc (0:ℝ) 1))
    (hx : ContDiffOn ℝ 2 x (Set.Icc (0:ℝ) 1)) (hH : ContDiffOn ℝ 2 H (Set.Icc (0:ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0:ℝ) 1, 0 < deriv x ξ)
    (hp : AntitoneOn (fun ξ => deriv H ξ / deriv x ξ) (Set.Ioo (0:ℝ) 1))
    {ξ₁ ξ₂ t ξ : ℝ} (hξ₁ : ξ₁ ∈ Set.Icc (0:ℝ) 1) (hξ₂ : ξ₂ ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hξ : ξ ∈ Set.Icc (0:ℝ) 1) (hlt : ξ₁ < ξ₂)
    (hxeq : x ξ = t * x ξ₁ + (1 - t) * x ξ₂) :
    t * H ξ₁ + (1 - t) * H ξ₂ ≤ H ξ := by
  have hsubIcc : Set.Icc ξ₁ ξ₂ ⊆ Set.Icc (0:ℝ) 1 := Set.Icc_subset_Icc hξ₁.1 hξ₂.2
  have hsub : Set.Ioo ξ₁ ξ₂ ⊆ Set.Ioo (0:ℝ) 1 :=
    fun z hz => ⟨lt_of_le_of_lt hξ₁.1 hz.1, lt_of_lt_of_le hz.2 hξ₂.2⟩
  have hcx : ContinuousOn x (Set.Icc ξ₁ ξ₂) := (hx.mono hsubIcc).continuousOn
  have hcH : ContinuousOn H (Set.Icc ξ₁ ξ₂) := (hH.mono hsubIcc).continuousOn
  have hdx : DifferentiableOn ℝ x (Set.Ioo ξ₁ ξ₂) :=
    (hx.mono (hsub.trans Set.Ioo_subset_Icc_self)).differentiableOn (by norm_num)
  have hdH : DifferentiableOn ℝ H (Set.Ioo ξ₁ ξ₂) :=
    (hH.mono (hsub.trans Set.Ioo_subset_Icc_self)).differentiableOn (by norm_num)
  have hcontF : ContinuousOn (chordFn x H ξ₁ ξ₂) (Set.Icc ξ₁ ξ₂) := continuousOn_chordFn hcx hcH
  have hdiffF : DifferentiableOn ℝ (chordFn x H ξ₁ ξ₂) (Set.Ioo ξ₁ ξ₂) :=
    differentiableOn_chordFn hdx hdH
  obtain ⟨c, hc, hcslope⟩ := exists_deriv_eq_slope (chordFn x H ξ₁ ξ₂) hlt hcontF hdiffF
  have hF1 : chordFn x H ξ₁ ξ₂ ξ₁ = 0 := by simp [chordFn]
  have hF2 : chordFn x H ξ₁ ξ₂ ξ₂ = 0 := by simp [chordFn]
  have hc0 : deriv (chordFn x H ξ₁ ξ₂) c = 0 := by
    rw [hcslope, hF2, hF1]; simp
  have hcdx : DifferentiableAt ℝ x c := hdx.differentiableAt (isOpen_Ioo.mem_nhds hc)
  have hcdH : DifferentiableAt ℝ H c := hdH.differentiableAt (isOpen_Ioo.mem_nhds hc)
  have hceq : (H ξ₂ - H ξ₁) * deriv x c = deriv H c * (x ξ₂ - x ξ₁) := by
    rw [deriv_chordFn (ξ₁ := ξ₁) (ξ₂ := ξ₂) hcdx hcdH] at hc0
    linarith
  have hcmem : c ∈ Set.Ioo (0:ℝ) 1 := hsub hc
  have hcpx : 0 < deriv x c := hxpos c hcmem
  have hΔxpos : 0 < x ξ₂ - x ξ₁ := by
    have := hxmono hξ₁ hξ₂ hlt; linarith
  have hsign1 : ∀ ξ' ∈ Set.Ioo ξ₁ c, 0 ≤ deriv (chordFn x H ξ₁ ξ₂) ξ' := by
    intro ξ' hξ'
    have hξ'12 : ξ' ∈ Set.Ioo ξ₁ ξ₂ := ⟨hξ'.1, hξ'.2.trans hc.2⟩
    have hξ'mem : ξ' ∈ Set.Ioo (0:ℝ) 1 := hsub hξ'12
    have hξ'px : 0 < deriv x ξ' := hxpos ξ' hξ'mem
    have hle : deriv H c / deriv x c ≤ deriv H ξ' / deriv x ξ' := hp hξ'mem hcmem hξ'.2.le
    have hle' : deriv H c * deriv x ξ' ≤ deriv H ξ' * deriv x c :=
      (div_le_div_iff₀ hcpx hξ'px).mp hle
    have hdx' : DifferentiableAt ℝ x ξ' := hdx.differentiableAt (isOpen_Ioo.mem_nhds hξ'12)
    have hdH' : DifferentiableAt ℝ H ξ' := hdH.differentiableAt (isOpen_Ioo.mem_nhds hξ'12)
    rw [deriv_chordFn (ξ₁ := ξ₁) (ξ₂ := ξ₂) hdx' hdH']
    have key : 0 ≤ deriv x c
        * (deriv H ξ' * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * deriv x ξ') := by
      have hfac : deriv x c * (deriv H ξ' * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * deriv x ξ')
          = (x ξ₂ - x ξ₁) * (deriv H ξ' * deriv x c - deriv H c * deriv x ξ') := by
        linear_combination (-(deriv x ξ')) * hceq
      rw [hfac]
      exact mul_nonneg hΔxpos.le (by linarith)
    exact nonneg_of_mul_nonneg_right key hcpx
  have hsign2 : ∀ ξ' ∈ Set.Ioo c ξ₂, deriv (chordFn x H ξ₁ ξ₂) ξ' ≤ 0 := by
    intro ξ' hξ'
    have hξ'12 : ξ' ∈ Set.Ioo ξ₁ ξ₂ := ⟨hc.1.trans hξ'.1, hξ'.2⟩
    have hξ'mem : ξ' ∈ Set.Ioo (0:ℝ) 1 := hsub hξ'12
    have hξ'px : 0 < deriv x ξ' := hxpos ξ' hξ'mem
    have hle : deriv H ξ' / deriv x ξ' ≤ deriv H c / deriv x c := hp hcmem hξ'mem hξ'.1.le
    have hle' : deriv H ξ' * deriv x c ≤ deriv H c * deriv x ξ' :=
      (div_le_div_iff₀ hξ'px hcpx).mp hle
    have hdx' : DifferentiableAt ℝ x ξ' := hdx.differentiableAt (isOpen_Ioo.mem_nhds hξ'12)
    have hdH' : DifferentiableAt ℝ H ξ' := hdH.differentiableAt (isOpen_Ioo.mem_nhds hξ'12)
    rw [deriv_chordFn (ξ₁ := ξ₁) (ξ₂ := ξ₂) hdx' hdH']
    have key : deriv x c * (deriv H ξ' * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * deriv x ξ') ≤ 0 := by
      have hfac : deriv x c * (deriv H ξ' * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * deriv x ξ')
          = (x ξ₂ - x ξ₁) * (deriv H ξ' * deriv x c - deriv H c * deriv x ξ') := by
        linear_combination (-(deriv x ξ')) * hceq
      rw [hfac]
      exact mul_nonpos_of_nonneg_of_nonpos hΔxpos.le (by linarith)
    exact nonpos_of_mul_nonpos_right key hcpx
  have hmono : MonotoneOn (chordFn x H ξ₁ ξ₂) (Set.Icc ξ₁ c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc ξ₁ c) ?_ ?_ ?_
    · exact hcontF.mono (Set.Icc_subset_Icc le_rfl hc.2.le)
    · rw [interior_Icc]; exact hdiffF.mono (Set.Ioo_subset_Ioo le_rfl hc.2.le)
    · intro ξ' hξ'; rw [interior_Icc] at hξ'; exact hsign1 ξ' hξ'
  have hanti : AntitoneOn (chordFn x H ξ₁ ξ₂) (Set.Icc c ξ₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc c ξ₂) ?_ ?_ ?_
    · exact hcontF.mono (Set.Icc_subset_Icc hc.1.le le_rfl)
    · rw [interior_Icc]; exact hdiffF.mono (Set.Ioo_subset_Ioo hc.1.le le_rfl)
    · intro ξ' hξ'; rw [interior_Icc] at hξ'; exact hsign2 ξ' hξ'
  have hxle : x ξ ≤ x ξ₂ := by
    have h1 : x ξ - x ξ₂ = t * (x ξ₁ - x ξ₂) := by rw [hxeq]; ring
    have h2 : t * (x ξ₁ - x ξ₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 (by linarith)
    linarith [h1, h2]
  have hxge : x ξ₁ ≤ x ξ := by
    have h1 : x ξ - x ξ₁ = (1 - t) * (x ξ₂ - x ξ₁) := by rw [hxeq]; ring
    have h2 : 0 ≤ (1 - t) * (x ξ₂ - x ξ₁) := mul_nonneg (by linarith [ht.2]) hΔxpos.le
    linarith [h1, h2]
  have hξ_ge : ξ₁ ≤ ξ := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt' := hxmono hξ hξ₁ hcon
    linarith
  have hξ_le : ξ ≤ ξ₂ := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt' := hxmono hξ₂ hξ hcon
    linarith
  have hchord : 0 ≤ chordFn x H ξ₁ ξ₂ ξ := by
    rcases le_total ξ c with hle | hle
    · have hmem : ξ ∈ Set.Icc ξ₁ c := ⟨hξ_ge, hle⟩
      have h' := hmono (Set.left_mem_Icc.mpr hc.1.le) hmem hξ_ge
      rw [hF1] at h'; exact h'
    · have hmem : ξ ∈ Set.Icc c ξ₂ := ⟨hle, hξ_le⟩
      have h' := hanti hmem (Set.right_mem_Icc.mpr hc.2.le) hξ_le
      rw [hF2] at h'; exact h'
  have hfinal : 0 ≤ (H ξ - H ξ₁) * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * (x ξ - x ξ₁) := hchord
  have hxξ1 : x ξ - x ξ₁ = (1 - t) * (x ξ₂ - x ξ₁) := by rw [hxeq]; ring
  rw [hxξ1] at hfinal
  have hfac : (H ξ - H ξ₁) * (x ξ₂ - x ξ₁) - (H ξ₂ - H ξ₁) * ((1 - t) * (x ξ₂ - x ξ₁))
      = (H ξ - H ξ₁ - (1 - t) * (H ξ₂ - H ξ₁)) * (x ξ₂ - x ξ₁) := by ring
  rw [hfac] at hfinal
  have hlast : 0 ≤ H ξ - H ξ₁ - (1 - t) * (H ξ₂ - H ξ₁) :=
    nonneg_of_mul_nonneg_left hfinal hΔxpos
  linarith

theorem lensConcaveInChordCoord {x H : ℝ → ℝ}
    (hxmono : StrictMonoOn x (Set.Icc (0 : ℝ) 1))
    (hx : ContDiffOn ℝ 2 x (Set.Icc (0 : ℝ) 1))
    (hH : ContDiffOn ℝ 2 H (Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv x ξ)
    (hcurv : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (deriv H) ξ * deriv x ξ - deriv H ξ * deriv (deriv x) ξ ≤ 0) :
    ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1, x ξ = t * x ξ₁ + (1 - t) * x ξ₂ →
        t * H ξ₁ + (1 - t) * H ξ₂ ≤ H ξ := by
  have hp : AntitoneOn (fun ξ => deriv H ξ / deriv x ξ) (Set.Ioo (0:ℝ) 1) :=
    antitoneOn_deriv_div hx hH hxpos hcurv
  intro ξ₁ hξ₁ ξ₂ hξ₂ t ht ξ hξ hxeq
  rcases lt_trichotomy ξ₁ ξ₂ with hlt | heq | hgt
  · exact chord_le_of_lt_chord hxmono hx hH hxpos hp hξ₁ hξ₂ ht hξ hlt hxeq
  · have hxξ : x ξ = x ξ₁ := by rw [hxeq, heq]; ring
    have hξeq : ξ = ξ₁ := hxmono.injOn hξ hξ₁ hxξ
    rw [hξeq, heq]
    have h : t * H ξ₂ + (1 - t) * H ξ₂ = H ξ₂ := by ring
    rw [h]
  · have h := chord_le_of_lt_chord (ξ₁ := ξ₂) (ξ₂ := ξ₁) (t := 1 - t)
      hxmono hx hH hxpos hp hξ₂ hξ₁
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ hξ hgt (by rw [hxeq]; ring)
    linarith

end Work.Drive
