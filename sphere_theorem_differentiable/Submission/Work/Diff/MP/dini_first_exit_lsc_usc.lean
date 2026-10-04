import Mathlib
import Submission.Work.Diff.MP.dini_first_exit
import Submission.Work.Diff.MP.dini_mono_of_lsc
import Submission.Work.Diff.MP.lsc_mul_exp
import Submission.Work.Diff.MP.lsc_left_mul_exp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Set

/-- The `ε`-`δ` form of lower semicontinuity of `f` at `t` *within* a set `s`. -/
lemma exists_delta_of_lsc {f : ℝ → ℝ} {s : Set ℝ} {t y : ℝ}
    (h : LowerSemicontinuousWithinAt f s t) (hy : y < f t) :
    ∃ δ > 0, ∀ x ∈ s, |x - t| < δ → y < f x := by
  have h' : ∀ᶠ x in nhdsWithin t s, y < f x := h y hy
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at h'
  obtain ⟨δ, hδ, hδ'⟩ := h'
  exact ⟨δ, hδ, fun x hx hxt => hδ' ⟨by rwa [Metric.mem_ball, Real.dist_eq], hx⟩⟩

/-- Lower semicontinuity on `[a,b]` yields lower semicontinuity "from the left" at every point of
`(a,b]`, in the quantitative form used by the Dini–Grönwall lemmas. -/
lemma lsc_left_of_lsc {f : ℝ → ℝ} {a b : ℝ} (hlsc : LowerSemicontinuousOn f (Icc a b)) :
    ∀ t ∈ Ioc a b, ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f t ≤ f (t - s) + ε := by
  intro t ht ε hε
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_of_lsc (hlsc t htIcc) (sub_lt_self (f t) hε)
  refine ⟨min δ (t - a), lt_min hδ (by linarith [ht.1]), ?_⟩
  intro s hs hsm
  have hmem : t - s ∈ Icc a b := by
    refine ⟨?_, by linarith [hs, ht.2]⟩
    have h1 : s < t - a := lt_of_lt_of_le hsm (min_le_right _ _)
    linarith
  have h2 : |t - s - t| < δ := by
    rw [show t - s - t = -s by ring, abs_neg, abs_of_pos hs]
    exact lt_of_lt_of_le hsm (min_le_left _ _)
  have h3 := hδ' (t - s) hmem h2
  linarith

/-- Lower semicontinuity on `[a,b]` together with upper semicontinuity from the right gives
continuity from the right at every `t ∈ [a,b)`. -/
lemma continuousWithinAt_Ici_of_lsc_usc {f : ℝ → ℝ} {a b : ℝ}
    (hlsc : LowerSemicontinuousOn f (Icc a b))
    (hrusc : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → f (t + h) ≤ f t + ε) :
    ∀ t ∈ Ico a b, ContinuousWithinAt f (Ici t) t := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have htIcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    exists_delta_of_lsc (hlsc t htIcc) (sub_lt_self (f t) hε2)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hrusc t ht (ε / 2) hε2
  refine ⟨min δ₁ (min δ₂ (b - t)), lt_min hδ₁ (lt_min hδ₂ (by linarith [ht.2])), ?_⟩
  intro y hy hyt
  have hy' : t ≤ y := hy
  rw [Real.dist_eq] at hyt ⊢
  have h1 : |y - t| < δ₁ := lt_of_lt_of_le hyt (min_le_left _ _)
  have h2 : |y - t| < δ₂ :=
    lt_of_lt_of_le hyt (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |y - t| < b - t :=
    lt_of_lt_of_le hyt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hnn : (0 : ℝ) ≤ y - t := by linarith
  have hyb : y ≤ b := by
    have h4 : y - t < b - t := by rwa [abs_of_nonneg hnn] at h3
    linarith
  have hmem : y ∈ Icc a b := ⟨le_trans ht.1 hy', hyb⟩
  have hlow : f t - ε / 2 < f y := hδ₁' y hmem h1
  have hup : f y ≤ f t + ε / 2 := by
    rcases eq_or_lt_of_le hy' with heq | hlt
    · rw [← heq]; linarith
    · have hh : 0 < y - t := sub_pos.mpr hlt
      have hle : y - t ≤ δ₂ := by rw [abs_of_nonneg hnn] at h2; linarith
      have h5 := hδ₂' (y - t) hh hle
      rwa [add_sub_cancel] at h5
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **The last zero.**  If `f ≥ 0` is lower semicontinuous on `[a,b]` and vanishes at `a`, then
below any `t₁ ∈ [a,b]` there is a last zero: `t₀ ∈ [a,t₁]` with `f t₀ = 0` and `f > 0` on
`(t₀,t₁]`. -/
lemma exists_last_zero_of_lsc {f : ℝ → ℝ} {a b t₁ : ℝ} (ha : f a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t) (hlsc : LowerSemicontinuousOn f (Icc a b))
    (ht₁ : t₁ ∈ Icc a b) :
    ∃ t₀ ∈ Icc a t₁, f t₀ = 0 ∧ ∀ s ∈ Ioc t₀ t₁, 0 < f s := by
  -- the zero set below `t₁` is closed, because `LowerSemicontinuousOn` makes `{f ≤ 0}` a
  -- relatively closed set
  let Z : Set ℝ := {t | t ∈ Icc a t₁ ∧ f t = 0}
  have haZ : a ∈ Z := ⟨⟨le_rfl, ht₁.1⟩, ha⟩
  have hZne : Z.Nonempty := ⟨a, haZ⟩
  have hZbd : BddAbove Z := ⟨t₁, fun t ht => ht.1.2⟩
  have hZclosed : IsClosed Z := by
    obtain ⟨v, hvcl, hv⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp hlsc) 0
    have hZeq : Z = Icc a t₁ ∩ v := by
      ext t
      constructor
      · rintro ⟨htI, hft⟩
        refine ⟨htI, ?_⟩
        have h1 : t ∈ Icc a b ∩ f ⁻¹' Iic (0 : ℝ) :=
          ⟨⟨htI.1, le_trans htI.2 ht₁.2⟩, by simpa using hft.le⟩
        rw [hv] at h1
        exact h1.2
      · rintro ⟨htI, htv⟩
        have h1 : t ∈ Icc a b ∩ v := ⟨⟨htI.1, le_trans htI.2 ht₁.2⟩, htv⟩
        rw [← hv] at h1
        exact ⟨htI, le_antisymm h1.2 (hnonneg t h1.1)⟩
    rw [hZeq]
    exact isClosed_Icc.inter hvcl
  have ht₀Z : sSup Z ∈ Z := hZclosed.csSup_mem hZne hZbd
  refine ⟨sSup Z, ht₀Z.1, ht₀Z.2, ?_⟩
  intro s hs
  have hsIccb : s ∈ Icc a b :=
    ⟨le_trans ht₀Z.1.1 hs.1.le, le_trans hs.2 ht₁.2⟩
  rcases lt_or_eq_of_le (hnonneg s hsIccb) with h | h
  · exact h
  · exfalso
    have hsZ : s ∈ Z := ⟨⟨le_trans ht₀Z.1.1 hs.1.le, hs.2⟩, h.symm⟩
    exact absurd hs.1 (not_lt.mpr (le_csSup hZbd hsZ))

/-- **Dini–Grönwall for a nonnegative function that is lower semi-continuous and upper
semi-continuous from the right** (this is the exact real-analysis input of the time-dependent
maximum principle; the older `dini_first_exit_lsc` asks for left-lower-semicontinuity plus full
right-continuity instead).

`f : [a,b] → ℝ`, `a < b`, `f ≥ 0`, `f a = 0`, `f` lower semi-continuous on `[a,b]`, right-USC
(`∀ t < b, ∀ ε > 0, f ≤ f t + ε` eventually on the right of `t`), and the upper right Dini
derivative of `f` is at most `C f` at the points where `f > 0` (quantitative `ε`-form).  Then
`f ≡ 0`.

Proof: if `f(s) > 0`, let `a' = sup {t ≤ s : f t = 0}`; LSC makes the zero set closed, so `f a' = 0`
and `f > 0` on `(a', s]`.  `g = e^{-Ct} f` satisfies `D⁺g ≤ 0` on `(a', s]` and is left-LSC, so `g`
is non-increasing there (Dini's monotonicity theorem, applied on `[a''，s]` for each `a'' ∈ (a',s)`).
Hence `f s ≤ e^{C(s-a'')} f a''` for `a'' ↓ a'`, and right-USC at `a'` gives `f s ≤ 0`, a
contradiction. -/
theorem dini_first_exit_lsc_usc {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t) (ha : f a = 0)
    (hlsc : LowerSemicontinuousOn f (Icc a b))
    (hrusc : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → f (t + h) ≤ f t + ε)
    (hD : ∀ t ∈ Ico a b, 0 < f t → ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
      f (t + h) ≤ f t + h * (C * f t + ε)) :
    ∀ t ∈ Icc a b, f t = 0 := by
  have _ := hab
  -- the two consequences of the hypotheses that the Dini machinery needs
  have hL : ∀ t ∈ Ioc a b, ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f t ≤ f (t - s) + ε :=
    lsc_left_of_lsc hlsc
  have hRt : ∀ t ∈ Ico a b, ContinuousWithinAt f (Ici t) t :=
    continuousWithinAt_Ici_of_lsc_usc hlsc hrusc
  intro t₁ ht₁
  by_contra hne
  have hft₁ : 0 < f t₁ := lt_of_le_of_ne (hnonneg t₁ ht₁) (Ne.symm hne)
  -- the last zero of `f` below `t₁`
  obtain ⟨t₀, ht₀I, hft₀, hpos⟩ := exists_last_zero_of_lsc ha hnonneg hlsc ht₁
  have ht₀lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀I.2 with h | h
    · exact h
    · exfalso
      rw [h] at hft₀
      linarith
  -- on every `[s,t] ⊆ (t₀,t₁]` the rotated function `g r = f r * exp (-(C*r))` is non-increasing
  have hkey : ∀ s t : ℝ, t₀ < s → s < t → t ≤ t₁ →
      f t * Real.exp (-(C * t)) ≤ f s * Real.exp (-(C * s)) := by
    intro s t hs hst hst₁
    have htb : t ≤ b := le_trans hst₁ ht₁.2
    have has : a < s := lt_of_le_of_lt ht₀I.1 hs
    refine dini_mono_of_lsc (u := fun r => f r * Real.exp (-(C * r))) (α := s) (β := t)
      hst.le ?_ ?_ ?_
    · -- lower semicontinuity of `g` at interior points
      intro z hz η hη
      have hzs : s < z := hz.1
      have hzt : z < t := hz.2
      have hzIoc : z ∈ Ioc a b := ⟨lt_trans has hzs, (lt_of_lt_of_le hzt htb).le⟩
      have hzIco : z ∈ Ico a b := ⟨le_of_lt (lt_trans has hzs), lt_of_lt_of_le hzt htb⟩
      exact lsc_mul_exp (hL z hzIoc) (hRt z hzIco) η hη
    · -- lower semicontinuity of `g` at the right endpoint, from the left
      exact lsc_left_mul_exp (hL t ⟨lt_trans has hst, htb⟩)
    · -- the upper right Dini bound for `g`
      intro z hz ε hε
      have hzs : s ≤ z := hz.1
      have hzt : z < t := hz.2
      have hfz : 0 < f z := hpos z ⟨lt_of_lt_of_le hs hzs, le_of_lt (lt_of_lt_of_le hzt hst₁)⟩
      have hzIco : z ∈ Ico a b :=
        ⟨le_trans has.le hzs, lt_of_lt_of_le hzt htb⟩
      obtain ⟨δ, hδ, hδ'⟩ :=
        local_dini_shift (C := C) (b := b) (t := z) (le_of_lt (lt_of_lt_of_le hzt htb)) hfz
          (fun ε hε => by
            obtain ⟨δ', hδ2, hδ3⟩ := hD z hzIco hfz ε hε
            exact ⟨δ', hδ2, fun h hh hhle _ => hδ3 h hh hhle⟩) ε hε
      exact ⟨δ, hδ, fun h hh hhle hztb => hδ' h hh hhle (le_trans hztb htb)⟩
  -- let `s ↓ t₀` and use upper semicontinuity from the right at `t₀`
  have hfin : ∀ η > 0, f t₁ ≤ η := by
    intro η hη
    set K : ℝ := Real.exp (max 0 (C * (t₁ - t₀))) with hKdef
    have hKpos : 0 < K := Real.exp_pos _
    have hε : 0 < η / K := div_pos hη hKpos
    obtain ⟨δ, hδ, hδ'⟩ := hrusc t₀ ⟨ht₀I.1, lt_of_lt_of_le ht₀lt ht₁.2⟩ (η / K) hε
    have hgap : 0 < t₁ - t₀ := sub_pos.mpr ht₀lt
    set hh : ℝ := min δ (t₁ - t₀) / 2 with hhdef
    have hhpos : 0 < hh := by rw [hhdef]; exact div_pos (lt_min hδ hgap) two_pos
    have hhδ : hh ≤ δ := by
      rw [hhdef]; have := min_le_left δ (t₁ - t₀); linarith
    have hhgap : hh < t₁ - t₀ := by
      rw [hhdef]; have := min_le_right δ (t₁ - t₀); linarith
    have h2 : t₀ < t₀ + hh := by linarith
    have h3 : t₀ + hh < t₁ := by linarith
    have hfnn : 0 ≤ f (t₀ + hh) := le_of_lt (hpos (t₀ + hh) ⟨h2, h3.le⟩)
    have hfs : f (t₀ + hh) ≤ η / K := by
      have h1 := hδ' hh hhpos hhδ
      rwa [hft₀, zero_add] at h1
    have h4 : f t₁ ≤ f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) := by
      have h4' := hkey (t₀ + hh) t₁ h2 h3 le_rfl
      have hmul := mul_le_mul_of_nonneg_right h4' (Real.exp_pos (C * t₁)).le
      have hleft : f t₁ * Real.exp (-(C * t₁)) * Real.exp (C * t₁) = f t₁ := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hright : f (t₀ + hh) * Real.exp (-(C * (t₀ + hh))) * Real.exp (C * t₁)
          = f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) := by
        rw [mul_assoc, ← Real.exp_add,
          show -(C * (t₀ + hh)) + C * t₁ = C * (t₁ - (t₀ + hh)) by ring]
      rwa [hleft, hright] at hmul
    have h5 : Real.exp (C * (t₁ - (t₀ + hh))) ≤ K := by
      rw [hKdef]
      refine Real.exp_le_exp.mpr ?_
      rcases le_total 0 C with hC | hC
      · have h7 : C * (t₁ - (t₀ + hh)) ≤ C * (t₁ - t₀) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
        exact le_trans h7 (le_max_right _ _)
      · have h7 : C * (t₁ - (t₀ + hh)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
        exact le_trans h7 (le_max_left _ _)
    have h6 : f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) ≤ η / K * K :=
      mul_le_mul hfs h5 (Real.exp_pos _).le (div_pos hη hKpos).le
    have h7 : η / K * K = η := div_mul_cancel₀ η hKpos.ne'
    linarith
  have hle0 : f t₁ ≤ 0 := by
    by_contra hcon
    have hpos₁ : 0 < f t₁ := not_le.mp hcon
    have h9 := hfin (f t₁ / 2) (by linarith)
    linarith
  linarith

end Work.Diff.MP
