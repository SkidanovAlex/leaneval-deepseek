import Mathlib
import Submission.Work.Diff.Alg.Pinch.le_of_dini_right

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dini's "first exit" argument

`Work.Diff.MP.dini_first_exit`: a continuous nonnegative function `f` on `[a,b]` with `f a = 0`
which satisfies the *upper right Dini bound* `f (t+h) ≤ f t + h * (C * f t + ε)` at every point
`t` with `f t > 0` must vanish identically.

The proof is the classical "first exit" argument.  Assume `f t₁ > 0`.  Let `t₀` be the last zero
of `f` before `t₁` (`exists_last_zero`); then `f > 0` on `(t₀, t₁]`, so the Dini bound is available
on all of `(t₀, t₁)`.  Rewriting it for the "rotated" function `u s = f s * exp (-(C*s))`
(`local_dini_shift`) turns it into the quantitative right-Dini condition `D⁺u ≤ 0`, and Dini's
theorem (`le_of_dini_right_open`, an open-interval variant of the existing
`Work.Diff.Alg.Pinch.le_of_dini_right`) gives `u t₁ ≤ u t₀ = 0`, contradicting `u t₁ > 0`.
-/

namespace Work.Diff.MP

open Set

/-- **The last zero.**  If `f` is continuous on `Icc a t`, vanishes at `a` but not at `t`, then
there is a last zero `t₀` of `f` in `Icc a t`, and `f` has no zero strictly between `t₀` and `t`. -/
theorem exists_last_zero {f : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hcont : ContinuousOn f (Icc a t)) (ha : f a = 0) (ht : f t ≠ 0) :
    ∃ t₀, t₀ ∈ Icc a t ∧ t₀ < t ∧ f t₀ = 0 ∧ ∀ s ∈ Ioo t₀ t, f s ≠ 0 := by
  let Z : Set ℝ := Icc a t ∩ f ⁻¹' ({0} : Set ℝ)
  have haZ : a ∈ Z := ⟨⟨le_rfl, hat⟩, by simpa using ha⟩
  have hZclosed : IsClosed Z :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := ⟨a, haZ⟩
  have hZbdd : BddAbove Z := ⟨t, by rintro x ⟨hx, -⟩; exact hx.2⟩
  have hsup : sSup Z ∈ Z := hZclosed.csSup_mem hZne hZbdd
  have hsup' : f (sSup Z) = 0 := by simpa using hsup.2
  have hle : sSup Z ≤ t := csSup_le hZne (by rintro x ⟨hx, -⟩; exact hx.2)
  refine ⟨sSup Z, hsup.1, lt_of_le_of_ne hle ?_, hsup', ?_⟩
  · intro heq
    exact ht (by rw [← heq]; exact hsup')
  · intro s hs hfs
    have hsZ : s ∈ Z := by
      refine ⟨⟨?_, hs.2.le⟩, ?_⟩
      · have ha_le : a ≤ sSup Z := le_csSup hZbdd haZ
        linarith [hs.1]
      · simpa using hfs
    have hle2 : s ≤ sSup Z := le_csSup hZbdd hsZ
    exact absurd hs.1 (not_lt.mpr hle2)

/-- **Rotating the Dini bound by `exp (-(C*s))`.**  If `f t > 0` and the upper right Dini bound
`f (t+h) ≤ f t + h * (C * f t + ε)` holds for all small `h ≥ 0` with `t + h ≤ b`, then the same
kind of bound (with the same `ε`) holds for `u s = f s * exp (-(C*s))` at `t`. -/
theorem local_dini_shift {f : ℝ → ℝ} {C t b : ℝ} (htb : t ≤ b) (hft : 0 < f t)
    (hD : ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
        f (t + h) ≤ f t + h * (C * f t + ε)) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      f (t + h) * Real.exp (-(C * (t + h))) ≤ f t * Real.exp (-(C * t)) + ε * h := by
  -- a positive bound for `exp (-(C*s))` on `[t,b]`
  have hKexists : ∃ K > 0, ∀ s ∈ Icc t b, Real.exp (-(C * s)) ≤ K := by
    refine ⟨max (Real.exp (-(C * t))) (Real.exp (-(C * b))),
      lt_max_iff.mpr (Or.inl (Real.exp_pos _)), ?_⟩
    intro s hs
    by_cases hC : 0 ≤ C
    · have h1 : -(C * s) ≤ -(C * t) := by nlinarith [hs.1, hC]
      exact le_trans (Real.exp_le_exp.mpr h1) (le_max_left _ _)
    · have hC' : C ≤ 0 := le_of_lt (not_le.mp hC)
      have h1 : -(C * s) ≤ -(C * b) := by nlinarith [hs.2, hC']
      exact le_trans (Real.exp_le_exp.mpr h1) (le_max_right _ _)
  obtain ⟨K, hKpos, hKb⟩ := hKexists
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hD (ε / K) (by positivity)
  refine ⟨δ, hδ, fun h hh hhle hth => ?_⟩
  have h1 : f (t + h) ≤ f t + h * (C * f t + ε / K) := hδ' h hh hhle hth
  have h2 : Real.exp (-(C * (t + h))) ≤ K := hKb (t + h) ⟨by linarith, hth⟩
  have h3 : Real.exp (-(C * (t + h))) = Real.exp (-(C * t)) * Real.exp (-(C * h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (-(C * h)) * (1 + C * h) ≤ 1 := by
    have h5 : Real.exp (-(C * h)) * (1 + C * h) ≤
        Real.exp (-(C * h)) * Real.exp (C * h) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (C * h)])
        (Real.exp_pos _).le
    have h6 : Real.exp (-(C * h)) * Real.exp (C * h) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linarith
  have hAX : (0 : ℝ) ≤ f t * Real.exp (-(C * t)) := (mul_pos hft (Real.exp_pos _)).le
  have expand : (f t + h * (C * f t + ε / K)) * Real.exp (-(C * (t + h)))
      = f t * Real.exp (-(C * t)) * (Real.exp (-(C * h)) * (1 + C * h))
        + h * (ε / K) * Real.exp (-(C * (t + h))) := by
    rw [h3]; ring
  have hle1 : f t * Real.exp (-(C * t)) * (Real.exp (-(C * h)) * (1 + C * h))
      ≤ f t * Real.exp (-(C * t)) := by
    simpa using mul_le_mul_of_nonneg_left h4 hAX
  have hle2 : h * (ε / K) * Real.exp (-(C * (t + h))) ≤ h * (ε / K) * K :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hle3 : h * (ε / K) * K = ε * h := by
    calc h * (ε / K) * K = (ε / K) * K * h := by ring
      _ = ε * h := by rw [div_mul_cancel₀ ε hKpos.ne']
  calc f (t + h) * Real.exp (-(C * (t + h)))
      ≤ (f t + h * (C * f t + ε / K)) * Real.exp (-(C * (t + h))) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = f t * Real.exp (-(C * t)) * (Real.exp (-(C * h)) * (1 + C * h))
        + h * (ε / K) * Real.exp (-(C * (t + h))) := expand
    _ ≤ f t * Real.exp (-(C * t)) + h * (ε / K) * K := by linarith [hle1, hle2]
    _ = f t * Real.exp (-(C * t)) + ε * h := by rw [hle3]

/-- **Dini's theorem, open-interval form.**  A function continuous on `[α,β]` whose upper right
Dini derivative is non-positive at every point of the *open* interval `(α,β)` is non-increasing. -/
theorem le_of_dini_right_open {u : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hu : ContinuousOn u (Icc α β))
    (hD : ∀ t ∈ Ioo α β, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
      u (t + h) ≤ u t + ε * h) :
    u β ≤ u α := by
  rcases eq_or_lt_of_le hαβ with heq | hlt
  · rw [← heq]
  · -- the claim at every interior point
    have key : ∀ η : ℝ, α < η → η < β → u β ≤ u η := by
      intro η hαη hηβ
      refine Work.Diff.Alg.Pinch.le_of_dini_right u hηβ.le (hu.mono ?_) ?_
      · exact Set.Icc_subset_Icc hαη.le le_rfl
      · intro t ht ε hε
        exact hD t ⟨lt_of_lt_of_le hαη ht.1, ht.2⟩ ε hε
    have hβsub : 0 < β - α := sub_pos.mpr hlt
    have hnhds : (Iio (β - α)) ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hβsub)
    have htend : Filter.Tendsto (fun η : ℝ => u (α + η)) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (u α)) := by
      have hcw : ContinuousWithinAt u (Icc α β) α := hu.continuousWithinAt ⟨le_rfl, hαβ⟩
      refine hcw.tendsto.comp ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h2 : Filter.Tendsto (fun η : ℝ => α + η) (nhds (0 : ℝ)) (nhds α) := by
          have hc : Continuous fun η : ℝ => α + η := by fun_prop
          simpa using hc.tendsto (0 : ℝ)
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin, hnhds] with η hη hlt'
        have h0 : (0 : ℝ) < η := hη
        have h1 : η < β - α := hlt'
        exact ⟨by linarith, by linarith⟩
    have hev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0), u β ≤ u (α + η) := by
      filter_upwards [self_mem_nhdsWithin, hnhds] with η hη hlt'
      have h0 : (0 : ℝ) < η := hη
      have h1 : η < β - α := hlt'
      exact key (α + η) (by linarith) (by linarith)
    exact ge_of_tendsto htend hev

/-- **Dini's first-exit lemma.**  A continuous nonnegative `f` on `[a,b]` with `f a = 0` which
satisfies the upper right Dini bound `f (t+h) ≤ f t + h * (C * f t + ε)` at every `t ∈ [a,b)`
with `f t > 0` must vanish identically. -/
theorem dini_first_exit {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t) (ha : f a = 0)
    (hD : ∀ t ∈ Ico a b, 0 < f t → ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      f (t + h) ≤ f t + h * (C * f t + ε)) :
    ∀ t ∈ Icc a b, f t = 0 := by
  intro t₁ ht₁
  by_contra hfne
  have hft₁ : 0 < f t₁ := lt_of_le_of_ne (hnonneg t₁ ht₁) (Ne.symm hfne)
  -- the last zero of `f` before `t₁`
  obtain ⟨t₀, ht₀mem, ht₀lt, ht₀zero, ht₀pos⟩ :=
    exists_last_zero ht₁.1 (hcont.mono (Set.Icc_subset_Icc le_rfl ht₁.2)) ha hfne
  -- the rotated function and its Dini bound on `(t₀, t₁)`
  have hucont : ContinuousOn (fun s : ℝ => f s * Real.exp (-(C * s))) (Icc t₀ t₁) :=
    (hcont.mono (Set.Icc_subset_Icc ht₀mem.1 ht₁.2)).mul
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(C * s))).continuousOn)
  have hloc : ∀ t ∈ Ioo t₀ t₁, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
      f (t + h) * Real.exp (-(C * (t + h))) ≤ f t * Real.exp (-(C * t)) + ε * h := by
    intro t ht ε hε
    have htIcc : t ∈ Icc a b := ⟨le_trans ht₀mem.1 ht.1.le, le_trans ht.2.le ht₁.2⟩
    have hft : 0 < f t := lt_of_le_of_ne (hnonneg t htIcc) (Ne.symm (ht₀pos t ht))
    have htIco : t ∈ Ico a b := ⟨htIcc.1, lt_of_lt_of_le ht.2 ht₁.2⟩
    obtain ⟨δ, hδ, hδ'⟩ :=
      local_dini_shift (le_trans ht.2.le ht₁.2) hft (hD t htIco hft) ε hε
    refine ⟨min δ ((t₁ - t) / 2), lt_min hδ (by linarith [ht.2]), ?_⟩
    intro h hh hhle
    refine hδ' h hh (le_trans hhle (min_le_left _ _)) ?_
    have hmin := min_le_right δ ((t₁ - t) / 2)
    linarith [ht.2, ht₁.2, hmin]
  have hfin : f t₁ * Real.exp (-(C * t₁)) ≤ f t₀ * Real.exp (-(C * t₀)) :=
    le_of_dini_right_open ht₀lt.le hucont hloc
  have hzero : f t₀ * Real.exp (-(C * t₀)) = 0 := by rw [ht₀zero, zero_mul]
  have hpos : 0 < f t₁ * Real.exp (-(C * t₁)) := mul_pos hft₁ (Real.exp_pos _)
  rw [hzero] at hfin
  linarith

end Work.Diff.MP
