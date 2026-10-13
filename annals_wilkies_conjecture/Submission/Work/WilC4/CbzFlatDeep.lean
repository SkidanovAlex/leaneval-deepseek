import Mathlib
import Submission.Work.WilC4.CbzAux
import Submission.Work.WilC4.cbz_pigeonhole_segment
import Submission.Work.WilC4.cbz_not_mid_between_of_image

set_option maxHeartbeats 2000000
set_option autoImplicit false
noncomputable section
open Classical Set
namespace Work.WilC4

open Work.WilC4.Route

variable {k : ℕ}

/-- **One flat piece of the doubling ratio (deep-bound version).**  Same as `cbz_flat`, except that
the bound on the doubling ratio is assumed at the *fixed* scale `Γ` instead of at scale `2`.  This
is the form that `deep_ratio_scale_bdd` supplies: the bound at `Γ`-deep points, with the constant
`Γ`.  Since the region `[1/W, W] = [N/M, M/N]` consists of `N`-deep points and `Γ ≤ N`, the ratio
is bounded by `Cbdd` there. -/
theorem cbz_flat_deep {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B) {Γ Cbdd : ℝ} (hΓ : 2 ≤ Γ) (hCbdd_pos : 0 < Cbdd)
    (hbdd : ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x → IsDeepR B c Γ x → RatW Y c x w → |w| ≤ Cbdd)
    {c : Fin k → ℝ} {x M : ℝ} {N m : ℕ} (hNΓ : Γ ≤ (N : ℝ)) (hN2 : 2 ≤ N) (hm : 0 < m)
    (hx : 0 < x) (hM2 : 2 ≤ M)
    (hCm : 2 * (N : ℝ) * Cbdd ≤ (m : ℝ)) (hwm : (N : ℝ) ^ (2 * m) ≤ M / (N : ℝ))
    (hdeep : IsDeepR B c M x) (havoid : CbzAvoid Y E M c x) (hmono : CbzMono Y M c x)
    {w : ℝ} (hw : w = ratioY Y c x) (mb sb : Bool)
    (hMB : mb = decide (MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M))) :
    ∃ y lam : ℝ, ((N : ℝ) / M ≤ y ∧ y ≤ M / (N : ℝ)) ∧
      lam = ratioY Y c (x * y) ∧ (0 < lam ∧ lam ≤ Cbdd) ∧
      ((sb = true ∧ w ≤ lam) ∨ (sb = false ∧ lam ≤ w)) ∧
      (∀ s : ℝ, y / (N : ℝ) ≤ s → s ≤ (N : ℝ) * y →
        |ratioY Y c (x * s) - lam| ≤ 1 / (2 * (N : ℝ))) ∧
      (∀ m' ∈ Mid E, ¬ (min w lam < m' ∧ m' < max w lam)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hMpos : 0 < M := by linarith
  set W : ℝ := M / (N : ℝ) with hWdef
  have hWpos : 0 < W := by rw [hWdef]; positivity
  have hWgt1 : 1 < W := by
    have h1 : (2 : ℝ) ^ (2 * m) ≤ W := by
      rw [hWdef]
      calc (2 : ℝ) ^ (2 * m) ≤ (N : ℝ) ^ (2 * m) :=
            pow_le_pow_left₀ (by norm_num) hNge2 _
        _ ≤ M / (N : ℝ) := hwm
    have h2 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hWle1 : 1 / W ≤ 1 := by
    rw [div_le_iff₀ hWpos]; linarith [hWgt1]
  have hWlt1 : 1 / W < 1 := by
    rw [div_lt_iff₀ hWpos]; linarith [hWgt1]
  have hWinv : 1 / W = (N : ℝ) / M := by
    rw [hWdef, one_div]; rw [inv_div]
  have hδ : Cbdd / (m : ℝ) ≤ 1 / (2 * (N : ℝ)) := by
    rw [div_le_iff₀ (by exact_mod_cast hm : (0 : ℝ) < (m : ℝ))]
    rw [show (1 : ℝ) / (2 * (N : ℝ)) * (m : ℝ) = (m : ℝ) / (2 * (N : ℝ)) by ring]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
    nlinarith [hCm]
  have hwidthW : (N : ℝ) ^ 2 ≤ W ^ ((1 : ℝ) / (m : ℝ)) :=
    cbz_rpow_inv (N := N) (m := m) (W := W) (by omega : 0 < N) hm hwm
  -- The ratio is bounded on the window `[1/W, W]`.
  have hbnd_region : ∀ t ∈ Set.Icc (1 / W) W, 0 < ratioY Y c (x * t) ∧ ratioY Y c (x * t) ≤ Cbdd := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht_lo : (N : ℝ) / M ≤ t := by
      have h : 1 / W = (N : ℝ) / M := hWinv
      linarith [h, ht1]
    have ht_hi : t ≤ M / (N : ℝ) := by
      have h : W = M / (N : ℝ) := hWdef
      linarith [h, ht2]
    have htpos : 0 < t := lt_of_lt_of_le (div_pos hNpos hMpos) ht_lo
    have hzpos : 0 < x * t := mul_pos hx htpos
    have ht1' : 2 * x / M ≤ x * t := by
      have h : (2 : ℝ) / M ≤ t := by
        rw [div_le_iff₀ hMpos] at ht_lo ⊢
        linarith [ht_lo, hNge2]
      calc 2 * x / M = x * (2 / M) := by ring
        _ ≤ x * t := mul_le_mul_of_nonneg_left h (le_of_lt hx)
    have ht2' : x * t ≤ M * x / 2 := by
      have h : t * (N : ℝ) ≤ M := by
        rw [le_div_iff₀ hNpos] at ht_hi; exact ht_hi
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h, hx, htpos, hMpos, hNge2]
    have hdeepG : IsDeepR B c Γ (x * t) := by
      -- the region `[N/M, M/N]` consists of `N`-deep points, and `N ≥ Γ`
      have htM : (N : ℝ) ≤ t * M := (div_le_iff₀ hMpos).mp ht_lo
      have htN : t * (N : ℝ) ≤ M := (le_div_iff₀ hNpos).mp ht_hi
      intro b hb hb'
      refine hdeep b hb ⟨?_, ?_⟩
      · have h1 : x / (2 * M) ≤ (x * t) / (2 * Γ) := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)
            (by positivity : (0 : ℝ) < 2 * Γ)]
          nlinarith [htM, hNΓ, hx, hΓ, htpos]
        linarith [hb'.1, h1]
      · have h2 : 2 * Γ * (x * t) ≤ 2 * M * x := by
          nlinarith [htN, hNΓ, hx, htpos, hΓ]
        linarith [hb'.2, h2]
    have hzlo : x / (2 * M) < x * t := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
      have h := ht1'
      rw [div_le_iff₀ hMpos] at h
      nlinarith [h, hx]
    have hzhi : x * t < M * x := by
      have h := ht2'
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
      nlinarith [h, hx, hMpos]
    have hrat2 : RatW Y c (x * t) (ratioY Y c (x * t)) :=
      cbz_ratW_ratioY_of_deep hfun hgf (by linarith : (1 : ℝ) < M) hx hdeep ⟨hzlo, hzhi⟩
    have hb := hbdd c (x * t) (ratioY Y c (x * t)) hzpos hdeepG hrat2
    have hpos := cbz_ratW_pos hfun hgf hΓ hzpos hdeepG hrat2
    exact ⟨hpos, le_of_abs_le hb⟩
  -- No midpoint of `E` lies strictly between `w` and `ratioY Y c (x y)` for `y` in the window.
  have hnoMid : ∀ y ∈ Set.Icc (1 / W) W,
      ∀ m' ∈ Mid E, ¬ (min w (ratioY Y c (x * y)) < m' ∧ m' < max w (ratioY Y c (x * y))) := by
    intro y hy
    have h1Wle1' : 1 / W ≤ 1 := hWle1
    obtain ⟨hy1, hy2⟩ := hy
    have hcont : ContinuousOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc (min 1 y) (max 1 y)) := by
      have hcontR : ContinuousOn (fun t : ℝ => ratioY Y c t) (Set.Ioo (x / (2 * M)) (M * x)) :=
        cbz_ratioY_cont hgf (by linarith : 1 ≤ M) hx hdeep
      have hlin : ContinuousOn (fun s : ℝ => x * s) (Set.Icc (min 1 y) (max 1 y)) :=
        (continuous_const.mul continuous_id).continuousOn
      have hseg : Set.Icc (min 1 y) (max 1 y) ⊆ Set.Icc (1 / W) W :=
        fun s hs => ⟨le_trans (le_min h1Wle1' hy1) hs.1,
          le_trans hs.2 (max_le (le_of_lt hWgt1) hy2)⟩
      have hmap : Set.MapsTo (fun s : ℝ => x * s) (Set.Icc (min 1 y) (max 1 y))
          (Set.Ioo (x / (2 * M)) (M * x)) := by
        intro s hs
        obtain ⟨hs1, hs2⟩ := hseg hs
        have hs1' : (N : ℝ) / M ≤ s := by linarith [hWinv, hs1]
        have hs2' : s ≤ M / (N : ℝ) := by linarith [hWdef, hs2]
        have hspos : 0 < s := lt_of_lt_of_le (div_pos hNpos hMpos) hs1'
        refine ⟨?_, ?_⟩
        · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
          rw [div_le_iff₀ hMpos] at hs1'
          nlinarith [hs1', hx, hNge2, hMpos]
        · show x * s < M * x
          have h := hs2'
          rw [le_div_iff₀ hNpos] at h
          have hsle : s * 2 ≤ M := by nlinarith [h, hspos, hNge2]
          have hmul := mul_le_mul_of_nonneg_left hsle (le_of_lt hx)
          nlinarith [hmul, hx, hMpos, hspos]
      exact hcontR.comp hlin hmap
    have havoid' : ∀ s ∈ Set.Icc (min 1 y) (max 1 y), ratioY Y c (x * s) ∉ Mid E := by
      intro s hs
      have hseg : Set.Icc (min 1 y) (max 1 y) ⊆ Set.Icc (1 / W) W :=
        fun s hs => ⟨le_trans (le_min h1Wle1' hy1) hs.1,
          le_trans hs.2 (max_le (le_of_lt hWgt1) hy2)⟩
      obtain ⟨hs1, hs2⟩ := hseg hs
      have hs1' : (N : ℝ) / M ≤ s := by linarith [hWinv, hs1]
      have hs2' : s ≤ M / (N : ℝ) := by linarith [hWdef, hs2]
      have hspos : 0 < s := lt_of_lt_of_le (div_pos hNpos hMpos) hs1'
      have hszlo : x / (2 * M) < x * s := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
        rw [div_le_iff₀ hMpos] at hs1'
        nlinarith [hs1', hx, hNge2, hMpos]
      have hszhi : x * s < M * x := by
        have h := hs2'
        rw [le_div_iff₀ hNpos] at h
        have hsle : s * 2 ≤ M := by nlinarith [h, hspos, hNge2]
        have hmul := mul_le_mul_of_nonneg_left hsle (le_of_lt hx)
        nlinarith [hmul, hx, hMpos, hspos]
      have hrat : RatW Y c (x * s) (ratioY Y c (x * s)) :=
        cbz_ratW_ratioY_of_deep hfun hgf (by linarith : (1 : ℝ) < M) hx hdeep ⟨hszlo, hszhi⟩
      exact havoid (x * s) ⟨hszlo, by nlinarith [hszhi, hx, hMpos]⟩ (ratioY Y c (x * s)) hrat
    have hmain := cbz_not_mid_between_of_image (E := E) (g := fun s => ratioY Y c (x * s))
      (a := min 1 y) (b := max 1 y) (le_trans (min_le_left _ _) (le_max_left _ _)) hcont havoid'
    rcases le_total y 1 with hyy | hyy
    · have hmin : min (1 : ℝ) y = y := min_eq_right hyy
      have hmax : max (1 : ℝ) y = 1 := max_eq_left hyy
      have hga : ratioY Y c (x * min 1 y) = ratioY Y c (x * y) := by rw [hmin]
      have hgb : ratioY Y c (x * max 1 y) = w := by rw [hmax, mul_one, ← hw]
      intro m' hm' hc
      exact hmain m' hm' (by rw [hga, hgb]; exact cbz_between_comm hc)
    · have hmin : min (1 : ℝ) y = 1 := min_eq_left hyy
      have hmax : max (1 : ℝ) y = y := max_eq_right hyy
      have hga : ratioY Y c (x * min 1 y) = w := by rw [hmin, mul_one, ← hw]
      have hgb : ratioY Y c (x * max 1 y) = ratioY Y c (x * y) := by rw [hmax]
      intro m' hm' hc
      exact hmain m' hm' (by rw [hga, hgb]; exact hc)
  -- The monotonicity and deviation types.
  have hmono_fact : (mb = true → MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M)) ∧
      (mb = false → AntitoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M)) := by
    constructor
    · intro h
      have h3 : decide (MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M)) = true := by
        rw [← hMB]; exact h
      exact of_decide_eq_true h3
    · intro h
      have h3 : decide (MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Ioo (1 / M) M)) = false := by
        rw [← hMB]; exact h
      rw [decide_eq_false_iff_not] at h3
      rcases hmono with hm' | ha'
      · exact absurd hm' h3
      · exact ha'
  have hg2_one : ratioY Y c (x * 1) = w := by rw [mul_one, ← hw]
  have hsubR : Set.Icc (1 : ℝ) W ⊆ Set.Ioo (1 / M) M := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ hMpos]
      nlinarith [hs.1, hM2]
    · calc s ≤ W := hs.2
        _ = M / (N : ℝ) := hWdef
        _ < M := by
            rw [div_lt_iff₀ hNpos]
            nlinarith [hMpos, hNge2]
  have hsubL : Set.Icc (1 / W) (1 : ℝ) ⊆ Set.Ioo (1 / M) M := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have h : (N : ℝ) / M ≤ s := by linarith [hWinv, hs.1]
      rw [div_lt_iff₀ hMpos]
      rw [div_le_iff₀ hMpos] at h
      nlinarith [h, hNge2]
    · linarith [hs.2, hM2]
  have hsubRIW : Set.Icc (1 : ℝ) W ⊆ Set.Icc (1 / W) W :=
    fun s hs => ⟨le_trans hWle1 hs.1, hs.2⟩
  have hsubLIW : Set.Icc (1 / W) (1 : ℝ) ⊆ Set.Icc (1 / W) W :=
    fun s hs => ⟨hs.1, le_trans hs.2 (le_of_lt hWgt1)⟩
  have step : ∀ (α β : ℝ), 0 < α → α < β → Set.Icc α β ⊆ Set.Icc (1 / W) W →
      (MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc α β) ∨
        AntitoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc α β)) →
      (N : ℝ) ^ 2 ≤ (β / α) ^ ((1 : ℝ) / (m : ℝ)) →
      ∃ y : ℝ, α ≤ y ∧ y ≤ β ∧
        ∀ s : ℝ, y / (N : ℝ) ≤ s → s ≤ (N : ℝ) * y →
          |ratioY Y c (x * s) - ratioY Y c (x * y)| ≤ 1 / (2 * (N : ℝ)) := by
    intro α β hα hαβ hsub hmono' hwidth
    have hbdd' : ∀ t ∈ Set.Icc α β, 0 < ratioY Y c (x * t) ∧ ratioY Y c (x * t) ≤ Cbdd :=
      fun t ht => hbnd_region t (hsub ht)
    exact cbz_pigeonhole_segment hα hαβ hCbdd_pos hmono' hbdd' hm hδ (by omega : 0 < N) hwidth
  cases mb <;> cases sb
  · -- antitone & lower: region [1, W]
    have hmonoR : AntitoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc (1 : ℝ) W) :=
      (hmono_fact.2 rfl).mono hsubR
    obtain ⟨y, hy1, hy2, hflat⟩ := step 1 W one_pos hWgt1 hsubRIW (Or.inr hmonoR)
      (by rw [div_one]; exact hwidthW)
    have hyW : y ∈ Set.Icc (1 / W) W := ⟨le_trans hWle1 hy1, hy2⟩
    refine ⟨y, ratioY Y c (x * y),
      ⟨by rw [← hWinv]; exact le_trans hWle1 hy1, hy2⟩,
      rfl, ⟨(hbnd_region y hyW).1, (hbnd_region y hyW).2⟩,
      Or.inr ⟨rfl, ?_⟩, hflat, hnoMid y hyW⟩
    have hmon : ratioY Y c (x * y) ≤ ratioY Y c (x * 1) :=
      hmonoR ⟨le_refl 1, le_of_lt hWgt1⟩ ⟨hy1, hy2⟩ hy1
    rwa [hg2_one] at hmon
  · -- antitone & upper: region [1/W, 1]
    have hmonoR : AntitoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc (1 / W) (1 : ℝ)) :=
      (hmono_fact.2 rfl).mono hsubL
    obtain ⟨y, hy1, hy2, hflat⟩ := step (1 / W) 1 (by positivity) hWlt1 hsubLIW (Or.inr hmonoR)
      (by rw [one_div_div, div_one]; exact hwidthW)
    have hyW : y ∈ Set.Icc (1 / W) W := ⟨hy1, le_trans hy2 (le_of_lt hWgt1)⟩
    refine ⟨y, ratioY Y c (x * y),
      ⟨by rw [← hWinv]; exact hy1, le_trans hy2 (le_of_lt hWgt1)⟩,
      rfl, ⟨(hbnd_region y hyW).1, (hbnd_region y hyW).2⟩,
      Or.inl ⟨rfl, ?_⟩, hflat, hnoMid y hyW⟩
    have hmon : ratioY Y c (x * 1) ≤ ratioY Y c (x * y) :=
      hmonoR ⟨hy1, hy2⟩ ⟨hWle1, le_refl 1⟩ hy2
    rwa [hg2_one] at hmon
  · -- monotone & lower: region [1/W, 1]
    have hmonoR : MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc (1 / W) (1 : ℝ)) :=
      (hmono_fact.1 rfl).mono hsubL
    obtain ⟨y, hy1, hy2, hflat⟩ := step (1 / W) 1 (by positivity) hWlt1 hsubLIW (Or.inl hmonoR)
      (by rw [one_div_div, div_one]; exact hwidthW)
    have hyW : y ∈ Set.Icc (1 / W) W := ⟨hy1, le_trans hy2 (le_of_lt hWgt1)⟩
    refine ⟨y, ratioY Y c (x * y),
      ⟨by rw [← hWinv]; exact hy1, le_trans hy2 (le_of_lt hWgt1)⟩,
      rfl, ⟨(hbnd_region y hyW).1, (hbnd_region y hyW).2⟩,
      Or.inr ⟨rfl, ?_⟩, hflat, hnoMid y hyW⟩
    have hmon : ratioY Y c (x * y) ≤ ratioY Y c (x * 1) :=
      hmonoR ⟨hy1, hy2⟩ ⟨hWle1, le_refl 1⟩ hy2
    rwa [hg2_one] at hmon
  · -- monotone & upper: region [1, W]
    have hmonoR : MonotoneOn (fun s : ℝ => ratioY Y c (x * s)) (Set.Icc (1 : ℝ) W) :=
      (hmono_fact.1 rfl).mono hsubR
    obtain ⟨y, hy1, hy2, hflat⟩ := step 1 W one_pos hWgt1 hsubRIW (Or.inl hmonoR)
      (by rw [div_one]; exact hwidthW)
    have hyW : y ∈ Set.Icc (1 / W) W := ⟨le_trans hWle1 hy1, hy2⟩
    refine ⟨y, ratioY Y c (x * y),
      ⟨by rw [← hWinv]; exact le_trans hWle1 hy1, hy2⟩,
      rfl, ⟨(hbnd_region y hyW).1, (hbnd_region y hyW).2⟩,
      Or.inl ⟨rfl, ?_⟩, hflat, hnoMid y hyW⟩
    have hmon : ratioY Y c (x * 1) ≤ ratioY Y c (x * y) :=
      hmonoR ⟨le_refl 1, le_of_lt hWgt1⟩ ⟨hy1, hy2⟩ hy1
    rwa [hg2_one] at hmon

end Work.WilC4
