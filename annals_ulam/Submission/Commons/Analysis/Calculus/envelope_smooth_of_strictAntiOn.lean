import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.Calculus.exists_contDiffAt_eqOn_of_deriv_ne_zero

namespace Commons.Analysis.Calculus

open scoped ContDiff Topology
open Set Filter

/-- If `y` is continuous and strictly antitone on `(0,∞)` with values in `(0,1)`, `us` is a right
inverse of `y` on `(0,1)`, and `F` agrees with `v ∘ y` near `s₀ > 0`, then `v ∘ us` agrees with `F`
near `y s₀`.  This is the crucial "local smoothness descends to the inverse" step. -/
lemma inverse_eventuallyEq {y us v F : ℝ → ℝ} {s₀ : ℝ}
    (hycont : ContinuousOn y (Set.Ioi 0)) (hyanti : StrictAntiOn y (Set.Ioi 0))
    (hym : ∀ σ, 0 < σ → y σ ∈ Set.Ioo (0:ℝ) 1)
    (hs₀ : 0 < s₀)
    (hus : ∀ t, 0 < t → t < 1 → 0 < us t ∧ y (us t) = t)
    (heq : ∀ᶠ σ in 𝓝 s₀, F (y σ) = v σ) :
    (fun t => v (us t)) =ᶠ[𝓝 (y s₀)] F := by
  rw [Metric.eventually_nhds_iff] at heq
  obtain ⟨δ, hδ, hP⟩ := heq
  set δ' := min δ (s₀ / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hlo : 0 < s₀ - δ' := by have := min_le_right δ (s₀/2); linarith
  have hhi : 0 < s₀ + δ' := by linarith
  have hylt : y (s₀ + δ') < y s₀ :=
    hyanti (a := s₀) (b := s₀ + δ') (by simpa using hs₀) (by simpa using hhi) (by linarith)
  have hygt : y s₀ < y (s₀ - δ') :=
    hyanti (a := s₀ - δ') (b := s₀) (by simpa using hlo) (by simpa using hs₀) (by linarith)
  rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨Set.Ioo (y (s₀ + δ')) (y (s₀ - δ')), ?_, ?_⟩
  · exact isOpen_Ioo.mem_nhds ⟨hylt, hygt⟩
  · intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hy0hi : y (s₀ + δ') ∈ Set.Ioo (0:ℝ) 1 := hym _ hhi
    have hy0lo : y (s₀ - δ') ∈ Set.Ioo (0:ℝ) 1 := hym _ hlo
    have ht0 : 0 < t := lt_trans hy0hi.1 ht1
    have ht1' : t < 1 := lt_trans ht2 hy0lo.2
    -- t is in the image of `y` on `(s₀-δ', s₀+δ')`
    have himg : t ∈ y '' Set.Ioo (s₀ - δ') (s₀ + δ') := by
      have hcont : ContinuousOn y (Set.Icc (s₀ - δ') (s₀ + δ')) :=
        hycont.mono (fun x hx => lt_of_lt_of_le hlo hx.1)
      have hmono : StrictAntiOn y (Set.Icc (s₀ - δ') (s₀ + δ')) :=
        hyanti.mono (fun x hx => lt_of_lt_of_le hlo hx.1)
      rw [hcont.image_Ioo_of_strictAntiOn (by linarith) hmono]
      exact ⟨ht1, ht2⟩
    obtain ⟨σ, hσ, hσy⟩ := himg
    have hσpos : 0 < σ := lt_of_lt_of_le hlo hσ.1.le
    have hdist : dist σ s₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    obtain ⟨hustpos, husty⟩ := hus t ht0 ht1'
    have huseq : us t = σ :=
      hyanti.injOn (by simpa using hustpos) (by simpa using hσpos)
        (by rw [husty, hσy])
    rw [huseq, ← hP hdist, hσy]

/-- For `s > 0`, `√(1 - (1/√(1+s²))²) = s/√(1+s²)`. -/
lemma sqrt_one_sub_inv_sqrt_sq (s : ℝ) (hs : 0 < s) :
    Real.sqrt (1 - (1 / Real.sqrt (1 + s ^ 2)) ^ 2) = s / Real.sqrt (1 + s ^ 2) := by
  have hr : 0 < 1 + s ^ 2 := by positivity
  have hsq : (1 / Real.sqrt (1 + s ^ 2)) ^ 2 = 1 / (1 + s ^ 2) := by
    rw [div_pow, one_pow, Real.sq_sqrt hr.le]
  rw [hsq]
  have harg : 1 - 1 / (1 + s ^ 2) = s ^ 2 / (1 + s ^ 2) := by
    field_simp
    ring
  rw [harg, Real.sqrt_div (by positivity : (0:ℝ) ≤ s ^ 2), Real.sqrt_sq (le_of_lt hs)]

theorem envelope_smooth_of_strictAntiOn {ε : ℝ} {h x y : ℝ → ℝ}
    (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hy : ContDiff ℝ (⊤ : ℕ∞) y) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx0 : x 0 = 1) (hy0 : y 0 = 1)
    (hxmem : ∀ s : ℝ, 0 < s → 0 < x s ∧ x s < 1)
    (hymem : ∀ s : ℝ, 0 < s → 0 < y s ∧ y s < 1)
    (hxanti : StrictAntiOn x (Set.Ioi 0)) (hyanti : StrictAntiOn y (Set.Ioi 0))
    (hxder : ∀ s : ℝ, 0 < s → deriv x s < 0)
    (hyder : ∀ s : ℝ, 0 < s → deriv y s < 0)
    (hxsurj : ∀ t : ℝ, 0 < t → t < 1 → ∃ s : ℝ, 0 < s ∧ x s = t)
    (hysurj : ∀ t : ℝ, 0 < t → t < 1 → ∃ s : ℝ, 0 < s ∧ y s = t)
    (hclarge : ∃ c : ℝ, 0 < c ∧ (∀ s : ℝ, c ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2) ∧ h s = 0) ∧
      (∀ s : ℝ, c ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2))) :
    ∃ f : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1) ∧
      Function.support f ⊆ Set.Icc (-1 : ℝ) 1 ∧
      f 1 = 0 ∧ f (-1) = 0 ∧
      (∀ s : ℝ, 0 < s → f (y s) = s * y s + ε * h s) ∧
      (∀ s : ℝ, 0 < s → f (-(x s)) = -(s * (-(x s)) + ε * h s)) := by
  obtain ⟨c, hcpos, hyc, hxc⟩ := hclarge
  -- Chosen inverses of `y` and `x` on `(0,1)`.
  let us : ℝ → ℝ := fun t => if hh : 0 < t ∧ t < 1 then Classical.choose (hysurj t hh.1 hh.2) else 0
  let ux : ℝ → ℝ := fun t => if hh : 0 < t ∧ t < 1 then Classical.choose (hxsurj t hh.1 hh.2) else 0
  have hus : ∀ t (ht0 : 0 < t) (ht1 : t < 1), 0 < us t ∧ y (us t) = t := by
    intro t ht0 ht1
    dsimp only [us]
    rw [dif_pos (show 0 < t ∧ t < 1 from ⟨ht0, ht1⟩)]
    exact Classical.choose_spec (hysurj t ht0 ht1)
  have hux : ∀ t (ht0 : 0 < t) (ht1 : t < 1), 0 < ux t ∧ x (ux t) = t := by
    intro t ht0 ht1
    dsimp only [ux]
    rw [dif_pos (show 0 < t ∧ t < 1 from ⟨ht0, ht1⟩)]
    exact Classical.choose_spec (hxsurj t ht0 ht1)
  have husy : ∀ s, 0 < s → us (y s) = s := by
    intro s hs
    obtain ⟨hypos, hyeq⟩ := hus (y s) (hymem s hs).1 (hymem s hs).2
    exact hyanti.injOn (x₁ := us (y s)) (x₂ := s) (by simpa using hypos) (by simpa using hs) hyeq
  have huxx : ∀ s, 0 < s → ux (x s) = s := by
    intro s hs
    obtain ⟨hxpos, hxeq⟩ := hux (x s) (hxmem s hs).1 (hxmem s hs).2
    exact hxanti.injOn (x₁ := ux (x s)) (x₂ := s) (by simpa using hxpos) (by simpa using hs) hxeq
  -- The two pieces and the target.
  let v : ℝ → ℝ := fun σ => σ * y σ + ε * h σ
  let w : ℝ → ℝ := fun σ => σ * x σ - ε * h σ
  let fy : ℝ → ℝ := fun t => v (us t)
  let gx : ℝ → ℝ := fun t => w (ux t)
  let sqr : ℝ → ℝ := fun t => Real.sqrt (1 - t ^ 2)
  let f : ℝ → ℝ := fun t =>
    if t ∈ Set.Ioo (-1 : ℝ) 1 then (if 0 < t then fy t else if t < 0 then gx (-t) else 1) else 0
  have hvcd : ContDiff ℝ (⊤ : ℕ∞) v := by
    dsimp only [v]
    exact (contDiff_id.mul hy).add (contDiff_const.mul hh)
  have hwcd : ContDiff ℝ (⊤ : ℕ∞) w := by
    dsimp only [w]
    exact (contDiff_id.mul hx).sub (contDiff_const.mul hh)
  have hym : ∀ σ, 0 < σ → y σ ∈ Set.Ioo (0:ℝ) 1 :=
    fun σ hσ => ⟨(hymem σ hσ).1, (hymem σ hσ).2⟩
  have hxm : ∀ σ, 0 < σ → x σ ∈ Set.Ioo (0:ℝ) 1 :=
    fun σ hσ => ⟨(hxmem σ hσ).1, (hxmem σ hσ).2⟩
  have hycont : ContinuousOn y (Set.Ioi 0) := hy.continuous.continuousOn
  have hxcont : ContinuousOn x (Set.Ioi 0) := hx.continuous.continuousOn
  -- Smoothness of the positive-side piece.
  have hfy_smooth : ContDiffOn ℝ (⊤ : ℕ∞) fy (Set.Ioo (0:ℝ) 1) := by
    rw [isOpen_Ioo.contDiffOn_iff]
    intro t ht
    obtain ⟨hustpos, husty⟩ := hus t ht.1 ht.2
    have hyca : ContDiffAt ℝ (⊤ : ℕ∞) y (us t) := hy.contDiffAt
    have hvca : ContDiffAt ℝ (⊤ : ℕ∞) v (us t) := hvcd.contDiffAt
    have hder : deriv y (us t) ≠ 0 := ne_of_lt (hyder (us t) hustpos)
    obtain ⟨F, hF, hFeq⟩ := exists_contDiffAt_eqOn_of_deriv_ne_zero hyca hvca hder
    have heq : fy =ᶠ[𝓝 (y (us t))] F := by
      have h := inverse_eventuallyEq hycont hyanti hym hustpos (fun u hu0 hu1 => hus u hu0 hu1) hFeq
      simpa only [fy] using h
    simpa [husty] using hF.congr_of_eventuallyEq heq
  -- Smoothness of the negative-side piece `gx`.
  have hgx_smooth : ContDiffOn ℝ (⊤ : ℕ∞) gx (Set.Ioo (0:ℝ) 1) := by
    rw [isOpen_Ioo.contDiffOn_iff]
    intro t ht
    obtain ⟨huxtpos, huxty⟩ := hux t ht.1 ht.2
    have hxca : ContDiffAt ℝ (⊤ : ℕ∞) x (ux t) := hx.contDiffAt
    have hwca : ContDiffAt ℝ (⊤ : ℕ∞) w (ux t) := hwcd.contDiffAt
    have hder : deriv x (ux t) ≠ 0 := ne_of_lt (hxder (ux t) huxtpos)
    obtain ⟨F, hF, hFeq⟩ := exists_contDiffAt_eqOn_of_deriv_ne_zero hxca hwca hder
    have heq : gx =ᶠ[𝓝 (x (ux t))] F := by
      have h := inverse_eventuallyEq hxcont hxanti hxm huxtpos (fun u hu0 hu1 => hux u hu0 hu1) hFeq
      simpa only [gx] using h
    simpa [huxty] using hF.congr_of_eventuallyEq heq
  -- The pieces agree with `f` on their ranges.
  have hf_eq_fy : ∀ t, 0 < t → t < 1 → f t = fy t := by
    intro t ht0 ht1
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
    dsimp only [f]
    rw [if_pos htI, if_pos ht0]
  have hf_eq_gx : ∀ t, -1 < t → t < 0 → f t = gx (-t) := by
    intro t ht0 ht1
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ht0, by linarith⟩
    dsimp only [f]
    rw [if_pos htI, if_neg (not_lt.mpr (le_of_lt ht1)), if_pos ht1]
  -- m := min (x c) (y c), a neighbourhood of 0 where everything equals `sqrt (1 - t^2)`.
  set m := min (x c) (y c) with hmdef
  have hm_pos : 0 < m := lt_min (hxmem c hcpos).1 (hymem c hcpos).1
  have hm_lt_one : m < 1 := lt_of_le_of_lt (min_le_right _ _) (hymem c hcpos).2
  have hm_le_xc : m ≤ x c := min_le_left _ _
  have hm_le_yc : m ≤ y c := min_le_right _ _
  -- `sqr` is smooth on `(-m, m)`.
  have hsqr_smooth : ContDiffOn ℝ (⊤ : ℕ∞) sqr (Set.Ioo (-m) m) := by
    have hbig : ContDiffOn ℝ (⊤ : ℕ∞) sqr (Set.Ioo (-1:ℝ) 1) := by
      apply ContDiffOn.sqrt
      · fun_prop
      · intro u hu
        have : u ^ 2 < 1 := by nlinarith [hu.1, hu.2]
        nlinarith [this]
    exact hbig.mono (fun u hu => ⟨by linarith [hm_lt_one, hu.1], by linarith [hm_lt_one, hu.2]⟩)
  -- `f` agrees with `sqr` on `(-m, m)`.
  have hf_eq_sqr : ∀ t ∈ Set.Ioo (-m) m, f t = sqr t := by
    intro t ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · -- t < 0
      rw [hf_eq_gx t (by linarith [ht.1, hm_lt_one]) hlt]
      have ha0 : 0 < -t := by linarith [hlt]
      have ha1 : -t < 1 := by linarith [ht.1, hm_lt_one]
      obtain ⟨huxtpos, huxty⟩ := hux (-t) ha0 ha1
      have hsge : c ≤ ux (-t) := by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : x c < x (ux (-t)) :=
          hxanti (a := ux (-t)) (b := c) (by simpa using huxtpos) (by simpa using hcpos) hcon
        have h2 : -t < x c := lt_of_lt_of_le (by linarith [ht.1]) hm_le_xc
        rw [huxty] at h1
        linarith
      have hxval : x (ux (-t)) = 1 / Real.sqrt (1 + (ux (-t)) ^ 2) := hxc (ux (-t)) hsge
      have hhzero : h (ux (-t)) = 0 := (hyc (ux (-t)) hsge).2
      have hkey : (1:ℝ) - t ^ 2 = 1 - (1 / Real.sqrt (1 + (ux (-t)) ^ 2)) ^ 2 := by
        have ht_eq : t = -(1 / Real.sqrt (1 + (ux (-t)) ^ 2)) := by
          have : -t = 1 / Real.sqrt (1 + (ux (-t)) ^ 2) := by
            conv_lhs => rw [← huxty]
            exact hxval
          linarith
        conv_lhs => rw [ht_eq, neg_sq]
      have hgxval : gx (-t) = (ux (-t)) / Real.sqrt (1 + (ux (-t)) ^ 2) := by
        dsimp only [gx, w]
        rw [hxval, hhzero]
        ring
      have hsqrval : sqr t = (ux (-t)) / Real.sqrt (1 + (ux (-t)) ^ 2) := by
        dsimp only [sqr]
        rw [hkey, sqrt_one_sub_inv_sqrt_sq (ux (-t)) huxtpos]
      rw [hgxval, hsqrval]
    · -- t = 0
      subst heq
      have hf0 : f 0 = 1 := by
        dsimp only [f]
        rw [if_pos (show (0:ℝ) ∈ Set.Ioo (-1) 1 from by norm_num),
            if_neg (lt_irrefl (0:ℝ)), if_neg (lt_irrefl (0:ℝ))]
      rw [hf0]
      dsimp only [sqr]
      norm_num [Real.sqrt_one]
    · -- t > 0
      rw [hf_eq_fy t hgt (by linarith [ht.2, hm_lt_one])]
      obtain ⟨hustpos, husty⟩ := hus t hgt (by linarith [ht.2, hm_lt_one])
      have hsge : c ≤ us t := by
        by_contra hcon
        rw [not_le] at hcon
        have h1 : y c < y (us t) :=
          hyanti (a := us t) (b := c) (by simpa using hustpos) (by simpa using hcpos) hcon
        have h2 : t < y c := lt_of_lt_of_le ht.2 hm_le_yc
        rw [husty] at h1
        linarith
      obtain ⟨hyval, hhzero⟩ := hyc (us t) hsge
      have ht_eq : t = 1 / Real.sqrt (1 + (us t) ^ 2) := by
        conv_lhs => rw [← husty]
        exact hyval
      have hkey : (1:ℝ) - t ^ 2 = 1 - (1 / Real.sqrt (1 + (us t) ^ 2)) ^ 2 := by
        conv_lhs => rw [ht_eq]
      have hfyval : fy t = (us t) / Real.sqrt (1 + (us t) ^ 2) := by
        dsimp only [fy, v]
        rw [hyval, hhzero]
        ring
      have hsqrval : sqr t = (us t) / Real.sqrt (1 + (us t) ^ 2) := by
        dsimp only [sqr]
        rw [hkey, sqrt_one_sub_inv_sqrt_sq (us t) hustpos]
      rw [hfyval, hsqrval]
  have hmid : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-m) m) :=
    hsqr_smooth.congr (fun t ht => hf_eq_sqr t ht)
  -- Smoothness of `f` on `(-1,1)`.
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-1 : ℝ) 1) := by
    rw [isOpen_Ioo.contDiffOn_iff]
    intro t ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · have hfy_at : ContDiffAt ℝ (⊤ : ℕ∞) gx (-t) :=
        hgx_smooth.contDiffAt (isOpen_Ioo.mem_nhds
          (show (-t) ∈ Set.Ioo (0:ℝ) 1 from ⟨by linarith [hlt], by linarith [ht.1]⟩))
      have hfxe : f =ᶠ[𝓝 t] (fun u => gx (-u)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (-1:ℝ) 0 from ⟨ht.1, hlt⟩)]
          with u hu
        exact hf_eq_gx u hu.1 hu.2
      have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => -u) t := by
        simpa using (contDiff_id (n := (⊤:ℕ∞))).neg.contDiffAt (x := t)
      have hcomp : ContDiffAt ℝ (⊤ : ℕ∞) (fun u => gx (-u)) t := hfy_at.comp t hneg
      exact hcomp.congr_of_eventuallyEq hfxe
    · subst heq
      exact hmid.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hm_pos], hm_pos⟩)
    · have hfy_at : ContDiffAt ℝ (⊤ : ℕ∞) fy t :=
        hfy_smooth.contDiffAt (isOpen_Ioo.mem_nhds ⟨hgt, ht.2⟩)
      have hfye : f =ᶠ[𝓝 t] fy := by
        filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (0:ℝ) 1 from ⟨hgt, ht.2⟩)]
          with u hu
        exact hf_eq_fy u hu.1 hu.2
      exact hfy_at.congr_of_eventuallyEq hfye
  refine ⟨f, hf_smooth, ?_, ?_, ?_, ?_, ?_⟩
  · -- support
    intro t ht
    rw [Function.mem_support] at ht
    by_contra hmem
    have hnotI : t ∉ Set.Ioo (-1:ℝ) 1 := fun h => hmem ⟨le_of_lt h.1, le_of_lt h.2⟩
    exact ht (by dsimp only [f]; rw [if_neg hnotI])
  · -- f 1 = 0
    dsimp only [f]
    rw [if_neg (by norm_num : ¬ ((1:ℝ) ∈ Set.Ioo (-1:ℝ) 1))]
  · -- f (-1) = 0
    dsimp only [f]
    rw [if_neg (by norm_num : ¬ ((-1:ℝ) ∈ Set.Ioo (-1:ℝ) 1))]
  · -- positive identity
    intro s hs
    rw [hf_eq_fy (y s) (hymem s hs).1 (hymem s hs).2]
    dsimp only [fy, v]
    rw [husy s hs]
  · -- negative identity
    intro s hs
    have h1 : -1 < -(x s) := by have := (hxmem s hs).2; linarith
    have h2 : -(x s) < 0 := by have := (hxmem s hs).1; linarith
    rw [hf_eq_gx (-(x s)) h1 h2]
    dsimp only [gx, w]
    rw [neg_neg, huxx s hs]
    ring

end Commons.Analysis.Calculus