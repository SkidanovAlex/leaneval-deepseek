import Mathlib.Analysis.ODE.ExistUnique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology NNReal
open Metric

theorem exists_extension_of_tendsto_atRight_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {L : NNReal} (hf : LipschitzWith L f)
    {a b : ℝ} (hab : a < b) {z : ℝ → E} {l : E}
    (hz : ∀ t ∈ Set.Ioo a b, HasDerivAt z (f (z t)) t)
    (hlim : Filter.Tendsto z (nhdsWithin b (Set.Iio b)) (nhds l)) :
    ∃ δ > (0 : ℝ), ∃ w : ℝ → E, (∀ t ∈ Set.Ioo a (b + δ), HasDerivAt w (f (w t)) t) ∧
      Set.EqOn w z (Set.Ioo a b) := by
  classical
  -- ## Local existence at `b` from the global Lipschitz hypothesis
  set L' : ℝ≥0 := ‖f l‖₊ + L with hL'def
  have hL' : (L' : ℝ) = ‖f l‖ + (L : ℝ) := by simp [hL'def]
  set ε : ℝ := (1 / 2) / ((L' : ℝ) + 1) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hmul : (L' : ℝ) * ε ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < (L' : ℝ) + 1 := by positivity
    have hle : (L' : ℝ) / ((L' : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    calc (L' : ℝ) * ε
        = (1 / 2) * ((L' : ℝ) / ((L' : ℝ) + 1)) := by rw [hεdef]; ring
      _ ≤ (1 / 2) * 1 := by gcongr
      _ = 1 / 2 := by ring
  have hbLip : ∀ x ∈ closedBall l (1 : ℝ), ‖f x‖ ≤ (L' : ℝ) := by
    intro x hx
    rw [hL']
    have h1 : ‖f x - f l‖ ≤ (L : ℝ) * ‖x - l‖ := by
      simpa [dist_eq_norm] using hf.dist_le_mul x l
    have h2 : ‖x - l‖ ≤ 1 := by
      rw [mem_closedBall_iff_norm] at hx; exact hx
    calc ‖f x‖ ≤ ‖f l‖ + ‖f x - f l‖ := by
          calc ‖f x‖ = ‖(f x - f l) + f l‖ := by rw [sub_add_cancel]
            _ ≤ ‖f x - f l‖ + ‖f l‖ := norm_add_le _ _
            _ = ‖f l‖ + ‖f x - f l‖ := by ring
      _ ≤ ‖f l‖ + (L : ℝ) * ‖x - l‖ := by gcongr
      _ ≤ ‖f l‖ + (L : ℝ) * 1 := by gcongr
      _ = ‖f l‖ + (L : ℝ) := by ring
  have hPL : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := b - ε) (tmax := b + ε) (t₀ := ⟨b, ⟨by linarith, by linarith⟩⟩)
      l (1 : ℝ≥0) (1 / 2 : ℝ≥0) L' L := by
    apply IsPicardLindelof.of_time_independent
    · intro x hx; exact hbLip x hx
    · exact hf.lipschitzOnWith
    · simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
      have h2 : ((1 : ℝ≥0) - (1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h2]; exact hmul
  obtain ⟨α, hαb, hαderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
  -- ## Gluing `z` and `α` at `b`
  let w : ℝ → E := fun t => if t < b then z t else α t
  have hwb : w b = l := by simp [w, hαb]
  have hwz : ∀ t, t < b → w =ᶠ[𝓝 t] z := by
    intro t ht
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    simp only [Set.mem_Iio] at hs
    simp only [w, if_pos hs]
  have hwα : ∀ t, b < t → w =ᶠ[𝓝 t] α := by
    intro t ht
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp only [Set.mem_Ioi] at hs
    simp only [w, if_neg (not_lt.mpr (le_of_lt hs))]
  refine ⟨ε, hε, w, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with hlt | heq | hgt
    · -- `t < b`
      have h := (hz t ⟨ht.1, hlt⟩).congr_of_eventuallyEq (hwz t hlt)
      have hwt : w t = z t := by simp only [w, if_pos hlt]
      rw [← hwt] at h
      exact h
    · -- `t = b`
      rw [heq]
      have hsub : Set.Ioo b (b + ε) ⊆ Set.Icc (b - ε) (b + ε) :=
        fun s hs => ⟨by linarith [hs.1], le_of_lt hs.2⟩
      have hleft : HasDerivWithinAt w (f l) (Iic b) b := by
        refine hasDerivWithinAt_Iic_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsLT hab) ?_
        · intro s hs
          exact ((hz s hs).congr_of_eventuallyEq (hwz s hs.2)).differentiableAt
            |>.differentiableWithinAt
        · have hzlim : Tendsto z (𝓝[Set.Ioo a b] b) (𝓝 l) :=
            hlim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)
          have hev : z =ᶠ[𝓝[Set.Ioo a b] b] w :=
            eventually_of_mem self_mem_nhdsWithin (fun s hs => by simp only [w, if_pos hs.2])
          have hwlim : Tendsto w (𝓝[Set.Ioo a b] b) (𝓝 l) := hzlim.congr' hev
          have : Tendsto w (𝓝[Set.Ioo a b] b) (𝓝 (w b)) := by rw [hwb]; exact hwlim
          exact this
        · have hev : (fun s => deriv w s) =ᶠ[𝓝[<] b] (fun s => f (z s)) := by
            filter_upwards [Ioo_mem_nhdsLT hab] with s hs
            rw [(hwz s hs.2).deriv_eq, (hz s hs).deriv]
          have hfl : Tendsto (fun s => f (z s)) (𝓝[<] b) (𝓝 (f l)) :=
            (hf.continuous.continuousAt).tendsto.comp hlim
          exact hfl.congr' hev.symm
      have hαcont : ContinuousWithinAt α (Set.Icc (b - ε) (b + ε)) b :=
        (hαderiv b ⟨by linarith, by linarith⟩).continuousWithinAt
      have hαcont' : ContinuousWithinAt α (Set.Ioo b (b + ε)) b := hαcont.mono hsub
      have hright : HasDerivWithinAt w (f l) (Ici b) b := by
        refine hasDerivWithinAt_Ici_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsGT (show b < b + ε by linarith)) ?_
        · intro s hs
          have hsIcc : s ∈ Set.Icc (b - ε) (b + ε) := hsub hs
          have hd : HasDerivAt w (f (α s)) s :=
            ((hαderiv s hsIcc).hasDerivAt (Icc_mem_nhds (by linarith [hs.1]) hs.2)).congr_of_eventuallyEq
              (hwα s hs.1)
          exact hd.differentiableAt.differentiableWithinAt
        · refine hαcont'.congr ?_ ?_
          · intro y hy
            simp only [w, if_neg (not_lt.mpr (le_of_lt hy.1))]
          · simp only [w, if_neg (lt_irrefl b)]
        · have hev : (fun s => deriv w s) =ᶠ[𝓝[>] b] (fun s => f (α s)) := by
            filter_upwards [Ioo_mem_nhdsGT (show b < b + ε by linarith)] with s hs
            rw [(hwα s hs.1).deriv_eq]
            exact ((hαderiv s (hsub hs)).hasDerivAt
              (Icc_mem_nhds (by linarith [hs.1]) hs.2)).deriv
          have hIoi : 𝓝[>] b = 𝓝[Set.Ioo b (b + ε)] b := by
            have hs : Set.Ioo (b - 1) (b + ε) ∈ 𝓝 b :=
              Ioo_mem_nhds (by linarith) (by linarith)
            have h2 : Set.Ioi b ∩ Set.Ioo (b - 1) (b + ε)
                = Set.Ioo b (b + ε) ∩ Set.Ioo (b - 1) (b + ε) := by
              ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
              constructor
              · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2, h3⟩
              · rintro ⟨⟨h1, h3⟩, h2, _⟩; exact ⟨h1, h2, h3⟩
            simpa using nhdsWithin_eq_nhdsWithin' hs h2
          have hαlim : Tendsto α (𝓝[>] b) (𝓝 l) := by
            rw [hIoi]
            have h : Tendsto α (𝓝[Set.Ioo b (b + ε)] b) (𝓝 (α b)) := hαcont'
            rw [show α b = l from hαb] at h
            exact h
          have hfl : Tendsto (fun s => f (α s)) (𝓝[>] b) (𝓝 (f l)) :=
            (hf.continuous.continuousAt).tendsto.comp hαlim
          exact hfl.congr' hev.symm
      have hunion : HasDerivWithinAt w (f l) univ b := by
        have h := hleft.union hright
        rwa [Iic_union_Ici] at h
      have hfin : HasDerivAt w (f l) b := hunion.hasDerivAt univ_mem
      simpa [hwb] using hfin
    · -- `t > b`
      have hIoo : t ∈ Set.Ioo (b - ε) (b + ε) := ⟨by linarith [hgt], ht.2⟩
      have hd : HasDerivAt α (f (α t)) t :=
        ((hαderiv t ⟨le_of_lt hIoo.1, le_of_lt hIoo.2⟩).hasDerivAt
          (Icc_mem_nhds hIoo.1 hIoo.2))
      have h := hd.congr_of_eventuallyEq (hwα t hgt)
      have hwt : w t = α t := by simp only [w, if_neg (not_lt.mpr (le_of_lt hgt))]
      rw [← hwt] at h
      exact h
  · intro t ht
    simp only [w, if_pos ht.2]

end Commons.Analysis.ODE