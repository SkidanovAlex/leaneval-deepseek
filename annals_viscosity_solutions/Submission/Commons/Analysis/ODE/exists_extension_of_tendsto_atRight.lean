import Mathlib.Analysis.ODE.ExistUnique

namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology
open Metric

theorem exists_extension_of_tendsto_atRight {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {X : E → E} {a b : ℝ} (hab : a < b) {z : ℝ → E}
    {l : E} (hX : ContDiffAt ℝ 1 X l)
    (hz : ∀ t ∈ Set.Ioo a b, HasDerivAt z (X (z t)) t)
    (hlim : Tendsto z (𝓝[<] b) (𝓝 l)) :
    ∃ δ > (0 : ℝ), ∃ w : ℝ → E, (∀ t ∈ Set.Ioo a (b + δ), HasDerivAt w (X (w t)) t) ∧
      Set.EqOn w z (Set.Ioo a b) := by
  classical
  obtain ⟨ε, hε, a₀, R, L, K, hR, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hX
  have hbIcc : b ∈ Set.Icc (b - ε) (b + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨α, hαb, hαderiv⟩ :=
    (hpl b).exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := l) (mem_closedBall_self (show (0 : ℝ) ≤ (R : ℝ) by positivity))
  let w : ℝ → E := fun t => if t < b then z t else α t
  have hwb : w b = l := by simp only [w, if_neg (lt_irrefl b)]; exact hαb
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
  have hsub_right : Set.Ioo b (b + ε) ⊆ Set.Icc (b - ε) (b + ε) :=
    fun s hs => ⟨by linarith [hs.1], le_of_lt hs.2⟩
  refine ⟨ε, hε, w, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with hlt | heq | hgt
    · -- t < b
      have h := (hz t ⟨ht.1, hlt⟩).congr_of_eventuallyEq (hwz t hlt)
      have hwt : w t = z t := by simp only [w, if_pos hlt]
      rw [← hwt] at h
      exact h
    · -- t = b
      rw [heq]
      have hleft : HasDerivWithinAt w (X l) (Iic b) b := by
        refine hasDerivWithinAt_Iic_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsLT hab) ?_
        · -- DifferentiableOn ℝ w (Ioo a b)
          intro s hs
          exact ((hz s hs).congr_of_eventuallyEq (hwz s hs.2)).differentiableAt
            |>.differentiableWithinAt
        · -- ContinuousWithinAt w (Ioo a b) b
          have hzlim : Tendsto z (𝓝[Set.Ioo a b] b) (𝓝 l) :=
            hlim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)
          have hev : z =ᶠ[𝓝[Set.Ioo a b] b] w :=
            eventually_of_mem self_mem_nhdsWithin (fun s hs => by simp only [w, if_pos hs.2])
          have hwlim : Tendsto w (𝓝[Set.Ioo a b] b) (𝓝 l) := hzlim.congr' hev
          have : Tendsto w (𝓝[Set.Ioo a b] b) (𝓝 (w b)) := by rw [hwb]; exact hwlim
          exact this
        · -- Tendsto (deriv w) (𝓝[<] b) (𝓝 (X l))
          have hev : (fun s => deriv w s) =ᶠ[𝓝[<] b] (fun s => X (z s)) := by
            filter_upwards [Ioo_mem_nhdsLT hab] with s hs
            rw [(hwz s hs.2).deriv_eq, (hz s hs).deriv]
          have hXlim : Tendsto (fun s => X (z s)) (𝓝[<] b) (𝓝 (X l)) :=
            hX.continuousAt.tendsto.comp hlim
          exact hXlim.congr' hev.symm
      have hright : HasDerivWithinAt w (X l) (Ici b) b := by
        refine hasDerivWithinAt_Ici_of_tendsto_deriv ?_ ?_ (Ioo_mem_nhdsGT (show b < b + ε by linarith)) ?_
        · -- DifferentiableOn ℝ w (Ioo b (b+ε))
          intro s hs
          have hsIcc : s ∈ Set.Icc (b - ε) (b + ε) := hsub_right hs
          have hd : HasDerivAt w (X (α s)) s :=
            ((hαderiv s hsIcc).hasDerivAt (Icc_mem_nhds (by linarith [hs.1]) hs.2)).congr_of_eventuallyEq
              (hwα s hs.1)
          exact hd.differentiableAt.differentiableWithinAt
        · -- ContinuousWithinAt w (Ioo b (b+ε)) b
          have hαcont : ContinuousWithinAt α (Set.Icc (b - ε) (b + ε)) b :=
            (hαderiv b hbIcc).continuousWithinAt
          have hαcont' : ContinuousWithinAt α (Set.Ioo b (b + ε)) b :=
            hαcont.mono hsub_right
          refine hαcont'.congr ?_ ?_
          · intro y hy
            simp only [w, if_neg (not_lt.mpr (le_of_lt hy.1))]
          · simp only [w, if_neg (lt_irrefl b)]
        · -- Tendsto (deriv w) (𝓝[>] b) (𝓝 (X l))
          have hev : (fun s => deriv w s) =ᶠ[𝓝[>] b] (fun s => X (α s)) := by
            filter_upwards [Ioo_mem_nhdsGT (show b < b + ε by linarith)] with s hs
            rw [(hwα s hs.1).deriv_eq]
            exact ((hαderiv s (hsub_right hs)).hasDerivAt
              (Icc_mem_nhds (by linarith [hs.1]) hs.2)).deriv
          have hαcontIoo : Tendsto α (𝓝[Set.Ioo b (b + ε)] b) (𝓝 l) := by
            have h2 : Tendsto α (𝓝[Set.Ioo b (b + ε)] b) (𝓝 (α b)) :=
              ((hαderiv b hbIcc).continuousWithinAt.mono hsub_right).tendsto
            rwa [hαb] at h2
          have hαlim : Tendsto α (𝓝[>] b) (𝓝 l) :=
            hαcontIoo.mono_left (le_inf nhdsWithin_le_nhds
              (le_principal_iff.mpr (Ioo_mem_nhdsGT (show b < b + ε by linarith))))
          have hXlim : Tendsto (fun s => X (α s)) (𝓝[>] b) (𝓝 (X l)) :=
            hX.continuousAt.tendsto.comp hαlim
          exact hXlim.congr' hev.symm
      have hunion : HasDerivWithinAt w (X l) univ b := by
        have h := hleft.union hright
        rwa [Iic_union_Ici] at h
      have hfin : HasDerivAt w (X l) b := hunion.hasDerivAt univ_mem
      rw [hwb]
      exact hfin
    · -- t > b
      have h := ((hαderiv t (hsub_right ⟨hgt, ht.2⟩)).hasDerivAt
          (Icc_mem_nhds (by linarith [hgt]) ht.2)).congr_of_eventuallyEq (hwα t hgt)
      have hwt : w t = α t := by simp only [w, if_neg (not_lt.mpr (le_of_lt hgt))]
      rw [← hwt] at h
      exact h
  · intro t ht
    simp only [w, if_pos ht.2]

end Commons.Analysis.ODE