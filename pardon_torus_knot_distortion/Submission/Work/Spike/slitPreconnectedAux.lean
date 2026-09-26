import Mathlib
import Submission.Work.Spike.spikeAux
import Submission.Work.Spike.spikeApply

/-!
# A slit with a free end does not disconnect a domain

`Work.Spike.domainSlitPreconnected`: if `D ⊆ ℂ` is an open preconnected set and `β : [0,1] → ℂ`
is an injective arc with `β 0 ∉ D` and `β t ∈ D` for `t > 0` (`β` enters `D` at once and never
returns to its base point), then `D \ range β` is preconnected.

The proof is a reduction to the *compact-obstacle* case `Work.Spike.spikePreconnected` by an
inversion about a point `c` of `D` that the arc misses.  Inverting in `c` turns every
neighbourhood of `c` inside `D` into a neighbourhood of `∞`, so the new obstacle
`ℂ \ φ '' D` is compact; preconnectedness transports back along the (continuous) inverse.

The two elementary facts used are `slitAux_ball_diff_center` (a punctured ball is
preconnected) and `slitAux_diff_point` (removing a point from an open preconnected
subset of `ℂ` keeps it preconnected).
-/

namespace Work.Spike

open Set Metric

noncomputable section

/-- **The centre-punctured open ball of `ℂ` is preconnected.** -/
theorem slitAux_ball_diff_center {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (Metric.ball z ε \ {z}) := by
  have hpre : IsPreconnected ({0}ᶜ : Set ℂ) :=
    ((isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)).isConnected).isPreconnected
  have hcont : Continuous (fun v : ℂ => z + v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)) := by
    refine continuous_const.add (continuous_id.mul ?_)
    exact Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.add continuous_norm) (fun v => by positivity))
  have himg : (fun v : ℂ => z + v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)) '' ({0}ᶜ : Set ℂ)
      = Metric.ball z ε \ {z} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hden : 0 < 1 + ‖v‖ := by positivity
      have hnorm : ‖v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)‖ < ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hε hden),
          ← mul_div_assoc, div_lt_iff₀ hden]
        nlinarith
      have hq : v * ((ε / (1 + ‖v‖) : ℝ) : ℂ) ≠ 0 := by
        intro h0
        have h1 : ‖v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)‖ = 0 := by rw [h0, norm_zero]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hε hden)] at h1
        have hpos : (0 : ℝ) < ε / (1 + ‖v‖) := div_pos hε hden
        have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        nlinarith
      constructor
      · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm
      · simp only [mem_singleton_iff]
        intro hcon
        have h : v * ((ε / (1 + ‖v‖) : ℝ) : ℂ) = 0 := by
          have := congrArg (fun x : ℂ => x - z) hcon
          simpa using this
        exact hq h
    · rintro ⟨hw, hwne⟩
      have hd : 0 < ε - ‖w - z‖ := by
        have h := hw; rw [Metric.mem_ball, dist_eq_norm] at h; linarith
      have hwz : w - z ≠ 0 := by
        intro h
        exact hwne (by simp only [mem_singleton_iff]; exact sub_eq_zero.mp h)
      refine ⟨(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hwz h
        · exact absurd h (Complex.ofReal_ne_zero.mpr (inv_ne_zero (ne_of_gt hd)))
      · have hnormv :
            ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖ = ‖w - z‖ / (ε - ‖w - z‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
            inv_eq_one_div, mul_one_div]
        have h1 : (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖ : ℝ)
            = ε / (ε - ‖w - z‖) := by
          rw [hnormv]; field_simp; try ring
        have h2 : (ε / (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖) : ℝ)
            = ε - ‖w - z‖ := by
          rw [h1]; field_simp; try ring
        have hne : (((ε - ‖w - z‖) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
        change z + ((w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)) *
          ((ε / (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖) : ℝ) : ℂ) = w
        rw [h2, Complex.ofReal_inv, mul_assoc, inv_mul_cancel₀ hne, mul_one]
        ring
  rw [← himg]
  exact hpre.image _ hcont.continuousOn

/-- **Removing a point from a nonempty open preconnected subset of `ℂ` keeps it preconnected.** -/
theorem slitAux_diff_point {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {c : ℂ} (hc : c ∈ D) : IsPreconnected (D \ {c}) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huv'
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDopen c hc
  set P : Set ℂ := Metric.ball c ε \ {c} with hPdef
  have hPpre : IsPreconnected P := slitAux_ball_diff_center hε
  have hPsub : P ⊆ D \ {c} := fun z hz => ⟨hεD hz.1, hz.2⟩
  have hPdisj : P ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at huv' ⊢
    intro z hz
    exact huv' z ⟨hPsub hz.1, hz.2⟩
  -- if `P` sits on the `a`-side then `c ∉ b`, and `D ⊆ (a ∪ ball) ∪ b` splits `D`
  have key : ∀ (a b : Set ℂ), IsOpen a → IsOpen b → P ⊆ a → D \ {c} ⊆ a ∪ b →
      (D \ {c}) ∩ (a ∩ b) = ∅ → D \ {c} ⊆ a := by
    intro a b ha hb hPa hab habdisj
    have hcbnot : c ∉ b := by
      intro hcb
      obtain ⟨ρ, hρ, hρb⟩ := Metric.isOpen_iff.mp hb c hcb
      set t : ℝ := min ρ ε / 2 with htdef
      have htpos : 0 < t := by rw [htdef]; positivity
      set z : ℂ := c + (t : ℂ) with hzdef
      have hzt : (t : ℂ) = z - c := by rw [hzdef]; ring
      have hzε : z ∈ Metric.ball c ε := by
        rw [Metric.mem_ball, dist_eq_norm, ← hzt, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos]
        linarith [min_le_right ρ ε]
      have hzρ : z ∈ Metric.ball c ρ := by
        rw [Metric.mem_ball, dist_eq_norm, ← hzt, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos]
        linarith [min_le_left ρ ε]
      have hzc : z ≠ c := by
        rw [hzdef]; intro hcon
        have : (t : ℂ) = 0 := by
          have := congrArg (fun x : ℂ => x - c) hcon; simpa using this
        exact (Complex.ofReal_ne_zero.mpr htpos.ne') this
      have hzcnot : z ∉ ({c} : Set ℂ) := by simpa [Set.mem_singleton_iff] using hzc
      have hzDc : z ∈ D \ {c} := ⟨hεD hzε, hzcnot⟩
      have hza : z ∈ a := hPa ⟨hzε, hzcnot⟩
      have hzb : z ∈ b := hρb hzρ
      exact Set.eq_empty_iff_forall_notMem.mp habdisj z ⟨hzDc, hza, hzb⟩
    have hA : IsOpen (a ∪ Metric.ball c ε) := ha.union Metric.isOpen_ball
    have hDsub : D ⊆ (a ∪ Metric.ball c ε) ∪ b := by
      intro z hz
      by_cases hzb : z ∈ Metric.ball c ε
      · exact Or.inl (Or.inr hzb)
      · by_cases hza : z ∈ a
        · exact Or.inl (Or.inl hza)
        · refine Or.inr ?_
          have hzc : z ≠ c := fun h => hzb (h ▸ mem_ball_self hε)
          exact (hab ⟨hz, hzc⟩).resolve_left hza
    have hdisj2 : D ∩ ((a ∪ Metric.ball c ε) ∩ b) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem] at habdisj ⊢
      intro z hz
      obtain ⟨hzD, hzab, hzb⟩ := hz
      rcases hzab with hza | hzbc
      · by_cases hzc : z = c
        · exact hcbnot (hzc ▸ hzb)
        · exact habdisj z ⟨⟨hzD, by simpa [Set.mem_singleton_iff] using hzc⟩, hza, hzb⟩
      · by_cases hzc : z = c
        · exact hcbnot (hzc ▸ hzb)
        · exact habdisj z ⟨⟨hzD, by simpa [Set.mem_singleton_iff] using hzc⟩,
            hPa ⟨hzbc, by simpa [Set.mem_singleton_iff] using hzc⟩, hzb⟩
    rcases (isPreconnected_iff_subset_of_disjoint.mp hDconn (a ∪ Metric.ball c ε) b hA hb
      hDsub hdisj2) with h | h
    · intro z hz
      rcases h hz.1 with hza | hzb
      · exact hza
      · exact hPa ⟨hzb, hz.2⟩
    · exact absurd (h hc) hcbnot
  rcases (isPreconnected_iff_subset_of_disjoint.mp hPpre u v hu hv
      (subset_trans hPsub huv) hPdisj) with hPu | hPv
  · left; exact key u v hu hv hPu huv huv'
  · right; exact key v u hv hu hPv (by rw [← Set.union_comm u v]; exact huv)
      (by rw [← Set.inter_comm u v]; exact huv')

/-- **A slit with a free end does not disconnect a domain** (see the module docstring). -/
theorem slitPreconnectedAux {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (h₀ : β ⟨0, by norm_num⟩ ∉ D) (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∈ D) :
    IsPreconnected (D \ Set.range β) := by
  have hDne : D.Nonempty := ⟨β ⟨1 / 2, by norm_num⟩, hint ⟨1 / 2, by norm_num⟩ (by norm_num)⟩
  have hinter : interior (Set.range β) = ∅ := interior_range_empty_of_injective hβ
  obtain ⟨c, hcD, hcr⟩ : ∃ c : ℂ, c ∈ D ∧ c ∉ Set.range β := by
    by_contra h
    push_neg at h
    have hsub : D ⊆ Set.range β := fun z hz => h z hz
    obtain ⟨d, hd⟩ := hDne
    have : d ∈ interior (Set.range β) :=
      interior_mono hsub (by rw [hDopen.interior_eq]; exact hd)
    rw [hinter] at this
    exact this
  -- the inversion `φ` about `c` and its inverse `ψ`
  set φ : ℂ → ℂ := fun w => (w - c)⁻¹ with hφ
  set ψ : ℂ → ℂ := fun w => c + w⁻¹ with hψ
  set D' : Set ℂ := {w : ℂ | w ≠ 0 ∧ ψ w ∈ D} with hD'set
  have hφψ : ∀ w : ℂ, φ (ψ w) = w := by
    intro w; simp only [hφ, hψ, add_sub_cancel_left, inv_inv]
  have hψφ : ∀ z : ℂ, ψ (φ z) = z := by
    intro z; simp only [hφ, hψ, inv_inv]; ring
  have hφinj : Function.Injective φ := fun a b hab => by
    have := congrArg ψ hab
    rwa [hψφ a, hψφ b] at this
  have hφcontOn : ContinuousOn φ (D \ {c}) := by
    rw [hφ]
    exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      (fun w hw => sub_ne_zero.mpr hw.2)
  have hD'eq : D' = φ '' (D \ {c}) := by
    ext w; constructor
    · intro hw
      rw [hD'set] at hw
      obtain ⟨hw0, hwD⟩ := hw
      refine ⟨ψ w, ⟨hwD, ?_⟩, hφψ w⟩
      intro hcon
      rw [hψ] at hcon
      have : w⁻¹ = 0 := by
        simp only [Set.mem_singleton_iff] at hcon
        have h := congrArg (fun x : ℂ => x - c) hcon
        simpa using h
      exact hw0 (inv_eq_zero.mp this)
    · rintro ⟨z, ⟨hzD, hzc⟩, rfl⟩
      rw [hD'set]
      refine ⟨?_, ?_⟩
      · rw [hφ]; exact inv_ne_zero (sub_ne_zero.mpr (by simpa [Set.mem_singleton_iff] using hzc))
      · rw [hψφ z]; exact hzD
  have hψcontOn0 : ContinuousOn ψ ({0}ᶜ : Set ℂ) := by
    rw [hψ]
    exact (ContinuousOn.inv₀ continuousOn_id (fun w hw => hw)).const_add c
  have hD'open : IsOpen D' := by
    have heq : D' = ({0}ᶜ : Set ℂ) ∩ ψ ⁻¹' D := by ext w; simp [hD'set]
    rw [heq]
    exact hψcontOn0.isOpen_inter_preimage isClosed_singleton.isOpen_compl hDopen
  have hD'pre : IsPreconnected D' := by
    have h1 : IsPreconnected (D \ {c}) := slitAux_diff_point hDopen hDconn hcD
    have h2 := h1.image φ hφcontOn
    rwa [hD'eq]
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDopen c hcD
  have hDbdd : Bornology.IsBounded D'ᶜ := by
    rw [isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨ε⁻¹, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hle
    rw [not_le] at hle
    apply hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hle
      exact not_lt_of_ge (inv_nonneg.mpr hε.le) hle
    rw [hD'set]
    refine ⟨hw0, ?_⟩
    have hnorm : ‖w⁻¹‖ < ε := by
      rw [norm_inv]
      exact (inv_lt_comm₀ hε (norm_pos_iff.mpr hw0)).mp hle
    have : c + w⁻¹ ∈ Metric.ball c ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hnorm
    exact hεD this
  have hK'cpt : IsCompact D'ᶜ :=
    isCompact_iff_isClosed_bounded.mpr ⟨hD'open.isClosed_compl, hDbdd⟩
  -- the inverted arc
  let β' : C(Set.Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun t => φ (β t), by
      rw [hφ]
      exact Continuous.inv₀ (β.continuous.sub continuous_const)
        (fun t => sub_ne_zero.mpr (fun h => hcr ⟨t, h⟩))⟩
  have hβ'inj : Function.Injective β' := fun t s hts => hβ (hφinj hts)
  have hβ'0 : β' ⟨0, by norm_num⟩ ∉ D' := by
    intro hmem
    rw [hD'eq] at hmem
    obtain ⟨z, ⟨hzD, hzc⟩, hzφ⟩ := hmem
    have hz0 : z = β ⟨0, by norm_num⟩ := hφinj hzφ
    exact h₀ (hz0 ▸ hzD)
  have hβ'hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β' t ∈ D' := by
    intro t ht
    rw [hD'eq]
    exact ⟨β t, ⟨hint t ht, fun h => hcr ⟨t, h⟩⟩, rfl⟩
  have hspike := spikePreconnected (K := D'ᶜ) hK'cpt (by simpa using hD'pre) hβ'inj
    (by rw [Set.mem_compl_iff]; exact hβ'0)
    (fun t ht => by simpa only [Set.mem_compl_iff, not_not] using hβ'hint t ht)
  have hD'r : IsPreconnected (D' \ Set.range β') := by
    simpa [Set.sdiff_eq] using hspike
  have hψcontOn : ContinuousOn ψ (D' \ Set.range β') := by
    rw [hψ]
    refine (ContinuousOn.inv₀ continuousOn_id ?_).const_add c
    intro w hw
    rw [hD'set] at hw
    exact hw.1.1
  -- transport back
  have hUeq : (D \ Set.range β) \ {c} = ψ '' (D' \ Set.range β') := by
    apply Subset.antisymm
    · rintro z ⟨⟨hzD, hzr⟩, hzc⟩
      refine ⟨φ z, ⟨?_, ?_⟩, hψφ z⟩
      · rw [hD'eq]; exact ⟨z, ⟨hzD, hzc⟩, rfl⟩
      · rintro ⟨t, ht⟩
        exact hzr ⟨t, hφinj ht⟩
    · rintro z ⟨w, ⟨hwD', hwr⟩, rfl⟩
      rw [hD'eq] at hwD'
      obtain ⟨y, ⟨hyD, hyc⟩, hyw⟩ := hwD'
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hyw, hψφ y]; exact hyD
      · rintro ⟨t, ht⟩
        exact hwr ⟨t, by show φ (β t) = w; rw [ht]; exact hφψ w⟩
      · rw [← hyw, hψφ y]; exact hyc
  have hUcp : IsPreconnected ((D \ Set.range β) \ {c}) := by
    rw [hUeq]
    exact hD'r.image ψ hψcontOn
  have hUopen : IsOpen (D \ Set.range β) :=
    hDopen.sdiff (isCompact_range β.continuous).isClosed
  have hcU : c ∈ D \ Set.range β := ⟨hcD, hcr⟩
  refine IsPreconnected.subset_closure hUcp Set.sdiff_subset (fun z hz => ?_)
  by_cases hzc : z = c
  · rw [hzc]
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨η, hη, hηD⟩ := Metric.isOpen_iff.mp hUopen c hcU
    set t : ℝ := min η δ / 2 with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    refine ⟨c + (t : ℂ), ⟨hηD ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos htpos]
      linarith [min_le_left η δ]
    · simp only [mem_singleton_iff]
      intro hcon
      have : (t : ℂ) = 0 := by
        have := congrArg (fun x : ℂ => x - c) hcon; simpa using this
      exact (Complex.ofReal_ne_zero.mpr htpos.ne') this
    · rw [dist_eq_norm]
      have hsub : c - (c + (t : ℂ)) = -(t : ℂ) := by ring
      rw [hsub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      linarith [min_le_right η δ]
  · exact subset_closure ⟨hz, by simpa [Set.mem_singleton_iff] using hzc⟩

end

end Work.Spike
