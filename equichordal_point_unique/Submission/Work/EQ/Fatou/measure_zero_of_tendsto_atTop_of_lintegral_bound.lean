import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory Filter ENNReal

/-- If a measurable set `T` is such that `g n x → ∞` for every `x ∈ T`, and the
lower integrals `∫⁻ x, g n x ∂μ` are uniformly bounded by a finite constant `C`,
then `T` is `μ`-null. -/
theorem measure_zero_of_tendsto_atTop_of_lintegral_bound {α : Type*} {mα : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} {T : Set α} {g : ℕ → α → ENNReal}
    (hTmeas : MeasurableSet T) (hmeas : ∀ n, Measurable (g n))
    (hT : ∀ x ∈ T, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds ⊤))
    {C : ENNReal} (hC : C ≠ ⊤) (hbound : ∀ n, ∫⁻ x, g n x ∂μ ≤ C) :
    μ T = 0 := by
  -- For every natural threshold `a = n + 1`, the measure of `T` is bounded by `C / a`.
  have key : ∀ n : ℕ, μ T ≤ C / (((n + 1 : ℕ)) : ENNReal) := by
    intro n
    have ha0 : (((n+1 : ℕ)) : ENNReal) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hat : (((n+1 : ℕ)) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- Sets of points of `T` whose `g k x` stays above `a` for all `k ≥ m`.
    let B : ℕ → Set α := fun m => T ∩ {x | ∀ k, m ≤ k → (((n+1:ℕ)) : ENNReal) ≤ g k x}
    have hBmono : Monotone B := by
      intro m m' hmm' x hx
      exact ⟨hx.1, fun k hk => hx.2 k (le_trans hmm' hk)⟩
    -- `T` is the increasing union of the `B m`, since `g k x → ∞` on `T`.
    have hUnion : T = ⋃ m, B m := by
      apply le_antisymm
      · intro x hx
        have hxev : ∀ᶠ k in atTop, (((n+1:ℕ)) : ENNReal) < g k x :=
          (ENNReal.tendsto_nhds_top_iff_nat.mp (hT x hx)) (n+1)
        rw [Set.mem_iUnion]
        rcases (eventually_atTop.mp hxev) with ⟨m, hm⟩
        exact ⟨m, hx, fun k hk => le_of_lt (hm k hk)⟩
      · intro x hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨m, hx⟩
        exact hx.1
    -- Markov's inequality bounds each `μ (B m)` by `C / a`.
    have hBbound : ∀ m, μ (B m) ≤ C / (((n+1:ℕ)) : ENNReal) := by
      intro m
      have hsub : B m ⊆ {x | (((n+1:ℕ)) : ENNReal) ≤ g m x} := by
        intro x hx
        exact hx.2 m le_rfl
      calc μ (B m) ≤ μ {x | (((n+1:ℕ)) : ENNReal) ≤ g m x} := measure_mono hsub
        _ ≤ C / (((n+1:ℕ)) : ENNReal) := by
              have hmark := mul_meas_ge_le_lintegral (μ := μ) (hmeas m) (((n+1:ℕ)) : ENNReal)
              have hle : (((n+1:ℕ)) : ENNReal) * μ {x | (((n+1:ℕ)) : ENNReal) ≤ g m x} ≤ C :=
                le_trans hmark (hbound m)
              have hle' : μ {x | (((n+1:ℕ)) : ENNReal) ≤ g m x} * (((n+1:ℕ)) : ENNReal) ≤ C := by
                rw [mul_comm]; exact hle
              exact (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).mpr hle'
    calc μ T = μ (⋃ m, B m) := by rw [hUnion]
      _ = ⨆ m, μ (B m) := Monotone.measure_iUnion hBmono
      _ ≤ C / (((n+1:ℕ)) : ENNReal) := ciSup_le hBbound
  -- `C / (n+1) → 0`, so the uniform bound `μ T ≤ C / (n+1)` forces `μ T = 0`.
  have hlim : Tendsto (fun n : ℕ => C / (((n+1 : ℕ)) : ENNReal)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ENNReal)) atTop (nhds ⊤) :=
      ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat 1)
    have := ENNReal.Tendsto.const_div (a := C) h1 (Or.inr hC)
    simpa using this
  have h2 : μ T ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
  exact le_bot_iff.mp h2

end Work.EQ.Fatou
