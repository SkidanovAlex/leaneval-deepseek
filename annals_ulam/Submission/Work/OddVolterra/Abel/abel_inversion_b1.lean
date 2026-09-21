import Submission.Commons.Analysis.Abel.volterra_equivalence_full

/-!
# The Abel form of a Volterra equation, `b = 1` version (Ryabogin, Annals 195 (2022))

This is the `b = 1` version of `Work.OddVolterra.Abel.abel_form_of_volterra_form`.
Only `ContinuousOn Q (Icc a 1)` and the differentiability of the Abel transform of
`Q` on `(a,1)` (`hPdiff`) are assumed, rather than `ContDiffOn ℝ 2 Q`.
-/

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Work.OddVolterra.Abel

theorem abel_inversion_b1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha1 : a < 1) {K : ℝ → ℝ → E} {Q : ℝ → E}
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a 1 ×ˢ Set.Icc a 1))
    (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hPdiff : ∀ x ∈ Set.Ioo a 1,
      DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) x)
    (hdvi : ∀ s ∈ Set.Ioo a 1,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s)
        + (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s)
      = deriv (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) s) :
    ∀ s ∈ Set.Ioo a 1, (∫ σ in s..1, (Real.sqrt (σ - s))⁻¹ • K s σ) = Q s := by
  have hKcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a 1 ×ˢ Set.Icc a 1) :=
    hK.continuousOn
  -- the single Abel transform of `K`
  let A : ℝ → E := fun x => ∫ σ in x..1, (Real.sqrt (σ - x))⁻¹ • K x σ
  -- the double Abel transform of `K`, written as the inner averaged kernel
  let H : ℝ → E := fun u => ∫ σ in u..1, ∫ τ in (0 : ℝ)..(1 : ℝ),
    (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ
  -- the Abel transform of `Q`
  let P : ℝ → E := fun u => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v
  -- ### The derivative of `H` is the left-hand side of the hypothesis
  have hHder : ∀ x ∈ Set.Ioo a 1, HasDerivAt H
      (- (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K x x) +
        (∫ σ in x..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..(1 : ℝ),
          (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) x)) x := by
    intro x hx
    simpa [H] using
      Commons.Analysis.Abel.volterra_integral_hasDerivAt (E := E) ha1 hK x hx
  have hdiffH : DifferentiableOn ℝ H (Set.Ioo a 1) := fun x hx =>
    (hHder x hx).differentiableAt.differentiableWithinAt
  -- ### `H` and `P` have the same derivative on `(a,1)`
  have hderiv_eq : Set.EqOn (deriv H) (deriv P) (Set.Ioo a 1) := by
    intro x hx
    rw [(hHder x hx).deriv]
    exact hdvi x hx
  have hdiffP : DifferentiableOn ℝ P (Set.Ioo a 1) := fun x hx =>
    (hPdiff x hx).differentiableWithinAt
  -- ### hence `H - P` is constant on `(a,1)`
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hdiffH hdiffP hderiv_eq
  -- ### the split of `P` against `Q 1`
  have hPsplit : ∀ u ∈ Set.Ioo a 1, P u =
      (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1)) + (2 * Real.sqrt (1 - u)) • Q 1 := by
    intro u hu
    have hu1 : u < 1 := hu.2
    have huIcc : u ∈ Set.Icc a 1 := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hw : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹) volume u 1 := by
      simpa using Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := 1) hu1
    have hQuI : ContinuousOn Q (Set.uIcc u 1) := by
      refine hQcont.mono ?_
      rw [Set.uIcc_of_le (le_of_lt hu1)]
      intro v hv
      exact ⟨le_trans huIcc.1 hv.1, hv.2⟩
    have hQuI' : ContinuousOn (fun v : ℝ => Q v - Q 1) (Set.uIcc u 1) :=
      hQuI.sub continuousOn_const
    have h1int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • (Q v - Q 1))
        volume u 1 := hw.smul_continuousOn hQuI'
    have h2int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q 1) volume u 1 :=
      hw.smul_continuousOn continuousOn_const
    have hcongr : (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) =
        ∫ v in u..1, ((Real.sqrt (v - u))⁻¹ • (Q v - Q 1) + (Real.sqrt (v - u))⁻¹ • Q 1) := by
      refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hu1) (fun v _ => ?_)
      show (Real.sqrt (v - u))⁻¹ • Q v =
        (Real.sqrt (v - u))⁻¹ • (Q v - Q 1) + (Real.sqrt (v - u))⁻¹ • Q 1
      rw [← smul_add, sub_add_cancel]
    dsimp only [P]
    calc (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v)
        = ∫ v in u..1,
            ((Real.sqrt (v - u))⁻¹ • (Q v - Q 1) + (Real.sqrt (v - u))⁻¹ • Q 1) := hcongr
      _ = (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1)) +
            ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q 1 :=
          intervalIntegral.integral_add h1int h2int
      _ = (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1)) +
            (∫ v in u..1, (Real.sqrt (v - u))⁻¹) • Q 1 := by
          rw [intervalIntegral.integral_smul_const]
      _ = (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1)) +
            (2 * Real.sqrt (1 - u)) • Q 1 := by
          rw [Commons.Analysis.Abel.integral_invSqrt_sub (a := u) (b := 1) hu1]
  -- ### `(a,1)` is a neighbourhood of `1` from the left
  have hIoo_nhds : Set.Ioo a 1 ∈ 𝓝[<] (1 : ℝ) := by
    have hmem : Set.Iio (1 : ℝ) ∩ Set.Ioi a ∈ 𝓝[<] (1 : ℝ) :=
      inter_mem_nhdsWithin (s := Set.Iio (1 : ℝ)) (t := Set.Ioi a) (isOpen_Ioi.mem_nhds ha1)
    have hset : Set.Iio (1 : ℝ) ∩ Set.Ioi a = Set.Ioo a 1 := by
      ext y
      constructor
      · intro hy; exact ⟨hy.2, hy.1⟩
      · intro hy; exact ⟨hy.2, hy.1⟩
    simpa [hset] using hmem
  -- ### both `H` and `P` tend to `0` at `1` from the left
  have hHlim : Tendsto H (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    simpa [H] using
      Commons.Analysis.Abel.tendsto_volterra_double_integral_nhdsWithin_lt (E := E) ha1 hKcont
  have hPlim : Tendsto P (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hQ1cont : ContinuousOn (fun v : ℝ => Q v - Q 1) (Set.Icc a 1) :=
      hQcont.sub continuousOn_const
    have hQ1one : (fun v : ℝ => Q v - Q 1) 1 = 0 := by simp
    have h1 : Tendsto (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1))
        (𝓝[<] (1 : ℝ)) (𝓝 0) :=
      Commons.Analysis.Abel.tendsto_intervalIntegral_invSqrt_Q_nhdsWithin_lt (E := E)
        ha1 hQ1cont hQ1one
    have h2 : Tendsto (fun u : ℝ => (2 * Real.sqrt (1 - u)) • Q 1) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hb : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] (1 : ℝ)) (𝓝 (1 - 1)) :=
          Tendsto.sub tendsto_const_nhds (tendsto_id.mono_left inf_le_left)
        simpa using h
      have hs : Tendsto (fun u : ℝ => Real.sqrt (1 - u)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
        simpa using hb.sqrt
      have hs2 : Tendsto (fun u : ℝ => 2 * Real.sqrt (1 - u)) (𝓝[<] (1 : ℝ)) (𝓝 (2 * 0)) :=
        hs.const_mul 2
      simpa using hs2.smul_const (Q 1)
    have hsum : Tendsto (fun u : ℝ =>
        (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • (Q v - Q 1)) + (2 * Real.sqrt (1 - u)) • Q 1)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 + 0)) := h1.add h2
    refine Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards [hIoo_nhds] with u hu
    exact (hPsplit u hu).symm
  -- ### the constant vanishes
  have hc0 : c = 0 := by
    have hHlim' : Tendsto (fun x : ℝ => P x + c) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
      hHlim.congr' (by
        filter_upwards [hIoo_nhds] with x hx
        exact hc hx)
    have hPlim' : Tendsto (fun x : ℝ => P x + c) (𝓝[<] (1 : ℝ)) (𝓝 (0 + c)) :=
      hPlim.add tendsto_const_nhds
    have h := tendsto_nhds_unique hHlim' hPlim'
    simpa using h.symm
  -- ### therefore `H = P` on `(a,1)`, i.e. the double Abel transforms agree
  have hHP : ∀ x ∈ Set.Ioo a 1, H x = P x := by
    intro x hx
    have h1 := hc hx
    rw [hc0] at h1
    simpa using h1
  -- ### Abel injectivity gives the pointwise equation
  have hEq : ∀ s ∈ Set.Ioo a 1,
      (∫ x in s..1, (Real.sqrt (x - s))⁻¹ • A x) =
        ∫ x in s..1, (Real.sqrt (x - s))⁻¹ • Q x := by
    intro s hs
    have hdbl := Commons.Analysis.Abel.volterra_double_integral (E := E) ha1 hKcont s hs
    have hHs : H s = ∫ x in s..1, (Real.sqrt (x - s))⁻¹ • A x := by
      simpa [H, A] using hdbl
    have hPs : P s = ∫ x in s..1, (Real.sqrt (x - s))⁻¹ • Q x := rfl
    rw [← hHs, ← hPs, hHP s hs]
  have hAcont : ContinuousOn A (Set.Icc a 1) := by
    simpa [A] using Commons.Analysis.Abel.continuousOn_abel_K (E := E) ha1 hK
  intro s hs
  have := Commons.Analysis.Abel.abel_transform_injective_on (E := E) ha1 hAcont hQcont hEq s hs
  simpa [A] using this

end Work.OddVolterra.Abel
