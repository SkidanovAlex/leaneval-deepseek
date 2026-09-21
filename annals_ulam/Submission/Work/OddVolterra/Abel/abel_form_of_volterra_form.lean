import Submission.Commons.Analysis.Abel.volterra_equivalence_full

/-!
# The Abel form of a Volterra equation (Ryabogin, Annals 195 (2022))

This file proves the inverse direction of the Abel/Volterra equivalence used in
the odd-dimensional case of the floating-body problem: if the *differentiated*
Abel system

`- ∫_0^1 K(s,s)/√(τ(1-τ)) dτ + ∫_s^b ∂₁G(s,σ) dσ = (d/ds) ∫_s^b Q(σ)/√(σ-s) dσ`

(where `G(s,σ) = ∫_0^1 K(s+τ(σ-s),σ)/√(τ(1-τ)) dτ`) holds on `(a,b)`, then the
pointwise Abel equation `∫_s^b K(s,σ)/√(σ-s) dσ = Q(s)` holds on `(a,b)`.

The proof goes through the iterated integral identity: the function
`u ↦ ∫_σ in u..b ∫_τ in 0..1 K(u+τ(σ-u),σ)/√(τ(1-τ)) dτ dσ` is both the
double Abel transform of `K` (its derivative is the left-hand side above) and,
by Abel injectivity, admits the constant-of-integration argument that pins down
the single Abel transform of `K` to be `Q`.
-/

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Work.OddVolterra.Abel

theorem abel_form_of_volterra_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b) {K : ℝ → ℝ → E} {Q : ℝ → E}
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hQ : ContDiffOn ℝ 2 Q (Set.Icc a b))
    (hdvi : ∀ s ∈ Set.Ioo a b,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s)
        + (∫ σ in s..b, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s)
      = deriv (fun u : ℝ => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) s) :
    ∀ s ∈ Set.Ioo a b, (∫ σ in s..b, (Real.sqrt (σ - s))⁻¹ • K s σ) = Q s := by
  have hKcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hK.continuousOn
  have hQcont : ContinuousOn Q (Set.Icc a b) := hQ.continuousOn
  -- the single Abel transform of `K`
  let A : ℝ → E := fun x => ∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ
  -- the double Abel transform of `K`, written as the inner averaged kernel
  let H : ℝ → E := fun u => ∫ σ in u..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
    (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ
  -- the Abel transform of `Q`
  let P : ℝ → E := fun u => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v
  -- ### The derivative of `H` is the left-hand side of the hypothesis
  have hHder : ∀ x ∈ Set.Ioo a b, HasDerivAt H
      (- (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K x x) +
        (∫ σ in x..b, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..(1 : ℝ),
          (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) x)) x := by
    intro x hx
    simpa [H] using
      Commons.Analysis.Abel.volterra_integral_hasDerivAt (E := E) hab hK x hx
  have hdiffH : DifferentiableOn ℝ H (Set.Ioo a b) := fun x hx =>
    (hHder x hx).differentiableAt.differentiableWithinAt
  -- ### `H` and `P` have the same derivative on `(a,b)`
  have hderiv_eq : Set.EqOn (deriv H) (deriv P) (Set.Ioo a b) := by
    intro x hx
    rw [(hHder x hx).deriv]
    exact hdvi x hx
  -- ### `P` is differentiable on `(a,b)` (the hypothesis `Q b = 0` is not needed)
  have hPsplit : ∀ u ∈ Set.Ioo a b, P u =
      (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) + (2 * Real.sqrt (b - u)) • Q b := by
    intro u hu
    have hub : u < b := hu.2
    have huIcc : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hw : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹) volume u b := by
      simpa using Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub (a := u) (b := b) hub
    have hQuI : ContinuousOn Q (Set.uIcc u b) := by
      refine hQcont.mono ?_
      rw [Set.uIcc_of_le (le_of_lt hub)]
      intro v hv
      exact ⟨le_trans huIcc.1 hv.1, hv.2⟩
    have hQuI' : ContinuousOn (fun v : ℝ => Q v - Q b) (Set.uIcc u b) :=
      hQuI.sub continuousOn_const
    have h1int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • (Q v - Q b))
        volume u b := hw.smul_continuousOn hQuI'
    have h2int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q b) volume u b :=
      hw.smul_continuousOn continuousOn_const
    have hcongr : (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) =
        ∫ v in u..b, ((Real.sqrt (v - u))⁻¹ • (Q v - Q b) + (Real.sqrt (v - u))⁻¹ • Q b) := by
      refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hub) (fun v _ => ?_)
      show (Real.sqrt (v - u))⁻¹ • Q v =
        (Real.sqrt (v - u))⁻¹ • (Q v - Q b) + (Real.sqrt (v - u))⁻¹ • Q b
      rw [← smul_add, sub_add_cancel]
    dsimp only [P]
    calc (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v)
        = ∫ v in u..b,
            ((Real.sqrt (v - u))⁻¹ • (Q v - Q b) + (Real.sqrt (v - u))⁻¹ • Q b) := hcongr
      _ = (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) +
            ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q b :=
          intervalIntegral.integral_add h1int h2int
      _ = (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) +
            (∫ v in u..b, (Real.sqrt (v - u))⁻¹) • Q b := by
          rw [intervalIntegral.integral_smul_const]
      _ = (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) +
            (2 * Real.sqrt (b - u)) • Q b := by
          rw [Commons.Analysis.Abel.integral_invSqrt_sub (a := u) (b := b) hub]
  have hdiffP : DifferentiableOn ℝ P (Set.Ioo a b) := by
    intro x hx
    have hQ1cont : ContDiffOn ℝ 2 (fun v : ℝ => Q v - Q b) (Set.Icc a b) :=
      hQ.sub contDiffOn_const
    have hQ1b : (fun v : ℝ => Q v - Q b) b = 0 := by simp
    have h1 : DifferentiableAt ℝ
        (fun u => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) x :=
      Commons.Analysis.Abel.differentiableAt_intervalIntegral_invSqrt_Q (E := E) hab hQ1cont hQ1b hx
    have h2 : DifferentiableAt ℝ (fun u : ℝ => (2 * Real.sqrt (b - u)) • Q b) x := by
      have hb' : (0 : ℝ) < b - x := sub_pos.mpr hx.2
      have hlin : HasDerivAt (fun u : ℝ => b - u) (-1) x := (hasDerivAt_id x).const_sub b
      have hsqrt0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (b - x))) (b - x) := by
        simpa using Real.hasDerivAt_sqrt (sub_ne_zero.mpr (ne_of_gt hb'))
      have hcomp : HasDerivAt (fun u : ℝ => Real.sqrt (b - u))
          (1 / (2 * Real.sqrt (b - x)) * -1) x := by
        simpa [Function.comp_def] using HasDerivAt.comp (x := x)
          (h := fun u : ℝ => b - u) (h₂ := Real.sqrt) (h' := -1)
          (h₂' := 1 / (2 * Real.sqrt (b - x))) hsqrt0 hlin
      exact ((hcomp.const_mul 2).smul_const (Q b)).differentiableAt
    have h3 : DifferentiableAt ℝ (fun u =>
        (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) + (2 * Real.sqrt (b - u)) • Q b) x :=
      h1.add h2
    have hev : P =ᶠ[𝓝 x] (fun u => (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) +
        (2 * Real.sqrt (b - u)) • Q b) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
      exact hPsplit u hu
    exact (h3.congr_of_eventuallyEq hev).differentiableWithinAt
  -- ### hence `H - P` is constant on `(a,b)`
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hdiffH hdiffP hderiv_eq
  -- ### both sides tend to `0` at `b`, so the constant vanishes
  have hIoo_nhds : Set.Ioo a b ∈ 𝓝[<] b := by
    have hmem : Set.Iio b ∩ Set.Ioi a ∈ 𝓝[<] b :=
      inter_mem_nhdsWithin (s := Set.Iio b) (t := Set.Ioi a) (isOpen_Ioi.mem_nhds hab)
    have hset : Set.Iio b ∩ Set.Ioi a = Set.Ioo a b := by
      ext y
      constructor
      · intro hy; exact ⟨hy.2, hy.1⟩
      · intro hy; exact ⟨hy.2, hy.1⟩
    simpa [hset] using hmem
  have hHlim : Tendsto H (𝓝[<] b) (𝓝 0) := by
    simpa [H] using
      Commons.Analysis.Abel.tendsto_volterra_double_integral_nhdsWithin_lt (E := E) hab hKcont
  have hPlim : Tendsto P (𝓝[<] b) (𝓝 0) := by
    have hQ1cont : ContinuousOn (fun v : ℝ => Q v - Q b) (Set.Icc a b) :=
      (hQ.sub contDiffOn_const).continuousOn
    have hQ1b : (fun v : ℝ => Q v - Q b) b = 0 := by simp
    have h1 : Tendsto (fun u : ℝ => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b))
        (𝓝[<] b) (𝓝 0) :=
      Commons.Analysis.Abel.tendsto_intervalIntegral_invSqrt_Q_nhdsWithin_lt (E := E)
        hab hQ1cont hQ1b
    have h2 : Tendsto (fun u : ℝ => (2 * Real.sqrt (b - u)) • Q b) (𝓝[<] b) (𝓝 0) := by
      have hb : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 0) := by
        have h : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 (b - b)) :=
          Tendsto.sub tendsto_const_nhds (tendsto_id.mono_left inf_le_left)
        simpa using h
      have hs : Tendsto (fun u : ℝ => Real.sqrt (b - u)) (𝓝[<] b) (𝓝 0) := by
        simpa using hb.sqrt
      have hs2 : Tendsto (fun u : ℝ => 2 * Real.sqrt (b - u)) (𝓝[<] b) (𝓝 (2 * 0)) :=
        hs.const_mul 2
      simpa using hs2.smul_const (Q b)
    have hsum : Tendsto (fun u : ℝ =>
        (∫ v in u..b, (Real.sqrt (v - u))⁻¹ • (Q v - Q b)) + (2 * Real.sqrt (b - u)) • Q b)
        (𝓝[<] b) (𝓝 (0 + 0)) := h1.add h2
    refine Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards [hIoo_nhds] with u hu
    exact (hPsplit u hu).symm
  have hc0 : c = 0 := by
    have hHlim' : Tendsto (fun x : ℝ => P x + c) (𝓝[<] b) (𝓝 0) :=
      hHlim.congr' (by
        filter_upwards [hIoo_nhds] with x hx
        exact hc hx)
    have hPlim' : Tendsto (fun x : ℝ => P x + c) (𝓝[<] b) (𝓝 (0 + c)) :=
      hPlim.add tendsto_const_nhds
    have h := tendsto_nhds_unique hHlim' hPlim'
    simpa using h.symm
  -- ### therefore `H = P` on `(a,b)`, i.e. the double Abel transforms agree
  have hHP : ∀ x ∈ Set.Ioo a b, H x = P x := by
    intro x hx
    have h1 := hc hx
    rw [hc0] at h1
    simpa using h1
  -- ### Abel injectivity gives the pointwise equation
  have hEq : ∀ s ∈ Set.Ioo a b,
      (∫ x in s..b, (Real.sqrt (x - s))⁻¹ • A x) =
        ∫ x in s..b, (Real.sqrt (x - s))⁻¹ • Q x := by
    intro s hs
    have hdbl := Commons.Analysis.Abel.volterra_double_integral (E := E) hab hKcont s hs
    have hHs : H s = ∫ x in s..b, (Real.sqrt (x - s))⁻¹ • A x := by
      simpa [H, A] using hdbl
    have hPs : P s = ∫ x in s..b, (Real.sqrt (x - s))⁻¹ • Q x := rfl
    rw [← hHs, ← hPs, hHP s hs]
  have hAcont : ContinuousOn A (Set.Icc a b) := by
    simpa [A] using Commons.Analysis.Abel.continuousOn_abel_K (E := E) hab hK
  intro s hs
  have := Commons.Analysis.Abel.abel_transform_injective_on (E := E) hab hAcont hQcont hEq s hs
  simpa [A] using this

end Work.OddVolterra.Abel
