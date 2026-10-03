import Mathlib
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.period_interface
import Submission.Lib.Unif2.Work.Drive.harmonicOnX_extension_off_pair
import Submission.Lib.Unif2.Work.Drive.exists_holomorphicOnX_div_of_simple_zero

namespace Work.Drive

/-- **An injective holomorphic function with a single simple zero.** Under the period condition
`hP` and the three inputs `hbddHolo` (`[♥]`: bounded holomorphic functions on `X` are constant),
`hb` (`singlePoleBounded`) and `hpair` (`pairFunction`), every point `b` is the single simple zero
of an injective holomorphic function `X → ℂ`.

Route (this is the Liouville injectivity argument, no simple connectivity needed):
* `hb b` gives `E_b`, harmonic off `b`, unit log pole at `b`, `E_b ≤ 1` off a compact set;
  `hP b E_b …` plus `Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods` gives
  `Φ : X → ℂ` holomorphic, `HasLogPoleAt b Φ`, `Φ x ≠ 0` for `x ≠ b`, `‖Φ x‖ = exp (-(E_b x))`.
  In particular `‖Φ x‖ ≥ exp (-1)` off a compact set.
* Suppose `Φ q = Φ q' = w` with `q ≠ q'`. Then `w ≠ 0` (`b` is the only zero), so no corner case.
  Put `R := 1 - w/Φ`, holomorphic on `X ∖ {b}`, `= 0` at `q,q'`, with a pole at `b`, and
  `‖R x‖ ≤ 1 + ‖w‖·e` off a compact set (from `E_b ≤ 1`).
* `hpair q b` gives `τ` with `τ ≤ 1` off a compact set; construct its holomorphic modulus
  `φ` (zero at `q`, pole at `b`) exactly as in `hb`+`hP` above, so `‖φ x‖ ≥ exp (-1)` off a
  compact set.
* `V := R/φ` is holomorphic on all of `X` (the pole of `R` at `b` is cancelled by that of `φ`,
  the zero of `R` at `q` by that of `φ`; use
  `Work.SimplyConnected.ABS.analyticAt_quotient_update_of_simple_zero`) and bounded, and
  `V q' = 0`. By `hbddHolo`, `V ≡ 0`, so `1 = w/Φ`, contradicting `Φ b = 0`.

**Proof as formalised** (the same argument, with the two-pole modulus written out explicitly).
From `hpair q b` one gets `τ`, and `u := E_q - τ` is harmonic on `X ∖ {q,b}` (the two unit log poles
at `q` cancel), bounded near `q`, with a unit log pole at `b`.  `Work.Drive.harmonicOnX_extension_off_pair`
extends it over `q` to a function `U` harmonic on `X ∖ {b}`, and `hP b` applies to `U`: the resulting
modulus `Ψ` is holomorphic on `X` with a simple zero at `b` and no other zero, and
`‖Ψ x‖ = exp (-(U x))` off `b`.  In terms of the period condition this is the meromorphic function
with a simple zero at `b` and a simple pole at `q`, and it is what plays the role of `1/φ` above
(the cancellation of the pole of `R` at `b` happens in the *numerator* `(Φ - w)·Ψ`, since
`Φ b = 0` and `Ψ b = 0`).  With `Φ_q` the modulus of `E_q`,
`V := (Φ - w)·Ψ/(Φ·Φ_q)` is holomorphic on `X` by two applications of the removable singularity
`Work.Drive.exists_holomorphicOnX_div_of_simple_zero` (at `q`, where `Φ_q` has a simple zero and
`Φ - w` vanishes, and then at `b`, where `Φ` has a simple zero and `(Φ - w)·Ψ` vanishes), and
`‖V x‖ = (‖Φ x - w‖/‖Φ x‖)·exp (τ x) ≤ (1 + ‖w‖e)e` off a compact set.  `V q' = 0`, so `hbddHolo`
gives `V ≡ 0`; hence `Φ = w` off `{q,b}`, contradicting the analyticity of `Φ` at `b`
(identity principle on a chart ball at `b`: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`),
since `Φ b = 0 ≠ w`. -/
theorem exists_injective_modulus {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (hP : Work.Drive.PeriodsHold X)
    (hbddHolo : ∀ {g : X → ℂ}, Submission.HolomorphicOnX g Set.univ →
      (∃ M : ℝ, ∀ x : X, ‖g x‖ ≤ M) → ∃ c : ℂ, ∀ x : X, g x = c)
    (hb : ∀ a : X, ∃ E : X → ℝ, Submission.HarmonicOnX E (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, E x ≤ 1)
    (hpair : ∀ a b : X, a ≠ b → ∃ τ : X → ℝ,
      Submission.HarmonicOnX τ (Set.univ \ {a, b}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a, b}) a τ ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b (fun x => -τ x) ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, τ x ≤ 1)
    (b : X) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt b Φ ∧
      (∀ x : X, x ≠ b → Φ x ≠ 0) ∧ Function.Injective Φ := by
  classical
  -- ## Step 1: the holomorphic modulus at `b`, from `hb b` and the period condition
  obtain ⟨E_b, hEb_harm, hEb_pole, K_b, hKb_comp, hEb_le⟩ := hb b
  obtain ⟨Φ, hΦhol, hΦ0, hΦmod, hΦpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hEb_harm hEb_pole
      (hP b E_b hEb_harm hEb_pole)
  have hΦne : ∀ x : X, x ≠ b → Φ x ≠ 0 := by
    intro x hx h0
    have h1 := hΦmod x hx
    rw [h0, norm_zero] at h1
    exact Real.exp_ne_zero (-(E_b x)) h1.symm
  refine ⟨Φ, hΦhol, hΦpole, hΦne, ?_⟩
  -- ## Step 2: injectivity, by contradiction
  intro q q' heq
  by_contra hne
  have hqb : q ≠ b := by
    intro h
    have h1 : Φ q' = 0 := by rw [← heq, h, hΦ0]
    have h2 : q' = b := by
      by_contra h'
      exact hΦne q' h' h1
    exact hne (h.trans h2.symm)
  have hq'b : q' ≠ b := by
    intro h
    have h1 : Φ q = 0 := by rw [heq, h, hΦ0]
    have h2 : q = b := by
      by_contra h'
      exact hΦne q h' h1
    exact hne (h2.trans h.symm)
  set w : ℂ := Φ q with hw
  have hw_ne : w ≠ 0 := by rw [hw]; exact hΦne q hqb
  have hq'w : Φ q' = w := by rw [hw]; exact heq.symm
  -- ## Step 3: the single-pole data at `q`, and the pair function
  obtain ⟨E_q, hEq_harm, hEq_pole, K_q, hKq_comp, hEq_le⟩ := hb q
  obtain ⟨Φ_q, hΦq_hol, hΦq_0, hΦq_mod, hΦq_pole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hEq_harm hEq_pole
      (hP q E_q hEq_harm hEq_pole)
  have hΦq_ne : ∀ x : X, x ≠ q → Φ_q x ≠ 0 := by
    intro x hx h0
    have h1 := hΦq_mod x hx
    rw [h0, norm_zero] at h1
    exact Real.exp_ne_zero (-(E_q x)) h1.symm
  obtain ⟨τ, hτ_harm, hτ_pole_q, hτ_pole_b, K_τ, hKτ_comp, hτ_le⟩ := hpair q b hqb
  -- ## Step 4: the harmonic function `u = E_q - τ`, which has a unit pole at `b` only
  set u : X → ℝ := fun x => E_q x - τ x with hu_def
  have hu_harm : Submission.HarmonicOnX u (Set.univ \ {q, b}) := by
    rw [hu_def]
    refine Submission.HarmonicOnX.sub ?_ hτ_harm
    refine hEq_harm.mono (fun x hx => ?_)
    refine ⟨trivial, ?_⟩
    intro hxq
    exact hx.2 (by rw [hxq]; simp)
  -- `u` is bounded near `q`: the two unit log poles cancel there
  have hu_bdd : ∃ M : ℝ, ∃ V : Set X, V ∈ nhds q ∧ ∀ x ∈ V, x ≠ q → |u x| ≤ M := by
    obtain ⟨C₁, V₁, hV₁, hb₁⟩ := hEq_pole
    obtain ⟨C₂, V₂, hV₂, hb₂⟩ := hτ_pole_q
    refine ⟨C₁ + C₂, V₁ ∩ V₂ ∩ ({b}ᶜ), ?_, ?_⟩
    · refine Filter.inter_mem (Filter.inter_mem hV₁ hV₂) ?_
      exact (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hqb)
    · intro x hx hxq
      obtain ⟨⟨hx₁, hx₂⟩, hxb⟩ := hx
      have hxne_b : x ≠ b := by simpa using hxb
      change |E_q x - τ x| ≤ C₁ + C₂
      have h1 : |E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖| ≤ C₁ :=
        hb₁ x hx₁ (by simp [hxq]) hxq
      have h2 : |τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖| ≤ C₂ :=
        hb₂ x hx₂ (by simp [hxq, hxne_b]) hxq
      have h3 : E_q x - τ x = (E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖)
          - (τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖) := by ring
      rw [h3]
      calc |(E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖)
            - (τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖)|
          = |(E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖)
            + (-(τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖))| := by ring_nf
        _ ≤ |E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖|
            + |-(τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖)| := abs_add_le _ _
        _ = |E_q x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖|
            + |τ x + Real.log ‖(chartAt ℂ q) x - (chartAt ℂ q) q‖| := by rw [abs_neg]
        _ ≤ C₁ + C₂ := add_le_add h1 h2
  -- ## Step 5: extend over the cancellation point `q`
  obtain ⟨U, hU_harm, hU_eq⟩ := harmonicOnX_extension_off_pair hqb hu_harm hu_bdd
  have hUeq' : ∀ x : X, x ≠ q → U x = E_q x - τ x := by
    intro x hx
    rw [hU_eq x hx, hu_def]
  -- ## Step 6: the unit log pole of `U` at `b`
  have hEq_bdd : ∃ M : ℝ, ∃ V : Set X, V ∈ nhds b ∧ ∀ x ∈ V, x ≠ b → |E_q x| ≤ M := by
    have hbq : b ∈ Set.univ \ ({q} : Set X) := ⟨trivial, by simpa using hqb.symm⟩
    have hcont : ContinuousAt E_q b := (hEq_harm b hbq).continuousAt
    have hset : {y : ℝ | |y - E_q b| < 1} ∈ nhds (E_q b) :=
      (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds
        (by simp)
    have hev : ∀ᶠ x in nhds b, |E_q x - E_q b| < 1 := hcont.eventually hset
    obtain ⟨V, hV, hVb⟩ := Filter.eventually_iff_exists_mem.mp hev
    refine ⟨|E_q b| + 1, V, hV, fun x hx _ => ?_⟩
    calc |E_q x| = |(E_q x - E_q b) + E_q b| := by ring_nf
      _ ≤ |E_q x - E_q b| + |E_q b| := abs_add_le _ _
      _ ≤ 1 + |E_q b| := by linarith [hVb x hx]
      _ = |E_q b| + 1 := by ring
  have hU_pole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {b}) b U := by
    obtain ⟨C₁, V₁, hV₁, hb₁⟩ := hEq_bdd
    obtain ⟨C₂, V₂, hV₂, hb₂⟩ := hτ_pole_b
    refine ⟨C₁ + C₂, V₁ ∩ V₂ ∩ ({q}ᶜ), ?_, ?_⟩
    · refine Filter.inter_mem (Filter.inter_mem hV₁ hV₂) ?_
      exact (isClosed_singleton.isOpen_compl).mem_nhds (by simpa using hqb.symm)
    · intro x hx hxmem hxne
      obtain ⟨⟨hx₁, hx₂⟩, hxq⟩ := hx
      have hxq' : x ≠ q := by simpa using hxq
      have h1 : |E_q x| ≤ C₁ := hb₁ x hx₁ hxne
      have h2 : |(-τ) x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖| ≤ C₂ :=
        hb₂ x hx₂ (by simpa using hxne) hxne
      have h3 : U x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖
          = E_q x + ((-τ) x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖) := by
        rw [hUeq' x hxq']
        simp only [Pi.neg_apply]
        ring
      rw [h3]
      calc |E_q x + ((-τ) x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖)|
          ≤ |E_q x| + |(-τ) x + Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖| := abs_add_le _ _
        _ ≤ C₁ + C₂ := add_le_add h1 h2
  -- ## Step 7: the holomorphic modulus `Ψ` of `U` (the meromorphic function with a simple
  -- zero at `b` and a simple pole at `q`)
  obtain ⟨Ψ, hΨhol, hΨ0, hΨmod, hΨpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods hU_harm hU_pole
      (hP b U hU_harm hU_pole)
  have hΨne : ∀ x : X, x ≠ b → Ψ x ≠ 0 := by
    intro x hx h0
    have h1 := hΨmod x hx
    rw [h0, norm_zero] at h1
    exact Real.exp_ne_zero (-(U x)) h1.symm
  -- ## Step 8: `V := (Φ - w)·Ψ/(Φ·Φ_q)`, holomorphic on `X` by two removable singularities
  set N : X → ℂ := fun x => (Φ x - w) * Ψ x with hN_def
  have hN_hol : Submission.HolomorphicOnX N Set.univ := by
    rw [hN_def]
    exact (hΦhol.sub (Submission.holomorphicOnX_const w)).mul hΨhol
  have hNq : N q = 0 := by rw [hN_def]; simp [hw]
  obtain ⟨W, hWhol, hWval⟩ :=
    exists_holomorphicOnX_div_of_simple_zero (q := q) (A := N) (B := Φ_q)
      hN_hol hΦq_hol hΦq_pole hΦq_ne hNq
  have hWb : W b = 0 := by
    rw [hWval b (fun h => hqb h.symm), hN_def]
    simp [hΦ0, hΨ0]
  obtain ⟨V, hVhol, hVval⟩ :=
    exists_holomorphicOnX_div_of_simple_zero (q := b) (A := W) (B := Φ)
      hWhol hΦhol hΦpole hΦne hWb
  have hVval_qb : ∀ x : X, x ≠ q → x ≠ b →
      V x = (Φ x - w) * Ψ x / (Φ_q x * Φ x) := by
    intro x hxq hxb
    rw [hVval x hxb, hWval x hxq, hN_def, div_div, mul_comm (Φ_q x) (Φ x)]
  have hVq' : V q' = 0 := by
    rw [hVval_qb q' (fun h => hne h.symm) hq'b]
    rw [hq'w, sub_self, zero_mul, zero_div]
  -- ## Step 9: `V` is bounded
  set K : Set X := K_b ∪ K_q ∪ K_τ ∪ ({b, q} : Set X) with hK_def
  have hK_comp : IsCompact K := by
    rw [hK_def]
    exact ((hKb_comp.union hKq_comp).union hKτ_comp).union
      (((Set.finite_singleton q).insert b).isCompact)
  have hnorm_le : ∀ x : X, x ∉ K → ‖V x‖ ≤ (1 + ‖w‖ * Real.exp 1) * Real.exp 1 := by
    intro x hxK
    have hxb : x ≠ b := fun h => hxK (by rw [hK_def, h]; simp)
    have hxq : x ≠ q := fun h => hxK (by rw [hK_def, h]; simp)
    have hxKb : x ∉ K_b := fun h => hxK (by
      rw [hK_def]
      exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ h)))
    have hxKτ : x ∉ K_τ :=
      fun h => hxK (by rw [hK_def]; exact Set.mem_union_left _ (Set.mem_union_right _ h))
    rw [hVval_qb x hxq hxb]
    -- the modulus identities
    have hPsi_div : ‖Ψ x‖ * (‖Φ_q x‖)⁻¹ = Real.exp (τ x) := by
      rw [hΨmod x hxb, hUeq' x hxq, hΦq_mod x hxq, ← div_eq_mul_inv, ← Real.exp_sub]
      congr 1
      ring
    have hPhi_inv : (‖Φ x‖)⁻¹ = Real.exp (E_b x) := by
      rw [hΦmod x hxb, inv_eq_one_div, ← Real.exp_zero, ← Real.exp_sub]
      congr 1
      ring
    have hnorm : ‖(Φ x - w) * Ψ x / (Φ_q x * Φ x)‖
        = (‖Φ x - w‖ * (‖Φ x‖)⁻¹) * Real.exp (τ x) := by
      rw [norm_div, norm_mul, norm_mul, div_eq_mul_inv, mul_inv_rev]
      rw [show ‖Φ x - w‖ * ‖Ψ x‖ * (‖Φ x‖⁻¹ * ‖Φ_q x‖⁻¹)
          = (‖Φ x - w‖ * ‖Φ x‖⁻¹) * (‖Ψ x‖ * ‖Φ_q x‖⁻¹) by ring]
      rw [hPsi_div, hPhi_inv]
    rw [hnorm]
    have h5a : (‖Φ x‖ + ‖w‖) * (‖Φ x‖)⁻¹ = 1 + ‖w‖ * (‖Φ x‖)⁻¹ := by
      rw [add_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hΦne x hxb))]
    have h2 : ‖Φ x - w‖ * (‖Φ x‖)⁻¹ ≤ 1 + ‖w‖ * Real.exp 1 := by
      have h3 : ‖Φ x - w‖ ≤ ‖Φ x‖ + ‖w‖ := norm_sub_le _ _
      have h4 : ‖Φ x - w‖ * (‖Φ x‖)⁻¹ ≤ (‖Φ x‖ + ‖w‖) * (‖Φ x‖)⁻¹ :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      rw [h5a] at h4
      have h5 : 1 + ‖w‖ * (‖Φ x‖)⁻¹ ≤ 1 + ‖w‖ * Real.exp 1 := by
        rw [hPhi_inv]
        have h7 : Real.exp (E_b x) ≤ Real.exp 1 := Real.exp_le_exp.mpr (hEb_le x hxKb)
        have h8 : ‖w‖ * Real.exp (E_b x) ≤ ‖w‖ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h7 (norm_nonneg w)
        linarith
      linarith
    have h9 : Real.exp (τ x) ≤ Real.exp 1 := Real.exp_le_exp.mpr (hτ_le x hxKτ)
    calc (‖Φ x - w‖ * (‖Φ x‖)⁻¹) * Real.exp (τ x)
        ≤ (1 + ‖w‖ * Real.exp 1) * Real.exp (τ x) :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _))
      _ ≤ (1 + ‖w‖ * Real.exp 1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left h9 (by positivity)
  -- ## Step 10: Liouville
  have hVcont : Continuous V := hVhol.continuous
  obtain ⟨M₁, hM₁⟩ := hK_comp.exists_bound_of_continuousOn hVcont.continuousOn
  obtain ⟨c, hc⟩ := hbddHolo hVhol ⟨max M₁ ((1 + ‖w‖ * Real.exp 1) * Real.exp 1), fun x => by
    by_cases hxK : x ∈ K
    · exact le_trans (hM₁ x hxK) (le_max_left _ _)
    · exact le_trans (hnorm_le x hxK) (le_max_right _ _)⟩
  have hc0 : c = 0 := by
    rw [← hVq']
    exact (hc q').symm
  have hVzero : ∀ x : X, V x = 0 := fun x => by rw [hc x, hc0]
  -- ## Step 11: hence `Φ = w` off `{q,b}`
  have hconst : ∀ x : X, x ≠ b → Φ x = w := by
    intro x hxb
    by_cases hxq : x = q
    · rw [hxq, hw]
    · have h1 : (Φ x - w) * Ψ x / (Φ_q x * Φ x) = 0 := by
        rw [← hVval_qb x hxq hxb, hVzero x]
      have h2 : (Φ x - w) * Ψ x = 0 := by
        rcases div_eq_zero_iff.mp h1 with h | h
        · exact h
        · exact absurd h (mul_ne_zero (hΦq_ne x hxq) (hΦne x hxb))
      have h3 : Φ x - w = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (hΨne x hxb)
      exact sub_eq_zero.mp h3
  -- ## Step 12: contradiction: `Φ` would be constant on a chart ball around `b`
  exfalso
  have hsrc : b ∈ (chartAt ℂ b).source := mem_chart_source ℂ b
  have htgt : (chartAt ℂ b) b ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source hsrc
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ b).open_target.mem_nhds htgt)
  have hvan : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) ρ, z ≠ (chartAt ℂ b) b →
      Φ ((chartAt ℂ b).symm z) - w = 0 := by
    intro z hz hzne
    have hzt : z ∈ (chartAt ℂ b).target := hsub hz
    have hs_ne : (chartAt ℂ b).symm z ≠ b := by
      intro h
      have h2 : (chartAt ℂ b) ((chartAt ℂ b).symm z) = (chartAt ℂ b) b := by rw [h]
      rw [(chartAt ℂ b).right_inv hzt] at h2
      exact hzne h2
    rw [hconst _ hs_ne]
    simp
  have hgan : AnalyticOnNhd ℂ (fun z : ℂ => Φ ((chartAt ℂ b).symm z) - w)
      (Metric.ball ((chartAt ℂ b) b) ρ) := by
    intro z hz
    have hzt : z ∈ (chartAt ℂ b).target := hsub hz
    have hs : (chartAt ℂ b).symm z ∈ (chartAt ℂ b).source := (chartAt ℂ b).map_target hzt
    have h1 : Submission.HolomorphicOnXAt Φ ((chartAt ℂ b).symm z) := hΦhol _ (Set.mem_univ _)
    have h1' := (Submission.HolomorphicOnXAt_iff_chart (f := Φ) (x := (chartAt ℂ b).symm z)
      (y := b) hs).mp h1
    have h3 : AnalyticAt ℂ (fun u : ℂ => Φ ((chartAt ℂ b).symm u))
        ((chartAt ℂ b) ((chartAt ℂ b).symm z)) := h1'
    rw [(chartAt ℂ b).right_inv hzt] at h3
    exact h3.sub analyticAt_const
  have hsphere : (Metric.sphere ((chartAt ℂ b) b) (ρ / 2) : Set ℂ).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ ρ / 2 by linarith)
  obtain ⟨z₀, hz₀s⟩ := hsphere
  have hz₀spec : dist z₀ ((chartAt ℂ b) b) = ρ / 2 := Metric.mem_sphere.mp hz₀s
  have hz₀ball : z₀ ∈ Metric.ball ((chartAt ℂ b) b) ρ := by
    rw [Metric.mem_ball, hz₀spec]
    linarith
  have hz₀ne : z₀ ≠ (chartAt ℂ b) b := by
    intro h
    have h1 : dist z₀ ((chartAt ℂ b) b) = 0 := by rw [h, dist_self]
    rw [h1] at hz₀spec
    linarith
  have hev : (fun z : ℂ => Φ ((chartAt ℂ b).symm z) - w) =ᶠ[nhds z₀] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds z₀ (show (0 : ℝ) < ρ / 4 by linarith),
      isOpen_ne.mem_nhds hz₀ne] with y hy hyne
    refine hvan y ?_ hyne
    rw [Metric.mem_ball] at hy ⊢
    calc dist y ((chartAt ℂ b) b) ≤ dist y z₀ + dist z₀ ((chartAt ℂ b) b) := dist_triangle _ _ _
      _ < ρ / 4 + ρ / 2 := by linarith
      _ < ρ := by linarith
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hgan analyticOnNhd_const
    (convex_ball ((chartAt ℂ b) b) ρ).isPreconnected hz₀ball hev
  have h0 : Φ ((chartAt ℂ b).symm ((chartAt ℂ b) b)) - w = 0 :=
    hEqOn (Metric.mem_ball_self hρ)
  rw [(chartAt ℂ b).left_inv hsrc, hΦ0, zero_sub] at h0
  exact hw_ne (neg_eq_zero.mp h0)

end Work.Drive
