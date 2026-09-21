import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.GlueIdent
import Submission.Work.OddRadon.abelReduceIter_contDiff_eqOn
import Submission.Work.Analysis.Calculus.contDiff_intervalIntegral_fixed
import Submission.Work.OddCurve.LowSlope.abel_integral_trig_substitution_no_hyp

/-!
# The glued-data deviations and the two-power data (`GluePhi`, `GluePsi` vs `glueA`, `glueB`)

The low-slope reconstruction of the odd case solves the two-power system

`R^{2n+2} + r^{2n+2} = Φ/ cos²α`,  `R^{2n+1} - r^{2n+1} = Ψ / cos α`

with `Φ = 2 𝓡^{-1}(GlueF n ρ)`, `Ψ = 2 𝓡^{-1}(GlueG n ρ)` and
`GlueF n ρ = gluedPhi n (radonPhi n ρ) ∘ |·|`, `GlueG n ρ = gluedPsi (radonPsi n ρ) ∘ |·|`.

`GlueDataDefs.glueA`/`glueB` *define* the data of that system by continuing the anchor's
expression `ρ (cos α)^{m} + ρ (-cos α)^{m} - 2` (resp. `ρ (cos α)^{k} - ρ (-cos α)^{k}`) past the
junction `cos α = 4/5`, where it degenerates at `α = π/2`.  This file proves that the continued
data really are the data of the glued datum:

`GluePhi n ρ α = (2 + glueA n ρ α) * cos²α`,  `GluePsi n ρ α = glueB n ρ α * cos α`

for every `α ∈ [0, π/2]`.

Away from `α = π/2` this is immediate from `GlueA_eq`/`GlueB_eq` (the anchor's data on the cap)
and from the definitions of `glueA`/`glueB`.  At `α = π/2` both sides are `0` on the `glueA`,
`glueB` side; the content is that

`GluePhi n ρ (π/2) = 2 * radonInverse n (GlueF n ρ) 0 = 0`

(and the same for `GluePsi`), an *endpoint* statement about the Radon inversion at `0`.  This is
`radonInverse_zero_of_even` below: for an *even* datum whose reduced Abel datum is obtained by
peeling a power of the variable, the Abel integral
`H u = ∫_0^u c Φ c / √(u²-c²) dc` is even, and its difference quotient is eventually bounded by a
constant times `|u|`, hence `deriv H 0 = 0`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## The Abel integral is even for an even density -/

open Work.OddRadon in
/-- `abelDatum n F = (2 |S^{2n-2}|)⁻¹ c^{2n-2} F` is even when `F` is. -/
lemma abelDatum_even (n : ℕ) {F : ℝ → ℝ} (hF : ∀ c : ℝ, F (-c) = F c) :
    ∀ c : ℝ, abelDatum n F (-c) = abelDatum n F c := by
  intro c
  have h2 : 2 * n - 2 = (n - 1) + (n - 1) := by omega
  have hneg : (-c) ^ ((n - 1) + (n - 1)) = c ^ ((n - 1) + (n - 1)) :=
    Even.neg_pow ⟨n - 1, rfl⟩ c
  simp only [Work.OddRadon.abelDatum, h2, hneg, hF c]

open Work.OddRadon in
/-- One exponent-reduction step preserves evenness. -/
lemma abelReduce_even {H : ℝ → ℝ} (hH : ∀ c : ℝ, H (-c) = H c) (α : ℝ) :
    ∀ c : ℝ, abelReduce α H (-c) = abelReduce α H c := by
  intro c
  have hfun : (fun x : ℝ => H (-x)) = H := funext hH
  have hd : deriv H (-c) = -deriv H c := by
    have h1 : deriv (fun x : ℝ => H (-x)) (-c) = -deriv H (-(-c)) := deriv_comp_neg H (-c)
    rw [hfun, neg_neg] at h1
    exact h1
  simp only [Work.OddRadon.abelReduce]
  rw [hd]
  ring

open Work.OddRadon in
/-- The iterated exponent reduction preserves evenness. -/
lemma abelReduceIter_even (k : ℕ) (α : ℝ) {H : ℝ → ℝ} (hH : ∀ c : ℝ, H (-c) = H c) :
    ∀ c : ℝ, abelReduceIter α k H (-c) = abelReduceIter α k H c := by
  induction k generalizing α H with
  | zero => intro c; exact hH c
  | succ k ih =>
      intro c
      rw [abelReduceIter_succ]
      exact ih (H := abelReduce α H) (α - 1) (abelReduce_even hH α) c

/-- **The Abel integral of an even density is even.** -/
lemma abelIntegral_even {Φ : ℝ → ℝ} (hΦ : ∀ c : ℝ, Φ (-c) = Φ c) (u : ℝ) :
    (∫ c in (0:ℝ)..(-u), c * Φ c / Real.sqrt ((-u) ^ 2 - c ^ 2))
      = ∫ c in (0:ℝ)..u, c * Φ c / Real.sqrt (u ^ 2 - c ^ 2) := by
  rw [neg_sq]
  set g : ℝ → ℝ := fun c => c * Φ c / Real.sqrt (u ^ 2 - c ^ 2) with hg
  have hodd : ∀ x : ℝ, g (-x) = -g x := by
    intro x
    simp only [hg]
    rw [hΦ x, neg_sq]
    ring
  have h1 : (∫ x in (-u)..(0:ℝ), g (-x)) = ∫ x in (0:ℝ)..u, g x := by
    have h := intervalIntegral.integral_comp_neg (a := -u) (b := (0:ℝ)) (f := g)
    rw [neg_neg, neg_zero] at h
    exact h
  have h2 : (∫ x in (-u)..(0:ℝ), g (-x)) = -∫ x in (-u)..(0:ℝ), g x := by
    rw [show (∫ x in (-u)..(0:ℝ), g (-x)) = ∫ x in (-u)..(0:ℝ), -g x from
      intervalIntegral.integral_congr (fun x _ => hodd x), intervalIntegral.integral_neg]
  have h3 : (∫ x in (0:ℝ)..(-u), g x) = -∫ x in (-u)..(0:ℝ), g x :=
    intervalIntegral.integral_symm (-u) 0
  rw [h3, ← h2, h1]

/-! ## A smooth function vanishing at `0` is `c` times a smooth function -/

/-- **Hadamard factorization at `0`**: a `C^N` function with `F 0 = 0` is `c ↦ c * G c` with
`G` of class `C^(N-1)`.  The proof uses the integral form `G c = ∫_0^1 F' (t c) dt`. -/
theorem contDiff_eq_mul_of_apply_zero_nat {N : ℕ} (hN : 1 ≤ N) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (((N : ℕ) : ℕ∞) : WithTop ℕ∞) F) (h0 : F 0 = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ((((N - 1 : ℕ)) : ℕ∞) : WithTop ℕ∞) G ∧ ∀ c : ℝ, F c = c * G c := by
  refine ⟨fun c : ℝ => ∫ t in (0:ℝ)..1, deriv F (t * c), ?_, ?_⟩
  · -- smoothness of the parametric integral
    have hderiv : ContDiff ℝ ((((N - 1 : ℕ)) : ℕ∞) : WithTop ℕ∞) (deriv F) := by
      have hF' : ContDiff ℝ (((((N - 1) + 1 : ℕ)) : ℕ∞) : WithTop ℕ∞) F := by
        rw [Nat.sub_add_cancel hN]; exact hF
      exact hF'.deriv'
    refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed (N - 1) ?_
    exact hderiv.comp (contDiff_snd.mul contDiff_fst)
  · intro c
    have hN0 : (((N : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have hN1 : (1 : WithTop ℕ∞) ≤ (((N : ℕ) : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hN
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun s : ℝ => F (s * c)) (c * deriv F (x * c)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => s * c) c x := by
        simpa using (hasDerivAt_id x).mul_const c
      have h2 : HasDerivAt (fun s : ℝ => F (s * c)) (deriv F (x * c) * c) x :=
        (hF.differentiable hN0).differentiableAt.hasDerivAt.comp x h1
      simpa [mul_comm] using h2
    have hcont : Continuous (fun t : ℝ => c * deriv F (t * c)) := by
      have h1 : Continuous (fun t : ℝ => deriv F (t * c)) :=
        (hF.continuous_deriv hN1).comp (continuous_id.mul continuous_const)
      exact continuous_const.mul h1
    have hint : IntervalIntegrable (fun t : ℝ => c * deriv F (t * c)) volume (0:ℝ) 1 :=
      hcont.intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [one_mul, zero_mul, h0, sub_zero] at h
    show F c = c * ∫ t in (0:ℝ)..1, deriv F (t * c)
    rw [← h, intervalIntegral.integral_const_mul]

/-! ## The endpoint `radonInverse n F 0 = 0` for an even datum -/

/-- **The Radon inverse vanishes at `0` for an even datum that is smooth on a right
neighbourhood of `0` and vanishes there.**

Let `F` be even and agree on `(0,b)`, `b ≤ 1`, with a globally `C^{n+2}` function `F'` having
`F' 0 = 0`.  Writing `Φ = abelReduceIter (n-3/2) (n-1) (abelDatum n F)` for the reduced Abel
datum and `H u = ∫_0^u c Φ c / √(u²-c²) dc` (so that `radonInverse n F 0 = (2/π) deriv H 0` by
definition), we show `deriv H 0 = 0`, hence `radonInverse n F 0 = 0`.

The two ingredients are:
* `H` is *even* (because `Φ` is even), so it is enough to control the difference quotient on
  `(0,b)`;
* on `(0,b)` the reduced datum is `Φ c = c · h' c` with `h'` bounded near `0`: `abelDatum n F'`
  is peeled `(n-1)` times by `abelReduceIter_contDiff_eqOn` (using `F' = c · G` from
  `contDiff_eq_mul_of_apply_zero_nat`), and `abelDatum n F = abelDatum n F'` on `(0,b)`.

Then `H u / u = ∫_0^{π/2} sin θ Φ (u sin θ) dθ` (the trigonometric substitution) is bounded by
`(π/2) C u`, so the one-sided difference quotient tends to `0`, and evenness gives the two-sided
statement. -/
theorem radonInverse_zero_of_even (n : ℕ) (hn : 1 ≤ n) {F F' : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hFeven : ∀ c : ℝ, F (-c) = F c)
    (hF' : ContDiff ℝ (((n + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) F')
    (hF'0 : F' 0 = 0)
    (hEq : Set.EqOn F' F (Set.Ioo 0 b)) :
    Work.OddRadon.radonInverse n F 0 = 0 := by
  set Φ : ℝ → ℝ :=
    Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (Work.OddRadon.abelDatum n F) with hΦ
  set H : ℝ → ℝ := fun u : ℝ => ∫ c in (0:ℝ)..u, c * Φ c / Real.sqrt (u ^ 2 - c ^ 2) with hH
  have hradon : Work.OddRadon.radonInverse n F 0 = (2 / Real.pi) * deriv H 0 := by
    rw [hH]
    rw [hΦ]
    rfl
  have hH0 : H 0 = 0 := by
    simp [hH]
  -- evenness of the reduced datum and of `H`
  have hΦeven : ∀ c : ℝ, Φ (-c) = Φ c := by
    rw [hΦ]
    exact abelReduceIter_even (n - 1) ((n : ℝ) - 3 / 2) (abelDatum_even n hFeven)
  have hHeven : ∀ u : ℝ, H (-u) = H u := by
    intro u
    rw [hH]
    exact abelIntegral_even hΦeven u
  -- the reduced datum is `c` times a bounded function on `(0,b)`
  obtain ⟨G, hGsm, hGmul⟩ := contDiff_eq_mul_of_apply_zero_nat (N := n + 2) (by omega) hF' hF'0
  have hGsm' : ContDiff ℝ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) G := by
    rw [show n + 2 - 1 = n + 1 by omega] at hGsm
    exact hGsm
  set h : ℝ → ℝ := fun c => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * G c with hh
  set g : ℝ → ℝ := Work.OddRadon.abelDatum n F' with hg
  have hgm : ∀ c : ℝ, g c = c ^ (2 * n - 1) * h c := by
    intro c
    simp only [hg, hh, Work.OddRadon.abelDatum]
    rw [hGmul c, show 2 * n - 1 = (2 * n - 2) + 1 by omega, pow_succ]
    ring
  have hgsm : ContDiff ℝ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) g := by
    simp only [hg]
    exact ContDiff.mul (ContDiff.mul contDiff_const (contDiff_id.pow (2 * n - 2)))
      (hF'.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2)))
  have hhsm : ContDiff ℝ (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) h := by
    simp only [hh]
    exact ContDiff.mul contDiff_const hGsm'
  obtain ⟨Θ, h', _, hh'sm, hΘeq, hEqOn⟩ :=
    Work.OddRadon.abelReduceIter_contDiff_eqOn ((n : ℝ) - 3 / 2) (n - 1) hgsm hhsm hgm
      (by omega) (by omega)
  -- `Φ` agrees with `Θ` on `(0,b)`
  have habel : Set.EqOn (Work.OddRadon.abelDatum n F) (Work.OddRadon.abelDatum n F')
      (Set.Ioo (0:ℝ) b) := by
    intro c hc
    simp only [Work.OddRadon.abelDatum]
    rw [hEq hc]
  have hcongr : Set.EqOn
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (Work.OddRadon.abelDatum n F))
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) g) (Set.Ioo (0:ℝ) b) := by
    rw [hg]
    exact Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2) habel
  have hΦ_eq : ∀ c ∈ Set.Ioo (0:ℝ) b, Φ c = c * h' c := by
    intro c hc
    have h1 : Φ c = Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) g c := by
      rw [hΦ]
      exact hcongr hc
    rw [h1]
    have h2 : c ∈ Set.Ioo (0:ℝ) 1 := ⟨hc.1, lt_of_lt_of_le hc.2 hb1⟩
    have hexp : 2 * n - 1 - 2 * (n - 1) = 1 := by omega
    rw [hEqOn h2, hΘeq c, hexp, pow_one]
  -- `h'` is bounded on `[0,b]`
  have hh'cont : Continuous h' := hh'sm.continuous
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hh'cont.continuousOn : ContinuousOn h' (Set.Icc (0:ℝ) b))
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, hb.le⟩)
  have hΦbound : ∀ c ∈ Set.Ioo (0:ℝ) b, ‖Φ c‖ ≤ C * c := by
    intro c hc
    have h1 := hC c ⟨hc.1.le, hc.2.le⟩
    rw [Real.norm_eq_abs] at h1
    rw [hΦ_eq c hc, norm_mul, Real.norm_eq_abs, abs_of_pos hc.1]
    calc c * ‖h' c‖ ≤ c * C := mul_le_mul_of_nonneg_left h1 hc.1.le
      _ = C * c := by ring
  -- the trigonometric form of the difference quotient
  have hsub : ∀ u ∈ Set.Ioo (0:ℝ) b, H u / u
      = ∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ * Φ (u * Real.sin θ) := by
    intro u hu
    have hu1 : u < 1 := lt_of_lt_of_le hu.2 hb1
    have h1 : H u = ∫ θ in (0:ℝ)..(Real.pi / 2),
        u * Real.sin θ * Φ (u * Real.sin θ) := by
      show (∫ c in (0:ℝ)..u, c * Φ c / Real.sqrt (u ^ 2 - c ^ 2)) = _
      exact abel_integral_trig_substitution_no_hyp hu.1
    rw [h1, div_eq_inv_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    simp only []
    field_simp
    try ring
  -- the one-sided bound
  have hbound_pos : ∀ u ∈ Set.Ioo (0:ℝ) b, ‖H u / u‖ ≤ (Real.pi / 2) * C * u := by
    intro u hu
    rw [hsub u hu]
    calc ‖∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ * Φ (u * Real.sin θ)‖
        ≤ (C * u) * |Real.pi / 2 - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro θ hθ
          rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
          by_cases h0 : θ = 0
          · simp only [h0, Real.sin_zero, mul_zero, zero_mul, norm_zero]
            exact mul_nonneg hCnn hu.1.le
          · have hsin_pos : 0 < Real.sin θ :=
              Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
            have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
            have hmem : u * Real.sin θ ∈ Set.Ioo (0:ℝ) b := by
              refine ⟨mul_pos hu.1 hsin_pos, ?_⟩
              calc u * Real.sin θ ≤ u * 1 := mul_le_mul_of_nonneg_left hsin_le hu.1.le
                _ = u := mul_one u
                _ < b := hu.2
            rw [norm_mul, Real.norm_eq_abs, abs_of_pos hsin_pos]
            calc Real.sin θ * ‖Φ (u * Real.sin θ)‖
                ≤ Real.sin θ * (C * (u * Real.sin θ)) :=
                  mul_le_mul_of_nonneg_left (hΦbound _ hmem) hsin_pos.le
              _ = C * u * Real.sin θ ^ 2 := by ring
              _ ≤ C * u * 1 := by
                  have h2 : Real.sin θ ^ 2 ≤ 1 := by nlinarith
                  exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hCnn hu.1.le)
              _ = C * u := by ring
      _ = (Real.pi / 2) * C * u := by
          rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 2)]
          ring
  -- the two-sided bound and the limit
  have hbound : ∀ᶠ u in 𝓝[≠] (0:ℝ), ‖H u / u‖ ≤ (Real.pi / 2) * C * ‖u‖ := by
    have hmem : Set.Ioo (-b) b ∈ 𝓝[≠] (0:ℝ) :=
      Filter.mem_of_superset
        (Filter.mem_inf_of_left (Ioo_mem_nhds (show -b < (0:ℝ) by linarith) hb))
        (fun x hx => hx)
    filter_upwards [hmem, self_mem_nhdsWithin] with u hu hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpos : -u ∈ Set.Ioo (0:ℝ) b := ⟨by linarith, by linarith [hu.1]⟩
      have h1 : ‖H u / u‖ = ‖H (-u) / (-u)‖ := by
        have h2 : H u / u = -(H (-u) / (-u)) := by
          rw [← hHeven u, div_eq_inv_mul, div_eq_inv_mul, inv_neg]
          ring
        rw [h2, norm_neg]
      have h2 : ‖u‖ = -u := by rw [Real.norm_eq_abs, abs_of_neg hlt]
      rw [h1, h2]
      exact hbound_pos (-u) hpos
    · have hpos : u ∈ Set.Ioo (0:ℝ) b := ⟨hgt, hu.2⟩
      have h2 : ‖u‖ = u := by rw [Real.norm_eq_abs, abs_of_pos hgt]
      rw [h2]
      exact hbound_pos u hpos
  have htendsto : Tendsto (fun u : ℝ => H u / u) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun u => norm_nonneg _) hbound ?_
    have hcont : Continuous fun u : ℝ => (Real.pi / 2) * C * ‖u‖ := by fun_prop
    have hf0 : (fun u : ℝ => (Real.pi / 2) * C * ‖u‖) 0 = 0 := by simp
    have ht : Tendsto (fun u : ℝ => (Real.pi / 2) * C * ‖u‖) (𝓝 0) (𝓝 0) := by
      simpa only [hf0] using hcont.tendsto 0
    exact ht.mono_left nhdsWithin_le_nhds
  have hHas : HasDerivAt H 0 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hslope : slope H 0 = fun u : ℝ => H u / u := by
      funext u
      rw [slope_fun_def]
      simp only [vsub_eq_sub, sub_zero, hH0, smul_eq_mul, div_eq_inv_mul]
    rw [hslope]
    exact htendsto
  rw [hradon, hHas.deriv, mul_zero]

/-! ## The applications to the two glued data -/

/-- **A datum whose profile is `γ` has vanishing inverse value at `0`**, provided `γ` is smooth on
`[-1/2,1/2]` and `γ 0 = 0`.

The datum is globalized by replacing `γ` with `taylorExtend γ (n+2) (-1/2) (1/2)` inside the
integral representation `radonProfile_eq_cos_any`, which gives a globally smooth `F'` agreeing
with `F` on `(0,1/2)`. -/
theorem radonInverse_zero_of_radonProfile (n : ℕ) (hn : 1 ≤ n) {γ F : ℝ → ℝ}
    (hγ : ContDiffOn ℝ (((n + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) γ (Set.Icc (-(1/2 : ℝ)) (1/2)))
    (hγ0 : γ 0 = 0)
    (hFeven : ∀ c : ℝ, F (-c) = F c)
    (hF : ∀ c ∈ Set.Ioo (0:ℝ) (1/2), F c = Work.OddRadon.radonProfile (2 * n + 1) γ c) :
    Work.OddRadon.radonInverse n F 0 = 0 := by
  set γg : ℝ → ℝ := Commons.Analysis.Calculus.taylorExtend γ (n + 2) (-(1/2)) (1/2) with hγg
  have hγgsm : ContDiff ℝ (((n + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) γg := by
    rw [hγg]
    exact Commons.Analysis.Calculus.contDiff_taylorExtend (n + 2) (by norm_num) hγ
  have hγgeq : ∀ c ∈ Set.Icc (-(1/2 : ℝ)) (1/2), γg c = γ c := by
    intro c hc
    rw [hγg]
    exact Commons.Analysis.Calculus.taylorExtend_eqOn_Icc hc
  have hγg0 : γg 0 = 0 := by
    rw [hγgeq 0 ⟨by norm_num, by norm_num⟩, hγ0]
  set F' : ℝ → ℝ := fun c : ℝ => Work.OddRadon.sphereArea (2 * n - 2) *
    ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Real.cos θ ^ (2 * n - 2) * γg (c * Real.sin θ)
    with hF'
  have hF'sm : ContDiff ℝ (((n + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) F' := by
    rw [hF']
    refine ContDiff.mul contDiff_const ?_
    refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed (n + 2) ?_
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hγgsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hF'0 : F' 0 = 0 := by
    rw [hF']
    simp [hγg0]
  have hF'eq : Set.EqOn F' F (Set.Ioo (0:ℝ) (1/2)) := by
    intro c hc
    rw [hF', hF c hc, Work.OddCurve.LowSlope.radonProfile_eq_cos_any n hn γ c]
    simp only []
    have h2 : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * γg (c * Real.sin θ))
        = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * γ (c * Real.sin θ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only []
      have hsin : |Real.sin θ| ≤ 1 := by
        rw [abs_le]; exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
      have hle : |c * Real.sin θ| ≤ 1/2 := by
        rw [abs_mul, abs_of_pos hc.1]
        calc c * |Real.sin θ| ≤ c * 1 := mul_le_mul_of_nonneg_left hsin hc.1.le
          _ = c := mul_one c
          _ ≤ 1/2 := hc.2.le
      rw [hγgeq (c * Real.sin θ) (abs_le.mp hle)]
    rw [h2]
  exact radonInverse_zero_of_even n hn (by norm_num) (by norm_num) hFeven hF'sm hF'0 hF'eq

/-- **The endpoint value of the inverse of the first glued datum.** -/
theorem radonInverse_GlueF_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    Work.OddRadon.radonInverse n (GlueF n ρ) 0 = 0 := by
  have hsub : Set.Icc (-(1/2 : ℝ)) (1/2) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine radonInverse_zero_of_radonProfile n hn (γ := fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2))
    ?_ ?_ (GlueF_even n ρ) ?_
  · refine ((contDiffOn_id.pow 2).mul ((hρ.mono hsub).pow (2 * n + 2))).of_le ?_
    exact_mod_cast (le_top : ((n + 2 : ℕ) : ℕ∞) ≤ ⊤)
  · simp
  · intro c hc
    have h4 : c < 4 / 5 := by linarith [hc.2]
    show gluedPhi n (Work.OddCurve.LowSlope.radonPhi n ρ) |c|
      = Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) c
    rw [abs_of_pos hc.1, gluedPhi_of_lt hc.1.le h4]
    rfl

/-- **The endpoint value of the inverse of the second glued datum.** -/
theorem radonInverse_GlueG_zero (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    Work.OddRadon.radonInverse n (GlueG n ρ) 0 = 0 := by
  have hsub : Set.Icc (-(1/2 : ℝ)) (1/2) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine radonInverse_zero_of_radonProfile n hn (γ := fun u : ℝ => u * ρ u ^ (2 * n + 1))
    ?_ ?_ (GlueG_even n ρ) ?_
  · refine ((contDiffOn_id.mul ((hρ.mono hsub).pow (2 * n + 1))).of_le ?_)
    exact_mod_cast (le_top : ((n + 2 : ℕ) : ℕ∞) ≤ ⊤)
  · simp
  · intro c hc
    have h4 : c < 4 / 5 := by linarith [hc.2]
    show gluedPsi (Work.OddCurve.LowSlope.radonPsi n ρ) |c|
      = Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1)) c
    rw [abs_of_pos hc.1, gluedPsi_of_lt hc.1.le h4]
    rfl

/-! ## The glued deviations vs the continued two-power data -/

/-- **The continued two-power data of the low-slope step agree with the glued datum's inverse.**

For every `α ∈ [0, π/2]`,
`GluePhi n ρ α = (2 + glueA n ρ α) * cos²α` and `GluePsi n ρ α = glueB n ρ α * cos α`.

Away from `α = π/2` this just unfolds the definitions of `glueA`/`glueB` (which continue the
anchor's data past the junction `cos α = 4/5`) together with `GlueA_eq`/`GlueB_eq`; at
`α = π/2` both sides are `0` on the `glueA`/`glueB` side, and the content is the endpoint
statement `radonInverse n (GlueF n ρ) 0 = radonInverse n (GlueG n ρ) 0 = 0`
(`radonInverse_GlueF_zero`, `radonInverse_GlueG_zero`). -/
theorem glue_deviations_eq (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      Work.OddCurve.LowSlope.GluePhi n ρ α =
          (2 + Work.OddCurve.LowSlope.glueA n ρ α) * Real.cos α ^ 2 ∧
        Work.OddCurve.LowSlope.GluePsi n ρ α =
          Work.OddCurve.LowSlope.glueB n ρ α * Real.cos α := by
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  by_cases hcos : Real.cos α = 0
  · have hpi : α = Real.pi / 2 := by
      have h1 : ¬ α < Real.pi / 2 := by
        intro hlt
        have h2 : 0 < Real.cos α := by
          apply Real.cos_pos_of_mem_Ioo
          exact ⟨by linarith [hα0, Real.pi_pos], hlt⟩
        linarith
      exact le_antisymm hα1 (not_lt.mp h1)
    subst hpi
    constructor
    · rw [GluePhi, Real.cos_pi_div_two, radonInverse_GlueF_zero n hn hρ, mul_zero]
      simp
    · rw [GluePsi, Real.cos_pi_div_two, radonInverse_GlueG_zero n hn hρ, mul_zero]
      simp
  · have hcosnn : 0 ≤ Real.cos α := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by linarith [hα0, Real.pi_pos], hα1⟩
    have hcospos : 0 < Real.cos α := lt_of_le_of_ne hcosnn (Ne.symm hcos)
    by_cases hge : (4 : ℝ) / 5 ≤ Real.cos α
    · constructor
      · rw [glueA_of_ge hge]
        simp only [GlueA]
        field_simp
        try ring
      · rw [glueB_of_ge hge]
        simp only [GlueB]
        field_simp
        try ring
    · have hlt : Real.cos α < 4 / 5 := not_le.mp hge
      constructor
      · rw [glueA_of_lt hlt, ← GlueA_eq n hn hρ hcospos hlt]
        simp only [GlueA]
        field_simp
        try ring
      · rw [glueB_of_lt hlt, ← GlueB_eq n hn hρ hcospos hlt]
        simp only [GlueB]
        field_simp
        try ring

end

end Work.OddCurve.LowSlope

