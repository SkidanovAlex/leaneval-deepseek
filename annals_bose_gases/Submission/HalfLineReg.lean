import Mathlib.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ChallengeDeps
import Submission.SndClassify
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# 1D regularity from the weak form on a half-line (Layer 3, scattering)

For a *radial* weak scattering solution `w` of a radial potential `v`, the
profile `u(r) := r · radialProfile w r` satisfies the 1D weak equation

    ∫_{r>a} u·χ'' = ∫_{r>a} h·χ        (∀ χ ∈ C∞c((a,∞)))          (W)

where `h(r) := −(1/2)·r·vprof(r)·(1−f(r))` (`Scat1D.scattering_1D_weak_equation`).
This module proves the *regularity* content of (W): if `h` is (globally)
integrable on `(a,∞)`, then `u` agrees a.e. with a function `U ∈ C¹((a,∞))`
whose derivative is absolutely continuous and satisfies `U'' = h` a.e. —
i.e. the weak equation (W) upgrades to a classical ODE in the Carathéodory
sense.  This is the gateway to the maximum-principle bounds
`0 ≤ ω ≤ 1` for the scattering solution.

## Proof route (the child should implement, in order)

1. **The twice-primitive of `h`.**  Define
   `F x := ∫ t in a..x, h t` (a continuous function on `(a,∞)`, since `h` is
   integrable) and `P x := ∫ s in a..x, F s`.  Prove:
   * `∀ x > a, HasDerivAt P (F x) x` (FTC-1, `F` continuous at `x`); hence
     `deriv P x = F x` for `x > a` and `P` is continuous (differentiable) on
     `(a,∞)`;
   * `∀ᵐ x, a < x → HasDerivAt F (h x) x` — the Lebesgue differentiation
     theorem: extend `h` by `0` on `(−∞,a]` to a globally (locally)
     integrable function `h₀`, then apply
     `MeasureTheory.LocallyIntegrable.ae_hasDerivAt_integral h₀`
     (`Mathlib/.../IntervalIntegral/LebesgueDifferentiationThm.lean`) with
     `c := a`, restricting to `x > a` where `∫ a..x, h₀ = ∫ a..x, h` (they
     agree a.e. on `[a,x]`, endpoints have measure zero).
   * the *weak identity for `P`*: `∀ χ ∈ C∞c((a,∞))`,
     `∫ P·χ'' = ∫ h·χ` (both sides over `(a,∞)`).  Integrate by parts twice
     on a bounded interval `[a', b']` containing the support of `χ` (so
     `χ`, `χ'` vanish at the endpoints): use
     `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` /
     `integral_deriv_mul_eq_sub` from
     `Mathlib/.../IntervalIntegral/AbsolutelyContinuousFun.lean`; for this
     you need `P` and `P' = F` absolutely continuous on `[a', b']`, which
     follows from the indefinite-integral absolute-continuity results in
     that same file (indefinite integrals of integrable functions are
     absolutely continuous), and `deriv P = F`, `F' = h` a.e. (from the
     previous two bullets).

2. **Difference has zero weak second derivative.**  From the hypothesis `(W)`
   for `u` and the weak identity for `P`, show
   `∀ χ ∈ C∞c((a,∞)): ∫_{r>a} (u − P)·χ'' = 0`.  Apply
   `SndClassify.affine_ae_of_snd_annihilates` (already in the corpus,
   imported above) to `(u − P)` to get `∃ A B`, `u x − P x = A + B·x` a.e.
   on `(a,∞)`.  [You need local integrability of `u − P` on `(a,∞)`: `u`
   locally integrable by hypothesis, `P` continuous; combine.]

3. **Assemble `U`.**  Set `U x := A + B·x + P x`.  Then `u = U` a.e. on
   `(a,∞)`; `∀ x > a, HasDerivAt U (B + F x) x` (derivative of the affine
   part plus `P`); and since `deriv U = B + F` pointwise on `(a,∞)`, the
   Lebesgue-differentiation step gives
   `∀ᵐ x, a < x → HasDerivAt (deriv U) (h x) x`.

## Notes on hypotheses and conventions

* `u` is only assumed locally integrable on `(a,∞)` (with respect to the
  Lebesgue measure `volume`), matching the corpus convention
  `MeasureTheory.LocallyIntegrableOn u (Set.Ioi a) volume` used throughout
  `SndClassify`/`ProfileEq1D`.  `h` is assumed *globally* integrable on
  `(a,∞)` (`MeasureTheory.IntegrableOn h (Set.Ioi a) volume`).
* Test-function support condition is stated pointwise:
  `(∀ r : ℝ, χ r ≠ 0 → a < r)`, the corpus idiom (equivalent to
  `tsupport χ ⊆ Set.Ioi a`).
* The conclusion uses the `∀ᵐ x, a < x → ...` idiom (filter
  `∀ᵐ x, a < x → p x` means `p` holds for a.e. `x > a`).  Use `Set.Ioi`
  throughout; interval integrals `∫ t in a..x, f t` need `open scoped
  Interval`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Function Set
open scoped ContDiff Topology Real Interval

/-- The (definite) antiderivative from `a` of a function. -/
noncomputable def primitive (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in a..x, f t

/-- Extension of `h` by zero below `a`.  Globally integrable when `h` is integrable on `(a,∞)`. -/
lemma ext_integrable {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    MeasureTheory.Integrable (fun x : ℝ => if a < x then h x else 0) := by
  let hz : ℝ → ℝ := fun x => if a < x then h x else 0
  have hz_on : MeasureTheory.IntegrableOn hz (Set.Ioi a) volume := by
    refine hh.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx' : a < x := by simpa using hx
    dsimp [hz]
    simp [hx']
  refine hz_on.integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  dsimp [hz]
  have hn : ¬ a < x := by simpa using hx
  simp [hn]

/-- `h` is interval-integrable on `a..x` for `x ≥ a`. -/
lemma h_intervalIntegrable_ge {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a ≤ x) :
    IntervalIntegrable h volume a x := by
  rw [intervalIntegrable_iff]
  have hsub : Ι a x ⊆ Set.Ioi a := by
    intro t ht
    have ht' : t ∈ Set.Ioc a x := by simpa [uIoc_of_le hx] using ht
    exact ht'.1
  exact hh.mono_set hsub

/-- The primitive of `h` equals the primitive of the zero-extension on `[a, ∞)`. -/
lemma primitive_eq_ext_ge {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    ∀ y : ℝ, a ≤ y → primitive a h y = primitive a (fun x => if a < x then h x else 0) y := by
  intro y hy
  unfold primitive
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  have ht' : t ∈ Set.Ioc a y := by simpa [uIoc_of_le hy] using ht
  simp [ht'.1]

/-- `primitive a h` is continuous on `[a, ∞)`. -/
lemma primitive_continuousOn_Ici {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    ContinuousOn (primitive a h) (Set.Ici a) := by
  let hz : ℝ → ℝ := fun x => if a < x then h x else 0
  have hz_int : MeasureTheory.Integrable hz := by
    simpa [hz] using ext_integrable hh
  have hG_cont : Continuous (primitive a hz) :=
    hz_int.continuous_primitive a
  refine (hG_cont.continuousOn).congr ?_
  intro y hy
  exact primitive_eq_ext_ge hh y hy



/-- Lebesgue differentiation: `primitive a h` is differentiable a.e. on `(a,∞)`
with derivative `h`. -/
lemma primitive_ae_hasDerivAt {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    ∀ᵐ x : ℝ, a < x → HasDerivAt (primitive a h) (h x) x := by
  let hz : ℝ → ℝ := fun x => if a < x then h x else 0
  have hz_int : MeasureTheory.Integrable hz := by
    simpa [hz] using ext_integrable hh
  have hloc : LocallyIntegrable hz volume := hz_int.locallyIntegrable
  have hLDT : ∀ᵐ x : ℝ, ∀ c : ℝ, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, hz t) (hz x) x :=
    LocallyIntegrable.ae_hasDerivAt_integral (f := hz) hloc
  filter_upwards [hLDT] with x hxLDT hxa
  have hmain : HasDerivAt (primitive a hz) (hz x) x := by
    exact hxLDT a
  have hcongr : primitive a h =ᶠ[𝓝 x] primitive a hz := by
    filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi a)).mem_nhds hxa] with y hy
    dsimp [hz]
    exact primitive_eq_ext_ge hh y hy.le
  have hxder : HasDerivAt (primitive a h) (hz x) x :=
    HasDerivAt.congr_of_eventuallyEq (f := primitive a hz) (f₁ := primitive a h) hmain hcongr
  have hzeq : hz x = h x := by simp [hz, hxa]
  simpa [hzeq] using hxder

/-- `deriv (primitive a h) = h` a.e. on `(a,∞)`. -/
lemma primitive_ae_deriv_eq {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    ∀ᵐ x : ℝ, a < x → deriv (primitive a h) x = h x := by
  filter_upwards [primitive_ae_hasDerivAt hh] with x hx hxa
  exact (hx hxa).deriv



/-- `primitive a h` is interval integrable on `a..x` for `x ≥ a`. -/
lemma primitive_intervalIntegrable_ge {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a ≤ x) :
    IntervalIntegrable (primitive a h) volume a x := by
  apply ContinuousOn.intervalIntegrable_of_Icc hx
  exact (primitive_continuousOn_Ici hh).mono (by intro y hy; exact hy.1)

/-- `primitive a h` is absolutely continuous on `[a, x]`. -/
lemma primitive_absolutelyContinuousOn_ge {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a ≤ x) :
    AbsolutelyContinuousOnInterval (primitive a h) a x := by
  exact (h_intervalIntegrable_ge hh hx).absolutelyContinuousOnInterval_intervalIntegral
    (f := h) (a := a) (b := x) (c := a) left_mem_uIcc

/-- Second primitive `primitive a (primitive a h)` is absolutely continuous on `[a, x]`. -/
lemma second_primitive_absolutelyContinuousOn_ge {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a ≤ x) :
    AbsolutelyContinuousOnInterval (primitive a (primitive a h)) a x := by
  exact (primitive_intervalIntegrable_ge hh hx).absolutelyContinuousOnInterval_intervalIntegral
    (f := primitive a h) (a := a) (b := x) (c := a) left_mem_uIcc

/-- FTC-1 for the second primitive: `d/dx ∫_a^x F = F x` on `(a, ∞)`. -/
lemma second_primitive_hasDerivAt {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a < x) :
    HasDerivAt (primitive a (primitive a h)) (primitive a h x) x := by
  have hFint : IntervalIntegrable (primitive a h) volume a x :=
    primitive_intervalIntegrable_ge hh hx.le
  have hFcont : ContinuousAt (primitive a h) x :=
    (primitive_continuousOn_Ici hh).continuousAt (Ici_mem_nhds hx)
  have hFmeas : StronglyMeasurableAtFilter (primitive a h) (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi a) isOpen_Ioi
      (fun y hy => (primitive_continuousOn_Ici hh).continuousAt (Ici_mem_nhds hy)) x hx
  exact (intervalIntegral.integral_hasStrictDerivAt_right (f := primitive a h) hFint hFmeas hFcont).hasDerivAt


/-- The second primitive is continuous on `(a,∞)`. -/
lemma second_primitive_continuousOn_Ioi {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) :
    ContinuousOn (primitive a (primitive a h)) (Set.Ioi a) := by
  intro x hx
  exact (second_primitive_hasDerivAt hh hx).continuousAt.continuousWithinAt

/-- `deriv` of the second primitive equals the first primitive on `(a,∞)`. -/
lemma deriv_second_primitive_eq {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {x : ℝ} (hx : a < x) :
    deriv (primitive a (primitive a h)) x = primitive a h x := by
  exact (second_primitive_hasDerivAt hh hx).deriv



/-- If a function is eventually zero at a point, its derivative vanishes there. -/
lemma deriv_eq_zero_of_eventually_const_zero {f : ℝ → ℝ} {x : ℝ}
    (hf : f =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ))) : deriv f x = 0 := by
  have h : HasDerivAt f 0 x := by
    simpa using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hf
  exact h.deriv

/-- A function vanishing in a neighbourhood of a point outside its `tsupport` is eventually zero. -/
lemma eventually_zero_of_not_mem_tsupport {χ : ℝ → ℝ} {z : ℝ} (hz : z ∉ tsupport χ) :
    χ =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
  have hcompl : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  filter_upwards [hcompl.mem_nhds (by simpa using hz)] with y hy
  by_contra h
  exact hy (subset_tsupport χ h)

/-- Outside the `tsupport` of a (smooth enough) function, it and its derivatives vanish. -/
lemma zero_derivs_of_not_mem_tsupport {χ : ℝ → ℝ} {z : ℝ} (hz : z ∉ tsupport χ) :
    χ z = 0 ∧ deriv χ z = 0 ∧ deriv (deriv χ) z = 0 := by
  have hz0 : χ z = 0 := by
    by_contra h
    exact hz (subset_tsupport χ h)
  have hdz : deriv χ z = 0 := by
    exact deriv_eq_zero_of_eventually_const_zero (f := χ) (x := z)
      (eventually_zero_of_not_mem_tsupport hz)
  have hderivnear : deriv χ =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    have hcompl : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hcompl.mem_nhds (by simpa using hz)] with y hy
    exact deriv_eq_zero_of_eventually_const_zero (f := χ) (x := y)
      (eventually_zero_of_not_mem_tsupport hy)
  have hdd : deriv (deriv χ) z = 0 := by
    exact deriv_eq_zero_of_eventually_const_zero (f := deriv χ) (x := z) hderivnear
  exact ⟨hz0, hdz, hdd⟩

/-- For a test function on `(a,∞)`, its `tsupport` is contained in `[a,∞)`. -/
lemma tsupport_subset_Ici_of_test {a : ℝ} {χ : ℝ → ℝ} (hχsup : ∀ r : ℝ, χ r ≠ 0 → a < r) :
    tsupport χ ⊆ Set.Ici a := by
  have hsub : Function.support χ ⊆ Set.Ici a := by
    intro x hx
    exact (hχsup x hx).le
  rw [tsupport]
  exact closure_minimal hsub isClosed_Ici

/-- Any test function on `(a,∞)` vanishes, together with its derivatives, below `a`. -/
lemma zero_derivs_of_le {a : ℝ} {χ : ℝ → ℝ} (hχsup : ∀ r : ℝ, χ r ≠ 0 → a < r) {z : ℝ}
    (hz : z < a) : χ z = 0 ∧ deriv χ z = 0 ∧ deriv (deriv χ) z = 0 := by
  have htsub : tsupport χ ⊆ Set.Ici a := tsupport_subset_Ici_of_test hχsup
  have hzts : z ∉ tsupport χ := by
    intro hzt
    have : a ≤ z := htsub hzt
    linarith
  exact zero_derivs_of_not_mem_tsupport hzts

/-- There is an upper bound beyond which a compactly supported test function and its
derivatives vanish. -/
lemma exists_upper_cutoff {a : ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcomp : HasCompactSupport χ)
    (hχsup : ∀ r : ℝ, χ r ≠ 0 → a < r) :
    ∃ d : ℝ, a ≤ d ∧ (∀ r : ℝ, d ≤ r → χ r = 0 ∧ deriv χ r = 0 ∧ deriv (deriv χ) r = 0) := by
  have hK : IsCompact (tsupport χ) := hcomp.isCompact
  rcases hK.bddAbove with ⟨R, hR⟩
  let d : ℝ := max a (R + 1)
  refine ⟨d, ?_, ?_⟩
  · exact le_max_left a (R + 1)
  · intro r hr
    have hzts : r ∉ tsupport χ := by
      intro hrts
      have hrle : r ≤ R := hR hrts
      have hdR : R + 1 ≤ d := le_max_right a (R + 1)
      have : R + 1 ≤ r := le_trans hdR hr
      linarith
    exact zero_derivs_of_not_mem_tsupport hzts


/-- The double primitive `P = ∫∫h` satisfies `∫ P·χ'' = ∫ h·χ` on `[a,d]` (weak form of `P'' = h`),
whenever `χ` and its derivatives vanish beyond `d`. -/
lemma second_primitive_weak_interval {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {d : ℝ} (had : a ≤ d)
    (hχge : ∀ r : ℝ, d ≤ r → χ r = 0 ∧ deriv χ r = 0 ∧ deriv (deriv χ) r = 0) :
    (∫ x : ℝ in a..d, (primitive a (primitive a h)) x * deriv (deriv χ) x) =
    (∫ x : ℝ in a..d, h x * χ x) := by
  let P : ℝ → ℝ := primitive a (primitive a h)
  let F : ℝ → ℝ := primitive a h
  have hPAC : AbsolutelyContinuousOnInterval P a d := by
    dsimp [P]
    exact second_primitive_absolutelyContinuousOn_ge hh had
  have hχ'AC : AbsolutelyContinuousOnInterval (deriv χ) a d := by
    have hχ' : ContDiff ℝ ∞ (deriv χ) := by
      have hhχ : ContDiff ℝ (∞ + 1) χ := by simpa using hχ
      exact ContDiff.deriv' (n := ∞) hhχ
    have hc : ContDiffOn ℝ 1 (deriv χ) (Set.uIcc a d) :=
      (hχ'.contDiffOn : ContDiffOn ℝ ∞ (deriv χ) (Set.uIcc a d)).of_le (by decide)
    exact ContDiffOn.absolutelyContinuousOnInterval hc
  have hFAC : AbsolutelyContinuousOnInterval F a d := by
    dsimp [F]
    exact primitive_absolutelyContinuousOn_ge hh had
  have hχAC : AbsolutelyContinuousOnInterval χ a d := by
    have hc : ContDiffOn ℝ 1 χ (Set.uIcc a d) :=
      (hχ.contDiffOn : ContDiffOn ℝ ∞ χ (Set.uIcc a d)).of_le (by decide)
    exact ContDiffOn.absolutelyContinuousOnInterval hc
  -- substitution deriv P = F on the interval
  have hsubP : (∫ x : ℝ in a..d, deriv P x * deriv χ x) =
      (∫ x : ℝ in a..d, F x * deriv χ x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x hx
    have hxa : a < x := by
      have hx' : x ∈ Set.Ioc a d := by simpa [uIoc_of_le had] using hx
      exact hx'.1
    have hdP : deriv P x = F x := by
      dsimp [P, F]
      exact deriv_second_primitive_eq hh hxa
    rw [hdP]
  -- substitution deriv F = h a.e. on the interval
  have hsubF : (∫ x : ℝ in a..d, deriv F x * χ x) =
      (∫ x : ℝ in a..d, h x * χ x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [primitive_ae_deriv_eq hh] with x hx hxa
    have hxlt : a < x := by
      have hx' : x ∈ Set.Ioc a d := by simpa [uIoc_of_le had] using hxa
      exact hx'.1
    have hdF : deriv F x = h x := hx hxlt
    rw [hdF]
  -- boundary values
  have hPa0 : P a = 0 := by dsimp [P]; simp [primitive]
  have hFa0 : F a = 0 := by dsimp [F]; simp [primitive]
  have hχd : χ d = 0 := (hχge d le_rfl).1
  have hχ'd : deriv χ d = 0 := (hχge d le_rfl).2.1
  -- integration by parts, twice
  have hI1raw := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    (f := P) (g := deriv χ) (a := a) (b := d) hPAC hχ'AC
  have hI1 : (∫ x : ℝ in a..d, P x * deriv (deriv χ) x) =
      - (∫ x : ℝ in a..d, F x * deriv χ x) := by
    have hbd1 : P d * deriv χ d - P a * deriv χ a = 0 := by simp [hχ'd, hPa0]
    rw [hI1raw, hbd1, hsubP]
    ring
  have hI2raw := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    (f := F) (g := χ) (a := a) (b := d) hFAC hχAC
  have hI2 : (∫ x : ℝ in a..d, F x * deriv χ x) =
      - (∫ x : ℝ in a..d, h x * χ x) := by
    have hbd2 : F d * χ d - F a * χ a = 0 := by simp [hχd, hFa0]
    rw [hI2raw, hbd2, hsubF]
    ring
  calc
    (∫ x : ℝ in a..d, (primitive a (primitive a h)) x * deriv (deriv χ) x)
        = - (∫ x : ℝ in a..d, F x * deriv χ x) := by simpa [P, F] using hI1
    _ = - (- (∫ x : ℝ in a..d, h x * χ x)) := by rw [hI2]
    _ = (∫ x : ℝ in a..d, h x * χ x) := by simp


/-- The weak form of `P'' = h` on the whole half-line: `∫_{Ioi a} P·χ'' = ∫_{Ioi a} h·χ`. -/
lemma second_primitive_weak_Ioi {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsup : ∀ r : ℝ, χ r ≠ 0 → a < r) {d : ℝ}
    (had : a ≤ d) (hχge : ∀ r : ℝ, d ≤ r → χ r = 0 ∧ deriv χ r = 0 ∧ deriv (deriv χ) r = 0) :
    (∫ x : ℝ in Set.Ioi a, (primitive a (primitive a h)) x * deriv (deriv χ) x) =
    (∫ x : ℝ in Set.Ioi a, h x * χ x) := by
  let P : ℝ → ℝ := primitive a (primitive a h)
  have hintv := second_primitive_weak_interval hh hχ had hχge
  have hPa0 : P a = 0 := by dsimp [P]; simp [primitive]
  have hsuppP : Function.support (fun x : ℝ => P x * deriv (deriv χ) x) ⊆ Set.Ioc a d := by
    intro x hx
    have hχx : deriv (deriv χ) x ≠ 0 := by
      intro h
      exact hx (by simp [h])
    have hxlt : ¬ x < a := by
      intro hxlt
      exact hχx (zero_derivs_of_le hχsup hxlt).2.2
    have hxne : x ≠ a := by
      intro hxa
      subst x
      exact hx (by simp [P, hPa0])
    have hxle : ¬ d < x := by
      intro hdx
      have : d ≤ x := hdx.le
      exact hχx (hχge x this).2.2
    constructor
    · exact lt_of_le_of_ne (not_lt.mp hxlt) (Ne.symm hxne)
    · exact le_of_not_gt hxle
  have hsupph : Function.support (fun x : ℝ => h x * χ x) ⊆ Set.Ioc a d := by
    intro x hx
    have hχx : χ x ≠ 0 := by
      intro h
      exact hx (by simp [h])
    constructor
    · exact hχsup x hχx
    · by_contra hxd
      have hdx : d < x := lt_of_not_ge hxd
      exact hχx (hχge x hdx.le).1
  have hχ0_le : ∀ x : ℝ, x ≤ a → χ x = 0 := by
    intro x hx
    by_contra h
    exact (not_lt_of_ge hx) (hχsup x h)
  calc
    (∫ x : ℝ in Set.Ioi a, P x * deriv (deriv χ) x)
        = (∫ x : ℝ, P x * deriv (deriv χ) x) := by
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Set.Ioi a) (f := fun x : ℝ => P x * deriv (deriv χ) x) ?_
      intro x hx
      have hxa : x ≤ a := le_of_not_gt hx
      rcases lt_or_eq_of_le hxa with hxlt | hxeq
      · have hzero := (zero_derivs_of_le hχsup hxlt).2.2
        simp [hzero]
      · subst x
        simp [P, hPa0]
    _ = (∫ x : ℝ in a..d, P x * deriv (deriv χ) x) := by
      exact (intervalIntegral.integral_eq_integral_of_support_subset hsuppP).symm
    _ = (∫ x : ℝ in a..d, h x * χ x) := by simpa [P] using hintv
    _ = (∫ x : ℝ, h x * χ x) := by
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupph
    _ = (∫ x : ℝ in Set.Ioi a, h x * χ x) := by
      refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Set.Ioi a) (f := fun x : ℝ => h x * χ x) ?_).symm
      intro x hx
      have hxa : x ≤ a := le_of_not_gt hx
      simp [hχ0_le x hxa]


/-- Derivative of a `C^∞` function is `C^∞`. -/
lemma contDiff_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) := by
  have hs : ContDiff ℝ (∞ + 1) f := by simpa using hf
  exact ContDiff.deriv' (n := ∞) hs

/-- The second primitive of `h` times `χ''` is integrable on `(a,∞)` for every test function. -/
lemma second_primitive_mul_smooth_integrableOn {a : ℝ} {h : ℝ → ℝ}
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχcomp : HasCompactSupport χ)
    (hχsup : ∀ r : ℝ, χ r ≠ 0 → a < r) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (primitive a (primitive a h)) x * deriv (deriv χ) x)
      (Set.Ioi a) volume := by
  rcases exists_upper_cutoff hχ hχcomp hχsup with ⟨d, had, hχge⟩
  let P : ℝ → ℝ := primitive a (primitive a h)
  have hPcont : ContinuousOn P (Set.Icc a d) := by
    have hAC : AbsolutelyContinuousOnInterval P a d := by
      dsimp [P]
      exact second_primitive_absolutelyContinuousOn_ge hh had
    have hUni : UniformContinuousOn P (Set.Icc a d) := by
      simpa [Set.uIcc_of_le had] using hAC.uniformContinuousOn
    exact hUni.continuousOn
  have hχ''cont : ContinuousOn (deriv (deriv χ)) (Set.Icc a d) :=
    (contDiff_deriv (contDiff_deriv hχ)).continuous.continuousOn
  have hprod_cont : ContinuousOn (fun x : ℝ => P x * deriv (deriv χ) x) (Set.Icc a d) :=
    hPcont.mul hχ''cont
  have hz : ∀ x : ℝ, x ∉ Set.Icc a d → P x * deriv (deriv χ) x = 0 := by
    intro x hx
    have hxlt : x < a ∨ d < x := by
      by_contra h
      have hxa : a ≤ x := by
        exact le_of_not_gt (fun hxa => h (Or.inl hxa))
      have hxd : x ≤ d := by
        exact le_of_not_gt (fun hxd => h (Or.inr hxd))
      exact hx ⟨hxa, hxd⟩
    rcases hxlt with hxlt | hxgt
    · have hzero := (zero_derivs_of_le hχsup hxlt).2.2
      simp [hzero]
    · have hzero := (hχge x hxgt.le).2.2
      simp [hzero]
  have hprod_int : MeasureTheory.Integrable (fun x : ℝ => P x * deriv (deriv χ) x) volume := by
    exact (ContinuousOn.integrableOn_Icc hprod_cont).integrable_of_forall_notMem_eq_zero hz
  exact hprod_int.integrableOn

/-- **1D regularity from the weak form on a half-line.**  If `u` is locally
integrable on `(a,∞)`, `h` is integrable on `(a,∞)`, and `u'' = h` in the weak
sense (`∫u·χ'' = ∫h·χ` for every `χ ∈ C∞c((a,∞))`), then `u` agrees a.e. with
the `C¹` function `U(x) := A + B·x + ∫_{a}^{x}∫_{a}^{s} h`, whose derivative
is differentiable a.e. with derivative `h`. -/
theorem weak_snd_regularity_Ioi {a : ℝ} {u h : ℝ → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi a) volume)
    (hh : MeasureTheory.IntegrableOn h (Set.Ioi a) volume)
    (hint : ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → a < r) →
      (∫ x : ℝ in Set.Ioi a, u x * deriv (deriv χ) x) =
      (∫ x : ℝ in Set.Ioi a, h x * χ x)) :
    ∃ A B : ℝ,
      (∀ᵐ x : ℝ, a < x →
        u x = A + B * x + (∫ s : ℝ in a..x, (∫ t : ℝ in a..s, h t))) ∧
      (∀ x : ℝ, a < x →
        HasDerivAt (fun y : ℝ => A + B * y + (∫ s : ℝ in a..y, (∫ t : ℝ in a..s, h t)))
          (B + (∫ t : ℝ in a..x, h t)) x) ∧
      (∀ᵐ x : ℝ, a < x →
        HasDerivAt (deriv (fun y : ℝ => A + B * y + (∫ s : ℝ in a..y, (∫ t : ℝ in a..s, h t))))
          (h x) x) := by
  let P : ℝ → ℝ := primitive a (primitive a h)
  let F : ℝ → ℝ := primitive a h
  -- `u - P` annihilates second derivatives of all test functions on `(a,∞)`
  have hg_ann : ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → a < r) →
      (∫ x : ℝ in Set.Ioi a, (u x - P x) * deriv (deriv χ) x) = 0 := by
    intro χ hχ hχcomp hχsup
    rcases exists_upper_cutoff hχ hχcomp hχsup with ⟨d, had, hχge⟩
    by_cases hfint : MeasureTheory.IntegrableOn
        (fun x : ℝ => (u x - P x) * deriv (deriv χ) x) (Set.Ioi a) volume
    · have hPint : MeasureTheory.IntegrableOn
          (fun x : ℝ => P x * deriv (deriv χ) x) (Set.Ioi a) volume := by
        simpa [P] using second_primitive_mul_smooth_integrableOn hh hχ hχcomp hχsup
      have hsum : (fun x : ℝ => ((u x - P x) * deriv (deriv χ) x) +
          (P x * deriv (deriv χ) x)) =ᵐ[volume.restrict (Set.Ioi a)]
          (fun x : ℝ => u x * deriv (deriv χ) x) := by
        filter_upwards with x
        ring
      have huχ : MeasureTheory.IntegrableOn (fun x : ℝ => u x * deriv (deriv χ) x)
          (Set.Ioi a) volume := (hfint.add hPint).congr_fun_ae hsum
      have hwP : (∫ x : ℝ in Set.Ioi a, P x * deriv (deriv χ) x) =
          (∫ x : ℝ in Set.Ioi a, h x * χ x) := by
        simpa [P] using (second_primitive_weak_Ioi hh hχ hχsup had hχge)
      calc
        (∫ x : ℝ in Set.Ioi a, (u x - P x) * deriv (deriv χ) x)
            = (∫ x : ℝ in Set.Ioi a, (u x * deriv (deriv χ) x) -
                (P x * deriv (deriv χ) x)) := by
              refine MeasureTheory.setIntegral_congr_fun (hs := measurableSet_Ioi) ?_
              intro x hx
              ring
        _ = (∫ x : ℝ in Set.Ioi a, u x * deriv (deriv χ) x) -
            (∫ x : ℝ in Set.Ioi a, P x * deriv (deriv χ) x) := by
              exact MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi a)) huχ hPint
        _ = (∫ x : ℝ in Set.Ioi a, h x * χ x) - (∫ x : ℝ in Set.Ioi a, h x * χ x) := by
              rw [hint χ hχ hχcomp hχsup, hwP]
        _ = 0 := by ring
    · exact MeasureTheory.integral_undef (μ := volume.restrict (Set.Ioi a)) hfint
  -- local integrability of `u - P` on `(a,∞)`
  have hP_li : MeasureTheory.LocallyIntegrableOn P (Set.Ioi a) volume := by
    simpa [P] using second_primitive_continuousOn_Ioi hh |>.locallyIntegrableOn measurableSet_Ioi
  have hgLI : MeasureTheory.LocallyIntegrableOn (fun x : ℝ => u x - P x) (Set.Ioi a) volume :=
    hu.sub hP_li
  -- classification: `u - P` is affine a.e.
  rcases affine_ae_of_snd_annihilates hgLI hg_ann with ⟨A, B, hcl⟩
  refine ⟨A, B, ?_, ?_, ?_⟩
  · filter_upwards [hcl] with x hx hxa
    have hx' : u x - P x = A + B * x := hx hxa
    have hPx : P x = (∫ s : ℝ in a..x, (∫ t : ℝ in a..s, h t)) := by rfl
    calc
      u x = A + B * x + P x := by linarith
      _ = A + B * x + (∫ s : ℝ in a..x, (∫ t : ℝ in a..s, h t)) := by rw [hPx]
  · intro x hx
    have hA : HasDerivAt (fun _ : ℝ => A) (0 : ℝ) x := hasDerivAt_const x A
    have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
    have hBmul : HasDerivAt (fun y : ℝ => B * y) B x := by
      have h0 : HasDerivAt (fun y : ℝ => B * y) (B * 1) x := hid.const_mul B
      simpa using h0
    have hlin : HasDerivAt (fun y : ℝ => A + B * y) B x := by
      simpa [add_comm] using hBmul.const_add A
    have hPder : HasDerivAt P (F x) x := by
      dsimp [P, F]
      exact second_primitive_hasDerivAt hh hx
    have hU : HasDerivAt (fun y : ℝ => A + B * y + P y) (B + F x) x := hlin.add hPder
    simpa [P, F, primitive] using hU
  · filter_upwards [primitive_ae_hasDerivAt hh] with x hxF hxa
    have hF : HasDerivAt F (h x) x := by
      dsimp [F]
      exact hxF hxa
    have hBF : HasDerivAt (fun y : ℝ => B + F y) (h x) x := hF.const_add B
    have hcongr : deriv (fun y : ℝ => A + B * y + P y) =ᶠ[𝓝 x]
        (fun y : ℝ => B + F y) := by
      filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi a)).mem_nhds hxa] with y hy
      have hA : HasDerivAt (fun _ : ℝ => A) (0 : ℝ) y := hasDerivAt_const y A
      have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) y := hasDerivAt_id y
      have hBmul : HasDerivAt (fun y : ℝ => B * y) B y := by
        have h0 : HasDerivAt (fun y : ℝ => B * y) (B * 1) y := hid.const_mul B
        simpa using h0
      have hlin : HasDerivAt (fun y : ℝ => A + B * y) B y := by
        simpa [add_comm] using hBmul.const_add A
      have hPder : HasDerivAt P (F y) y := by
        dsimp [P, F]
        exact second_primitive_hasDerivAt hh hy
      have hU : HasDerivAt (fun y : ℝ => A + B * y + P y) (B + F y) y := hlin.add hPder
      exact hU.deriv
    have hgoal : HasDerivAt (deriv (fun y : ℝ => A + B * y + P y)) (h x) x :=
      HasDerivAt.congr_of_eventuallyEq (f := fun y : ℝ => B + F y)
        (f₁ := deriv (fun y : ℝ => A + B * y + P y)) hBF hcongr
    simpa [P, F, primitive] using hgoal
end Submission.BoseGases
