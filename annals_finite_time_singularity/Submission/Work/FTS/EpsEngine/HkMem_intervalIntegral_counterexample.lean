/-
Copyright: work module for the Elgindi finite-time singularity project.

# A counterexample to `Work.FTS.EpsEngine.HkMem_intervalIntegral`

**Verdict: the requested lemma is FALSE as stated** (see
`Submission/Work/FTS/EpsEngine/NOTES_HkMem_intervalIntegral_FALSE.md`).

The requested statement asserts that, for a family `s ↦ H s` of profiles that are `C^∞` on the
open quadrant, whose `H^k`-norms are bounded by `B` and whose `HkIntegrand` is jointly measurable
with a per-`z` uniform angular-energy bound `∫_θ HkIntegrand α k (H s) z θ ≤ C z`,

  `HkMem α k (∫_s H s)`   and   `HkNorm α k (∫_s H s) ≤ B (b - a)`.

The hypotheses `hbd` and `hperz` are **vacuous when the angular slices are not integrable**: the
Bochner integral of a non-integrable function is `0` in Mathlib
(`MeasureTheory.integral_undef`), so `HkNorm α k (H s) ≤ B` and `∫_θ HkIntegrand α k (H s) z θ ≤ C z`
are satisfied by the *junk value* `0` whenever the slices of `H s` blow up.  The conclusion, on
the other hand, contains the honest statement `∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand …) Iθ`
for each `z ∈ Iz = [0,∞)` — and nothing in the hypotheses forbids a profile whose
`HkIntegrand`, while finite on the open quadrant, is **not** integrable in `θ` at some fixed `z`.

This file makes that failure completely explicit with the simplest possible family: the profile

  `cexP z θ = 1 / sin(2θ)`      (smooth — indeed analytic — on the open quadrant `Q0`),

taken **constant in `s`**.  Then

* every slice `cexH s = cexP` is `SmoothOpen`;
* at every `z > 0` the angular slice `θ ↦ HkIntegrand α 0 cexP z θ` equals
  `(w z)^2 · sin(2θ)^{-(2+η)}` on `Q0`, which is **not** integrable at `θ = 0` because
  `2 + η > 1`; consequently `∫_θ HkIntegrand α 0 cexP z θ = 0` (junk) and hence
  `HkSq α 0 cexP = 0`, `HkNorm α 0 cexP = 0 ≤ B` for every `B ≥ 0`, and the per-`z` energy bound
  `hperz` holds with `C z = 0`;
* the slots are constant in `s`, so `hmeas` is trivial and the joint measurability `hjoint` is
  the one proved in `Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand`; uniform bounds on
  compacts (`hsup`) follow from continuity on `Q0`;
* but the primitive of the family is `∫_s cexH s = (b-a) • cexP`, whose angular slice at `z = 1`
  is genuinely non-integrable, so `HkMem α 0 (∫_s cexH s)` **fails**.

Hence the requested lemma is false already for `k = 0`, `α` arbitrary, `T = 1`, `a = 0`, `b = 1`,
`B = 0`.  The missing hypothesis is the *per-slice* honesty `∀ s ∈ Icc 0 T, HkMem α k (H s)`
(equivalently: integrability of the angular slices of each `H s`), which is what makes `hbd` and
`hperz` mean what they are intended to mean.

Everything in this file is `sorry`-free; the main theorem is
`Work.FTS.EpsEngine.HkMem_intervalIntegral_counterexample`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-! ## The profile `θ ↦ 1/sin(2θ)` and the constant family -/

/-- The counterexample profile: `cexP z θ = 1/sin(2θ)`.  It is smooth (even analytic) on the
open quadrant `Q0`, and its angular slices are not in `ℋ^k` for any `k` (the weight
`sin(2θ)^{-η/2}` leaves an exponent `2 + η > 1`). -/
def cexP : ℝ → ℝ → ℝ := fun _ θ => (Real.sin (2 * θ))⁻¹

/-- The counterexample family: constant in `s`. -/
def cexH : ℝ → ℝ → ℝ → ℝ := fun _ => cexP

lemma cexP_sin_pos {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * θ) := by
  obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp h
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- `cexP` is smooth on the open quadrant. -/
lemma cexP_smoothOpen : Work.FTS.EllipticEst.SmoothOpen cexP := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have hfun : Function.uncurry cexP = fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹ := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  refine ContDiffOn.inv ?_ ?_
  · have hsin : ContDiffOn ℝ (n : WithTop ℕ∞) Real.sin Set.univ := Real.contDiff_sin.contDiffOn
    have hinner : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => 2 * p.2)
        Work.FTS.EllipticEst.Q0 := by
      fun_prop
    exact hsin.comp hinner (fun p hp => trivial)
  · intro p hp
    exact ne_of_gt (cexP_sin_pos hp)

/-- Continuity of `cexP` on the open quadrant (the form used for the compact bounds). -/
lemma cexP_continuousOn_Q0 : ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2))⁻¹)
    Work.FTS.EllipticEst.Q0 :=
  cexP_smoothOpen.continuousOn

/-! ## The `HkIntegrand` of a single slice -/

/-- At `k = 0` the `HkIntegrand` of `cexP` has the single slot `(f · w / sin(2θ)^{η/2})²`. -/
lemma cexP_hkIntegrand_one (α z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 cexP z θ
      = (cexP z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand, Finset.sum_range_one]
  simp only [Work.Spaces.DzIter_zero]
  rw [Finset.sum_range_one, Finset.sum_range_one]
  simp only [ite_eq_right (show ¬ (1 ≤ (0:ℕ) ∧ 0 + 0 ≤ 0) by omega), add_zero]

/-- **The exact value of the `HkIntegrand` of `cexP`** (on the quadrant, where `sin 2θ > 0`). -/
lemma cexP_hkIntegrand {α z θ : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    Work.Spaces.HkIntegrand α 0 cexP z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hs
  have hsq : ∀ x : ℝ, ((Real.sin (2 * θ)) ^ x) ^ 2 = (Real.sin (2 * θ)) ^ (x * 2) := by
    intro x
    rw [← Real.rpow_two, ← Real.rpow_mul hs0 x 2]
  rw [cexP_hkIntegrand_one]
  simp only [cexP]
  rw [div_eq_mul_inv, ← Real.rpow_neg_one (Real.sin (2 * θ)),
    ← Real.rpow_neg hs0 (Work.Spaces.eta / 2)]
  rw [show (Real.sin (2 * θ)) ^ (-1 : ℝ)
        * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      = Work.Spaces.w z * ((Real.sin (2 * θ)) ^ (-1 : ℝ)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) by ring]
  rw [(Real.rpow_add hs _ _).symm, mul_pow, hsq]
  congr 1
  ring_nf

/-- On the boundary line `z = 0` the `HkIntegrand` vanishes (the weight `w` does). -/
lemma cexP_hkIntegrand_zero (α θ : ℝ) : Work.Spaces.HkIntegrand α 0 cexP 0 θ = 0 := by
  rw [cexP_hkIntegrand_one]
  rw [show Work.Spaces.w (0:ℝ) = 0 by norm_num [Work.Spaces.w]]
  ring

lemma cexP_w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

/-! ## Non-integrability of the angular slices -/

/-- **The angular slice of `HkIntegrand α 0 cexP z ·` is not integrable at any `z > 0`.**  On
`(0, π/4)` the integrand dominates `(w z)² 2^{-(2+η)} θ^{-(2+η)}`, and `θ ↦ θ^s` is integrable
on `(0, π/4)` only for `s > -1` (`intervalIntegral.integrableOn_Ioo_rpow_iff`), while here
`s = -(2 + η) ≤ -1`. -/
lemma cexP_not_integrableOn (α z : ℝ) (hz : 0 < z) :
    ¬ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 cexP z θ)
        Work.Spaces.Iθ := by
  intro hInt
  set s : ℝ := -(2 + Work.Spaces.eta) with hsdef
  have hsle : s ≤ 0 := by rw [hsdef]; have := Work.Spaces.eta_nonneg; linarith
  have hpit : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hsub : Set.Ioo (0:ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hIoo : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 cexP z θ)
      (Set.Ioo (0:ℝ) (Real.pi / 4)) := hInt.mono_set hsub
  set c : ℝ := (Work.Spaces.w z) ^ 2 * (2:ℝ) ^ s with hcdef
  have hcw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (cexP_w_pos hz) 2
  have hcpos : 0 < c := by
    rw [hcdef]; exact mul_pos hcw (Real.rpow_pos_of_pos (by norm_num) s)
  -- the minorant is measurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => c * θ ^ s)
      (volume.restrict (Set.Ioo (0:ℝ) (Real.pi / 4))) := by
    refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo).const_mul c
    intro x hx
    exact (Real.continuousAt_rpow_const x s (Or.inl (ne_of_gt hx.1))).continuousWithinAt
  -- the pointwise domination
  have hbound : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0:ℝ) (Real.pi / 4))),
      ‖c * θ ^ s‖ ≤ Work.Spaces.HkIntegrand α 0 cexP z θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsin : 0 < Real.sin (2 * θ) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
      linarith [hθ.2, Real.pi_pos]
    have hsin_le : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have h1 : (2 * θ) ^ s ≤ (Real.sin (2 * θ)) ^ s :=
      Real.rpow_le_rpow_of_nonpos hsin hsin_le hsle
    have h2 : (2 * θ) ^ s = (2:ℝ) ^ s * θ ^ s := by
      rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (le_of_lt hθpos)]
    have hθs : 0 ≤ θ ^ s := Real.rpow_nonneg (le_of_lt hθpos) s
    have hnorm : ‖c * θ ^ s‖ = c * θ ^ s := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hcpos) hθs)]
    rw [hnorm, cexP_hkIntegrand hsin, hcdef]
    have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2 := le_of_lt hcw
    calc (Work.Spaces.w z) ^ 2 * (2:ℝ) ^ s * θ ^ s
        = (Work.Spaces.w z) ^ 2 * ((2:ℝ) ^ s * θ ^ s) := by ring
      _ = (Work.Spaces.w z) ^ 2 * (2 * θ) ^ s := by rw [h2]
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ s :=
          mul_le_mul_of_nonneg_left h1 hw0
  have hmin : MeasureTheory.Integrable (fun θ : ℝ => c * θ ^ s)
      (volume.restrict (Set.Ioo (0:ℝ) (Real.pi / 4))) :=
    MeasureTheory.Integrable.mono' hIoo hmeas hbound
  -- scale back to the pure power
  have hscale : MeasureTheory.Integrable (fun θ : ℝ => c⁻¹ * (c * θ ^ s))
      (volume.restrict (Set.Ioo (0:ℝ) (Real.pi / 4))) := hmin.const_mul c⁻¹
  have hone : MeasureTheory.Integrable (fun θ : ℝ => θ ^ s)
      (volume.restrict (Set.Ioo (0:ℝ) (Real.pi / 4))) := by
    refine hscale.congr ?_
    filter_upwards with θ
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
  have hlt := (intervalIntegral.integrableOn_Ioo_rpow_iff hpit).mp hone
  rw [hsdef] at hlt
  have heta := Work.Spaces.eta_nonneg
  linarith

/-! ## The junk values: `HkSq`, `HkNorm`, and the failure of `HkMem` -/

/-- The angular energy of a slice is `0` — the honest value `0` at `z = 0`, and the junk value of
a non-integrable Bochner integral for `z > 0`. -/
lemma cexP_integral_eq_zero (α z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 cexP z θ) = 0 := by
  have hz' : (0:ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with h | h
  · subst h
    rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 cexP 0 θ) = fun _ => 0 from
      funext (fun θ => cexP_hkIntegrand_zero α θ)]
    simp
  · exact MeasureTheory.integral_undef (by
      simpa only [MeasureTheory.IntegrableOn] using cexP_not_integrableOn α z h)

/-- `HkSq α 0 cexP = 0`, for the junk reason (the slices are not integrable). -/
lemma cexP_HkSq_eq_zero (α : ℝ) : Work.Spaces.HkSq α 0 cexP = 0 := by
  have h1 : Work.Spaces.HkSq α 0 cexP = ∫ z in Work.Spaces.Iz, (0 : ℝ) := by
    unfold Work.Spaces.HkSq
    exact MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz) measurableSet_Ici
      (fun z hz => cexP_integral_eq_zero α z hz)
  rw [h1]
  simp

/-- Consequently the `H^k`-norm of `cexP` is `0`: this is the (junk) content of `hbd`. -/
lemma cexP_HkNorm_eq_zero (α : ℝ) : Work.Spaces.HkNorm α 0 cexP = 0 := by
  rw [Work.Spaces.HkNorm, cexP_HkSq_eq_zero α]
  simp

/-- **`cexP` is not in `ℋ^0`**, because its angular slice at `z = 1` is not integrable. -/
theorem cexP_not_HkMem (α : ℝ) : ¬ Work.Spaces.HkMem α 0 cexP := by
  intro h
  exact cexP_not_integrableOn α 1 (by norm_num) (h.1 1 (by norm_num [Work.Spaces.Iz]))

/-! ## The hypotheses of the requested lemma hold for the constant family -/

theorem cexH_smoothOpen : ∀ s ∈ Set.Icc (0:ℝ) 1,
    Work.FTS.EllipticEst.SmoothOpen (cexH s) := fun s _ => cexP_smoothOpen

/-- `hbd` holds with `B = 0` — via the junk value `HkNorm α 0 cexP = 0`. -/
theorem cexH_HkNorm_le (α : ℝ) : ∀ s ∈ Set.Icc (0:ℝ) 1,
    Work.Spaces.HkNorm α 0 (cexH s) ≤ 0 := fun s _ => by
  show Work.Spaces.HkNorm α 0 cexP ≤ 0
  rw [cexP_HkNorm_eq_zero α]

theorem cexH_hmeas : ∀ (j i : ℕ), j + i ≤ 0 → ∀ z θ : ℝ,
    (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (cexH s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) := by
  intro j i hji z θ _
  have hj : j = 0 := by omega
  have hi : i = 0 := by omega
  subst hj; subst hi
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero, cexH]
    using MeasureTheory.aestronglyMeasurable_const
      (μ := MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) (b := cexP z θ)

/-- `hjoint`: the joint measurability of the `HkIntegrand` family, which holds by
`aemeasurable_uncurry_HkIntegrand` because the family is constant in `s`. -/
theorem cexH_hjoint (α : ℝ) : MeasureTheory.AEStronglyMeasurable
    (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (cexH p.1) p.2.1 p.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
  (Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand (α := α) (T := 1) (k := 0)
    (H := cexH) cexH_smoothOpen
    (fun z θ _ => continuousOn_const)).aestronglyMeasurable

/-- `hsup`: uniform bounds on compact subsets of the open quadrant, from continuity of `cexP`
there. -/
theorem cexH_hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 0 →
      |Work.Spaces.mixed j i (cexH s) q.1 q.2| ≤ C := by
  intro K hK hKQ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (cexP_continuousOn_Q0.mono hKQ)
  refine ⟨max C 0, le_max_right _ _, fun s _ q hq j i hji => ?_⟩
  have hj : j = 0 := by omega
  have hi : i = 0 := by omega
  subst hj; subst hi
  have h1 : ‖(Real.sin (2 * q.2))⁻¹‖ ≤ C := hC q hq
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero, cexH, cexP,
    Real.norm_eq_abs] at h1 ⊢
  exact le_trans h1 (le_max_left _ _)

/-- `hperz` holds with `C z = 0` — again by the junk value of the Bochner integral. -/
theorem cexH_hperz (α : ℝ) : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ,
    ∀ s ∈ Set.Icc (0:ℝ) 1,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (cexH s) z θ) ≤ Cz :=
  fun z hz => ⟨0, fun s _ => by
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 cexP z θ) ≤ 0
    rw [cexP_integral_eq_zero α z hz]⟩

/-! ## The conclusion fails -/

/-- The primitive of the constant family is `(b - a) • cexP`; at `a = 0`, `b = 1` it is `cexP`. -/
theorem cex_primitive_eq : (fun z θ : ℝ => ∫ s in (0:ℝ)..1, cexH s z θ) = cexP := by
  funext z θ
  rw [show (fun s : ℝ => cexH s z θ) = fun _ => cexP z θ from funext (fun s => rfl)]
  rw [intervalIntegral.integral_const]
  simp

/-- **The conclusion of the requested lemma fails** for this family: the primitive is `cexP`,
which is not in `ℋ^0`. -/
theorem cex_not_HkMem_primitive (α : ℝ) :
    ¬ Work.Spaces.HkMem α 0 (fun z θ => ∫ s in (0:ℝ)..1, cexH s z θ) := by
  rw [cex_primitive_eq]
  exact cexP_not_HkMem α

/-- **The counterexample, packaged.**  All the hypotheses of
`Work.FTS.EpsEngine.HkMem_intervalIntegral` hold for `α` arbitrary, `B = 0`, `k = 0`, `T = 1`,
`a = 0`, `b = 1` and the constant family `cexH`, while its conclusion fails. -/
theorem HkMem_intervalIntegral_counterexample (α : ℝ) :
    ∃ (B : ℝ) (k : ℕ) (T a b : ℝ) (H : ℝ → ℝ → ℝ → ℝ),
      a ≤ b ∧ 0 ≤ T ∧ a ∈ Set.Icc 0 T ∧ b ∈ Set.Icc 0 T ∧
      (∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s)) ∧
      (∀ s ∈ Set.Icc (0:ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B) ∧
      (∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
          (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T))) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)).prod
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0:ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
          |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) ∧
      (∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0:ℝ) T,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) ∧
      ¬ (Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
          Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a)) :=
  ⟨0, 0, 1, 0, 1, cexH, zero_le_one, zero_le_one, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩,
    cexH_smoothOpen, cexH_HkNorm_le α, cexH_hmeas, cexH_hjoint α, cexH_hsup, cexH_hperz α,
    by
      rintro ⟨hmem, -⟩
      exact cex_not_HkMem_primitive α hmem⟩

/-- **The requested lemma is refuted.**  This is the exact negation of the (universally
quantified) statement of `Work.FTS.EpsEngine.HkMem_intervalIntegral`, written out with the same
hypothesis block; the tuple theorem above produces the counterexample data, and any proof of the
requested lemma would turn those data into its conclusion. -/
theorem not_HkMem_intervalIntegral :
    ¬ (∀ (α B : ℝ) (k : ℕ) (T a b : ℝ) (H : ℝ → ℝ → ℝ → ℝ),
        a ≤ b → 0 ≤ T → a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T →
        (∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s)) →
        (∀ s ∈ Set.Icc (0:ℝ) T, Work.Spaces.HkNorm α k (H s) ≤ B) →
        (∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
            (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T))) →
        MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
          ((MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)).prod
            ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) →
        (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0:ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
            |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) →
        (∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0:ℝ) T,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz) →
        Work.Spaces.HkMem α k (fun z θ => ∫ s in a..b, H s z θ) ∧
          Work.Spaces.HkNorm α k (fun z θ => ∫ s in a..b, H s z θ) ≤ B * (b - a)) := by
  intro h
  obtain ⟨B, k, T, a, b, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hbad⟩ :=
    HkMem_intervalIntegral_counterexample 0
  exact hbad (h 0 B k T a b H h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

end Work.FTS.EpsEngine
