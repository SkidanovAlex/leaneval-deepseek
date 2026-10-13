/-
# `GalFields/Norm/RadA4/Own` — the order-`4` radial bound for the transfer profile `radA α f`

The `E1Norm` chapter proves (`E1Norm.radA_sum_le`) the radial estimate

  `∫_0^∞ ∑_{j≤n} (D_z^j (radA α f)(z))² w(z)² dz ≤ C·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`  (`n ≤ 3`)

with a constant `C` independent of `α`, `n` and `f`.  The consumer
`Work.FTS.GalFields.Norm.radA_slotSum4_le` needs the same statement at `n = 4`: the order-`4`
`D_z`-slot is the top slot of the `ℋ⁴`-data, and `CoerAdm α f` supplies exactly `ℋ⁵`-membership
(`RegQ α 5`), so order `4` is the sharp reachable bound.

This file assembles the `n ≤ 4` version out of the five order-`4` ingredients, each of which is
the one-order-up counterpart of a lemma of `E1Parts`/`E1Norm`:

* `RadA4.L12f_DzdIter_sq_w_sq_integrable_four` — order-`4` integrability of the `L₁₂ f`-iterates;
* `RadA4.RadA_Efun_eq_four` — the pointwise identity for the integrand;
* `RadA4.Efun_le_Maj_four` — the pointwise majorant;
* `RadA4.continuousOn_Efun_four` — measurability of the integrand;
* `RadA4.Maj_int_le_four` — the integral of the majorant at level `n ≤ 4`,

together with the two profile bounds that are `α`-independent and therefore need no
strengthening: `ampB_slotSum5_bound` (here) and `E1Norm.ampA_uniform_bound` (`ampA`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Radial
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.GalFields.Norm.RadA4.L12f_DzdIter_sq_w_sq_integrable_four
import Submission.Work.FTS.GalFields.Norm.RadA4.Maj_int_le_four
import Submission.Work.FTS.GalFields.Norm.RadA4.RadA_Efun_eq_four
import Submission.Work.FTS.GalFields.Norm.RadA4.Efun_le_Maj_four
import Submission.Work.FTS.GalFields.Norm.RadA4.continuousOn_Efun_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `(0,∞)`-form of the order-`4` integrability -/

/-- `(D_z^c (L₁₂ f))²w² ∈ L¹((0,∞))` for `c ≤ 4`: the `Iz`-statement of
`L12f_DzdIter_sq_w_sq_integrable_four`, transported off the null point `z = 0`. -/
theorem L12f_DzdIter_sq_w_sq_integrable_Ioi_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ c : ℕ, c ≤ 4 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
  fun c hc => (L12f_DzdIter_sq_w_sq_integrable_four α hα hα1 hf c hc).congr_set_ae
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))

/-! ## Integrability of the order-`4` radial slot of `radA α f` -/

/-- **The order-`4` radial integrability.**  For `0 < α ≤ 1` and `f ∈ CoerAdm α`, every
weighted square `(D_z^j (radA α f)(z))²w(z)²` with `j ≤ 4` is integrable on `Iz = [0,∞)`.

This is `E1Parts.RadA` (`j ≤ 3`) one order up: the `j = 4` term needs
`D_z^4 (L₁₂ f) = -Qang f 3` (`DzdIter_L12f_eq_neg_Qang`) and the order-`4` majorant. -/
theorem RadA_four (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ j : ℕ, j ≤ 4 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  obtain ⟨K, hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_dzdIter_bound α hα hα1
  intro j hj4
  have hMaj_int : MeasureTheory.IntegrableOn
      (Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K) (Set.Ioi (0 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.integrable_finsetSum _ (fun c hc =>
        L12f_DzdIter_sq_w_sq_integrable_Ioi_four α hα hα1 hf c
          (by have := Finset.mem_range.mp hc; omega))
    have h2 : MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.ampB_DzdIter_sq_w_sq_integrable_Ioi α hα hα1
        (c := j) (by omega)
    have hfun : Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K = fun z : ℝ =>
        2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
          * (∑ c ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
          * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
      funext z; rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Maj_eq]
    rw [hfun]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hEfun_int : MeasureTheory.Integrable
      (Work.FTS.CoercivityFix.Transfer.E1Parts.Efun α f j)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.Integrable.mono' hMaj_int
      ((continuousOn_Efun_four α hα hα1 f hf hj4).aestronglyMeasurable measurableSet_Ioi)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (Work.FTS.CoercivityFix.Transfer.E1Parts.Efun_nonneg α f j z)]
        exact Efun_le_Maj_four α hα hα1 f hf hj4 hKnn hKbd z hz))
  have hF_int : MeasureTheory.Integrable
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.IntegrableOn.congr_fun hEfun_int
      (fun z hz => (RadA_Efun_eq_four α hα hα1 f hf hj4 z hz).symm) measurableSet_Ioi
  exact MeasureTheory.IntegrableOn.congr_set_ae hF_int
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm

/-! ## The projecter profile's slot sum at order `5` -/

/-- **The `α`-independent order-`5` slot sum of `ampB`.**  `ampB β z = 2z²/(1+z)³` does not
depend on `β` at all, so the value of the slot sum at `β = 1`, increased by `1`, is a uniform
bound.  (No integrability input is needed: the two integrals are *equal* because the
integrands agree, and the bound is therefore trivial.) -/
theorem ampB_slotSum5_bound : ∃ Kb : ℝ, 0 < Kb ∧ ∀ β : ℝ, 0 < β → β ≤ 1 →
    (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      ≤ Kb := by
  refine ⟨(∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB 1) z) ^ 2
        * (Work.Spaces.w z) ^ 2) + 1, ?_, ?_⟩
  · have hnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB 1) z) ^ 2
          * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg (fun z => Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    linarith
  intro β _hβ _hβ1
  have hfunβ : Work.FTS.CoercivityFix.Transfer.ampB β
      = Work.FTS.CoercivityFix.Transfer.ampB 1 := by
    funext z
    simp only [Work.FTS.CoercivityFix.Transfer.ampB]
  rw [hfunβ]
  linarith

/-! ## The level-`4` assembly -/

/-- **The order-`4` radial bound for `radA α f`.**  For `0 < α ≤ 1` and `n ≤ 4`,

  `∫_0^∞ ∑_{j≤n} (D_z^j (radA α f)(z))² w(z)² dz ≤ C·(|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ})`

with `C` independent of `α`, `n` and `f`; the integrand is honestly integrable on `[0,∞)`.

This is `E1Norm.radA_sum_le` with `3 → 4` everywhere (`hB` now bounding the slot sum over
`range 5`, and the numerical constants `8 → 16`, `16 → 25`, `4 → 5`). -/
theorem radA_sum_le_four {CQ CC Kb K : ℝ} (hCQ : 0 ≤ CQ) (hCC : 0 < CC) (hKb : 0 < Kb)
    (hK : 0 ≤ K)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ CQ * Work.Spaces.HkSq β m g)
    (hC0 : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 → Work.FTS.Nonlin.CoerAdm β g →
      Work.Spaces.HkMem β m g → (Work.Coercivity.C0 g) ^ 2 ≤ CC * Work.Spaces.HkSq β m g)
    (hB : ∀ (β : ℝ), 0 < β → β ≤ 1 → (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 5,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB β) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ Kb)
    (hA : ∀ (β : ℝ), 0 < β → β ≤ 1 → ∀ b ≤ 4, ∀ z ∈ Set.Ioi 0,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA β) z| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → n ≤ 4 →
      Work.FTS.Nonlin.CoerAdm α f → Work.Spaces.HkMem α n f →
      MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  refine ⟨5 * (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) + 1,
    by have : 0 ≤ 2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb := by positivity
       linarith, ?_⟩
  intro α n f hα hα1 hn hf hmem
  have hKbd := hA α hα hα1
  have hmeas : MeasureTheory.volume.restrict (Set.Ioi 0)
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    Work.FTS.CoercivityFix.Transfer.E1Norm.restrict_Ioi_eq_restrict_Iz
  -- ## the pointwise majorant, a.e. on `Iz`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ j ∈ Finset.range (n + 1),
            Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z := by
    have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
          ≤ ∑ j ∈ Finset.range (n + 1),
              Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
        rw [RadA_Efun_eq_four α hα hα1 f hf hj4 z hz]
        exact Efun_le_Maj_four α hα hα1 f hf hj4 hK hKbd z hz)
    rw [hmeas] at h1
    exact h1
  -- ## integrability of the majorant
  have hMint : ∀ j : ℕ, j ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) Work.Spaces.Iz := by
    intro j hj4
    have hAint : MeasureTheory.IntegrableOn (fun z => 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) *
        (∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
      (MeasureTheory.integrable_finsetSum _ (fun c hc =>
        L12f_DzdIter_sq_w_sq_integrable_four α hα hα1 hf c
          (by have := Finset.mem_range.mp hc; omega))).const_mul _
    have hBint : MeasureTheory.IntegrableOn (fun z =>
        2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
          ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
      ((Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 j
        (by omega)).const_mul _
    have hfun : (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
        = fun z => 2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1)) *
            (∑ c ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
          + 2 * ((Work.Coercivity.C0 f / Work.Spaces.c α) ^ 2) *
            ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) :=
      funext (fun z => Work.FTS.CoercivityFix.Transfer.E1Parts.Maj_eq α f j K z)
    rw [hfun]
    exact hAint.add hBint
  have hRint : MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
      Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun j hj => hMint j (by
      have := Finset.mem_range.mp hj; omega))
  have hLint : MeasureTheory.IntegrableOn (fun z => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum _ (fun j hj =>
      RadA_four α hα hα1 f hf j (by have := Finset.mem_range.mp hj; omega))
  refine ⟨hLint, ?_⟩
  have hle : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))) hRint hae
  have hsum2 : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
      Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z)
      ≤ ∑ _j ∈ Finset.range (n + 1),
          ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) := by
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hMint j (by
      have := Finset.mem_range.mp hj; omega))]
    exact Finset.sum_le_sum (fun j hj => Maj_int_le_four hCQ hCC hKb hK hQ hC0 hB α hα hα1 n hn
      hf hmem j (by have := Finset.mem_range.mp hj; omega))
  have hcard : (∑ _j ∈ Finset.range (n + 1),
        ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f))
      = ((n : ℝ) + 1) * ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
          * Work.Spaces.HkSq α n f) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hCnn : 0 ≤ (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
      * Work.Spaces.HkSq α n f := by
    have := Work.Spaces.HkSq_nonneg α n f
    positivity
  have hn5 : ((n : ℝ) + 1) ≤ 5 := by
    have : (n : ℝ) ≤ 4 := by exact_mod_cast hn
    linarith
  have hkey : 5 * ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
        * Work.Spaces.HkSq α n f)
      ≤ (5 * (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hC0nn : 0 ≤ 2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb := by positivity
    have hNd : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
    have hNf : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
    nlinarith [hNd, hNf, hC0nn]
  calc (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          Work.FTS.CoercivityFix.Transfer.E1Parts.Maj α f j K z := hle
    _ ≤ ∑ _j ∈ Finset.range (n + 1),
          ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) * Work.Spaces.HkSq α n f) :=
        hsum2
    _ = ((n : ℝ) + 1) * ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
          * Work.Spaces.HkSq α n f) := hcard
    _ ≤ 5 * ((2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
          * Work.Spaces.HkSq α n f) := mul_le_mul_of_nonneg_right hn5 hCnn
    _ = 5 * (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb)
          * Work.Spaces.HkSq α n f := by ring
    _ ≤ (5 * (2 * ((K * 16) ^ 2 * 25 * 107 * CQ) + 200 * CC * Kb) + 1)
        * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
        simpa only [mul_assoc] using hkey

end Work.FTS.GalFields.Norm.RadA4
