/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment relation `F_*(b) = F_*(a) + ∫_a^b F_*(∂_z u)` for the certificate `F_*(F)·sin 2θ ∈ ℋ^k`

This module proves

  `Work.FTS.EllipticEst.Cert.moment_relation_layer` :

for a source `u` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen u`) and whose weighted radial derivative is square
integrable on every box `[a,b] × Iθ` in the sense

  `(s,θ) ↦ (∂_z u(s,θ))² · sin(2θ)^{-η} ∈ L¹([a,b] × Iθ)`,   `η = 99/100`,

the angular moment `F_*(z) = ∫_θ u(z,θ) sinθcos²θ dθ` (`Work.Elliptic.Fstar`) is a primitive
of `z ↦ ∫_θ ∂_z u(z,θ) sinθcos²θ dθ` on every interval `0 < a < b`:

  `F_*(b) = F_*(a) + ∫_s∈[a,b] ∫_θ ∂_z u(s,θ) sinθcos²θ dθ ds`.

This is the single analytic input of the "moment tower" `B_{j+1} = (B_j)'` of
§'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

and the layer certificate `Cert.Fstar_Hk_le_open` (`Cert/FstarSin_norm.lean`) instantiates it
at `u = D_z^j F`.

## Proof

The statement is *not* obtained by differentiating under the `θ`-integral sign (that would
need joint continuity of `∂_z u` on the closed quadrant, which `SmoothOpen` deliberately does
not provide — see the audit note in `Fstar_Hk_le_open`).  Instead the two integrations are
interchanged:

1. `F_*(b) - F_*(a) = ∫_θ (u(b,θ) - u(a,θ))·sinθcos²θ dθ`, by linearity of the `θ`-integral
   and the assumed slice integrability `hsl`;
2. for every interior angle `θ ∈ (0,π/2)` the radial slice is `C^∞`, so the fundamental
   theorem of calculus along the slice
   (`Work.FTS.EllipticEst.DzIter_slice_FTC_open` at `j = 0`) gives
   `u(b,θ) - u(a,θ) = ∫_s∈[a,b] ∂_z u(s,θ) ds`; the two endpoints `θ = 0, π/2` form a null
   set, so this is an identity of the `θ`-integrands a.e. on `Iθ`;
3. pulling the constant `sinθcos²θ` inside the radial integral;
4. Fubini for the product of the restricted measures `volume|[a,b]` and `volume|Iθ`, which
   only needs the joint integrability of `(s,θ) ↦ ∂_z u(s,θ)·sinθcos²θ` on the box.

The joint integrability — the only use of the hypothesis `hbox` — comes from the pointwise
absorption `|y·sinθcos²θ| ≤ (1/2)(y² sin(2θ)^{-η} + 1)` (`abs_mul_sinCos2_le_half` below)
together with the finiteness of the box; a.e. strong measurability is deduced from continuity
on the open quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), the box differing from the open
quadrant only by null sets.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzIter_slice_FTC_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary inputs of the assembly -/

/-- A predicate which holds on the open interval `(0, π/2)` holds almost everywhere on
`Iθ = [0,π/2]`: the two endpoints form a null set. -/
private theorem ae_imp_of_mem_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Work.Spaces.Iθ → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := by
      by_contra hc
      exact hθ (fun h' => absurd h' hc)
    have hpθ : ¬ p θ := fun hp => hθ (fun _ => hp)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    have hcon1 : θ ≠ 0 := fun h => hcon (Or.inl h)
    have hcon2 : θ ≠ π / 2 := fun h => hcon (Or.inr h)
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    exact hpθ (h θ ⟨lt_of_le_of_ne hθI.1 (Ne.symm hcon1), lt_of_le_of_ne hθI.2 hcon2⟩)
  · have hset : ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (π / 2))

/-- Pointwise absorption of the angular weight `sinθcos²θ` by the angular weight
`sin(2θ)^{-η}` of the hypothesis `hbox`: for `θ ∈ Iθ = [0,π/2]` and every `y ∈ ℝ`,

  `|y · sinθcos²θ| ≤ (1/2) (y² · sin(2θ)^{-η} + 1)`.

Indeed `sinθcos²θ ≤ sin(2θ)/2` and `sin(2θ) ≤ sin(2θ)^{-η/2}` for `0 ≤ sin(2θ) ≤ 1`, so
`|y·sinθcos²θ| ≤ (1/2)|y| sin(2θ)^{-η/2}`, and `2ab ≤ a² + b²` with `a = |y| sin(2θ)^{-η/2}`,
`b = 1` gives the claim. -/
private lemma abs_mul_sinCos2_le_half (y θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |y * Work.Elliptic.sinCos2 θ|
      ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ π / 2 := hθ.2
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθ1
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hσ0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]; exact mul_nonneg hs0 (pow_nonneg hc0 2)
  have hsc_le : Work.Elliptic.sinCos2 θ ≤ 1 / 2 * Real.sin (2 * θ) := by
    have hmul : Real.sin θ * Real.cos θ * Real.cos θ ≤ Real.sin θ * Real.cos θ * 1 :=
      mul_le_mul_of_nonneg_left hc1 (mul_nonneg hs0 hc0)
    rw [Work.Elliptic.sinCos2, Real.sin_two_mul]
    nlinarith [hmul]
  have h1 : |y * Work.Elliptic.sinCos2 θ| ≤ 1 / 2 * |y| * Real.sin (2 * θ) := by
    rw [abs_mul, abs_of_nonneg hsc0]
    calc |y| * Work.Elliptic.sinCos2 θ
        ≤ |y| * (1 / 2 * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hsc_le (abs_nonneg y)
      _ = 1 / 2 * |y| * Real.sin (2 * θ) := by ring
  have hσle : Real.sin (2 * θ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rcases eq_or_lt_of_le hσ0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    · have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
        have h := Real.rpow_le_one hσ0 hσ1
          (by rw [Work.Spaces.eta]; norm_num : (0 : ℝ) ≤ 1 + Work.Spaces.eta / 2)
        rwa [Real.rpow_add hpos, Real.rpow_one] at h
      rw [Real.rpow_neg (le_of_lt hpos), ← one_div,
        le_div_iff₀ (Real.rpow_pos_of_pos hpos _)]
      exact hkey
  have hsq : (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, sq_abs]
    congr 1
    rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) 2,
      ← Real.rpow_mul hσ0]
    congr 1
    push_cast
    ring
  have hA : 2 * (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) * 1
      ≤ (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2 + 1 ^ 2 :=
    two_mul_le_add_sq _ 1
  rw [hsq] at hA
  have hA' : 2 * (|y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      ≤ y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 := by
    nlinarith [hA]
  have h3 : 1 / 2 * |y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := by
    nlinarith [hA']
  calc |y * Work.Elliptic.sinCos2 θ| ≤ 1 / 2 * |y| * Real.sin (2 * θ) := h1
    _ ≤ 1 / 2 * |y| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) :=
        mul_le_mul_of_nonneg_left hσle (by positivity)
    _ ≤ 1 / 2 * (y ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1) := h3

/-! ## The moment relation -/

theorem moment_relation_layer (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- ### joint integrability of `∂_z u · sinθcos²θ` on the box `[a,b] × Iθ`
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hu.pz).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop)
  have hBsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1)) subset_rfl
  have hmono : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hBsub le_rfl
  have hAE : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).mono_measure hmono
  have hEq : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]; rfl
  have hGint : Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hEq]
    exact hbox a b ha hab
  have hdom : Integrable (fun p : ℝ × ℝ => 1 / 2 * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) + 1))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (hGint.add (integrable_const 1)).const_mul (1 / 2)
  have hInt : Integrable
      (Function.uncurry (fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine Integrable.mono' hdom hAE ?_
    rw [MeasureTheory.Measure.prod_restrict,
      MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod hIθ_meas)]
    refine Eventually.of_forall fun p hp => ?_
    have hb' := abs_mul_sinCos2_le_half (Work.Spaces.pz u p.1 p.2) p.2 hp.2
    show ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
      ≤ 1 / 2 * (Work.Spaces.pz u p.1 p.2 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.eta)) + 1)
    simpa only [Real.norm_eq_abs] using hb'
  -- ### the fundamental theorem of calculus along the radial slices
  have hftc : ∀ θ ∈ Set.Ioo 0 (π / 2),
      u b θ - u a θ = ∫ s in Set.Icc a b, Work.Spaces.pz u s θ := by
    intro θ hθ
    have h := Work.FTS.EllipticEst.DzIter_slice_FTC_open hu 0 ha hab.le hθ
    simp only [Work.Spaces.DzIter_zero] at h
    rw [show (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
        = ∫ r in a..b, Work.Spaces.pz u r θ from by
      rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Icc_eq_integral_Ioc]]
    exact h
  -- ### the chain of equalities
  have e1 : Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a
      = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
        = fun θ => u b θ * Work.Elliptic.sinCos2 θ
            - u a θ * Work.Elliptic.sinCos2 θ from by
      funext θ; ring]
    rw [MeasureTheory.integral_sub (hsl b hb) (hsl a ha)]
  have e2 : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_ae hIθ_meas ?_
    refine ae_imp_of_mem_Ioo fun θ hθ => ?_
    rw [hftc θ hθ]
  have e3 : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc a b, Work.Spaces.pz u s θ)
        * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
    refine MeasureTheory.setIntegral_congr_fun hIθ_meas fun θ _ => ?_
    exact (MeasureTheory.integral_mul_const (Work.Elliptic.sinCos2 θ)
      (fun s => Work.Spaces.pz u s θ)).symm
  have e4 : (∫ θ in Work.Spaces.Iθ,
        (∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      = ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) :=
    (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict Work.Spaces.Iθ)
      (f := fun s θ : ℝ => Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) hInt).symm
  have hkey := e1.trans (e2.trans (e3.trans e4))
  linarith [hkey]

end Work.FTS.EllipticEst.Cert
