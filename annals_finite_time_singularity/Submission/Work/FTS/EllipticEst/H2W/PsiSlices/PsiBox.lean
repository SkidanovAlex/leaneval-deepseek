/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.PsiSlices.PsiBox`: the angular slices of `D_z^i Ψ` and the box integrability

This module produces, for a datum of the weak elliptic class (`Ψ` smooth on the open quadrant,
`∂_θ²Ψ` honestly in `ℋ²`), the two analytic inputs of the *integrated* moment chain for `Ψ`:

* `slice_bound`: for `i ≤ 2` and `u > 0`,
  `∫_θ |D_z^i Ψ(u,θ)| sinθcos²θ ≤ Bnd Ψ i u`, where `Bnd` is an explicit majorant built from the
  values at the interior angle `π/4` and from the `ℋ²`-slot of `∂_θ²Ψ`
  (`Work.FTS.EllipticEst.Mine.SliceMomentTaylor` supplies the estimate
  `∫|g| sinθcos²θ ≤ 3|g(π/4)| + 9|g'(π/4)| + 9√(∫(g'')²sin(2θ)^{-η})` for a `C²` slice `g`);

* `Bnd_integrableOn`: `Bnd Ψ i` is integrable on every `(a,b] ⊂ (0,∞)`;

* `integrable_uncurry_div_of_fibre_bound`: Tonelli from a fibre bound, giving the box
  integrability of a function of the shape `(r,θ) ↦ f r θ / r`.

The route for the box integrability is the fibre bound: the `θ`-fibre of `D_z^i Ψ` is
integrable at every `r ∈ (s,z]` with an `r`-integrable bound (`Bnd`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.FTS.EllipticEst.Mine.SliceMomentTaylor
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §1 Pointwise facts -/

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
theorem sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  simp only [Work.Elliptic.sinCos2]
  positivity

/-- `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- `sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem rpow_neg_eta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.H2W.sin_two_nonneg hθ) _

/-- **The pointwise energy/slot inequality.**  For `θ ∈ Iθ`, `u > 0` and any real `D`,
`D²·sin(2θ)^{-η} ≤ (D · w u / sin(2θ)^{η/2})²`, because `w u ≥ 1` on `(0,∞)`. -/
theorem sq_mul_rpow_le_slot {D : ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (D * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hs := Work.FTS.EllipticEst.H2W.sin_two_nonneg hθ
  have hkey : (D * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = D ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.H2W.rho θ) := by
    change (D * Work.FTS.EllipticEst.H2W.Wf z θ) ^ 2
      = D ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.H2W.rho θ)
    rw [mul_pow, Work.FTS.EllipticEst.H2W.Wf_sq_eq hs]
  rw [hkey]
  have hD : 0 ≤ D ^ 2 := sq_nonneg D
  have hr : 0 ≤ Work.FTS.EllipticEst.H2W.rho θ := Work.FTS.EllipticEst.H2W.rho_nonneg hθ
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have h := one_le_w hz
    nlinarith
  calc D ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = D ^ 2 * Work.FTS.EllipticEst.H2W.rho θ := by
        rw [Work.FTS.EllipticEst.H2W.rho]
    _ ≤ D ^ 2 * Work.FTS.EllipticEst.H2W.rho θ * (Work.Spaces.w z) ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg hD hr) hw
    _ = D ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.H2W.rho θ) := by ring

/-- The slice of a function `C^∞` on the open quadrant is `C^2` on `(0,π/2)`. -/
theorem contDiffOn_slice_two {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) :
    ContDiffOn ℝ 2 (fun θ : ℝ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hg.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

/-! ## §2 Almost everywhere strong measurability of the energy integrand -/

/-- The angular factor `sin(2θ)^{-η}` is continuous on the open quadrant. -/
theorem continuousOn_sin_rpow_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The energy integrand `θ ↦ (D_z^i g u θ)² sin(2θ)^{-η}` is a.e. strongly measurable. -/
theorem aesm_energy_slice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ)
    {u : ℝ} (hu : 0 < u) :
    AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
    (((hg.DzIter i).continuousOn).pow 2 |>.mul continuousOn_sin_rpow_Q0) hu

/-! ## §3 Integrability of the energy slice, and the energy/slot comparison -/

/-- The `ℋ²`-slot function `u ↦ ∫_θ (D_z^i g u θ)² sin(2θ)^{-η}` is dominated by the
`HkIntegrand`-slot of `g`. -/
theorem energy_le_slot_aux {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 g) (i : ℕ) (hi : i ≤ 2) {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ
          * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hslot := Work.FTS.EllipticEst.integrableOn_zSummand α 2 hg hB i hi (Set.mem_Ici.mpr hu.le)
  have henergy : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    Integrable.mono' hslot (aesm_energy_slice hg i hu) (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (rpow_neg_eta_nonneg hθ))]
      exact sq_mul_rpow_le_slot hθ hu)
  refine integral_mono_ae henergy hslot ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact sq_mul_rpow_le_slot hθ hu

/-- The `∂_θ²`-energy integrand of the slice `D_z^i Ψ` is integrable. -/
theorem integrableOn_pthIter2_slice {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine Integrable.mono'
    (Work.FTS.EllipticEst.integrableOn_zSummand α 2 ((hΨ.pth).pth) hB i hi
      (Set.mem_Ici.mpr hu.le)) ?_ ?_
  · exact (aesm_energy_slice ((hΨ.pth).pth) i hu).congr hae.symm
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ hθeq
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (rpow_neg_eta_nonneg hθ)), hθeq]
    exact sq_mul_rpow_le_slot hθ hu

/-- The `∂_θ²`-energy of the slice `D_z^i Ψ` is bounded by the `ℋ²`-slot of `∂_θ²Ψ`. -/
theorem energy_pthIter2_le_slot {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ
          * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hpt_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ
        = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ :=
    fun θ hθ => Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i
      (show (u, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθ⟩)
  have hae : (fun θ : ℝ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ) u θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt_eq] with θ hθ
    rw [hθ]
  refine le_trans (le_of_eq ?_) (energy_le_slot_aux ((hΨ.pth).pth) hB i hi hu)
  exact integral_congr_ae hae

/-! ## §4 The slice bound -/

/-- The weighted `ℋ²`-slot of `g` at the radius `u`. -/
def slot (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g u θ
    * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The majorant of `∫_θ |D_z^i Ψ(u,θ)| sinθcos²θ` delivered by the slice Taylor estimate. -/
def Bnd (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)

theorem slot_nonneg (g : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : 0 ≤ slot g i u :=
  integral_nonneg fun θ => sq_nonneg _

/-- **The angular slice bound** for `D_z^i Ψ`, `i ≤ 2`. -/
theorem slice_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u : ℝ, 0 < u →
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ
        ≤ Bnd Ψ i u := by
  intro u hu
  have hE := integrableOn_pthIter2_slice hΨ hB i hi hu
  obtain ⟨-, hbound⟩ := Work.FTS.EllipticEst.Mine.SliceMomentTaylor
    (contDiffOn_slice_two (hΨ.DzIter i) hu) hE
  have hsqrt : Real.sqrt (∫ θ in Work.Spaces.Iθ,
        deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
    have henergy : (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ slot (Work.Spaces.pthIter 2 Ψ) i u :=
      energy_pthIter2_le_slot hΨ hB i hi hu
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
          deriv (deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ)) θ ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u) := Real.sqrt_le_sqrt henergy
      _ ≤ slot (Work.Spaces.pthIter 2 Ψ) i u + 1 := by
          have h := slot_nonneg (Work.Spaces.pthIter 2 Ψ) i u
          nlinarith [Real.sq_sqrt h, sq_nonneg (Real.sqrt (slot (Work.Spaces.pthIter 2 Ψ) i u))]
  have hd1 : Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)
      = deriv (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ) (Real.pi / 4) := rfl
  rw [Bnd]
  rw [← hd1] at hbound
  linarith [hbound, hsqrt]

/-- `Bnd Ψ i` is integrable on `(a,b] ⊂ (0,∞)`. -/
theorem Bnd_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd Ψ i) (Set.Ioc a b) := by
  have h4 : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hsub2 : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have h1 : IntegrableOn (fun u : ℝ => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|)
      (Set.Icc a b) :=
    (((hΨ.DzIter i).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun u : ℝ => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|)
      (Set.Icc a b) :=
    ((((hΨ.DzIter i).pth).curry_z h4).continuousOn.mono hsub).abs.integrableOn_compact
      isCompact_Icc
  have h3 : IntegrableOn (slot (Work.Spaces.pthIter 2 Ψ) i) (Set.Icc a b) :=
    (Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 ((hΨ.pth).pth) hB i hi).mono_set
      (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1))
  have hsum : IntegrableOn (fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1)) (Set.Ioc a b) :=
    (((h1.mono_set hsub2).const_mul 3).add ((h2.mono_set hsub2).const_mul 9)).add
      (((h3.mono_set hsub2).add (integrableOn_const (by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))).const_mul 9)
  have hEq : Bnd Ψ i = fun u : ℝ => 3 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 9 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 9 * (slot (Work.Spaces.pthIter 2 Ψ) i u + 1) := rfl
  rw [hEq]
  exact hsum

/-! ## §5 Box integrability from a fibre bound -/

/-- **Integrability of a divided fibre bound.**  If the fibres `θ ↦ f r θ` are integrable with
`∫_θ |f r θ| ≤ B r` for `r ∈ (s,z]` and `B` is integrable there, then `(r,θ) ↦ f r θ / r` is
integrable on `(s,z] × Iθ`.  (This is the Tonelli step: the `θ`-integral of the absolute value
is dominated by `s⁻¹B`.) -/
theorem integrable_uncurry_div_of_fibre_bound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Work.Spaces.Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Work.Spaces.Iθ) := inferInstance
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Work.Spaces.Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Work.Spaces.Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Work.Spaces.Iθ, |f r θ / r| = (∫ θ in Work.Spaces.Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Work.Spaces.Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        exact le_trans hstep1 hstep2
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])

end Work.FTS.EllipticEst.H2W.PsiSlices
