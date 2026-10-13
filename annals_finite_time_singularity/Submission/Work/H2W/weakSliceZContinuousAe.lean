/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.H2W.weakSliceZContinuousAe`

For every datum `(F, Ψ)` of the weak hypothesis class
`Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ` (with `0 < α ≤ 1/4`) and almost every `z > 0`, the
two angular slices

  `θ ↦ z ^ 2 * ∂_z²Ψ(z,θ)`   and   `θ ↦ D_z²Ψ(z,θ) = (z∂_z)²Ψ(z,θ)`

are continuous on the closed angular interval `[0, π/2]`.

## Route

Both slices are `C^∞` on the *open* interval and both vanish at both endpoints (because
`Ψ · 0 ≡ Ψ · (π/2) ≡ 0`, so all `z`-derivatives vanish there).  Continuity on `Icc` therefore
reduces to the two one-sided endpoint limits, which are obtained as follows.

* **Right endpoint.**  `Work.FTS.EllipticEst.H2W.weakSliceLimits` gives, for a `C^∞` slice whose
  second derivative is `L²(sEta)` and whose `Lzero1` is `L²(sEta)`, the limit `0` at `(π/2)⁻`
  (the Dirichlet value at `π/2` is `0`).  The two weighted `L²`-hypotheses are
  `aSliceHonest` (the field `HkMem α 2 (z²∂_z²Ψ)` re-read as a slice estimate) and
  `Work.H2W.asliceLzero1Energy`.

* **Left endpoint.**  `Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment` gives
  `lim_{0⁺} = -∫_θ Lzero1(slice)·sinθcos²θ`, so it suffices that the angular moment of the
  `Lzero1` of the slice vanishes.  For the slice `A := z²∂_z²Ψ` this moment equals

    `F_*(D_z²F)(z) + α² F_*(D_z⁴Ψ)(z)`

  (`Work.H2W.asliceMomentEq`, a purely algebraic computation from `bslOp α A = D_z²F - D_zF` on
  the open quadrant and the pointwise moments `F_*(D_z^jΨ) = 0`, `j ≤ 3`), and both summands
  vanish for almost every `z > 0`: the first is `Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F_ae`,
  the second is `Work.H2W.fstarDzIterFourAe` (the level-`4` `Ψ`-moment).

The second conjunct follows from the first together with the continuity of the `D_zΨ`-slice
(`Work.H2W.dzPsiSliceLimits`, which gives the two endpoint limits of `θ ↦ ∂_zΨ(z,θ)`) and the
product rule `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open interval, the endpoint values being `0`.

Everything is assembled a.e. in `z`; the four analytic inputs are the sibling modules
`fstarDzIterFourAe`, `asliceLzero1Energy`, `asliceMomentEq`, `dzPsiSliceLimits`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiFinal
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F
import Submission.Work.FTS.EllipticEst.H2W.aSliceHonest
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots
import Submission.Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
import Submission.Work.H2W.momentChainAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.H2W.asliceLzero1Energy
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H2W.dzPsiSliceLimits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2W

set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## Slice continuity on `Icc` from the two one-sided endpoint limits -/

theorem continuousWithinAt_Icc_of_tendsto_Ioi {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (h : Filter.Tendsto f (𝓝[>] a) (𝓝 c)) (hv : f a = c) :
    ContinuousWithinAt f (Set.Icc a b) a := by
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab, hv]
  rw [Filter.tendsto_def]
  intro V hV
  have hVc : c ∈ V := mem_of_mem_nhds hV
  obtain ⟨δ, hδ, hsub⟩ := (nhdsGT_basis a).eventually_iff.1 (h.eventually hV)
  refine mem_of_superset ((mem_nhdsGE_iff_exists_Ico_subset).2 ⟨δ, hδ, subset_rfl⟩) ?_
  intro x hx
  rw [Set.mem_Ico] at hx
  rw [Set.mem_preimage]
  rcases eq_or_lt_of_le hx.1 with h' | h'
  · rw [← h', hv]; exact hVc
  · exact hsub ⟨h', hx.2⟩

theorem continuousWithinAt_Icc_of_tendsto_Iio {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (h : Filter.Tendsto f (𝓝[<] b) (𝓝 c)) (hv : f b = c) :
    ContinuousWithinAt f (Set.Icc a b) b := by
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab, hv]
  rw [Filter.tendsto_def]
  intro V hV
  have hVc : c ∈ V := mem_of_mem_nhds hV
  obtain ⟨δ, hδ, hsub⟩ := (nhdsLT_basis b).eventually_iff.1 (h.eventually hV)
  obtain ⟨δ', hδ1, hδ2⟩ := exists_between hδ
  refine mem_of_superset ((mem_nhdsLE_iff_exists_Icc_subset).2 ⟨δ', hδ2, subset_rfl⟩) ?_
  intro x hx
  rw [Set.mem_Icc] at hx
  rw [Set.mem_preimage]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h', hv]; exact hVc
  · exact hsub ⟨lt_of_lt_of_le hδ1 hx.1, h'⟩

/-- A function which is continuous on the open angular interval and has the right one-sided
limit at both endpoints is continuous on the closed interval `[0, π/2]`. -/
theorem continuousOn_Icc_of_limits {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)))
    (h1 : Filter.Tendsto f (𝓝[<] (Real.pi / 2)) (𝓝 (f (Real.pi / 2)))) :
    ContinuousOn f (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx
  rw [Set.mem_Icc] at hx
  rcases eq_or_lt_of_le hx.1 with h' | h'
  · subst h'
    exact continuousWithinAt_Icc_of_tendsto_Ioi (by positivity) h0 rfl
  · rcases eq_or_lt_of_le hx.2 with h'' | h''
    · subst h''
      exact continuousWithinAt_Icc_of_tendsto_Iio (by positivity) h1 rfl
    · exact ((hf.continuousWithinAt (show x ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h', h''⟩)).continuousAt
        (isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h', h''⟩))).continuousWithinAt

/-- A function continuous on the open angular interval is a.e. strongly measurable for the
restricted measure on `Iθ` (the two endpoints are null). -/
theorem aesm_of_continuousOn_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Iθ) := by
  have h1 : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aestronglyMeasurable measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))] at h1
  exact h1

/-! ## The endpoint values of the slices

`Ψ · 0` and `Ψ · (π/2)` are identically zero (`EllWeakPos.zero`, `EllWeakPos.pi_half`), so all
`z`-derivatives of `Ψ`, and hence all the slices appearing below, vanish at `θ = 0` and
`θ = π/2`. -/

theorem pz_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pz Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Ψ z' 0) = fun _ => (0 : ℝ) := funext fun z' => h.zero z'
  show deriv (fun z' : ℝ => Ψ z' 0) z = 0
  rw [hfun, deriv_const]

theorem pz_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pz Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => h.pi_half z'
  show deriv (fun z' : ℝ => Ψ z' (Real.pi / 2)) z = 0
  rw [hfun, deriv_const]

theorem pzIter_two_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pzIter 2 Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => pz_zero_at_zero h z'
  show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' 0) z = 0
  rw [hfun, deriv_const]

theorem pzIter_two_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.pz Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => pz_zero_at_pi_half h z'
  show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' (Real.pi / 2)) z = 0
  rw [hfun, deriv_const]

theorem aslice_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0 := by
  rw [pzIter_two_zero_at_zero h z, mul_zero]

theorem aslice_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 := by
  rw [pzIter_two_zero_at_pi_half h z, mul_zero]

theorem dz_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.Dz Ψ z 0 = 0 := by
  show z * Work.Spaces.pz Ψ z 0 = 0
  rw [pz_zero_at_zero h z, mul_zero]

theorem dz_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.Dz Ψ z (Real.pi / 2) = 0 := by
  show z * Work.Spaces.pz Ψ z (Real.pi / 2) = 0
  rw [pz_zero_at_pi_half h z, mul_zero]

theorem dzIter_two_zero_at_zero (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z 0 = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => dz_zero_at_zero h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0 = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z 0
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' 0) z from rfl, hfun, deriv_const,
    mul_zero]

theorem dzIter_two_zero_at_pi_half (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (z : ℝ) :
    Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
  have hfun : (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => dz_zero_at_pi_half h z'
  show z * Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2) = 0
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 Ψ) z (Real.pi / 2)
      = deriv (fun z' : ℝ => Work.Spaces.DzIter 1 Ψ z' (Real.pi / 2)) z from rfl, hfun,
    deriv_const, mul_zero]

/-! ## Integrability of the square of the `A`-slice -/

/-- `(z²∂_z²Ψ(z,·))²` is integrable on `Iθ`: it is the `i = 0` weighted `D_z`-slot of
`HkMem α 2 (z²∂_z²Ψ)`, divided by the weight `sEta ≥ 1` on the open interval. -/
theorem aslice_sq_integrableOn (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hslot :=
    (Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots (k := 2) (le_refl 2) h z hz)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h1 := hslot.2.2.2.2.1
    refine MeasureTheory.IntegrableOn.congr_fun (h1.const_mul (z ^ 4))
      (fun θ _ => ?_) measurableSet_Icc
    show z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    ring
  have hcont : ContinuousOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.SmoothOpen.curry_θ
      (Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso) hz).continuousOn).pow 2
  have haesm := aesm_of_continuousOn_Ioo hcont
  refine Integrable.mono' h2 haesm ?_
  have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
      ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2‖
        ≤ (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hs : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
        rw [Work.FTS.EllipticEst.sEta]
        have h0 : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
        have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
        have h3 := Real.rpow_le_rpow_of_nonpos h0 h1 h2
        rwa [Real.one_rpow] at h3
      nlinarith [sq_nonneg (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)])
  exact hb

/-! ## The `A`-slice is continuous on `Icc` when the two moments vanish -/

/-- If the two moments `F_*(D_z²F)(z)` and `F_*(D_z⁴Ψ)(z)` vanish, then the `A`-slice
`θ ↦ z²∂_z²Ψ(z,θ)` is continuous on the closed angular interval. -/
theorem aslice_continuousOn (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (h2F : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0)
    (h4 : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0) :
    ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hall : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) := fun n =>
    contDiffOn_iff_forall_nat_le.mp (hAso.curry_θ hz) n le_top
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.H2W.aSliceHonest α F Ψ hα hα4 h z (Set.mem_Ici.mpr hz.le)
  have hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1
        (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    asliceLzero1Energy α F Ψ h z hz
  have h3 := aslice_sq_integrableOn (α := α) (F := F) h hz
  have hmom : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1
      (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ * Work.Elliptic.sinCos2 θ) = 0 := by
    rw [asliceMomentEq α F Ψ h z hz, h2F, h4]
    ring
  have hleft := Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
    (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (hall 2) h2 hL h3 hmom
  have hright := (Work.FTS.EllipticEst.H2W.weakSliceLimits
    (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hall (aslice_zero_at_zero h z)
    (aslice_zero_at_pi_half h z) h2 hL).2.2.1
  exact continuousOn_Icc_of_limits (hall 0).continuousOn
    (by rw [aslice_zero_at_zero h z]; exact hleft)
    (by rw [aslice_zero_at_pi_half h z]; exact hright)

/-! ## The `D_zΨ`-slice is continuous on `Icc` -/

theorem dzPsi_continuousOn (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.Dz Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hl, hr⟩ := dzPsiSliceLimits α F Ψ h z hz
  have hcont : ContinuousOn (fun θ => z * Work.Spaces.pz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.SmoothOpen.curry_θ (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)
      hz).continuousOn).const_mul z
  have h0 : Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := hl.const_mul z
    simpa using hh
  have hp : Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hh := hr.const_mul z
    simpa using hh
  exact continuousOn_Icc_of_limits hcont
    (by
      show Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[>] (0 : ℝ))
        (𝓝 (z * Work.Spaces.pz Ψ z 0))
      rw [pz_zero_at_zero h z, mul_zero]
      exact h0)
    (by
      show Filter.Tendsto (fun θ => z * Work.Spaces.pz Ψ z θ) (𝓝[<] (Real.pi / 2))
        (𝓝 (z * Work.Spaces.pz Ψ z (Real.pi / 2)))
      rw [pz_zero_at_pi_half h z, mul_zero]
      exact hp)

/-! ## The `D_z²Ψ`-slice is continuous on `Icc` when the two moments vanish -/

/-- The `D_z²Ψ`-slice is the sum of the `D_zΨ`-slice (continuous by `dzPsi_continuousOn`) and
the `A`-slice (continuous when the two moments vanish), by the product rule
`D_z²Ψ = D_zΨ + z²∂_z²Ψ`; the identity also holds at the two endpoints, where every term is `0`. -/
theorem dzIterTwo_continuousOn (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (h2F : Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0)
    (h4 : Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0) :
    ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA := aslice_continuousOn hα hα4 h hz h2F h4
  have hdz := dzPsi_continuousOn (α := α) (F := F) h hz
  refine (hdz.add hA).congr ?_
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]
    show Work.Spaces.DzIter 2 Ψ z 0
      = Work.Spaces.Dz Ψ z 0 + z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0
    rw [aslice_zero_at_zero h z, dz_zero_at_zero h z, dzIter_two_zero_at_zero h z]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1]
      show Work.Spaces.DzIter 2 Ψ z (Real.pi / 2)
        = Work.Spaces.Dz Ψ z (Real.pi / 2) + z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2)
      rw [aslice_zero_at_pi_half h z, dz_zero_at_pi_half h z,
        dzIter_two_zero_at_pi_half h z]
      ring
    · show Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      rw [Work.FTS.EllipticEst.H2W.PsiSlices.DzIter_two_eq hΨso hz ⟨h0, h1⟩,
        show Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl]

/-! ## The target -/

theorem weakSliceZContinuousAe : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.Dz (Work.Spaces.Dz Ψ) z θ)
            (Set.Icc 0 (Real.pi / 2)) := by
  intro α F Ψ hα hα4 h
  have hfour : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 4 Ψ) z = 0 := fstarDzIterFourAe α F Ψ h
  have htwoF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 :=
    Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F_ae α F Ψ h
  have hgoal : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2))
        ∧ ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := by
    filter_upwards [hfour, htwoF, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z h4z h2Fz _
    intro hz
    exact ⟨aslice_continuousOn hα hα4 h hz h2Fz h4z,
      dzIterTwo_continuousOn hα hα4 h hz h2Fz h4z⟩
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hgoal
  filter_upwards [hgoal] with z hz _ hzpos
  exact hz (Set.mem_Ioi.mpr hzpos) hzpos

end Work.H2W
