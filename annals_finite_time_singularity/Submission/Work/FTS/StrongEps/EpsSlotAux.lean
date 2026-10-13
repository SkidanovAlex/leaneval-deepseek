/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSlotAux.lean` — differentiation under the `s`-integral

This module contains the general analytic machinery behind `Work.FTS.StrongEps.EpsSlotLip`:
the exchange of the iterated spatial operators `mixed j i = D_z^j D_θ^i` (for `j + i ≤ 4`) with
an interval integral over a *family* of profiles `s ↦ H s`,

  `mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ = ∫ s in a..b, mixed j i (H s) z θ`.

The hypotheses are exactly the ones available for the `ε`-scheme's right-hand side:

* `hsm` — every `H s` is `C^∞` on the open quadrant `Q0` (so every slot is differentiable);
* `hcont` — for each point of `Q0` the map `s ↦ H s z θ` is continuous on `[0,T]`
  (this is what makes the *slots* measurable in `s`, via the difference-quotient representation
  of `deriv` as a pointwise limit of continuous functions — see
  `Work.FTS.StrongEps.aemeasurable_mixed_family`);
* `hbdd` — a uniform bound on the slots of order `≤ 4` on a *closed box*
  `Icc z₁ z₂ ×ˢ Icc θ₁ θ₂ ⊆ Q0`.

The route is the two nested inductions of the file: the angular one
(`DthIter_intervalIntegral_eq`), then the radial one (`DzIter_intervalIntegral_eq`), each single
step being an instance of Mathlib's parametric differentiation
(`hasDerivAt_intervalIntegral_of_deriv_le`, the interval form of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), whose domination constant is
supplied by `hbdd` after dividing by `z` resp. by `sin (2θ)` (whence the lower bounds `z₁ > 0`
and `sin (2θ₁) > 0`, and the auxiliary `exists_pos_min_sin_two`).

`exists_uniform_compact_set` is the bookkeeping that turns a compact `K ⊆ Q0` into a compact
`S ⊆ Q0`, a `δ > 0` and, for every `p ∈ K`, a closed box around `p` inside `S` together with the
elementary bounds `2δ ≤ p.1`, `2δ ≤ p.2`, `p.2 + 2δ ≤ π/2`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.Blocks.HalfInfra
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Pointwise

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## Differentiation of an interval integral in the spatial variable -/

/-- **Parametric differentiation of an interval integral** (the `IntervalIntegral` form of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, in the shape used below:
the differentiation variable is the *first* argument of `G`, the integration variable `s` the
second one).

The hypotheses are those of Mathlib's lemma with the `∀ᶠ x in 𝓝 x₀` replaced by
`∀ x ∈ Ioo x₁ x₂` (so that the callers can discharge them from pointwise bounds). -/
theorem hasDerivAt_intervalIntegral_of_deriv_le {G G' : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    {a b x₀ x₁ x₂ : ℝ} (hx₁ : x₁ < x₀) (hx₂ : x₀ < x₂)
    (hG_meas : ∀ x ∈ Set.Ioo x₁ x₂,
      AEStronglyMeasurable (fun s : ℝ => G s x) (volume.restrict (Set.uIoc a b)))
    (hG_int : IntervalIntegrable (fun s : ℝ => G s x₀) volume a b)
    (hG'_meas : AEStronglyMeasurable (fun s : ℝ => G' s x₀) (volume.restrict (Set.uIoc a b)))
    (h_bound : ∀ t ∈ Set.uIoc a b, ∀ x ∈ Set.Ioo x₁ x₂, |G' t x| ≤ bound t)
    (h_bound_int : IntervalIntegrable bound volume a b)
    (h_diff : ∀ t ∈ Set.uIoc a b, ∀ x ∈ Set.Ioo x₁ x₂, HasDerivAt (fun x' => G t x') (G' t x) x) :
    HasDerivAt (fun x => ∫ s in a..b, G s x) (∫ s in a..b, G' s x₀) x₀ := by
  have hmem : Set.Ioo x₁ x₂ ∈ 𝓝 x₀ := isOpen_Ioo.mem_nhds ⟨hx₁, hx₂⟩
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x s => G s x) (F' := fun x s => G' s x) (bound := bound)
    (x₀ := x₀) (s := Set.Ioo x₁ x₂) hmem ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hmem] with x hx
    exact hG_meas x hx
  · exact hG_int
  · exact hG'_meas
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    simpa [Real.norm_eq_abs] using h_bound t ht x hx
  · exact h_bound_int
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    exact h_diff t ht x hx

/-- The `θ`-slice derivative of a `C^∞`-on-`Q0` function (the companion of the workspace lemma
`Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice`, which is the `z`-direction). -/
theorem SmoothOpen.hasDerivAt_slice_th {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  simpa only [Work.Spaces.pth] using hd.hasDerivAt

/-- A continuous function strictly positive on a compact interval has a positive lower bound. -/
theorem exists_pos_min_sin_two {θlo θhi : ℝ} (h0 : 0 < θlo) (h1 : θhi < Real.pi / 2) :
    ∃ smin : ℝ, 0 < smin ∧ ∀ y ∈ Set.Icc θlo θhi, smin ≤ Real.sin (2 * y) := by
  have hpos : ∀ y ∈ Set.Icc θlo θhi, (0:ℝ) < Real.sin (2 * y) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le h0 hy.1
    have hy1 : y < Real.pi / 2 := lt_of_le_of_lt hy.2 h1
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  obtain ⟨a', ha'pos, ha'⟩ := (isCompact_Icc).exists_forall_le' (f := fun y => Real.sin (2 * y))
    (by fun_prop) (a := 0) hpos
  exact ⟨a', ha'pos, ha'⟩

/-! ## Locality of the iterated operators on an open set -/

/-- `∂_z` is local on an open set. -/
theorem pz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hzθ)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  simpa only [Work.Spaces.pz] using hev.deriv_eq

/-- `∂_θ` is local on an open set. -/
theorem pth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hzθ)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  simpa only [Work.Spaces.pth] using hev.deriv_eq

/-- The iterates `D_z^j` are local on an open set. -/
theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    have hzp : Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2 := pz_congr_of_isOpen hV ih hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
    rw [hzp]

/-- The mixed slots `D_z^jD_θ^i` are local on an open set. -/
theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  intro p hp
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V :=
    Work.Blocks.Half.DthIter_congrOn hV h i
  exact DzIter_congr_of_isOpen hV h1 j hp

/-! ## The angular induction -/

/-- **The angular part of the exchange.**  For a family `H` with the hypotheses described at the
top of the file, the `D_θ`-iterates (`i ≤ 4`) of the interval integral are the interval integrals
of the `D_θ`-iterates, on the interior of the closed box. -/
theorem DthIter_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (l : ℕ) (hl : l ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction l with
  | zero => intro z θ _; rfl
  | succ l ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hzcl : z ∈ Set.Icc z₁ z₂ := ⟨le_of_lt hzz.1, le_of_lt hzz.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set θlo : ℝ := max θ₁ (θ / 2) with hθlo
    set θhi : ℝ := min θ₂ ((θ + Real.pi / 2) / 2) with hθhi
    have hθlo_lt : θlo < θ := by
      rw [hθlo]; exact max_lt hθθ.1 (by linarith)
    have hθ_lt_θhi : θ < θhi := by
      rw [hθhi]; exact lt_min hθθ.2 (by linarith)
    have hθlo0 : 0 < θlo := lt_of_lt_of_le (by linarith : (0:ℝ) < θ / 2) (le_max_right _ _)
    have hθhi_lt : θhi < Real.pi / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨smin, hsmin_pos, hsmin_le⟩ := exists_pos_min_sin_two hθlo0 hθhi_lt
    have hmem_box : ∀ y ∈ Set.Ioo θlo θhi,
        (z, y) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro y hy
      exact ⟨hzcl, ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hy.1),
        le_of_lt (lt_of_lt_of_le hy.2 (min_le_left _ _))⟩⟩
    have hyQ : ∀ y ∈ Set.Ioo θlo θhi, (z, y) ∈ Work.FTS.EllipticEst.Q0 :=
      fun y hy => hboxQ (hmem_box y hy)
    have hyf : ∀ y ∈ Set.Ioo θlo θhi, 0 < y ∧ y < Real.pi / 2 := by
      intro y hy
      obtain ⟨-, hy1, hy2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hyQ y hy)
      exact ⟨hy1, hy2⟩
    have hcore := hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t y => Work.Spaces.DthIter l (H t) z y)
      (G' := fun t y => Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y))
      (bound := fun _ => C / smin) hθlo_lt hθ_lt_θhi ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro y hy
      have := (hmeas 0 l z y (hyQ y hy)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed_zero_left] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas 0 l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed_zero_left] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        have := hbdd t htT 0 l (by omega) (z, θ) ⟨hzcl, ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩⟩
        simpa only [Work.Spaces.mixed_zero_left] using this
    · have h1 := (hmeas 0 (l + 1) z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const (Real.sin (2 * θ))⁻¹
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hsinpos : 0 < Real.sin (2 * y) :=
        lt_of_lt_of_le hsmin_pos (hsmin_le y (Set.Ioo_subset_Icc_self hy))
      have hb := hbdd t htT 0 (l + 1) (by omega) (z, y) (hmem_box y hy)
      calc |Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y)|
          = |Work.Spaces.mixed 0 (l + 1) (H t) z y| / Real.sin (2 * y) := by
            rw [abs_div, abs_of_pos hsinpos]
        _ ≤ C / Real.sin (2 * y) := div_le_div_of_nonneg_right hb (le_of_lt hsinpos)
        _ ≤ C / smin := div_le_div_of_nonneg_left hC hsmin_pos
            (hsmin_le y (Set.Ioo_subset_Icc_self hy))
    · exact intervalIntegrable_const
    · intro t ht y hy
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder := SmoothOpen.hasDerivAt_slice_th
        (Work.FTS.LocData.contDiffOn_DthIter Work.FTS.EllipticEst.isOpen_Q0
          (hsm t htT) l) hz0 (hyf y hy)
      have hid : Work.Spaces.pth (Work.Spaces.DthIter l (H t)) z y
          = Work.Spaces.mixed 0 (l + 1) (H t) z y / Real.sin (2 * y) := by
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.FTS.StrongEps.LocUnif.pth_mixed_div 0 l (hsm t htT) z y (hyQ y hy)
      exact hder.congr_deriv hid
    have hev : (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) =ᶠ[𝓝 θ]
        (fun y => ∫ s in a..b, Work.Spaces.DthIter l (H s) z y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθθ] with y hy
      exact ih (by omega) z y ⟨hzz, hy⟩
    have hpth : Work.Spaces.pth (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ) := by
      show deriv (fun y => Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ) z y) θ = _
      rw [hev.deriv_eq, hcore.deriv]
    have hsinne : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    calc Work.Spaces.DthIter (l + 1) (fun z θ => ∫ s in a..b, H s z θ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth
            (Work.Spaces.DthIter l (fun z θ => ∫ s in a..b, H s z θ)) z θ := by
          rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      _ = Real.sin (2 * θ) * (∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ / Real.sin (2 * θ)) := by rw [hpth]
      _ = Real.sin (2 * θ) * ((∫ s in a..b,
            Work.Spaces.mixed 0 (l + 1) (H s) z θ) / Real.sin (2 * θ)) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed 0 (l + 1) (H s) z θ :=
          mul_div_cancel₀ _ hsinne
      _ = ∫ s in a..b, Work.Spaces.DthIter (l + 1) (H s) z θ := rfl

/-! ## The radial induction -/

/-- **The radial part of the exchange.**  For a family `H` with the hypotheses described at the
top of the file, the `D_z`-iterates of the interval integral of `D_θ^i (H s)` are the interval
integrals of `D_z^j D_θ^i (H s)`, for `j + i ≤ 4`. -/
theorem DzIter_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l x θ (hxQ x hx)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

/-! ## The exchange for `mixed j i` -/

/-- **The exchange of `mixed j i` (`j + i ≤ 4`) with the interval integral.** -/
theorem mixed_intervalIntegral_eq {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (volume.restrict (Set.Icc (0:ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 4) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ i (by omega)
  have hB := DzIter_intervalIntegral_eq (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

/-! ## The compact box around a compact subset of the open quadrant -/

/-- **A compact `S ⊆ Q0` around a compact `K ⊆ Q0`, together with a box around each point.**
There are `δ > 0` and a compact `S ⊆ Q0` such that for every `p ∈ K` the box of radius `δ/2`
around `p` is contained in `S`, and `2δ ≤ p.1`, `2δ ≤ p.2`, `p.2 + 2δ ≤ π/2` (so that the boxes
have positive radial and angular lower bounds and stay below `π/2`). -/
theorem exists_uniform_compact_set (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ S : Set (ℝ × ℝ), IsCompact S ∧ S ⊆ Work.FTS.EllipticEst.Q0 ∧
      ∃ δ : ℝ, 0 < δ ∧ (∀ p ∈ K, 2 * δ ≤ p.1) ∧ (∀ p ∈ K, 2 * δ ≤ p.2) ∧
        (∀ p ∈ K, p.2 + 2 * δ ≤ Real.pi / 2) ∧
        (∀ p ∈ K, ∀ x : ℝ, |x - p.1| ≤ δ → (x, p.2) ∈ S) ∧
        (∀ p ∈ K, ∀ y : ℝ, |y - p.2| ≤ δ → (p.1, y) ∈ S) ∧
        (∀ p ∈ K, ∀ x y : ℝ, |x - p.1| ≤ δ / 2 → |y - p.2| ≤ δ / 2 → (x, y) ∈ S) := by
  rcases K.eq_empty_or_nonempty with hEmpty | hne
  · subst hEmpty
    exact ⟨∅, isCompact_empty, by simp, 1, one_pos, by simp, by simp, by simp,
      by simp, by simp, by simp⟩
  · have hcont : Continuous fun p : ℝ × ℝ => min p.1 (min p.2 (Real.pi / 2 - p.2)) := by fun_prop
    have hpos : ∀ p ∈ K, (0:ℝ) < min p.1 (min p.2 (Real.pi / 2 - p.2)) := by
      intro p hp
      obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
      exact lt_min hp1 (lt_min hp2 (by linarith))
    obtain ⟨m, hmpos, hm⟩ := hK.exists_forall_le' hcont.continuousOn (a := 0) hpos
    have hm1 : ∀ p ∈ K, m ≤ p.1 := fun p hp => le_trans (hm p hp) (min_le_left _ _)
    have hm2 : ∀ p ∈ K, m ≤ p.2 :=
      fun p hp => le_trans (hm p hp) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hm3 : ∀ p ∈ K, m ≤ Real.pi / 2 - p.2 :=
      fun p hp => le_trans (hm p hp) (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨K + Metric.closedBall (0 : ℝ × ℝ) (m / 4), hK.add (isCompact_closedBall _ _), ?_,
      m / 4, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro q ⟨p, hp, v, hv, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv
      have hv1 : |v.1| ≤ m / 4 := by
        have := le_trans (norm_fst_le v) hv
        simpa [Real.norm_eq_abs] using this
      have hv2 : |v.2| ≤ m / 4 := by
        have := le_trans (norm_snd_le v) hv
        simpa [Real.norm_eq_abs] using this
      refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨?_, ?_, ?_⟩
      · show 0 < p.1 + v.1
        linarith [hm1 p hp, hv1, neg_abs_le v.1]
      · show 0 < p.2 + v.2
        linarith [hm2 p hp, hv2, neg_abs_le v.2]
      · show p.2 + v.2 < Real.pi / 2
        linarith [hm3 p hp, hv2, abs_le.mp hv2]
    · intro p hp; have h := hm1 p hp; linarith
    · intro p hp; have h := hm2 p hp; linarith
    · intro p hp; have h := hm3 p hp; linarith
    · intro p hp x hx
      refine Set.mem_add.mpr ⟨p, hp, (x - p.1, 0), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, max_le_iff]
        refine ⟨?_, ?_⟩
        · simpa [Real.norm_eq_abs] using hx
        · rw [norm_zero]; linarith
      · ext <;> simp
    · intro p hp y hy
      refine Set.mem_add.mpr ⟨p, hp, (0, y - p.2), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, max_le_iff]
        refine ⟨?_, ?_⟩
        · rw [norm_zero]; linarith
        · simpa [Real.norm_eq_abs] using hy
      · ext <;> simp
    · intro p hp x y hx hy
      refine Set.mem_add.mpr ⟨p, hp, (x - p.1, y - p.2), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, max_le_iff]
        refine ⟨?_, ?_⟩
        · rw [Real.norm_eq_abs]; linarith
        · rw [Real.norm_eq_abs]; linarith
      · ext <;> simp

end Work.FTS.StrongEps
