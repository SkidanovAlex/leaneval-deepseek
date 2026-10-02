import Mathlib
import Submission.Work.Thom.relCohMap_homotopic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The pullback `H⁸(ℝ⁸, ℝ⁸∖0) → H⁸(D, D∖0)` depends only on the derivative at the origin

Let `g : ℝ⁸ → ℝ⁸` be continuous near `0`, with `g 0 = 0`, `g ≠ 0` off `0` and differentiable at `0`
with derivative `L` (a linear isomorphism).  Then the two maps of pairs
`(D, D∖0) → (ℝ⁸, ℝ⁸∖0)` given by `g` and by `L` agree on relative cohomology.

The proof is homotopy invariance.  On the ball of radius `r'` the two maps are homotopic through
maps of pairs: with `s ∈ (0,1]` so small that the straight segment between `g w` and `L w` avoids the
origin for `‖w‖ ≤ s r'` (this is the differentiability of `g` at `0` together with the injectivity
of `L`), the homotopy runs

`g(z) → g(s z) → (straight line) → L(s z) → L(z)`

where the first and last steps interpolate `z` and `s z` radially.
-/

namespace Work.ThomBordism.FrameSigns

open scoped unitInterval Topology

/-- The model space `ℝ⁸`. -/
abbrev E8 : Type := EuclideanSpace ℝ (Fin 8)

/-- The closed ball of radius `r'` in `ℝ⁸`: the common domain of the maps compared. -/
abbrev FrameBall (r' : ℝ) : Type := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) r')

/-- The affine interpolation between the identity and the scaling by `s`: `z ↦ ((1-u) + u s) • z`. -/
abbrev germAff (s u : ℝ) (z : E8) : E8 := ((1 - u) + u * s) • z

/-- The norm of an element of the closed ball of radius `r'` is at most `r'`. -/
theorem norm_coe_le {r' : ℝ} (z : FrameBall r') : ‖(z : E8)‖ ≤ r' := by
  have h := Metric.mem_closedBall.mp z.2
  rwa [dist_eq_norm, sub_zero] at h

@[simp] theorem germAff_zero (s : ℝ) (z : E8) : germAff s 0 z = z := by
  show ((1 - 0) + 0 * s) • z = z
  simp

@[simp] theorem germAff_one (s : ℝ) (z : E8) : germAff s 1 z = s • z := by
  show ((1 - 1) + 1 * s) • z = s • z
  simp

theorem continuous_germAff (s : ℝ) {Y : Type*} [TopologicalSpace Y] {u : Y → ℝ} {z : Y → E8}
    (hu : Continuous u) (hz : Continuous z) : Continuous fun y => germAff s (u y) (z y) := by
  unfold germAff
  exact (((continuous_const : Continuous fun _ : Y => (1:ℝ)).sub hu).add
    (hu.mul (continuous_const : Continuous fun _ : Y => s))).smul hz

/-- **The derivative gives a uniform estimate on a ball.**  If `L` is an invertible linear map and
`g` is differentiable at `0` with derivative `L` and `g 0 = 0`, then on a suitable ball the
difference `g - L` is dominated by `L/2`. -/
theorem exists_pos_mul_norm_le_of_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : E →L[ℝ] E} (hL : Function.Bijective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : E, c * ‖z‖ ≤ ‖L z‖ := by
  let e₀ : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (L : E →ₗ[ℝ] E) hL
  let e : E ≃L[ℝ] E := e₀.toContinuousLinearEquiv
  have hle : ∀ z : E, e z = L z := by
    intro z
    have h1 : e z = e₀ z := rfl
    have h2 : e₀ z = L z := by
      rw [LinearEquiv.ofBijective_apply]
      rfl
    exact h1.trans h2
  have hMz : ∀ z : E, ‖z‖ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖L z‖ := by
    intro z
    have hsym : (e.symm : E →L[ℝ] E) (e z) = z := by
      simp only [← ContinuousLinearEquiv.coe_toLinearEquiv]
      exact ContinuousLinearEquiv.symm_apply_apply e z
    calc ‖z‖ = ‖(e.symm : E →L[ℝ] E) (e z)‖ := by rw [hsym]
      _ = ‖(e.symm : E →L[ℝ] E) (L z)‖ := by rw [hle z]
      _ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
  refine ⟨(max ‖(e.symm : E →L[ℝ] E)‖ 1)⁻¹,
    inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _)), fun z => ?_⟩
  rw [inv_mul_le_iff₀ (lt_of_lt_of_le one_pos (le_max_right ‖(e.symm : E →L[ℝ] E)‖ 1))]
  calc ‖z‖ ≤ ‖(e.symm : E →L[ℝ] E)‖ * ‖L z‖ := hMz z
    _ ≤ max ‖(e.symm : E →L[ℝ] E)‖ 1 * ‖L z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **The germ estimate.**  If `L` is bijective, `g 0 = 0` and `g` is differentiable at `0` with
derivative `L`, then `‖g w - L w‖ ≤ ‖L w‖ / 2` on a ball around `0`. -/
theorem exists_norm_sub_le_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} {L : E →L[ℝ] E} (hL : Function.Bijective L)
    (hg0 : g 0 = 0) (hgd : HasFDerivAt g L 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : E, ‖z‖ ≤ δ → ‖g z - L z‖ ≤ (1/2) * ‖L z‖ := by
  obtain ⟨c, hc, hcL⟩ := exists_pos_mul_norm_le_of_bijective hL
  have hlit : (fun z : E => g z - L z) =o[𝓝 (0:E)] fun z : E => z := by
    have h := hgd.isLittleO
    simpa [hg0] using h
  have hev : ∀ᶠ z in 𝓝 (0:E), ‖g z - L z‖ ≤ (c/2) * ‖z‖ :=
    hlit.def (c := c/2) (by linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2, by linarith, fun z hz => ?_⟩
  have hmem : z ∈ Metric.ball (0:E) δ := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have h2 : ‖g z - L z‖ ≤ (c/2) * ‖z‖ := hδsub hmem
  have h3 : (c/2) * ‖z‖ ≤ (1/2) * ‖L z‖ := by
    have := hcL z
    linarith
  linarith

theorem germFDeriv (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 8))
    (L : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (hgc : ContinuousOn g (Metric.closedBall 0 r))
    (hL : Function.Bijective L) (hg0 : g 0 = 0)
    (hgd : HasFDerivAt g L 0)
    (hnz : ∀ z ∈ Metric.closedBall (0:EuclideanSpace ℝ (Fin 8)) r, z ≠ 0 → g z ≠ 0)
    (r' : ℝ) (hr' : 0 < r') (hr'r : r' ≤ r)
    (ξ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) ({0}ᶜ)) :
    (Work.Thom.relCohMap
      (⟨fun z : ↥(Metric.closedBall (0:EuclideanSpace ℝ (Fin 8)) r') => g (z : EuclideanSpace ℝ (Fin 8)),
        continuousOn_iff_continuous_domRestrict.mp
          (hgc.mono (Metric.closedBall_subset_closedBall hr'r))⟩ :
        C(↥(Metric.closedBall (0:EuclideanSpace ℝ (Fin 8)) r'), EuclideanSpace ℝ (Fin 8)))
      {z | (z : EuclideanSpace ℝ (Fin 8)) ≠ 0} ({0}ᶜ)
      (fun z hz => hnz (z : EuclideanSpace ℝ (Fin 8)) (Metric.closedBall_subset_closedBall hr'r z.2) hz)
      ℤ 8).hom ξ
    = (Work.Thom.relCohMap
      (⟨fun z : ↥(Metric.closedBall (0:EuclideanSpace ℝ (Fin 8)) r') => L (z : EuclideanSpace ℝ (Fin 8)),
        L.continuous.comp continuous_subtype_val⟩ :
        C(↥(Metric.closedBall (0:EuclideanSpace ℝ (Fin 8)) r'), EuclideanSpace ℝ (Fin 8)))
      {z | (z : EuclideanSpace ℝ (Fin 8)) ≠ 0} ({0}ᶜ)
      (fun z hz => by
        intro h
        exact hz (hL.1 (by simpa using h)))
      ℤ 8).hom ξ := by
  obtain ⟨δ, hδpos, hδest⟩ := exists_norm_sub_le_half (E := E8) hL hg0 hgd
  set s : ℝ := min 1 (δ / r') with hs
  have hs_pos : 0 < s := lt_min one_pos (div_pos hδpos hr')
  have hs_le_one : s ≤ 1 := min_le_left _ _
  have hsr : s * r' ≤ δ := by
    have h2 : s ≤ δ / r' := min_le_right _ _
    calc s * r' ≤ (δ / r') * r' := mul_le_mul_of_nonneg_right h2 hr'.le
      _ = δ := by rw [div_mul_cancel₀ _ (ne_of_gt hr')]
  let X : Type := FrameBall r'
  let A : Set X := {z | (z : E8) ≠ 0}
  let B : Set E8 := ({0}ᶜ : Set E8)
  let F : C(X, E8) := ⟨fun z => g z,
    continuousOn_iff_continuous_domRestrict.mp
      (hgc.mono (Metric.closedBall_subset_closedBall hr'r))⟩
  let G : C(X, E8) := ⟨fun z => L z, L.continuous.comp continuous_subtype_val⟩
  have hΦmem : ∀ z : X, s • (z : E8) ∈ Metric.closedBall (0 : E8) r' := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖s • (z : E8)‖ = s * ‖(z : E8)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      _ ≤ s * r' := mul_le_mul_of_nonneg_left (norm_coe_le z) hs_pos.le
      _ ≤ r' := by
          calc s * r' ≤ 1 * r' := mul_le_mul_of_nonneg_right hs_le_one hr'.le
            _ = r' := one_mul r'
  let Φ : C(X, X) := ⟨fun z => ⟨s • (z : E8), hΦmem z⟩,
      Continuous.subtype_mk
        ((continuous_const : Continuous fun _ : X => (s:ℝ)).smul continuous_subtype_val) hΦmem⟩
  have hΦne : ∀ z : X, (z : E8) ≠ 0 → (Φ z : E8) ≠ 0 := by
    intro z hz h
    exact hz ((smul_eq_zero.mp h).resolve_left (ne_of_gt hs_pos))
  have hF : ∀ z ∈ A, F z ∈ B := fun z hz =>
    hnz (z : E8) (Metric.closedBall_subset_closedBall hr'r z.2) hz
  have hG : ∀ z ∈ A, G z ∈ B := fun z hz => by
    show L (z : E8) ≠ 0
    intro h
    exact hz (hL.1 (by simpa using h))
  have hFΦ : ∀ z ∈ A, (F.comp Φ) z ∈ B := fun z hz => hF (Φ z) (hΦne z hz)
  have hGΦ : ∀ z ∈ A, (G.comp Φ) z ∈ B := fun z hz => hG (Φ z) (hΦne z hz)
  change (Work.Thom.relCohMap F A B hF ℤ 8).hom ξ
    = (Work.Thom.relCohMap G A B hG ℤ 8).hom ξ
  have hSnorm : ∀ (u : ℝ), u ∈ Set.Icc (0:ℝ) 1 → ∀ z : X, ‖germAff s u (z : E8)‖ ≤ r' := by
    intro u hu z
    have hz : ‖(z : E8)‖ ≤ r' := norm_coe_le z
    have hcoef_le : (1 - u) + u * s ≤ 1 := by
      nlinarith [hu.1, hs_le_one, mul_nonneg hu.1 (sub_nonneg.mpr hs_le_one)]
    have hcoef : ‖(1 - u) + u * s‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hu.1, hu.2, mul_nonneg hu.1 hs_pos.le], hcoef_le⟩
    calc ‖germAff s u (z : E8)‖ = ‖((1 - u) + u * s) • (z : E8)‖ := rfl
      _ = ‖(1 - u) + u * s‖ * ‖(z : E8)‖ := norm_smul _ _
      _ ≤ 1 * r' := mul_le_mul hcoef hz (norm_nonneg _) zero_le_one
      _ = r' := one_mul r'
  have hSne : ∀ (u : ℝ), u ∈ Set.Icc (0:ℝ) 1 → ∀ z : X, (z : E8) ≠ 0 →
      germAff s u (z : E8) ≠ 0 := by
    intro u hu z hz h
    have hc : 0 < (1 - u) + u * s := by
      by_cases h' : u ≤ 1/2
      · nlinarith [hu.1, hs_pos.le, mul_nonneg hu.1 hs_pos.le]
      · have h2' : 1/2 < u := not_le.mp h'
        nlinarith [hu.2, hs_pos, hs_le_one,
          mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hs_le_one)]
    have h2 : ((1 - u) + u * s) • (z : E8) = 0 := h
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (ne_of_gt hc)
    · exact hz h3
  let hA : F.Homotopy (F.comp Φ) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × X => g (germAff s (p.1 : ℝ) (p.2 : E8)),
        hgc.comp_continuous
          (continuous_germAff s (continuous_subtype_val.comp continuous_fst)
            (continuous_subtype_val.comp continuous_snd))
          (fun p => by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact le_trans (hSnorm _ p.1.2 _) hr'r)⟩
      (fun z => by
        show g (((1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * s) •
          (z : E8)) = F z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
      (fun z => by
        show g (((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * s) •
          (z : E8)) = (F.comp Φ) z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
  have hAmem : ∀ (t : unitInterval) (z : X), z ∈ A → hA (t, z) ∈ B := by
    intro t z hz
    show g (germAff s (t : ℝ) (z : E8)) ≠ 0
    refine hnz (germAff s (t : ℝ) (z : E8)) (Metric.mem_closedBall.mpr ?_) (hSne _ t.2 z hz)
    rw [dist_zero_right]
    exact le_trans (hSnorm _ t.2 _) hr'r
  let hB : (F.comp Φ).Homotopy (G.comp Φ) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × X =>
          (1 - (p.1 : ℝ)) • F (Φ p.2) + (p.1 : ℝ) • G (Φ p.2), by
        have hfst : Continuous fun p : unitInterval × X => ((p.1 : unitInterval) : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have hFc : Continuous fun p : unitInterval × X => F (Φ p.2) :=
          F.continuous.comp (Φ.continuous.comp continuous_snd)
        have hGc : Continuous fun p : unitInterval × X => G (Φ p.2) :=
          G.continuous.comp (Φ.continuous.comp continuous_snd)
        exact (((continuous_const : Continuous fun _ : unitInterval × X => (1:ℝ)).sub hfst).smul
          hFc).add (hfst.smul hGc)⟩
      (fun z => by
        show (1 - ((0 : unitInterval) : ℝ)) • F (Φ z) + ((0 : unitInterval) : ℝ) • G (Φ z)
          = (F.comp Φ) z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
      (fun z => by
        show (1 - ((1 : unitInterval) : ℝ)) • F (Φ z) + ((1 : unitInterval) : ℝ) • G (Φ z)
          = (G.comp Φ) z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
  have hBmem : ∀ (t : unitInterval) (z : X), z ∈ A → hB (t, z) ∈ B := by
    intro t z hz
    show (1 - (t : ℝ)) • F (Φ z) + (t : ℝ) • G (Φ z) ≠ 0
    have hFv : F (Φ z) = g (s • (z : E8)) := rfl
    have hGv : G (Φ z) = L (s • (z : E8)) := rfl
    rw [hFv, hGv]
    have hz0 : (z : E8) ≠ 0 := hz
    have hw0 : s • (z : E8) ≠ 0 := fun h =>
      hz0 ((smul_eq_zero.mp h).resolve_left (ne_of_gt hs_pos))
    have hwle : ‖s • (z : E8)‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      calc s * ‖(z : E8)‖ ≤ s * r' := mul_le_mul_of_nonneg_left (norm_coe_le z) hs_pos.le
        _ ≤ δ := hsr
    have hest := hδest (s • (z : E8)) hwle
    have hLw : L (s • (z : E8)) ≠ 0 := fun h => hw0 (hL.1 (by simpa using h))
    intro hzero
    have hdec : L (s • (z : E8)) + (1 - (t : ℝ)) •
        (g (s • (z : E8)) - L (s • (z : E8))) = 0 := by
      have hsame : L (s • (z : E8)) + (1 - (t : ℝ)) •
            (g (s • (z : E8)) - L (s • (z : E8)))
          = (1 - (t : ℝ)) • g (s • (z : E8)) + (t : ℝ) • L (s • (z : E8)) := by
        module
      rw [hsame]
      exact hzero
    have h1 : ‖L (s • (z : E8))‖ =
        ‖(1 - (t : ℝ)) • (g (s • (z : E8)) - L (s • (z : E8)))‖ := by
      have hneg : L (s • (z : E8)) = -((1 - (t : ℝ)) •
          (g (s • (z : E8)) - L (s • (z : E8)))) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hdec
      calc ‖L (s • (z : E8))‖
          = ‖-((1 - (t : ℝ)) • (g (s • (z : E8)) - L (s • (z : E8))))‖ :=
            congrArg (fun x => ‖x‖) hneg
        _ = ‖(1 - (t : ℝ)) • (g (s • (z : E8)) - L (s • (z : E8)))‖ := norm_neg _
    have h2 : ‖(1 - (t : ℝ)) • (g (s • (z : E8)) - L (s • (z : E8)))‖ ≤
        (1/2) * ‖L (s • (z : E8))‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have ht1 : |1 - (t : ℝ)| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
      calc |1 - (t : ℝ)| * ‖g (s • (z : E8)) - L (s • (z : E8))‖
            ≤ 1 * ‖g (s • (z : E8)) - L (s • (z : E8))‖ :=
              mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖g (s • (z : E8)) - L (s • (z : E8))‖ := one_mul _
        _ ≤ (1/2) * ‖L (s • (z : E8))‖ := hest
    have hpos : 0 < ‖L (s • (z : E8))‖ := norm_pos_iff.mpr hLw
    linarith
  let hC : (G.comp Φ).Homotopy G :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × X => L (germAff s (1 - (p.1 : ℝ)) (p.2 : E8)),
        L.continuous.comp (continuous_germAff s
          ((continuous_const : Continuous fun _ : unitInterval × X => (1:ℝ)).sub
            (continuous_subtype_val.comp continuous_fst))
          (continuous_subtype_val.comp continuous_snd))⟩
      (fun z => by
        show L (((1 - (1 - ((0 : unitInterval) : ℝ))) + (1 - ((0 : unitInterval) : ℝ)) * s) •
          (z : E8)) = (G.comp Φ) z
        have h0 : 1 - ((0 : unitInterval) : ℝ) = 1 := by
          rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
        rw [h0]
        simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
      (fun z => by
        show L (((1 - (1 - ((1 : unitInterval) : ℝ))) + (1 - ((1 : unitInterval) : ℝ)) * s) •
          (z : E8)) = G z
        have h1 : 1 - ((1 : unitInterval) : ℝ) = 0 := by
          rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self]
        rw [h1]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
  have hCmem : ∀ (t : unitInterval) (z : X), z ∈ A → hC (t, z) ∈ B := by
    intro t z hz
    have hu : (1 - (t : ℝ)) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    have hne : germAff s (1 - (t : ℝ)) (z : E8) ≠ 0 := hSne _ hu z hz
    show L (germAff s (1 - (t : ℝ)) (z : E8)) ≠ 0
    intro h
    exact hne (hL.1 (by simpa using h))
  have hchain : Work.Thom.relCohMap F A B hF ℤ 8 = Work.Thom.relCohMap G A B hG ℤ 8 := by
    have h1 := Work.Thom.relCohMap_homotopic A B hF hFΦ hA hAmem ℤ 8
    have h2 := Work.Thom.relCohMap_homotopic A B hFΦ hGΦ hB hBmem ℤ 8
    have h3 := Work.Thom.relCohMap_homotopic A B hGΦ hG hC hCmem ℤ 8
    exact h1.trans (h2.trans h3)
  exact congrArg (fun φ => φ.hom ξ) hchain

end Work.ThomBordism.FrameSigns
