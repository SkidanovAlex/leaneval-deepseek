import Mathlib
import Submission.Work.ThomBordism.FrameSigns.germFDeriv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The pullback `H^n(ℝ^n, ℝ^n∖0) → H^n(D, D∖0)` depends only on the derivative at the origin

Dimension-`n` version of `Work.ThomBordism.FrameSigns.germFDeriv` (which is the case `n = 8`).

Let `g : ℝ^n → ℝ^n` be continuous near `0`, with `g 0 = 0`, `g ≠ 0` off `0` and differentiable at `0`
with derivative `L` (a linear isomorphism).  Then the two maps of pairs `(D, D∖0) → (ℝ^n, ℝ^n∖0)`
given by `g` and by `L` agree on relative cohomology.

The proof is homotopy invariance.  On the ball of radius `r'` the two maps are homotopic through
maps of pairs: with `s ∈ (0,1]` so small that the straight segment between `g w` and `L w` avoids the
origin for `‖w‖ ≤ s r'` (this is the differentiability of `g` at `0` together with the injectivity
of `L`), the homotopy runs

`g(z) → g(s z) → (straight line) → L(s z) → L(z)`

where the first and last steps interpolate `z` and `s z` radially.
-/

namespace Work.ThomBordism.KeyLocal

open scoped unitInterval Topology

/-- The model space `ℝⁿ`. -/
abbrev EucN (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The closed ball of radius `r'` in `ℝⁿ`: the common domain of the maps compared. -/
abbrev EucBall (n : ℕ) (r' : ℝ) : Type := ↥(Metric.closedBall (0 : EucN n) r')

/-- The affine interpolation between the identity and the scaling by `s`: `z ↦ ((1-u) + u s) • z`. -/
abbrev germAffEuc {n : ℕ} (s u : ℝ) (z : EucN n) : EucN n := ((1 - u) + u * s) • z

/-- The norm of an element of the closed ball of radius `r'` is at most `r'`. -/
theorem norm_coe_le_euc {n : ℕ} {r' : ℝ} (z : EucBall n r') : ‖(z : EucN n)‖ ≤ r' := by
  have h := Metric.mem_closedBall.mp z.2
  rwa [dist_eq_norm, sub_zero] at h

theorem continuous_germAffEuc {n : ℕ} (s : ℝ) {Y : Type*} [TopologicalSpace Y] {u : Y → ℝ}
    {z : Y → EucN n} (hu : Continuous u) (hz : Continuous z) :
    Continuous fun y => germAffEuc s (u y) (z y) := by
  unfold germAffEuc
  exact (((continuous_const : Continuous fun _ : Y => (1:ℝ)).sub hu).add
    (hu.mul (continuous_const : Continuous fun _ : Y => s))).smul hz

theorem germFDerivEuc {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hgc : ContinuousOn g (Metric.closedBall 0 r))
    (hL : Function.Bijective L) (hg0 : g 0 = 0) (hgd : HasFDerivAt g L 0)
    (hnz : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, z ≠ 0 → g z ≠ 0)
    (r' : ℝ) (hr' : 0 < r') (hr'r : r' ≤ r)
    (ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({0}ᶜ)) :
    (Work.Thom.relCohMap
      (⟨fun z : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r') =>
          g (z : EuclideanSpace ℝ (Fin n)),
        continuousOn_iff_continuous_domRestrict.mp
          (hgc.mono (Metric.closedBall_subset_closedBall hr'r))⟩ :
        C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r'), EuclideanSpace ℝ (Fin n)))
      {z | (z : EuclideanSpace ℝ (Fin n)) ≠ 0} ({0}ᶜ)
      (fun z hz => hnz (z : EuclideanSpace ℝ (Fin n))
        (Metric.closedBall_subset_closedBall hr'r z.2) hz) ℤ n).hom ξ
    = (Work.Thom.relCohMap
      (⟨fun z : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r') =>
          L (z : EuclideanSpace ℝ (Fin n)),
        L.continuous.comp continuous_subtype_val⟩ :
        C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r'), EuclideanSpace ℝ (Fin n)))
      {z | (z : EuclideanSpace ℝ (Fin n)) ≠ 0} ({0}ᶜ)
      (fun z hz => by intro h; exact hz (hL.1 (by simpa using h))) ℤ n).hom ξ := by
  obtain ⟨δ, hδpos, hδest⟩ := Work.ThomBordism.FrameSigns.exists_norm_sub_le_half (E := EucN n) hL hg0 hgd
  set s : ℝ := min 1 (δ / r') with hs
  have hs_pos : 0 < s := lt_min one_pos (div_pos hδpos hr')
  have hs_le_one : s ≤ 1 := min_le_left _ _
  have hsr : s * r' ≤ δ := by
    have h2 : s ≤ δ / r' := min_le_right _ _
    calc s * r' ≤ (δ / r') * r' := mul_le_mul_of_nonneg_right h2 hr'.le
      _ = δ := by rw [div_mul_cancel₀ _ (ne_of_gt hr')]
  let X : Type := EucBall n r'
  let A : Set X := {z | (z : EucN n) ≠ 0}
  let B : Set (EucN n) := ({0}ᶜ : Set (EucN n))
  let F : C(X, EucN n) := ⟨fun z => g z,
    continuousOn_iff_continuous_domRestrict.mp
      (hgc.mono (Metric.closedBall_subset_closedBall hr'r))⟩
  let G : C(X, EucN n) := ⟨fun z => L z, L.continuous.comp continuous_subtype_val⟩
  have hΦmem : ∀ z : X, s • (z : EucN n) ∈ Metric.closedBall (0 : EucN n) r' := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖s • (z : EucN n)‖ = s * ‖(z : EucN n)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      _ ≤ s * r' := mul_le_mul_of_nonneg_left (norm_coe_le_euc z) hs_pos.le
      _ ≤ r' := by
          calc s * r' ≤ 1 * r' := mul_le_mul_of_nonneg_right hs_le_one hr'.le
            _ = r' := one_mul r'
  let Φ : C(X, X) := ⟨fun z => ⟨s • (z : EucN n), hΦmem z⟩,
      Continuous.subtype_mk
        ((continuous_const : Continuous fun _ : X => (s:ℝ)).smul continuous_subtype_val) hΦmem⟩
  have hΦne : ∀ z : X, (z : EucN n) ≠ 0 → (Φ z : EucN n) ≠ 0 := by
    intro z hz h
    exact hz ((smul_eq_zero.mp h).resolve_left (ne_of_gt hs_pos))
  have hF : ∀ z ∈ A, F z ∈ B := fun z hz =>
    hnz (z : EucN n) (Metric.closedBall_subset_closedBall hr'r z.2) hz
  have hG : ∀ z ∈ A, G z ∈ B := fun z hz => by
    show L (z : EucN n) ≠ 0
    intro h
    exact hz (hL.1 (by simpa using h))
  have hFΦ : ∀ z ∈ A, (F.comp Φ) z ∈ B := fun z hz => hF (Φ z) (hΦne z hz)
  have hGΦ : ∀ z ∈ A, (G.comp Φ) z ∈ B := fun z hz => hG (Φ z) (hΦne z hz)
  change (Work.Thom.relCohMap F A B hF ℤ n).hom ξ
    = (Work.Thom.relCohMap G A B hG ℤ n).hom ξ
  have hSnorm : ∀ (u : ℝ), u ∈ Set.Icc (0:ℝ) 1 → ∀ z : X, ‖germAffEuc s u (z : EucN n)‖ ≤ r' := by
    intro u hu z
    have hz : ‖(z : EucN n)‖ ≤ r' := norm_coe_le_euc z
    have hcoef_le : (1 - u) + u * s ≤ 1 := by
      nlinarith [hu.1, hs_le_one, mul_nonneg hu.1 (sub_nonneg.mpr hs_le_one)]
    have hcoef : ‖(1 - u) + u * s‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hu.1, hu.2, mul_nonneg hu.1 hs_pos.le], hcoef_le⟩
    calc ‖germAffEuc s u (z : EucN n)‖ = ‖((1 - u) + u * s) • (z : EucN n)‖ := rfl
      _ = ‖(1 - u) + u * s‖ * ‖(z : EucN n)‖ := norm_smul _ _
      _ ≤ 1 * r' := mul_le_mul hcoef hz (norm_nonneg _) zero_le_one
      _ = r' := one_mul r'
  have hSne : ∀ (u : ℝ), u ∈ Set.Icc (0:ℝ) 1 → ∀ z : X, (z : EucN n) ≠ 0 →
      germAffEuc s u (z : EucN n) ≠ 0 := by
    intro u hu z hz h
    have hc : 0 < (1 - u) + u * s := by
      by_cases h' : u ≤ 1/2
      · nlinarith [hu.1, hs_pos.le, mul_nonneg hu.1 hs_pos.le]
      · have h2' : 1/2 < u := not_le.mp h'
        nlinarith [hu.2, hs_pos, hs_le_one,
          mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hs_le_one)]
    have h2 : ((1 - u) + u * s) • (z : EucN n) = 0 := h
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (ne_of_gt hc)
    · exact hz h3
  let hA : F.Homotopy (F.comp Φ) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × X => g (germAffEuc s (p.1 : ℝ) (p.2 : EucN n)),
        hgc.comp_continuous
          (continuous_germAffEuc s (continuous_subtype_val.comp continuous_fst)
            (continuous_subtype_val.comp continuous_snd))
          (fun p => by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact le_trans (hSnorm _ p.1.2 _) hr'r)⟩
      (fun z => by
        show g (((1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * s) •
          (z : EucN n)) = F z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
      (fun z => by
        show g (((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * s) •
          (z : EucN n)) = (F.comp Φ) z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
  have hAmem : ∀ (t : unitInterval) (z : X), z ∈ A → hA (t, z) ∈ B := by
    intro t z hz
    show g (germAffEuc s (t : ℝ) (z : EucN n)) ≠ 0
    refine hnz (germAffEuc s (t : ℝ) (z : EucN n)) (Metric.mem_closedBall.mpr ?_) (hSne _ t.2 z hz)
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
    have hFv : F (Φ z) = g (s • (z : EucN n)) := rfl
    have hGv : G (Φ z) = L (s • (z : EucN n)) := rfl
    rw [hFv, hGv]
    have hz0 : (z : EucN n) ≠ 0 := hz
    have hw0 : s • (z : EucN n) ≠ 0 := fun h =>
      hz0 ((smul_eq_zero.mp h).resolve_left (ne_of_gt hs_pos))
    have hwle : ‖s • (z : EucN n)‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      calc s * ‖(z : EucN n)‖ ≤ s * r' := mul_le_mul_of_nonneg_left (norm_coe_le_euc z) hs_pos.le
        _ ≤ δ := hsr
    have hest := hδest (s • (z : EucN n)) hwle
    have hLw : L (s • (z : EucN n)) ≠ 0 := fun h => hw0 (hL.1 (by simpa using h))
    intro hzero
    have hdec : L (s • (z : EucN n)) + (1 - (t : ℝ)) •
        (g (s • (z : EucN n)) - L (s • (z : EucN n))) = 0 := by
      have hsame : L (s • (z : EucN n)) + (1 - (t : ℝ)) •
            (g (s • (z : EucN n)) - L (s • (z : EucN n)))
          = (1 - (t : ℝ)) • g (s • (z : EucN n)) + (t : ℝ) • L (s • (z : EucN n)) := by
        module
      rw [hsame]
      exact hzero
    have h1 : ‖L (s • (z : EucN n))‖ =
        ‖(1 - (t : ℝ)) • (g (s • (z : EucN n)) - L (s • (z : EucN n)))‖ := by
      have hneg : L (s • (z : EucN n)) = -((1 - (t : ℝ)) •
          (g (s • (z : EucN n)) - L (s • (z : EucN n)))) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hdec
      calc ‖L (s • (z : EucN n))‖
          = ‖-((1 - (t : ℝ)) • (g (s • (z : EucN n)) - L (s • (z : EucN n))))‖ :=
            congrArg (fun x => ‖x‖) hneg
        _ = ‖(1 - (t : ℝ)) • (g (s • (z : EucN n)) - L (s • (z : EucN n)))‖ := norm_neg _
    have h2 : ‖(1 - (t : ℝ)) • (g (s • (z : EucN n)) - L (s • (z : EucN n)))‖ ≤
        (1/2) * ‖L (s • (z : EucN n))‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have ht1 : |1 - (t : ℝ)| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
      calc |1 - (t : ℝ)| * ‖g (s • (z : EucN n)) - L (s • (z : EucN n))‖
            ≤ 1 * ‖g (s • (z : EucN n)) - L (s • (z : EucN n))‖ :=
              mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖g (s • (z : EucN n)) - L (s • (z : EucN n))‖ := one_mul _
        _ ≤ (1/2) * ‖L (s • (z : EucN n))‖ := hest
    have hpos : 0 < ‖L (s • (z : EucN n))‖ := norm_pos_iff.mpr hLw
    linarith
  let hC : (G.comp Φ).Homotopy G :=
    ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × X => L (germAffEuc s (1 - (p.1 : ℝ)) (p.2 : EucN n)),
        L.continuous.comp (continuous_germAffEuc s
          ((continuous_const : Continuous fun _ : unitInterval × X => (1:ℝ)).sub
            (continuous_subtype_val.comp continuous_fst))
          (continuous_subtype_val.comp continuous_snd))⟩
      (fun z => by
        show L (((1 - (1 - ((0 : unitInterval) : ℝ))) + (1 - ((0 : unitInterval) : ℝ)) * s) •
          (z : EucN n)) = (G.comp Φ) z
        have h0 : 1 - ((0 : unitInterval) : ℝ) = 1 := by
          rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
        rw [h0]
        simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
      (fun z => by
        show L (((1 - (1 - ((1 : unitInterval) : ℝ))) + (1 - ((1 : unitInterval) : ℝ)) * s) •
          (z : EucN n)) = G z
        have h1 : 1 - ((1 : unitInterval) : ℝ) = 0 := by
          rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self]
        rw [h1]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul]
        rfl)
  have hCmem : ∀ (t : unitInterval) (z : X), z ∈ A → hC (t, z) ∈ B := by
    intro t z hz
    have hu : (1 - (t : ℝ)) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    have hne : germAffEuc s (1 - (t : ℝ)) (z : EucN n) ≠ 0 := hSne _ hu z hz
    show L (germAffEuc s (1 - (t : ℝ)) (z : EucN n)) ≠ 0
    intro h
    exact hne (hL.1 (by simpa using h))
  have hchain : Work.Thom.relCohMap F A B hF ℤ n = Work.Thom.relCohMap G A B hG ℤ n := by
    have h1 := Work.Thom.relCohMap_homotopic A B hF hFΦ hA hAmem ℤ n
    have h2 := Work.Thom.relCohMap_homotopic A B hFΦ hGΦ hB hBmem ℤ n
    have h3 := Work.Thom.relCohMap_homotopic A B hGΦ hG hC hCmem ℤ n
    exact h1.trans (h2.trans h3)
  exact congrArg (fun φ => φ.hom ξ) hchain

end Work.ThomBordism.KeyLocal

