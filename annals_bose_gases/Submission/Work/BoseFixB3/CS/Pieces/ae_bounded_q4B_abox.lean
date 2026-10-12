import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.PotChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.ae_bounded_q4B_abox`

The three `a.e.`-measurability/boundedness side conditions of the `CS`-step word
`q4B ℓ (omC w₀) Φ p` on the centred box `abox n ℓ`, with `w₀ := Classical.choose h`
the chosen radial scattering solution and `omC w₀ (xᵢ,xⱼ) = w₀(xᵢ − xⱼ)`:

* `0 ≤ w₀(x p.1 − x p.2) ∧ w₀(x p.1 − x p.2) ≤ 1` a.e. on the box;
* `q4B` (as a function of `x`) is a.e. strongly measurable on the box;
* `q4B` is bounded a.e. on the box (by `9·M`, `M` a sup-norm bound for `Φ` on the box).

The three pieces are independent:

1. the a.e. bounds `0 ≤ w₀ ≤ 1` on `ℝ³` are FS's `eq:omegabounds`
   (`Submission.BoseGases.scattering_bounds_ae`, from `hv : 0 ≤ v` and the support
   hypothesis), pulled back along the difference map `x ↦ x p.1 − x p.2` by
   `Submission.BoseGases.ae_pair_pullback` (the pair has `p.1 ≠ p.2` because
   `p ∈ pairSet n`);
2. `q4B = QⱼQᵢΦ + w₀(xᵢ−xⱼ)·(PⱼPᵢΦ + PⱼQᵢΦ + QⱼPᵢΦ)` with `Pᵢ = aP ℓ i`,
   `Qᵢ = aQ ℓ i`; every projection factor is *continuous* in `x` for continuous
   `Φ` (`aP_continuous`, `aQ_continuous`) and `x ↦ w₀(x p.1 − x p.2)` is a.e.
   strongly measurable by `Submission.BoseGases.w0_diff_aem` (local integrability
   of the scattering solution); a.e. strong measurability is closed under
   addition and multiplication;
3. on the box the condensate mean `aP ℓ i` does not increase the sup-norm
   (`Submission.BoseGases.aP_abs_le`), so with `M ≥ |Φ|` on `abox n ℓ`
   (compactness of the box, `Φ` continuous) one gets
   `|QⱼQᵢΦ| ≤ 4M`, `|PⱼPᵢΦ| ≤ M`, `|PⱼQᵢΦ| ≤ 2M`, `|QⱼPᵢΦ| ≤ 2M`, hence
   `|q4B| ≤ 4M + 1·(M + 2M + 2M) = 9M` wherever `|w₀(xᵢ−xⱼ)| ≤ 1`.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.BoseFixB3.CS.Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem ae_bounded_q4B_abox {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {p : Fin n × Fin n} (hp : p ∈ Submission.BoseGases.pairSet n) :
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        0 ≤ Classical.choose h (x p.1 - x p.2) ∧ Classical.choose h (x p.1 - x p.2) ≤ 1) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      |Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x| ≤ B := by
  -- the pair consists of distinct particles
  have hne : p.1 ≠ p.2 := by
    have h2 := hp
    simp [Submission.BoseGases.pairSet] at h2
    exact h2
  -- the chosen solution is radial and solves the scattering equation
  have hspec := Submission.BoseGases.w0_spec h
  -- FS `eq:omegabounds`: `0 ≤ w₀ ≤ 1` a.e. on `ℝ³`
  have hbnds := Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h)
    hR hv hvrad hv_supp hspec.1 hspec.2
  refine ⟨?_, ?_, ?_⟩
  · -- (1) pull the a.e. bounds back along `x ↦ x p.1 − x p.2`
    have hconj : ∀ᵐ z : ℝ³, 0 ≤ Classical.choose h z ∧ Classical.choose h z ≤ 1 := by
      filter_upwards [hbnds.1, hbnds.2] with z h1 h2
      exact ⟨h1, h2⟩
    exact Submission.BoseGases.ae_pair_pullback (N := n) (ℓ := ℓ) hℓ hne hconj
  · -- (2) a.e. strong measurability: `q4B = QⱼQᵢΦ + w₀(xᵢ−xⱼ)·(PⱼPᵢΦ + PⱼQᵢΦ + QⱼPᵢΦ)`
    have hQQc : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) :=
      Submission.BoseGases.aQ_continuous hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)
    have hSSc : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) := by
      have h1 : Continuous (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
            + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) :=
        (Submission.BoseGases.aP_continuous hℓ p.2 (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).add
          (Submission.BoseGases.aP_continuous hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
      exact h1.add
        (Submission.BoseGases.aQ_continuous hℓ p.2 (Submission.BoseGases.aP_continuous hℓ p.1 hΦc))
    have homx : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => Classical.choose h (x p.1 - x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      Submission.BoseGases.w0_diff_aem hℓ hne hspec.2.lhs_integrable
    have hEq : (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        = fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Classical.choose h (x p.1 - x p.2) *
              (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
                + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) := by
      funext x
      rfl
    rw [hEq]
    exact hQQc.aestronglyMeasurable.add (homx.mul hSSc.aestronglyMeasurable)
  · -- (3) the a.e. bound `|q4B| ≤ 9M`, `M` a sup-norm bound of `Φ` on the box
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      hΦc.continuousOn
    have hC' : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ max C 0 := by
      intro x hx
      have h1 := hC x hx
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    set M : ℝ := max C 0 with hM
    have hM0 : 0 ≤ M := by rw [hM]; exact le_max_right _ _
    have hΦM : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ M := by
      intro x hx; rw [hM]; exact hC' x hx
    -- the condensate mean does not increase the sup-norm
    have hPi : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Submission.BoseGases.aP ℓ p.1 Φ x| ≤ M :=
      Submission.BoseGases.aP_abs_le hℓ p.1 hΦc hM0 hΦM
    have hQi : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Submission.BoseGases.aQ ℓ p.1 Φ x| ≤ 2 * M := by
      intro x hx
      have h1 := hΦM x hx
      have h2 := hPi x hx
      have h3 : |Φ x - Submission.BoseGases.aP ℓ p.1 Φ x|
          ≤ |Φ x| + |Submission.BoseGases.aP ℓ p.1 Φ x| := abs_sub _ _
      have h4 : Submission.BoseGases.aQ ℓ p.1 Φ x
          = Φ x - Submission.BoseGases.aP ℓ p.1 Φ x := rfl
      rw [h4]
      linarith
    have hPP : ∀ x ∈ Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ M :=
      Submission.BoseGases.aP_abs_le hℓ p.2 (Submission.BoseGases.aP_continuous hℓ p.1 hΦc) hM0 hPi
    have hPQ : ∀ x ∈ Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x| ≤ 2 * M :=
      Submission.BoseGases.aP_abs_le hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)
        (by linarith) hQi
    have hQP : ∀ x ∈ Submission.BoseGases.abox n ℓ,
        |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ 2 * M := by
      intro x hx
      have h1 := hPi x hx
      have h2 := hPP x hx
      have h3 : |Submission.BoseGases.aP ℓ p.1 Φ x
            - Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
          ≤ |Submission.BoseGases.aP ℓ p.1 Φ x|
            + |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| := abs_sub _ _
      have h4 : Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          = Submission.BoseGases.aP ℓ p.1 Φ x
            - Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x := rfl
      rw [h4]
      linarith
    -- `|w₀(x p.1 − x p.2)| ≤ 1` a.e. on the box
    have hom1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Classical.choose h (x p.1 - x p.2)| ≤ 1 := by
      have hle : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
        filter_upwards [hbnds.1, hbnds.2] with z h1 h2
        rw [abs_of_nonneg h1]; exact h2
      exact Submission.BoseGases.ae_pair_pullback (N := n) (ℓ := ℓ) hℓ hne hle
    refine ⟨9 * M, by linarith, ?_⟩
    filter_upwards [hom1, MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)]
      with x hom hx
    have hQQx : |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x| ≤ 4 * M := by
      have h1 := hQi x hx
      have h2 := hPQ x hx
      have h3 : |Submission.BoseGases.aQ ℓ p.1 Φ x
            - Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x|
          ≤ |Submission.BoseGases.aQ ℓ p.1 Φ x|
            + |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x| := abs_sub _ _
      have h4 : Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          = Submission.BoseGases.aQ ℓ p.1 Φ x
            - Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x := rfl
      rw [h4]
      linarith
    have hSSx : |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ 5 * M := by
      have h1 := hPP x hx
      have h2 := hPQ x hx
      have h3 := hQP x hx
      have h12 : |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x| ≤ 3 * M := by
        have h4 := abs_add_le (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)
          (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x)
        linarith
      calc |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
            + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
          ≤ |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
              + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x|
            + |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| :=
            abs_add_le _ _
        _ ≤ 5 * M := by linarith
    have hq4 : Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
        = Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Classical.choose h (x p.1 - x p.2) *
            (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
              + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) := rfl
    rw [hq4]
    calc |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Classical.choose h (x p.1 - x p.2) *
            (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
              + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)|
        ≤ |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x|
          + |Classical.choose h (x p.1 - x p.2) *
            (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
              + Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)| :=
          abs_add_le _ _
      _ ≤ 9 * M := by
          rw [abs_mul]
          have hm := mul_le_mul hom hSSx (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
          linarith

end Work.BoseFixB3.CS.Pieces
