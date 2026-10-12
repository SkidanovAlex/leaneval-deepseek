import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Endgame
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The uniform dilute box bound implies the box hypothesis `hbox` (interface)

`theorem_1_2` is reduced to two machine-verified hypotheses
(`theorem_1_2_of_liminf_continuous_and_box`, `Submission.Endgame`):
`hcont` (continuity of the liminf density — proved, `MargLipschitz`) and

    hbox : ∀ᶠ ρ in 𝓝[>] 0, ∀ᶠ p in jointFilter ρ,
             lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1/2 + η) ((p.2:ℝ)/p.1^3) ≤ boxDensity v p.

This module records the *final assembly step* that the eventual Fournais--Solovej
box analysis (Layer 5) will feed: it is enough to prove the **uniform dilute
box lower bound** (their Theorem LHY-Box / eq. (eq:EnergyBoxRes1))

    UBB : ∃ ε₀ > 0, ∃ C ≥ 0, ∀ L ≥ 1, ∀ N : ℕ,
            ((N:ℝ)/L³)·A³ ≤ ε₀  ⟹  lhyRhs A C (1/2 + η₀) (N/L³) ≤ boxEnergy N L v / L³

for the fixed potential `v`, `A := a v > 0`, for *some explicit* error exponent
`η₀ > 0`.  (All the regime conditions of the FS paper -- `R/a ≪ (ρa³)^{-1/4}`
etc. -- are absorbed by the two "eventual" quantifiers of `hbox` and are not
part of this interface.)

## The absorption

Because `0 < η < η₀`, for small `t := ρa³` the FS error
`C·t^{1/2+η₀} = C·t^{η₀−η}·t^{1/2+η}` is dominated by `K·t^{1/2+η}` for any
`K ≥ C·ε₀^{η₀−η}`.  This module therefore takes the subtraction coefficient
`K` (later `𝓒 (𝓡 v) (R / a v)`) and the exponent `η` (later `Submission.η`)
as parameters, with the domination hypothesis stated uniformly:

    ∀ t, 0 ≤ t → t ≤ ε₀ → C * t ^ (η₀ - η) ≤ K

(`hKbig`).  Then `UBB` gives the pointwise inequality
`lhyRhs A K (1/2+η) (N/L³) ≤ boxDensity v (L,N)` for every box with
`(N/L³)·A³ ≤ ε₀`, and the two eventual quantifiers of `hbox` (density along
the joint filter tends to `ρ`, and `ρ` is taken small) do the rest.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The density argument of the box-density filter is positive and eventually
away from zero: along the joint filter at `ρ > 0` the density `N / L³` stays
larger than `ρ / 2` eventually. -/
lemma eventually_density_gt_half {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ p in jointFilter ρ, ρ / 2 < (p.2 : ℝ) / p.1 ^ 3 := by
  have htd : Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3) (jointFilter ρ) (𝓝 ρ) :=
    density_tendsto ρ
  have hb : ∀ᶠ p in jointFilter ρ, |(p.2 : ℝ) / p.1 ^ 3 - ρ| < ρ / 2 :=
    (Metric.tendsto_nhds.mp htd) (ρ / 2) (half_pos hρ)
  filter_upwards [hb] with p hp
  have hlt := (abs_lt.mp hp).1
  linarith

/-- Along the joint filter at `ρ` with `0 < ρ` and `ρ·A³ < ε₀`, the scaled
density `(N/L³)·A³` is eventually below `ε₀`. -/
lemma eventually_scaled_density_le {ρ A ε₀ : ℝ} (hρ : 0 < ρ) (hρA : ρ * A ^ 3 < ε₀) :
    ∀ᶠ p in jointFilter ρ, ((p.2 : ℝ) / p.1 ^ 3) * A ^ 3 ≤ ε₀ := by
  have htd : Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3) (jointFilter ρ) (𝓝 ρ) :=
    density_tendsto ρ
  have htdA : Tendsto (fun p : ℝ × ℕ => ((p.2 : ℝ) / p.1 ^ 3) * A ^ 3)
      (jointFilter ρ) (𝓝 (ρ * A ^ 3)) := by
    exact htd.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ × ℕ => A ^ 3)
      (jointFilter ρ) (𝓝 (A ^ 3)))
  have hε : 0 < ε₀ - ρ * A ^ 3 := sub_pos.mpr hρA
  have hb : ∀ᶠ p in jointFilter ρ,
      dist (((p.2 : ℝ) / p.1 ^ 3) * A ^ 3) (ρ * A ^ 3) < ε₀ - ρ * A ^ 3 :=
    (Metric.tendsto_nhds.mp htdA) (ε₀ - ρ * A ^ 3) hε
  filter_upwards [hb] with p hp
  have hlt := (abs_lt.mp (by simpa [Real.dist_eq] using hp)).2
  linarith

/-- The canonical box density is exactly `boxEnergy N L v / L³` when the box
is nondegenerate. -/
lemma boxDensity_eq {v : ℝ³ → ℝ} (p : ℝ × ℕ) :
    boxDensity v p = boxEnergy p.2 p.1 v / p.1 ^ 3 := by
  dsimp [boxDensity]
  rw [div_eq_mul_inv, mul_comm]
  rfl

/-- Pointwise domination: if `C·(ρA³)^(η₀−η) ≤ K`, the LHY bound with the
`K`-coefficient and the smaller error exponent `1/2 + η` is below the one with
the `C`-coefficient and the larger error exponent `1/2 + η₀` (the `√` and `1`
terms agree, and the difference of the error terms is nonpositive). -/
lemma lhyRhs_le_of_domination {A C K : ℝ} {η₀ η ρ : ℝ} (hA : 0 ≤ A)
    (hu : 0 < ρ * A ^ 3) (hdom : C * (ρ * A ^ 3) ^ (η₀ - η) ≤ K) :
    lhyRhs A K (1 / 2 + η) ρ ≤ lhyRhs A C (1 / 2 + η₀) ρ := by
  have hu0 : 0 ≤ ρ * A ^ 3 := le_of_lt hu
  have hCK : C * (ρ * A ^ 3) ^ (1 / 2 + η₀) ≤ K * (ρ * A ^ 3) ^ (1 / 2 + η) := by
    calc
      C * (ρ * A ^ 3) ^ (1 / 2 + η₀)
          = C * ((ρ * A ^ 3) ^ (1 / 2 + η) * (ρ * A ^ 3) ^ (η₀ - η)) := by
            rw [show 1 / 2 + η₀ = (1 / 2 + η) + (η₀ - η) by ring]
            rw [Real.rpow_add hu]
      _ = (C * (ρ * A ^ 3) ^ (η₀ - η)) * (ρ * A ^ 3) ^ (1 / 2 + η) := by ring
      _ ≤ K * (ρ * A ^ 3) ^ (1 / 2 + η) :=
            mul_le_mul_of_nonneg_right hdom (Real.rpow_nonneg hu0 (1 / 2 + η))
  have hinner : 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ (1 / 2 + η)
      ≤ 1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - C * (ρ * A ^ 3) ^ (1 / 2 + η₀) := by
    linarith
  have hpre : 0 ≤ 4 * π * ρ ^ 2 * A := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg ρ)) hA
  calc
    lhyRhs A K (1 / 2 + η) ρ
        = 4 * π * ρ ^ 2 * A *
            (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ (1 / 2 + η)) := by
          rw [lhyRhs]
    _ ≤ 4 * π * ρ ^ 2 * A *
            (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - C * (ρ * A ^ 3) ^ (1 / 2 + η₀)) := by
          exact mul_le_mul_of_nonneg_left hinner hpre
    _ = lhyRhs A C (1 / 2 + η₀) ρ := by rw [lhyRhs]

/-- From the uniform dilute box bound (UBB) at one small density `ρ`: every box
`(L,N)` (eventually along the joint filter at `ρ`) satisfies the
`K`-coefficient LHY lower bound against the canonical box density. -/
lemma boxDensity_lower_of_UBB {v : ℝ³ → ℝ} {A C K ε₀ : ℝ} {η₀ η : ℝ}
    (hA : 0 < A)
    (hdom : ∀ t : ℝ, 0 ≤ t → t ≤ ε₀ → C * t ^ (η₀ - η) ≤ K)
    (hboxbound : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      ((N : ℝ) / L ^ 3) * A ^ 3 ≤ ε₀ →
      lhyRhs A C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3)
    {ρ : ℝ} (hρ : 0 < ρ) (hρA : ρ * A ^ 3 < ε₀) :
    ∀ᶠ p in jointFilter ρ,
      lhyRhs A K (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p := by
  have hL1 : ∀ᶠ p in jointFilter ρ, 1 ≤ p.1 :=
    (tendsto_fst_atTop ρ).eventually (Filter.eventually_ge_atTop (1 : ℝ))
  have hpos : ∀ᶠ p in jointFilter ρ, 0 < (p.2 : ℝ) / p.1 ^ 3 := by
    filter_upwards [eventually_density_gt_half hρ] with p hp
    exact lt_trans (half_pos hρ) hp
  have hle : ∀ᶠ p in jointFilter ρ, ((p.2 : ℝ) / p.1 ^ 3) * A ^ 3 ≤ ε₀ :=
    eventually_scaled_density_le (ρ := ρ) (A := A) (ε₀ := ε₀) hρ hρA
  filter_upwards [hL1, hpos, hle] with p hL1p hposp hlep
  let t : ℝ := (p.2 : ℝ) / p.1 ^ 3
  have hA3 : 0 < A ^ 3 := pow_pos hA 3
  have hscale : 0 < t * A ^ 3 := mul_pos hposp hA3
  have hdomp : C * (t * A ^ 3) ^ (η₀ - η) ≤ K := hdom (t * A ^ 3) hscale.le hlep
  have hmono : lhyRhs A K (1 / 2 + η) t ≤ lhyRhs A C (1 / 2 + η₀) t :=
    lhyRhs_le_of_domination (hA := hA.le) hscale hdomp
  have hbox : lhyRhs A C (1 / 2 + η₀) t ≤ boxEnergy p.2 p.1 v / p.1 ^ 3 :=
    hboxbound p.1 hL1p p.2 hlep
  simpa [t] using hmono.trans (hbox.trans_eq (boxDensity_eq (v := v) p).symm)

/-- From the uniform dilute box bound (UBB, any explicit `ε₀ > 0`, `C ≥ 0`,
`η₀ > 0`) with the domination `C·t^(η₀−η) ≤ K` on `0 ≤ t ≤ ε₀`, the box
hypothesis `hbox` follows for the subtraction coefficient `K` and error
exponent `1/2 + η` (`0 < η < η₀`).  `A` is the scattering length `a v`
(assumed positive), and `0 ≤ v` with `tsupport v ⊆ ball 0 R`. -/
theorem hbox_of_uniform_box {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {A : ℝ} (hA : 0 < A)
    {η₀ : ℝ} (hη₀ : 0 < η₀)
    {η : ℝ} (hη : 0 < η) (hηlt : η < η₀)
    {K : ℝ}
    (hubb : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ ε₀ → C * t ^ (η₀ - η) ≤ K) ∧
      ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
        ((N : ℝ) / L ^ 3) * A ^ 3 ≤ ε₀ →
        lhyRhs A C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs A K (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p := by
  rcases hubb with ⟨ε₀, hε₀, C, hC₀, hdom, hboxbound⟩
  have hA3 : 0 < A ^ 3 := pow_pos hA 3
  have hδ : 0 < ε₀ / A ^ 3 := div_pos hε₀ hA3
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ), ρ < ε₀ / A ^ 3 := by
    have hio : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), y < ε₀ / A ^ 3 := isOpen_Iio.mem_nhds hδ
    exact hio.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
  have hρA : ρ * A ^ 3 < ε₀ := (lt_div_iff₀ hA3).mp hρlt
  exact boxDensity_lower_of_UBB (v := v) (A := A) (C := C) (K := K) (ε₀ := ε₀)
    (η₀ := η₀) (η := η) (hA := hA) hdom hboxbound hρpos hρA

/-- UBB applied to the chosen scattering length `a v` (this is the form the
Layer-5 box analysis will discharge).  Stated for readability; it specialises
`hbox_of_uniform_box` to `A := a v` with the `𝓒`-coefficient made explicit. -/
theorem hbox_of_uniform_box_av {v : ℝ³ → ℝ} (_hv : 0 ≤ v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    {η₀ : ℝ} (hη₀ : 0 < η₀)
    {η : ℝ} (hη : 0 < η) (hηlt : η < η₀)
    {K : ℝ}
    (hubb : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ ε₀ → C * t ^ (η₀ - η) ≤ K) ∧
      ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
        ((N : ℝ) / L ^ 3) * (a v) ^ 3 ≤ ε₀ →
        lhyRhs (a v) C (1 / 2 + η₀) ((N : ℝ) / L ^ 3) ≤ boxEnergy N L v / L ^ 3) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) K (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p := by
  exact hbox_of_uniform_box (v := v) (R := R) hR hv_supp (A := a v) hav
    (η₀ := η₀) hη₀ (η := η) hη hηlt (K := K) hubb

end Submission.BoseGases
