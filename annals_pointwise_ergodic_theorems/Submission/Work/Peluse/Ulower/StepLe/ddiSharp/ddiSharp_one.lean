import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.hypoMass_eq_sum
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.concMass_eq_sum
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.rowGram_local
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.tsum_avgNormSq_le

/-!
# The base case `SharpMassDDI 1`

This proves the `σ = 1` instance of the sharp (density-free) dual--difference interchange
(`Work.Peluse.Ulower.StepLe.SharpMassDDI`): for `G : Z → ℤ → ℂ` with `‖G z x‖ ≤ 1`, each `G z`
supported (up to its own translation) in `symIcc L`, a set `H` of shift pairs with coordinates in
`[1,D]`, a phase `φ` and `B ≥ L + D`,

  `9⁻¹ * (hypoMass 1 B G H φ)² / D ≤ concMass 1 D B G H φ`.

The proof is the Gram/energy ("Frobenius") argument in the Hilbert space `ℓ²(Z × ℤ)`, run row by
row in the first shift coordinate.  With `f = avgFn G = |Z|⁻¹ ∑_z G z` the row correlations
`rowC G φ a u = ∑'_x e(φ a u x) conj (f (x + a 0)) f (x + u 0)` and the Gram entries
`gramD G φ a u v = ∑'_x e((φ a v - φ a u) x) |Z|⁻¹ ∑_z G z (x + v 0) conj (G z (x + u 0))` satisfy

  `(∑_{u ∈ R_a} ‖rowC a u‖²)² ≤ (∑_{u,v ∈ R_a} ‖gramD a u v‖²) * (∑'_x ‖f (x + a 0)‖²)²`

(`rowGram_local`, the energy lemma with the constant-family test vector absorbing the decorations),
while `∑'_x ‖f (x + a 0)‖² ≤ 2L + 1` (`tsum_avgNormSq_le`, Jensen plus the support hypothesis).
The hypothesis and conclusion masses are the row sums and the cube-set sums of these objects
(`hypoMass_eq_sum`, `concMass_eq_sum`), and `|Θ₁(H)|`-free Cauchy--Schwarz over the `D` rows gives
`(hypoMass)² ≤ 9 D concMass` because `(2L+1)² ≤ 9B²` and `B ≥ L`.
-/

open scoped BigOperators
open Work.Peluse.Ulower.StepLe.ddiSharp.one

namespace Work.Peluse.Ulower.StepLe.ddiSharp

theorem ddiSharp_one : Work.Peluse.Ulower.StepLe.SharpMassDDI 1 := by
  classical
  refine ⟨9, by norm_num, ?_⟩
  intro L D B hL hD hB Z instZ G hG1 hsupp H φ hHmem
  -- the hypothesis on `H`, in the `thetaBox` form used by the decompositions
  have hHbox : ∀ p ∈ H, p.1 ∈ Work.Peluse.Ulower.thetaBox 1 D ∧
      p.2 ∈ Work.Peluse.Ulower.thetaBox 1 D := fun p hp =>
    ⟨Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => (hHmem p hp i).1),
     Work.Peluse.Ulower.mem_thetaBox.mpr (fun i => (hHmem p hp i).2)⟩
  -- the numeric hypotheses
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
  have hBL : (L : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show L ≤ B by omega)
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  -- the mass inequality `hypoMass² ≤ 9 D concMass`
  have hmain : (Work.Peluse.Ulower.StepLe.hypoMass 1 B G H φ) ^ 2 ≤
      9 * (D : ℝ) * Work.Peluse.Ulower.StepLe.concMass 1 D B G H φ := by
    rcases isEmpty_or_nonempty Z with hZi | hZn
    · -- the decoration space is empty: both masses vanish
      have hcard : Fintype.card Z = 0 := Fintype.card_eq_zero_iff.mpr hZi
      have havg : avgFn G = 0 := by
        funext y
        simp [avgFn, hcard]
      have hhm : Work.Peluse.Ulower.StepLe.hypoMass 1 B G H φ = 0 := by
        simp only [Work.Peluse.Ulower.StepLe.hypoMass]
        refine Finset.sum_eq_zero (fun p hp => ?_)
        have h1 : (fun y : ℤ => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) = (0 : ℤ → ℂ) := havg
        rw [h1]
        have h2 : (∑' x : ℤ, Work.Peluse.cubeTerm p.1 p.2 (0 : ℤ → ℂ) x *
            Complex.exp (2 * Real.pi * Complex.I * (φ p.1 p.2 : ℂ) * (x : ℂ))) = 0 := by
          rw [tsum_congr (fun x => by rw [cubeTerm_zero p.1 p.2 x, zero_mul])]
          exact tsum_zero
        rw [h2]
        simp
      have hcm : Work.Peluse.Ulower.StepLe.concMass 1 D B G H φ = 0 := by
        simp only [Work.Peluse.Ulower.StepLe.concMass]
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have h0 : ((Fintype.card Z : ℂ))⁻¹ = 0 := by rw [hcard]; simp
        have h2 : (∑' x : ℤ, ((Fintype.card Z : ℂ))⁻¹ * ∑ z,
            Work.Peluse.cubeTerm k.2.1 k.2.2 (G z) x *
            Complex.exp (2 * Real.pi * Complex.I *
              ((Work.Peluse.Ulower.StepLe.mixedPhase φ k : ℝ) : ℂ) * (x : ℂ))) = 0 := by
          rw [show (∑' x : ℤ, ((Fintype.card Z : ℂ))⁻¹ * ∑ z,
                Work.Peluse.cubeTerm k.2.1 k.2.2 (G z) x *
                Complex.exp (2 * Real.pi * Complex.I *
                  ((Work.Peluse.Ulower.StepLe.mixedPhase φ k : ℝ) : ℂ) * (x : ℂ)))
              = ∑' x : ℤ, (0 : ℂ) from tsum_congr (fun x => by simp [h0])]
          exact tsum_zero
        rw [h2]
        simp
      rw [hhm, hcm]
      norm_num
    · -- the main case
      haveI : Nonempty Z := hZn
      -- a common window for the supports of the `G z`
      let c0 : Z → ℤ := fun z => Classical.choose (hsupp z)
      have hc0 : ∀ z, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c0 z) = 0 :=
        fun z => Classical.choose_spec (hsupp z)
      let T : Finset ℤ := Finset.univ.biUnion
        (fun z => (Work.Peluse.symIcc L).image (fun t => t + c0 z))
      have hT : ∀ z x, x ∉ T → G z x = 0 := by
        intro z x hx
        have hmem : x - c0 z ∉ Work.Peluse.symIcc L := fun h =>
          hx (Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z,
            Finset.mem_image.mpr ⟨x - c0 z, h, by ring⟩⟩)
        have h0 := hc0 z (x - c0 z) hmem
        rwa [show x - c0 z + c0 z = x from by ring] at h0
      -- the two masses as row and cube sums
      rw [hypoMass_eq_sum B D G H φ hHbox, concMass_eq_sum D B G H φ hHbox]
      -- factor the `B⁻¹` normalisation out of every term
      have hLHS : (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
            ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
              ‖((B : ℂ))⁻¹ * rowC G φ a u‖ ^ 2)
          = (((B : ℝ))⁻¹) ^ 2 * ∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun u _ => normSq_inv_natCast_mul B (rowC G φ a u))
      have hRHS : (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
            ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
              ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a,
                ‖((B : ℂ))⁻¹ * gramD G φ a u v‖ ^ 2)
          = (((B : ℝ))⁻¹) ^ 2 * ∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v _ => normSq_inv_natCast_mul B (gramD G φ a u v))
      -- the unnormalised core inequality
      have hcore : (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
            ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2
          ≤ 9 * (D : ℝ) * (B : ℝ) ^ 2 *
            (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2) := by
        -- one row at a time
        have hrow : ∀ a : Fin 1 → ℤ,
            (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2
              ≤ (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                  ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a,
                    ‖gramD G φ a u v‖ ^ 2) * (9 * (B : ℝ) ^ 2) := by
          intro a
          have hrg := rowGram_local T G a (Work.Peluse.Ulower.thetaFibre D H a) φ hT
          have hQ := tsum_avgNormSq_le G L (a 0) hG1 hsupp
          have hgnn : 0 ≤ ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
              ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2 :=
            Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
          have hQnn : 0 ≤ ∑' x : ℤ, ‖avgFn G (x + a 0)‖ ^ 2 :=
            tsum_nonneg (fun x => by positivity)
          have h9 : (2 * (L : ℝ) + 1) ^ 2 ≤ 9 * (B : ℝ) ^ 2 := by
            nlinarith [hBL, hL1]
          calc (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2
              ≤ (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                  ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a,
                    ‖gramD G φ a u v‖ ^ 2) * (∑' x : ℤ, ‖avgFn G (x + a 0)‖ ^ 2) ^ 2 := hrg
            _ ≤ (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                  ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a,
                    ‖gramD G φ a u v‖ ^ 2) * (9 * (B : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hQnn hQ 2) h9) hgnn
        -- Cauchy--Schwarz over the `D` rows
        have hcs : (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2
            ≤ (D : ℝ) * ∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
                (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2 := by
          have h := sq_sum_le_card_mul_sum_sq (s := Work.Peluse.Ulower.thetaBox 1 D)
            (f := fun a => ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2)
          rw [Work.Peluse.Ulower.thetaBox_card] at h
          simpa using h
        calc (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2
            ≤ (D : ℝ) * ∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
                (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2 := hcs
          _ ≤ (D : ℝ) * ∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
                (∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                  ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a,
                    ‖gramD G φ a u v‖ ^ 2) * (9 * (B : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hrow a))
                (by positivity)
          _ = 9 * (D : ℝ) * (B : ℝ) ^ 2 *
                (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
                  ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                    ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2) := by
              rw [← Finset.sum_mul]
              ring
      rw [hLHS, hRHS]
      calc ((((B : ℝ))⁻¹) ^ 2 * (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2)) ^ 2
          = ((((B : ℝ))⁻¹) ^ 2) ^ 2 * (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖rowC G φ a u‖ ^ 2) ^ 2 := by ring
        _ ≤ ((((B : ℝ))⁻¹) ^ 2) ^ 2 * (9 * (D : ℝ) * (B : ℝ) ^ 2 *
              (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
                ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                  ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = 9 * (D : ℝ) * ((((B : ℝ))⁻¹) ^ 2 * (∑ a ∈ Work.Peluse.Ulower.thetaBox 1 D,
              ∑ u ∈ Work.Peluse.Ulower.thetaFibre D H a,
                ∑ v ∈ Work.Peluse.Ulower.thetaFibre D H a, ‖gramD G φ a u v‖ ^ 2)) := by
            field_simp
  -- conclude
  have hstep : (9 : ℝ)⁻¹ * (Work.Peluse.Ulower.StepLe.hypoMass 1 B G H φ) ^ 2 ≤
      Work.Peluse.Ulower.StepLe.concMass 1 D B G H φ * (D : ℝ) := by
    calc (9 : ℝ)⁻¹ * (Work.Peluse.Ulower.StepLe.hypoMass 1 B G H φ) ^ 2
        ≤ (9 : ℝ)⁻¹ * (9 * (D : ℝ) * Work.Peluse.Ulower.StepLe.concMass 1 D B G H φ) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = Work.Peluse.Ulower.StepLe.concMass 1 D B G H φ * (D : ℝ) := by ring
  rw [show (2 : ℕ) ^ (1 : ℕ) = 2 from by norm_num,
      show 1 * (2 ^ (1 + 1) - 3) = 1 from by norm_num, pow_one]
  rw [div_le_iff₀ hDpos]
  exact hstep

end Work.Peluse.Ulower.StepLe.ddiSharp
