import Mathlib
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.vol_wl1_ball
import Submission.Work.BW.basisRed_bridge
import Submission.Work.BW.basisRed_wNorm_isLatticeNorm
import Submission.Work.BW.Minkowski2.volume_wNorm_ball
import Submission.Work.BW.KW.minkowski_second_norm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory

/-!
# Minkowski's second theorem for the weighted `ℓ¹` body and the lattice `A ℤⁿ`

We prove `Work.BW.kummer_minkowski_second`:
`∏_j succMin (latOf A) (wl1 c) (j+1) ≤ n! · |det A| · ∏ cᵢ`.

The proof has three ingredients, all in terms of the standard lattice `ℤⁿ` and a "lattice norm"
`F` on `ℝⁿ` (`Work.BW.IsLatticeNorm F`):

* `Work.BW.basisRed_bridge` (imported, proved): the successive minima of the lattice `A ℤⁿ` with
  respect to the weighted `ℓ¹` body `{x | wl1 c x ≤ 1}` are the successive minima of `ℤⁿ` with
  respect to the unit ball of `wNorm A c = wl1 c ∘ A` — this is the linear change of variables
  `y ↦ A y` (`A.det ≠ 0`), transported through the definitions of `succMin`/`succMinL`;
* Minkowski's second convex body theorem for `ℤⁿ`: for every lattice norm `F`,
  `(∏_j succMinL F (j+1)) * volume.real {x | F x ≤ 1} ≤ 2 ^ n` (this is the classical theorem,
  see `Work.BW.KW.minkowski_second_norm`; here it is taken as a hypothesis so that the assembly
  below can be checked independently);
* `Work.BW.Minkowski2.volume_wNorm_ball` (imported, proved): the unit ball of `wNorm A c` has
  volume `2 ^ n / (n! · (∏ i, c i) · |det A|)`.

Dividing the second inequality by the third volume gives the claim.
-/

/-- Assembly of `Work.BW.kummer_minkowski_second` from Minkowski's second theorem for the
lattice norm `wNorm A c`: if `(∏_j succMinL (wNorm A c) (j+1)) * vol{wNorm A c ≤ 1} ≤ 2ⁿ`, then
`∏_j succMin (latOf A) (wl1 c) (j+1) ≤ n! · |det A| · ∏ cᵢ`.

The auxiliary hypothesis `hcore` is exactly the conclusion of `Work.BW.KW.minkowski_second_norm`
specialised to `F = Work.BW.wNorm A c`, whose `IsLatticeNorm` instance is
`Work.BW.basisRed_wNorm_isLatticeNorm`. -/
theorem kummer_minkowski_second_of_core {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (hcore : (∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1)) *
        MeasureTheory.volume.real {x : Fin n → ℝ | Work.BW.wNorm A c x ≤ 1} ≤ (2 : ℝ) ^ n) :
    ∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1)
      ≤ (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  -- The successive minima of `A ℤⁿ` with respect to `{wl1 c ≤ 1}` are those of `ℤⁿ` with
  -- respect to the unit ball of `wNorm A c`.
  have hstep1 : (∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1))
      = ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) :=
    Finset.prod_congr rfl fun j _ => (Work.BW.basisRed_bridge A hA c (j.1 + 1)).symm
  rw [hstep1]
  set P : ℝ := ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1) with hP
  set D : ℝ := (n.factorial : ℝ) * (∏ i, c i) * |((A.det : ℤ) : ℝ)| with hD
  have hcore' : P * MeasureTheory.volume.real {x : Fin n → ℝ | Work.BW.wNorm A c x ≤ 1}
      ≤ (2 : ℝ) ^ n := by
    rw [hP]; exact hcore
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hprod : (0 : ℝ) < ∏ i, c i := Finset.prod_pos fun i _ => hc i
  have hdet : (0 : ℝ) < |((A.det : ℤ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hA
  have hDpos : 0 < D := by
    rw [hD]
    exact mul_pos (mul_pos hfac hprod) hdet
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n
  have hDne : D ≠ 0 := ne_of_gt hDpos
  -- Insert the volume of the unit ball and divide by it.
  rw [Work.BW.Minkowski2.volume_wNorm_ball A hA c hc, ← hD] at hcore'
  have hPD : P * (2 ^ n / D) * ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hcore'
      (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)
    rwa [mul_inv_cancel₀ h2ne] at hh
  have hsimp : (2 : ℝ) ^ n / D * ((2 : ℝ) ^ n)⁻¹ = D⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc, mul_comm D⁻¹ ((2 : ℝ) ^ n)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ h2ne, one_mul]
  have hPD' : P / D ≤ 1 := by
    rw [div_eq_mul_inv]
    have h := hPD
    rwa [mul_assoc, hsimp] at h
  have h4 : P ≤ D := by
    have h := (div_le_iff₀ hDpos).mp hPD'
    rwa [one_mul] at h
  rw [hP, hD] at h4
  calc ∏ j : Fin n, Work.BW.succMinL (Work.BW.wNorm A c) (j.1 + 1)
      ≤ (n.factorial : ℝ) * (∏ i, c i) * |((A.det : ℤ) : ℝ)| := h4
    _ = (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by ring

/-- Minkowski's second (convex body) inequality for the weighted `ℓ¹` body
`B = {x | ∑ i, c i * |x i| ≤ 1}` and the lattice `latOf A = A ℤⁿ ⊆ ℝⁿ` (a full lattice when
`A.det ≠ 0`): the product of the successive minima `λ_j = succMin (latOf A) (wl1 c) (j+1)` is at
most `n! * |det A| * ∏ c i`.

Indeed `vol B = 2^n / (n! * ∏ c i)` (see `Submission.Work.BW.vol_wl1_ball`) and the second
inequality states `∏_{j=1}^n λ_j ≤ 2^n * covol(latOf A) / vol B = n! * |det A| * ∏ c i`.

Definitions `wl1`, `latOf`, `succMin` are in `Submission.Work.BW.minkowski_defs`. A possible route
(the classical counting/"density" proof) is sketched in the scratch file
`Submission/Work/BW/Minkowski2/scratch.lean`: `latOf A` discrete and a `ℤ`-lattice,
`covolume (latOf A) = |det A|`, counting lattice points in growing cubes, and the
slicing/covering estimates. -/
theorem kummer_minkowski_second {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∏ j : Fin n, Work.BW.succMin (Work.BW.latOf A) (Work.BW.wl1 c) (j.1 + 1)
      ≤ (n.factorial : ℝ) * |((A.det : ℤ) : ℝ)| * ∏ i, c i := by
  exact kummer_minkowski_second_of_core hn A hA c hc
    (Work.BW.KW.minkowski_second_norm (Work.BW.wNorm A c)
      (Work.BW.basisRed_wNorm_isLatticeNorm A hA c hc))

end Work.BW
