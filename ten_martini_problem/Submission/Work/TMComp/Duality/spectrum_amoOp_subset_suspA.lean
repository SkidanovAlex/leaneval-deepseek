import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.Basic
import Submission.Work.TMComp.Duality.blockVec_norm
import Submission.Work.TMComp.Duality.blockVec_residual
import Submission.Work.TMComp.Duality.amoOp_selfAdjoint
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# `σ(amoOp α λ 0) ⊆ σ(suspA α λ)`

The spectrum of the almost Mathieu operator at phase `0` is contained in the spectrum of
the suspension operator on `ℓ²(ℤ × ℤ)`.

The proof is the "block vector" argument of Aubry duality: `suspA α λ` is (up to the Aubry
twist) unitarily equivalent to the direct integral of the `amoOp α λ θ` over all phases,
so each spectral point of `amoOp α λ 0` is a spectral point of `suspA α λ`.

Suppose `z ∈ σ(amoOp α λ 0)` but `z ∉ σ(suspA α λ)`. Then `suspA α λ - z` is bounded below
by some `d > 0`, while (since `amoOp α λ 0` is self-adjoint) `z` is real and admits a
finitely supported approximate eigenvector `u` with residual `< (d/4)‖u‖`. Spreading `u`
over the `N` phase modes (`blockVec u s N`) gives a vector whose `suspA`-residual is
`O(1/√N)` while its norm is `‖u‖/√N`; comparing with the lower bound and letting `N → ∞`
forces `‖residual u‖ ≥ (d/4)‖u‖`, a contradiction.
-/

open LeanEval.Analysis.TenMartini

namespace Work.TMComp.Duality

noncomputable section

theorem spectrum_amoOp_subset_suspA (α lam : ℝ) :
    spectrum ℂ (Work.TMComp.Duality.amoOp α lam 0) ⊆
      spectrum ℂ (Work.TMComp.Duality.suspA α lam) := by
  intro z hz
  -- `amoOp α lam 0` is self-adjoint, so `z` is real.
  have hzre : z = (z.re : ℂ) := (amoOp_selfAdjoint α lam 0).mem_spectrum_eq_re hz
  set E : ℝ := z.re with hE
  have hzE : (E : ℂ) ∈ spectrum ℂ (amoOp α lam 0) := by
    rw [hE, ← hzre]; exact hz
  by_contra hznot
  have hnotE : (E : ℂ) ∉ spectrum ℂ (suspA α lam) := by
    rw [hE, ← hzre]; exact hznot
  -- Lower bound from the assumption that `z` is not in the suspension spectrum.
  obtain ⟨d, hdpos, hlow⟩ := exists_lower_bound_of_notMem (suspA α lam) E hnotE
  -- A finitely supported approximate eigenvector with residual `< (d/4)‖u‖`.
  obtain ⟨u, hu_ne, ⟨s, hs⟩, hu_res⟩ :=
    Work.TMC7Core.Scale.fs_approx (amoOp α lam 0) (amoOp_selfAdjoint α lam 0) E hzE
      (δ := d / 4) (by positivity)
  -- Choose `N` large.
  obtain ⟨N, hNbig⟩ := exists_nat_gt (128 * lam ^ 2 / d ^ 2)
  have hNposR : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hNbig
  have hNpos : 0 < N := by exact_mod_cast hNposR
  set Rv : EllTwo := (amoOp α lam 0 - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u with hRv
  set v : EllTwo2 := blockVec (u : ℤ → ℂ) s N with hv
  -- Rewrite the `algebraMap`-scalars as real scalars to match `blockVec_residual`.
  have hEqR : (amoOp α lam 0 - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E)
      = (amoOp α lam 0 - E • (1 : EllTwo →L[ℂ] EllTwo)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact congrArg (fun t : EllTwo →L[ℂ] EllTwo => amoOp α lam 0 - t) (Complex.coe_smul E 1)
  have hEqS : (suspA α lam - algebraMap ℂ (EllTwo2 →L[ℂ] EllTwo2) E)
      = (suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact congrArg (fun t : EllTwo2 →L[ℂ] EllTwo2 => suspA α lam - t) (Complex.coe_smul E 1)
  have hres : ‖(suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) v‖ ^ 2
      ≤ 8 * (‖Rv‖ ^ 2 / (N : ℝ) + 8 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := by
    have h := blockVec_residual α lam E u s hs hNpos
    rw [← hv, ← hEqR, ← hRv] at h
    exact h
  have hlow_v : d * ‖v‖ ≤ ‖(suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) v‖ := by
    have h := hlow v
    rwa [hEqS] at h
  have hnormv : ‖v‖ ^ 2 = ‖u‖ ^ 2 / (N : ℝ) := by
    rw [hv]; exact blockVec_norm u s hs hNpos
  have hsq : d ^ 2 * ‖v‖ ^ 2 ≤ ‖(suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) v‖ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ d * ‖v‖) hlow_v 2
    simpa [mul_pow] using h
  have hU2 : (0 : ℝ) < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have step1 : d ^ 2 * ‖u‖ ^ 2 / (N : ℝ)
      ≤ 8 * ‖Rv‖ ^ 2 / (N : ℝ) + 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := by
    calc d ^ 2 * ‖u‖ ^ 2 / (N : ℝ) = d ^ 2 * ‖v‖ ^ 2 := by rw [hnormv]; ring
      _ ≤ ‖(suspA α lam - E • (1 : EllTwo2 →L[ℂ] EllTwo2)) v‖ ^ 2 := hsq
      _ ≤ 8 * (‖Rv‖ ^ 2 / (N : ℝ) + 8 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2) := hres
      _ = 8 * ‖Rv‖ ^ 2 / (N : ℝ) + 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2 := by ring
  have step2 : d ^ 2 * ‖u‖ ^ 2 ≤ 8 * ‖Rv‖ ^ 2 + 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left step1 (le_of_lt hNposR)
    have e1 : (N : ℝ) * (d ^ 2 * ‖u‖ ^ 2 / (N : ℝ)) = d ^ 2 * ‖u‖ ^ 2 := by
      field_simp
    have e2 : (N : ℝ) * (8 * ‖Rv‖ ^ 2 / (N : ℝ) + 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) ^ 2)
        = 8 * ‖Rv‖ ^ 2 + 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) := by
      field_simp
    rwa [e1, e2] at h
  have hkey : d ^ 2 * ‖u‖ ^ 2 / 2 < 8 * ‖Rv‖ ^ 2 := by
    have hlt : 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ) < d ^ 2 * ‖u‖ ^ 2 / 2 := by
      have h1 : 128 * lam ^ 2 < (N : ℝ) * d ^ 2 := by
        have hd2 : (0 : ℝ) < d ^ 2 := by positivity
        have h2 := (div_lt_iff₀ hd2).mp hNbig
        linarith [h2]
      have hmain : 64 * lam ^ 2 / (N : ℝ) < d ^ 2 / 2 := by
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2),
          show (64 * lam ^ 2 / (N : ℝ)) * 2 = 128 * lam ^ 2 / (N : ℝ) by ring,
          div_lt_iff₀ hNposR]
        linarith [h1]
      calc 64 * lam ^ 2 * ‖u‖ ^ 2 / (N : ℝ)
          = (64 * lam ^ 2 / (N : ℝ)) * ‖u‖ ^ 2 := by ring
        _ < (d ^ 2 / 2) * ‖u‖ ^ 2 := mul_lt_mul_of_pos_right hmain hU2
        _ = d ^ 2 * ‖u‖ ^ 2 / 2 := by ring
    linarith [step2, hlt]
  have hRgt : d * ‖u‖ / 4 < ‖Rv‖ := by
    have h4 : (d * ‖u‖ / 4) ^ 2 < ‖Rv‖ ^ 2 := by
      have hkey' : d ^ 2 * ‖u‖ ^ 2 / 16 < ‖Rv‖ ^ 2 := by nlinarith [hkey]
      have e : (d * ‖u‖ / 4) ^ 2 = d ^ 2 * ‖u‖ ^ 2 / 16 := by ring
      rwa [e]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg Rv) h4
  have hu_res' : ‖Rv‖ < d / 4 * ‖u‖ := by
    rw [hRv]; exact hu_res
  have he : d / 4 * ‖u‖ = d * ‖u‖ / 4 := by ring
  rw [he] at hu_res'
  linarith [hRgt, hu_res']

end

end Work.TMComp.Duality
