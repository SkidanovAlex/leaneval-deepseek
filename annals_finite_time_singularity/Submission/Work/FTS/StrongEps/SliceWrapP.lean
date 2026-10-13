/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/SliceWrapP.lean` — the `E1` commutation for the *projected* family

`SliceWrap.lean` records the slicewise form of the `E1` commutation for the scheme's family
`Jfam ρ ε g = fun z θ τ => J_ε (slice g τ)`.  With the `P₀`-repair of the scheme
(`PZeroScheme.lean`) the family on the proof path is the *projected* one

  `JfamP ρ ε g = fun z θ τ => P₀ (J_ε (slice g τ))`,

so the same two statements are needed for it:

* `mixed_JfamP` — the mixed derivatives of the projected profile, from the (proved)
  `PZeroAux.mixed_Pz` applied to `J_ε (slice g τ)`:
  `D_z^j D_θ^i (JfamP ρ ε g)(τ) = D_z^j D_θ^i (J_ε g_τ) − (L₁₂(J_ε g_τ)(0)/pzNorm)·D_z^j D_θ^i bump`;
* `HkSq_JfamP_le` — the `ℋ^k`-bound `|JfamP ρ ε g(τ)|_{ℋ^k}² ≤ C·|g(τ)|_{ℋ⁶}²`, from the proved
  `E1` bound `HkSq_Jeps_le` composed with the proved norm distortion of `P₀`
  (`PZeroAux.hkNorm_Pz_le`).

Nothing here is a reduction: both proofs compose already proved lemmas.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SliceWrap
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The slicewise commutation, projected form**: the mixed derivative of the projected mollified
slice is the mixed derivative of the mollified slice, corrected by the rank-one `P₀`-term. -/
theorem mixed_JfamP (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {g : Fam}
    (hloc : ∀ τ : ℝ, MeasureTheory.LocallyIntegrable (logPull (slice g τ)) volume)
    {τ z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (slice (JfamP ρ ε g) τ) z θ
      = Work.Spaces.mixed j i (Jeps ρ ε (slice g τ)) z θ
        - (Work.Construction.L12 (Jeps ρ ε (slice g τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump z θ := by
  rw [slice_JfamP]
  refine PZeroAux.mixed_Pz ?_ hz hθ j i
  exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
    (Jeps_contDiffOn ρ hρ hε (hloc τ))

/-- **The slicewise weighted bound, projected form**: a single constant `C` (depending only on the
mollifier) with `|JfamP ρ ε g(τ)|_{ℋ^k}² ≤ C·|g(τ)|_{ℋ⁶}²` for every `α ∈ (0,1]`, `k ≤ 6`,
`0 < ε ≤ 1`. -/
theorem HkSq_JfamP_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ g : Fam, ∀ τ : ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Quad) →
        MeasureTheory.LocallyIntegrable (logPull (slice g τ)) volume →
        Work.Spaces.HkMem α 6 (slice g τ) →
        Work.Spaces.HkSq α k (slice (JfamP ρ ε g) τ)
          ≤ C * Work.Spaces.HkSq α 6 (slice g τ) := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨A, hApos, hA⟩ := PZeroAux.hkNorm_Pz_le
  refine ⟨A ^ 2 * Real.exp CJ, by positivity, ?_⟩
  intro α hα k hk ε hε hε1 g τ hsm hloc hmem6
  have hmem6J : Work.Spaces.HkMem α 6 (Jeps ρ ε (slice g τ)) :=
    HkMem_Jeps hρ.moll hα hε hsm hmem6
  -- the `P₀`-distortion at level `k`
  have hP := hA α hα k hk (Jeps ρ ε (slice g τ))
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (Jeps_contDiffOn ρ hρ hε hloc)) hmem6J
  -- the `E1` bound at level `6`
  have hJ := hCJ α hα 6 ε hε hε1 (slice g τ) hsm hmem6 hmem6J
  have hsq : Work.Spaces.HkSq α k (slice (JfamP ρ ε g) τ)
      = (Work.Spaces.HkNorm α k (slice (JfamP ρ ε g) τ)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k _)]
  have hPz : slice (JfamP ρ ε g) τ = Pz (Jeps ρ ε (slice g τ)) := slice_JfamP ρ ε g τ
  rw [hsq, hPz]
  calc (Work.Spaces.HkNorm α k (Pz (Jeps ρ ε (slice g τ)))) ^ 2
      ≤ (A * Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g τ))) ^ 2 :=
        pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg _ _ _) hP 2
    _ = A ^ 2 * (Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g τ))) ^ 2 := by ring
    _ = A ^ 2 * Work.Spaces.HkSq α 6 (Jeps ρ ε (slice g τ)) := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)]
    _ ≤ A ^ 2 * (Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ)) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ A ^ 2 * Real.exp CJ * Work.Spaces.HkSq α 6 (slice g τ) := by
        have hexp : Real.exp (CJ * ε) ≤ Real.exp CJ :=
          Real.exp_le_exp.mpr (by nlinarith [hCJpos, hε1])
        have h1 : A ^ 2 * Real.exp (CJ * ε) ≤ A ^ 2 * Real.exp CJ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        calc A ^ 2 * (Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ))
            = A ^ 2 * Real.exp (CJ * ε) * Work.Spaces.HkSq α 6 (slice g τ) := by ring
          _ ≤ A ^ 2 * Real.exp CJ * Work.Spaces.HkSq α 6 (slice g τ) :=
              mul_le_mul_of_nonneg_right h1 (Work.Spaces.HkSq_nonneg α 6 _)

end Work.FTS.StrongEps
