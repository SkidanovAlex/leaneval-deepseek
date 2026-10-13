import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

/-
# The `j`-th slice group of the `ℋ^k`-integrand, rewritten through a single slice

`Work.FTS.EllipticEst.sliceGroup α k j f z θ` is the `j`-th group of
`Work.Spaces.HkIntegrand α k f z θ`: its radial summand `(D_z^j f z θ · w z/sin(2θ)^{η/2})²` plus
the mixed summands `(mixed j i f z θ · Wt α z θ)²` for `1 ≤ i ≤ k-j`; the integrand is the sum of
the groups over `j ≤ k` (`Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum`).
Claim: for `z > 0`, `θ ∈ (0,π/2)` and `f` of class `C^∞` on the open quadrant,

  `sliceGroup α k j f z θ = (w z)² · sliceW (k-j) α (fun θ' => D_z^j f z θ') θ`,

where `sliceW K α u θ = (u θ)²·thEta θ + ∑_{1≤i≤K}(L^i u θ)²·thGam α θ` is the single-slice
functional of `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean` and `L^i = LopIter i` is the
iterate of `D_θ = sin(2θ)∂_θ`.

ROUTE: unfold `sliceGroup`, rewrite the two weight squares with
`Work.FTS.EllipticEst.w_div_sin_sq` and `Work.FTS.EllipticEst.Wt_sq` (both in
`Submission/Work/FTS/EllipticEst/SliceAux.lean`), and identify
`mixed j i f z θ = LopIter i (fun θ' => D_z^j f z θ') θ` for `θ ∈ (0,π/2)`, which is
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` (open-quadrant commutation, in
`Submission/Work/FTS/EllipticEst/SliceDecompDefs.lean`) combined with
`Work.FTS.EllipticEst.LopIter_slice` (which identifies the `D_θ`-iterate of a `z`-slice with the
`L`-iterate of the one-variable slice). The hypothesis `0 < z` is needed exactly because the
commutation is available on the open quadrant only. The mixed indices of the group run over
`Finset.Icc 1 (k-j)`, matching `sliceW (k-j)`.
-/
theorem sliceGroup_eq_sliceW (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceGroup α k j f z θ
        = (Work.Spaces.w z) ^ 2
            * Work.FTS.EllSol.VopAux.sliceW (k - j) α
                (fun θ' => Work.Spaces.DzIter j f z θ') θ := by
  intro θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `L`-iterate of the `z`-slice is the mixed derivative
  have hmixed : ∀ i : ℕ,
      Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ
        = Work.Spaces.mixed j i f z θ := by
    intro i
    have hLS := congrFun (Work.FTS.EllipticEst.LopIter_slice i (Work.Spaces.DzIter j f) z) θ
    rw [hLS]
    exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hf j i hz hθ
  rw [Work.FTS.EllipticEst.sliceGroup, Work.FTS.EllSol.VopAux.sliceW]
  -- the radial summand, rewritten with the weight identity
  have hrad := Work.FTS.EllipticEst.rad_term_eq hθIθ z (Work.Spaces.DzIter j f z θ)
  -- the mixed summands, rewritten with the weight identity and the `L`-iterate
  have hsum : (∑ i ∈ Finset.Icc 1 (k - j),
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * ∑ i ∈ Finset.Icc 1 (k - j),
          (Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.EllipticEst.mix_term_eq hθIθ α z (Work.Spaces.mixed j i f z θ),
      ← hmixed i, Work.FTS.EllipticEst.sGam_eq_thGam]
  rw [hrad, hsum, Work.FTS.EllipticEst.sEta_eq_thEta, mul_add]

end Work.FTS.EllSol.VopAux
