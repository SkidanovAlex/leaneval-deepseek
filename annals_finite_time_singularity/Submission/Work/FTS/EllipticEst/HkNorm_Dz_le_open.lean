import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.DzV_amgm_clean_sect
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

/-!
# The radial Agmon--Nirenberg interpolation `α |D_z f|_{ℋ^k} ≤ C (|f|_{ℋ^k} + α² |z²∂_z²f|_{ℋ^k})`

This module owns the statement `Work.FTS.EllipticEst.HkNorm_Dz_le_open`, the `ℋ^k` form of the
radial Agmon--Nirenberg (AM--GM) interpolation for `D_z = z ∂_z` in the weighted `H^k`-norm of
the paper, together with its honesty clause `HkMem α k (D_z f)`.

The identical statement is proved in `Submission/Work/FTS/EllipticEst/DzV_amgm_clean_sect.lean` (a frozen self-contained copy of `Submission/Work/Blocks/DzV_amgm_clean.lean`, with the unused import of the in-progress module `DzAmgm.RDzAmgmLintegralSmooth` replaced by the frozen copy `DzAmgmScratchSect`) under the name
`Work.BlocksSect.DzVamgm.HkNorm_Dz_amgm` (sorry-free; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`).  Its conclusion is *verbatim* the conclusion below,
so this module records the statement under the requested name in the shared
`Work.FTS.EllipticEst` namespace and proves it by that reference.

For the reader, the route of the cited proof:

* **the one-dimensional analytic core** (`DzAgmon1D_clean`): the weighted Agmon--Nirenberg
  inequality `α² ∫⁻ (w z)² (z h')² ≤ C² (α⁴ ∫⁻ (w z)² (z² h'')² + ∫⁻ (w z)² h²)` for `C^∞`
  data `h` on `(0,∞)` — the `L²(w²dz)` log-convexity `‖X‖² ≤ C(‖u‖² + ‖u‖‖A‖)` with
  `u = h w`, `X = z h' w`, `A = z²h'' w`, obtained from the normal form of the weight
  (`w' = -2w/(z(1+z))`), integration by parts and Cauchy--Schwarz, via a `logChi`-cutoff family
  and monotone convergence so that no decay hypothesis at `z = 0, ∞` is needed;
* **the `θ`-integration** (`hgen_of_agmon`): the one-dimensional inequality is applied to every
  angular slice; the slices are finite for a.e. `θ` because Tonelli applied to the two `HkMem`
  hypotheses (`HkMem α k f`, `HkMem α k (z²∂_z²f)`) makes the slice norms finite a.e.;
* **the term-by-term assembly** (`TZ_termwise`, `TM_termwise`, `LkSq_Dz_le`, `HkNorm_Dz_le_of`):
  applied to the summands `D_z^m f` and `D_z^m D_θ^i f` of the `ℋ^k`-integrand, using the
  identity `z²∂_z² (D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (commutation of `z²∂_z² = D_z² - D_z`
  with the powers of `D_z` and with `D_θ`);
* **the honesty certificate** (`HkMem_Dz_slices`): the `θ`-slice of every summand of
  `HkIntegrand α k (D_z f)` is finite; for the corner terms (order `1` of the `i = 0` family and
  the mixed corner `D_z D_θ^k f`) this rests on the two-point Taylor identity with integral
  remainder (`SliceZDeriv_finite` / `SliceTaylorIdentity`), all other orders being linear
  combinations `D_z^n = D_z^{n-2}(z²∂_z²) + D_z^{n-1}` of already available summands.
-/

namespace Work.FTS.EllipticEst

theorem HkNorm_Dz_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz f) ∧
        α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
          ≤ C * (Work.Spaces.HkNorm α k f
              + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :=
  Work.BlocksSect.DzVamgm.HkNorm_Dz_amgm k

end Work.FTS.EllipticEst
