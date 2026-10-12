import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.PotCubicPoissonAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs` — the kernel vocabulary of the `(D)` slot

The `(D)`-channel alias slot `PCFU.chDslot` pairs the low-momentum slot function
`Γ_x(z) = lowSlot fc κ ℓ j Ψ (x[j↦z])` against the `z`-kernel

      F(z) = KχfrU v h μ fu N z − ∫_y χ_ℓ(y)·W1fun v h ℓ (y − z) dy ,      χ_ℓ = chiLam ℓ .

This module names the pieces of `F` so that the analytic estimates can be stated:

* `chDC`  — the second term `Ĉ z = ∫_y χ_ℓ(y)·W1fun v h ℓ (y−z) dy`, as a complex number (it is
  the object literally occurring in `chDslot`);
* `chDkerE` — the *truncation kernel* `E = uvSmear fu Λ (W1fun) − W1fun`
  (`chat E = (uvCut−1)·chat W1fun`, compactly supported in frequency);
* `chDkerS` — the *smoothed* kernel `uvSmear fu Λ (W1fun)`;
* `chDconv` — the `χ`-convolution `(χ_ℓ ⋆ f)(u) = ∫_w χ_ℓ(w)·f(u−w) dw`, complex-valued.

The two Poisson-summation identities which drive the estimate are

    KχfrU v h μ fu N z = Σ'_d (χ_ℓ ⋆ uvSmear)(z + ℓ•d)                        (`chDpoisson_uvSmear`)
    Σ'_d (χ_ℓ ⋆ E)(z + ℓ•d) = Σ'_m (uvCut−1)(κ_m)·chat W1fun(κ_m)·χ̂(ℓκ_m)·e^{i⟪κ_m,z⟫}
                                                                               (`chDpoisson_E`)

(both from `Work.BoseBoxFock.latSampling_decay`), and the two errors are

* the Fourier tail of the second line: small because `uvCut − 1` is supported on `‖p‖ ≥ Λ_N`, where
  `chat W1fun` is small (`PCFU.W1fun_chat_small`), against the lattice tail
  `Σ_{‖m‖ ≥ M}|χ̂(vec m)| ≤ C/(M+1)` of the bump (`BoseRowQ2.chiHat_abs_tail_le`);
* the *alias* sum `Σ'_{d≠0}(χ_ℓ ⋆ W1fun)(z+ℓ•d)`, small by the face layer
  (`chi_mul_chi_le_of_alias`) since `W1fun` is supported in `ball 0 R` with `2R ≤ ℓ`
  (only the `d` with `‖d‖ ≤ 1+R/ℓ` survive, and each of them carries the factor `(R/ℓ)^{2M}`).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `χ_ℓ`-convolution of a complex kernel: `(χ_ℓ ⋆ f)(u) = ∫_w χ_ℓ(w)·f(u−w) dw`. -/
def chDconv (ℓ : ℝ) (f : E3 → ℂ) (u : E3) : ℂ :=
  ∫ w : E3, (((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ)) : ℂ) * f (u - w)

/-- The second term of the `(D)`-slot kernel: `Ĉ z = ∫_y χ_ℓ(y)·W1fun v h ℓ (y−z) dy`
(complex-valued, exactly as it occurs in `chDslot`). -/
def chDC {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (ℓ : ℝ) (z : E3) : ℂ :=
  ∫ y : E3, (((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ)) : ℂ)
    * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)

/-- The truncation kernel `E = uvSmear fu Λ_N (W1fun) − W1fun`, whose Fourier transform is
`(uvCut fu Λ_N − 1)·chat W1fun` (compactly supported in `‖p‖ ≥ Λ_N`). -/
def chDkerE {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ)
    (N : ℕ) : E3 → ℝ :=
  fun u => Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
      (Work.BoseFixR.W1fun v h ℓ) u - Work.BoseFixR.W1fun v h ℓ u

/-- The smoothing kernel `uvSmear fu Λ_N (W1fun)` as a complex function. -/
def chDkerS {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ)
    (N : ℕ) : E3 → ℂ :=
  fun u => ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
      (Work.BoseFixR.W1fun v h ℓ) u : ℝ) : ℂ)

end Work.BoseBoxFock.PCFU
