import ChallengeDeps
import Submission.Work.BoseBogFS.ZPE1E2Corrected
import Submission.Work.BoseBogFS.ZPKernel.CosTelescope
import Submission.Work.BoseBogFS.ZPKernel.Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

/-- **The sharp lattice–Coulomb row at the honest kernel `W₁ = W1fun v h ℓ`** (FS
`eq:I2-integral` mechanism, the design's D5 item `latticeCoulomb_approx`; the mass input of
`Work.BoseBogFS.ZPLatticeRow`).

For every admissible datum (`Adm v ε₀ μ`, `CloseCondFS v μ ρ`) and every finite set `S` of
*nonzero* dual-lattice labels, the lattice sum of `Ŵ₁(k_n)²/(4‖k_n‖²)`
(`k_n = kAt v μ n = ℓ⁻¹•vec n = 2πn/ℓ`) is at most the continuum integral
`(2π)⁻³ℓ³∫Ŵ₁(p)²/(4‖p‖²)dp` plus the near-image error `C·ℓ²(∫W₁)²` (with a **fixed**
constant `C`, independent of `v,h,R,μ,ρ`).

WHY THIS SHAPE / WHY IT IS NOT ALREADY IN THE WORKSPACE.  An earlier version of this row is
filed at `Submission/Work/BoseBogFS/ZPMassLatticeRowSharp.lean` as
`... * ∫ p, (chat W p)^2/(4*‖p‖^2) + C * ℓ^2 * (∫ x, W x)^2`: Lean's `∫ p, …` swallows the
trailing `+ C ℓ²(∫W)²` (the integral body extends to the next delimiter), so that statement has
the error term *inside* the integral, which makes the integral the junk value `0` and the row
FALSE.  The statement here has the integral parenthesised.  (A second, differently flat
statement is `Submission/Work/BoseRowsL/LatticeCoulomb/latticeCoulomb_approx.lean`: matched
cut-off form, currently `sorry`, and its supporting `latticeKernel_bound.lean` does not even
compile at present.)

PROOF INGREDIENTS (all proved in this workspace, and enough to finish):
* `Work.BoseBogFS.ZPW1Facts` (proved) supplies, at one diluteness threshold, all the structural
  facts about `W₁ = W1At v h μ` used below: evenness, `tsupport ⊆ ball 0 R`, `L¹`,
  a.e. nonnegativity, pair-integrability, `4 * R ≤ ell v μ`, and `8πa ≤ ∫W₁ ≤ 16πa`.  In
  particular **`4R ≤ ℓ` must be extracted from it** (or from `existsAdmRegime` at `r₁ = 1/4`);
  with only `R ≤ ℓ` the row is FALSE (`FINDING_ZPMassLatticeRow_FALSE.md`: a two-half-ball
  counterexample, `chat` invisible to the shift by `ℓ/2` while the Coulomb energy doubles).
* `Work.BoseB7AK.W1rows.W1hat_abs_le` (`|Ŵ₁(p)| ≤ 16πa` for all `p`) and the support bound
  `|∇Ŵ₁(p)| ≤ ∫‖x‖|W₁ x|dx ≤ R·∫W₁` (from the definition of `chat`/`kinFT`) give the pointwise
  control of `f := Ŵ₁(p)²/(4‖p‖²)` needed by either route below.
* the position-space kernel comparison (Madelung-type): `Ω(z) := Σ_{n≠0}cos(2π⟪nvec n,z⟫)/‖nvec n‖²
  − ∫_{ball 0 R}cos(2π⟪q,z⟫)/‖q‖²dq` is bounded on `‖z‖ ≤ 1/2`
  (`BoseRowsL/LatticeCoulomb/kernelDefs.lean` is the proved development of exactly this object;
  note that `latticeKernel_bound.lean`'s own reduction imports `sorry`-carrying telescope
  modules, so re-derive what you need there or use the cheap route below).
* cheap alternative for the same content: the Riemann/cell argument
  `Σ_{n≠0} f(k_n) = (2π)⁻³ℓ³∫_{∪_{n≠0} cell_n} f + Σ_{n≠0} (f(k_n) − (2π)⁻³ℓ³∫_{cell_n} f)`
  with the mean-value bound `|f(k_n) − (2π)⁻³ℓ³∫_{cell_n}f| ≤ (2π/ℓ)·∫_{cell_n}‖∇f‖`
  (the cell containing `p = 0` is excluded because `S` has no zero label, and its integral is
  dropped using `f ≥ 0`);
* for the *untruncation* of the integral (necessary because `S` is an arbitrary finite set):
  `Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq` plus the finiteness of the Coulomb double
  lintegral from the sandwich in `BoseB7AK/C3Q/I2_integral_bound.lean`
  (`I2coul W₁ ≤ (1+2C₁(R/ℓ)²)²·8π∫g₀ω < ⊤`, via `W1_sharp_ae_aux` and
  `lintegral_double_eq_ofReal_newton`) give `Integrable (fun p => Ŵ₁(p)²/(2‖p‖²))`, hence
  `∫_{‖p‖≤K} f ≤ ∫_{all} f`.  `Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal` identifies
  `(2π)⁻³∫Ŵ₁(p)²/(2‖p‖²)dp` with `(1/8π)∬W₁x W₁y/‖x−y‖`, which is the natural pairing with
  the kernel comparison.

The `ρ`-dependence is deliberately absent (the row is homogeneous: the consumer multiplies by
`ρ ^ 2`), and `CloseCondFS v μ ρ` is kept only to match the consumer's interface. -/
theorem ZPMassLatticeRowHonest :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R → 0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
        Work.BoseBoxFock.CloseCondFS v μ ρ →
        ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, n ≠ 0) →
          ∑ n ∈ S, (Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ)
              (Work.BoseBogFS.kAt v μ n)) ^ 2 / (4 * ‖Work.BoseBogFS.kAt v μ n‖ ^ 2)
            ≤ ((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
                * (∫ p : EuclideanSpace ℝ (Fin 3),
                    (Work.BoseFixR.chat (Work.BoseBogFS.W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
              + C * (Work.BoseFixR.ell v μ) ^ 2
                  * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.W1At v h μ x) ^ 2 := by
  refine ZPMassLatticeRowHonest_of ?_
  intro R T j z h1 h2 h4 hz
  have h := Work.BoseBogFS.ZPKernel.CosTelescope R T j z h1 h2 h4 hz
  have h' : (10 : ℝ) ^ 8 = 100000000 := by norm_num
  exact le_trans h (le_of_eq h'.symm)

end Work.BoseBogFS
