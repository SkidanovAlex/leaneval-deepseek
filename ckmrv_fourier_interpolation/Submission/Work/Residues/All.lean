/-
# The residues chapter of the CKMRV Fourier-interpolation project

Import this module to obtain the whole area developed under `Submission/Work/Residues/`:
the quotient algebra `R/𝓘`, `R/𝓘_±` of the group algebra `R = ℂ[SL(2,ℤ)]` together with the
linear functionals `φ`, `φ_±` (CKMRV Section 3.3, Proposition 3.8), and the residue theorems of
CKMRV Theorem 4.9 -- the residue of the slashed kernels at `τ = z` and at every point of the
`SL(2,ℤ)`-orbit of `z`.

## Main definitions

* `Work.Residues.Rneg`, `Work.Residues.augIdeal`, `Work.Residues.idealI`, `idealIp`, `idealIm`
  (`Basic`) : the ideals `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` (with `z = -I`, the central element
  that CKMRV call `z`) and `𝓘_± = (S±I)R + (T-I)²R + (z-1)R`, with the elements
  `M6 = (1,T,TS,S,ST,STS)` and `M3 = (1,T,TS)`.
* `Work.Residues.HasResidue f z c` (`Poles`) : the limit form `(τ-z)f τ → c` of "at most a
  simple pole with residue `c`", with its API (`HasResidue.add`, `.sub`, `.neg`, `.const_mul`,
  `.unique`, `.of_eventuallyEq`, `HasResidue.sum`), the bridge from
  `Work.Kernels.HasSimplePoleWithResidue`, and the master computation
  `Work.Residues.hasResidue_of_cleared` of the residue of a kernel from its cleared form and
  `j'(z) = -2πiE₄²E₆/Δ`.
* `Work.Residues.HasSimplePoleWithResidue.*` (`SimplePoleAPI`) : the API of the
  `MDifferentiableAt`-based notion of `Work.Kernels`, including the model function
  `Work.Residues.hasSimplePoleWithResidue_inv_sub`.  (Caution: with Lean's convention
  `0⁻¹ = 0` that notion is *false* for the diagonal function `z ↦ K z z`; all residue theorems
  here are stated with `HasResidue`.)

## Main results

* **Proposition 3.8 / Theorem 4.9(1)** (`Work.Residues.Quotient`, `Work.Residues.Basic`):
  `dim_ℂ R/𝓘 = 6`, `dim_ℂ R/𝓘_± = 3` with the explicit bases `1,T,TS,S,ST,STS` and `1,T,TS`:
  `Work.Residues.finrank_quotient_idealI`, `finrank_quotient_idealIp`, `finrank_quotient_idealIm`,
  `basisI`, `basisIp`, `basisIm`, and the functionals `Work.Residues.phi`, `phiPlus`, `phiMinus`
  of (3.12) with their values on the bases (`phiPlus_R_T`, `phiPlus_TS`, `phiPlus_R_S`,
  `phiPlus_ST`, `phiPlus_STS`, ...) and `phi = (phiPlus + phiMinus)/2`.

* **Theorem 4.9(3)** (`Work.Residues.ResidueKernel`, `ResidueTheorem`, `ResidueTheoremMinus`,
  `ResidueTheoremK`): for every `r ∈ R` and every `z` with `j'(z) ≠ 0`,
  `Work.Residues.hasResidue_slash_KPlus : HasResidue (slash (d/2) r (K_+ · z)) z (-(1/2π)φ_+(r))`,
  `Work.Residues.hasResidue_slash_KMinus` (with `φ_-`), and for `K = (K_++K_-)/2`,
  `K̂ = (K_+-K_-)/2`: `hasResidue_slash_Kfun` (residue `-(1/2π)φ(r)`) and
  `hasResidue_slash_Khat` (residue `-(1/2π)(φ_+(r)-φ_-(r))/2`).

* **Theorem 4.9(1)+(3) on the whole orbit** (`Work.Residues.ResidueOrbit`):
  `Work.Residues.hasResidue_slash_KPlus_orbit` and `hasResidue_slash_KMinus_orbit` compute the
  residue at `τ = δz` of the transported kernel:
  `Res_{τ=δz}(K_±|^τ_{d/2}(rδ⁻¹)) = -(j(δ,z)^{d/2-2}/2π)φ_±(r)`, with the `rδ` form
  `hasResidue_slash_KPlus_orbit'`; the transport step is isolated as
  `Work.Residues.hasResidue_transfer_inv` (the paper's (residue1)) and the automorphy factor is
  `Work.Residues.jFun_inv_smul_zpow`.

* **The location of the poles (Theorem 4.9(1))** (`Work.Residues.KernelPoleLocation`):
  `Work.Residues.mdifferentiableAt_Kfun_fst`, `..._Kfun_snd` (and the `KPlus`/`KMinus`/`Khat`
  versions) : `τ ↦ K^{(d)}(τ,z)` (resp. `ζ ↦ K^{(d)}(z,ζ)`) is holomorphic at every point with
  `j ≠ j(z)`, i.e. the poles are *contained* in the `SL(2,ℤ)`-orbit of `z`; and conversely
  `Work.Residues.not_mdifferentiableAt_KPlus_orbit` (`..._KMinus_orbit`) : for
  `φ_±(single δ) ≠ 0` the point `δz` **is** a pole (a nonzero residue), so the pole set of
  `K_±(·,z)` is exactly `{δz : φ_±(δ) ≠ 0}`.

* **The residue in the second variable** (`Work.Residues.ResidueSecondVariable`): the
  companion of Theorem 4.9(3) obtained by swapping the roles of the two variables (the
  paper's (genpart5) with `α = T⁻¹`, `r = 1`):
  `Work.Residues.hasResidue_Kfun_second (ℓ)(d)(hd)(z)(hne) :
  HasResidue (fun ζ => Kfun ℓ d z ζ) (T⁻¹ • z) (1/(2π))` -- equivalently
  `Work.Residues.hasResidue_Kfun_second' : HasResidue (fun ζ => Kfun ℓ d z ζ) ((-1:ℝ)+ᵥz) (1/(2π))`,
  i.e. `Res_{z = τ-1} K(τ,z) = 1/(2π)`, the second-variable pole that CKMRV's contour shift
  (Proposition 4.6, (matchF2sharp)) picks up.  Also `hasResidue_KPlus_second`,
  `hasResidue_KMinus_second` (residue `1/(2π)`) and `hasResidue_Khat_second` (residue `0`).

* **Theorem 4.9(4), the `i∞` bounds** (`Work.Residues.KPlus_isBigO_atImInfty`,
  `KMinus_isBigO_atImInfty`): for fixed `z` there are `H, C` with
  `‖K_±^{(d)}(τ,z)‖ ≤ C ‖τ‖ exp(-(2 or 4)π Im τ)` for `Im τ ≥ H` (`2` for `d = 8`, `4` for
  `d = 24`); the threshold `H` is needed because the poles of `K_±` lie on the `SL(2,ℤ)`-orbit
  of `z`, whose imaginary parts are bounded.

* **Theorem 4.9(2) at the level of the contour** (`Work.Residues.slash_kernelTransform`,
  `Work.Residues.Section5`): `Work.Residues.slash_Kfun_kernelTransform_eq_zero` (the
  `S(T-I)²`-recurrence of the kernel transform, i.e. `h5b` of
  `Work.Kernels.Section5Pack.satisfiesThm31_of_analysis`, from the pointwise kernel identity and
  the linearity of the Bochner integral only) and `Work.Residues.slash_Kfun_kernelTransform`
  (`h5b` as a function identity, modulo the Bochner integrability of the contour integrands on a
  pole-free contour).

* **The status of `h5a`** (`Work.Residues.T2op_gaussTerm`, `Work.Residues.Section5Corrected`):
  `Work.Residues.T2op_gaussTerm` computes the `(T-I)²`-defect of the Gaussian
  (`= -4 e^{πir²(τ+1)} sin²(πr²/2)`, via the elementary `Work.Residues.exp_I_sub_one_sq`), while
  `Work.Asymptotics.T2op_kernelTransform` shows that the *projective* integral
  `Work.Kernels.kernelTransform (Kfun ℓ d) · r` has vanishing `(T-I)²`-defect.  Hence
  `Work.Residues.h5a_false` proves that **`h5a` of
  `Work.Kernels.satisfiesThm31_of_analysis` is false for `K = Kfun logLambda d` as literally
  stated**: the paper's `F₂` is the analytic continuation of the integral (CKMRV Proposition
  4.6), not the integral.  The reduction interface for the repair is
  `Work.Residues.T2op_kernelTransform_add` and
  `Work.Residues.slash_Kfun_kernelTransform_add`: any correction `G` with
  `T2op G = -T2op (gaussTerm · r)` and `slash (d/2) (S(T-I)²) G = 0` restores both recurrences
  for `F₂^♯ + G`.

* **Proposition 5.1 in the contour-shift form, and the correction `G = F₂ - F₂^♯`**
  (`Work.Residues.Section5Shift`).  The residue term of the contour shift is
  `Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ` (`resCorr r τ = e^{πir²(τ-1)}`), and
  `Work.Residues.resCorr_vadd_two` identifies it *at the shifted point* with the right-hand side
  of the recurrence: `sinSqC r * resCorr r (τ+2) = -T2op (gaussTerm · r) τ`.  From this:
  * `Work.Residues.T2op_of_contourShift` : if `Ψ` is the corrected `F₂` (agrees with the
    projective integral at `τ` and `τ+1`, and with the integral *plus* the residue correction at
    the shifted point `τ+2` — the paper's `(matchF2sharp)`), then `T2op Ψ τ = -T2op (gaussTerm·r) τ`;
  * `Work.Residues.slash_of_agrees` : if `Ψ` agrees with the integral at the three contour
    points `S•τ, ST•τ, ST²•τ` (where those integrands are Bochner integrable — the paper's
    "each of the three terms can be computed using `(5.2)`"), then
    `slash (d/2) (S(T-I)²) Ψ τ = 0`.  (Proved unconditionally for any such `Ψ`.)
  Consequently the correction `G := fun σ => Ψ σ - kernelTransform (Kfun ℓ d) σ r` produced by
  the continuation satisfies exactly the two conditions the socket consumes:
  `Work.Residues.T2op_correction : T2op G = -T2op (gaussTerm · r)` and
  `Work.Residues.slash_correction : slash (d/2) (S(T-I)²) G = 0` — so
  `Work.Residues.T2op_kernelTransform_add`/`slash_Kfun_kernelTransform_add` assemble the two
  recurrences of Proposition 5.1 for `F₂^♯ + G = Ψ`.

* **Why the projective statements cannot supply `h5a`/`h5b`.**  `Work.Residues.h5a_false` and
  the analysis recorded in `Work.Residues.Section5Corrected` show that the projective contour
  integral `kernelTransform (Kfun ℓ d) · r` is *not* CKMRV's `F₂`: its `(T-I)²`-defect is `0`
  (not `-T2op (gaussTerm · r) ≠ 0`), and its `S(T-I)²`-defect is `0` only when the three contour
  points `S•τ`, `ST•τ`, `ST²•τ` are all Bochner-integrable or all non-integrable.  The latter
  "all-or-none" property is *not* automatic: it is invariant under `S` (the annihilation law
  gives `K_±(S•σ,ζ) = -j(S,σ)^{∓k}K_±(σ,ζ)` pointwise) but the clean/bad status of the
  `T`-translates can differ, the pole set of `ζ ↦ K(τ,ζ)` being `{δ•τ : φ(δ) ≠ 0}` (the paper's
  §5.3 computation, whose `δ = T⁻¹` case is
  `Work.Residues.hasResidue_Kfun_second`/`not_mdifferentiableAt_Kfun_second`).  At `τ = i`, for
  instance, `i` is clean (`φ(±I) = φ(±S) = 0`) while `1+i` and `2+i` are not
  (`φ(T) = 1`, `φ(T²) = 2`), so two of the three integrals take the junk value `0`; the
  projective identity then collapses to its single surviving term.  Consequently
  `h5a`/`h5b` must be stated for the *continued* `F₂` (the `Work.Asymptotics` propagation), and
  `Work.Residues.T2op_kernelTransform_add`/`slash_Kfun_kernelTransform_add` are the socket for
  it.

## Auxiliary modules in this directory

Besides the modules above (all of which are compiled and on this import path), the directory
contains a number of further auxiliary modules that were used while building the chapter and
are *not* imported here, because they are superseded or independent:
`Work.Residues.CuspPolyBounds`, `KMinus_axis_bound`, `LamSExpBound`, `LogLambdaExpEqConst`,
`ThetaLowerBound`, `bracket8_axis_bound`, `bracket24_axis_bound`, `bracket24_uniform`,
`imagAxis_factor_bounds`, `kpre_inv_axis_bound` (quantitative cusp/axis estimates used by the
`i∞` bounds), `Work.Residues.mapDomain_eq_zero_mem_span`, `Work.Residues.theta_E6_identity`,
and `Work.Residues.basis_quotient_IdealIp` (see the note on duplicate names below).  They all
compile (`lake build Submission.Work.Residues.<name>`).

## A note on duplicate names

`Submission/Work/Residues/basis_quotient_IdealIp.lean` is a self-contained proof of
Proposition 3.8(2) for `𝓘_+` that introduces its own copies of the transfer map
`ℂ[SL(2,ℤ)] → ℂ[Γ]` (named `toPSL`, `toGamma`, `Phi`, ...).  Those names are also used by
`Submission/Work/Residues/XiTransfer.lean` (which this `All` module does import, through
`Quotient`), so the two modules cannot be imported together.  The statement proved there is
available here as `Work.Residues.basis_quotient_IdealIp'` (equivalently `basisIp`, with
`finrank_quotient_idealIp`).
-/
import Submission.Work.Residues.center_SL2Z
import Submission.Work.Residues.idealI_direct_augIdeal
import Submission.Work.Residues.normalizedDeriv_jInvariantFun
import Submission.Work.Residues.normalizedDeriv_DeltaFun
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Residues.Basic
import Submission.Work.Residues.Poles
import Submission.Work.Residues.SimplePoleAPI
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.tendsto_slope_jInvariantFun
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KPlusClear_T
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.hasResidue_smul_SL
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Residues.ResidueOrbit
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.KernelPoleLocation
import Submission.Work.Residues.KPlus_isBigO_atImInfty
import Submission.Work.Residues.KMinus_isBigO_atImInfty
import Submission.Work.Residues.slash_kernelTransform
import Submission.Work.Residues.Section5
import Submission.Work.Residues.T2op_gaussTerm
import Submission.Work.Residues.Section5Corrected
import Submission.Work.Residues.Section5Shift
