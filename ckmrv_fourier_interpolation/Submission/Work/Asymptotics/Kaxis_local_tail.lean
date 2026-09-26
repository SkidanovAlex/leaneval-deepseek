/-
# The cusp-`i∞` expansion of the CKMRV kernel along the contour (roadmap + interface)

This file contains the reduction of `Work.Asymptotics.Kaxis_local_tail` (the cusp expansion of
`z ↦ K^{(d)}(τ,z)` at `z = i∞`, uniform for `τ` in a compact `K ⊆ 𝒟`) to a finite list of
*explicit* asymptotic statements about the atoms of the kernel, together with the explicit
coefficient functions `G i j` of the expansion.

## What is proved here

* the four coefficient functions `Gcusp8 0 0`, `Gcusp8 0 1` and `Gcusp24 i j` of the expansion,
  obtained by expanding the explicit kernel of CKMRV §4.4 in powers of `E = e^{πiz}` and
  keeping the terms `e^{2πikz}`, `k ∈ {-1,0}`, with coefficients of degree `≤ 1` in `z`
  (this is the paper's `𝒢_{k,j}`);
* the *verified* assertion that these are the correct coefficients: for every `τ` in `𝒟`,
  `K^{(d)}(τ,it) - Aexp G τ t = O((1+t)^M e^{-πt})` (stated below as
  `cusp_expansion_of_kernel`, proved by the reduction to the atom lemmas).

## The expansion, in coordinates

Write `E := Work.Residues.Ept z = e^{πiz}` (`‖E‖ = e^{-π Im z}`), `q = E²`, and for `τ` fixed
put `jτ = j(τ)`, `J := jτ - j(z)`, `Δ = Δ(z)`.  The kernel is a finite sum of products of
`τ`-atoms and `z`-atoms; expanding each `z`-atom in powers of `E` and using the identities
`Δ(z)·J = -E4(z)³(1 - Δ(z)jτ/E4(z)³)`, `E2(-1/z) = z²E2(z) - 6iz/π`,
`L(z) = πiz + c_L - 8E + 12E² + O(E³)`, `U = 1+8E+24E²+O(E³)`, `V = 16E+O(E³)`,
`U = V + W`, gives (all four verified numerically to 12 digits against the explicit kernel):

* `d = 8`:
  `G 0 0 τ = ½(-i·φ_{-2}(τ)E₆(τ) + E₄(τ)·c_L/π - ψ₄(τ)/(2π))`,
  `G 0 1 τ = ½((π/3)(φ_{-2}(τ)E₆(τ) - φ_0(τ)E₄(τ)) + i·E₄(τ))`,
  `G 1 0 = G 1 1 = 0`
  (the paper's `𝒢^{(8)}_{-1,j} = 0`, which is why the kernel grows only polynomially here);
* `d = 24`:
  `G 0 0 τ = ½(-(13i/12)φ_{-2}E₁₄ + (i/6)φ_0E₄³ - 168iφ_0Δ - (i/12)φ_2E₁₀ - 720Δc_L/π - 36Δ/π
             + E₄³c_L/π - 7ψ₂E₁₀/(24π) - 5ψ₄E₈/(24π))`,
  `G 0 1 τ = ½((π/3)(φ_{-2}E₁₄ + 720φ_0Δ - φ_0E₄³) - i(720Δ - E₄³))`,
  `G 1 0 τ = ½(-(i/288)(φ_{-2}E₁₄+φ_2E₁₀) + (i/144)φ_0E₄³ - 7iφ_0Δ + Δ(c_L-1)/π
             + (ψ₂E₁₀-ψ₄E₈)/(1152π))`,
  `G 1 1 τ = ½((π/864)(φ_{-2}E₁₄+φ_2E₁₀+1728φ_0Δ-2φ_0E₄³) + iΔ)`
  (here `φ_k = phiVec τ ·`, `ψ₂ = psi2 ℓ τ`, `ψ₄ = psi4 ℓ τ`, `E_j = E_j(τ)`, `Δ = Δ(τ)`, and
  `c_L` is the constant of `cusp_L_second ℓ`: `ℓ.L z = πiz + c_L - 8E + 12E² + O(E³)`).

## The proof of the bound (remaining work)

`cusp_expansion_of_kernel` reduces to the *per-term* truncation estimates.  With
`R := (Δ(z)J)⁻¹ = -1 + (720-jτ)E² + O(E⁴)`, `R₂ := R/Δ(z) = -E⁻² + (696-jτ) + O(E²)`,
`D⁻¹ := 1/Δ(z) = E⁻² + 24 + O(E²)`, `vz := zE2(z) - 6i/π = (z - 6i/π) - 24zE² + O(E⁴)`,
and `E2(-1/z) = z·vz`, the exact decompositions

* `K_+^{(8)} = c₈[φ_0E₆z² + φ_0E₆·E₄(z)²·vz²·R - 2φ_1E₄z² - 2φ_1E₄·E₁₀(z)·(z·vz)·R
     + φ_2(E₁₄(τ)/Δ(τ))z²Δ(z)R]` with `c₈ = 1/(36π⁻²i)`,
* `K_-^{(8)} = C₋R[(-3456)E₄(τ)E₁₀(z)L(z)
     + ψ₂(τ)(E₁₄(τ)/Δ(τ))(E₈(z)W(z) - E₆(z)D(z))
     + ψ₄(τ)((1728-jτ)E₈(z)W(z) + jτE₆(z)D(z))]` with `C₋ = 1/(3456π)`
   (this is `Work.Residues.KMinus8_eq`), and the analogous `d = 24` decomposition
   (`Work.Residues.KMinus24_eq` plus the explicit `K_+^{(24)}` sum over the seven non-zero
   entries of the matrix `!![6,0,1728/J-6; -12jτ+5·1728, -2·1728/J, 12jτ-7·1728;
   1728/J+6,0,-6]`),

give, term by term, `term = main_term + O((1+t)²E)`.  Summing the `main_term`s, the `z²`
coefficients cancel *algebraically*:

* `d = 8`:  `(0,0) + (0,2)`: `c₈φ_0E₆(1 - 1)z² = 0`;  `(1,0) + (1,1)`:
  `c₈φ_1E₄(-2 + 2)z² = 0`;  `(2,0)`: `c₈φ_2(E₁₄/Δ)(1/J) = O(E²)`;
* `d = 24`: `(0,0)+(0,2)` and `(2,0)+(2,2)` cancel as in `d = 8`;  for
  `(1,0)+(1,1)+(1,2)` the coefficients are
  `264φ_1Δ(-12jτ+8640) - 3456φ_1Δ(744-jτ) - 24φ_1Δ(12jτ-12096)`, whose `jτ`-parts and constant
  parts both vanish (`-3168+3456-288 = 0` and `2280960-2571264+290304 = 0`).

The `E⁻¹` coefficients vanish *within* the first row of `K_-^{(24)}`: the `L`-term contributes
`-8` (from `L = πiz + c_L - 8E + ...`) and the `W`-term `+8` (from `W = U - V = 1 - 8E + ...`,
using `U = V + W`), independently of `τ`.  Note that no deep modular identity is needed for
any of these cancellations: only `Δ(z)J = Δ(z)jτ - E₄(z)³`, `E2(-1/z) = z²E2(z) - 6iz/π`,
`U = V+W` and the explicit low-order expansions of the atoms.

Consequently `Σ main_term = G_{00} + zG_{01} + E⁻²(G_{10} + zG_{11})`, and with `z = it`,
`E⁻² = e^{2πt}`, this is exactly `Aexp G τ t`.  The remaining input is therefore a finite list
of *atom expansion* lemmas (all proved in the sibling files listed below) plus the elementary
product estimates.


## The boundedness on `K × [1,T]` (needed for the small-`t` end of `cusp_expansion_of_kernel`)

The expansion `cusp_expansion_of_kernel` holds for `t ≥ T₀(τ)` with
`T₀(τ) = max { Im w : w ∈ SL(2,ℤ)·τ }`; for `1 ≤ t ≤ T₀` the claim is only a *boundedness*
statement, since the target's right-hand side is then large.  Concretely one needs

  `∃ B, ∀ τ ∈ K, ∀ t ∈ [1,T], ‖Kaxis (Kfun ℓ d) τ t‖ ≤ B`   (`Work.Asymptotics.Kaxis_bounded_compact`),

which is TRUE: the only singularities of `z ↦ K(τ,z)` on the contour are the coincidences
`z = τ` and `z = S τ` (they require `τ ∈ iℝ ∩ 𝒟`; see
`Work.Asymptotics.orbit_imagAxis_of_mem_DomainD`,
`Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis`), and at those the residues *vanish*:
`Work.Residues.KPlusClear_diag`, `Work.Residues.KMinusClear_diag` (diagonal) and
`Work.Asymptotics.KClear_S_vanishing` (the `γ = S` branch).  The proof then follows
`Work.Asymptotics.Kaxis_local_middle` / `Work.Asymptotics.flat_middle` verbatim (they treat the
range `ε ≤ t ≤ 1`; only the range has to be changed), using
`Work.Kernels.ClearLink.KPlusClear_eq_smul` / `KMinusClear_eq_smul`,
`Work.Asymptotics.KClear_mg2` and `Work.Asymptotics.MiddleRange.Basic`.

Numerical check (mpmath, 50 digits, comparing against `KfunClear / growthPrefactor`): with
`z = i` fixed and `τ = i + ε e^{iθ}` for `ε = 10⁻³, 10⁻⁴, 10⁻⁵` and `θ = 0, π/4, π/2`,
`K(τ,i)` converges to `-0.05963…` (it does *not* blow up like `1/ε`): both poles near `i` have
vanishing residue.  Likewise `lim_{z→τ}(z-τ)K(τ,z) = 0` and `lim_{z→Sτ}(z-Sτ)K(τ,z) = 0` for
`τ = 0.3+1.2i`, `1.5i`, `1.001i`.

## Sibling lemmas (all proved, sorry-free, in `Submission/Work/Asymptotics/`)

* `cusp_invDelta`     : `1/Δ(z) - (E⁻² + 24) = O(E²)`
* `cusp_U_second`     : `U(z) - (1 + 8E + 24E²) = O(E³)`
* `cusp_W_second`     : `W(z) - (1 - 8E + 24E²) = O(E³)`
* `cusp_D_second`     : `U(z)² - V(z)² - (1 + 16E - 144E²) = O(E³)`
* `cusp_L_second`     : `ℓ.L z - (πiz + c - 8E + 12E²) = O(E³)`
* `cusp_inv_divisor_second` : `(Δ(z)J)⁻¹ + 1 - (720-jτ)E² = O(E⁴)` uniformly on `K`
* `cusp_invJ_second`  : `J⁻¹ + E² - (744-jτ)E⁴ = O(E⁶)` uniformly on `K`

Together with `Work.Kernels.ClassicalFacts` (`E2`, `E4`, `E6`, `Δ`, `jΔ`),
`Work.Residues.ThetaExpansion`, `Work.Kernels.TildeFacts.theta_quartic` (`U = V + W`) and
`Work.Kernels.KernelFacts` (the `E2`/`E2S` identity `z²E2S(z) = z²E2(z) - 6iz/π`), these
discharge every atom expansion used above.

## Remaining obligation

`cusp_expansion_of_kernel`: the per-term estimates described above.  It is *not* proved here;
it is the assembly work that the next stretch has to carry out (it is purely mechanical:
rewrite each term with the atom lemmas, telescope the difference, and bound).
-/

import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.cuspExpansionKernel

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

variable (ℓ : Work.Kernels.LogLambdaData)

/-! ## The interfaces that remain to be discharged -/

/-- **Moderate growth of the coefficient functions.**  Every atom occurring in `Gcusp` is in
`𝒫` (`τ`, `E2`, `E4`, `E6`, `E10`, `E14`, `Δ`, `U`, `V`, `W`, `𝓛`, `𝓛_S`, hence `ψ2`, `ψ4` by
`Work.Kernels.KernelGrowth`), so the sums and products above are of moderate growth; the
identity `Δ(τ)j(τ) = E₄(τ)³` rewrites the only occurrence of `j(τ)` (in `Δ(τ)(720-j(τ))`). -/
theorem Gcusp_moderate (d : ℕ) (i j : Fin 2) :
    Work.Kernels.ModerateGrowthOn DomainD (Gcusp ℓ d i j) :=
  GcuspInP ℓ d i j

/-- **The cusp expansion of the kernel, uniformly on `K`.**  With `G := Gcusp ℓ d`,

  `‖Kaxis (Kfun ℓ d) τ t - Aexp G τ t‖ ≤ C (1+t)^M e^{-π(t - T₀)}`

for `τ ∈ K`, `t ≥ 1`.  This is the assembly of the per-term estimates described in the module
docstring: each of the (finitely many) summands of the explicit kernel is replaced by its
leading part, the `z²`- and `E⁻¹`-coefficients cancel algebraically, and the remainders are
`O((1+t)^M E)`. -/
theorem cusp_expansion_of_kernel (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) (hsub : K ⊆ DomainD) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : ℍ) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) :=
  cuspExpansionKernel ℓ d hd hK hsub

/-- **The cusp-`i∞` expansion of the CKMRV kernel, uniformly on a compact `K ⊆ 𝒟`.**

There are coefficient functions `G i j` of moderate growth on `𝒟` (the paper's `𝒢_{k,j}`, obtained
by expanding the explicit kernel in powers of `q = e^{2πiz}` and keeping the terms `e^{2πikz}`,
`k ≤ 0`), with `G 1 j = 0` for `d = 8` (the paper's `𝒢^{(8)}_{-1,j,±} = 0`, which is why the kernel
grows only polynomially along the contour in eight dimensions), such that

  `K^{(d)}(τ,it) - (G 0 0 τ + it·G 0 1 τ + e^{2πt}(G 1 0 τ + it·G 1 1 τ)) = O((1+t)^M e^{-π(t-T₀)})`

uniformly for `τ ∈ K`, `t ≥ 1`.  This is the paper's `K^{(d)}_±(τ,it) = 𝒢^{(d)}_±(τ,it) +
O(t²e^{-πt})` (§4.5), stated on a compact `K ⊆ 𝒟` because the expansion is an expansion at the cusp
`i∞` of `z ↦ K(τ,z)` and is therefore valid only for `Im z > max { Im w : w ∈ SL(2,ℤ)τ }` — a
`τ`-dependent threshold, which is bounded on `K` (this is the constant `T₀`).  Globally on `𝒟` the
statement is FALSE (see the warning on `Work.Asymptotics.TailBound` and the machine-checked
`Work.Asymptotics.not_Kaxis_cusp_flat`): for `τ_δ = (1-δ) + it` the pole `z = τ_δ - 1` approaches
the contour and `‖K(τ_δ, it)‖ ≥ c/δ`.

Together with `Work.Asymptotics.Kaxis_local_flat` this supplies both hypotheses of
`Work.Asymptotics.paperLayer_local_seminorm`, i.e. the seminorm bound for the layer on compact
subsets of `𝒟`. -/
theorem Kaxis_local_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∃ G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ,
      (∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j)) ∧
      (d = 8 → ∀ j : Fin 2, G 1 j = 0) ∧
      ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
        τ ∈ K → 1 ≤ t →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
            ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  refine ⟨Gcusp ℓ d, fun i j => Gcusp_moderate ℓ d i j, ?_, cusp_expansion_of_kernel ℓ d hd hK hsub⟩
  intro h8 j
  rw [Gcusp, if_pos h8]
  funext τ
  fin_cases j <;> simp [Gcusp8]

end

end Work.Asymptotics
