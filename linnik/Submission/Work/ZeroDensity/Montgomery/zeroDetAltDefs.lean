import Mathlib
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Work.LinnikAreas.Density4.rect_edge_tendsto_zero

/-!
# `Work.ZeroDensity.Montgomery.zeroDetAltDefs`

Vocabulary for Montgomery's zero-detecting alternatives
(`Work.ZeroDensity.Montgomery.zeroDetectorAlternatives`).

* `mCoef X n` is the truncated Möbius convolution coefficient
  `m_n = Σ_{d | n, d ≤ X} μ(d)` of the statement;
* `MX χ X s` is the truncated Möbius Dirichlet polynomial `M_X(s,χ) = Σ_{n ≤ ⌊X⌋₊} μ(n)χ(n)n^{-s}`;
* `PhiNaive ρ χ X Y w = L(ρ+w,χ)·M_X(ρ+w,χ)·Γ(w)·Y^w` is the (naive) integrand of the
  contour integral of the statement, on the line `Re w = 1/2 - Re ρ`;
* `Phi ρ χ X Y w = Γ(w+1)·dslope(L(ρ+·)) 0 w·M_X(ρ+w)·Y^w` is its regularisation at the
  removable singularity `w = 0` (the pole of `Γ` is cancelled by the zero of `L` at `ρ`);
  the two agree for `w ≠ 0`.
-/

open scoped Classical BigOperators

namespace Work.ZeroDensity.Montgomery

open DirichletCharacter Complex

/-- The truncated Möbius convolution coefficient `m_n = Σ_{d | n, d ≤ X} μ(d)`. -/
noncomputable def mCoef (X : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X), (ArithmeticFunction.moebius d : ℂ)

/-- The truncated Möbius Dirichlet polynomial `M_X(s,χ) = Σ_{n ≤ ⌊X⌋₊} μ(n)χ(n)n^{-s}`. -/
noncomputable def MX {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (ArithmeticFunction.moebius n : ℂ) * χ (n : ZMod q) * (n : ℂ) ^ (-s)

/-- The naive integrand `L(ρ+w,χ)·M_X(ρ+w,χ)·Γ(w)·Y^w` of Montgomery's contour integral. -/
noncomputable def PhiNaive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (ρ + w) * MX χ X (ρ + w) * Complex.Gamma w * (Y : ℂ) ^ w

/-- The regularised integrand, entire in `w`:
`Γ(w+1) · (L(ρ+w,χ) - L(ρ,χ))/w · M_X(ρ+w,χ) · Y^w`.  For `w ≠ 0` and `L(ρ,χ) = 0` it
agrees with `PhiNaive`. -/
noncomputable def Phi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 w
    * MX χ X (ρ + w) * (Y : ℂ) ^ w

end Work.ZeroDensity.Montgomery
