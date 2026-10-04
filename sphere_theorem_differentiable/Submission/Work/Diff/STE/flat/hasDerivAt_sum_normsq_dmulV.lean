import Mathlib
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.hasDerivAt_normsq_of_hasDerivAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability of the truncated `H^j` energy in the coefficients

`dmulV l c` is the coefficient family of the iterated derivative `pdList l` (see
`ENormSq_seriesFun_le`): it multiplies the `m`-th Fourier coefficient by the *frequency-only*
factor `vCoeff l m = ∏_{i ∈ l} (2π i m_i)`,

  `dmulV l c m = vCoeff l m * c m`.

Hence if every coefficient family `σ ↦ c σ m` (`m ∈ s`) is differentiable at `t` with derivative
`d m`, then so is the (truncated) Sobolev square
`σ ↦ ∑_{l : Fin j → ι} ∑_{m ∈ s} ‖dmulV (List.ofFn l) (c σ) m‖ ^ 2`,
with the derivative obtained by the product rule `(‖z‖²)' = 2 Re(z' · conj z)` applied termwise
(`hasDerivAt_normsq_of_hasDerivAt`).  This is the coefficient-side differentiability step feeding
the energy estimates of the short-time-existence layer.
-/

noncomputable section

namespace Work.Diff.STE.flat

/-- The frequency-only part of the Fourier multiplier `dmulV l`: the product `∏_{i ∈ l} 2π i m_i`
(so that `dmulV l c m = vCoeff l m * c m`). -/
def vCoeff {ι : Type*} (l : List ι) (m : ι → ℤ) : ℂ :=
  (l.map (fun i => (2 * Real.pi * Complex.I * (m i : ℂ)))).prod

/-- The defining factorisation of the iterated Fourier multiplier. -/
lemma dmulV_eq_vCoeff_mul {ι : Type*} (l : List ι) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    Work.Diff.STE.dmulV l c m = vCoeff l m * c m := rfl

/-- Termwise derivative of `σ ↦ ‖dmulV l (c σ) m‖ ^ 2` for a single frequency `m`. -/
lemma hasDerivAt_normsq_dmulV_list {ι : Type*} (l : List ι) (c : ℝ → (ι → ℤ) → ℂ)
    (d : (ι → ℤ) → ℂ) (t : ℝ) (m : ι → ℤ)
    (hm : HasDerivAt (fun σ : ℝ => c σ m) (d m) t) :
    HasDerivAt (fun σ : ℝ => ‖Work.Diff.STE.dmulV l (c σ) m‖ ^ 2)
      (2 * (Work.Diff.STE.dmulV l d m * star (Work.Diff.STE.dmulV l (c t) m)).re) t := by
  -- `dmulV l · m` is multiplication by the constant `vCoeff l m`, so `c ↦ dmulV l (c ·) m` is
  -- `ℝ`-linear and the chain rule is just `HasDerivAt.const_mul`.
  have h : HasDerivAt (fun σ : ℝ => Work.Diff.STE.dmulV l (c σ) m)
      (Work.Diff.STE.dmulV l d m) t := by
    simpa only [dmulV_eq_vCoeff_mul] using hm.const_mul (vCoeff l m)
  simpa only using Work.Diff.STE.hasDerivAt_normsq_of_hasDerivAt h

/-- Summing the previous lemma over a finite set of frequencies.  (The derivative of a finite sum
of functions is the finite sum of function-valued summands, so the two sides are reconciled by
`Finset.sum_apply`.) -/
lemma hasDerivAt_sum_normsq_dmulV_list {ι : Type*} (l : List ι) (c : ℝ → (ι → ℤ) → ℂ)
    (d : (ι → ℤ) → ℂ) (t : ℝ) (s : Finset (ι → ℤ))
    (hc : ∀ m ∈ s, HasDerivAt (fun σ : ℝ => c σ m) (d m) t) :
    HasDerivAt (fun σ : ℝ => ∑ m ∈ s, ‖Work.Diff.STE.dmulV l (c σ) m‖ ^ 2)
      (∑ m ∈ s, 2 * (Work.Diff.STE.dmulV l d m * star (Work.Diff.STE.dmulV l (c t) m)).re) t := by
  convert HasDerivAt.sum (fun m hm => hasDerivAt_normsq_dmulV_list l c d t m (hc m hm)) using 1
  ext σ
  simp only [Finset.sum_apply]

theorem hasDerivAt_sum_normsq_dmulV {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) (c : ℝ → (ι → ℤ) → ℂ) (d : (ι → ℤ) → ℂ) (t : ℝ) (s : Finset (ι → ℤ))
    (hc : ∀ m ∈ s, HasDerivAt (fun σ : ℝ => c σ m) (d m) t) :
    HasDerivAt (fun σ : ℝ => ∑ l : Fin j → ι, ∑ m ∈ s,
        ‖Work.Diff.STE.dmulV (List.ofFn l) (c σ) m‖ ^ 2)
      (∑ l : Fin j → ι, ∑ m ∈ s, 2 * (Work.Diff.STE.dmulV (List.ofFn l) d m
        * star (Work.Diff.STE.dmulV (List.ofFn l) (c t) m)).re) t := by
  convert HasDerivAt.sum (fun l _ => hasDerivAt_sum_normsq_dmulV_list (List.ofFn l) c d t s hc)
    using 1
  ext σ
  simp only [Finset.sum_apply]

end Work.Diff.STE.flat
