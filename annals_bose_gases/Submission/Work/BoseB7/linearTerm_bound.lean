import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB7.bp_cauchy
import Submission.Work.BoseB7.spectLe_nOp
import Submission.Work.BoseB7.sqrt_mul_sqrt_le
import Submission.Work.BoseB7.sum_a_bound_finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.linearTerm_bound` — the linear term of FS §10

FS's `thm:Control3Q` controls, among other things, the *linear* term
`ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s† + ã_s) ds` of `eq:Q3Cancels`, and the
`EstQ3four` estimate (`eq:EstimateQ3Tilde4`) is proved by estimating precisely
this kind of expression.  At the level of the `B7` Fock interface the linear
term is an operator of the form

  `L = Σ_{s ∈ excited Mode} c_s (a_s† + a_s)`

(a sum of creation plus annihilation operators of the excited modes, with real
coefficients `c_s`), and the estimate needed for the whole chapter is: **on FS's
spectral window `⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²` the quadratic form of `L` is bounded by**

  `|⟨Φ, LΦ⟩| ≤ 2 √𝓜 (Σ_s |c_s|) ‖Φ‖²`.

## The argument

Write `A = Σ_s c_s a_s` and `A† = Σ_s c_s a_s†` (its adjoint, the `c_s` being
real), so that `L = A† + A`.  Three elementary facts give the estimate.

1. *`L` is `2A` in the form.*  By adjointness of `a_s†` and symmetry of the Fock
   form, `⟨Φ, A†Φ⟩ = ⟨Φ, AΦ⟩ = ⟨AΦ, Φ⟩`, hence
   `⟨Φ, LΦ⟩ = 2⟨AΦ, Φ⟩` (`bp_linearOp_eq`).

2. *Cauchy–Schwarz and the weighted-sum bound.*  `bp_cauchy_abs` gives
   `|⟨AΦ, Φ⟩| ≤ √⟨AΦ, AΦ⟩ √⟨Φ, Φ⟩`, and the weighted Cauchy–Schwarz of
   `Work.BoseB7.sum_a_bound_finset` (applied to the finset `excited Mode`) gives

     `⟨AΦ, AΦ⟩ ≤ (Σ_s |c_s|)(Σ_s |c_s| ⟨a_sΦ, a_sΦ⟩)`.

3. *The spectral window, mode by mode.*  `Work.BoseB7.spectLe_nOp` gives
   `⟨a_sΦ, a_sΦ⟩ = ⟨Φ, a_s†a_sΦ⟩ ≤ 𝓜‖Φ‖²` for every excited mode `s`
   (`s ≠ 0`), so the second factor is at most `(Σ_s |c_s|)·𝓜‖Φ‖²`.  Hence

     `⟨AΦ, AΦ⟩ ≤ (Σ_s |c_s|)² 𝓜 ‖Φ‖²`.

The final arithmetic step is `Work.BoseB7.sqrt_mul_sqrt_le`: from
`Q ≤ S²(𝓜W)` with `S, W ≥ 0` and `𝓜W ≥ 0` (the last is `0 ≤ ⟨Φ, n₊Φ⟩ ≤ 𝓜W`,
i.e. exactly `hspec`) it produces `√Q √W ≤ S √𝓜 W`, which multiplied by `2` is
the claim.

No hypothesis beyond `hspec` is used: in particular `𝓜 ≥ 0` is *derived* (from
`0 ≤ ⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²`), and the degenerate case `‖Φ‖ = 0` (i.e. `Φ = 0`) is
absorbed by the `√W = 0` branch of `sqrt_mul_sqrt_le`.
-/

namespace Work.BoseB7

/-- The linear term `L = Σ_s c_s (a_s† + a_s)` is twice the annihilation part in
the Fock form: `⟨Φ, LΦ⟩ = 2⟨(Σ_s c_s a_s)Φ, Φ⟩`.

This is adjointness of `a_s†` (`FockData.aDag_adjoint`) plus symmetry of `bp`:
`⟨Φ, A†Φ⟩ = ⟨AΦ, Φ⟩ = ⟨Φ, AΦ⟩`, so the creation and annihilation halves
contribute equally. -/
lemma bp_linearOp_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (c : Mode → ℝ) (Φ : F.H) :
    F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • (F.aDag s + F.a s)) Φ) Φ
      = 2 * F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ) Φ := by
  have hsplit : (∑ s ∈ Work.BoseB7.excited Mode, (c s) • (F.aDag s + F.a s))
      = (∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.aDag s)
        + (∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => smul_add _ _ _)
  have hadj : F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.aDag s) Φ) Φ
      = F.bp Φ ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      F.aDag_adjoint]
  rw [hsplit, LinearMap.add_apply, map_add, LinearMap.add_apply, hadj,
    F.bp_symm Φ ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)]
  ring

/-- **The linear term of FS §10 is controlled by the spectral window.**  For a
state `Φ` with `⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²` and real coefficients `c` on the excited
modes,

  `|⟨Φ, Σ_s c_s (a_s† + a_s) Φ⟩| ≤ 2 √𝓜 (Σ_s |c_s|) ‖Φ‖²`.

The proof is: reduce the creation half to the annihilation half
(`bp_linearOp_eq`, since `a_s†` is the adjoint of `a_s`), apply
Cauchy–Schwarz (`bp_cauchy_abs`), bound `⟨AΦ, AΦ⟩` by the weighted sum of the
individual mode energies (`sum_a_bound_finset`, the `excited Mode` version of
`sum_a_bound`), bound each mode energy by `𝓜‖Φ‖²` (`spectLe_nOp`), and take
square roots (`sqrt_mul_sqrt_le`). -/
theorem linearTerm_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (c : Mode → ℝ) {Φ : F.H}
    (hspec : F.SpectLe E.bigM Φ) :
    |F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • (F.aDag s + F.a s)) Φ) Φ| ≤
      2 * Real.sqrt E.bigM * (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * F.normSq Φ := by
  -- Step 1: the linear term is twice its annihilation part in the Fock form.
  have hbp := bp_linearOp_eq F c Φ
  -- Step 2: mode-by-mode, `⟨a_sΦ, a_sΦ⟩ ≤ 𝓜‖Φ‖²` (the spectral window).
  have hterm : ∀ s ∈ Work.BoseB7.excited Mode, F.bp (F.a s Φ) (F.a s Φ)
      ≤ E.bigM * F.bp Φ Φ := by
    intro s hs
    have hsne : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have h := Work.BoseB7.spectLe_nOp F E hspec s hsne
    simp only [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint, FockData.normSq] at h
    exact h
  -- Step 3: the weighted-sum bound on the annihilation part.
  have hsum : F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
        ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
      ≤ (∑ s ∈ Work.BoseB7.excited Mode, |c s|)
        * (∑ s ∈ Work.BoseB7.excited Mode, |c s| * F.bp (F.a s Φ) (F.a s Φ)) :=
    Work.BoseB7.sum_a_bound_finset F c (Work.BoseB7.excited Mode) Φ
  have hsum2 : (∑ s ∈ Work.BoseB7.excited Mode, |c s| * F.bp (F.a s Φ) (F.a s Φ))
      ≤ (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * (E.bigM * F.bp Φ Φ) := by
    calc (∑ s ∈ Work.BoseB7.excited Mode, |c s| * F.bp (F.a s Φ) (F.a s Φ))
        ≤ ∑ s ∈ Work.BoseB7.excited Mode, |c s| * (E.bigM * F.bp Φ Φ) :=
          Finset.sum_le_sum
            (fun s hs => mul_le_mul_of_nonneg_left (hterm s hs) (abs_nonneg _))
      _ = (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * (E.bigM * F.bp Φ Φ) := by
          rw [Finset.sum_mul]
  have hSnn : (0 : ℝ) ≤ ∑ s ∈ Work.BoseB7.excited Mode, |c s| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hQbound : F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
        ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
      ≤ (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * (∑ s ∈ Work.BoseB7.excited Mode, |c s|)
        * (E.bigM * F.bp Φ Φ) := by
    calc F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
          ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
        ≤ (∑ s ∈ Work.BoseB7.excited Mode, |c s|)
            * (∑ s ∈ Work.BoseB7.excited Mode, |c s| * F.bp (F.a s Φ) (F.a s Φ)) := hsum
      _ ≤ (∑ s ∈ Work.BoseB7.excited Mode, |c s|)
            * ((∑ s ∈ Work.BoseB7.excited Mode, |c s|) * (E.bigM * F.bp Φ Φ)) :=
          mul_le_mul_of_nonneg_left hsum2 hSnn
      _ = (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * (∑ s ∈ Work.BoseB7.excited Mode, |c s|)
            * (E.bigM * F.bp Φ Φ) := by ring
  -- Step 4: `𝓜‖Φ‖² ≥ 0` from the spectral window (`0 ≤ ⟨Φ, n₊Φ⟩ ≤ 𝓜‖Φ‖²`).
  have hMW : 0 ≤ E.bigM * F.bp Φ Φ := by
    have h1 : 0 ≤ F.bp (F.nPlus Φ) Φ := by
      rw [Work.BoseB7.bp_nPlus_eq_sum]
      exact Finset.sum_nonneg (fun j _ => Work.BoseB7.bp_nOp_nonneg F j Φ)
    exact le_trans h1 hspec
  -- Step 5: Cauchy–Schwarz, then the square-root arithmetic.
  have hcs : |F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ) Φ|
      ≤ Real.sqrt (F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ)
            ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ))
        * Real.sqrt (F.bp Φ Φ) :=
    Work.BoseB7.bp_cauchy_abs F _ Φ
  have hkey := Work.BoseB7.sqrt_mul_sqrt_le hSnn (F.bp_nonneg Φ) hMW hQbound
  calc |F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • (F.aDag s + F.a s)) Φ) Φ|
      = 2 * |F.bp ((∑ s ∈ Work.BoseB7.excited Mode, (c s) • F.a s) Φ) Φ| := by
        rw [hbp, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ 2 * ((∑ s ∈ Work.BoseB7.excited Mode, |c s|) * Real.sqrt E.bigM * F.bp Φ Φ) :=
        mul_le_mul_of_nonneg_left (le_trans hcs hkey) (by norm_num)
    _ = 2 * Real.sqrt E.bigM * (∑ s ∈ Work.BoseB7.excited Mode, |c s|) * F.normSq Φ := by
        rw [FockData.normSq]; ring

end Work.BoseB7
