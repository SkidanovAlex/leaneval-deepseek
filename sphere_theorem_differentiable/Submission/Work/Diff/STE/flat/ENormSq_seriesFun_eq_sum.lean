import Mathlib
import Submission.Work.Diff.STE.ENormSq_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ENormSq_seriesFun_eq_sum`: the exact energy of a finitely supported Fourier series

For a coefficient family `c : (ι → ℤ) → ℂ` that is **supported on a finite set** `s`
(`c m = 0` for `m ∉ s`), the Fourier series `seriesFun c = Σ_k c k · exp(2πi k·x)` is a
trigonometric polynomial, and the `Hᵏ` energy

  `ENormSq j (seriesFun c) = Σ_{l : Fin j → ι} ∫_{unitCube} ‖∂^l (seriesFun c)‖²`

is **exactly** the finite double sum of the (differentiated) coefficients over the support:

  `ENormSq j (seriesFun c) = Σ_{l : Fin j → ι} Σ_{m ∈ s} ‖dmulV (List.ofFn l) c m‖²`.

This is Parseval's identity (`ens_integral_normSq_seriesFun`) combined with term-by-term
differentiation (`pdList_seriesFun`) and the reduction of the lattice sum to the finite support
(`tsum_eq_sum`).  It is the "no loss" companion of the inequality `ENormSq_seriesFun_le` used to
identify the physical energy of a Galerkin/trigonometric-polynomial approximation with the
coefficient energy of the truncated family.
-/

noncomputable section

namespace Work.Diff.STE.flat

theorem ENormSq_seriesFun_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) (c : (ι → ℤ) → ℂ) (s : Finset (ι → ℤ)) (hc : ∀ m : ι → ℤ, m ∉ s → c m = 0) :
    Work.Diff.STE.ENormSq j (Work.Diff.STE.seriesFun c)
      = ∑ l : Fin j → ι, ∑ m ∈ s, ‖Work.Diff.STE.dmulV (List.ofFn l) c m‖ ^ 2 := by
  -- A finitely supported family has summable weighted `ℓ¹`-norms, at every order.
  have hsum_c : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖) :=
    fun N => summable_of_ne_finset_zero (fun b hb => by rw [hc b hb]; simp)
  rw [Work.Diff.STE.ENormSq]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  -- Term by term differentiation: the `l`-th derivative is the series of `dmulV l c`.
  have hpd : Work.Diff.STE.pdVec j l (Work.Diff.STE.seriesFun c)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) c) :=
    funext (Work.Diff.STE.pdList_seriesFun (List.ofFn l) c hsum_c)
  rw [hpd,
    Work.Diff.STE.ens_integral_normSq_seriesFun _
      (summable_of_ne_finset_zero (fun b hb => by
        rw [Work.Diff.STE.dmulV, hc b hb, mul_zero]; simp))]
  -- The differentiated family is still supported on `s`, so the lattice sum is a finite sum.
  exact tsum_eq_sum (fun b hb => by
    rw [Work.Diff.STE.dmulV, hc b hb, mul_zero]; simp)

end Work.Diff.STE.flat
