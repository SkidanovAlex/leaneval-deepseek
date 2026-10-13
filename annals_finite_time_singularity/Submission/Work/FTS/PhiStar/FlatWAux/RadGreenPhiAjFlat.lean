import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenDivFlatU
import Submission.Work.FTS.PhiStar.FlatWAux.PhiAjFlatDecayU
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat`

The two α-uniform flat `z`-derivative estimates for the divided radial Green function
`(z+1)/z · radGreen α m c` at the two sources that occur in the `FlatW_psiSeries` route:

* `c = φ = phiA α = phiAj 1 α` (the source of the mode expansion of `RemSource α ψ`);
* `c = 𝒜^J φ = Ajit α J (phiA α) = phiAj (J+1) α` (the remainder term of the `1/λ_m`-expansion).

Both are immediate instances of `RadGreenDivFlatU`, whose only inputs are the smoothness of `c`
on `(0,∞)` and the two-sided flat/decay bounds `|∂^k c| ≤ A/(1+t^{k+1})`,
`|∂^k (c/t)| ≤ A/(1+t^{k+2})` for `k ≤ 14`.  Those are exactly what `PhiAjFlatDecayU` provides
(for the single *α-free* constant `A`, in the range `j ≤ 9`), and `phiAj 1 α = phiA α` while
`phiAj (J+1) α = phiAj 9 α`.  The smoothness input `ContDiffOn ℝ 14` for the `𝒜`-iterates is
proved below by induction on the number of iterations.
-/

/-- **`𝒜^j φ` is `C^∞` at every `z > 0`.**  Here `𝒜 a = αz²a'' + (5+α)za'` is the radial
operator of the `Φ_*` decomposition.  Induction on `j`: the case `j = 0` is the explicit rational
function `φ` (`contDiffAt_phiA_of` for `j = 1`), and the step is a sum of products of the smooth
`z²`, `z` with the first and second iterated derivatives of a `C^∞` function. -/
theorem contDiffAt_Ajit_phiA (α : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ ∞ (Ajit α j (Work.FTS.VocabO.phiA α)) z := by
  induction j with
  | zero => simpa only [Ajit_zero] using Work.FTS.PhiStar.contDiffAt_phiA α hz
  | succ j ih =>
      rw [Ajit_succ]
      have hd1 : ContDiffAt ℝ ∞ (deriv (Ajit α j (Work.FTS.VocabO.phiA α))) z :=
        Work.FTS.PhiStar.contDiffAt_infty_deriv ih
      have hd2 : ContDiffAt ℝ ∞ (iteratedDeriv 2 (Ajit α j (Work.FTS.VocabO.phiA α))) z :=
        Work.FTS.PhiStar.contDiffAt_infty_iteratedDeriv 2 ih
      exact (((contDiffAt_const (c := α)).mul (contDiffAt_id.pow 2)).mul hd2).add
        (((contDiffAt_const (c := (5 + α))).mul contDiffAt_id).mul hd1)

/-- The `ContDiffOn` form of `contDiffAt_Ajit_phiA`, at any finite order. -/
theorem contDiffOn_Ajit_phiA (α : ℝ) (j : ℕ) (n : ℕ) :
    ContDiffOn ℝ n (Ajit α j (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
  fun z hz => ((contDiffAt_Ajit_phiA α j hz).of_le
    (by simp : ((n : ℕ∞ω)) ≤ ∞)).contDiffWithinAt

theorem RadGreenPhiAjFlat : ∃ C : ℝ, 0 < C ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.VocabO.phiA α) z') z|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 / 5 → ∀ (m : ℕ), 1 ≤ m →
      ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k
        (fun z' => (z' + 1) / z' * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) z') z|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := RadGreenDivFlatU
  obtain ⟨A, hApos, hA⟩ := PhiAjFlatDecayU
  refine ⟨C₀ * A, mul_pos hC₀pos hApos, ?_, ?_⟩
  · -- the source `φ = phiA α = phiAj 1 α`
    intro α hα hα5 m hm k hk z hz
    have hsmooth : ContDiffOn ℝ 14 (Work.FTS.VocabO.phiA α) (Set.Ioi 0) :=
      fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α 14 hz).contDiffWithinAt
    have hdata := hA α hα hα5 1 (by norm_num)
    exact hC₀ α hα hα5 m hm (Work.FTS.VocabO.phiA α) A (le_of_lt hApos) hsmooth
      hdata.1 hdata.2 k hk z hz
  · -- the remainder source `𝒜^J φ = phiAj (J+1) α = phiAj 9 α`
    intro α hα hα5 m hm k hk z hz
    have hAj : Ajit α J (Work.FTS.VocabO.phiA α) = Work.FTS.PhiStar.phiAj (J + 1) α :=
      Ajit_phiA α J
    have hsmooth : ContDiffOn ℝ 14 (Ajit α J (Work.FTS.VocabO.phiA α)) (Set.Ioi 0) :=
      contDiffOn_Ajit_phiA α J 14
    have hdata := hA α hα hα5 (J + 1) (by norm_num [J])
    have hb1 : ∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (Ajit α J (Work.FTS.VocabO.phiA α)) t|
          ≤ A / (1 + t ^ (k + 1)) := by
      intro k hk t ht
      rw [hAj]
      exact hdata.1 k hk t ht
    have hb2 : ∀ k : ℕ, k ≤ 14 → ∀ t : ℝ, 0 < t →
        |iteratedDeriv k (fun t' => Ajit α J (Work.FTS.VocabO.phiA α) t' / t') t|
          ≤ A / (1 + t ^ (k + 2)) := by
      intro k hk t ht
      rw [hAj]
      exact hdata.2 k hk t ht
    exact hC₀ α hα hα5 m hm (Ajit α J (Work.FTS.VocabO.phiA α)) A (le_of_lt hApos)
      hsmooth hb1 hb2 k hk z hz

end Work.FTS.PhiStar.FlatWAux
