import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.realPsiComplexZeroFree
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.noCompletionOfPsiTrivial
import Submission.Work.FIArea6Hecke.R.chiPrimeSelfDual
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.lvalSameSeries
import Submission.Work.FIArea6Hecke.R.chiPrimeAgree

/-!
# `Submission.Work.FIArea6Hecke.R.zfrOffAxisSdSelfDual`

**The self-dual case of *FI* (16.20)**: for a self-dual strict character pair
(`Work.FIArea6Hecke.R.SelfDual`: `psi_{chi,m} = ±1` on the primary units modulo `4d`) the Hecke
`L`-function has no zero with `im s ≠ 0` in the de la Vallée Poussin region
`re s > 1 - c/log(4d + |m| + |im s|)`.

(`SelfDual` forces `m = 0`; the *only* exceptional zeros of such an `L`-function are real, so the
claim needs no real-axis exception because it is restricted to `im s ≠ 0`.)

The reduction is the same as in `Work.FIArea6Hecke.R.zfrRealAxisSdClean`: the self-dual pair has
real Hecke eigenvalues, hence the same `L`-series as the real character `chiPrime d chi`
(`Work.FIArea6Hecke.R.chiPrimeSelfDual`), the `L`-values of the two completions agree on `re s > 0`
(`Work.FIArea6Hecke.R.lval_eq_of_same_series`), and the proved complex zero-free region for real
characters `Work.FIArea6Hecke.R.realPsiComplexZeroFree` applies to the normalised pair.
-/
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric
open scoped Topology BigOperators

noncomputable section

/-- **The self-dual case of (16.20).**  There is `c > 0` such that for every self-dual strict
character pair `(chi, m)`, every entire completion `Lam` of `Λ(s,ψ)` and every `s` with
`im s ≠ 0` and `1 - c/log(4d + |m| + |im s|) < re s ≤ 2`, the value `Lval d m Lam s` is nonzero. -/
theorem zfrOffAxisSdSelfDual :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        Work.FIArea6Hecke.R.SelfDual d chi m →
        ∀ s : ℂ,
          1 - c / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re → s.re ≤ 2 →
          s.im ≠ 0 → Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  obtain ⟨c0, hc0pos, hreal⟩ := Work.FIArea6Hecke.R.realPsiComplexZeroFree
  refine ⟨min c0 1, lt_min hc0pos one_pos, ?_⟩
  intro d chi m Lam hd hchi hAn hagr hsd s hreg hsle2 hsim
  obtain ⟨hchi', hst, hlam⟩ := Work.FIArea6Hecke.R.chiPrimeSelfDual hd hchi hsd
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiPrime d chi) 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi m := by
    unfold Work.FIArea5.S16Hecke.heckeLSeries
    exact funext (fun s => LSeries_congr (fun {n} _ => hlam n) s)
  have hm0 : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_selfDual hd hchi hsd
  have hpsi : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.R.chiPrime d chi) 0 z
        = Work.FIArea5.S16Hecke.psi chi m z := by
    intro z hzp hzu
    have hz1 : Work.FIArea6Hecke.R.chiPrime d chi z = chi z :=
      Work.FIArea6Hecke.R.chiPrime_eq_chi_of_primary hzp hzu
    rw [hm0]
    simp [Work.FIArea5.S16Hecke.psi, hz1]
  have hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.R.chiPrime d chi) 0 z ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact Work.FIArea6Hecke.R.noCompletionOfPsiTrivial d hd chi m Lam ⟨hd, hchi, hAn, hagr⟩
      (fun z hzp hzu => by rw [← hpsi z hzp hzu]; exact hcon z hzp hzu)
  obtain ⟨Lam', hAn', hagr'⟩ := heckeCompletionImprimitive d (Work.FIArea6Hecke.R.chiPrime d chi)
    0 hd hchi' hne
  have hagr'' : ∀ s : ℂ, 1 < s.re → Lam' s =
      Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiPrime d chi) 0 s := by
    intro s hs
    refine hagr' s ?_
    simpa using hs
  have hEq := lval_eq_of_same_series (d := d) (chi := chi)
    (chi' := Work.FIArea6Hecke.R.chiPrime d chi) (m := m) hd hAn hAn' hagr hagr'' hL
  have hlog1 : 1 ≤ Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := by
    have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) + |(m : ℝ)| + |s.im| := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have h1 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
      linarith
    have hlog4 : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith [Real.exp_one_lt_three]
    exact le_trans hlog4.le (Real.log_le_log (by norm_num) h4)
  have hlogpos : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) := lt_of_lt_of_le one_pos hlog1
  have hminpos : 0 < min c0 1 := lt_min hc0pos one_pos
  have h1 : min c0 1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) ≤ 1 := by
    rw [div_le_one hlogpos]
    exact le_trans (min_le_right _ _) hlog1
  have hsre : 0 < s.re := by linarith
  intro hzero
  have h0 : Work.FIArea6Hecke.Lval d 0 Lam' s = 0 := by
    rw [← hEq s hsre]; exact hzero
  refine hreal d (Work.FIArea6Hecke.R.chiPrime d chi) Lam' hd hchi' ?_ hAn' ?_ s hsim
    ?_ hsle2 h0
  · intro z; exact (hst z).symm
  · intro t ht
    refine hagr' t ?_
    simpa using ht
  · rw [hm0] at hreg
    simp only [Int.cast_zero, abs_zero, add_zero] at hreg
    have hlogpos' : 0 < Real.log (4 * (d : ℝ) + |s.im|) := by
      apply Real.log_pos
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have h : (0 : ℝ) ≤ |s.im| := abs_nonneg _
      nlinarith
    have h2 : min c0 1 / Real.log (4 * (d : ℝ) + |s.im|)
        ≤ c0 / Real.log (4 * (d : ℝ) + |s.im|) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hlogpos'.le
    linarith

end

end Work.FIArea6Hecke.R
