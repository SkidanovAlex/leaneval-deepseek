import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeZFRrealAxisClean
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.noCompletionOfPsiTrivial
import Submission.Work.FIArea6Hecke.R.chiPrimeSelfDual
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.lvalSameSeries
import Submission.Work.FIArea6Hecke.R.chiPrimeAgree

/-!
# `Submission.Work.FIArea6Hecke.R.zfrRealAxisSdClean`

**Lemma 16.1 (Landau–Siegel) on the real axis for self-dual pairs**, i.e. the statement
`Work.FIArea6Hecke.R.ZFRrealAxisSd ε`, deduced from the *proved* Siegel input for genuinely real
characters, `Work.FIArea6Hecke.R.heckeZFRrealAxisClean ε`.

A self-dual pair `(chi, m)` (`Work.FIArea6Hecke.R.SelfDual`: `psi_{chi,m} = ±1` on the primary units
modulo `4d`) has real Hecke eigenvalues, so it has the same `L`-series as a *real-valued* strict
character: the normalised character `chiPrime d chi z = chi (primAssoc z)`
(`Work.FIArea6Hecke.R.chiPrimeSelfDual`).  Given an entire completion `Λ` of `(chi, m)` we

* transport the `L`-value across the two completions, `Lval d m Λ = Lval d 0 Λ'` on `re s > 0`
  (`Work.FIArea6Hecke.R.lval_eq_of_same_series`, the identity theorem on a half-plane), and
* build an entire completion `Λ'` of the real pair `(chiPrime d chi, 0)` by
  `Work.FIArea6Hecke.R.heckeCompletionImprimitive` — its non-triviality hypothesis is forced, since
  `chiPrime d chi` agrees with `psi_{chi,m}` on the primary units (`chiPrime_eq_psi_of_primary`,
  after `SelfDual` forces `m = 0`) and a completion with `psi ≡ 1` on the primary units cannot exist
  (`Work.FIArea6Hecke.R.noCompletionOfPsiTrivial`).

Applying `heckeZFRrealAxisClean` to `(chiPrime d chi, 0, Λ')` then gives the claim.
-/
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric
open scoped Topology BigOperators

noncomputable section

/-- **Lemma 16.1 (Landau–Siegel) for self-dual pairs** — the statement `ZFRrealAxisSd ε`, proved
from the real-character version `heckeZFRrealAxisClean ε`. -/
theorem zfrRealAxisSdClean (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.R.ZFRrealAxisSd ε := by
  obtain ⟨c0, hc0pos, hclean⟩ := heckeZFRrealAxisClean ε hε hε4
  refine ⟨min c0 1, lt_min hc0pos one_pos, ?_⟩
  intro d chi m Lam hd hchi hAn hagr hsd s hsim hreg hsle2
  obtain ⟨hchi', hreal, hlam⟩ := Work.FIArea6Hecke.R.chiPrimeSelfDual hd hchi hsd
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiPrime d chi) 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi m := by
    unfold Work.FIArea5.S16Hecke.heckeLSeries
    exact funext (fun s => LSeries_congr (fun {n} _ => hlam n) s)
  -- the completions agree on the `L`-series, and `chiPrime` agrees with `psi` on the primary units
  have hm0 : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_selfDual hd hchi hsd
  have hpsi : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.R.chiPrime d chi) 0 z
        = Work.FIArea5.S16Hecke.psi chi m z := by
    intro z hzp hzu
    have hz1 : Work.FIArea6Hecke.R.chiPrime d chi z = chi z :=
      chiPrime_eq_chi_of_primary hzp hzu
    rw [hm0]
    simp [Work.FIArea5.S16Hecke.psi, hz1]
  -- non-triviality of `chiPrime d chi` on the primary units (forced by the existence of `Lam`)
  have hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.R.chiPrime d chi) 0 z ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact Work.FIArea6Hecke.R.noCompletionOfPsiTrivial d hd chi m Lam
      ⟨hd, hchi, hAn, hagr⟩
      (fun z hzp hzu => by rw [← hpsi z hzp hzu]; exact hcon z hzp hzu)
  obtain ⟨Lam', hAn', hagr'⟩ := heckeCompletionImprimitive d (Work.FIArea6Hecke.R.chiPrime d chi)
    0 hd hchi' hne
  have hagr'' : ∀ s : ℂ, 1 < s.re → Lam' s =
      Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiPrime d chi) 0 s := by
    intro s hs
    refine hagr' s ?_
    simpa using hs
  -- the transported identity of `Lval`s
  have hEq := lval_eq_of_same_series (d := d) (chi := chi)
    (chi' := Work.FIArea6Hecke.R.chiPrime d chi) (m := m) hd hAn hAn' hagr hagr'' hL
  have hsre : 0 < s.re := by
    have h1 : min c0 1 / (d : ℝ) ^ ε ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast hd) ε)]
      exact le_trans (min_le_right _ _) (Real.one_le_rpow (by exact_mod_cast hd) hε.le)
    linarith
  have hreg' : 1 - c0 / (d : ℝ) ^ ε < s.re := by
    have h2 : min c0 1 / (d : ℝ) ^ ε ≤ c0 / (d : ℝ) ^ ε :=
      div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hd) ε))
    linarith
  intro hzero
  have h0 : Work.FIArea6Hecke.Lval d 0 Lam' s = 0 := by
    rw [← hEq s hsre]; exact hzero
  exact hclean d (Work.FIArea6Hecke.R.chiPrime d chi) 0 Lam' hd hchi' hAn' hagr'
    ((Work.FIArea6Hecke.R.psiReal_zero_iff).mpr hreal) s hsim hreg' hsle2 h0

end

end Work.FIArea6Hecke.R
