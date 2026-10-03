import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.noCompletion_principalStrict

namespace Work.FIArea6Hecke.R

/-- **A strict character that is trivial on the primary units is the principal strict character on
all primary elements.**  If `chi` is a strict character modulo `4d` with `chi z = 1` for every
primary `z` that is a unit modulo `4d`, then for every primary `z` the value `psi chi 0 z = chi z`
equals `principalStrict d z`: both are `1` when `z` is a unit modulo `4d`, and both are `0`
otherwise (`chi` because it is a strict character, `principalStrict d` by definition). -/
theorem heckeLam_eq_principalStrict_of_primary_trivial (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1) :
    Work.FIArea5.S16Hecke.heckeLam chi 0
      = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 := by
  classical
  funext n
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hprim, -⟩ := hz
  by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · simp only [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one, hexc z hprim hu,
      Work.FIArea6Hecke.principalStrict_of_unit hu]
  · simp only [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one, hchi.2 z hu,
      Work.FIArea6Hecke.principalStrict_of_not_unit hu]

/-- The two Hecke `L`-series agree (pointwise). -/
theorem heckeLSeries_eq_principalStrict_of_primary_trivial (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1) (s : ℂ) :
    Work.FIArea5.S16Hecke.heckeLSeries chi 0 s
      = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s :=
  LSeries_congr
    (fun {n} _ => congrFun (heckeLam_eq_principalStrict_of_primary_trivial d chi hchi hexc) n) s

/-- **The exceptional case of the Hecke completion.**  If the strict character `χ` mod `4d` is
trivial on every primary unit mod `4d`, then its Hecke `L`-function is that of the principal strict
character, namely `ζ_{ℚ(i)}` with the Euler factors over the primes above `4d` removed, which has a
pole at `s = 1`.  Consequently there is *no* entire function agreeing with
`heckeArch d 0 s · heckeLSeries χ 0 s` on the half-plane `re s > 1`. -/
theorem NoCompletionPrimaryAux (d : ℕ) (chi : GaussianInt → ℂ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = 1) :
    ¬ ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) := by
  rintro ⟨Lam, hAnal, hagr⟩
  refine noCompletion_principalStrict d hd ⟨Lam, hAnal, fun s hs => ?_⟩
  rw [← heckeLSeries_eq_principalStrict_of_primary_trivial d chi hchi hexc s]
  exact hagr s hs

end Work.FIArea6Hecke.R
