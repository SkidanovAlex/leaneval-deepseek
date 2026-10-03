import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6Hecke.R

open scoped LSeries.notation

/-- `chi4fun` agrees with the `ℕ`-restriction of the Dirichlet character `chi4C` modulo `4`. -/
lemma chi4fun_eq_chi4C (n : ℕ) : chi4fun n = chi4C (n : ZMod 4) := by
  simp [chi4fun, chi4C, MulChar.ringHomComp_apply]

/-- The naive `L`-series of `chi4fun` is the `L`-series of the `ℕ`-restriction of `chi4C`. -/
lemma LSeries_chi4fun_eq (s : ℂ) :
    LSeries chi4fun s = LSeries (fun n : ℕ => (chi4C (n : ZMod 4) : ℂ)) s :=
  LSeries_congr (f := chi4fun) (g := fun n : ℕ => (chi4C (n : ZMod 4) : ℂ))
    (fun {n} _ => chi4fun_eq_chi4C n) s

theorem LSeries_chi4fun_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))⁻¹)
      (LSeries Work.FIArea6Hecke.R.chi4fun s) := by
  rw [LSeries_chi4fun_eq]
  refine (DirichletCharacter.LSeries_eulerProduct_hasProd chi4C hs).congr_fun ?_
  intro p
  simp only [chi4fun_eq_chi4C]

end Work.FIArea6Hecke.R
