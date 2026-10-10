import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

/-- **Corresponding number fields have the same completely split primes.**  For a local
correspondence `a` of `ϕ` (CoNF (12.1.9)), a rational prime `p` splits completely in `K₁` if and
only if it splits completely in `K₂`.

Proof route: `a.residueChar` forces `a.primeMap` to preserve the rational prime below a prime
(`CharP` of the residue field detects it, cf. `primeEquivOver` and `primeMap_mem_primesOver` in
`Submission/Work/ReconstructField/finrank_eq_of_localCorrespondence.lean`), so `a.primeMap` restricts
to a bijection between the primes of `K₁` above `p` and those of `K₂` above `p`, giving the equality
of the two `ncard`s; the equality of the two `finrank`s is
`NK.ReconstructField.finrank_eq_of_localCorrespondence`.  (Alternatively, via `a.localDegree`:
complete splitting is `e = f = 1` at every prime above `p`, and the prime bijection preserves
`inertiaDeg * ramificationIdx`.) -/
theorem splitsCompletely_rat_iff_of_localCorrespondence
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (p : NK.Chebotarev.PrimeIdeal ℚ) :
    NK.ReconstructField.SplitsCompletely ℚ K₁ p ↔
      NK.ReconstructField.SplitsCompletely ℚ K₂ p := by
  -- the local correspondence restricts to a bijection of the primes above the rational prime `p`
  have hn : (p.asIdeal.primesOver (NumberField.RingOfIntegers K₁)).ncard =
      (p.asIdeal.primesOver (NumberField.RingOfIntegers K₂)).ncard :=
    Nat.card_congr (NK.ReconstructField.primeEquivOver a p)
  -- corresponding number fields have the same degree over `ℚ`
  have hf : Module.finrank ℚ K₁ = Module.finrank ℚ K₂ :=
    NK.ReconstructField.finrank_eq_of_localCorrespondence a
  -- `SplitsCompletely` is the equality of exactly these two numbers
  simp only [NK.ReconstructField.SplitsCompletely, hn, hf]

end NK.ReconstructField
