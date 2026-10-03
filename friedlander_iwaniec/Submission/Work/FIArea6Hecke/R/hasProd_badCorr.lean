import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators

/-- The finite Euler-factor correction `G_d(s) = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})` is the
infinite product over the rational primes of the local correction factor, which is `1` off the
finitely many primes dividing `4d`. -/
theorem hasProd_badCorr (d : ℕ) (s : ℂ) :
    HasProd (fun p : Nat.Primes =>
        if (p : ℕ) ∈ (4 * d).primeFactors then
          (1 - (((p : ℕ) : ℂ) ^ (-s))) *
            (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        else 1)
      (Work.FIArea6Hecke.R.badPoly d s) := by
  classical
  -- the finitely many rational primes dividing `4d`, viewed as `Nat.Primes`
  let e : {q // q ∈ (4 * d).primeFactors} ↪ Nat.Primes :=
    ⟨fun q => ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩,
     fun a b h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩
  let t : Finset Nat.Primes := ((4 * d).primeFactors.attach).map e
  -- the local factor is `1` outside `t`
  have hf : ∀ p : Nat.Primes, p ∉ t →
      (if (p : ℕ) ∈ (4 * d).primeFactors then
          (1 - (((p : ℕ) : ℂ) ^ (-s))) *
            (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        else 1) = 1 := by
    intro p hp
    rw [if_neg]
    intro hcon
    exact hp (Finset.mem_map.mpr ⟨⟨(p : ℕ), hcon⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
  have hmain := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Nat.Primes)
    (f := fun p : Nat.Primes =>
        if (p : ℕ) ∈ (4 * d).primeFactors then
          (1 - (((p : ℕ) : ℂ) ^ (-s))) *
            (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        else 1) (s := t) hf
  -- the finite product over `t` is exactly `badPoly d s`
  have hprod : (∏ p ∈ t,
        (if (p : ℕ) ∈ (4 * d).primeFactors then
          (1 - (((p : ℕ) : ℂ) ^ (-s))) *
            (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        else 1)) = Work.FIArea6Hecke.R.badPoly d s := by
    rw [Work.FIArea6Hecke.R.badPoly]
    rw [show t = ((4 * d).primeFactors.attach).map e from rfl, Finset.prod_map]
    rw [← Finset.prod_attach (s := (4 * d).primeFactors)
      (f := fun q : ℕ => (1 - (q : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun q * (q : ℂ) ^ (-s)))]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' : ((e x : Nat.Primes) : ℕ) = (x : ℕ) := rfl
    rw [hx', if_pos x.2]
  rw [← hprod]
  exact hmain

end Work.FIArea6Hecke.R
