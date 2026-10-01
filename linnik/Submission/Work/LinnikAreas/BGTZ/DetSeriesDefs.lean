/-
# Auxiliary vocabulary for the BGTZ detector-series identity

The identity proved in `DetSeriesIdentity` is

`Σ_n detCoeff χ₁ χ θw n · n^{-s} = L(s,χ)L(s,χχ₁)·G(s,χ)`   (`1 < Re s`),

where `detCoeff χ₁ χ θw n = a(n)χ(n)(Σ_{d|n}θ_d)²` (see `DetectorDefs`) and `G(s,χ)` is the
Selberg sieve function `sieveG` (see `BGTZSetup`).  The proof writes the coefficient series as
`Σ_{d,e ≤ R} θ_dθ_e · Σ_{n : [d,e] | n} a(n)χ(n)n^{-s}` and evaluates, for squarefree `m`, the
"multiples of `m`" series

`detMultSer χ₁ χ m s = Σ_{n : m | n} a(n)χ(n)n^{-s} = L(s,χ)L(s,χχ₁)·∏_{p | m} sieveLocal χ₁ χ s p`.

The present module fixes the objects used in that evaluation.  (It is deliberately
self-contained: `a(n)χ(n)` and the multiples series are defined here, and the only imported
vocabulary is `aCoeff`, `sieveLocal`, `sieveG`, `IsSieveWeight` from `BGTZSetup` and `detCoeff`
from `DetectorDefs`.)

* `detCfun χ₁ χ n = a(n)χ(n)`, the Dirichlet coefficient of `L(s,χ)L(s,χχ₁)`;
* `detMultSer χ₁ χ m s = Σ_{n : m | n} detCfun χ₁ χ n · n^{-s}`, the "multiples of `m`" series;
* `rProd T = ∏_{p ∈ T} p`, the squarefree number attached to a finite set `T` of primes, used to
  index the product expansion `[m | uv] = ∏_{p | m} [p | uv]`;
* `pairSer χ₁ χ m s` — the same series re-indexed along the Dirichlet convolution
  `a(n)χ(n) = Σ_{uv = n} (χχ₁)(u)χ(v)`, i.e. as a double sum over the pair `(u,v)` subject to
  the single condition `m | u·v`.

The equality `detMultSer χ₁ χ m s = pairSer χ₁ χ m s` is `DetMultSerPair.DetMultSerPair`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- `∏_{p ∈ T} p`, the squarefree integer attached to a finite set `T` of natural numbers
(used only for `T` a set of primes). -/
def rProd (T : Finset ℕ) : ℕ := ∏ p ∈ T, p

/-- The Dirichlet coefficient `a(n)χ(n)` of `L(s,χ)L(s,χχ₁)`. -/
def detCfun (χ₁ χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (aCoeff χ₁ n : ℂ) * χ ((n : ℕ) : ZMod q)

/-- The "multiples of `m`" series `Σ_{n : m | n} a(n)χ(n)n^{-s}`. -/
def detMultSer (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (if m ∣ n then detCfun χ₁ χ n else 0) / ((n : ℂ) ^ s)

/-- The pair-series form of the detector coefficient series.  Re-indexing the Dirichlet
convolution `detCfun χ₁ χ = (χχ₁) ⍟ χ` turns `Σ_n [m|n]·a(n)χ(n)n^{-s}` into the double sum over
the pair `(u,v) ∈ ℕ+ × ℕ+` subject to the single condition `m ∣ u·v`. -/
def pairSer (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' p : ℕ+ × ℕ+,
    (if m ∣ (p.1 : ℕ) * (p.2 : ℕ) then
        ((χ * χ₁) (((p.1 : ℕ) : ZMod q))) * (χ (((p.2 : ℕ) : ZMod q))) else 0)
      / (((((p.1 : ℕ) * (p.2 : ℕ)) : ℕ) : ℂ) ^ s)

@[simp] lemma rProd_empty : rProd (∅ : Finset ℕ) = 1 := by simp [rProd]

lemma rProd_pos {T : Finset ℕ} (h : ∀ p ∈ T, 0 < p) : 0 < rProd T :=
  Finset.prod_pos fun p hp => h p hp

@[simp] lemma detCfun_zero (χ₁ χ : DirichletCharacter ℂ q) : detCfun χ₁ χ 0 = 0 := by
  simp [detCfun, aCoeff, Nat.divisors_zero]

@[simp] lemma detMultSer_zero (χ₁ χ : DirichletCharacter ℂ q) (s : ℂ) : detMultSer χ₁ χ 0 s = 0 := by
  rw [detMultSer]
  have hz : (fun n : ℕ => (if 0 ∣ n then detCfun χ₁ χ n else 0) / ((n : ℂ) ^ s)) = fun _ => 0 := by
    funext n
    by_cases h : 0 ∣ n
    · rw [if_pos h, (zero_dvd_iff.mp h), detCfun_zero, zero_div]
    · rw [if_neg h, zero_div]
  rw [hz, tsum_zero]

end Work.LinnikAreas.BGTZ
