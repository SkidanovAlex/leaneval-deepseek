import Mathlib
import Submission.Work.MotAS.ASResidual
-- NOTE (2026-10-08): `Submission.Work.MotAS.aszPresentation`, `Submission.Work.MotAS.satGraphIsPrimeGen`
-- and `Submission.Work.MotA.coheight_eq_one_iff` were imported here and are **not used** by the
-- proofs below (the proof consumes `ASZElimP_irreducible`, `ASZElimMem`, `ASZGC.not_dvd_D0`,
-- `ASZGC.clause1_mem` and `ASResidual` only).  The first of them is heavy: it reaches
-- `MotAS/ASZGraphCert2.lean` → `MotAS/ASZF/ASZFCert.lean` → `MotAS/ASZC2/Cert{0..4}.lean` →
-- `MotAS/ASZC2/Data{0..4}.lean` (46 KB–153 KB, over the workspace limit and unbuilt), and so *this*
-- file used to sit on one of the two import chains by which those over-limit modules entered the
-- closure of `Work.MotV5.ASChart.linkCertAS` / `Work.MotC5N3.Wire`.  Dropping the three unused
-- imports breaks that chain (see `STATUS.md` §25.4 and `../REPORT_TO_LEAD.md` §11.1).  The four
-- used imports are kept individually, so the closure above them is exactly what the proof needs.
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.MotAS.ASZGC.clause1_mem

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotV5.Contrib.le_two_height_radical_ZIAS`

The radical of the AS residual chart ideal `ZIAS a b g ⊂ K[X₀,X₁,X₂]` has height at least `2`:
the residual curve is one-dimensional, so every component of it has codimension at least two.

## Route

For `K` a field of characteristic `5`, `a b g : K` with `a² - ab - b² ≠ 0` and `g ∉ ℘(K)`, the
workspace's AS chapter supplies (all axiom-clean)

* `Work.MotAS.ASZElimP_irreducible`, `Work.MotAS.ASZElimMem` — the eliminant
  `P := ASZElim.P a b g ∈ K[X₀,X₁]` is irreducible and its `Fin.succ`-rename lies in `Z`;
* `Work.MotAS.ASZGC.not_dvd_D0`, `Work.MotAS.ASZGC.clause1_mem` — the graph element
  `G := rename D₀ · X₀ + rename R₀` of the plane model lies in `Z`, and `P ∤ D₀`.

Since `Ideal.height` of a general ideal is the *infimum* of the heights of its minimal primes
(`Ideal.height_eq_inf_minimalPrimes`), it suffices to show that every minimal prime `𝔭` of `Z` has
height `≥ 2`.  Such a `𝔭` contains both `P' := rename P` and `G`.  The rename `P'` is prime in
`K[X₀,X₁,X₂]` (transfer `Prime P` from `K[X₀,X₁]` along the algebra equivalence
`MvPolynomial.finSuccEquiv K 2`, using `Polynomial.prime_C_iff`), so the principal ideal `(P')` is a
prime of height one; and `P' ∤ G`, because `P' ∣ G` would force `P ∣ D₀` after comparing the
coefficients of `X₀` (again via `finSuccEquiv`), contradicting `ASZGC.not_dvd_D0`.  Hence
`(P') < 𝔭`, and `Ideal.height_add_one_le_of_lt_of_isPrime` gives
`2 = height (P') + 1 ≤ height 𝔭`.
-/

set_option autoImplicit false

namespace Work.MotV5.Contrib

open MvPolynomial

/-- The `Fin.succ`-rename of a two-variable polynomial is sent to the corresponding constant
polynomial by `MvPolynomial.finSuccEquiv K 2`. -/
private lemma finSuccEquiv_rename_succ (K : Type) [Field K] (p : MvPolynomial (Fin 2) K) :
    (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) p)
      = Polynomial.C p := by
  have hcomp : ((MvPolynomial.finSuccEquiv K 2 : MvPolynomial (Fin 3) K →+*
      Polynomial (MvPolynomial (Fin 2) K)).comp
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)).toRingHom) = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show (MvPolynomial.finSuccEquiv K 2) ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3))
          (MvPolynomial.C r)) = Polynomial.C (MvPolynomial.C r)
      rw [MvPolynomial.rename_C, ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 3),
        AlgEquiv.commutes (MvPolynomial.finSuccEquiv K 2) r,
        ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 2)]
      exact (AlgHom.commutes (Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 2) K)) r).symm
    · intro i
      show (MvPolynomial.finSuccEquiv K 2) ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3))
          (MvPolynomial.X i)) = Polynomial.C (MvPolynomial.X i)
      rw [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun hcomp p

/-- **The eliminant's rename is prime in `K[X₀,X₁,X₂]`**, being the `finSuccEquiv`-image of a
constant polynomial whose constant coefficient `ASZElim.P a b g` is prime in `K[X₀,X₁]`. -/
private lemma prime_rename_elim (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Prime (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g) :
      MvPolynomial (Fin 3) K) := by
  have hEprime : Prime (Work.MotAS.ASZElim.P a b g) :=
    (Work.MotAS.ASZElimP_irreducible K a b g ha hg).prime
  have heq : (MvPolynomial.finSuccEquiv K 2)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g))
      = Polynomial.C (Work.MotAS.ASZElim.P a b g) := finSuccEquiv_rename_succ K _
  have h1 : Prime ((MvPolynomial.finSuccEquiv K 2)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g))) :=
    heq ▸ (Polynomial.prime_C_iff.mpr hEprime)
  exact (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2).toMulEquiv).mp h1

/-- **The graph element is not a multiple of the eliminant.**  In the plane model of the AS
residual curve the graph relation is `D₀ · X₀ + R₀ = 0`; if it were divisible by the eliminant
`P` (renamed to `K[X₀,X₁,X₂]`), comparing the coefficients of `X₀` would give `P ∣ D₀`, which is
excluded by `Work.MotAS.ASZGC.not_dvd_D0`. -/
private lemma graph_notMem_span_elim (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) :
          MvPolynomial (Fin 3) K)
      ∉ Ideal.span
        {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨H, hH⟩ := hmem
  have hL : (MvPolynomial.finSuccEquiv K 2)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) :
          MvPolynomial (Fin 3) K)
      = Polynomial.C (Work.MotAS.ASZGC.D0 a b g) * Polynomial.X
        + Polynomial.C (Work.MotAS.ASZGC.R0 a b g) := by
    rw [map_add, map_mul, finSuccEquiv_rename_succ, MvPolynomial.finSuccEquiv_X_zero,
      finSuccEquiv_rename_succ]
  have hR : (MvPolynomial.finSuccEquiv K 2)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g) * H)
      = Polynomial.C (Work.MotAS.ASZElim.P a b g) * (MvPolynomial.finSuccEquiv K 2) H := by
    rw [map_mul, finSuccEquiv_rename_succ]
  have hcoeff : (Polynomial.coeff ((MvPolynomial.finSuccEquiv K 2)
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) :
          MvPolynomial (Fin 3) K)) 1)
      = Polynomial.coeff ((MvPolynomial.finSuccEquiv K 2)
        (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g) * H)) 1 := by
    rw [hH]
  rw [hL, hR] at hcoeff
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C] at hcoeff
  simp at hcoeff
  exact Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg
    ⟨Polynomial.coeff ((MvPolynomial.finSuccEquiv K 2) H) 1, hcoeff⟩

theorem le_two_height_radical_ZIAS (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (2 : ℕ∞) ≤ (Ideal.radical (Work.MotAS.ZIAS a b g)).height := by
  classical
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.radical_minimalPrimes]
  refine le_iInf₂ fun 𝔭 h𝔭 => ?_
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  have hEmem : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
      ∈ Work.MotAS.ZIAS a b g := Work.MotAS.ASZElimMem K a b g ha hg
  have hGmem : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) :
          MvPolynomial (Fin 3) K) ∈ Work.MotAS.ZIAS a b g :=
    Work.MotAS.ASZGC.clause1_mem K a b g
  have hE'prime : Prime (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      (Work.MotAS.ASZElim.P a b g) : MvPolynomial (Fin 3) K) :=
    prime_rename_elim K a b g ha hg
  have hspan_prime : (Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} : Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hE'prime.ne_zero).mpr hE'prime
  have hE'ne : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
      ∈ nonZeroDivisors (MvPolynomial (Fin 3) K) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hE'prime.ne_zero
  have hheight1 : (Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} : Ideal (MvPolynomial (Fin 3) K)).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hE'ne hE'prime.not_isUnit
  have hnotmem : (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
        * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) :
          MvPolynomial (Fin 3) K)
      ∉ Ideal.span
        {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} :=
    graph_notMem_span_elim K a b g ha hg
  have hle : Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} ≤ 𝔭 := by
    rw [Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h𝔭.le hEmem
  have hlt : Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)} < 𝔭 := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hnotmem (heq ▸ h𝔭.le hGmem)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hheight1] at h2
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ 𝔭.height := h2

end Work.MotV5.Contrib
