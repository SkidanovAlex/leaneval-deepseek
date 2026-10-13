import Mathlib
import Submission.Work.DSM5b.locBCRing
import Submission.Work.DSM5b.H0Defs

/-!
# `Work.DSM5b.hCdBaseChange` — the honest chart Čech differential commutes with base change

Let `R₀ → R` be a ring homomorphism (`Algebra R₀ R`), `t : ι → R₀` a family, `b = algebraMap ∘ t`
the base-changed family, and let `HCd t m : HCX t m →ₗ[R] HCX t (m+1)` be the explicit coordinate
form of the honest (unperfected) chart Čech differential,
`(HCd t m z) τ = ∑ i, (-1)^i • rhoH t (tupRng_del_subset i τ) (z (tupDel i τ))`
(`Submission/Work/DSM5b/H0Defs.lean`), with `HCXb t m : HCX t m →ₗ[R₀] HCX b m` the base-change map
of the terms, applied componentwise `locBCRing t (tupRng σ)`
(`Submission/Work/DSM5b/locBCRing.lean`).

**The statement proved here** is that the square

    HCX t m  --HCd t m-->  HCX t (m+1)
       |                       |
     HCXb                    HCXb
       v                       v
    HCX b m  --HCd b m-->  HCX b (m+1)

commutes: `HCd b m (HCXb t m z) = HCXb t (m+1) (HCd t m z)`.  Equivalently, the coordinate
differential of the base-changed complex is the base change of the coordinate differential — the
"step 2" of the plan recorded in the header of `Submission/Work/DSM5b/locBCRing.lean`.

The proof is a two-line computation, once one notices the only two inputs:

* `locBCRing_rhoH` (proved in `locBCRing.lean`): `locBCRing` commutes with the chart restriction
  maps `rhoH t h` — so it commutes with each *term* of the alternating sum, and
* the base-change of the scalar `(-1)^i`: `R₀` acts on the base-changed chart ring through
  `algebraMap R₀ R`, so `(-1 : R)^i • x = (-1 : R₀)^i • x` for `x` a base-changed chart element
  (this is the helper `neg_one_pow_smul_eq_chartRing` below; it uses
  `IsScalarTower.algebraMap_smul` for the tower `R₀ → R → R[J/b_S]`).

Beyond that, both sides are the same finite alternating sum of the same terms, so the two sides
agree componentwise: first push `locBCRing` through the sum and the scalar action (`map_sum`,
`map_smul`), then rewrite each summand along `locBCRing_rhoH` and fold `HCXb` back up
(`← HCXb_apply`), then convert the scalar.
-/

namespace Work.DSM5b

universe a

/-- **Base change of the scalar `(-1)^i` on a base-changed chart ring.**  If `b = algebraMap ∘ t`
and `x ∈ R[J/b_S] = chartRing b S`, then `(-1 : R)^i • x = (-1 : R₀)^i • x`: the `R₀`-module
structure on `chartRing b S` is the restriction of scalars along `algebraMap R₀ R`, and
`algebraMap R₀ R ((-1 : R₀)^i) = (algebraMap R₀ R (-1))^i = (-1 : R)^i`. -/
lemma neg_one_pow_smul_eq_chartRing {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R]
    [Algebra R₀ R] {ι : Type a} [DecidableEq ι] (t : ι → R₀) (S : Finset ι)
    (x : DSMap.Mix2.chartRing (fun i => algebraMap R₀ R (t i)) S) (k : ℕ) :
    ((-1 : R) ^ k) • x = ((-1 : R₀) ^ k) • x := by
  have h : ((-1 : R) ^ k) = algebraMap R₀ R (((-1 : R₀) ^ k)) := by
    rw [map_pow, map_neg, map_one]
  rw [h, IsScalarTower.algebraMap_smul]

theorem hCdBaseChange {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R] [Algebra R₀ R] {ι : Type a} [DecidableEq ι] (t : ι → R₀) (m : ℕ) (z : Work.DSM5b.HCX t m) :
    Work.DSM5b.HCd (fun i => algebraMap R₀ R (t i)) m (Work.DSM5b.HCXb (R := R) t m z)
      = Work.DSM5b.HCXb (R := R) t (m + 1) (Work.DSM5b.HCd t m z) := by
  funext τ
  rw [HCd_apply, HCXb_apply]
  rw [HCd_apply, map_sum]
  simp only [map_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [locBCRing_rhoH, ← HCXb_apply, neg_one_pow_smul_eq_chartRing]

end Work.DSM5b
