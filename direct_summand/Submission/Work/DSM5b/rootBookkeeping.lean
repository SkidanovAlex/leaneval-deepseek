import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff
import Submission.Work.DSPB5.Basic

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

/-- **Injectivity of the `p ^ n`-th power map in a reduced ring in which `p = 0`.**

For a prime `p` and a reduced commutative ring `A` with `(p : A) = 0`, the map `z ↦ z ^ (p ^ n)` is
injective.  This is the form needed in the localisations `Localization.Away (tS t S)` of the M5b
argument, for which only `(p : ·) = 0` is available (`p` need not be the characteristic).

Route: the Freshman's dream `(u + v) ^ (p ^ n) = u ^ (p ^ n) + v ^ (p ^ n)`
(`Commute.exists_add_pow_prime_pow_eq`, whose correction term is killed by `(p : A) = 0`) exhibits
`z ↦ z ^ (p ^ n)` as an additive map; its kernel consists of the elements with `z ^ (p ^ n) = 0`,
i.e. of the nilpotents (`(z ^ (p ^ n)) ^ p = z ^ (p ^ (n + 1))` strips the exponent one `p` at a
time), and `IsReduced.eq_zero` kills those. -/
theorem pow_pow_injective_of_reduced {A : Type*} [CommRing A] [IsReduced A] {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) = 0) (n : ℕ) : Function.Injective fun z : A => z ^ (p ^ n) := by
  have hadd : ∀ m : ℕ, ∀ u v : A, (u + v) ^ (p ^ m) = u ^ (p ^ m) + v ^ (p ^ m) := by
    intro m u v
    obtain ⟨c, hc⟩ := (Commute.all u v).exists_add_pow_prime_pow_eq hp m
    rw [hc, hp0]
    ring
  have hker : ∀ z : A, z ^ (p ^ n) = 0 → z = 0 := fun z h => IsReduced.eq_zero z ⟨p ^ n, h⟩
  let φ : A →+ A :=
    { toFun := fun z => z ^ (p ^ n)
      map_zero' := zero_pow (pow_pos hp.pos n).ne'
      map_add' := hadd n }
  intro u v huv
  have hkey : φ u = φ v := huv
  have h0 : φ (u - v) = 0 := by rw [map_sub φ u v, hkey, sub_self]
  exact sub_eq_zero.mp (hker (u - v) h0)

/-- **Root bookkeeping: the `p^e`-th root turns honest `ϖ k`-killing into perfected `ϖ k`-killing.**

`Z : PCX p t 0` is a family of perfected chart ring elements (concrete tuple complex,
`Submission/Work/DSM5b/PerfComplexDefs.lean`), `e` a level at which all its components are honest
(`(Z τ)^{p^e} ∈ chartRing t (tupRng τ)`), and `Y τ = ⟨(Z τ)^{p^e}, he τ⟩ : HCX t 0` the honest
`p^e`-th power family (`Submission/Work/DSM5b/H0Defs.lean`).  Suppose the honest killing equation
holds at level `k`, `ϖ k • Y = HCcoaug t w` (componentwise: the image of `ϖ k = T^(1/p^k)` times
`(Z τ)^{p^e}` is the image of `w`, for every `τ`).  Then the same holds for `Z` itself at level `k`:
`∃ w', ϖ k • Z = PCcoaug p t w'`.

Route (elementary, componentwise): the hypothesis says in `L_S = Localization.Away (tS t (tupRng τ))`
that `(ϖ k)·(Z τ)^{p^e} = algebraMap w`.  Apply the `p^e`-th root map of `L_S` — a ring homomorphism
on the localisation with `ψ^e (x^{p^e}) = x` and
`ψ^e (algebraMap R _ c) = algebraMap R _ ((frobeniusEquiv R p).symm^[e] c)`.  Using the tower relation
`(frobeniusEquiv R p).symm^[k+e] T ^ (p^e) = (frobeniusEquiv R p).symm^[k] T` (i.e.
`IsRootTower.pow_pow` for `IsRootTower.frozen`, in `Submission/Work/DSM5b/Basic.lean` — it needs only
`CharP`/`PerfectRing` on `R`), the rooted equation is `(ϖ (k+e)) • Z τ = (image of ψ^e w)`.
Multiplying by `ϖ (k+e)^{p^e - 1}` yields the claim with the single
`w' := (ϖ (k+e))^{p^e - 1} * ψ^e w`; conclude in `PCX p t 0` by `Subtype.ext`/`funext`.

CAVEAT for the prover: Mathlib has no `PerfectRing`/`ExpChar` instance for `Localization.Away (tS t S)`
(it need not have characteristic `p`), so the root map on the localisation has to be constructed by
hand.  The hypothesis gives the equation *inside* `chartRing t S ⊆ L_S`; either build the root map
from `IsLocalization.Away`/`IsLocalization.surj` reasoning (`L_S` is a localisation of the perfect
ring `R`, so the `p^e`-th root of an element of the image of `R` is again in the image), or reduce
componentwise: write the hypothesis in the form `algebraMap (R) _ (ϖ k) * (Z τ)^{p^e} = algebraMap _ w`
and use that `R` is perfect and reduced (hence `p^e`-th roots in `L_S` of images of elements of `R`
are images).  Degenerate `tS t S = 0` (trivial localisation) and `e = 0` cases are immediate
(`Subsingleton.elim`). -/
theorem rootBookkeeping (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [DecidableEq ι] (t : ι → R) (T : R) (k : ℕ) (Z : PCX p t 0)
    (e : ℕ)
    (he : ∀ τ : Fin 1 → ι,
      (Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e) ∈ chartRing t (tupRng τ))
    (w : R)
    (hw : (frobeniusEquiv R p).symm^[k] T •
            (fun τ => ⟨(Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e), he τ⟩ : HCX t 0)
          = HCcoaug t w) :
    ∃ w' : R, (frobeniusEquiv R p).symm^[k] T • Z = PCcoaug p t w' := by
  classical
  have hp : p.Prime := Fact.out
  set B : R := (frobeniusEquiv R p).symm^[k + e] T with hB
  set w₁ : R := (frobeniusEquiv R p).symm^[e] w with hw₁
  -- the two tower relations used by the bookkeeping
  have hBpow : B ^ (p ^ e) = (frobeniusEquiv R p).symm^[k] T := by
    rw [hB]
    exact (IsRootTower.frozen p R T).pow_pow k e
  have hw₁pow : w₁ ^ (p ^ e) = w := by
    rw [hw₁]
    simpa using (IsRootTower.frozen p R w).pow_pow 0 e
  have hpe : 1 ≤ p ^ e := pow_pos hp.pos e
  have hpow : (frobeniusEquiv R p).symm^[k] T ^ (p ^ e - 1) * (frobeniusEquiv R p).symm^[k] T
      = (frobeniusEquiv R p).symm^[k] T ^ (p ^ e) := by
    rw [← pow_succ, Nat.sub_add_cancel hpe]
  -- the hypothesis, componentwise in the localisation
  have hcomp : ∀ τ : Fin 1 → ι,
      algebraMap R (Localization.Away (tS t (tupRng τ))) ((frobeniusEquiv R p).symm^[k] T) *
        (Z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e) = algebraMap R _ w := by
    intro τ
    have h1 := congrFun hw τ
    have h2 := congrArg
      (fun y : chartRing t (tupRng τ) => (y : Localization.Away (tS t (tupRng τ)))) h1
    simpa [HCcoaug, Algebra.smul_def] using h2
  -- the localisation-level root bookkeeping
  have key : ∀ (S : Finset ι) (x : Localization.Away (tS t S)),
      algebraMap R (Localization.Away (tS t S)) ((frobeniusEquiv R p).symm^[k] T) * x ^ (p ^ e)
        = algebraMap R (Localization.Away (tS t S)) w →
      algebraMap R (Localization.Away (tS t S)) ((frobeniusEquiv R p).symm^[k] T) * x
        = algebraMap R (Localization.Away (tS t S)) (B ^ (p ^ e - 1) * w₁) := by
    intro S x hx
    refine pow_pow_injective_of_reduced (A := Localization.Away (tS t S)) hp
      (natCast_p_eq_zero_localization p t S) e ?_
    have hL : (algebraMap R (Localization.Away (tS t S)) ((frobeniusEquiv R p).symm^[k] T) * x)
          ^ (p ^ e)
        = algebraMap R (Localization.Away (tS t S))
            ((frobeniusEquiv R p).symm^[k] T ^ (p ^ e - 1) * w) := by
      rw [mul_pow, ← map_pow, ← hpow, map_mul, mul_assoc, hx, ← map_mul]
    have hR : (algebraMap R (Localization.Away (tS t S)) (B ^ (p ^ e - 1) * w₁)) ^ (p ^ e)
        = algebraMap R (Localization.Away (tS t S))
            ((frobeniusEquiv R p).symm^[k] T ^ (p ^ e - 1) * w) := by
      rw [← map_pow, mul_pow, ← pow_mul, hw₁pow, mul_comm (p ^ e - 1) (p ^ e), pow_mul, hBpow]
    exact hL.trans hR.symm
  refine ⟨B ^ (p ^ e - 1) * w₁, ?_⟩
  funext τ
  apply Subtype.ext
  simpa [PCcoaug, Algebra.smul_def]
    using key (tupRng τ) (Z τ : Localization.Away (tS t (tupRng τ))) (hcomp τ)

end Work.DSM5b

