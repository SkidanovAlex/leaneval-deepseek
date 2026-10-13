import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff
import Submission.Work.DSM5b.phiPC_aux
import Submission.Work.DSMap.Mix2

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

set_option maxHeartbeats 1600000

namespace Work.DSM5b

/-! ## Auxiliary ring theory of `Localization.Away f` over a perfect ring of characteristic `p`

Everything in this section is self-contained (only `Mathlib`): it provides the `p`-th roots of
`Localization.Away f` (`FrobSurjAway`), the injectivity of `x ↦ x ^ p` there (`pow_injective_away`),
and the two elementary manipulations of `p`-th powers in a ring in which `p = 0` used for the
Freshman's dream of the Frobenius map. -/

section RootTheory

/-- In a localisation `R[1/f]` of a ring of characteristic `p`, the natural number `p` is `0`.
(No `CharP` instance is available on the localisation itself: it can be the trivial ring; only
`(p : ·) = 0` survives, and that is all the Frobenius arguments need.) -/
lemma natCast_p_eq_zero_away {R : Type*} [CommRing R] {p : ℕ} [CharP R p] (f : R) :
    (p : Localization.Away f) = 0 := by
  rw [← map_natCast (algebraMap R (Localization.Away f)) p, CharP.cast_eq_zero R p, map_zero]

/-- Freshman's dream in a commutative ring in which `p = 0` for a prime `p`. -/
lemma add_pow_prime_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h : (p : A) = 0)
    (u v : A) : (u + v) ^ p = u ^ p + v ^ p := by
  obtain ⟨c, hc⟩ := (Commute.all u v).exists_add_pow_prime_pow_eq hp 1
  rw [pow_one] at hc
  rw [hc, h]
  ring

/-- In a commutative ring in which `p = 0` for a prime `p`, `(-1) ^ p = -1` (for `p = 2` this says
`1 = -1` in a ring of characteristic two). -/
lemma neg_one_pow_eq_neg_one_of_natCast_prime_eq_zero {A : Type*} [CommRing A] {p : ℕ}
    (hp : p.Prime) (h : (p : A) = 0) : (-1 : A) ^ p = -1 := by
  rcases Nat.Prime.eq_two_or_odd' hp with h2 | hodd
  · subst h2
    have h0 : (2 : A) = 0 := by simpa using h
    have hone : (1 : A) = -1 := by
      apply eq_neg_of_add_eq_zero_right
      rw [← two_mul]
      simpa using h0
    have hsq : (-1 : A) ^ 2 = 1 := by ring
    rw [hsq]
    exact hone
  · exact Odd.neg_one_pow hodd

/-- The signs `(-1) ^ i` are fixed by the `p`-th power map in a ring in which `p = 0`. -/
lemma neg_one_pow_pow_eq_self {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (h : (p : A) = 0)
    (i : ℕ) : ((-1 : A) ^ i) ^ p = (-1 : A) ^ i := by
  rw [← pow_mul, mul_comm i p, pow_mul, neg_one_pow_eq_neg_one_of_natCast_prime_eq_zero hp h]

/-- A perfect ring of characteristic a prime is reduced. -/
lemma isReduced_of_charP_perfectRing (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R]
    [CharP R p] [PerfectRing R p] : IsReduced R := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := hz
  have hpow : z ^ (p ^ n) = 0 :=
    pow_eq_zero_of_le (le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hn
  have h1 : (frobenius R p)^[n] z = 0 := by rw [iterate_frobenius, hpow]
  have h2 : (frobenius R p)^[n] (0 : R) = 0 := Function.iterate_fixed (map_zero _) n
  exact (injective_frobenius R p).iterate n (h1.trans h2.symm)

/-- On a localisation away from an element of a perfect ring of characteristic `p`, the `p`-th power
map is injective. -/
lemma pow_injective_away (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) {x y : Localization.Away f} (h : x ^ p = y ^ p) : x = y := by
  haveI : IsReduced R := isReduced_of_charP_perfectRing p
  haveI : IsReduced (Localization.Away f) := inferInstance
  have hp : p.Prime := Fact.out
  have hp0 : (p : Localization.Away f) = 0 := natCast_p_eq_zero_away f
  have hadd := add_pow_prime_eq_zero hp hp0
  have h1 : x ^ p = (x - y) ^ p + y ^ p := by rw [← hadd (x - y) y, sub_add_cancel]
  have h2 : (x - y) ^ p = 0 := by
    rw [h] at h1
    have h3 : (x - y) ^ p + y ^ p = 0 + y ^ p := by rw [zero_add, ← h1]
    exact add_right_cancel h3
  exact sub_eq_zero.mp (IsReduced.eq_zero (x - y) ⟨p, h2⟩)

/-- **`p`-th roots exist in a localisation of a perfect ring.**  `R` is a commutative ring of
characteristic the prime `p` which is perfect; then for every `f : R` and every element `x` of
`R[1/f] = Localization.Away f` there is `y` with `y ^ p = x`.

The localisation need not have characteristic `p` (`f = 0` gives the trivial ring), so the root is
built by hand: `IsLocalization.lift` of the ring hom
`algebraMap R R[1/f] ∘ (frobeniusEquiv R p).symm` gives a ring hom `ψ` with
`ψ (algebraMap r) = algebraMap (r ^ (1/p))`; the composite `ψ' = (·)^p ∘ ψ` is again a ring hom
because `(p : R[1/f]) = 0`, it agrees with the identity on `algebraMap R R[1/f]`, hence equals the
identity by `IsLocalization.ringHom_ext`. -/
lemma frobSurjAway (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (f : R) (x : Localization.Away f) :
    ∃ y : Localization.Away f, y ^ p = x := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : Localization.Away f) = 0 := natCast_p_eq_zero_away f
  have hroot : ∀ r : R, (frobeniusEquiv R p).symm r ^ p = r := by
    intro r
    rw [← frobenius_def p ((frobeniusEquiv R p).symm r)]
    exact frobenius_apply_frobeniusEquiv_symm R p r
  let g : R →+* Localization.Away f :=
    { toFun := fun r => algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm r)
      map_one' := by simp
      map_mul' := by intro a b; simp
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hgunit : ∀ y : Submonoid.powers f, IsUnit (g y) := by
    rintro ⟨y, hy⟩
    rw [Submonoid.mem_powers_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    have hval : g (f ^ n)
        = (algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm f)) ^ n := by
      show algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm (f ^ n)) = _
      rw [map_pow, map_pow]
    rw [hval]
    have hunit : IsUnit (algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm f)) := by
      have h2 : IsUnit ((algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm f)) ^ p) := by
        rw [← map_pow, hroot f]
        exact IsLocalization.Away.algebraMap_isUnit f
      exact (isUnit_pow_iff hp.ne_zero).mp h2
    exact hunit.pow n
  let ψ : Localization.Away f →+* Localization.Away f :=
    IsLocalization.lift (M := Submonoid.powers f) (g := g) hgunit
  have hψ : ∀ r : R, ψ (algebraMap R (Localization.Away f) r)
      = algebraMap R (Localization.Away f) ((frobeniusEquiv R p).symm r) := fun r => by
    show IsLocalization.lift (M := Submonoid.powers f) (g := g) hgunit
      (algebraMap R (Localization.Away f) r) = _
    rw [IsLocalization.lift_eq (M := Submonoid.powers f) (g := g) hgunit r]
    rfl
  let frobL : Localization.Away f →+* Localization.Away f :=
    frobeniusOfNatCastEqZero (Localization.Away f) p hp hp0
  have hfrobL : ∀ z, frobL z = z ^ p := fun z => rfl
  have hcomp : (frobL.comp ψ).comp (algebraMap R (Localization.Away f))
      = (RingHom.id (Localization.Away f)).comp (algebraMap R (Localization.Away f)) := by
    ext r
    show frobL (ψ (algebraMap R (Localization.Away f) r))
      = algebraMap R (Localization.Away f) r
    rw [hfrobL, hψ r, ← map_pow, hroot r]
  have hEq : frobL.comp ψ = RingHom.id (Localization.Away f) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) hcomp
  refine ⟨ψ x, ?_⟩
  have h := DFunLike.congr_fun hEq x
  rw [RingHom.comp_apply, RingHom.id_apply, hfrobL] at h
  exact h

end RootTheory

/-! ## The perfected coordinate complex: the honest inclusion, the Frobenius and its inverse -/

section Complex

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R)

/-- The honest chart complex, read in the perfected one (componentwise inclusion of the chart
rings `chartRing t S ⊆ perfChartRing p t S`), as an `R`-linear map. -/
noncomputable def iota (m : ℕ) : HCX t m →ₗ[R] PCX p t m where
  toFun w := fun τ => ⟨(w τ : Localization.Away (tS t (tupRng τ))),
    chartRing_le_perfChartRing p t (tupRng τ) (w τ).2⟩
  map_add' w w' := by
    funext τ; apply Subtype.ext; simp
  map_smul' r w := by
    funext τ; apply Subtype.ext; simp

lemma iota_injective (m : ℕ) {w w' : HCX t m} (h : iota p t m w = iota p t m w') : w = w' := by
  funext τ
  have hτ : ((iota p t m) w) τ = ((iota p t m) w') τ := congrFun h τ
  exact Subtype.ext (congrArg (fun z : ↥(perfChartRing p t (tupRng τ)) =>
    (z : Localization.Away (tS t (tupRng τ)))) hτ)

/-- The honest inclusion is a chain map. -/
lemma PCd_iota (m : ℕ) (w : HCX t m) : PCd p t m (iota p t m w) = iota p t (m+1) (HCd t m w) := by
  funext τ
  apply Subtype.ext
  simp only [PCd_apply, HCd_apply, iota, LinearMap.coe_mk, AddHom.coe_mk,
    AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, rho_coe, rhoH_coe]
  try rfl

/-- The componentwise `p`-th power map `phiPC` commutes with the differential. -/
lemma PCd_phiPC (m : ℕ) (z : PCX p t m) :
    PCd p t m (phiPC p t m z) = phiPC p t (m + 1) (PCd p t m z) := by
  funext τ
  apply Subtype.ext
  simp only [PCd_apply, phiPC_apply, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
    Algebra.smul_def, Subalgebra.coe_algebraMap, rho_phiPC_val]
  exact (sum_smul_pow_p_away p (tS t (tupRng τ)) (m + 2)
    (fun i => ↑(rho p t (tupRng_del_subset i τ) (z (tupDel i τ))))).symm

/-- The componentwise `p`-th power map is `R`-semilinear. -/
lemma phiPC_smul (m : ℕ) (r : R) (z : PCX p t m) :
    phiPC p t m (r • z) = r ^ p • phiPC p t m z := by
  funext τ
  apply Subtype.ext
  rw [phiPC_apply, Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, mul_pow, ← map_pow,
    Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, phiPC_apply]

/-- Every element of the perfected coordinate complex has a componentwise `p`-th root there. -/
lemma phiPC_surj (m : ℕ) (z : PCX p t m) : ∃ z' : PCX p t m, phiPC p t m z' = z := by
  refine ⟨fun τ => ⟨Classical.choose (frobSurjAway p (tS t (tupRng τ)) (z τ).1), ?_⟩, ?_⟩
  · exact (perfChartRing_pow_p_mem_iff p t (tupRng τ) _).1 (by
      rw [Classical.choose_spec (frobSurjAway p (tS t (tupRng τ)) (z τ).1)]
      exact (z τ).2)
  · funext τ
    apply Subtype.ext
    rw [phiPC_apply]
    exact Classical.choose_spec (frobSurjAway p (tS t (tupRng τ)) (z τ).1)

/-- The componentwise `p`-th power map is injective. -/
lemma phiPC_inj (m : ℕ) : Function.Injective (phiPC p t m) := by
  intro z z' h
  funext τ
  apply Subtype.ext
  refine pow_injective_away p (tS t (tupRng τ)) ?_
  simpa only [phiPC_apply] using congrArg Subtype.val (congrFun h τ)

/-- The componentwise `p`-th root map of the perfected coordinate complex (the inverse of `phiPC`,
chosen by `Classical.choose` from `phiPC_surj`). -/
noncomputable def psi (m : ℕ) : PCX p t m → PCX p t m :=
  fun z => Classical.choose (phiPC_surj p t m z)

lemma phiPC_psi (m : ℕ) (z : PCX p t m) : phiPC p t m (psi p t m z) = z :=
  Classical.choose_spec (phiPC_surj p t m z)

lemma psi_phiPC (m : ℕ) (z : PCX p t m) : psi p t m (phiPC p t m z) = z :=
  phiPC_inj p t m (phiPC_psi p t m (phiPC p t m z))

/-- The root map is `R`-semilinear, with the `p`-th root of the scalar. -/
lemma psi_smul (m : ℕ) (r : R) (z : PCX p t m) :
    psi p t m (r • z) = ((frobeniusEquiv R p).symm r) • psi p t m z := by
  refine phiPC_inj p t m ?_
  rw [phiPC_psi, phiPC_smul, phiPC_psi, ← frobenius_def p ((frobeniusEquiv R p).symm r),
    frobenius_apply_frobeniusEquiv_symm R p r]

/-- The root map commutes with the differential. -/
lemma psi_PCd (m : ℕ) (z : PCX p t m) :
    psi p t (m+1) (PCd p t m z) = PCd p t m (psi p t m z) := by
  refine phiPC_inj p t (m+1) ?_
  rw [phiPC_psi, ← PCd_phiPC, phiPC_psi]

/-- The `e`-fold iterated componentwise `p`-th power map. -/
noncomputable def phiPow (m : ℕ) : ℕ → PCX p t m → PCX p t m
  | 0, z => z
  | e + 1, z => phiPC p t m (phiPow m e z)

/-- The `e`-fold iterated componentwise `p`-th root map. -/
noncomputable def psiPow (m : ℕ) : ℕ → PCX p t m → PCX p t m
  | 0, z => z
  | e + 1, z => psi p t m (psiPow m e z)

@[simp] lemma phiPow_zero (m : ℕ) (z : PCX p t m) : phiPow p t m 0 z = z := rfl

@[simp] lemma psiPow_zero (m : ℕ) (z : PCX p t m) : psiPow p t m 0 z = z := rfl

lemma phiPow_succ (m : ℕ) (e : ℕ) (z : PCX p t m) :
    phiPow p t m (e + 1) z = phiPC p t m (phiPow p t m e z) := rfl

lemma psiPow_succ (m : ℕ) (e : ℕ) (z : PCX p t m) :
    psiPow p t m (e + 1) z = psi p t m (psiPow p t m e z) := rfl

/-- Componentwise, `phiPow` is raising to the `p ^ e`-th power. -/
lemma phiPow_apply_val (m : ℕ) (e : ℕ) (z : PCX p t m) (τ : Fin (m + 1) → ι) :
    ((phiPow p t m e z) τ : Localization.Away (tS t (tupRng τ)))
      = (z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ e) := by
  induction e generalizing z with
  | zero => simp
  | succ e ih =>
      show (((phiPC p t m) (phiPow p t m e z)) τ : Localization.Away (tS t (tupRng τ)))
        = (z τ : Localization.Away (tS t (tupRng τ))) ^ (p ^ (e + 1))
      rw [phiPC_apply, ih, ← pow_mul, pow_succ]

lemma phiPow_comm (m : ℕ) (e : ℕ) (z : PCX p t m) :
    phiPow p t m (e + 1) z = phiPow p t m e (phiPC p t m z) := by
  induction e generalizing z with
  | zero => rfl
  | succ e ih =>
      show phiPC p t m (phiPow p t m (e + 1) z)
        = phiPC p t m (phiPow p t m e (phiPC p t m z))
      rw [ih]

lemma PCd_phiPow (m : ℕ) (e : ℕ) (z : PCX p t m) :
    PCd p t m (phiPow p t m e z) = phiPow p t (m + 1) e (PCd p t m z) := by
  induction e generalizing z with
  | zero => rfl
  | succ e ih =>
      show PCd p t m (phiPC p t m (phiPow p t m e z))
        = phiPC p t (m + 1) (phiPow p t (m + 1) e (PCd p t m z))
      rw [PCd_phiPC, ih]

lemma phiPow_zero_zero (m : ℕ) (e : ℕ) : phiPow p t m e (0 : PCX p t m) = 0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
      show phiPC p t m (phiPow p t m e 0) = 0
      rw [ih]
      funext τ
      apply Subtype.ext
      rw [phiPC_apply]
      simp only [Pi.zero_apply, Subalgebra.coe_zero]
      exact zero_pow (Fact.out : p.Prime).pos.ne'

lemma psiPow_phiPow (m : ℕ) (e : ℕ) (z : PCX p t m) :
    psiPow p t m e (phiPow p t m e z) = z := by
  induction e generalizing z with
  | zero => rfl
  | succ e ih =>
      show psi p t m (psiPow p t m e (phiPow p t m (e + 1) z)) = z
      rw [phiPow_comm, ih (phiPC p t m z)]
      exact psi_phiPC p t m z

/-- Iterated semilinearity of the root map. -/
lemma psiPow_smul (m : ℕ) (e : ℕ) (r : R) (z : PCX p t m) :
    psiPow p t m e (r • z) = (((frobeniusEquiv R p).symm)^[e] r) • psiPow p t m e z := by
  induction e generalizing z with
  | zero => rfl
  | succ e ih =>
      show psi p t m (psiPow p t m e (r • z))
        = (((frobeniusEquiv R p).symm)^[e + 1] r) • psi p t m (psiPow p t m e z)
      rw [ih, psi_smul, Function.iterate_succ_apply']

/-- The iterated root map commutes with the differential. -/
lemma psiPow_PCd (m : ℕ) (e : ℕ) (z : PCX p t m) :
    psiPow p t (m + 1) e (PCd p t m z) = PCd p t m (psiPow p t m e z) := by
  induction e generalizing z with
  | zero => rfl
  | succ e ih =>
      show psi p t (m + 1) (psiPow p t (m + 1) e (PCd p t m z))
        = PCd p t m (psi p t m (psiPow p t m e z))
      rw [ih, psi_PCd]

/-- The iterated root of the scalar: `(T ^ N) ^ (1/p^e) = (T ^ (1/p^e)) ^ N`. -/
lemma iterate_frobSymm_pow (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (e N : ℕ) (a : R) :
    ((frobeniusEquiv R p).symm)^[e] (a ^ N) = (((frobeniusEquiv R p).symm)^[e] a) ^ N := by
  induction e generalizing a with
  | zero => rfl
  | succ e ih =>
      simp only [Function.iterate_succ_apply]
      rw [map_pow, ih]

end Complex

/-- **Transport of uniform honest killing to root killing of the perfected complex.**

`PCX p t ·`/`PCd p t ·` is the explicit perfected chart Čech complex
(`Submission.Work.DSM5b.PerfComplexDefs.lean`), `HCX t ·`/`HCd t ·` its honest subcomplex
(`Submission.Work.DSM5b.H0Defs.lean`, `Work.DSM5b.honestPerfCompat`), `phiPC` the componentwise
`p`-th power map with inverse `ψ` (`Work.DSM5b.phiPC_properties`), `t j₀ = T^e`, and
`ϖ k = (frobeniusEquiv R p).symm^[k] T`.

Assume that the *single* power `T^N` kills all positive-degree cohomology of the honest complex
(uniformly over the degree `n` and over the cycle `w`).  Then `ϖ k` kills the positive-degree
cohomology of the *perfected* complex, for every `k`.

Route.  Let `z` be a cycle of the perfected complex in degree `n+1`.
1. *Staging*: choose `e` large enough that every component of `φ^e(z)` is honest, i.e.
   `(z τ)^{p^e} ∈ chartRing t (tupRng τ)` for all `τ` (finitely many `τ`, so the exponents can be
   maximised; `Work.DSM5b.phiPC_pow_mem_chartRing`).  By the second conjunct of
   `Work.DSM5b.honestPerfCompat` (and `φ^e(PCd z) = PCd(φ^e z) = 0`) the honest element
   `φ^e(z) ∈ HCX t (n+1)` is an honest cycle, so `T^N • φ^e(z) = HCd t n w` for some honest `w`.
2. *Transport by the root map*: apply `ψ^e` (the componentwise `p^e`-th root map, the inverse of
   `φ^e`).  It is additive and `R`-semilinear with `ψ^e(r • x) = r^{1/p^e} • ψ^e x`, and it commutes
   with the differentials (`φ` does, hence so does its inverse).  Since
   `(T^N)^{1/p^e} = (T^{1/p^e})^N = (ϖ e)^N`, this gives
   `(ϖ e)^N • z = PCd p t n (ψ^e w)`.
3. *Exponent comparison*: choose `e` (still larger if necessary, keeping 1.) with `e ≥ k` and
   `p^{e-k} ≥ N`.  Then `ϖ k = (ϖ e)^{p^{e-k}} = (ϖ e)^N · (ϖ e)^{p^{e-k} - N}` (the root tower
   `IsRootTower.frozen`, `Work.DSM5b.Basic`), so
   `ϖ k • z = PCd p t n ((ϖ e)^{p^{e-k} - N} • ψ^e w)` is a boundary in the perfected complex.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`. -/
theorem rootKillTransport (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (N : ℕ)
    (hN : ∀ (n : ℕ) (w : HCX t (n + 1)),
      HCd t (n + 1) w = 0 → T ^ N • w ∈ LinearMap.range (HCd t n)) :
    ∀ (n : ℕ) (z : PCX p t (n + 1)), PCd p t (n + 1) z = 0 → ∀ k : ℕ,
      ∃ y : PCX p t n, ((frobeniusEquiv R p).symm^[k] T) • z = PCd p t n y := by
  intro n z hz k
  classical
  have hp : p.Prime := Fact.out
  -- staging: pick the level `E` at which `z` becomes honest
  obtain ⟨e₀, he₀⟩ := phiPC_pow_mem_chartRing p t (n + 1) z
  set E : ℕ := e₀ + k + N with hE
  have hle : e₀ ≤ E := by omega
  have hmem : ∀ τ : Fin (n + 2) → ι, (z τ).1 ^ (p ^ E) ∈ chartRing t (tupRng τ) := fun τ =>
    perfChartGens_mono p t (tupRng τ) hle (he₀ τ)
  -- the honest `p ^ E`-th power family, an honest element of `HCX t (n+1)`
  set Y : HCX t (n + 1) := fun τ => ⟨(z τ).1 ^ (p ^ E), hmem τ⟩
  have hYiota : iota p t (n + 1) Y = phiPow p t (n + 1) E z := by
    funext τ
    apply Subtype.ext
    rw [phiPow_apply_val]
    rfl
  -- it is an honest cycle
  have hcycle : HCd t (n + 1) Y = 0 := by
    refine iota_injective p t (n + 2) ?_
    rw [← PCd_iota p t (n + 1) Y, hYiota, PCd_phiPow, hz, phiPow_zero_zero, map_zero]
  -- the honest killing hypothesis applies
  obtain ⟨w, hw⟩ := hN n Y hcycle
  -- transport the equation to the perfected complex
  have hEq : T ^ N • phiPow p t (n + 1) E z = PCd p t n (iota p t n w) := by
    have h1 : iota p t (n + 1) (HCd t n w) = iota p t (n + 1) (T ^ N • Y) := by rw [hw]
    rw [← PCd_iota p t n w] at h1
    rw [LinearMap.map_smul] at h1
    rw [hYiota] at h1
    exact h1.symm
  -- apply the iterated root map
  have hEq2 : (((frobeniusEquiv R p).symm)^[E] T) ^ N • z
      = PCd p t n (psiPow p t n E (iota p t n w)) := by
    have h2 := congrArg (psiPow p t (n + 1) E) hEq
    rw [psiPow_smul, psiPow_phiPow, psiPow_PCd] at h2
    rw [iterate_frobSymm_pow] at h2
    exact h2
  -- the exponent comparison
  have hkE : k ≤ E := by omega
  have hEk : E - k = e₀ + N := by omega
  have hNpow : N ≤ p ^ N :=
    le_trans (Nat.le_of_lt N.lt_two_pow_self) (pow_le_pow_left' (Fact.out : p.Prime).two_le N)
  have hNle : N ≤ p ^ (E - k) := by
    rw [hEk]
    exact le_trans hNpow (pow_le_pow_right' (le_trans (by norm_num) hp.two_le) (by omega))
  have htower : (((frobeniusEquiv R p).symm)^[E] T) ^ (p ^ (E - k))
      = ((frobeniusEquiv R p).symm)^[k] T := by
    have h := (IsRootTower.frozen p R T).pow_eq (k := E) (j := E - k) (by omega)
    rwa [Nat.sub_sub_self hkE] at h
  refine ⟨(((frobeniusEquiv R p).symm)^[E] T) ^ (p ^ (E - k) - N)
    • psiPow p t n E (iota p t n w), ?_⟩
  rw [map_smul, ← hEq2, ← htower, ← mul_smul, ← pow_add, Nat.sub_add_cancel hNle]

end Work.DSM5b

/-- **Transport of uniform honest killing to root killing of the perfected complex** — the same
statement as `Work.DSM5b.rootKillTransport` above, exposed under the name of this module
(`Submission.Work.DSM5b.rootKillTransport`, i.e. the namespace `Work.DSM5b`), which is the name the
workspace's consumers refer to. -/
theorem rootKillTransport (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) (N : ℕ)
    (hN : ∀ (n : ℕ) (w : HCX t (n + 1)),
      HCd t (n + 1) w = 0 → T ^ N • w ∈ LinearMap.range (HCd t n)) :
    ∀ (n : ℕ) (z : PCX p t (n + 1)), PCd p t (n + 1) z = 0 → ∀ k : ℕ,
      ∃ y : PCX p t n, ((frobeniusEquiv R p).symm^[k] T) • z = PCd p t n y :=
  _root_.Work.DSM5b.Work.DSM5b.rootKillTransport p t T j₀ e hj₀ N hN

end Work.DSM5b
