/-
The analytic comparison of the two *truncated* Euler products which occur in the Čebotarev
chapter: `NK.HeckeL.zetaUnramified K L S` (the Euler product of `L` over the primes that do not
lie over the modulus `S`) and `NK.HeckeL.zetaUnramifiedK K S` (the Euler product of `K` over the
primes outside `S`).  We prove that their quotient has a *limit* as `s → 1⁺`, and that the limit is
a positive real number.

The value of the limit is **not** `Res_{s=1} ζ_L / Res_{s=1} ζ_K`: deleting the Euler factors at
`S` on both sides changes the limit by the finite correction
`∏_{𝔭 ∈ S} (1 - N𝔭^{-1})^{-1} / ∏_{𝔮 | S} (1 - N𝔮^{-1})^{-1}`,
which need not be `1`.  Only the *existence* of a positive limit is needed, and that is what we
prove.

The argument is the standard one.

* On `s > 1` both truncated products are the full Euler product of the corresponding Dedekind zeta
  function divided by the *finite* product of the factors that were deleted
  (`zetaEulerFactor_prod_mul_zetaUnramified`, `zetaEulerFactor_prod_mul_zetaUnramifiedK`); the
  product identities for the full Euler products are the proved Euler products
  `dedekindZeta_eulerProduct` of the chapter.
* Hence the quotient is `(ζ_L(s)/ζ_K(s)) · (finite correction)`.
* `(s - 1) ζ_K(s)` tends to the (positive) residue of `ζ_K` at `s = 1`
  (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), so `ζ_L(s)/ζ_K(s)` tends to
  `Res_{s=1} ζ_L / Res_{s=1} ζ_K > 0`.
* The correction is a finite product of continuous functions, so it tends to its value at `s = 1`,
  which is a positive real number.
* The product of the two limits is the required positive `c`.

The hypothesis `hS` of the statement (that `S` contains the ramified primes) is *not* used: the
existence of the limit holds for every finite `S`.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Product.dedekindZeta_eulerProduct

open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators Topology
open Commons.NumberTheory.NumberField.DedekindZeta

noncomputable section

namespace NK.HeckeL.Product

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The Euler factors -/

/-- The complex Euler factor `(1 - N𝔭^{-s})⁻¹` at a finite place `𝔭`. -/
noncomputable def zetaEulerFactor (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) (s : ℝ) : ℂ :=
  ((localFactor K s 𝔭.asIdeal : ℝ) : ℂ)

theorem zetaEulerFactor_apply (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) (s : ℝ) :
    zetaEulerFactor K 𝔭 s = (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
  rw [zetaEulerFactor, localFactor, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]

/-- The local Euler factor is positive on the half line `s > 0`. -/
theorem localFactor_pos {K : Type*} [Field K] [NumberField K] {s : ℝ} (hs : 0 < s)
    (𝔭 : NK.HeckeL.PrimeIdeal K) : 0 < localFactor K s 𝔭.asIdeal := by
  rw [localFactor]
  exact inv_pos.mpr (by linarith [rpow_neg_absNorm_primeIdeal_lt_one (K := K) hs 𝔭])

theorem localFactor_ne_zero {K : Type*} [Field K] [NumberField K] {s : ℝ} (hs : 0 < s)
    (𝔭 : NK.HeckeL.PrimeIdeal K) : localFactor K s 𝔭.asIdeal ≠ 0 :=
  ne_of_gt (localFactor_pos hs 𝔭)

theorem zetaEulerFactor_ne_zero {K : Type*} [Field K] [NumberField K] {s : ℝ} (hs : 0 < s)
    (𝔭 : NK.HeckeL.PrimeIdeal K) : zetaEulerFactor K 𝔭 s ≠ 0 := by
  rw [zetaEulerFactor]
  exact fun h => localFactor_ne_zero hs 𝔭 (Complex.ofReal_injective h)

/-- **Multipliability of the Euler product over any set of places**, `s > 1`: the logarithms of
the (positive) local factors are summable, and `exp` of the sum is the product. -/
theorem multipliable_zetaEulerFactor_subtype (K : Type*) [Field K] [NumberField K] {s : ℝ}
    (hs : 1 < s) (p : NK.HeckeL.PrimeIdeal K → Prop) :
    Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // p 𝔭} => zetaEulerFactor K 𝔭.1 s) := by
  have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
  have hlog : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // p 𝔭} =>
      Real.log (localFactor K s 𝔭.1.asIdeal)) :=
    (summable_log_localFactor (K := K) hs).subtype p
  have hm : Multipliable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // p 𝔭} =>
      localFactor K s 𝔭.1.asIdeal) :=
    Real.multipliable_of_summable_log (fun 𝔭 => localFactor_pos hs0 𝔭.1) hlog
  have hmap := hm.map Complex.ofRealHom Complex.continuous_ofReal
  simpa [zetaEulerFactor, Function.comp_def] using hmap

/-- The truncated Euler product of `K` is the product over the primes outside `S` of the Euler
factors. -/
theorem zetaUnramifiedK_eq_eulerFactor (S : Finset (NK.HeckeL.PrimeIdeal K)) (s : ℝ) :
    zetaUnramifiedK K S s =
      ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, zetaEulerFactor K 𝔭.1 s := by
  rw [NK.HeckeL.zetaUnramifiedK]
  exact tprod_congr fun 𝔭 => (zetaEulerFactor_apply K 𝔭.1 s).symm

/-- The truncated Euler product of `L` is the product over the primes of `L` that do not lie over
any prime of `S`, of the Euler factors. -/
theorem zetaUnramified_eq_eulerFactor (S : Finset (NK.HeckeL.PrimeIdeal K)) (s : ℝ) :
    zetaUnramified K L S s =
      ∏' 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L // ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal},
        zetaEulerFactor L 𝔮.1 s := by
  rw [NK.HeckeL.zetaUnramified]
  exact tprod_congr fun 𝔮 => (zetaEulerFactor_apply L 𝔮.1 s).symm

/-! ## The finite set of primes above the modulus -/

/-- The primes of `L` lying over a prime in `S`. -/
def overS (S : Finset (NK.HeckeL.PrimeIdeal K)) : Set (NK.HeckeL.PrimeIdeal L) :=
  {𝔮 | ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal}

/-- Only finitely many primes of `L` lie over a given prime of `K`. -/
theorem finite_setOf_liesOver (Q : NK.HeckeL.PrimeIdeal K) :
    Set.Finite {𝔮 : NK.HeckeL.PrimeIdeal L | 𝔮.asIdeal.LiesOver Q.asIdeal} := by
  haveI : Q.asIdeal.IsMaximal := inferInstance
  have hfin : (Q.asIdeal.primesOver (𝓞 L)).Finite :=
    IsDedekindDomain.primesOver_finite Q.asIdeal (𝓞 L)
  refine Set.Finite.of_finite_image (f := fun 𝔮 : NK.HeckeL.PrimeIdeal L => 𝔮.asIdeal)
    (hfin.subset ?_) ?_
  · rintro P ⟨𝔮, h𝔮, rfl⟩
    exact ⟨𝔮.isPrime, h𝔮⟩
  · intro 𝔮 _ 𝔮' _ h
    exact HeightOneSpectrum.ext h

/-- Only finitely many primes of `L` lie over the (finite) modulus `S`. -/
theorem finite_overS (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    (overS (K := K) (L := L) S).Finite := by
  classical
  have heq : overS (K := K) (L := L) S =
      ⋃ Q ∈ (S : Set (NK.HeckeL.PrimeIdeal K)),
        {𝔮 : NK.HeckeL.PrimeIdeal L | 𝔮.asIdeal.LiesOver Q.asIdeal} := by
    ext 𝔮
    simp only [overS, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
  rw [heq]
  exact (Finset.finite_toSet S).biUnion fun Q _ => finite_setOf_liesOver (K := K) (L := L) Q

/-- The primes of `L` above the modulus can be listed by a finset. -/
theorem exists_primesOver_finset (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    ∃ T : Finset (NK.HeckeL.PrimeIdeal L),
      ∀ 𝔮 : NK.HeckeL.PrimeIdeal L, 𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal := by
  classical
  refine ⟨(finite_overS (K := K) (L := L) S).toFinset, fun 𝔮 => ?_⟩
  rw [Set.Finite.mem_toFinset]
  rfl

/-! ## Splitting an infinite product along a finite set -/

/-- **Splitting an infinite product along a finite set**: if both the product over a finite set
`T` and the product over its complement converge, then their product is the full product. -/
theorem tprod_finset_mul_tprod_compl {β M : Type*} [CommMonoid M] [TopologicalSpace M]
    [T2Space M] [ContinuousMul M] {f : β → M} {T : Finset β}
    (h1 : Multipliable (fun x : ↑(T : Set β) => f x))
    (h2 : Multipliable (fun x : ↑((T : Set β)ᶜ) => f x)) :
    (∏ x ∈ T, f x) * (∏' x : ↑((T : Set β)ᶜ), f x) = ∏' x, f x := by
  rw [← Finset.tprod_subtype' T f]
  exact Multipliable.tprod_mul_tprod_compl h1 h2

/-! ## The finite correction factors -/

/-- The finite product `∏_{𝔭 ∈ T} (1 - N𝔭^{-s})⁻¹` of the real local factors over a finset of
primes; for `T = S` it is the correction at the primes of the modulus, for `T` the primes of `L`
above `S` it is the correction on the `L`-side. -/
noncomputable def corr (T : Finset (NK.HeckeL.PrimeIdeal K)) (s : ℝ) : ℝ :=
  ∏ 𝔭 ∈ T, localFactor K s 𝔭.asIdeal

theorem corr_pos {T : Finset (NK.HeckeL.PrimeIdeal K)} {s : ℝ} (hs : 0 < s) : 0 < corr T s :=
  Finset.prod_pos fun 𝔭 _ => localFactor_pos hs 𝔭

theorem corr_ne_zero {T : Finset (NK.HeckeL.PrimeIdeal K)} {s : ℝ} (hs : 0 < s) :
    corr T s ≠ 0 :=
  ne_of_gt (corr_pos hs)

/-- Each local factor is continuous at `s = 1`. -/
theorem continuousAt_localFactor (K : Type*) [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) :
    ContinuousAt (fun s : ℝ => localFactor K s 𝔭.asIdeal) 1 := by
  have hN : (Ideal.absNorm 𝔭.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast absNorm_primeIdeal_ne_zero 𝔭
  have hcont : ContinuousAt (fun s : ℝ => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) 1 :=
    (Real.continuousAt_const_rpow hN).comp continuous_neg.continuousAt
  have hlt : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ)) < 1 :=
    rpow_neg_absNorm_primeIdeal_lt_one (K := K) one_pos 𝔭
  have hne : (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ))) ≠ 0 := by linarith
  show ContinuousAt (fun s : ℝ => (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))⁻¹) 1
  exact (continuousAt_const.sub hcont).inv₀ hne

/-- The finite correction factor is continuous at `s = 1`. -/
theorem continuousAt_corr (T : Finset (NK.HeckeL.PrimeIdeal K)) :
    ContinuousAt (fun s : ℝ => corr T s) 1 :=
  tendsto_finsetProd T fun 𝔭 _ => (continuousAt_localFactor K 𝔭).tendsto

/-- The finite product of Euler factors is the coercion of the finite product of the (real) local
factors. -/
theorem prod_zetaEulerFactor_eq_ofReal (K : Type*) [Field K] [NumberField K]
    (T : Finset (NK.HeckeL.PrimeIdeal K)) (s : ℝ) :
    (∏ 𝔭 ∈ T, zetaEulerFactor K 𝔭 s) = ((corr T s : ℝ) : ℂ) := by
  rw [corr]
  push_cast
  exact Finset.prod_congr rfl fun 𝔭 _ => rfl

theorem prod_zetaEulerFactor_ne_zero {T : Finset (NK.HeckeL.PrimeIdeal K)} {s : ℝ}
    (hs : 0 < s) : (∏ 𝔭 ∈ T, zetaEulerFactor K 𝔭 s) ≠ 0 := by
  rw [prod_zetaEulerFactor_eq_ofReal]
  exact fun h => corr_ne_zero (K := K) hs (Complex.ofReal_injective h)

/-! ## The full Euler products, divided by the deleted factors -/

/-- On `s > 1`, the truncated Euler product of `L` at the modulus `S` is the Euler product of the
Dedekind zeta function of `L` divided by the deleted factors. -/
theorem zetaEulerFactor_prod_mul_zetaUnramified {S : Finset (NK.HeckeL.PrimeIdeal K)}
    {T : Finset (NK.HeckeL.PrimeIdeal L)}
    (hT : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L,
      𝔮 ∈ T ↔ ∃ Q ∈ S, 𝔮.asIdeal.LiesOver Q.asIdeal) {s : ℝ} (hs : 1 < s) :
    (∏ 𝔮 ∈ T, zetaEulerFactor L 𝔮 s) * zetaUnramified K L S s =
      ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by
  have hiff : ∀ 𝔮 : NK.HeckeL.PrimeIdeal L,
      𝔮 ∈ ((T : Set (NK.HeckeL.PrimeIdeal L))ᶜ) ↔
        ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal := by
    intro 𝔮
    rw [Set.mem_compl_iff, Finset.mem_coe, hT 𝔮]
    exact ⟨fun h Q hQ hLQ => h ⟨Q, hQ, hLQ⟩, fun h ⟨Q, hQ, hLQ⟩ => h Q hQ hLQ⟩
  have heq : (∏' 𝔮 : ↑((T : Set (NK.HeckeL.PrimeIdeal L))ᶜ), zetaEulerFactor L 𝔮 s) =
      zetaUnramified K L S s := by
    rw [zetaUnramified_eq_eulerFactor (K := K) (L := L) S s]
    refine (tprod_congr (fun 𝔮 : ↑((T : Set (NK.HeckeL.PrimeIdeal L))ᶜ) => ?_)).trans
      (Equiv.tprod_eq (Equiv.subtypeEquivRight hiff) (fun 𝔮 : {𝔮 : NK.HeckeL.PrimeIdeal L //
        ∀ Q ∈ S, ¬ 𝔮.asIdeal.LiesOver Q.asIdeal} => zetaEulerFactor L 𝔮.1 s))
    rfl
  have hsplit := tprod_finset_mul_tprod_compl
    (f := fun 𝔮 : NK.HeckeL.PrimeIdeal L => zetaEulerFactor L 𝔮 s) (T := T)
    ⟨_, hasProd_fintype _⟩
    (multipliable_zetaEulerFactor_subtype L hs
      fun x => x ∈ (T : Set (NK.HeckeL.PrimeIdeal L))ᶜ)
  rw [heq] at hsplit
  refine hsplit.trans ?_
  have hfull : (∏' 𝔮 : NK.HeckeL.PrimeIdeal L,
      (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) =
      ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := dedekindZeta_eulerProduct (K := L) hs
  exact (tprod_congr fun 𝔮 => zetaEulerFactor_apply L 𝔮 s).trans hfull

/-- On `s > 1`, the truncated Euler product of `K` at the modulus `S` is the Euler product of the
Dedekind zeta function of `K` divided by the deleted factors. -/
theorem zetaEulerFactor_prod_mul_zetaUnramifiedK (S : Finset (NK.HeckeL.PrimeIdeal K))
    {s : ℝ} (hs : 1 < s) :
    (∏ 𝔭 ∈ S, zetaEulerFactor K 𝔭 s) * zetaUnramifiedK K S s =
      ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := by
  have hiff : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K,
      𝔭 ∈ ((S : Set (NK.HeckeL.PrimeIdeal K))ᶜ) ↔ 𝔭 ∉ S := by
    intro 𝔭
    rw [Set.mem_compl_iff, Finset.mem_coe]
  have heq : (∏' 𝔭 : ↑((S : Set (NK.HeckeL.PrimeIdeal K))ᶜ), zetaEulerFactor K 𝔭 s) =
      zetaUnramifiedK K S s := by
    rw [zetaUnramifiedK_eq_eulerFactor (K := K) S s]
    refine (tprod_congr (fun 𝔭 : ↑((S : Set (NK.HeckeL.PrimeIdeal K))ᶜ) => ?_)).trans
      (Equiv.tprod_eq (Equiv.subtypeEquivRight hiff)
        (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} => zetaEulerFactor K 𝔭.1 s))
    rfl
  have hsplit := tprod_finset_mul_tprod_compl
    (f := fun 𝔭 : NK.HeckeL.PrimeIdeal K => zetaEulerFactor K 𝔭 s) (T := S)
    ⟨_, hasProd_fintype _⟩
    (multipliable_zetaEulerFactor_subtype K hs fun x => x ∈ (S : Set (NK.HeckeL.PrimeIdeal K))ᶜ)
  rw [heq] at hsplit
  refine hsplit.trans ?_
  have hfull : (∏' 𝔭 : NK.HeckeL.PrimeIdeal K,
      (1 - (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) =
      ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) := dedekindZeta_eulerProduct (K := K) hs
  exact (tprod_congr fun 𝔭 => zetaEulerFactor_apply K 𝔭 s).trans hfull

/-! ## Positivity and the limit of the quotient of Dedekind zeta functions -/

/-- The Dedekind zeta function is positive on the real axis to the right of `1`. -/
theorem dedekindZeta_re_pos (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    0 < (NumberField.dedekindZeta K (s : ℂ)).re := by
  rw [logEuler_dedekindZeta_re_eq_tsum (K := K) hs]
  have hsumm := summable_zetaTerm (K := K) hs
  have h1 : zetaTerm K s 1 = 1 := by
    have hc := Commons.NumberTheory.NumberField.card_absNorm_eq_one (K := K)
    simp only [zetaTerm, hc, Nat.cast_one, Real.one_rpow, mul_one]
  exact Summable.tsum_pos hsumm
    (fun n => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) 1
    (by rw [h1]; norm_num)

/-- **The quotient of the Dedekind zeta functions of `L` and `K` tends to the quotient of their
residues at `s = 1`.** -/
theorem tendsto_dedekindZeta_re_div (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] :
    Tendsto
      (fun s : ℝ =>
        (NumberField.dedekindZeta L (s : ℂ)).re / (NumberField.dedekindZeta K (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (𝓝 (NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K)) := by
  have hL : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta L (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (NumberField.dedekindZeta_residue L)) := by
    have h := (Complex.continuous_re.tendsto
      ((NumberField.dedekindZeta_residue L : ℝ) : ℂ)).comp
        (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT L)
    simp only [Complex.ofReal_re] at h
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hK : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)).comp
        (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    simp only [Complex.ofReal_re] at h
    refine h.congr fun s => ?_
    simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  refine (hL.div hK (ne_of_gt (NumberField.dedekindZeta_residue_pos K))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hs1 : s - 1 ≠ 0 := by linarith
  exact mul_div_mul_left _ _ hs1

/-! ## The algebra of the comparison -/

theorem eq_mul_inv_of_mul_eq {M : Type*} [Field M] {a b c : M} (h : b * a = c)
    (hb : b ≠ 0) : a = c * b⁻¹ := by
  rw [← h, mul_comm b a, mul_assoc, mul_inv_cancel₀ hb, mul_one]

theorem div_mul_inv_div {M : Type*} [Field M] {a b c d : M} (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) : (a * b⁻¹) / (c * d⁻¹) = a / c * (d * b⁻¹) := by
  field_simp

/-! ## The main theorem -/

theorem tendsto_zetaUnramified_div {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto (fun s : ℝ => NK.HeckeL.zetaUnramified K L S s /
      NK.HeckeL.zetaUnramifiedK K S s) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds c) := by
  classical
  obtain ⟨T, hT⟩ := exists_primesOver_finset (K := K) (L := L) S
  refine ⟨NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K *
    (corr S 1 * (corr T 1)⁻¹), ?_, ?_⟩
  · exact mul_pos
      (div_pos (NumberField.dedekindZeta_residue_pos L) (NumberField.dedekindZeta_residue_pos K))
      (mul_pos (corr_pos (K := K) one_pos) (inv_pos.mpr (corr_pos (K := L) one_pos)))
  · have hlimK : Tendsto (fun s : ℝ => corr (K := K) S s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (corr (K := K) S 1)) :=
      (continuousAt_corr (K := K) S).tendsto.mono_left nhdsWithin_le_nhds
    have hlimL : Tendsto (fun s : ℝ => corr (K := L) T s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (corr (K := L) T 1)) :=
      (continuousAt_corr (K := L) T).tendsto.mono_left nhdsWithin_le_nhds
    have hcorr1 : corr (K := L) T 1 ≠ 0 := corr_ne_zero (K := L) one_pos
    have hlimR : Tendsto
        (fun s : ℝ =>
          (NumberField.dedekindZeta L (s : ℂ)).re / (NumberField.dedekindZeta K (s : ℂ)).re *
            (corr (K := K) S s * (corr (K := L) T s)⁻¹))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (𝓝 (NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K *
          (corr (K := K) S 1 * (corr (K := L) T 1)⁻¹))) :=
      (tendsto_dedekindZeta_re_div K L).mul (hlimK.mul (hlimL.inv₀ hcorr1))
    have hlimC := (Complex.continuous_ofReal.tendsto _).comp hlimR
    refine hlimC.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    symm
    have hs0 : (0 : ℝ) < s := lt_trans zero_lt_one hs
    have hPLne : (∏ 𝔮 ∈ T, zetaEulerFactor L 𝔮 s) ≠ 0 := prod_zetaEulerFactor_ne_zero hs0
    have hPKne : (∏ 𝔭 ∈ S, zetaEulerFactor K 𝔭 s) ≠ 0 := prod_zetaEulerFactor_ne_zero hs0
    have hhL := zetaEulerFactor_prod_mul_zetaUnramified (K := K) (L := L) (S := S) (T := T) hT hs
    have hhK := zetaEulerFactor_prod_mul_zetaUnramifiedK (K := K) (S := S) hs
    have hzL : zetaUnramified K L S s =
        ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) *
          (∏ 𝔮 ∈ T, zetaEulerFactor L 𝔮 s)⁻¹ :=
      eq_mul_inv_of_mul_eq hhL hPLne
    have hzK : zetaUnramifiedK K S s =
        ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) *
          (∏ 𝔭 ∈ S, zetaEulerFactor K 𝔭 s)⁻¹ :=
      eq_mul_inv_of_mul_eq hhK hPKne
    have hzeKne : (((NumberField.dedekindZeta K (s : ℂ)).re : ℝ) : ℂ) ≠ 0 :=
      fun h => (ne_of_gt (dedekindZeta_re_pos K hs)) (Complex.ofReal_injective h)
    calc zetaUnramified K L S s / zetaUnramifiedK K S s
        = (((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) *
              (∏ 𝔮 ∈ T, zetaEulerFactor L 𝔮 s)⁻¹) /
            (((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) *
              (∏ 𝔭 ∈ S, zetaEulerFactor K 𝔭 s)⁻¹) := by rw [hzL, hzK]
      _ = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) /
            ((NumberField.dedekindZeta K (s : ℂ)).re : ℂ) *
            ((∏ 𝔭 ∈ S, zetaEulerFactor K 𝔭 s) *
              (∏ 𝔮 ∈ T, zetaEulerFactor L 𝔮 s)⁻¹) :=
          div_mul_inv_div hPLne hzeKne hPKne
      _ = (((NumberField.dedekindZeta L (s : ℂ)).re /
              (NumberField.dedekindZeta K (s : ℂ)).re *
              (corr (K := K) S s * (corr (K := L) T s)⁻¹) : ℝ) : ℂ) := by
          rw [prod_zetaEulerFactor_eq_ofReal K S s, prod_zetaEulerFactor_eq_ofReal L T s,
            corr, corr]
          push_cast
          ring

end NK.HeckeL.Product
