import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.area_M2pos_of_inputs
import Submission.Work.DSM2p.rootElementPos_aeval
import Submission.Work.DSM2p.adicCompletion_eq_zero_of_mem_pow

/-!
# `Work.DSM2p.CSCompletionOne_perfectoidData`

The requested lemma is the *single-polynomial* analogue of
`Work.DSM2p.area_M2pos_of_inputs_sameUniverse` (see `area_M2pos_of_inputs.lean`), on the ring

`B_F = CSCompletionOne A p (P.ϖ 0) F = AdicCompletion (p) A'_F`,
`A'_F = CSIntegralClosureOne A p (P.ϖ 0) F = pIntClosure p (CSAlgOne A p (P.ϖ 0) F)`

of `One.lean`.  Unlike the older request, the ring on which the `PerfectoidData` structure is
built is *named explicitly* (it is `CSCompletionOne A p (P.ϖ 0) F`, no existential over an
independent universe), so there is no universe defect here: the statement is well posed.

Given

* `h1` — Frobenius surjectivity of `B_F` modulo `ϖ ^ p` (ČS `p-oid-rec`);
* `h3` — Frobenius injectivity of `B_F` modulo `ϖ ^ p`;
* `hsmu` — `p`-torsion-freeness of `B_F`,

the proof assembles the `PerfectoidData` structure on `B_F` with pseudo-uniformizer the image of
`P.ϖ`, exactly as in `area_M2pos_of_inputs_sameUniverse`:

* `root`, `unit` are `P.root`, `P.unit` transported along `algebraMap A B_F`;
* `torsionFree` is `hsmu`;
* `complete` is `CSCompletionOne_isAdicComplete`, transported along the identification
  `(p) B_F = (p) A'_F · B_F` (`IsAdicComplete.map_algebraMap_iff`);
* `frobSurj`, `frobInj` are `h1`, `h3`, using that `(algebraMap A B_F (P.ϖ 0 ^ p)) = (p)` in
  `B_F` because `P.ϖ 0 ^ p = p · u` with `u` a unit of `A`.

The roots clause uses the compatible system `rootElementOneK A p (P.ϖ 0) F` of `p`-power roots of
`T` in `B_F` (`One.lean`), whose `aeval` relation `aeval (rootElementOneK … 0) F = 0` is proved
here (`rootElementOne_zero_aeval`) by the same computation as `rootElementPos_aeval`: in `A'_F`
the element `F(T)` is divisible by every power of `p`, hence dies in the `p`-adic completion.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## `F(T)` vanishes at the root `T ∈ B_F` -/

/-- The inclusion `A'_F ⊆ Λ[1/ϖ]` for the one-polynomial construction, as an `A`-algebra
homomorphism.  The `A`-algebra structure on `A'_F = CSIntegralClosureOne A p ϖ F` is the one
defined in `LamOne.lean` (the restriction of `A → Λ → Λ[1/ϖ]`), so the subtype inclusion is an
`A`-algebra map. -/
noncomputable def csInclAlgHomOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    CSIntegralClosureOne A p ϖ F →ₐ[A] Lam1Loc A p ϖ where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

/-- `F(T)`, computed in `A'_F`, agrees with `F(T)` computed in `Λ[1/ϖ]`. -/
theorem aeval_TOneInClosure_val (A : Type u) [CommRing A] (p : ℕ) (ϖ : A) (F : Polynomial A) :
    ((Polynomial.aeval (TOneInClosure A p ϖ F) F : CSIntegralClosureOne A p ϖ F) :
        Lam1Loc A p ϖ)
      = Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F :=
  (Polynomial.aeval_algHom_apply (csInclAlgHomOne A p ϖ F) (TOneInClosure A p ϖ F) F).symm

/-- `F(T) / ϖ^m` lies in `A_∞ = CSAlgOne A p ϖ F ⊆ Λ[1/ϖ]` for every `m`. -/
theorem aeval_T1_zero_mul_invSelf_pow_mem_CSAlgOne (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) (m : ℕ) :
    Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F *
        (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ m ∈ CSAlgOne A p ϖ F := by
  rw [← IsScalarTower.toAlgHom_apply A (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)]
  rw [Polynomial.aeval_algHom_apply]
  exact frac_aeval_T1_zero_mem_CSAlgOne A p ϖ F m

/-- **The divisibility that makes `F(T)` vanish in the `p`-adic completion.**  If
`ϖ ^ p = p · u` with `u` a unit, then `p ^ n` divides `F(T)` in `A'_F` for every `n`. -/
theorem p_pow_dvd_aeval_TOneInClosure (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (hunit : ∃ u : Aˣ, ϖ ^ p = (p : A) * u) (F : Polynomial A) (n : ℕ) :
    (p : CSIntegralClosureOne A p ϖ F) ^ n ∣
      Polynomial.aeval (TOneInClosure A p ϖ F) F := by
  obtain ⟨u, hu⟩ := hunit
  have hpA : (p : A) = ϖ ^ p * (↑(u⁻¹) : A) := by
    rw [hu, mul_assoc, Units.mul_inv, mul_one]
  have hmemR : Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F *
      (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ (p * n)
      ∈ CSIntegralClosureOne A p ϖ F :=
    CSAlgOne_le_CSIntegralClosureOne A p ϖ F
      (aeval_T1_zero_mul_invSelf_pow_mem_CSAlgOne A p ϖ F (p * n))
  refine dvd_def.mpr ⟨(algebraMap A (CSIntegralClosureOne A p ϖ F) (↑u : A)) ^ n *
      ⟨Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F *
        (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ (p * n), hmemR⟩, ?_⟩
  apply Subtype.ext
  rw [aeval_TOneInClosure_val A p ϖ F]
  push_cast
  rw [show ((p : Lam1Loc A p ϖ)) = algebraMap A (Lam1Loc A p ϖ) (p : A)
      from (map_natCast _ p).symm]
  rw [show (↑((algebraMap A (CSIntegralClosureOne A p ϖ F) (↑u : A))) : Lam1Loc A p ϖ)
      = algebraMap A (Lam1Loc A p ϖ) (↑u : A) from rfl]
  have hsinv : algebraMap A (Lam1Loc A p ϖ) ϖ *
      IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ) = 1 := by
    rw [IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p ϖ) ϖ]
    exact IsLocalization.Away.mul_invSelf _
  have huL : algebraMap A (Lam1Loc A p ϖ) (↑(u⁻¹) : A) *
      algebraMap A (Lam1Loc A p ϖ) (↑u : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hpA, map_mul, map_pow, mul_pow, ← pow_mul]
  have hbc : (algebraMap A (Lam1Loc A p ϖ) (↑(u⁻¹) : A)) ^ n *
      (algebraMap A (Lam1Loc A p ϖ) (↑u : A)) ^ n = 1 := by
    rw [← mul_pow, huL, one_pow]
  have hai : (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ (p * n) *
      (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ (p * n) = 1 := by
    rw [← mul_pow, hsinv, one_pow]
  rw [show (algebraMap A (Lam1Loc A p ϖ) ϖ) ^ (p * n) *
        (algebraMap A (Lam1Loc A p ϖ) (↑(u⁻¹) : A)) ^ n *
        ((algebraMap A (Lam1Loc A p ϖ) (↑u : A)) ^ n *
          (Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F *
           (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ (p * n)))
      = ((algebraMap A (Lam1Loc A p ϖ) ϖ) ^ (p * n) *
         (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) ^ (p * n)) *
        ((algebraMap A (Lam1Loc A p ϖ) (↑(u⁻¹) : A)) ^ n *
         (algebraMap A (Lam1Loc A p ϖ) (↑u : A)) ^ n) *
        Polynomial.aeval (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) (T1 A p 0)) F from by ring]
  rw [hai, hbc, mul_one, one_mul]

/-- **The roots clause, at the root `T_F^{1/p^k}` of `One.lean`.**  In
`B_F = AdicCompletion (p) A'_F` the image of `T = T_F^{1/p^0}` is a root of `F`. -/
theorem rootElementOne_zero_aeval (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (hunit : ∃ u : Aˣ, ϖ ^ p = (p : A) * u) (F : Polynomial A) :
    Polynomial.aeval (rootElementOneK A p ϖ F 0) F = 0 := by
  have hmain : ∀ n : ℕ, Polynomial.aeval (TOneInClosure A p ϖ F) F ∈
      (Ideal.span {(p : CSIntegralClosureOne A p ϖ F)}) ^ n := by
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact p_pow_dvd_aeval_TOneInClosure A p ϖ hunit F n
  have hzero : AdicCompletion.of (Ideal.span {(p : CSIntegralClosureOne A p ϖ F)})
      (CSIntegralClosureOne A p ϖ F) (Polynomial.aeval (TOneInClosure A p ϖ F) F) = 0 :=
    adicCompletion_eq_zero_of_mem_pow _ hmain
  show Polynomial.aeval (algebraMap (CSIntegralClosureOne A p ϖ F) (CSCompletionOne A p ϖ F)
    (TOneInClosure A p ϖ F)) F = 0
  have hbridge : Polynomial.aeval (algebraMap (CSIntegralClosureOne A p ϖ F)
        (CSCompletionOne A p ϖ F) (TOneInClosure A p ϖ F)) F
      = AdicCompletion.of (Ideal.span {(p : CSIntegralClosureOne A p ϖ F)})
        (CSIntegralClosureOne A p ϖ F)
        (Polynomial.aeval (TOneInClosure A p ϖ F) F) := by
    trans (IsScalarTower.toAlgHom A (CSIntegralClosureOne A p ϖ F) (CSCompletionOne A p ϖ F))
        (Polynomial.aeval (TOneInClosure A p ϖ F) F)
    · exact Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom A (CSIntegralClosureOne A p ϖ F) (CSCompletionOne A p ϖ F))
        (TOneInClosure A p ϖ F) F
    · show algebraMap (CSIntegralClosureOne A p ϖ F) (CSCompletionOne A p ϖ F)
        (Polynomial.aeval (TOneInClosure A p ϖ F) F) = _
      rw [AdicCompletion.algebraMap_apply]
      rfl
  rw [hbridge]
  exact hzero

/-! ## The requested lemma -/

theorem CSCompletionOne_perfectoidData (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (hFd : 0 < F.natDegree)
    (h1 : ∀ x : CSCompletionOne A p (P.ϖ 0) F, ∃ y : CSCompletionOne A p (P.ϖ 0) F,
      x - y ^ p ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)})
    (h3 : ∀ x : CSCompletionOne A p (P.ϖ 0) F,
      x ^ p ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)} →
      x ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0)})
    (hsmu : IsSMulRegular (CSCompletionOne A p (P.ϖ 0) F) (p : CSCompletionOne A p (P.ϖ 0) F)) :
    ∃ Q : DSMap.PerfectoidData p (CSCompletionOne A p (P.ϖ 0) F),
      (∀ k, Q.ϖ k = algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ k)) ∧
      (∃ r : ℕ → CSCompletionOne A p (P.ϖ 0) F,
        Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k) := by
  -- In `B_F`, the ideal generated by the image of `P.ϖ 0 ^ p` is the ideal generated by `p`,
  -- because `P.ϖ 0 ^ p = p · u` with `u` a unit of `A`.
  have hspan : Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)
        = (p : CSCompletionOne A p (P.ϖ 0) F)
          * algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `B_F` is `p`-adically complete: this is `p`-adic completeness of `A'_F`, transported along
  -- `A'_F → B_F` under the identification `(p) B_F = (p) A'_F · B_F`.
  have hcomplete : IsAdicComplete (Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)})
      (CSCompletionOne A p (P.ϖ 0) F) := by
    have hmap : (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)}).map
        (algebraMap (CSIntegralClosureOne A p (P.ϖ 0) F) (CSCompletionOne A p (P.ϖ 0) F))
        = Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← hmap]
    exact (IsAdicComplete.map_algebraMap_iff
        (Ideal.span {(p : CSIntegralClosureOne A p (P.ϖ 0) F)})
        (CSCompletionOne A p (P.ϖ 0) F)).mpr (CSCompletionOne_isAdicComplete A p (P.ϖ 0) F)
  let Q : DSMap.PerfectoidData p (CSCompletionOne A p (P.ϖ 0) F) :=
    { ϖ := fun k => algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ k)
      root := fun k => by
        show (algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ (k + 1))) ^ p
          = algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ k)
        rw [← map_pow, P.root k]
      unit := by
        obtain ⟨v, hv⟩ := P.unit
        refine ⟨Units.map (algebraMap A (CSCompletionOne A p (P.ϖ 0) F)) v, ?_⟩
        show (algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0)) ^ p
          = (p : CSCompletionOne A p (P.ϖ 0) F)
            * algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (↑v : A)
        rw [← map_pow, hv, map_mul, map_natCast]
      torsionFree := hsmu
      complete := hcomplete
      frobSurj := fun x => by
        obtain ⟨y, hy⟩ := h1 x
        exact ⟨y, by rwa [hspan] at hy⟩
      frobInj := fun y hy => h3 y (by rwa [← hspan] at hy) }
  refine ⟨Q, fun k => rfl, fun k => rootElementOneK A p (P.ϖ 0) F k, ?_, ?_⟩
  · exact rootElementOne_zero_aeval A p (P.ϖ 0) P.unit F
  · intro k
    exact rootElementOneK_pow A p (P.ϖ 0) F k

end Work.DSM2p
