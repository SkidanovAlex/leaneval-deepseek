import Mathlib
import Submission.Work.SSGRoute.H9.NarrowMu2
import Submission.Work.SSGRoute.EscapeCoreLib.readOffSupPow
import Submission.Work.SSGRoute.step4_y_escape_v2.CorrectionSupPow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *narrow* read-off of the `p = 2` escape correction

`Work.H9Narrow.readOff_narrow` is `Work.SSGRoute.EscapeCoreLib.readOffSupPow` for the *narrow*
modulus `Work.SSGRoute.H9.narrowGesU`, at `p = 2`, with the additional conclusion that the read-off
element `γ` is **totally positive**.

The extra clause is what the `p = 2` escape needs for its third conjunct (`χ_b` kills the
involutions of `G_K`): with the narrow modulus the idèle decomposition
`fracIdele 𝔵 = (γ) · e · b` has all archimedean components positive (`e` by narrowness, `b` because,
for `p = 2`, a `p`-th power class is lifted by a *square* of an idèle), while `fracIdele 𝔵` has
archimedean component `1`; hence `γ` is positive at every real place —
`Work.SSGRoute.H9.pos_of_decomposition`.

The wide version `readOffSupPow` produces `γ` with no control on its signs (the freedom is by units
which are local `p`-th powers at `T'`, whose signs are not free), which is precisely why the wide
modulus cannot deliver the corrected class `b = a γ⁻¹` totally positive.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT
open NK.Chebotarev

namespace Work.SSGRoute.H9

variable {K : Type} [Field K] [NumberField K]

/-- The `q`-adic exponent of a square of an idèle. -/
private lemma exp_mul_self (q : PrimeIdeal K) (x : Idele K) :
    Idele.exp q (x * x) = 2 * Idele.exp q x := by
  rw [Idele.exp_mul]
  ring

/-- The components of a square of an idèle. -/
private lemma mul_self_apply (x : Idele K) (v : Place K) :
    (x * x) v = x v * x v := Idele.mul_apply x x v

/-- A square of a local unit at a real place is positive. -/
private lemma isPosInf_mul_self {w : InfinitePlace K} {x : w.Completionˣ} :
    IsPosInf K w (x * x) := by
  intro hw
  rw [Units.val_mul, map_mul]
  have hne : InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) ≠ 0 :=
    fun h0 => x.ne_zero
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective (by rw [h0, map_zero]))
  rcases lt_or_gt_of_ne hne with h | h
  · exact mul_pos_of_neg_of_neg h h
  · exact mul_pos h h

/-- **Lifting the `2`-th powers of `C_K` to positive idèles.**  Every class in
`pPowSubgroup 2 C_K` has an idèle representative `b` which is a local square at every prime of `T`,
whose `𝔮`-adic exponents are all even, and whose **archimedean components are positive** (for
`p = 2` the lift `β²` of a square class has this property). -/
private lemma lift_pPow_two_pos (T : Finset (PrimeIdeal K)) (w : IdeleClassGroup K)
    (hw : w ∈ Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup K)) :
    ∃ b : Idele K, IdeleClassGroup.mk K b = w ∧
      (∀ 𝔭 ∈ T, b (Place.ofFinite 𝔭) ∈
        NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2) ∧
      (∀ 𝔮 : PrimeIdeal K, (2 : ℤ) ∣ Idele.exp 𝔮 b) ∧
      (∀ w' : InfinitePlace K, IsPosInf K w' (b (Place.ofInfinite w'))) := by
  classical
  have key : ∀ w : IdeleClassGroup K,
      w ∈ Subgroup.closure (Set.range fun g : IdeleClassGroup K => g ^ 2) →
      ∃ b : Idele K, IdeleClassGroup.mk K b = w ∧
        (∀ 𝔭 ∈ T, b (Place.ofFinite 𝔭) ∈
          NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2) ∧
        (∀ 𝔮 : PrimeIdeal K, (2 : ℤ) ∣ Idele.exp 𝔮 b) ∧
        (∀ w' : InfinitePlace K, IsPosInf K w' (b (Place.ofInfinite w'))) := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => ∃ b : Idele K,
        IdeleClassGroup.mk K b = w ∧
          (∀ 𝔭 ∈ T, b (Place.ofFinite 𝔭) ∈
            NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2) ∧
          (∀ 𝔮 : PrimeIdeal K, (2 : ℤ) ∣ Idele.exp 𝔮 b) ∧
          (∀ w' : InfinitePlace K, IsPosInf K w' (b (Place.ofInfinite w'))))
      ?_ ?_ ?_ ?_ hw
    · rintro x ⟨g, rfl⟩
      obtain ⟨β, hβ⟩ := IdeleClassGroup.mk_surjective K g
      refine ⟨β * β, ?_, ?_, ?_, ?_⟩
      · rw [map_mul, hβ]
        simp only [pow_two]
      · intro 𝔭 _
        refine (MonoidHom.mem_range).mpr ⟨β (Place.ofFinite 𝔭), ?_⟩
        rw [powMonoidHom_apply, pow_two, mul_self_apply]
      · intro 𝔮
        rw [exp_mul_self]
        exact ⟨Idele.exp 𝔮 β, rfl⟩
      · intro w'
        rw [mul_self_apply]
        exact isPosInf_mul_self
    · refine ⟨1, ?_, ?_, ?_, ?_⟩
      · rw [map_one]
      · intro 𝔭 _
        exact Subgroup.one_mem _
      · intro 𝔮
        rw [Idele.exp_one]
        exact dvd_zero _
      · intro w'
        rw [Idele.one_apply]
        exact isPosInf_one K w'
    · rintro x y _ _ ⟨b₁, h₁, hT₁, he₁, hp₁⟩ ⟨b₂, h₂, hT₂, he₂, hp₂⟩
      refine ⟨b₁ * b₂, ?_, ?_, ?_, ?_⟩
      · rw [map_mul, h₁, h₂]
      · intro 𝔭 h𝔭
        rw [Idele.mul_apply]
        exact Subgroup.mul_mem _ (hT₁ 𝔭 h𝔭) (hT₂ 𝔭 h𝔭)
      · intro 𝔮
        rw [Idele.exp_mul]
        exact dvd_add (he₁ 𝔮) (he₂ 𝔮)
      · intro w'
        rw [Idele.mul_apply]
        exact (hp₁ w').mul (hp₂ w')
    · rintro x _ ⟨b₁, h₁, hT₁, he₁, hp₁⟩
      refine ⟨b₁⁻¹, ?_, ?_, ?_, ?_⟩
      · rw [map_inv, h₁]
      · intro 𝔭 h𝔭
        rw [Idele.inv_apply]
        exact Subgroup.inv_mem _ (hT₁ 𝔭 h𝔭)
      · intro 𝔮
        rw [NK.NUV2.RouteB.RayModulus.exp_inv]
        exact dvd_neg.mpr (he₁ 𝔮)
      · intro w'
        rw [Idele.inv_apply]
        exact (hp₁ w').inv
  exact key w hw

/-- Local factorisation in the reading-off step (the `p = 2` copy of the private helper of
`readOffSupPow`). -/
private lemma localFactorOfMul_two (γ : Kˣ) (a e b : Idele K) (𝔭 : PrimeIdeal K)
    (h : Idele.principalIdele K γ * e * b = a) (ha : a (Place.ofFinite 𝔭) = 1)
    (he : e (Place.ofFinite 𝔭) ∈ NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2)
    (hb : b (Place.ofFinite 𝔭) ∈ NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2) :
    NK.UchidaKummer.localPowClass K 2 𝔭 γ = 1 := by
  have hcomp : (Idele.principalIdele K γ) (Place.ofFinite 𝔭)
      * e (Place.ofFinite 𝔭) * b (Place.ofFinite 𝔭) = 1 := by
    rw [← Idele.mul_apply, ← Idele.mul_apply, h, ha]
  have hmem : (Idele.principalIdele K γ) (Place.ofFinite 𝔭) ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) 2 := by
    have h3 : (Idele.principalIdele K γ) (Place.ofFinite 𝔭)
        * (e (Place.ofFinite 𝔭) * b (Place.ofFinite 𝔭)) = 1 := by
      rw [← mul_assoc]
      exact hcomp
    have h2 : (Idele.principalIdele K γ) (Place.ofFinite 𝔭) =
        (e (Place.ofFinite 𝔭) * b (Place.ofFinite 𝔭))⁻¹ :=
      eq_inv_of_mul_eq_one_left h3
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ he hb)
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  simpa [Idele.principalIdele_apply] using hmem

/-- **The narrow read-off.**  A fractional ideal `𝔵` coprime to `T'` whose idèle class lies in the
narrow `U · C_K²` differs from a principal ideal `(γ)` by a square of an ideal, where `γ` is a local
square at every prime of `T'` **and positive at every real place of `K`**. -/
theorem readOff_narrow (T' : Finset (PrimeIdeal K))
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (h𝔵T : ∀ 𝔭 ∈ T', FractionalIdeal.count K 𝔭 𝔵 = 0)
    (hmem : IdeleClassGroup.mk K (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵) ∈
      narrowGesU K 2 T' ⊔
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup 2 (IdeleClassGroup K)) :
    ∃ γ : Kˣ, (∀ 𝔭 ∈ T', NK.UchidaKummer.localPowClass K 2 𝔭 γ = 1) ∧
      (∀ 𝔮 : PrimeIdeal K, (2 : ℤ) ∣ FractionalIdeal.count K 𝔮 𝔵
        - FractionalIdeal.count K 𝔮
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
              (γ : K))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        0 < InfinitePlace.embedding_of_isReal hw (γ : K)) := by
  classical
  set a : Idele K := NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 with hadef
  -- decompose the class of `𝔵` as `u · w` with `u ∈ narrowGesU` and `w` a square of a class
  obtain ⟨u, hu, w, hw, huw⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu
  obtain ⟨p₁, hp₁, e, he, hp₁e⟩ := Subgroup.mem_sup.mp hy
  obtain ⟨γ₀, hγ₀⟩ := Idele.mem_principalSubgroup.mp hp₁
  have hprincipal : IdeleClassGroup.mk K (Idele.principalIdele K γ₀ * e) = u := by
    rw [map_mul, hγ₀, ← map_mul, hp₁e, hyu]
  -- lift the square class by a *positive* idèle
  obtain ⟨b, hb, hbT, hbexp, hbpos⟩ := lift_pPow_two_pos T' w hw
  have hprod : IdeleClassGroup.mk K (Idele.principalIdele K γ₀ * e * b)
      = IdeleClassGroup.mk K a := by
    rw [map_mul, hprincipal, hb, huw]
  have hker : Idele.principalIdele K γ₀ * e * b * a⁻¹ ∈ Idele.principalSubgroup K := by
    rw [← Work.SSGRoute.ker_mk_eq_principal, MonoidHom.mem_ker, map_mul, hprod, map_inv,
      mul_inv_cancel]
  obtain ⟨δ, hδ⟩ := Idele.mem_principalSubgroup.mp hker
  have hEq : Idele.principalIdele K (δ⁻¹ * γ₀) * e * b = a := by
    have h₁ : Idele.principalIdele K δ * a = Idele.principalIdele K γ₀ * e * b := by
      rw [hδ]
      group
    calc Idele.principalIdele K (δ⁻¹ * γ₀) * e * b
        = (Idele.principalIdele K δ)⁻¹ * (Idele.principalIdele K δ * a) := by
          rw [map_mul, map_inv, h₁]
          group
      _ = a := by group
  refine ⟨δ⁻¹ * γ₀, ?_, ?_, ?_⟩
  · -- the local square condition at `T'`
    intro 𝔭 h𝔭
    refine localFactorOfMul_two (δ⁻¹ * γ₀) a e b 𝔭 hEq ?_ ?_ ?_
    · rw [hadef, Work.SSGRoute.fracIdele_apply_ofFinite, h𝔵T 𝔭 h𝔭, zpow_zero]
    · exact (Work.SSGRoute.mem_powTIdeles.mp (narrowPowTIdeles_le_powTIdeles 2 T' he)).1 𝔭 h𝔭
    · exact hbT 𝔭 h𝔭
  · -- the `𝔮`-adic exponents differ by a square
    intro 𝔮
    have hγexp : FractionalIdeal.count K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ⁻¹ * γ₀ : Kˣ) : K))
        = Idele.exp 𝔮 (Idele.principalIdele K (δ⁻¹ * γ₀)) := by
      rw [← Idele.idealOf_principalIdele, Idele.count_idealOf]
    have haexp : Idele.exp 𝔮 a = FractionalIdeal.count K 𝔮 𝔵 := by
      rw [hadef]
      exact IdeleClassGroup.exp_ideleOfFun (fun q => FractionalIdeal.count K q 𝔵)
        (FractionalIdeal.finite_factors 𝔵) 𝔮
    have hsum : Idele.exp 𝔮 a = Idele.exp 𝔮 (Idele.principalIdele K (δ⁻¹ * γ₀))
        + Idele.exp 𝔮 e + Idele.exp 𝔮 b := by
      have h := congrArg (Idele.exp 𝔮) hEq
      simp only [Idele.exp_mul] at h
      exact h.symm
    have he_div : (2 : ℤ) ∣ Idele.exp 𝔮 e := by
      by_cases h𝔮 : 𝔮 ∈ T'
      · exact Work.SSGRoute.dvd_exp_of_mem_ellPowSubgroup 2 𝔮 e
          ((Work.SSGRoute.mem_powTIdeles.mp (narrowPowTIdeles_le_powTIdeles 2 T' he)).1 𝔮 h𝔮)
      · rw [(NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero 𝔮 e).mp
          ((Work.SSGRoute.mem_powTIdeles.mp (narrowPowTIdeles_le_powTIdeles 2 T' he)).2 (Place.ofFinite 𝔮)
            (fun hcon => h𝔮 (hcon 𝔮 rfl)))]
        exact dvd_zero _
    rw [hγexp, ← haexp, hsum]
    have hsub : Idele.exp 𝔮 (Idele.principalIdele K (δ⁻¹ * γ₀)) + Idele.exp 𝔮 e
        + Idele.exp 𝔮 b - Idele.exp 𝔮 (Idele.principalIdele K (δ⁻¹ * γ₀))
        = Idele.exp 𝔮 e + Idele.exp 𝔮 b := by
      ring
    rw [hsub]
    exact dvd_add he_div (hbexp 𝔮)
  · -- the positivity of `γ` at the real places
    intro w hw
    refine pos_of_decomposition (γ := δ⁻¹ * γ₀) (e := e * b) (a := a) ?_ ?_ ?_ w hw
    · rw [← mul_assoc]
      exact hEq
    · intro w'
      rw [Idele.mul_apply]
      exact ((Work.SSGRoute.H9.mem_narrowPowTIdeles.mp he).2 w').mul (hbpos w')
    · intro w'
      rw [hadef, fracIdele_ofInfinite]

end Work.SSGRoute.H9
