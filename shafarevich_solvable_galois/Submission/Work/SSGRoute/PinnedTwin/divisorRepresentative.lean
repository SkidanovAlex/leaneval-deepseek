import Mathlib
import Submission.Work.SSGRoute.PinnedTwin.Shim
import Submission.Work.SSGRoute.PinnedTwin.ideleOfIdeal_smul_cong
import Submission.Work.SSGRoute.PinnedTwin.rhoStableCongSubgroup
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
import Submission.Work.SSGRoute.NodeS37.divisorOfClassRepresentative
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_coprime_representative_two
import Submission.Work.SSGRoute.PinnedTwin.twistIdeleExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The divisor representative `z = b·y²`

`Work.SSGRoute.PinnedTwin.divisorRepresentative`: given `b : Kˣ` whose divisor is odd exactly at
`𝔮` (and even at every other place), with `𝔮` not fixed by the involution `ρ`, there are `z = b·y²`
and a prime `Q'` with `ριQ' ≠ Q'`, `Q' ≠ ρι𝔮` and `div z = 𝔮 · Q'²`.

## The two arithmetic inputs

The proof reduces the statement to two inputs, each of which is a statement about the *idèle*
group of `K` (not about primes or ideal classes):

* `Work.SSGRoute.PinnedTwin.twistIdeleExists` — the representative normalisation: there are a
  `ρ`-stable modulus `𝔪` with `pos = ∅` and `ρι𝔮 ∈ supp`, and an **integral** idèle `u` whose
  twist `ρ • u * u⁻¹` escapes `Kˣ · U(𝔪)`.  Such an idèle exhibits a *non-`ρ`-fixed* class in the
  ray class group `𝕀 K ⧸ (Kˣ · U(𝔪))` that has the same ideal class as `A`;
* `Work.SSGRoute.PinnedTwin.rhoStableCongSubgroup` — the `ρ`-stability of `U(𝔪)`, which makes the
  Galois action well defined on the ray class group.

The remaining ingredients are Čebotarev for the ray class group
(`Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass`, proved), the congruence statement
`Work.SSGRoute.PinnedTwin.ideleOfIdeal_smul_cong` (proved), the square root of the divisor of `b`
(`Work.SSGRoute.ZDataTwo.TwoRec.exists_fractionalIdeal_count_eq`, proved) and the divisor
arithmetic of `Work.SSGRoute.NodeS37.count_mul_sq_of_classRepresentative` (proved).
-/

namespace Work.SSGRoute.PinnedTwin

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- The congruence subgroup `U(𝔪)` consists of integral idèles. -/
private lemma congSubgroup_le_integralIdeles {K : Type} [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) :
    NK.NUV2.RouteB.CongSubgroup K 𝔪 ≤ NK.GlobalCFT.Idele.integralIdeles K := by
  intro x hx
  rw [NK.GlobalCFT.Idele.mem_integralIdeles]
  intro v hv
  rw [NK.GlobalCFT.Place.isFinite_iff] at hv
  obtain ⟨q, rfl⟩ := hv
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  exact ((NK.NUV2.RouteB.Modulus.mem_congSubgroup_iff.mp hx).1 q).1

/-- The count form of the identity `(Q') = A · (y)`. -/
private lemma count_of_asIdeal_eq_mul {L : Type} [Field L] [NumberField L]
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers L)) L) (hA : A ≠ 0)
    (Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (y : Lˣ)
    (hy : ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers L)) L)
        = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
            (y : L))) :
    ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      FractionalIdeal.count L P A
        + FractionalIdeal.count L P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers L)) (y : L))
      = (if P = Q' then 1 else 0) := by
  intro P
  have hyl : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
      (y : L) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero y)
  have h1 : FractionalIdeal.count L P (A * FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers L)) (y : L))
      = FractionalIdeal.count L P A
        + FractionalIdeal.count L P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers L)) (y : L)) :=
    FractionalIdeal.count_mul L P hA hyl
  have h2 : FractionalIdeal.count L P
        ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers L)) L))
      = (if P = Q' then 1 else 0) := by
    have := FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers L) (K := L) P Q'
    simpa [eq_comm] using this
  rw [← h1, ← hy]; exact h2

/-- In the (commutative) idèle group, conjugating by an idèle is the identity. -/
private lemma idele_conj_eq_self {L : Type} [Field L] [NumberField L]
    (x z : NK.GlobalCFT.Idele L) : x * z * x⁻¹ = z := by
  rw [mul_assoc, mul_comm z x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The idèle of an ideal has that ideal as its attached fractional ideal. -/
private lemma idealOf_ideleOfIdeal_eq {L : Type} [Field L] [NumberField L]
    (I : Ideal (NumberField.RingOfIntegers L)) (hI : I ≠ 0) :
    (NK.HeckeL.ideleOfIdeal L I).idealOf = (I : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers L)) L) := by
  refine NK.GlobalCFT.IdeleClassGroup.fractionalIdeal_eq_of_count_eq
    (NK.GlobalCFT.Idele.idealOf_ne_zero _)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI) (fun q => ?_)
  exact NK.GlobalCFT.IdeleClassGroup.count_idealOf_ideleOfFun _ _ q

variable (ρ : K ≃ₐ[k] K)

/-- **The main step.**  If `x` is an idèle whose attached ideal is `A` and whose twist
`ρ • x * x⁻¹` escapes the subgroup `Kˣ · U(𝔪)`, then a prime `Q'` with the required properties and
`(Q') = A · (y)` exists.  The proof is Čebotarev in the ray class group, together with the
contrapositive of the twist: a `ρ`-fixed prime would have a `ρ`-fixed ray class. -/
private theorem prime_of_twist
    (hP1 : ∀ (𝔪 : NK.NUV2.RouteB.Modulus K), 𝔪.pos = ∅ →
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) →
      ∀ x : NK.GlobalCFT.Idele K, x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 →
        ρ • x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪)
    (b : Kˣ) (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (hcount : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))
      = (if P = 𝔮 then 1 else 0) + 2 * FractionalIdeal.count K P A)
    (𝔪 : NK.NUV2.RouteB.Modulus K) (hpos : 𝔪.pos = ∅)
    (hstab : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q)
    (hsupp : 𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ≠ 0)
    (x : NK.GlobalCFT.Idele K) (hxid : x.idealOf = A)
    (hx : (ρ • x) * x⁻¹ ∉ NK.GlobalCFT.Idele.principalSubgroup K ⊔
      NK.NUV2.RouteB.CongSubgroup K 𝔪) :
    ∃ z y : Kˣ, z = b * y ^ 2 ∧
      ∃ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
        Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
        ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
            = FractionalIdeal.count K P
                ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
              + 2 * FractionalIdeal.count K P
                ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
  classical
  -- ## Čebotarev in the ray class group, at the class of `x`
  obtain ⟨Q', hQ'm, hQ'c⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass (K := K) 𝔪
      (QuotientGroup.mk x)
  -- ## the class relation `ideleOfIdeal Q' · x⁻¹ ∈ Kˣ · U(𝔪)`
  have hy : (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x ∈
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
    QuotientGroup.eq.mp hQ'c
  -- ## `U(𝔪)` is `ρ`-stable and `Kˣ` too, so `Kˣ · U(𝔪)` is
  have hstabU : ∀ {z : NK.GlobalCFT.Idele K},
      z ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 →
      ρ • z ∈ NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
    intro z hz
    obtain ⟨a, ha, w, hw, rfl⟩ := Subgroup.mem_sup.mp hz
    obtain ⟨a₀, rfl⟩ := ha
    refine Subgroup.mem_sup.mpr
      ⟨NK.GlobalCFT.Idele.principalIdele K (Units.map ρ.toMulEquiv.toMonoidHom a₀),
        ⟨_, rfl⟩, ρ • w, hP1 𝔪 hpos hstab w hw, ?_⟩
    rw [NK.GlobalCFT.Galois.globalCFT_smul_idele_mul,
      NK.GlobalCFT.Galois.globalCFT_smul_principalIdele]
  -- ## `Q'` is not `ρ`-fixed (contrapositive of the twist)
  have hnonfix : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' := by
    intro hfix
    -- the congruence statement turns `ρ`-fixedness of `Q'` into `ρ`-fixedness of its class
    have hcong : (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
        (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ ∈
        NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
      have h1 := ideleOfIdeal_smul_cong ρ 𝔪 hpos hstab Q' hQ'm
      rwa [hfix] at h1
    have hmem1 : (ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
        (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ ∈
        NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
      Subgroup.mem_sup.mpr ⟨1, Subgroup.one_mem _, _, hcong, one_mul _⟩
    -- decompose `x = (ideleOfIdeal Q') · ((ideleOfIdeal Q')⁻¹ · x)`
    have htw : (ρ • x) * x⁻¹ ∈
        NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
      have hzH : ((ρ • ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)) *
          ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)⁻¹) ∈
          NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 :=
        Subgroup.mul_mem _ (hstabU hy) (Subgroup.inv_mem _ hy)
      have hdecomp : x = NK.HeckeL.ideleOfIdeal K Q'.asIdeal *
          ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x) := by group
      have hsplit : (ρ • x) * x⁻¹
          = ((ρ • NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
              (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹) *
            ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
              (((ρ • ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)) *
                ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)⁻¹)) *
              (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹) := by
        rw [hdecomp, NK.GlobalCFT.Galois.globalCFT_smul_idele_mul, mul_inv_rev]; group
      rw [hsplit, show (NK.HeckeL.ideleOfIdeal K Q'.asIdeal) *
            (((ρ • ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)) *
              ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)⁻¹)) *
            (NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹
          = (((ρ • ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)) *
              ((NK.HeckeL.ideleOfIdeal K Q'.asIdeal)⁻¹ * x)⁻¹)) from
        idele_conj_eq_self _ _]
      exact Subgroup.mul_mem _ hmem1 hzH
    exact hx htw
  -- ## `Q' ≠ ρι𝔮`
  have havoid : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 := by
    intro h
    exact hsupp (by rw [← h]; exact hQ'm)
  -- ## the generator of the ideal class
  have hIdeal : ∃ y₁ : Kˣ, ((Q'.asIdeal : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
      = A * FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (y₁ : K)) := by
    obtain ⟨a, ha, v, hv, hav⟩ := Subgroup.mem_sup.mp hy
    obtain ⟨a₀, rfl⟩ := ha
    have hv1 : v.idealOf = 1 :=
      (NK.GlobalCFT.Idele.idealOf_eq_one_iff v).mpr (congSubgroup_le_integralIdeles 𝔪 hv)
    have hcomp : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (a₀ : K) = ((Q'.asIdeal : FractionalIdeal
          (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ * A := by
      have h1 : (NK.GlobalCFT.Idele.principalIdele K a₀ * v).idealOf
          = ((Q'.asIdeal : FractionalIdeal
              (nonZeroDivisors (NumberField.RingOfIntegers K)) K))⁻¹ * A := by
        rw [hav, NK.GlobalCFT.Idele.idealOf_mul, NK.GlobalCFT.Idele.idealOf_inv,
          idealOf_ideleOfIdeal_eq Q'.asIdeal Q'.ne_bot, hxid]
      rw [NK.GlobalCFT.Idele.idealOf_mul, NK.GlobalCFT.Idele.idealOf_principalIdele, hv1,
        mul_one] at h1
      exact h1
    refine ⟨a₀⁻¹, ?_⟩
    rw [show (((a₀⁻¹ : Kˣ)) : K) = ((a₀ : K))⁻¹ from Units.val_inv_eq_inv_val a₀,
      ← FractionalIdeal.spanSingleton_inv (K := K) (x := ((a₀ : K))), hcomp, mul_inv_rev,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  obtain ⟨y₁, hy₁⟩ := hIdeal
  -- ## the divisor arithmetic
  refine ⟨b * y₁ ^ 2, y₁, rfl, Q', hnonfix, havoid, ?_⟩
  intro P
  have hmain := Work.SSGRoute.NodeS37.count_mul_sq_of_classRepresentative 𝔮 Q' A b y₁ hcount
    (count_of_asIdeal_eq_mul A hA Q' y₁ hy₁) P
  have hq : FractionalIdeal.count K P
      ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = 𝔮 then 1 else 0) := by
    rw [FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers K) (K := K) P 𝔮]
    simp [eq_comm]
  have hQ' : FractionalIdeal.count K P
      ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = Q' then 1 else 0) := by
    rw [FractionalIdeal.count_maximal (R := NumberField.RingOfIntegers K) (K := K) P Q']
    simp [eq_comm]
  rw [hmain, hq, hQ']

/-- **The assembly.**  From the two arithmetic inputs, the divisor representative exists. -/
private theorem core
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), P ≠ 𝔮 →
      Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hodd : Odd (FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hP1 : ∀ (𝔪 : NK.NUV2.RouteB.Modulus K), 𝔪.pos = ∅ →
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) →
      ∀ x : NK.GlobalCFT.Idele K, x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪 →
        ρ • x ∈ NK.NUV2.RouteB.CongSubgroup K 𝔪)
    (hp2 : ∃ (𝔪 : NK.NUV2.RouteB.Modulus K) (u : NK.GlobalCFT.Idele K),
      𝔪.pos = ∅ ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
      𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ≠ 0 ∧
      u ∈ NK.GlobalCFT.Idele.integralIdeles K ∧
      ρ • u * u⁻¹ ∉ NK.GlobalCFT.Idele.principalSubgroup K ⊔
        NK.NUV2.RouteB.CongSubgroup K 𝔪) :
    ∃ z y : Kˣ, z = b * y ^ 2 ∧
      ∃ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
        Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
        ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
            = FractionalIdeal.count K P
                ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
              + 2 * FractionalIdeal.count K P
                ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
  classical
  -- ## the square root of the divisor of `b`
  obtain ⟨A, hAne, hcount⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.exists_fractionalIdeal_count_eq b 𝔮 heven hodd
  -- ## the twist idèle
  obtain ⟨𝔪, u, hpos, hstab, hsupp, huint, htwist⟩ := hp2
  -- ## an idèle of ideal class `A`
  obtain ⟨x₀, hx₀⟩ :=
    NK.GlobalCFT.IdeleClassGroup.idealOf_surjective K (Units.mk0 A hAne)
  have hx₀' : x₀.idealOf = A := by simpa using hx₀
  -- ## is the class of `x₀` `ρ`-fixed?
  by_cases hfixed : (ρ • x₀) * x₀⁻¹ ∈
      NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪
  · -- ### `ρ`-fixed: multiply by `u`, whose twist escapes
    have hx : (ρ • (x₀ * u)) * (x₀ * u)⁻¹ ∉
        NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
      intro hmem
      have hsplit : (ρ • (x₀ * u)) * (x₀ * u)⁻¹
          = ((ρ • x₀) * x₀⁻¹) * (x₀ * ((ρ • u) * u⁻¹) * x₀⁻¹) := by
        rw [NK.GlobalCFT.Galois.globalCFT_smul_idele_mul, mul_inv_rev]; group
      rw [hsplit] at hmem
      have hsol : (ρ • u) * u⁻¹ ∈
          NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
        have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hfixed) hmem
        have h3 : ((ρ • x₀) * x₀⁻¹)⁻¹ * (((ρ • x₀) * x₀⁻¹) * (x₀ * ((ρ • u) * u⁻¹) * x₀⁻¹))
            = x₀ * ((ρ • u) * u⁻¹) * x₀⁻¹ := by group
        rw [h3] at h2
        rwa [idele_conj_eq_self] at h2
      exact htwist hsol
    have hxid : (x₀ * u).idealOf = A := by
      rw [NK.GlobalCFT.Idele.idealOf_mul, hx₀',
        (NK.GlobalCFT.Idele.idealOf_eq_one_iff u).mpr huint,
        mul_one]
    exact prime_of_twist ρ hP1 b 𝔮 A hAne hcount 𝔪 hpos hstab hsupp (x₀ * u) hxid hx
  · -- ### not `ρ`-fixed: use `x₀` itself
    exact prime_of_twist ρ hP1 b 𝔮 A hAne hcount 𝔪 hpos hstab hsupp x₀ hx₀'
      (fun h => hfixed h)

theorem divisorRepresentative {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (b : Kˣ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (heven : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), P ≠ 𝔮 →
      Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hodd : Odd (FractionalIdeal.count K 𝔮 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K))))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ z y : Kˣ, z = b * y ^ 2 ∧
      ∃ Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q' ∧
        Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ∧
        ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          FractionalIdeal.count K P (FractionalIdeal.spanSingleton
            (nonZeroDivisors (NumberField.RingOfIntegers K)) (z : K))
            = FractionalIdeal.count K P
                ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
              + 2 * FractionalIdeal.count K P
                ((Q'.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) := by
  classical
  -- The `ρ`-stability of `U(𝔪)` is proved in `Work.SSGRoute.PinnedTwin.rhoStableCongSubgroup`.
  -- The twist idèle is supplied by `Work.SSGRoute.PinnedTwin.twistIdeleExists`.
  exact core ρ hρ2 b 𝔮 heven hodd
    (fun 𝔪 hpos hstab x hx => rhoStableCongSubgroup ρ 𝔪 hpos hstab x hx)
    (twistIdeleExists ρ hρ2 𝔮 hne)

end Work.SSGRoute.PinnedTwin
