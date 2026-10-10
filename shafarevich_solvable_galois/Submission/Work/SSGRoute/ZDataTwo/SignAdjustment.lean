import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.Work.SSGRoute.ZDataTwo.AdicBridge
import Submission.Work.SSGRoute.ZDataTwo.LocalCongruence
import Submission.Work.SSGRoute.ZDataTwo.TotallyPositive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` sign adjustment (the archimedean half of the escape construction)

`Work.SSGRoute.ZDataTwo.signAdjustment_mu2`: given a finite set `T` of finite places of `Ω` over
`k` and `a ∈ (↥K)ˣ`, there is `s ∈ (↥K)ˣ` which is a local `2`-power at every prime of `↥K` below
`T` and such that `a · s` is totally positive (kills the involutions of `G_K`).

The element is `s = 1 + m·u` with `m := 2 · ∏_{A ∈ T} (absNorm 𝔭_A)^{N_A}` (so that `m` lies in
`𝔭_A^{N_A}` for every `A ∈ T`) and `u ∈ 𝓞 ↥K` an algebraic integer chosen by
`NK.CFTLib.Arl.exists_integral_sign_adjust` so that `1 + m·u` has the sign of `a` at every real
place of `↥K`.  Then `s ≡ 1 (mod 𝔭_A^{N_A})`, so the image of `s` in the completion at `𝔭_A` is a
square (`isCongAt_adicCompletion_of_mem_asIdeal_pow` + `exists_pow_eq_of_isCongAt`) and
`kummerCharZMod_eq_zero_of_isSquare_completion` gives the local vanishing; the total positivity of
`a · s` is the product of two positive reals and `kummerCharZMod_eq_zero_of_forall_not_isNegAt`
gives the vanishing on the involutions.

If `↥K` has no real place at all, take `s := 1`: both conjuncts are then immediate.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

/-- **The `K`-prime below a finite place of `Ω`.**  (This is
`Work.SSGRoute.GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top`, restated here so that this
module does not have to depend on the (heavy) correction-step file; the import cone of
`ZDataTwo` is fragile while colleagues edit `ZConstruction/TransferLevel.lean`.) -/
theorem exists_heightOneSpectrum_below (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    [NumberField ↥K] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) :
    ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
  have hproper : B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro htop
    apply hB
    refine top_unique ?_
    intro c _
    rw [ValuationSubring.mem_comap, IsScalarTower.algebraMap_apply k ↥K Ω]
    have hc : algebraMap k ↥K c ∈ B.comap (algebraMap ↥K Ω) := by rw [htop]; trivial
    rwa [ValuationSubring.mem_comap] at hc
  obtain ⟨𝔭, h𝔭⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (B.comap (algebraMap ↥K Ω)) hproper
      (fun x => Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring _ x)
  exact ⟨𝔭, h𝔭⟩

/-- The real value of `y : K` at a real place, read through the completion, is the value of the
real embedding attached to that place. -/
theorem ringEquivRealOfIsReal_algebraMap_eq {K : Type} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) (y : K) :
    NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap K w.Completion y) =
      NumberField.InfinitePlace.embedding_of_isReal hw y := by
  rw [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

/-- **Sign adjustment at `p = 2`.**  Given a finite set `T` of finite places of `Ω` over `k` and
`a ∈ (↥K)ˣ`, there is `s ∈ (↥K)ˣ` such that

* `s` kills the local Kummer character on the local group `decomp k A ⊓ K.fixingSubgroup` of every
  `A ∈ T` (i.e. `s` is a local `2`-power at the prime of `↥K` below `A`), and
* `a · s` is totally positive, i.e. its Kummer character vanishes at every involution of `G_K`. -/
theorem signAdjustment_mu2 (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (a : (↥K)ˣ) :
    ∃ s : (↥K)ˣ,
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ s
          (Work.SSGRoute.gesLocalToGalK K σ) = 0) ∧
      (∀ (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup), c ^ 2 = 1 →
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) 2 (ζ := ζ) hζ (a * s)
          (Work.SSGRoute.gesGalKOfFixing K c hc) = 0) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## the local data of `T`, independent of the case split
  have hex : ∀ A : {A // A ∈ T},
      ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        A.1.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    fun A => exists_heightOneSpectrum_below k Ω K A.1
      (hTfin A.1 A.2)
  choose 𝔭 h𝔭 using hex
  choose N hN using fun A : {A // A ∈ T} =>
    Work.SSGRoute.GrunwaldEscapeCore.exists_pow_eq_of_isCongAt (K := ↥K) 2 (𝔭 A)
  -- ## the modulus `m`
  let f : {A // A ∈ T} → ℕ := fun A => (Ideal.absNorm (𝔭 A).asIdeal) ^ (N A)
  let m : ℕ := 2 * ∏ A, f A
  have hm : 0 < m := by
    have hpos : ∀ A : {A // A ∈ T}, 0 < f A := by
      intro A
      refine pow_pos ?_ _
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact (𝔭 A).ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
    refine mul_pos (by norm_num) ?_
    exact Finset.prod_pos fun A _ => hpos A
  have hdvd : ∀ A : {A // A ∈ T}, f A ∣ m := by
    intro A
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem f (Finset.mem_univ A)) 2
  -- the `m`-multiple lies in every `𝔭_A^{N_A}`
  have hm_mem : ∀ A : {A // A ∈ T}, (m : 𝓞 ↥K) ∈ (𝔭 A).asIdeal ^ (N A) := by
    intro A
    obtain ⟨k, hk⟩ := hdvd A
    have hmk : m = (Ideal.absNorm (𝔭 A).asIdeal) ^ (N A) * k := by
      rw [hk]
    have hcast : (m : 𝓞 ↥K) =
        ((Ideal.absNorm (𝔭 A).asIdeal : 𝓞 ↥K)) ^ (N A) * (k : 𝓞 ↥K) := by
      rw [hmk, Nat.cast_mul, Nat.cast_pow]
    rw [hcast]
    exact Ideal.mul_mem_right (k : 𝓞 ↥K) _
      (Ideal.pow_mem_pow (Ideal.absNorm_mem (𝔭 A).asIdeal) (N A))
  by_cases hreal : ∃ w : NumberField.InfinitePlace ↥K, w.IsReal
  · -- ## the case where `↥K` has a real place: the construction `s = 1 + m·u`
    let r : NumberField.InfinitePlace ↥K → ℝ := fun w =>
      if h : w.IsReal then
        (if 0 < NumberField.InfinitePlace.embedding_of_isReal h (a : ↥K) then 1 else -1)
      else 1
    have hr : ∀ w, w.IsReal → r w ≠ 0 := by
      intro w hw
      simp only [r, dif_pos hw]
      split_ifs <;> norm_num
    obtain ⟨u, hu⟩ := NK.CFTLib.Arl.exists_integral_sign_adjust ↥K m hm r hr
    let sInt : 𝓞 ↥K := 1 + (m : 𝓞 ↥K) * u
    have hsInt : (sInt : ↥K) = 1 + (m : ↥K) * (u : ↥K) := by
      simp only [sInt]
      push_cast
      ring
    have hs_ne : (sInt : ↥K) ≠ 0 := by
      obtain ⟨w, hw⟩ := hreal
      intro h0
      have h1 := hu w hw
      rw [ringEquivRealOfIsReal_algebraMap_eq w hw] at h1
      rw [← hsInt] at h1
      rw [h0, map_zero, mul_zero] at h1
      exact lt_irrefl 0 h1
    let sUnit : (↥K)ˣ := Units.mk0 (sInt : ↥K) hs_ne
    have hsUnit : (sUnit : ↥K) = (sInt : ↥K) := rfl
    have hsu : (sUnit : ↥K) = 1 + (m : ↥K) * (u : ↥K) := by
      rw [hsUnit, hsInt]
    refine ⟨sUnit, ?_, ?_⟩
    · -- ## the local vanishing at `T`
      intro A hA σ
      refine kummerCharZMod_eq_zero_of_isSquare_completion k Ω K ζ hζ A (hTfin A hA) (𝔭 ⟨A, hA⟩)
        (h𝔭 ⟨A, hA⟩) sUnit ?_ σ
      have hy : ((m : 𝓞 ↥K) * u : 𝓞 ↥K) ∈ (𝔭 ⟨A, hA⟩).asIdeal ^ (N ⟨A, hA⟩) :=
        Ideal.mul_mem_right u _ (hm_mem ⟨A, hA⟩)
      have hys : (((m : 𝓞 ↥K) * u : 𝓞 ↥K) : ↥K) = (sUnit : ↥K) - 1 := by
        rw [hsu]
        push_cast
        ring
      exact hN ⟨A, hA⟩ sUnit
        (isCongAt_adicCompletion_of_mem_asIdeal_pow (K := ↥K) (𝔭 ⟨A, hA⟩) sUnit (N ⟨A, hA⟩)
          ((m : 𝓞 ↥K) * u) hy hys)
    · -- ## total positivity of `a · s`
      intro c hc hc2
      refine kummerCharZMod_eq_zero_of_forall_not_isNegAt k Ω K ζ hζ (a * sUnit) ?_ c hc hc2
      intro w hw
      rw [not_isNegAt_iff hw (a * sUnit)]
      have hS : 0 < r w * NumberField.InfinitePlace.embedding_of_isReal hw (sUnit : ↥K) := by
        have h1 := hu w hw
        rw [ringEquivRealOfIsReal_algebraMap_eq w hw, ← hsInt, ← hsUnit] at h1
        exact h1
      have hr2 : r w * r w = 1 := by
        simp only [r, dif_pos hw]
        split_ifs <;> norm_num
      have hApos : 0 < r w * NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K) := by
        have hne : NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K) ≠ 0 := by
          simp [(NumberField.InfinitePlace.embedding_of_isReal hw).injective.ne
            (Units.ne_zero a)]
        have hne' : 0 < NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K) ∨
            NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K) < 0 := by
          rcases lt_trichotomy (NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K)) 0 with
            h | h | h
          · exact Or.inr h
          · exact absurd h hne
          · exact Or.inl h
        simp only [r, dif_pos hw]
        split_ifs with hlt
        · linarith
        · push_neg at hlt
          rcases hne' with h' | h'
          · exact absurd h' (not_lt.mpr hlt)
          · nlinarith
      rw [Units.val_mul, map_mul]
      calc 0 < (r w * NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K)) *
            (r w * NumberField.InfinitePlace.embedding_of_isReal hw (sUnit : ↥K)) :=
            mul_pos hApos hS
        _ = NumberField.InfinitePlace.embedding_of_isReal hw (a : ↥K) *
            NumberField.InfinitePlace.embedding_of_isReal hw (sUnit : ↥K) := by
            rw [mul_mul_mul_comm, hr2, one_mul]
  · -- ## the case where `↥K` has no real place: `s = 1`
    refine ⟨1, ?_, ?_⟩
    · intro A hA σ
      refine kummerCharZMod_eq_zero_of_isSquare_completion k Ω K ζ hζ A (hTfin A hA) (𝔭 ⟨A, hA⟩)
        (h𝔭 ⟨A, hA⟩) 1 ⟨1, ?_⟩ σ
      rw [one_pow, map_one]
    · intro c hc hc2
      refine kummerCharZMod_eq_zero_of_forall_not_isNegAt k Ω K ζ hζ (a * 1) ?_ c hc hc2
      intro w hw
      exact absurd ⟨w, hw⟩ hreal

end Work.SSGRoute.ZDataTwo
