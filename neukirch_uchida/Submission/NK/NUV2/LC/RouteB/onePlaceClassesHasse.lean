import Mathlib
import Submission.NK.NUV2.LC.RouteB.cycClassUnitsAvatar
import Submission.NK.NUV2.LC.RouteB.HasseRes.CycDict
import Submission.NK.NUV2.LC.RouteB.HasseRes.ResAux2
import Submission.NK.NUV2.LC.RouteB.index_localNormSubgroup_of_localDeg_eq_prime
import Submission.NK.NUV2.LC.RouteB.onePlaceLevelClassesNaive
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.UchidaKummer.Embedding.isKummerEmbeddingProblem
import Submission.NK.UchidaKummer.Embedding.exists_localPowClass_family
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.NK.CFTLib.IdeleHasse.exists_localMap_ofFinite
import Submission.NK.BrauerHasse.local_ofLevel_zero
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot

/-!
# The one-place classes of NSW (9.2.1) (`Hasse` variant)

`NK.NUV2.LC.RouteB.onePlaceClassesHasse` is the one-place-classes statement, proved here from

* the explicit-cocycle cyclic-algebra avatar `NK.NUV2.LC.RouteB.cycClassUnitsAvatar` (the units
  class `γ b = ofLevel ⟨E⟩ ((unitsTransport ⟨E⟩).symm (cycClassOf g hg b))` in the units colimit,
  together with its `μ_p`-avatar `Y`), and
* the two proved halves of the localisation dictionary of that avatar:
  `NK.NUV2.LC.RouteB.cyclicClassMap_loc_eq_zero_imp_mem_localNormPreimage` (the "only if"
  direction) and `NK.NUV2.LC.RouteB.loc_eq_zero_of_localLevelGroup_subsingleton_h` (the
  completely split case).

For each index `i` the Kummer data of `NK.UchidaKummer.Embedding.exists_localPowClass_family`
produce `a i = b (𝔭 i) ∈ Fˣ` which is a local `p`-th power at every prime `𝔭 j` with `j ≠ i` and a
non-`p`-th power at `𝔭 i`; the cyclic Kummer field `E i = F((a i)^{1/p})` therefore splits
completely at the places `A j` (`j ≠ i`) and does not at `A i`.  The class of the cyclic algebra
`(E i / F, b i)` localises to `0` at every `A j` with `j ≠ i` (the split case), while at `A i` its
localisation is non-zero by the contrapositive of the "only if" direction, applied to a global unit
`b i` which is not a local norm at `𝔭 i` (existence from the density of `F` in its completions).

The auxiliary lemmas in the first section are verbatim copies (renamed) of the local preliminaries
of `Submission/Work/NUV2/LC/RouteB/hasseSurjTop.lean`, which cannot be imported here: that module
and `cyclicClassColimAltDefs.lean` both define `NK.NUV2.LC.RouteB.muToH2_zero`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped Pointwise NumberField

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse IsDedekindDomain

/-! ### Local preliminaries -/

/-- **The local degree in a prime-degree Galois extension of number fields is `1` or `p`.**

The fundamental identity `∑_{q | Q} e(q) f(q) = [L : K]` — in the Galois form
`g · e · f = |Gal(L/K)|` (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`) —
exhibits `e(q) f(q)` as a divisor of `p = [L : K]`. -/
lemma localDeg_eq_one_or_eq_prime_h {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) (hp : p.Prime)
    (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    NK.UchidaKummer.localDeg q Q = 1 ∨ NK.UchidaKummer.localDeg q Q = p := by
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank K L, hdeg]
  have key := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Q.asIdeal) (NumberField.RingOfIntegers L) (L ≃ₐ[K] L)
  have hdvd : Q.asIdeal.ramificationIdxIn (𝓞 L) * Q.asIdeal.inertiaDegIn (𝓞 L) ∣ p := by
    refine ⟨(Q.asIdeal.primesOver (𝓞 L)).ncard, ?_⟩
    rw [← hcard, mul_comm, ← key]
  have h1 : Q.asIdeal.ramificationIdxIn (𝓞 L) = q.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdxIn_eq_ramificationIdx Q.asIdeal q.asIdeal (L ≃ₐ[K] L)
  have h2 : Q.asIdeal.inertiaDegIn (𝓞 L) = q.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDegIn_eq_inertiaDeg Q.asIdeal q.asIdeal (L ≃ₐ[K] L)
  have hld : NK.UchidaKummer.localDeg q Q
      = Q.asIdeal.ramificationIdxIn (𝓞 L) * Q.asIdeal.inertiaDegIn (𝓞 L) := by
    rw [NK.UchidaKummer.localDeg, h1, h2]
  rw [hld]
  exact (Nat.dvd_prime hp).mp hdvd

/-- **The local `ℓ`-power class vanishes exactly at local `ℓ`-th powers.** -/
lemma localPowClass_eq_one_iff_h {K : Type} [Field K] [NumberField K] (ℓ : ℕ)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (a : Kˣ) :
    NK.UchidaKummer.localPowClass K ℓ 𝔮 a = 1 ↔
      ∃ b : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)ˣ,
        ((b : IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) ^ ℓ
          = algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮) (a : K) := by
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, NK.UchidaKummer.ellPowSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [powMonoidHom_apply] at hb
    have hbval := congrArg (fun u : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)ˣ =>
      (u : IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔮)) hb
    rw [Units.val_pow_eq_pow_val, Units.coe_map] at hbval
    exact hbval
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [powMonoidHom_apply]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.coe_map]
    exact hb

/-- **`p`-th powers of the base are local norms.**  If the local degree of `E_q / F_Q` is `p`, then
for `x ∈ F_Qˣ` the element `x ^ p` is the norm of (the image of) `x`. -/
lemma pow_mem_range_localNormFinite_h {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (p : ℕ)
    (hfr : Module.finrank (Q.adicCompletion F) (q.adicCompletion E) = p)
    (x : (Q.adicCompletion F)ˣ) :
    x ^ p ∈ MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q Q hq) := by
  letI : Algebra (Q.adicCompletion F) (q.adicCompletion E) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have hdef : NK.GlobalCFT.Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (Q.adicCompletion F) : q.adicCompletion E →* Q.adicCompletion F) :=
    rfl
  have h1 : (Algebra.norm (Q.adicCompletion F))
      (algebraMap (Q.adicCompletion F) (q.adicCompletion E) (x : Q.adicCompletion F))
      = (x : Q.adicCompletion F) ^ p := by
    rw [Algebra.norm_algebraMap, hfr]
  refine ⟨Units.map (algebraMap (Q.adicCompletion F) (q.adicCompletion E)).toMonoidHom x, ?_⟩
  rw [hdef]
  exact Units.ext h1

/-- **`p`-th powers of the local field lie in the local norm subgroup.** -/
lemma pow_mem_localNormSubgroup_h {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (p : ℕ)
    (hfr : Module.finrank (Q.adicCompletion F) (q.adicCompletion E) = p)
    (x : (Q.adicCompletion F)ˣ) :
    x ^ p ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := E)
      (NK.GlobalCFT.Place.ofFinite Q) := by
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
  exact le_iSup (fun q' : {q' : HeightOneSpectrum (𝓞 E) // q'.asIdeal.LiesOver Q.asIdeal} =>
    MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q'.1 Q q'.2)) ⟨q, hq⟩
    (pow_mem_range_localNormFinite_h Q q hq p hfr x)

/-- **The local norm subgroup at a non-split prime is proper.**  If the local degree of `E_q/F_Q`
is `p`, the norm group has index `p`, hence is a proper subgroup. -/
lemma localNormSubgroup_ne_top_h {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (p : ℕ) (hp : p.Prime)
    (hld : NK.UchidaKummer.localDeg q Q = p) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := E)
      (NK.GlobalCFT.Place.ofFinite Q) ≠ ⊤ := by
  intro htop
  have hidx : (MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q Q hq)).index = p :=
    index_localNormSubgroup_of_localDeg_eq_prime p hp Q q hq hld
  rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup Q q hq, htop] at hidx
  rw [Subgroup.index_top] at hidx
  exact hp.ne_one hidx.symm

/-- **A global unit which is not a local norm at a non-split prime.**

The subgroup of `p`-th powers of `F_Qˣ` is open, so a coset `u·(F_Qˣ)^p` is an open subset of
`F_Q`; by the density of `F` in its completion
(`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`) it contains a global element
`a`, and `a` is not a local norm: if it were, then `u = a·y⁻¹` with `y ∈ (F_Qˣ)^p ⊆ M` would be a
local norm too. -/
lemma exists_notMem_localNormPreimage_h {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (p : ℕ) (hp : p.Prime)
    (hfr : Module.finrank (Q.adicCompletion F) (q.adicCompletion E) = p)
    (hM : NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := E)
      (NK.GlobalCFT.Place.ofFinite Q) ≠ ⊤) :
    ∃ b : Fˣ, b ∉ NK.CFTLib.localNormPreimage (K := F) (L := E)
      (NK.GlobalCFT.Place.ofFinite Q) := by
  classical
  let M : Subgroup (Q.adicCompletion F)ˣ :=
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := E) (NK.GlobalCFT.Place.ofFinite Q)
  have hPowM : ∀ y : (Q.adicCompletion F)ˣ, y ^ p ∈ M :=
    fun y => pow_mem_localNormSubgroup_h Q q hq p hfr y
  obtain ⟨x, hx⟩ : ∃ x : (Q.adicCompletion F)ˣ, x ∉ M := by
    by_contra h
    push_neg at h
    exact hM ((Subgroup.eq_top_iff' _).mpr fun x => h x)
  have hO : IsOpen ((fun y : (Q.adicCompletion F)ˣ => (y : Q.adicCompletion F)) ''
      (x • ((NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion F) p :
        Subgroup (Q.adicCompletion F)ˣ) : Set (Q.adicCompletion F)ˣ))) :=
    NK.UchidaKummer.Approximation.isOpen_unitsVal_image_smul_subgroup x
      (NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion F) p)
      (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup F p hp Q)
  have hne : ((fun y : (Q.adicCompletion F)ˣ => (y : Q.adicCompletion F)) ''
      (x • ((NK.UchidaKummer.ellPowSubgroup (Q.adicCompletion F) p :
        Subgroup (Q.adicCompletion F)ˣ) : Set (Q.adicCompletion F)ˣ))).Nonempty :=
    ⟨(x : Q.adicCompletion F), x * 1, ⟨1, one_mem _, by simp⟩, by simp⟩
  obtain ⟨a, ha⟩ :=
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F Q).exists_mem_open hO hne
  obtain ⟨z, hz, hzval⟩ := ha
  obtain ⟨y, hy, hzy⟩ := hz
  have hz_eq : z = x * y := by simpa [smul_eq_mul] using hzy.symm
  have hyM : y ∈ M := by
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hy
    rw [powMonoidHom_apply] at hc
    rw [← hc]
    exact hPowM c
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hz0 : (z : Q.adicCompletion F) = 0 := by simpa using hzval
    exact Units.ne_zero z hz0
  refine ⟨Units.mk0 a ha0, fun hpre => hx ?_⟩
  have hbM : Units.map (algebraMap F (Q.adicCompletion F)).toMonoidHom (Units.mk0 a ha0) ∈ M :=
    (NK.CFTLib.mem_localNormPreimage).mp hpre
  have hval : (Units.map (algebraMap F (Q.adicCompletion F)).toMonoidHom (Units.mk0 a ha0)
      : Q.adicCompletion F) = (z : Q.adicCompletion F) := by
    rw [Units.coe_map, Units.val_mk0]
    exact hzval.symm
  have hzM : z ∈ M := by
    have hzu : Units.map (algebraMap F (Q.adicCompletion F)).toMonoidHom (Units.mk0 a ha0) = z :=
      Units.ext hval
    rw [← hzu]
    exact hbM
  have hxy : x * y ∈ M := by rw [← hz_eq]; exact hzM
  have hxeq : x = (x * y) * y⁻¹ := by group
  rw [hxeq]
  exact Subgroup.mul_mem _ hxy (Subgroup.inv_mem _ hyM)

/-- **`Multiplicative.ofAdd` detects the identity.** -/
lemma multiplicative_ofAdd_eq_one_iff_h {α : Type*} [AddZeroClass α] (y : α) :
    (Multiplicative.ofAdd y : Multiplicative α) = 1 ↔ y = 0 := by
  rw [show (1 : Multiplicative α) = Multiplicative.ofAdd 0 from rfl]
  exact (Multiplicative.ofAdd (α := α)).injective.eq_iff

/-- **A homomorphism into a group of prime order is surjective as soon as it is non-trivial.** -/
lemma monoidHom_surjective_of_card_prime_h {G H : Type*} [Group G] [Group H]
    (p : ℕ) (hp : p.Prime) (Φ : G →* H) (hcard : Nat.card H = p) (hne : ∃ b, Φ b ≠ 1) :
    Function.Surjective Φ := by
  obtain ⟨b₀, hb₀⟩ := hne
  have hdvd : Nat.card (MonoidHom.range Φ) ∣ p := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hcardrange : Nat.card (MonoidHom.range Φ) = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      haveI : Subsingleton (MonoidHom.range Φ) := (Nat.card_eq_one_iff_unique.mp h1).1
      have hmem : Φ b₀ ∈ MonoidHom.range Φ := ⟨b₀, rfl⟩
      have hbot : MonoidHom.range Φ = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        exact congrArg Subtype.val (Subsingleton.elim ⟨x, hx⟩ ⟨1, one_mem _⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hb₀ hmem
    · exact h1
  have hidx : (MonoidHom.range Φ).index = 1 := by
    have h := Subgroup.index_mul_card (MonoidHom.range Φ)
    rw [hcardrange, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h, one_mul])
  exact MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp hidx)

/-- **Simultaneous Kummer surjectivity along an injective family of primes.**

For a finite injective family `𝔭 : ι → PrimeIdeal F` and global units `b₀ i`, there is a global
unit `b` whose local `p`-power class at `𝔭 i` agrees with that of `b₀ i` for every `i`.  (This is
Kummer surjectivity at the finite set of primes, transported to the index type `ι`; the index of a
prime of the image is recovered by `Function.Injective`.) -/
lemma exists_localPowClass_eq_family_h {F : Type} [Field F] [NumberField F] (p : ℕ) (hp : p.Prime)
    {ι : Type} [Fintype ι]
    (𝔭 : ι → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hinj : Function.Injective 𝔭) (b₀ : ι → Fˣ) :
    ∃ b : Fˣ, ∀ i : ι, NK.UchidaKummer.localPowClass F p (𝔭 i) b =
      NK.UchidaKummer.localPowClass F p (𝔭 i) (b₀ i) := by
  classical
  have hsurj : NK.UchidaKummer.IsKummerSurjective F p (Finset.univ.image 𝔭) :=
    NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation p _
      (NK.UchidaKummer.Approximation.isWeakApproximation F _)
      (NK.UchidaKummer.Approximation.isOpenEllPowSubgroup F p hp)
  have hidx : ∀ 𝔮 : ↥(Finset.univ.image 𝔭), ∃ i : ι, 𝔭 i = 𝔮.1 := by
    intro 𝔮
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp 𝔮.2
    exact ⟨i, hi⟩
  choose idx hidx' using hidx
  obtain ⟨b, hb⟩ := hsurj (fun 𝔮 : ↥(Finset.univ.image 𝔭) =>
    NK.UchidaKummer.localPowClass F p 𝔮.1 (b₀ (idx 𝔮)))
  refine ⟨b, fun i => ?_⟩
  have h := hb ⟨𝔭 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hidx_i : idx ⟨𝔭 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ = i :=
    hinj (hidx' ⟨𝔭 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  rw [hidx_i] at h
  exact h

/-- **A prime of a prime-degree Galois extension with local degree different from `1`.**

For `L/K` Galois of prime degree `p` and any prime `q` of `L` over `Q`, the local degree is `1` or
`p` (`localDeg_eq_one_or_eq_prime_h`); hence a prime with local degree `≠ 1` has local degree `p`. -/
lemma exists_prime_localDeg_eq_prime_of_not_one_h {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ)
    (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      q.asIdeal.LiesOver Q.asIdeal ∧ NK.UchidaKummer.localDeg q Q ≠ 1) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      q.asIdeal.LiesOver Q.asIdeal ∧ NK.UchidaKummer.localDeg q Q = p := by
  obtain ⟨q₀, hq₀, hq₀ne⟩ := h
  refine ⟨q₀, hq₀, ?_⟩
  rcases localDeg_eq_one_or_eq_prime_h p hp hdeg Q q₀ hq₀ with h1 | h1
  · exact absurd h1 hq₀ne
  · exact h1

/-- **The local Kummer dichotomy gives a prime of local degree different from `1`.**

If the Kummer radical `a` is not a local `p`-th power at `𝔭`, then `𝔭` does not split completely in
`L = K(a^{1/p})`, i.e. some prime of `L` over `𝔭` has local degree `≠ 1`. -/
lemma kummerField_exists_prime_localDeg_ne_one_h {K K' : Type} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (a : Kˣ) (L : IntermediateField K K') [FiniteDimensional K L]
    [NumberField ↥L] (hL : L = NK.LocalAnabelian.kummerField (K' := K') p a)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : NK.UchidaKummer.localPowClass K p 𝔭 a ≠ 1) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
      q.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.UchidaKummer.localDeg q 𝔭 ≠ 1 := by
  have hdich := NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := K) (K' := K') p hp
    hζ a L hL 𝔭
  by_contra h
  push_neg at h
  rw [hdich] at h
  obtain ⟨b, hb⟩ := h
  exact hne ((localPowClass_eq_one_iff_h p 𝔭 a).mpr ⟨b, hb.symm⟩)


/-! ### The completely split case of the localisation dictionary -/

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']

/-- **The localisation of `muToH2 (Y b)` vanishes at a place whose decomposition group fixes `E`**
(the completely split case of the localisation dictionary).

This is `NK.NUV2.LC.RouteB.loc_eq_zero_of_localLevelGroup_subsingleton_h` with its hypothesis
`Subsingleton (LocalLevelGroup ⊤ A.1 ⟨E⟩)` derived from the splitting of `v` in `E`. -/
lemma loc_muToH2_eq_zero_of_le_fixingSubgroup_h (p : ℕ) (hp : p.Prime) [NeZero p]
    (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E] [NumberField ↥E]
    (hdeg : Module.finrank F E = p)
    (g : ↥E ≃ₐ[F] ↥E) (hg : ∀ σ : ↥E ≃ₐ[F] ↥E, σ ∈ Subgroup.zpowers g)
    (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
    (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)))
    (hγ : ∀ b : Fˣ, NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
      ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
        (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) = γ b)
    (hY : ∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
      (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (A : NK.BrauerHasse.OverFinitePrime F F')
    (hA : A.1.comap (algebraMap F F') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v)
    (hAc : NK.BrauerHasse.stabSubgroup A.1 ≤
      (⟨E⟩ : FiniteGaloisIntermediateField F F').fixingSubgroup)
    (b : Fˣ) :
    NK.BrauerHasse.H2Profinite.loc p ⊤
      (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ (Y b)) A = 0 := by
  let V : Subgroup Gal(F'/F) := ⊤ ⊓ NK.BrauerHasse.stabSubgroup A.1
  have hVle : V ≤ (⟨E⟩ : FiniteGaloisIntermediateField F F').fixingSubgroup :=
    fun σ hσ => hAc hσ.2
  haveI htriv : Subsingleton (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(F'/F)) A.1
      (⟨E⟩ : FiniteGaloisIntermediateField F F')) := by
    rw [NK.BrauerHasse.LocalLevelGroup, Subgroup.subgroupOf_eq_top.mpr hVle]
    exact QuotientGroup.subsingleton_quotient_top
  exact NK.NUV2.LC.RouteB.loc_eq_zero_of_localLevelGroup_subsingleton_h p hp F' ζ hζ E hdeg
    g hg γ Y hγ hY v A hA b htriv

/-! ### The one-place classes -/

theorem onePlaceClassesHasse (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (ι : Type) [Fintype ι]
    (A : ι → NK.BrauerHasse.OverFinitePrime F F')
    (hnot : ∀ i j : ι, i ≠ j → ¬ NK.NUV2.LC.RouteB.InOrbit (K := F) (K' := F') ⊤ (A i).1 (A j).1) :
    ∃ a : ι → NK.BrauerHasse.H2Profinite (K := F) (K' := F') p ⊤,
      (∀ i : ι, NK.BrauerHasse.H2Profinite.loc p ⊤ (a i) (A i) ≠ 0) ∧
      (∀ i j : ι, i ≠ j → NK.BrauerHasse.H2Profinite.loc p ⊤ (a i) (A j) = 0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- ## The primes of `F` below the places `A i`
  have hAne : ∀ i, (A i).1.comap (algebraMap F F') ≠ ⊤ := fun i => (A i).2
  let 𝔭 : ι → NK.Chebotarev.PrimeIdeal F :=
    fun i => Submission.NeukirchUchida.primeOf (A i).1 (hAne i)
  have h𝔭 : ∀ i, (A i).1.comap (algebraMap F F') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F (𝔭 i) :=
    fun i => Submission.NeukirchUchida.primeOf_spec (A i).1 (hAne i)
  have hinj : Function.Injective 𝔭 := by
    intro i j hij
    by_contra hne
    apply hnot i j hne
    have hcomap : (A i).1.comap (algebraMap F F') = (A j).1.comap (algebraMap F F') := by
      rw [h𝔭 i, h𝔭 j, hij]
    obtain ⟨σ, hσ⟩ := Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'
      (A := (A i).1) (B := (A j).1) (hAne i) hcomap
    exact ⟨σ, Subgroup.mem_top σ, hσ⟩
  -- ## The Kummer data
  let T : Finset (NK.Chebotarev.PrimeIdeal F) := Finset.univ.image 𝔭
  have hTmem : ∀ i, 𝔭 i ∈ T := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨b, hb1, hb2⟩ :=
    NK.UchidaKummer.Embedding.exists_localPowClass_family (L := F) p hp T ∅ (by simp)
  have hKnot : ∀ P ∈ T, ¬ ∃ c : (P.adicCompletion F)ˣ,
      algebraMap F (P.adicCompletion F) (b P : F) = (c : (P.adicCompletion F)) ^ p := by
    intro P hP h
    exact hb1 P hP (NK.UchidaKummer.Embedding.localPowClass_eq_one_of_exists_pow_eq p P (b P) h)
  have hnotpow : ∀ P ∈ T, b P ∉ NK.LocalAnabelian.powSubgroup p F := by
    intro P hP hmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    rw [powMonoidHom_apply] at hc
    refine hKnot P hP ⟨Units.map (algebraMap F (P.adicCompletion F)).toMonoidHom c, ?_⟩
    have h2 : ((c ^ p : Fˣ) : F) = (b P : F) := congrArg (fun u : Fˣ => (u : F)) hc
    rw [Units.val_pow_eq_pow_val] at h2
    show algebraMap F (P.adicCompletion F) (b P : F)
      = (algebraMap F (P.adicCompletion F) (c : F)) ^ p
    rw [← h2, map_pow]
  -- ## The cyclic Kummer fields
  let E : ι → IntermediateField F F' :=
    fun i => NK.LocalAnabelian.kummerField (K' := F') p (b (𝔭 i))
  have hEgal : ∀ i, IsGalois F ↥(E i) := fun i =>
    (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := F) (K' := F') p hp hζ
      (b (𝔭 i)) (hnotpow (𝔭 i) (hTmem i))).1
  have hEdeg : ∀ i, Module.finrank F ↥(E i) = p := fun i =>
    (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := F) (K' := F') p hp hζ
      (b (𝔭 i)) (hnotpow (𝔭 i) (hTmem i))).2
  haveI : ∀ i, IsGalois F ↥(E i) := hEgal
  haveI : ∀ i, FiniteDimensional F ↥(E i) := fun i =>
    FiniteDimensional.of_finrank_pos (by rw [hEdeg i]; exact hp.pos)
  haveI : ∀ i, NumberField ↥(E i) := fun i =>
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (E i)
  have hEcyc : ∀ i, IsCyclic (↥(E i) ≃ₐ[F] ↥(E i)) := fun i =>
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank F ↥(E i)]; exact hEdeg i)
  -- ## The explicit-cocycle avatars
  have havatar : ∀ i, ∃ (g : ↥(E i) ≃ₐ[F] ↥(E i))
      (hg : ∀ σ : ↥(E i) ≃ₐ[F] ↥(E i), σ ∈ Subgroup.zpowers g)
      (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
      (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))),
      (∀ b : Fˣ, NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
        (⊤ : Subgroup Gal(F'/F)) (⟨E i⟩ : FiniteGaloisIntermediateField F F')
        ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
          (⟨E i⟩ : FiniteGaloisIntermediateField F F')).symm
          (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥(E i)) g hg b)) = γ b) ∧
      (∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b) := by
    intro i
    obtain ⟨g, hg, γ, Y, hγ, -, hY, -⟩ :=
      NK.NUV2.LC.RouteB.cycClassUnitsAvatar p hp F' (E i) (hEdeg i) (hEcyc i)
    exact ⟨g, hg, γ, Y, hγ, hY⟩
  choose g hg γ Y hγ hY using havatar
  -- ## A prime of `E i` over `𝔭 i` of local degree `p`, and a non-local-norm
  have hqex : ∀ i, ∃ q : NK.Chebotarev.PrimeIdeal ↥(E i),
      q.asIdeal.LiesOver (𝔭 i).asIdeal ∧ NK.UchidaKummer.localDeg q (𝔭 i) = p := fun i =>
    exists_prime_localDeg_eq_prime_of_not_one_h p hp (hEdeg i) (𝔭 i)
      (kummerField_exists_prime_localDeg_ne_one_h p hp hζ (b (𝔭 i)) (E i) rfl (𝔭 i)
        (hb1 (𝔭 i) (hTmem i)))
  choose q hqover hqdeg using hqex
  have hfr : ∀ i, Module.finrank ((𝔭 i).adicCompletion F) ((q i).adicCompletion ↥(E i)) = p :=
    fun i => by
      rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        (𝔭 i) (q i) (hqover i)]
      exact hqdeg i
  have hMtop : ∀ i, NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := ↥(E i))
      (NK.GlobalCFT.Place.ofFinite (𝔭 i)) ≠ ⊤ :=
    fun i => localNormSubgroup_ne_top_h (𝔭 i) (q i) (hqover i) p hp (hqdeg i)
  have hb'ex : ∀ i, ∃ c : Fˣ, c ∉ NK.CFTLib.localNormPreimage (K := F) (L := ↥(E i))
      (NK.GlobalCFT.Place.ofFinite (𝔭 i)) :=
    fun i => exists_notMem_localNormPreimage_h (𝔭 i) (q i) (hqover i) p hp (hfr i) (hMtop i)
  choose b' hb' using hb'ex
  -- ## `E i` splits completely at `A j` for `j ≠ i`
  have hAc : ∀ i j, i ≠ j → NK.BrauerHasse.stabSubgroup (A j).1 ≤
      (⟨E i⟩ : FiniteGaloisIntermediateField F F').fixingSubgroup := by
    intro i j hij
    have hne : 𝔭 j ≠ 𝔭 i := fun h => hij (hinj h.symm)
    refine (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := F) (K' := F')
      (N := E i) (𝔭 j) (A j).1 (h𝔭 j)).mpr ?_
    refine (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one (K := F)
      (L := ↥(E i)) (𝔭 j)).mpr ?_
    intro R hR
    exact localDeg_eq_one_of_kummerData p hp hζ b
      (hb2 (𝔭 i) (hTmem i) (𝔭 j) (Finset.mem_union_right ∅ (hTmem j)) hne) R hR
  -- ## The one-place classes
  refine ⟨fun i => NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ (Y i (b' i)), ?_, ?_⟩
  · intro i h0
    exact hb' i (NK.NUV2.LC.RouteB.cyclicClassMap_loc_eq_zero_imp_mem_localNormPreimage_c
      p hp hodd F F' ζ hζ (E i) (hEdeg i) (hEcyc i) (g i) (hg i) (γ i) (Y i) (hγ i) (hY i)
      (𝔭 i) (A i) (h𝔭 i) (b' i) h0)
  · intro i j hij
    exact loc_muToH2_eq_zero_of_le_fixingSubgroup_h p hp ζ hζ (E i) (hEdeg i) (g i) (hg i)
      (γ i) (Y i) (hγ i) (hY i) (𝔭 j) (A j) (h𝔭 j) (hAc i j hij) (b' i)

end NK.NUV2.LC.RouteB
