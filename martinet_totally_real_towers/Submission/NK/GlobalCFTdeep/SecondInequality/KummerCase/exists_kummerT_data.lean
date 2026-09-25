import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_adicCompletion_units_pow_eq_of_splitsCompletely
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.exists_prime_splitsCompletely_notMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT NK.GlobalCFTdeep

variable {K : Type} [Field K] [NumberField K]

/-- The elements of `Kˣ` which are `p`-th powers in the completion of `K` at the finite prime `q`. -/
def localPowUnits (p : ℕ) (q : HeightOneSpectrum (𝓞 K)) : Subgroup Kˣ :=
  (powMonoidHom (α := (q.adicCompletion K)ˣ) p).range.comap
    (Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom)

theorem mem_localPowUnits {p : ℕ} {q : HeightOneSpectrum (𝓞 K)} {x : Kˣ} :
    x ∈ localPowUnits (K := K) p q ↔
      ∃ c : (q.adicCompletion K)ˣ,
        algebraMap K (q.adicCompletion K) (x : K) = (c : q.adicCompletion K) ^ p := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h
    refine ⟨c, ?_⟩
    have h2 := congrArg (fun z : (q.adicCompletion K)ˣ => (z : q.adicCompletion K)) hc
    simpa [Units.val_pow_eq_pow_val] using h2.symm
  · rintro ⟨c, hc⟩
    refine MonoidHom.mem_range.mpr ⟨c, Units.ext ?_⟩
    simpa using hc.symm

/-- The finite primes underlying a finite set of places. -/
def finPrimes (S : Finset (Place K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  S.filterMap (fun v => match v with
      | Sum.inl _ => none
      | Sum.inr q => some q)
    (by
      intro a a' b hb hb'
      cases a with
      | inl w => simp at hb
      | inr q =>
          cases a' with
          | inl w => simp at hb'
          | inr q' =>
              simp only [Option.mem_def, Option.some.injEq] at hb hb'
              simpa [hb, hb'])

theorem mem_finPrimes {S : Finset (Place K)} {q : HeightOneSpectrum (𝓞 K)} :
    q ∈ finPrimes S ↔ Place.ofFinite q ∈ S := by
  rw [finPrimes]
  constructor
  · intro h
    rw [Finset.mem_filterMap] at h
    obtain ⟨v, hvS, hvq⟩ := h
    cases v with
    | inl w => simp at hvq
    | inr q' =>
        simp only [Option.some.injEq] at hvq
        subst hvq
        exact hvS
  · intro h
    exact (Finset.mem_filterMap (fun v : Place K => match v with
        | Sum.inl _ => none
        | Sum.inr q => some q)).mpr ⟨Place.ofFinite q, h, rfl⟩

/-- The primes of `K` which have to be avoided: those in `T` and those lying under `S`. -/
theorem finite_forbidden (S : Finset (Place K)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ({q : HeightOneSpectrum (𝓞 K) | q ∈ T ∨ Place.ofFinite q ∈ S} : Set _).Finite := by
  have h1 : ((T : Set (HeightOneSpectrum (𝓞 K))) ∪
      (Place.ofFinite ⁻¹' ((S : Set (Place K))))).Finite :=
    Set.Finite.union (Finset.finite_toSet T)
      (Set.Finite.preimage (f := @Place.ofFinite K _ _)
        (fun a _ a' _ h => Place.ofFinite_inj.mp h) (Finset.finite_toSet S))
  refine Set.Finite.subset h1 ?_
  intro q hq
  rcases hq with hq | hq
  · exact Or.inl hq
  · exact Or.inr hq

/-- The subgroup of `G` of elements which are `p`-th powers at every prime of `T`. -/
def ktSub (p : ℕ) (G : Subgroup Kˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  G ⊓ T.inf (fun q => localPowUnits (K := K) p q)

@[simp] theorem ktSub_empty (p : ℕ) (G : Subgroup Kˣ) : ktSub (K := K) p G ∅ = G := by
  simp [ktSub]

theorem ktSub_cons (p : ℕ) (G : Subgroup Kˣ) (q : HeightOneSpectrum (𝓞 K))
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hq : q ∉ T) :
    ktSub (K := K) p G (Finset.cons q T hq) = ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q := by
  rw [ktSub, ktSub, Finset.inf_cons]
  ac_rfl

theorem mem_ktSub {p : ℕ} {G : Subgroup Kˣ} {T : Finset (HeightOneSpectrum (𝓞 K))} {x : Kˣ} :
    x ∈ ktSub (K := K) p G T ↔ x ∈ G ∧ ∀ q ∈ T, x ∈ localPowUnits (K := K) p q := by
  rw [ktSub, Subgroup.mem_inf, Finset.inf_eq_iInf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => (Subgroup.mem_iInf.mp (h2 q)) hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q => Subgroup.mem_iInf.mpr (fun hq => h2 q hq)⟩

theorem ktSub_le (p : ℕ) (G : Subgroup Kˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ktSub (K := K) p G T ≤ G := inf_le_left

theorem ktSub_le_local (p : ℕ) (G : Subgroup Kˣ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    {q : HeightOneSpectrum (𝓞 K)} (hq : q ∈ T) :
    ktSub (K := K) p G T ≤ localPowUnits (K := K) p q := by
  rw [ktSub]
  exact le_trans inf_le_right (Finset.inf_le hq)

/-- **A strict inclusion of subgroups containing the `p`-th powers forces a `p`-index.**
If `N ≤ H' < H` and every `p`-th power of an element of `H` lies in `N`, then `p ∣ [H : H']`. -/
theorem dvd_relIndex_of_pow_mem {G₀ : Type*} [CommGroup G₀] {p : ℕ} (hp : p.Prime)
    {N H' H : Subgroup G₀} (hN : N ≤ H') (hH'H : H' ≤ H)
    (hpow : ∀ x ∈ H, x ^ p ∈ N) (hne : H' ≠ H) : p ∣ H'.relIndex H := by
  classical
  obtain ⟨x, hxH, hxH'⟩ : ∃ x ∈ H, x ∉ H' := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hH'H h)
  haveI : (H'.subgroupOf H).Normal := Subgroup.normal_of_isMulCommutative (H'.subgroupOf H)
  have hpowx : (⟨x, hxH⟩ : H) ^ p ∈ H'.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hN (hpow x hxH)
  set y : H ⧸ (H'.subgroupOf H) := QuotientGroup.mk' (H'.subgroupOf H) ⟨x, hxH⟩ with hy
  have hyne : y ≠ 1 := by
    intro hcon
    have h3 : (QuotientGroup.mk' (H'.subgroupOf H)) (⟨x, hxH⟩ : H) = 1 := by
      rw [← hy]; exact hcon
    rw [QuotientGroup.mk'_apply] at h3
    exact hxH' (Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨x, hxH⟩ : H)).mp h3))
  have hypow : y ^ p = 1 := by
    have h3 : (QuotientGroup.mk' (H'.subgroupOf H)) ((⟨x, hxH⟩ : H) ^ p) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff ((⟨x, hxH⟩ : H) ^ p)).mpr hpowx
    rw [hy, ← map_pow]
    exact h3
  have horder : orderOf y = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_iff_pow_eq_one.mpr hypow) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hyne
    · exact h1
  have hrel : H'.relIndex H = Nat.card (H ⧸ (H'.subgroupOf H)) := Subgroup.index_eq_card _
  rw [hrel]
  exact horder ▸ orderOf_dvd_natCard y

/-- `a` is not a `p`-th power in `K` when `L = K(a^{1/p})` has degree `p` over `K`. -/
theorem not_isPow_of_adjoin {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤) : ¬ ∃ c : K, c ^ p = a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact ha hc.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hα
    exact (map_ne_zero (algebraMap K L)).mpr ha hα.symm
  have hpow : (α / algebraMap K L c) ^ p = 1 := by
    rw [div_pow, hα, ← map_pow, hc, div_self ((map_ne_zero (algebraMap K L)).mpr ha)]
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hpow
  have hαK : α ∈ (⊥ : IntermediateField K L) := by
    have heq : α = algebraMap K L c * algebraMap K L (ζ ^ i) := by
      rw [map_pow, hi]
      field_simp
      exact (div_self ((map_ne_zero (algebraMap K L)).mpr hc0)).symm
    rw [heq]
    exact mul_mem (IntermediateField.algebraMap_mem _ c)
      (IntermediateField.algebraMap_mem _ (ζ ^ i))
  have htopbot : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← hadj]
    exact le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr hαK) bot_le
  have hsurj : Function.Surjective (algebraMap K L) := by
    intro x
    exact IntermediateField.mem_bot.mp
      (htopbot ▸ (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K L)))
  have hfr : Module.finrank K L = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap K L).injective, hsurj⟩
  have hp1 : p = 1 := by
    rw [← IsGalois.card_aut_eq_finrank K L, hcard] at hfr
    exact hfr
  exact hp.ne_one hp1

/-- **The local condition at a completely split prime is automatic on `⟨a⟩ · U(S)^p`.** -/
theorem kummerH0_le_localPowUnits {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] {p : ℕ} {a : K} (ha : a ≠ 0) {α : L}
    (hα : α ^ p = algebraMap K L a) (S : Set (Place K)) {q : HeightOneSpectrum (𝓞 K)}
    (hspl : ∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver q.asIdeal →
      Q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ Q.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Subgroup.closure {Units.mk0 a ha} ⊔
        Subgroup.map (powMonoidHom p) (NK.GlobalCFTdeep.TUnits (L := K) S)
      ≤ localPowUnits (K := K) p q := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, mem_localPowUnits]
    obtain ⟨c, hc⟩ :=
      exists_adicCompletion_units_pow_eq_of_splitsCompletely (K := K) (L := L) ha hα q hspl
    exact ⟨c, by rw [Units.val_mk0]; exact hc⟩
  · intro x hx
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp hx
    rw [powMonoidHom_apply] at hy
    rw [← hy]
    first
      | rw [SetLike.mem_coe, mem_localPowUnits]
      | rw [mem_localPowUnits]
    refine ⟨Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom y, ?_⟩
    rw [Units.coe_map, Units.val_pow_eq_pow_val, map_pow]
    rfl

section Main

variable {L : Type} [Field L] [NumberField L]

/-- **Existence of the auxiliary set `T` of primes** (Milne, *CFT*, VII §6.9).

Let `L = K(α)` be a cyclic Kummer extension of prime degree `p` with `α ^ p = a`, let `S` be a
finite set of places of `K` containing the infinite places and the places above `p`, and assume
the Kummer-theoretic input (`hA`, `hB`) that the `S`-units which are `p`-th powers in `L` are
exactly `⟨a⟩ · U(S)^p`, and that any other `S`-unit fails to be a `p`-th power at some prime
outside `S` splitting completely in `L`.  Then there is a finite set `T` of `|S| - 1` primes
outside `S`, splitting completely in `L`, such that the `S`-units which are `p`-th powers locally
at all primes of `T` are exactly `⟨a⟩ · U(S)^p`. -/
theorem exists_kummerT_data {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a : K} (ha : a ≠ 0) {α : L} (hα : α ^ p = algebraMap K L a)
    (hadj : IntermediateField.adjoin K {α} = ⊤)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S)
    (haS : Units.mk0 a ha ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)))
    (hA : ∀ b : K, ∀ hb : b ≠ 0, Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) →
      (∃ β : L, β ^ p = algebraMap K L b) →
      Units.mk0 b hb ∈ Subgroup.closure {Units.mk0 a ha} ⊔
        Subgroup.map (powMonoidHom p) (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K))))
    (hB : ∀ b : K, ∀ hb : b ≠ 0, Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) →
      (¬ ∃ β : L, β ^ p = algebraMap K L b) →
      ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.GlobalCFT.Place.ofFinite q ∉ S ∧
        (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          Q.asIdeal.LiesOver q.asIdeal →
            Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
            Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ∧
        (¬ ∃ c : (q.adicCompletion K)ˣ,
          algebraMap K (q.adicCompletion K) b = ((c : (q.adicCompletion K)ˣ) : q.adicCompletion K) ^ p)) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∀ q ∈ T, NK.GlobalCFT.Place.ofFinite q ∉ S) ∧
      S.card = T.card + 1 ∧
      (∀ q ∈ T, ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        Q.asIdeal.LiesOver q.asIdeal →
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) ∧
      (∀ b : K, ∀ hb : b ≠ 0,
        Units.mk0 b hb ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)) →
        (∀ q ∈ T, ∃ c : (q.adicCompletionIntegers K)ˣ,
          algebraMap K (q.adicCompletion K) b =
            ((c : q.adicCompletionIntegers K) : q.adicCompletion K) ^ p) →
        Units.mk0 b hb ∈ Subgroup.closure {Units.mk0 a ha} ⊔
          Subgroup.map (powMonoidHom p)
            (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K)))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- ## setup
  set G : Subgroup Kˣ := NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)) with hG
  set u : Kˣ := Units.mk0 a ha with hu
  set Gp : Subgroup Kˣ := Subgroup.map (powMonoidHom p) G with hGp
  set H0 : Subgroup Kˣ := Subgroup.closure {u} ⊔ Gp with hH0
  have haG : u ∈ G := by rw [hu, hG]; exact haS
  have hGp_le_G : Gp ≤ G := by
    rw [hGp, Subgroup.map_le_iff_le_comap]
    intro x hx
    simpa using pow_mem hx p
  have hGp_le_H0 : Gp ≤ H0 := by rw [hH0]; exact le_sup_right
  have hH0_le_G : H0 ≤ G := by
    rw [hH0]
    refine sup_le ?_ hGp_le_G
    rw [Subgroup.closure_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact haG
  have hu_notMem_Gp : u ∉ Gp := by
    intro hmem
    rw [hGp] at hmem
    obtain ⟨y, hyG, hy⟩ := Subgroup.mem_map.mp hmem
    rw [powMonoidHom_apply] at hy
    rw [hu] at hy
    have hyK : (y : K) ^ p = a := by
      have h2 := congrArg (fun z : Kˣ => (z : K)) hy
      simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using h2
    exact not_isPow_of_adjoin hp hcard hζ ha hα hadj ⟨(y : K), hyK⟩
  have hSinf' : ∀ w : Place K, w.IsInfinite → w ∈ S := by
    intro w hw
    obtain ⟨w', rfl⟩ := Place.isInfinite_iff.mp hw
    exact hSinf w'
  have hposS : 1 ≤ S.card := by
    have h1 : 0 < Fintype.card (NumberField.InfinitePlace K) :=
      lt_of_lt_of_le Nat.zero_lt_one (NK.GlobalCFTdeep.one_le_card_infinitePlace (L := K))
    obtain ⟨w⟩ := Fintype.card_pos_iff.mp h1
    exact Finset.card_pos.mpr ⟨Place.ofInfinite w, hSinf w⟩
  -- ## index of the `p`-th powers in `G`
  have hGp_relIndex : Gp.relIndex G = p ^ S.card := by
    rw [hGp, hG]
    have h : (Subgroup.map (powMonoidHom p)
          (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)))).relIndex
          (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))) = p ^ Nat.card ↥S :=
      NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup (K := K) p hp hζ S hSinf'
    rw [h]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hH0_relIndex_dvd : H0.relIndex G ∣ p ^ S.card := by
    have hmul : Gp.relIndex H0 * H0.relIndex G = Gp.relIndex G :=
      Subgroup.relIndex_mul_relIndex (H := Gp) (K := H0) (L := G) hGp_le_H0 hH0_le_G
    rw [hGp_relIndex] at hmul
    exact ⟨Gp.relIndex H0, hmul.symm.trans (mul_comm _ _)⟩
  have hH0_relIndex_pos : 0 < H0.relIndex G := by
    obtain ⟨i, -, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp hH0_relIndex_dvd
    rw [hi_eq]
    exact pow_pos hp.pos i
  have hH0_relIndex_ne : H0.relIndex G ≠ p ^ S.card := by
    intro hcon
    have hmul : Gp.relIndex H0 * H0.relIndex G = Gp.relIndex G :=
      Subgroup.relIndex_mul_relIndex (H := Gp) (K := H0) (L := G) hGp_le_H0 hH0_le_G
    have h1 : Gp.relIndex H0 * H0.relIndex G = 1 * H0.relIndex G := by
      rw [hmul, hGp_relIndex, hcon, one_mul]
    have h1' : Gp.relIndex H0 = 1 :=
      Nat.eq_of_mul_eq_mul_right hH0_relIndex_pos h1
    have h2 : (Gp.subgroupOf H0).index = 1 := h1'
    have h3 : Gp.subgroupOf H0 = ⊤ := Subgroup.index_eq_one.mp h2
    have huH0 : u ∈ H0 := by
      rw [hH0]
      exact Subgroup.mem_sup_left (Subgroup.mem_closure_singleton.mpr ⟨1, by simp⟩)
    refine hu_notMem_Gp ?_
    have h4 : (⟨u, huH0⟩ : H0) ∈ Gp.subgroupOf H0 := by rw [h3]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h4
  have hH0_relIndex_le : H0.relIndex G ≤ p ^ (S.card - 1) := by
    obtain ⟨i, hi_le, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp hH0_relIndex_dvd
    have hi_ne : i ≠ S.card := by
      intro h
      exact hH0_relIndex_ne (by rw [hi_eq, h])
    have hi_le' : i ≤ S.card - 1 := by omega
    rw [hi_eq]
    exact Nat.pow_le_pow_right hp.pos hi_le'
  -- ## the `p`-th powers of `G` are local `p`-th powers everywhere
  have hGp_le_local : ∀ q : HeightOneSpectrum (𝓞 K), Gp ≤ localPowUnits (K := K) p q := by
    intro q y hy
    rw [hGp] at hy
    obtain ⟨z, hzG, hz⟩ := Subgroup.mem_map.mp hy
    rw [powMonoidHom_apply] at hz
    rw [← hz]
    first
      | rw [SetLike.mem_coe, mem_localPowUnits]
      | rw [mem_localPowUnits]
    refine ⟨Units.map (algebraMap K (q.adicCompletion K)).toMonoidHom z, ?_⟩
    rw [Units.coe_map, Units.val_pow_eq_pow_val, map_pow]
    rfl
  have hGp_le_ktSub : ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
      Gp ≤ ktSub (K := K) p G T := fun T =>
    le_inf hGp_le_G (Finset.le_inf fun q _ => hGp_le_local q)
  -- ## the inductive construction of `T`
  have key : ∀ n : ℕ, ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      T.card = n ∧
      (∀ q ∈ T, Place.ofFinite q ∉ S ∧
        (∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver q.asIdeal →
          Q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ Q.asIdeal.inertiaDeg (𝓞 K) = 1)) ∧
      H0 ≤ ktSub (K := K) p G T ∧
      (ktSub (K := K) p G T ≠ H0 → p ^ n ≤ (ktSub (K := K) p G T).relIndex G) := by
    intro n
    induction n with
    | zero =>
        refine ⟨∅, by simp, by simp, ?_, ?_⟩
        · rw [ktSub_empty]; exact hH0_le_G
        · intro _
          rw [ktSub_empty, pow_zero, Subgroup.relIndex_self]
    | succ n ih =>
        obtain ⟨T, hTcard, hTgood, hTKt, hTidx⟩ := ih
        by_cases hcase : ktSub (K := K) p G T = H0
        · -- `T` already cuts out `H0`: add any new completely split prime
          let F : Finset (HeightOneSpectrum (𝓞 K)) := (finite_forbidden S T).toFinset
          obtain ⟨q, hqF, hqspl⟩ := exists_prime_splitsCompletely_notMem (K := K) (L := L) F
          have hqT : q ∉ T := fun h => hqF ((Set.Finite.mem_toFinset _).mpr (Or.inl h))
          have hqS : Place.ofFinite q ∉ S :=
            fun h => hqF ((Set.Finite.mem_toFinset _).mpr (Or.inr h))
          have hqgood : Place.ofFinite q ∉ S ∧
              (∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver q.asIdeal →
                Q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ Q.asIdeal.inertiaDeg (𝓞 K) = 1) :=
            ⟨hqS, hqspl⟩
          refine ⟨Finset.cons q T hqT, ?_, ?_, ?_, ?_⟩
          · rw [Finset.card_cons, hTcard]
          · intro r hr
            rw [Finset.mem_cons] at hr
            rcases hr with rfl | hr
            · exact hqgood
            · exact hTgood r hr
          · rw [ktSub_cons]
            refine le_inf hcase.ge ?_
            rw [hH0, hu, hGp, hG]
            exact kummerH0_le_localPowUnits ha hα (S : Set (Place K)) hqspl
          · intro hne
            exfalso
            have hcon : ktSub (K := K) p G (Finset.cons q T hqT) = H0 := by
              rw [ktSub_cons, hcase, inf_eq_left]
              rw [hH0, hu, hGp, hG]
              exact kummerH0_le_localPowUnits ha hα (S : Set (Place K)) hqspl
            exact hne hcon
        · -- `T` does not cut out `H0` yet: add a Frobenius witness
          obtain ⟨x, hxKt, hxH0⟩ : ∃ x : Kˣ, x ∈ ktSub (K := K) p G T ∧ x ∉ H0 := by
            by_contra h
            push_neg at h
            exact hcase (le_antisymm h hTKt)
          have hxG : x ∈ G := ktSub_le (K := K) p G T hxKt
          have hxeq : Units.mk0 (x : K) (Units.ne_zero x) = x := Units.ext rfl
          have hxTU : Units.mk0 (x : K) (Units.ne_zero x) ∈
              NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)) := by
            rw [hxeq, ← hG]
            exact hxG
          have hxnp : ¬ ∃ β : L, β ^ p = algebraMap K L (x : K) := by
            intro hβ
            have hmem : Units.mk0 (x : K) (Units.ne_zero x) ∈ H0 := by
              have h1 := hA (x : K) (Units.ne_zero x) hxTU hβ
              rwa [hH0, hu, hGp, hG]
            exact hxH0 (hxeq ▸ hmem)
          obtain ⟨q, hqS, hqspl, hqloc⟩ := hB (x : K) (Units.ne_zero x) hxTU hxnp
          have hxq : x ∉ localPowUnits (K := K) p q := by
            intro hmem
            exact hqloc (mem_localPowUnits.mp hmem)
          have hqT : q ∉ T := fun hq => hxq (ktSub_le_local (K := K) p G T hq hxKt)
          have hstrict : ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q ≠
              ktSub (K := K) p G T := by
            intro hcon
            have hmem : x ∈ ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q := by
              rw [hcon]; exact hxKt
            exact hxq hmem.2
          have hmul := Subgroup.relIndex_mul_relIndex
            (H := ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q)
            (K := ktSub (K := K) p G T) (L := G) inf_le_left (ktSub_le (K := K) p G T)
          have hge : p ≤ (ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q).relIndex
              (ktSub (K := K) p G T) := by
            refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (dvd_relIndex_of_pow_mem hp
              (le_inf (hGp_le_ktSub T) (hGp_le_local q)) inf_le_left ?_ hstrict)
            · intro h0
              have hz : (ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q).relIndex G = 0 := by
                rw [← hmul, h0, zero_mul]
              have hdvd2 := Subgroup.relIndex_dvd_of_le_left (L := G)
                (le_inf (hGp_le_ktSub T) (hGp_le_local q))
              rw [hz] at hdvd2
              have hGp0 : Gp.relIndex G = 0 := Nat.eq_zero_of_zero_dvd hdvd2
              rw [hGp_relIndex] at hGp0
              exact absurd hGp0 (pow_ne_zero _ hp.ne_zero)
            · intro y hy
              rw [hGp]
              exact Subgroup.mem_map.mpr
                ⟨y, ktSub_le (K := K) p G T hy, by rw [powMonoidHom_apply]⟩
          have hqgood : Place.ofFinite q ∉ S ∧
              (∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver q.asIdeal →
                Q.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ Q.asIdeal.inertiaDeg (𝓞 K) = 1) :=
            ⟨hqS, hqspl⟩
          refine ⟨Finset.cons q T hqT, ?_, ?_, ?_, ?_⟩
          · rw [Finset.card_cons, hTcard]
          · intro r hr
            rw [Finset.mem_cons] at hr
            rcases hr with rfl | hr
            · exact hqgood
            · exact hTgood r hr
          · rw [ktSub_cons]
            refine le_inf hTKt ?_
            rw [hH0, hu, hGp, hG]
            exact kummerH0_le_localPowUnits ha hα (S : Set (Place K)) hqspl
          · intro _
            rw [ktSub_cons]
            have hlow := hTidx hcase
            calc p ^ (n + 1) = p ^ n * p := pow_succ p n
              _ ≤ (ktSub (K := K) p G T).relIndex G *
                    (ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q).relIndex
                      (ktSub (K := K) p G T) := Nat.mul_le_mul hlow hge
              _ = (ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q).relIndex
                      (ktSub (K := K) p G T) * (ktSub (K := K) p G T).relIndex G := mul_comm _ _
              _ = (ktSub (K := K) p G T ⊓ localPowUnits (K := K) p q).relIndex G := hmul
  -- ## conclusion
  obtain ⟨T, hTcard, hTgood, hTKt, hTidx⟩ := key (S.card - 1)
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (hTgood q hq).1
  · rw [hTcard]
    exact (Nat.sub_add_cancel hposS).symm
  · intro q hq Q hQ
    exact (hTgood q hq).2 Q hQ
  · intro b hb hbS hloc
    have hKt_eq : ktSub (K := K) p G T = H0 := by
      by_contra hne
      have hlow := hTidx hne
      have hup : (ktSub (K := K) p G T).relIndex G ≤ H0.relIndex G :=
        Nat.le_of_dvd hH0_relIndex_pos
          (dvd_of_mul_left_eq _ (Subgroup.relIndex_mul_relIndex (H := H0)
            (K := ktSub (K := K) p G T) (L := G) hTKt (ktSub_le (K := K) p G T)))
      have heq : (ktSub (K := K) p G T).relIndex G = H0.relIndex G :=
        le_antisymm hup (le_trans hH0_relIndex_le hlow)
      have hpos' : (ktSub (K := K) p G T).relIndex G ≠ 0 := by
        rw [heq]; exact ne_of_gt hH0_relIndex_pos
      have hone : H0.relIndex (ktSub (K := K) p G T) = 1 := by
        have h2 : H0.relIndex (ktSub (K := K) p G T) * (ktSub (K := K) p G T).relIndex G
            = (ktSub (K := K) p G T).relIndex G := by
          rw [Subgroup.relIndex_mul_relIndex (H := H0) (K := ktSub (K := K) p G T) (L := G)
            hTKt (ktSub_le (K := K) p G T), heq]
        exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos') (by rw [one_mul]; exact h2)
      have hle : ktSub (K := K) p G T ≤ H0 := by
        have h3 : H0.subgroupOf (ktSub (K := K) p G T) = ⊤ := Subgroup.index_eq_one.mp hone
        intro y hy
        have h4 : (⟨y, hy⟩ : ↥(ktSub (K := K) p G T)) ∈
            H0.subgroupOf (ktSub (K := K) p G T) := by
          rw [h3]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp h4
      exact hne (le_antisymm hle hTKt)
    have hmemKt : Units.mk0 b hb ∈ ktSub (K := K) p G T := by
      first
      | rw [SetLike.mem_coe, mem_ktSub]
      | rw [mem_ktSub]
      refine ⟨?_, ?_⟩
      · rw [hG]; exact hbS
      · intro q hq
        obtain ⟨c, hc⟩ := hloc q hq
        first
        | rw [SetLike.mem_coe, mem_localPowUnits]
        | rw [mem_localPowUnits]
        refine ⟨Units.map (ValuationSubring.subtype (q.adicCompletionIntegers K)) c, ?_⟩
        rw [Units.val_mk0, hc, Units.coe_map]
        rfl
    have hmemH0 : Units.mk0 b hb ∈ H0 := by
      rw [← hKt_eq]
      exact hmemKt
    rwa [hH0, hu, hGp, hG] at hmemH0

end Main

end NK.GlobalCFTdeep.SecondInequality.KummerCase
