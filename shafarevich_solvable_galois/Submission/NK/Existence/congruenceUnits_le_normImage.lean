import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.exists_congruenceSubgroup_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence subgroup intersected with the integral idèles is a norm group

For a finite Galois extension `L / K` of number fields, an admissible modulus `m > 0` divisible by
all the ramified primes (`hram`), the subgroup of the idèle group `𝕀 K` consisting of the idèles
which are `≡ 1 mod m` at the primes dividing `(m)`, positive at the real places, and which are
*local units at every finite place* (i.e. whose attached fractional ideal is `(1)`, the kernel of
`NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom`) is contained in the idèlic norm group
`N_{L/K} 𝕀 L`.

The proof is place-by-place, using only the local theory of the norm map (no local class field
theory):

* at a prime `𝔭 | (m)` the idèle is a *congruence unit* at level `m`, hence a local norm at every
  prime above `𝔭` — this is exactly the admissibility hypothesis `IsAdmissible`;
* at a prime `𝔭 ∤ (m)` the extension is unramified (by `hram`), so the local norm is surjective on
  the local units, and the idèle is a local unit there by the kernel hypothesis;
* at an infinite place the element is positive, hence a local norm (`ℂ/ℝ` case: everything is a
  norm; `ℝ/ℝ` case: the norm is surjective).

The per-place local data is assembled into a global norm by
`NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage`.  This is the statement that the
congruence subgroup (of Neukirch–Schmidt–Wingberg, Chapter XII, resp. Lang, Chapter VII §4) is
contained in the norm group, which is the input used to identify `𝕀 K / (W_m · N 𝕀 L)` with the
class group quotient `C_K / N C_L`.
-/

set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct WithZero NumberField.LiesOver
open NumberField IsDedekindDomain
open NK.GlobalCFT NK.CFTLib.ExistsCongruence

namespace NK.Existence

theorem congruenceUnits_le_normImage (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m) :
    NK.CFTLib.Arl.congruenceSubgroup K m ⊓
        MonoidHom.ker (NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K) ≤
      NK.GlobalCFT.Idele.normImage K L := by
  classical
  -- The finite set of primes of `K` dividing `(m)`.
  have hfin : {Q : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {((m : ℕ) : 𝓞 K)}) ?_).subset ?_
    · exact fun h0 => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
        (Ideal.span_singleton_eq_bot.mp h0)
    · intro Q hQ
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem Q.asIdeal).mpr hQ)
  set Sfin : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hSfindef
  have hSfinmem : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∈ Sfin ↔ (m : 𝓞 K) ∈ Q.asIdeal :=
    fun Q => Set.Finite.mem_toFinset hfin
  -- The finite set of places at which a local condition is imposed: all the infinite places, and
  -- the finite places dividing `(m)`.
  set S : Finset (Place K) :=
    (Finset.univ.image Place.ofInfinite) ∪ (Sfin.image Place.ofFinite) with hSdef
  have hSinf : ∀ w : InfinitePlace K, Place.ofInfinite w ∈ S := by
    intro w
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hSfinmem' : ∀ Q : HeightOneSpectrum (𝓞 K),
      (m : 𝓞 K) ∈ Q.asIdeal → Place.ofFinite Q ∈ S := by
    intro Q hQ
    rw [hSdef]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Q, (hSfinmem Q).mpr hQ, rfl⟩)
  have hSofFinite : ∀ Q : HeightOneSpectrum (𝓞 K),
      Place.ofFinite Q ∈ S → (m : 𝓞 K) ∈ Q.asIdeal := by
    intro Q hQ
    rw [hSdef] at hQ
    rcases Finset.mem_union.mp hQ with h | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
      exact absurd (hw ▸ Place.isInfinite_ofInfinite w) (Place.not_isInfinite_ofFinite Q)
    · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp h
      have h' : Q' = Q := Place.ofFinite_inj.mp hQQ'
      exact h' ▸ (hSfinmem Q').mp hQ'
  -- The local norm at the chosen place of `L` above each place of `K`.
  set Φ : (v : Place K) →
      (Place.localField L (NK.CFTLib.IdeleHasse.placeAbove v))ˣ →* (Place.localField K v)ˣ :=
    (fun v => match v with
      | Sum.inl w =>
          @Place.localNormInfinite K _ L _ _ (aboveInf (K := K) (L := L) w) w
            (aboveInf_liesOver w)
      | Sum.inr Q =>
          Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q (abovePrime_liesOver Q))
    with hΦdef
  have hΦfin : ∀ Q : HeightOneSpectrum (𝓞 K),
      Φ (Place.ofFinite Q) = Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
        (abovePrime_liesOver Q) := fun Q => rfl
  have hΦinf : ∀ w : InfinitePlace K,
      Φ (Place.ofInfinite w) = @Place.localNormInfinite K _ L _ _
        (aboveInf (K := K) (L := L) w) w (aboveInf_liesOver w) := fun w => rfl
  -- `Φ` computes the idèlic norm of a single-place idèle.
  have hbridge : ∀ (v : Place K)
      (u : (Place.localField L (NK.CFTLib.IdeleHasse.placeAbove v))ˣ),
      Idele.normIdeleFun K L
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
          (NK.CFTLib.IdeleHasse.placeAbove v) u) v = Φ v u := by
    intro v u
    cases v with
    | inl w =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite
          (v := w) (w := aboveInf (K := K) (L := L) w) (hw := aboveInf_liesOver w) u
    | inr Q =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite
          Q (abovePrime Q) (abovePrime_liesOver Q) u
  -- The congruence units with trivial ideal class lie in the constrained idèles.
  have hU : NK.CFTLib.Arl.congruenceSubgroup K m ⊓
        MonoidHom.ker (IdeleClassGroup.idealOfUnitHom K) ≤
      NK.GlobalCFTdeep.constrainedE S (fun v : ↥S => (Φ ↑v).range) := by
    intro x hx
    obtain ⟨hxc, hxk⟩ := hx
    have hxcong : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∈ 𝔭.asIdeal →
        Valued.v (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
          ≤ Valued.v (((m : ℕ) : 𝔭.adicCompletion K)) := hxc.1
    have hxpos : ∀ w : InfinitePlace K, NK.CFTLib.Arl.PosAtReal w (x (Place.ofInfinite w)) :=
      hxc.2
    -- the kernel of the ideal-class map consists of the idèles which are local units everywhere
    have hint : x ∈ Idele.integralIdeles K := by
      have hval : IdeleClassGroup.idealOfUnitHom K x = 1 := MonoidHom.mem_ker.mp hxk
      have h2 := congrArg Units.val hval
      have hid : x.idealOf = 1 := by simpa using h2
      exact (Idele.idealOf_eq_one_iff x).mp hid
    have hlu : ∀ v : Place K, v.IsFinite → x v ∈ Place.localUnits K v :=
      (Idele.mem_integralIdeles).mp hint
    rw [NK.GlobalCFTdeep.mem_constrainedE]
    refine ⟨fun v => ?_, fun v hvS => ?_⟩
    · rcases hv : (↑v : Place K) with w | Q
      · have hpos : NK.CFTLib.Arl.PosAtReal w (x (Place.ofInfinite w)) := hxpos w
        rw [hΦinf w]
        exact posAtReal_mem_range_localNormInfinite (v := w) (w := aboveInf (K := K) (L := L) w)
          (hw := aboveInf_liesOver w) hpos
      · have hv' : (↑v : Place K) = Place.ofFinite Q := hv
        have hmQ : (m : 𝓞 K) ∈ Q.asIdeal := hSofFinite Q (hv' ▸ v.2)
        have hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (Place.ofFinite Q) : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1)
            ≤ Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : Q.adicCompletion K)) := hxcong Q hmQ
        rw [hΦfin Q]
        exact hadm Q hmQ (abovePrime (K := K) (L := L) Q) (abovePrime_liesOver Q)
          (x (Place.ofFinite Q)) hz
    · cases v with
      | inl w => exact absurd (hSinf w) hvS
      | inr Q => exact hlu (Place.ofFinite Q) (Place.isFinite_ofFinite Q)
  -- outside `S` the local norm is surjective on the local units
  have hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (NK.CFTLib.IdeleHasse.placeAbove v), Φ v u = a := by
    intro v
    cases v with
    | inl w => exact fun hvS => absurd (hSinf w) hvS
    | inr Q =>
      intro hvS a ha
      have hnotm : (m : 𝓞 K) ∉ Q.asIdeal := fun hmem => hvS (hSfinmem' Q hmem)
      have hunr' : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q := by
        by_contra h
        exact hnotm (hram Q h)
      have hunr : (abovePrime (K := K) (L := L) Q).asIdeal.ramificationIdx (𝓞 K) = 1 :=
        hunr' (abovePrime (K := K) (L := L) Q) (abovePrime_liesOver Q)
      obtain ⟨u, hu, hua⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q (abovePrime Q) (abovePrime_liesOver Q) hunr a ha
      refine ⟨u, ?_, ?_⟩
      · show u ∈ Place.localUnits L (Place.ofFinite (abovePrime (K := K) (L := L) Q))
        exact hu
      · show (Place.localNormFinite (abovePrime Q) Q (abovePrime_liesOver Q)) u = a
        exact hua
  exact hU.trans (NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage S
    (fun v : ↥S => (Φ ↑v).range) NK.CFTLib.IdeleHasse.placeAbove
    NK.CFTLib.IdeleHasse.liesOver_placeAbove Φ hbridge
    (fun v => le_rfl) hunit)

end NK.Existence
