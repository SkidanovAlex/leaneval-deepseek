import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.complexUnits_quot_pow
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.realUnits_quot_pow_two
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.units_quot_pow_of_ringEquiv
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.no_isReal_of_isPrimitiveRoot_ne_two
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.norm_algebraMap_natCast_adicCompletion_eq_one_of_notMem
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.norm_algebraMap_natCast_adicCompletion_eq_zpow_localDegree
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.norm_algebraMap_natCast_infinitePlace
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_mem
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
import Submission.NK.GlobalCFT.IdeleNorm.globalCFT_abs_principalIdele

/-!
# The product of the local `p`-power indices is `p ^ (2 * |S|)` (Milne, *CFT*, Prop. 6.8 / Lemma 6.6)

Let `K` be a number field, `p` a rational prime and `ζ ∈ K` a primitive `p`-th root of unity.
Let `S` be a finite set of places of `K` containing every archimedean place and every finite
place above `p`.  Then

  `∏_{v ∈ S} [K_vˣ : (K_vˣ)^p] = p ^ (2 * |S|)`.

The local computation is the classical one (`|K_vˣ : (K_vˣ)^p| = p ⋅ |μ_p(K_v)| / |p|_v`):

* `v` finite, `v | p` (so `p` is the residue characteristic and `K_v ⊇ ℚ_p`):
  `[K_vˣ : (K_vˣ)^p] = p ^ ([K_v : ℚ_p] + 2)` (`localIndex_finite_mem`) and
  `|p|_v = p ^ (-[K_v : ℚ_p])` (`adicAbv_prime_eq_zpow_localDegree`), so the two factors
  multiply to `p²`;
* `v` finite, `v ∤ p`: `[K_vˣ : (K_vˣ)^p] = p²` (`localIndex_finite_notMem`) and `|p|_v = 1`;
* `v` archimedean complex: `ℂˣ` is divisible, so the index is `1`, and `|p|_v = p²`;
* `v` archimedean real: necessarily `p = 2` (a real place of a field containing a primitive
  `p`-th root of unity forces `p = 2`), the index is `2` and `|p|_v = p = 2`.

Summing up, `∏_{v ∈ S} [K_vˣ : (K_vˣ)^p] = ∏_{v ∈ S} p²/|p|_v`, and `∏_{v ∈ S}|p|_v = 1` by the
product formula, because `S` contains every place at which `|p|_v ≠ 1` (the places above `p` by
hypothesis, the archimedean places trivially).  The product formula is fed in through the
content of the principal idèle `(p)_v ∈ 𝕀 K` (`globalCFT_abs_principalIdele`).
-/

set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

variable {K : Type} [Field K] [NumberField K]

/-- The normalized local absolute value of a global unit at a finite place, evaluated through the
principal idèle: it is the norm of the image in the completion. -/
private lemma localAbs_principalIdele_finite (u : Kˣ)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ((Idele.localAbs K (Place.ofFinite q) (Idele.principalIdele K u (Place.ofFinite q)) : ℝˣ) : ℝ)
      = ‖algebraMap K (q.adicCompletion K) (u : K)‖ := by
  rw [Idele.localAbs_ofFinite, Idele.principalIdele_apply, Units.val_mk0, Units.coe_map]
  rfl

/-- The normalized local absolute value of a global unit at an archimedean place: it is the
`mult`-th power of the norm of the image in the completion. -/
private lemma localAbs_principalIdele_infinite (u : Kˣ) (w : NumberField.InfinitePlace K) :
    ((Idele.localAbs K (Place.ofInfinite w)
      (Idele.principalIdele K u (Place.ofInfinite w)) : ℝˣ) : ℝ)
      = ‖algebraMap K w.Completion (u : K)‖ ^ w.mult := by
  rw [Idele.localAbs_ofInfinite, Idele.principalIdele_apply, Units.val_pow_eq_pow_val,
    Units.val_mk0, Units.coe_map]
  congr 1

end NK.GlobalCFTdeep.SecondInequality.KummerCase

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

theorem prod_localPow_eq_pow {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) :
    ∏ v ∈ S, Nat.card ((NK.GlobalCFT.Place.localField K v)ˣ ⧸ (KummerCase.localPow (K := K) p v)) = p ^ (2 * S.card) := by
  classical
  have hp0K : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Kˣ, (u₀ : K) = (p : K) := ⟨Units.mk0 (p : K) hp0K, Units.val_mk0 _⟩
  obtain ⟨la, hla⟩ : ∃ la : Place K → ℝˣ,
      ∀ v, la v = Idele.localAbs K v (Idele.principalIdele K u₀ v) := ⟨_, fun v => rfl⟩
  -- **The per-place identity** `[K_vˣ : (K_vˣ)^p] · |p|_v = p²`.
  have hper : ∀ v ∈ S, (Nat.card ((Place.localField K v)ˣ ⧸ (localPow (K := K) p v)) : ℝ)
      * (la v : ℝ) = (p : ℝ) ^ 2 := by
    intro v hv
    rcases v with w | q
    · -- archimedean places
      have hlaw : (la (Place.ofInfinite w) : ℝ) =
          ‖algebraMap K w.Completion (p : K)‖ ^ w.mult := by
        rw [hla (Place.ofInfinite w), localAbs_principalIdele_infinite u₀ w, hu₀]
      rcases w.isReal_or_isComplex with hwr | hwc
      · -- a real place: then `p = 2`, the index is `2` and the absolute value of `p` is `p`
        have hp2 : p = 2 := by
          by_contra hne
          exact no_isReal_of_isPrimitiveRoot_ne_two hp hne hζ w hwr
        subst hp2
        have hidx : Nat.card ((Place.localField K (Place.ofInfinite w))ˣ ⧸
            (localPow (K := K) 2 (Place.ofInfinite w)))
            = Nat.card (ℝˣ ⧸ (powMonoidHom 2 : ℝˣ →* ℝˣ).range) :=
          units_quot_pow_of_ringEquiv
            (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwr) 2
        rw [hidx, realUnits_quot_pow_two, hlaw, norm_algebraMap_natCast_infinitePlace w 2,
          hwr.mult_eq_one, pow_one]
        norm_num
      · -- a complex place: `ℂˣ` is divisible, and the normalized absolute value of `p` is `p²`
        have hidx : Nat.card ((Place.localField K (Place.ofInfinite w))ˣ ⧸
            (localPow (K := K) p (Place.ofInfinite w))) = 1 :=
          (units_quot_pow_of_ringEquiv
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) p).trans
            (complexUnits_quot_pow p hp.pos)
        rw [hidx, hlaw, norm_algebraMap_natCast_infinitePlace w p, hwc.mult_eq_two]
        norm_num
    · -- finite places
      have hlaq : (la (Place.ofFinite q) : ℝ) = ‖algebraMap K (q.adicCompletion K) (p : K)‖ := by
        rw [hla (Place.ofFinite q), localAbs_principalIdele_finite u₀ q, hu₀]
      have hζq : ∃ ζ' : q.adicCompletion K, IsPrimitiveRoot ζ' p :=
        ⟨algebraMap K (q.adicCompletion K) ζ,
          hζ.map_of_injective (RingHom.injective (algebraMap K (q.adicCompletion K)))⟩
      by_cases hmem : (p : 𝓞 K) ∈ q.asIdeal
      · -- `p` is the residue characteristic: the index is `p ^ ([K_q : ℚ_p] + 2)`
        have hidx : Nat.card ((Place.localField K (Place.ofFinite q))ˣ ⧸
            (localPow (K := K) p (Place.ofFinite q)))
            = p ^ (NK.LocalInputs.localDegree K q + 2) :=
          NK.GlobalCFTdeep.SecondInequality.localIndex_finite_mem q hp hmem hζq
        rw [hidx, hlaq, norm_algebraMap_natCast_adicCompletion_eq_zpow_localDegree q hp hmem]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        push_cast
        rw [zpow_neg, zpow_natCast, pow_add,
          mul_comm ((p : ℝ) ^ (NK.LocalInputs.localDegree K q)) ((p : ℝ) ^ 2), mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero (NK.LocalInputs.localDegree K q) hp0), mul_one]
      · -- `p` is a local unit: the index is `p²` and the absolute value of `p` is `1`
        have hidx : Nat.card ((Place.localField K (Place.ofFinite q))ˣ ⧸
            (localPow (K := K) p (Place.ofFinite q))) = p ^ 2 :=
          NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem q hp hmem hζq
        rw [hidx, hlaq, norm_algebraMap_natCast_adicCompletion_eq_one_of_notMem q hmem]
        push_cast
        ring
  -- the terms of the product formula vanish off `S`
  have hla1 : ∀ v : Place K, v ∉ S → la v = 1 := by
    intro v hv
    have hfinite : Place.IsFinite v := by
      rcases v with w | q
      · exact absurd (hSinf w) hv
      · exact Place.isFinite_ofFinite q
    obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfinite
    have hnotmem : (p : 𝓞 K) ∉ q.asIdeal := fun hmem => hv (hSp q hmem)
    apply Units.ext
    rw [hla (Place.ofFinite q), localAbs_principalIdele_finite u₀ q, hu₀,
      norm_algebraMap_natCast_adicCompletion_eq_one_of_notMem q hnotmem]
    simp
  -- the product formula, restricted to `S`
  have hprod : ∏ v ∈ S, la v = 1 := by
    have h1 : ∏ᶠ v : Place K, la v = 1 := by
      have h2 : (∏ᶠ v : Place K, Idele.localAbs K v (Idele.principalIdele K u₀ v)) = 1 := by
        rw [← Idele.abs_apply]
        exact IdeleNorm.globalCFT_abs_principalIdele u₀
      simpa only [hla] using h2
    rw [finprod_eq_prod_of_mulSupport_subset la ?_] at h1
    · exact h1
    · intro v hv
      simp only [Function.mem_mulSupport] at hv
      by_contra hcon
      exact hv (hla1 v hcon)
  -- assemble in `ℝ`
  have hmain : (∏ v ∈ S,
      ((Nat.card ((Place.localField K v)ˣ ⧸ (localPow (K := K) p v))) : ℝ))
      = (p : ℝ) ^ (2 * S.card) := by
    have h1 : (∏ v ∈ S, ((Nat.card ((Place.localField K v)ˣ ⧸ (localPow (K := K) p v))) : ℝ))
        * (∏ v ∈ S, (la v : ℝ)) = ∏ v ∈ S, ((p : ℝ) ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl hper
    have h2 : (∏ v ∈ S, (la v : ℝ)) = 1 := by
      rw [← Units.coe_prod, hprod, Units.val_one]
    rw [h2, mul_one, Finset.prod_const] at h1
    rw [h1, ← pow_mul]
  refine Nat.cast_injective (R := ℝ) ?_
  rw [Nat.cast_prod, Nat.cast_pow, hmain]

end NK.GlobalCFTdeep.SecondInequality.KummerCase
