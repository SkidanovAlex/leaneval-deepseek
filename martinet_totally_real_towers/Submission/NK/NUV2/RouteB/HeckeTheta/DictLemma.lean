import Mathlib
import Submission.NK.NUV2.HeckeAnalytic.Dict
import Submission.NK.NUV2.HeckeAnalytic.CountDefs
import Submission.NK.NUV2.RouteB.CongCount.CongConeCoset
import Submission.NK.NUV2.RouteB.CongCount.CongConeSetup
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq

/-!
# The lattice-coset count in `K` form and the local congruence dictionary

This is a self-contained copy of the two ingredients of the ray-class/lattice dictionary that are
needed by `NK.NUV2.RouteB.HeckeTheta.rayClassCnt_eq_coset_sum`:

* `piece 𝔪 𝔡 T u β` — the elements `β ∈ K` whose translate `uβ` is `≡ 1` modulo the modulus `𝔪`
  (equivalently `β - u⁻¹ ∈ 𝔪·𝔡⁻¹`), lying in the fundamental cone with the signs of `u⁻¹` and of
  norm `≤ T`, together with `card_piece_eq_cosetConeCnt` identifying its cardinality with the
  lattice-coset count `cosetConeCnt 𝔪 𝔡 u⁻¹ T`;
* `sub_inv_mem_magIdeal_iff` — the local dictionary: for `β ∈ 𝔡⁻¹` and a unit `u`, the membership
  `β - u⁻¹ ∈ 𝔪·𝔡⁻¹` is equivalent to `uβ ≡ 1 (mod 𝔪)` at the primes of the support of `𝔪`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors BigOperators
open NK.NUV2.RouteB

noncomputable section

namespace NK.NUV2.RouteB.HeckeTheta

variable {K : Type} [Field K] [NumberField K]

/-- The positivity of `IsCongElem` is the sign of the mixed embedding. -/
theorem ringEquivReal_alg_eq_mixed (w : InfinitePlace K) (hw : w.IsReal) (x : K) :
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) (x : w.Completion)
      = (mixedEmbedding K x).1 ⟨w, hw⟩ := by
  rw [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    mixedEmbedding_apply_isReal, WithAbs.equiv_apply]


/-! ## The local congruence dictionary -/

/-- The positivity of a unit at the places of `𝔪.pos`, read off from its mixed embedding. -/
theorem mem_posUnits_iff (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    u ∈ NK.NUV2.HeckeAnalytic.posUnits K 𝔪.pos ↔
      ∀ w : NK.NUV2.HeckeAnalytic.posRealPlace 𝔪,
        0 < (mixedEmbedding K (((u : 𝓞 K) : K))).1 ⟨w.1, w.2.2⟩ := by
  rw [NK.NUV2.HeckeAnalytic.posUnits, Subgroup.mem_iInf]
  refine forall_congr' fun w => ?_
  rw [Subgroup.mem_comap, Units.mem_posSubgroup]
  show (0 : ℝ) < ((NK.NUV2.HeckeAnalytic.unitToReal K w.1 w.2.2 u : ℝˣ) : ℝ) ↔ _
  have h : ((NK.NUV2.HeckeAnalytic.unitToReal K w.1 w.2.2 u : ℝˣ) : ℝ)
      = (mixedEmbedding K (((u : 𝓞 K) : K))).1 ⟨w.1, w.2.2⟩ :=
    ringEquivReal_alg_eq_mixed w.1 w.2.2 (((u : 𝓞 K) : K))
  rw [h]

/-- The real coordinate of a unit is nonzero. -/
theorem embedding_unit_ne_zero (w : InfinitePlace K) (hw : w.IsReal) (u : (𝓞 K)ˣ) :
    NumberField.InfinitePlace.embedding_of_isReal hw (((u : 𝓞 K) : K)) ≠ 0 := by
  intro h
  have h2 : (((u : 𝓞 K) : K)) = 0 :=
    RingHom.injective (NumberField.InfinitePlace.embedding_of_isReal hw) (by rw [h, map_zero])
  exact Units.ne_zero u (RingOfIntegers.coe_injective h2)

/-- The coercion of an inverse unit. -/
theorem unit_coe_inv (u : (𝓞 K)ˣ) :
    ((((u⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) : K) = ((((u : (𝓞 K)ˣ)) : K))⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  simp

theorem unit_carrier_ne_zero (u : (𝓞 K)ˣ) : ((((u : (𝓞 K)ˣ)) : K)) ≠ 0 := by
  intro h
  exact Units.ne_zero u (RingOfIntegers.coe_injective h)

theorem embedding_unit_inv (w : InfinitePlace K) (hw : w.IsReal) (u : (𝓞 K)ˣ) :
    (NumberField.InfinitePlace.embedding_of_isReal hw) ((((u⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) : K)
      = ((NumberField.InfinitePlace.embedding_of_isReal hw) ((((u : (𝓞 K)ˣ)) : K)))⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  simp

/-- The valuation of `u β - 1` equals that of `β - u⁻¹`, for a unit `u`. -/
theorem valued_mul_sub_one_eq (q : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) (β : K) :
    (q.valuation K) ((((u : (𝓞 K)ˣ) : K)) * β - 1)
      = (q.valuation K) (β - (((u : (𝓞 K)ˣ) : K))⁻¹) := by
  have hval : (q.valuation K) (((u : (𝓞 K)ˣ) : K)) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro hmem
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem q.asIdeal hmem u.isUnit)
  have hsplit : (((u : (𝓞 K)ˣ) : K)) * β - 1
      = (((u : (𝓞 K)ˣ) : K)) * (β - (((u : (𝓞 K)ˣ) : K))⁻¹) := by
    rw [mul_sub, mul_inv_cancel₀, sub_eq_add_neg]
    intro h
    exact Units.ne_zero u (RingOfIntegers.coe_injective h)
  rw [hsplit, map_mul, hval, one_mul]

/-- `x ≤ exp (-e)` is `e ≤ -log x`, for a nonzero valuation. -/
theorem val_le_exp_neg_iff {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) (e : ℤ) :
    x ≤ WithZero.exp (-e) ↔ e ≤ -x.log := by
  have h := (WithZero.log_le_log hx (WithZero.exp_ne_zero (a := -e))).symm
  rw [h, WithZero.log_exp]
  omega

/-- An inverse unit of `𝓞 K` lies in the unit fractional ideal. -/
theorem inv_unit_mem_one (u : (𝓞 K)ˣ) :
    ((((u : (𝓞 K)ˣ) : K))⁻¹ ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨(u⁻¹ : (𝓞 K)ˣ), by simp⟩

/-- **The local dictionary.**  For a unit `u` and `β ∈ 𝔡⁻¹`, the element `β - u⁻¹` lies in the
lattice `𝔪.ideal·𝔡⁻¹` if and only if `u β ≡ 1 (mod 𝔪)` at every prime of the support, i.e. if and
only if the valuation of `uβ - 1` is at least the exponent of the modulus. -/
theorem sub_inv_mem_magIdeal_iff (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (u : (𝓞 K)ˣ) {β : K}
    (hβ : β ∈ (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) :
    (β - (((u : (𝓞 K)ˣ) : K))⁻¹ ∈
        ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K))
      ↔ (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
          (q.valuation K) ((((u : (𝓞 K)ˣ) : K)) * β - 1) ≤ WithZero.exp (-(𝔪.exps q : ℤ))) := by
  classical
  set y : K := β - (((u : (𝓞 K)ˣ) : K))⁻¹ with hy
  have hMne : ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero _
  have hone : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
      (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
    exact NK.NUV2.RouteB.CongCount.one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K))
      (NK.NUV2.RouteB.CongCount.baseIdeal_ne_zero 𝔡)
  have hβinv : (((u : (𝓞 K)ˣ) : K))⁻¹ ∈
      (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) :=
    hone (inv_unit_mem_one u)
  have hyβ : y ∈ (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hy]
    exact Submodule.sub_mem _ hβ hβinv
  rcases eq_or_ne y 0 with hy0 | hyne
  · have hβeq : β = (((u : (𝓞 K)ˣ) : K))⁻¹ := by
      have h : β - (((u : (𝓞 K)ˣ) : K))⁻¹ = 0 := by rw [← hy, hy0]
      exact sub_eq_zero.mp h
    constructor
    · intro _ q _
      rw [hβeq, mul_inv_cancel₀, sub_self, map_zero]
      · simp
      · intro h
        exact Units.ne_zero u (RingOfIntegers.coe_injective h)
    · intro _
      rw [hy0]
      exact Submodule.zero_mem _
  · have hyne' : ∀ q : HeightOneSpectrum (𝓞 K), (q.valuation K) y ≠ 0 :=
      fun q => (q.valuation K).ne_zero_iff.mpr hyne
    have hycount : ∀ q : HeightOneSpectrum (𝓞 K),
        -FractionalIdeal.count K q ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          ≤ -((q.valuation K) y).log := by
      intro q
      have hM' : (((FractionalIdeal.mk0 K 𝔡)⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
        rw [Units.val_inv_eq_inv_val]
        exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr
          (NK.NUV2.RouteB.CongCount.baseIdeal_ne_zero 𝔡))
      have h1 := (NK.NUV2.RouteB.CongCount.mem_iff_count_le hM' hyne).mp hyβ q
      rwa [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, FractionalIdeal.coe_mk0] at h1
    have key : y ∈ ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
        ↔ (∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 →
            (𝔪.exps q : ℤ) ≤ -((q.valuation K) y).log) := by
      rw [NK.NUV2.RouteB.CongCount.mem_iff_count_le hMne hyne]
      constructor
      · intro h q hq
        have := h q
        rwa [NK.NUV2.RouteB.CongCount.count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq] at this
      · intro h q
        by_cases hq : 𝔪.exps q ≠ 0
        · rw [NK.NUV2.RouteB.CongCount.count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq]
          exact h q hq
        · rw [NK.NUV2.RouteB.CongCount.count_magIdeal, not_not.mp hq, Nat.cast_zero, zero_sub]
          exact hycount q
    rw [key]
    constructor
    · intro h q hq
      rw [valued_mul_sub_one_eq q u β, ← hy]
      exact (val_le_exp_neg_iff (hyne' q) (𝔪.exps q)).mpr (h q hq)
    · intro h q hq
      have h1 : (q.valuation K) y ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
        rw [hy, ← valued_mul_sub_one_eq q u β]
        exact h q hq
      exact (val_le_exp_neg_iff (hyne' q) (𝔪.exps q)).mp h1


/-! ## The lattice-coset count in `K` form -/

/-- The piece of the cone generators attached to the unit `u`: the elements `β` whose translate
`u β` is `≡ 1` modulo the modulus, of norm `≤ T`, in the fundamental cone with the signs of
`u⁻¹`. -/
def piece (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (T : ℝ) (u : (𝓞 K)ˣ) (β : K) : Prop :=
  β - (((u : (𝓞 K)ˣ) : K))⁻¹ ∈
      ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ∧
    mixedEmbedding K β ∈ fundamentalCone K ∧
    (∀ w : NK.NUV2.HeckeAnalytic.posRealPlace 𝔪,
      (((mixedEmbedding K ((((u : (𝓞 K)ˣ) : K))⁻¹)).1 ⟨w.1, w.2.2⟩ > 0 ∧
        (mixedEmbedding K β).1 ⟨w.1, w.2.2⟩ > 0) ∨
      ((mixedEmbedding K ((((u : (𝓞 K)ˣ) : K))⁻¹)).1 ⟨w.1, w.2.2⟩ < 0 ∧
        (mixedEmbedding K β).1 ⟨w.1, w.2.2⟩ < 0))) ∧
    mixedEmbedding.norm (mixedEmbedding K β) ≤ T

/-- The mixed-space set counted by `cosetConeCnt`. -/
def cosetSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (γ : K) (T : ℝ) : Set (mixedSpace K) :=
  {y | y - mixedEmbedding K γ ∈ (idealLattice K (NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡) : Set (mixedSpace K)) ∧
    y ∈ fundamentalCone K ∧
    (∀ w : NK.NUV2.HeckeAnalytic.posRealPlace 𝔪,
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ > 0 ∧ y.1 ⟨w.1, w.2.2⟩ > 0) ∨
      ((mixedEmbedding K γ).1 ⟨w.1, w.2.2⟩ < 0 ∧ y.1 ⟨w.1, w.2.2⟩ < 0)) ∧
    mixedEmbedding.norm y ≤ T}

/-- `cosetConeCnt` is the cardinality of the set `cosetSet`. -/
theorem cosetConeCnt_eq_card_cosetSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (γ : K) (T : ℝ) :
    NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡 γ T
      = Nat.card {y : mixedSpace K // y ∈ cosetSet 𝔪 𝔡 γ T} := rfl

/-- The elements of `𝔪.ideal·𝔡⁻¹` whose mixed embedding is a given lattice point of the coset. -/
theorem exists_mixedEmbedding_eq (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (u : (𝓞 K)ˣ)
    {y : mixedSpace K}
    (hy : y - mixedEmbedding K ((((u : (𝓞 K)ˣ) : K))⁻¹) ∈
      (idealLattice K (NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡) : Set (mixedSpace K))) :
    ∃ t : K, t ∈ ((NK.NUV2.RouteB.CongCount.magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) ∧
      mixedEmbedding K t = y - mixedEmbedding K ((((u : (𝓞 K)ˣ) : K))⁻¹) :=
  (NumberField.mixedEmbedding.mem_idealLattice (K := K) (I := NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡)).mp hy

/-- The piece conditions in the mixed space. -/
theorem exists_of_mem_cosetSet (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (T : ℝ) (u : (𝓞 K)ˣ)
    {y : mixedSpace K} (hy : y ∈ cosetSet 𝔪 𝔡 ((((u : (𝓞 K)ˣ) : K))⁻¹) T) :
    ∃ β : K, mixedEmbedding K β = y ∧ piece 𝔪 𝔡 T u β := by
  obtain ⟨t, ht, hty⟩ := exists_mixedEmbedding_eq 𝔪 𝔡 u hy.1
  have hβeq : mixedEmbedding K (t + (((u : (𝓞 K)ˣ) : K))⁻¹) = y := by
    rw [map_add, hty, sub_add_cancel]
  refine ⟨t + (((u : (𝓞 K)ˣ) : K))⁻¹, hβeq, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t + (((u : (𝓞 K)ˣ) : K))⁻¹ - (((u : (𝓞 K)ˣ) : K))⁻¹ ∈ _
    rw [add_sub_cancel_right]
    exact ht
  · rw [hβeq]; exact hy.2.1
  · rw [hβeq]; exact hy.2.2.1
  · rw [hβeq]; exact hy.2.2.2

/-- The membership of a `piece` element in the mixed-space coset set. -/
theorem mem_cosetSet_of_piece (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (T : ℝ) (u : (𝓞 K)ˣ)
    {β : K} (hβ : piece 𝔪 𝔡 T u β) :
    mixedEmbedding K β ∈ cosetSet 𝔪 𝔡 ((((u : (𝓞 K)ˣ) : K))⁻¹) T := by
  obtain ⟨h1, h2, h3, h4⟩ := hβ
  have hmem : mixedEmbedding K β - mixedEmbedding K ((((u : (𝓞 K)ˣ) : K))⁻¹) ∈
      (idealLattice K (NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡) : Set (mixedSpace K)) := by
    rw [← map_sub]
    exact (NumberField.mixedEmbedding.mem_idealLattice (K := K) (I := NK.NUV2.HeckeAnalytic.dictLattice 𝔪 𝔡)).mpr
      ⟨β - (((u : (𝓞 K)ˣ) : K))⁻¹, h1, rfl⟩
  exact ⟨hmem, h2, h3, h4⟩

/-- **The `K`-level piece is exactly the set counted by `cosetConeCnt`.** -/
theorem card_piece_eq_cosetConeCnt (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (T : ℝ)
    (u : (𝓞 K)ˣ) :
    Nat.card {β : K // piece 𝔪 𝔡 T u β}
      = NK.NUV2.HeckeAnalytic.cosetConeCnt 𝔪 𝔡 ((((u : (𝓞 K)ˣ) : K))⁻¹) T := by
  rw [cosetConeCnt_eq_card_cosetSet]
  refine Nat.card_congr ?_
  refine
    { toFun := fun β => ⟨mixedEmbedding K β.1, mem_cosetSet_of_piece 𝔪 𝔡 T u β.2⟩
      invFun := fun y =>
        ⟨Classical.choose (exists_of_mem_cosetSet 𝔪 𝔡 T u y.2),
          (Classical.choose_spec (exists_of_mem_cosetSet 𝔪 𝔡 T u y.2)).2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro β
    refine Subtype.ext ?_
    exact NumberField.mixedEmbedding_injective K
      (Classical.choose_spec (exists_of_mem_cosetSet 𝔪 𝔡 T u
        (mem_cosetSet_of_piece 𝔪 𝔡 T u β.2))).1
  · intro y
    refine Subtype.ext ?_
    exact (Classical.choose_spec (exists_of_mem_cosetSet 𝔪 𝔡 T u y.2)).1

end NK.NUV2.RouteB.HeckeTheta
