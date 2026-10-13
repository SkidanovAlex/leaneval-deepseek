import Mathlib
import Submission.Work.DSM2p.AALvaln
import Submission.Work.DSM2p.AALcopy_nilp_quot_trick
import Submission.Work.DSM2p.valuation_extend_hgen
import Submission.Work.DSM2p.AALcopy_exists_real_valuation_of_continuous

/-!
# `Work.DSM2p.nilp_sub_auxB2`

The requested lemma (statement untouched, at the bottom of this file): for a commutative ring `R`,
a subring `S ⊆ R`, a prime `𝔮 ⊆ S`, an element `x ∈ 𝔮` and the generation hypothesis

`hgen : ∀ y : R, ∃ n : ℕ, ∃ s : S, y * (x : R) ^ n = (s : R)`

(which says exactly that `R` is generated over `S` by inverting `x`, i.e. `R = S[x⁻¹]`), there is a
valuation `v` on `R` with `IsUnitBall v S` (`v ≤ 1` on `S`), `v x < 1` and `IsContinuousValuation
x v` (the values of the powers of `x` become smaller than any prescribed non-zero element of the
value group).

## The argument

* If `x` is **not a unit** of `R`, quotient `R` by a maximal ideal `𝔪 ∋ x` and take the trivial
  valuation of the residue field: then `v x = 0 < 1`, `v ≤ 1` everywhere, and continuity is
  trivial.
* If `x` **is a unit** of `R`, then `hgen` upgrades to `R = S[x⁻¹]` and `x` is a nonzerodivisor.  A
  minimal prime `𝔰 ≤ 𝔮` of `S` then misses `x`; passing to `A = S ⧸ 𝔰`, its fraction field `K` and
  a valuation subring `V ⊇ A` in which the image of `x` is a non-unit (`Ideal.image_subset_nonunits_valuationSubring`,
  applied to the image of `𝔮`) gives a ring hom `S →+* V`, to which the *quotient trick*
  `nilp_quot_trick` applies: it produces a valuation `vS` on `S` with `vS ≤ 1`, `vS x < 1`,
  `vS x ≠ 0` and continuous at `x`.  That valuation extends to `R` along `hgen`
  (`valuation_extend_hgen`), and a final coarsening of its value group to a rank-one group
  (`exists_real_valuation_of_continuous`) makes it real-valued.

The universe of the value group is finally pushed to the (arbitrary) universe of the statement with
`ULift` (`Valuation.ulift` and the `ULift` order instances below).

## References

* Česnavičius–Scholze, *Purity for flat cohomology*, arXiv:1912.10932, `nilp-lem`.
-/

namespace Work.DSM2p

open scoped Classical

set_option maxHeartbeats 1600000

universe u v

/-! ## Universe flexibility: `ULift` instances for ordered groups and the valuation transport -/

instance uliftLinearOrderedCommMonoidWithZero {α : Type u} [LinearOrderedCommMonoidWithZero α] :
    LinearOrderedCommMonoidWithZero (ULift.{v, u} α) :=
  Function.Injective.linearOrderedCommMonoidWithZero ULift.down ULift.down_injective
    (rfl) (rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (rfl) (fun _ _ => rfl)

instance uliftLinearOrderedCommGroupWithZero {α : Type u} [LinearOrderedCommGroupWithZero α] :
    LinearOrderedCommGroupWithZero (ULift.{v, u} α) where
  __ := uliftLinearOrderedCommMonoidWithZero (α := α)
  __ := ULift.commGroupWithZero

/-- Push a valuation to the universe-lifted copy of its value group. -/
def Valuation.ulift {R : Type*} [CommRing R] {Γ : Type u} [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation R Γ) : Valuation R (ULift.{v, u} Γ) where
  toFun x := ULift.up (v x)
  map_zero' := congrArg ULift.up v.map_zero
  map_one' := congrArg ULift.up v.map_one
  map_mul' x y := congrArg ULift.up (v.map_mul x y)
  map_add_le_max' x y := v.map_add_le_max' x y

@[simp] theorem Valuation.ulift_apply {R : Type*} [CommRing R] {Γ : Type u}
    [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) (x : R) :
    (Valuation.ulift v) x = ULift.up (v x) := rfl

theorem IsUnitBall.ulift {R : Type*} [CommRing R] {Γ : Type u}
    [LinearOrderedCommMonoidWithZero Γ] {v : Valuation R Γ} {s : Set R}
    (h : IsUnitBall v s) : IsUnitBall (Valuation.ulift v) s := by
  intro a ha
  rw [Valuation.ulift_apply]
  exact ULift.up_le.mpr (h a ha)

theorem Valuation.ulift_lt_one {R : Type*} [CommRing R] {Γ : Type u}
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation R Γ} {x : R} (h : v x < 1) :
    (Valuation.ulift v) x < 1 := by
  rw [Valuation.ulift_apply]
  exact ULift.up_lt.mpr h

theorem IsContinuousValuation.ulift {R : Type*} [CommRing R] {Γ : Type u}
    [LinearOrderedCommGroupWithZero Γ] {v : Valuation R Γ} {x : R}
    (h : IsContinuousValuation x v) : IsContinuousValuation x (Valuation.ulift v) := by
  intro γ hγ
  obtain ⟨c, rfl⟩ := ULift.up_surjective γ
  have hc : c ≠ 0 := fun h0 => hγ (by rw [h0]; rfl)
  obtain ⟨n, hn⟩ := h c hc
  exact ⟨n, by
    rw [show (Valuation.ulift v) x ^ n = ULift.up ((v x) ^ n) from by
      rw [Valuation.ulift_apply]; rfl]
    exact hn⟩

/-! ## The trivial valuation of a field -/

/-- The trivial valuation of a field into an arbitrary linearly ordered commutative group with
nonzero: `0 ↦ 0`, everything else `↦ 1`. -/
noncomputable def trivialValuation (K : Type*) [Field K] (Γ : Type*) [LinearOrderedCommGroupWithZero Γ] :
    Valuation K Γ where
  toFun z := if z = 0 then 0 else 1
  map_zero' := if_pos rfl
  map_one' := if_neg one_ne_zero
  map_mul' x y := by
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, mul_one]
  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · rw [if_pos hxy]; exact zero_le
    · rw [if_neg hxy]
      by_cases hx : x = 0
      · rw [if_pos hx]
        have hy : y ≠ 0 := fun hy => hxy (by rw [hx, hy, zero_add])
        rw [if_neg hy]
        exact le_max_right 0 1
      · rw [if_neg hx]
        exact le_max_left 1 _

@[simp] theorem trivialValuation_zero {K : Type*} [Field K] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] :
    trivialValuation K Γ 0 = 0 := if_pos rfl

@[simp] theorem trivialValuation_apply {K : Type*} [Field K] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (z : K) :
    trivialValuation K Γ z = if z = 0 then 0 else 1 := rfl

/-! ## The main theorem -/

theorem nilp_sub_auxB2 {R : Type*} [CommRing R] (S : Subring R)
    (𝔮 : Ideal S) (h𝔮 : 𝔮.IsPrime) (x : S) (hx : x ∈ 𝔮)
    (hgen : ∀ y : R, ∃ n : ℕ, ∃ s : S, y * (x : R) ^ n = (s : R)) :
    ∃ (Γ₀ : Type*) (_ : LinearOrderedCommGroupWithZero Γ₀), ∃ v : Valuation R Γ₀,
      IsUnitBall v (S : Set R) ∧ v (x : R) < 1 ∧ IsContinuousValuation (x : R) v := by
  by_cases hunit : IsUnit (x : R)
  · -- ## Case 2: `x` is a unit of `R`
    -- (a) `x` is a nonzerodivisor of `R` and of `S`
    have hregR : IsSMulRegular R (x : R) := by
      intro a b hab
      exact hunit.mul_left_cancel (by simpa [smul_eq_mul] using hab)
    have hregS : IsSMulRegular S x := by
      intro a b hab
      refine Subtype.ext (hregR ?_)
      simpa [smul_eq_mul] using congrArg (fun z : S => (z : R)) hab
    -- (b) a minimal prime `𝔰 ≤ 𝔮` of `S`, which misses `x`
    haveI : 𝔮.IsPrime := h𝔮
    obtain ⟨𝔰, h𝔰min, h𝔰le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := 𝔮) bot_le
    have h𝔰prime : 𝔰.IsPrime := h𝔰min.isPrime
    haveI : 𝔰.IsPrime := h𝔰prime
    have hx𝔰 : x ∉ 𝔰 := by
      have hann : (Module.annihilator S S : Ideal S) = ⊥ := by
        ext r; rw [Ideal.mem_bot]; constructor
        · intro h
          have := (Module.mem_annihilator (R := S)).1 h 1
          simpa using this
        · intro h; subst h; rw [Module.mem_annihilator]; intro m; simp
      have hmem : 𝔰 ∈ (Module.annihilator S S).minimalPrimes := by
        rw [hann]; exact h𝔰min
      exact IsSMulRegular.notMem_of_mem_minimalPrimes hregS hmem
    -- (c) the domain `S ⧸ 𝔰`, its fraction field `K`, and the subring `A = image`
    haveI hdom : IsDomain (S ⧸ 𝔰) := Ideal.Quotient.isDomain 𝔰
    let K := FractionRing (S ⧸ 𝔰)
    let A : Subring K := (algebraMap (S ⧸ 𝔰) K).range
    let qbar : S ⧸ 𝔰 := Ideal.Quotient.mk 𝔰 x
    have hqbar : qbar ≠ 0 := by
      intro h1
      exact hx𝔰 (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    let xA : A := ⟨algebraMap (S ⧸ 𝔰) K qbar, Set.mem_range_self qbar⟩
    -- the ideal of `A` generated by the image of `𝔮`
    let I : Ideal A := (𝔮.map (Ideal.Quotient.mk 𝔰)).map (algebraMap (S ⧸ 𝔰) K).rangeRestrict
    have hxA_mem : xA ∈ I := by
      show (algebraMap (S ⧸ 𝔰) K).rangeRestrict (Ideal.Quotient.mk 𝔰 x) ∈ _
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
    have hI_ne : I ≠ ⊤ := by
      intro htop
      have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
      obtain ⟨z, hzJ, hz1⟩ := (Ideal.mem_map_iff_of_surjective _
        (algebraMap (S ⧸ 𝔰) K).rangeRestrict_surjective).mp h1
      have hz : z = 1 := by
        apply IsFractionRing.injective (S ⧸ 𝔰) K
        have h2 := congrArg (fun w : A => (w : K)) hz1
        simpa using h2
      subst hz
      obtain ⟨y, hy𝔮, hy1⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk 𝔰)
        Ideal.Quotient.mk_surjective).mp hzJ
      have hy1' : Ideal.Quotient.mk 𝔰 y = Ideal.Quotient.mk 𝔰 1 := by simpa using hy1
      have hy𝔰 : y - 1 ∈ 𝔰 := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hy1', map_one, sub_self]
      exact h𝔮.ne_top (Ideal.eq_top_iff_one 𝔮 |>.mpr (by
        have : (1 : S) = y - (y - 1) := by ring
        rw [this]; exact 𝔮.sub_mem hy𝔮 (h𝔰le hy𝔰)))
    -- (d) a valuation subring `V ⊇ A` in which `xA` is a non-unit
    obtain ⟨V, hAV, hIV⟩ :=
      Ideal.image_subset_nonunits_valuationSubring (K := K) (A := A) (I := I) hI_ne
    -- (e) the ring hom `S →+* V` and the quotient trick
    let g : S ⧸ 𝔰 →+* A := (algebraMap (S ⧸ 𝔰) K).rangeRestrict
    let f : S →+* V := (Subring.inclusion hAV).comp (g.comp (Ideal.Quotient.mk 𝔰))
    have hfx : ((f x : V) : K) = (xA : K) := rfl
    have hf0 : (f x : V) ≠ 0 := by
      intro h0
      have h1 : (xA : K) = 0 := by rw [← hfx, h0]; rfl
      have h2 : algebraMap (S ⧸ 𝔰) K qbar = 0 := h1
      exact hqbar (IsFractionRing.injective (S ⧸ 𝔰) K (by simpa using h2))
    have hf1 : ¬ IsUnit (f x) := by
      have hmem : ((f x : V) : K) ∈ V.nonunits := by
        rw [hfx]
        exact hIV ⟨xA, hxA_mem, rfl⟩
      have hlt : V.valuation ((f x : V) : K) < 1 := (ValuationSubring.mem_nonunits_iff V).mp hmem
      have hmem_m : f x ∈ IsLocalRing.maximalIdeal V :=
        (ValuationSubring.valuation_lt_one_iff V (f x)).mpr hlt
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem_m
    obtain ⟨Γ₀, hΓ₀, vS, hvSball, hvSlt, hvSne, hvScont⟩ := nilp_quot_trick V f hf0 hf1
    letI := hΓ₀
    -- (f) extend the valuation to `R` along `hgen`
    obtain ⟨vR, hvRs, hvRx⟩ := valuation_extend_hgen S x hgen vS hvSne
    -- (g) coarsen to a real-valued valuation
    obtain ⟨w, hwball, hwlt, hwcont⟩ := exists_real_valuation_of_continuous vR (x : R) (S : Set R)
      (fun s hs => by rw [hvRs ⟨s, hs⟩]; exact hvSball ⟨s, hs⟩)
      (by rw [hvRx]; exact hvSlt)
      (by rw [hvRx]; exact hvSne)
      (by
        intro γ hγ
        obtain ⟨n, hn⟩ := hvScont γ hγ
        exact ⟨n, by simpa [map_pow, hvRs] using hn⟩)
    -- (h) lift the value group to the universe of the statement
    refine ⟨ULift (WithZero (Multiplicative ℝ)), inferInstance, Valuation.ulift w, ?_, ?_, ?_⟩
    · exact IsUnitBall.ulift hwball
    · exact Valuation.ulift_lt_one hwlt
    · exact IsContinuousValuation.ulift hwcont
  · -- ## Case 1: `x` is not a unit of `R`
    obtain ⟨𝔪, hmax, hle⟩ := Ideal.exists_le_maximal (Ideal.span ({(x : R)} : Set R))
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    haveI : 𝔪.IsMaximal := hmax
    have hx𝔪 : (x : R) ∈ 𝔪 := hle (Ideal.subset_span (Set.mem_singleton (x : R)))
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let v : Valuation R (WithZero (Multiplicative ℝ)) :=
      Valuation.comap (Ideal.Quotient.mk 𝔪)
        (trivialValuation (R ⧸ 𝔪) (WithZero (Multiplicative ℝ)))
    have hvx : v (x : R) = 0 := by
      rw [Valuation.comap_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx𝔪]
      exact trivialValuation_zero
    refine ⟨ULift (WithZero (Multiplicative ℝ)), inferInstance, Valuation.ulift v, ?_, ?_, ?_⟩
    · intro s _
      rw [Valuation.ulift_apply]
      refine ULift.up_le.mpr ?_
      rw [Valuation.comap_apply]
      by_cases h : Ideal.Quotient.mk 𝔪 s = 0
      · rw [h, trivialValuation_zero]; exact zero_le
      · rw [trivialValuation_apply, if_neg h]
    · rw [Valuation.ulift_apply, hvx]
      exact ULift.up_lt.mpr zero_lt_one
    · intro γ hγ
      obtain ⟨c, rfl⟩ := ULift.up_surjective γ
      have hc : c ≠ 0 := fun h0 => hγ (by rw [h0]; rfl)
      refine ⟨1, ?_⟩
      rw [pow_one, Valuation.ulift_apply, hvx]
      exact ULift.up_lt.mpr (zero_lt_iff.mpr hc)

end Work.DSM2p
