import Mathlib
import Submission.NK.GlobalCFT.Norm
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.IdeleNorm
import Submission.NK.GlobalCFT.Norm.globalCFT_localAbs_localNormInfinite
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg

/-!
# The content of the norm of an idèle

For a finite extension `L / K` of number fields and an idèle `x` of `L`, the **content** (the
normalized absolute value) of the idèlic norm equals the content of `x`:

`|N_{L/K} x|_K = |x|_L`,  i.e. `Idele.abs K (Idele.normIdeleHom K L x) = Idele.abs L x`.

This is the compatibility of the idèlic norm with the content homomorphism `𝕀 K →* ℝˣ`; it is
the statement that the norm map on idèles preserves the norm-one subgroups `𝕀¹`.

## Strategy

Writing `abs K y = ∏ᶠ_v |y_v|_v` as a finitary product of the normalized local absolute values,
the identity follows by comparing the two products place by place.  The two local inputs are

* `globalCFT_localAbs_localNormFinite`: at a finite place, `v x` is multiplied by the inertia
  degree `f` under the local norm (`globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg`), which
  is exactly the change of normalization between `toNNReal` at a prime and at a prime above it
  (`toNNReal_absNorm_pow`);
* `globalCFT_localAbs_localNormInfinite`: at an infinite place (proved by the sibling module
  `NK.GlobalCFT.Norm.globalCFT_localAbs_localNormInfinite`), where the local fields are `ℝ`
  and `ℂ`.

The global comparison then uses the fibration of the places of `L` over the places of `K`
(`globalCFT_placeUnder`, `globalCFT_fiberPlaces`) together with
`Finset.prod_fiberwise_of_maps_to` (in the form `finprod_prod_filter`).

## Main result

* `NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct WithZero NNReal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace NK.GlobalCFT.Norm

section Helpers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- In the value group `ℤᵐ⁰`, the `e`-th power map is injective on nonzero elements. -/
theorem withZero_pow_left_cancel' {e : ℕ} (he : e ≠ 0)
    {a b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) (h : a ^ e = b ^ e) : a = b := by
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow he] at h
    exact (pow_ne_zero e hb) h.symm
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨WithZero.log a, WithZero.exp_log ha⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, WithZero.exp n = b := ⟨WithZero.log b, WithZero.exp_log hb⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul, nsmul_eq_mul] at h
  rw [WithZero.exp_inj]
  exact mul_left_cancel₀ (show (e : ℤ) ≠ 0 from by exact_mod_cast he) h

/-- The local norm multiplies valuations by the inertia degree. -/
theorem globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : (q.adicCompletion L)ˣ,
      Valued.v (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L)) =
        (Valued.v (x : q.adicCompletion L)) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hIC : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension Q q hq
  have hnorm_int : ∀ y : q.adicCompletion L, y ∈ q.adicCompletionIntegers L →
      Algebra.norm (Q.adicCompletion K) y ∈ Q.adicCompletionIntegers K := by
    intro y hy
    have hint : IsIntegral (Q.adicCompletionIntegers K) y :=
      (IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)
        (R := Q.adicCompletionIntegers K) (B := q.adicCompletion L) (x := y)).mpr
        ⟨⟨y, hy⟩, rfl⟩
    have h2 := Algebra.isIntegral_norm (Q.adicCompletion K) hint
    obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff (A := Q.adicCompletionIntegers K)
      (R := Q.adicCompletionIntegers K) (B := Q.adicCompletion K)
      (x := Algebra.norm (Q.adicCompletion K) y)).mp h2
    exact hz ▸ z.2
  have hnorm_unit : ∀ y : q.adicCompletion L, Valued.v y = 1 →
      Valued.v (Algebra.norm (Q.adicCompletion K) y) = 1 := by
    intro y hy
    have hyne : y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp (by rw [hy]; exact one_ne_zero)
    have hmem : y ∈ q.adicCompletionIntegers L :=
      (mem_adicCompletionIntegers (𝓞 L) L q).mpr (le_of_eq hy)
    have hmem' : y⁻¹ ∈ q.adicCompletionIntegers L := by
      rw [mem_adicCompletionIntegers (𝓞 L) L q, map_inv₀, hy]
      exact le_refl 1
    have h1 : Valued.v (Algebra.norm (Q.adicCompletion K) y) ≤ 1 :=
      (mem_adicCompletionIntegers (𝓞 K) K Q).mp (hnorm_int y hmem)
    have h2 : Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) ≤ 1 :=
      (mem_adicCompletionIntegers (𝓞 K) K Q).mp (hnorm_int y⁻¹ hmem')
    have hprod : Valued.v (Algebra.norm (Q.adicCompletion K) y) *
        Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyne]
      simp
    have hge : (1 : ℤᵐ⁰) ≤ Valued.v (Algebra.norm (Q.adicCompletion K) y) :=
      calc (1 : ℤᵐ⁰) = Valued.v (Algebra.norm (Q.adicCompletion K) y) *
            Valued.v (Algebra.norm (Q.adicCompletion K) y⁻¹) := hprod.symm
        _ ≤ Valued.v (Algebra.norm (Q.adicCompletion K) y) * 1 := mul_le_mul_right h2 _
        _ = Valued.v (Algebra.norm (Q.adicCompletion K) y) := mul_one _
    exact le_antisymm h1 hge
  have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq :=
    RingHom.algebraMap_toAlgebra _
  have hkey : ∀ π : q.adicCompletionIntegers L,
      Valued.v (π : q.adicCompletion L) = (WithZero.exp (-1) : ℤᵐ⁰) →
      Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) =
        (WithZero.exp (-1) : ℤᵐ⁰) ^ (q.asIdeal.inertiaDeg (𝓞 K)) := by
    intro π hπval
    obtain ⟨ϖ, hϖval, -⟩ :=
      Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers (K := K) Q
    have hπne : (π : q.adicCompletion L) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hπval]; exact WithZero.exp_ne_zero)
    set e := q.asIdeal.ramificationIdx (𝓞 K) with he
    set f := q.asIdeal.inertiaDeg (𝓞 K) with hf
    have he0 : e ≠ 0 := by
      rw [he]
      exact (Ideal.ramificationIdx_pos (q := q.asIdeal) (𝓞 K)).ne'
    have hn : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = e * f := by
      rw [he, hf]
      exact (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        Q q hq).symm
    set u : q.adicCompletion L :=
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K) *
        ((π : q.adicCompletion L) ^ e)⁻¹ with hu
    have hvalπe : Valued.v ((π : q.adicCompletion L) ^ e) = (WithZero.exp (-1) : ℤᵐ⁰) ^ e := by
      rw [Valuation.map_pow, hπval]
    have hvalalg : Valued.v ((algebraMap (Q.adicCompletion K) (q.adicCompletion L))
        (ϖ : Q.adicCompletion K)) = (WithZero.exp (-1) : ℤᵐ⁰) ^ e := by
      rw [halg,
        Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
          (ϖ : Q.adicCompletion K), hϖval, ← he]
    have huval : Valued.v u = 1 := by
      rw [hu, map_mul, map_inv₀, hvalalg, hvalπe,
        mul_inv_cancel₀ (pow_ne_zero e (WithZero.exp_ne_zero))]
    have hsplit : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K) =
        (π : q.adicCompletion L) ^ e * u := by
      rw [hu, ← mul_assoc, mul_comm ((π : q.adicCompletion L) ^ e), mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero e hπne), mul_one]
    have hnormsplit : Algebra.norm (Q.adicCompletion K)
          ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K)) =
        (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) ^ e *
          Algebra.norm (Q.adicCompletion K) u := by
      rw [hsplit, map_mul, map_pow]
    have hLHS : Valued.v (Algebra.norm (Q.adicCompletion K)
        ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K))) =
        (WithZero.exp (-1) : ℤᵐ⁰) ^ (e * f) := by
      rw [Algebra.norm_algebraMap, Valuation.map_pow, hϖval, hn]
    have heq : (Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L))) ^ e =
        ((WithZero.exp (-1) : ℤᵐ⁰) ^ f) ^ e := by
      have h1 : Valued.v (Algebra.norm (Q.adicCompletion K)
            ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)) (ϖ : Q.adicCompletion K))) =
          (Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L))) ^ e := by
        rw [hnormsplit, map_mul, map_pow, hnorm_unit u huval, mul_one]
      rw [← h1, hLHS, mul_comm e f, pow_mul]
    exact withZero_pow_left_cancel' he0 (pow_ne_zero f WithZero.exp_ne_zero) heq
  intro x
  obtain ⟨π, hπval, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers (K := L) q
  have hπkey := hkey π hπval
  set f := q.asIdeal.inertiaDeg (𝓞 K) with hf
  have hπne : (π : q.adicCompletion L) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mp (by rw [hπval]; exact WithZero.exp_ne_zero)
  set m : ℤ := WithZero.log (Valued.v (x : q.adicCompletion L)) with hm
  have hvxne : Valued.v (x : q.adicCompletion L) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero x)
  have hexpm : Valued.v (x : q.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hvxne).symm
  set y : q.adicCompletion L := (x : q.adicCompletion L) * (π : q.adicCompletion L) ^ m with hy
  have hvaly : Valued.v y = 1 := by
    rw [hy, map_mul, hexpm, map_zpow₀, hπval, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      show m + m • (-1 : ℤ) = 0 by ring, WithZero.exp_zero]
  have hNπ : Valued.v (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) =
      (WithZero.exp (-1) : ℤᵐ⁰) ^ f := hπkey
  have hxsplit : (x : q.adicCompletion L) = y * (π : q.adicCompletion L) ^ (-m) := by
    rw [hy, mul_assoc, ← zpow_add₀ hπne m (-m), add_neg_cancel, zpow_zero, mul_one]
  have hnormx : Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L) =
      Algebra.norm (Q.adicCompletion K) y *
        (Algebra.norm (Q.adicCompletion K) (π : q.adicCompletion L)) ^ (-m) := by
    rw [hxsplit, map_mul, Algebra.norm_zpow]
  rw [hnormx, map_mul, hnorm_unit y hvaly, one_mul, map_zpow₀, hNπ, hexpm]
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
  congr 1
  ring



open WithZeroMulInt

/-- Base change for `WithZeroMulInt.toNNReal`: if `e' = e ^ k` with `k ≠ 0`, then `toNNReal`
at `e'` is the `k`-th power of `toNNReal` at `e`. -/
theorem toNNReal_eq_pow_of_base {e e' : ℝ≥0} (he : e ≠ 0) (he' : e' ≠ 0) {k : ℕ}
    (hk : k ≠ 0) (hbase : e' = e ^ k) (z : ℤᵐ⁰) :
    toNNReal he (z ^ k) = toNNReal he' z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [zero_pow hk, map_zero, map_zero]
  · rw [map_pow, toNNReal_neg_apply he hz, toNNReal_neg_apply he' hz, hbase,
      ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]

/-- The `toNNReal` normalizations at a prime and at a prime above it differ by the inertia
degree: `toNNReal` at `q` is `toNNReal` at `Q` raised to the `f`. -/
theorem toNNReal_absNorm_pow (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (z : ℤᵐ⁰) :
    toNNReal (HeightOneSpectrum.absNorm_ne_zero Q) (z ^ q.asIdeal.inertiaDeg (𝓞 K)) =
      toNNReal (HeightOneSpectrum.absNorm_ne_zero q) z := by
  have hbase : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ≥0) =
      ((Ideal.absNorm Q.asIdeal : ℕ) : ℝ≥0) ^ q.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← Ideal.absNorm_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 L) Q.asIdeal q.asIdeal,
      Nat.cast_pow]
  exact toNNReal_eq_pow_of_base (HeightOneSpectrum.absNorm_ne_zero Q)
    (HeightOneSpectrum.absNorm_ne_zero q)
    (Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)).ne' hbase z

/-- **The local compatibility of the content with the local norm at a finite place.** -/
theorem globalCFT_localAbs_localNormFinite (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (y : (q.adicCompletion L)ˣ) :
    Idele.localAbs K (Place.ofFinite Q) (Place.localNormFinite q Q hq y) =
      Idele.localAbs L (Place.ofFinite q) y := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  rw [show Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (Q.adicCompletion K)) from rfl]
  rw [Idele.localAbs_ofFinite, Idele.localAbs_ofFinite]
  apply Units.ext
  simp only [Units.coe_map, Units.val_mk0]
  rw [NumberField.FinitePlace.norm_def (v := Q) (x := Algebra.norm (Q.adicCompletion K)
        (y : q.adicCompletion L)),
    NumberField.FinitePlace.norm_def (v := q) (x := (y : q.adicCompletion L))]
  rw [globalCFT_val_norm_adicCompletion_eq_pow_inertiaDeg Q q hq y]
  exact congrArg _ (toNNReal_absNorm_pow Q q hq (Valued.v (y : q.adicCompletion L)))


/-! ## The place of `K` below a place of `L`, and the fibres -/

/-- A choice of the place of `K` below a given place of `L`. -/
noncomputable def globalCFT_placeUnder (w : Place L) : Place K :=
  Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

theorem liesOver_globalCFT_placeUnder (w : Place L) :
    Place.LiesOver w (globalCFT_placeUnder (K := K) (L := L) w) :=
  Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

/-- The places of `L` above a given place of `K`, as a finset. -/
noncomputable def globalCFT_fiberPlaces (v : Place K) : Finset (Place L) :=
  match v with
  | Sum.inl v' => (Place.fiberInfinite (K := K) (L := L) v').map
      ⟨Place.ofInfinite, fun _ _ h => Place.ofInfinite_inj.mp h⟩
  | Sum.inr Q => (Place.primesOverFinite (K := K) (L := L) Q).map
      ⟨Place.ofFinite, fun _ _ h => Place.ofFinite_inj.mp h⟩

theorem mem_globalCFT_fiberPlaces {v : Place K} {w : Place L} :
    w ∈ globalCFT_fiberPlaces (K := K) (L := L) v ↔ Place.LiesOver w v := by
  cases v with
  | inl v' =>
    constructor
    · intro hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
      exact Place.liesOver_ofInfinite ((Place.mem_fiberInfinite).mp hw')
    · intro hw
      rcases hw with ⟨w', v'', hw', hv', hLies⟩ | ⟨q', Q', hw', hv', hLies⟩
      · have hvv : v' = v'' := Place.ofInfinite_inj.mp hv'
        rw [hw']
        exact Finset.mem_map.mpr ⟨w', (Place.mem_fiberInfinite).mpr (hvv.symm ▸ hLies), rfl⟩
      · exact absurd hv' (Place.ofInfinite_ne_ofFinite v' Q')
  | inr Q =>
    constructor
    · intro hw
      obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hw
      exact Place.liesOver_ofFinite ((Place.mem_primesOverFinite).mp hq')
    · intro hw
      rcases hw with ⟨w', v'', hw', hv', hLies⟩ | ⟨q', Q', hw', hv', hLies⟩
      · exact absurd hv' (Place.ofInfinite_ne_ofFinite v'' Q).symm
      · have hQQ : Q = Q' := Place.ofFinite_inj.mp hv'
        rw [hw']
        exact Finset.mem_map.mpr ⟨q', (Place.mem_primesOverFinite).mpr (hQQ.symm ▸ hLies), rfl⟩

/-! ## The content of the norm of an idèle -/

end Helpers

theorem globalCFT_abs_normIdeleHom {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (x : 𝕀[L]) :
    Idele.abs K (Idele.normIdeleHom K L x) = Idele.abs L x := by
  classical
  set f : Place L → ℝˣ := fun w => Idele.localAbs L w (x w) with hf
  have hf_fin : (Function.mulSupport f).Finite := by
    have h := Idele.localAbs_eq_one_eventually (K := L) x
    rw [Filter.eventually_cofinite] at h
    simpa [f, Function.mulSupport] using h
  obtain ⟨S, hSsub⟩ : ∃ S : Finset (Place L), Function.mulSupport f ⊆ (S : Set (Place L)) :=
    ⟨hf_fin.toFinset, fun w hw => by simpa using hw⟩
  have hSout : ∀ w : Place L, w ∉ S → f w = 1 := fun w hw => by
    by_contra h
    exact hw (hSsub (by simpa [Function.mulSupport] using h))
  have hterm : ∀ v : Place K,
      Idele.localAbs K v ((Idele.normIdeleHom K L x) v) =
        ∏ w ∈ S.filter (fun w => globalCFT_placeUnder (K := K) (L := L) w = v), f w := by
    intro v
    rw [Idele.normIdeleHom_apply]
    have hfiber : Idele.localAbs K v (Idele.normIdeleFun K L x v) =
        ∏ w ∈ globalCFT_fiberPlaces (K := K) (L := L) v, f w := by
      cases v with
      | inl v' =>
        rw [Idele.normIdeleFun_ofInfinite, map_prod]
        have hfac : (∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
            (letI : (w'.1 : InfinitePlace L).LiesOver v' := (Place.mem_fiberInfinite).mp w'.2
             (Idele.localAbs K (Place.ofInfinite v'))
               (Place.localNormInfinite w'.1 v' (x (Place.ofInfinite w'.1)))))
            = ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach, f (Place.ofInfinite w'.1) :=
          Finset.prod_congr rfl (fun w' _ => globalCFT_localAbs_localNormInfinite v' w'.1
            ((Place.mem_fiberInfinite).mp w'.2) (x (Place.ofInfinite w'.1)))
        rw [hfac, show (∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
              f (Place.ofInfinite w'.1)) =
            ∏ w' ∈ (Place.fiberInfinite (K := K) (L := L) v').attach,
              (f ∘ Place.ofInfinite) w'.1 from rfl,
          Finset.prod_attach]
        exact (Finset.prod_map _ ⟨Place.ofInfinite, fun _ _ h => Place.ofInfinite_inj.mp h⟩ f).symm
      | inr Q =>
        rw [Idele.normIdeleFun_ofFinite, map_prod]
        have hfac : (∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
            (letI : q'.1.asIdeal.LiesOver Q.asIdeal := (Place.mem_primesOverFinite).mp q'.2
             (Idele.localAbs K (Place.ofFinite Q))
               (Place.localNormFinite q'.1 Q (Place.mem_primesOverFinite.mp q'.2)
                 (x (Place.ofFinite q'.1)))))
            = ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach, f (Place.ofFinite q'.1) :=
          Finset.prod_congr rfl (fun q' _ => globalCFT_localAbs_localNormFinite Q q'.1
            ((Place.mem_primesOverFinite).mp q'.2) (x (Place.ofFinite q'.1)))
        rw [hfac, show (∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
              f (Place.ofFinite q'.1)) =
            ∏ q' ∈ (Place.primesOverFinite (K := K) (L := L) Q).attach,
              (f ∘ Place.ofFinite) q'.1 from rfl,
          Finset.prod_attach]
        exact (Finset.prod_map _ ⟨Place.ofFinite, fun _ _ h => Place.ofFinite_inj.mp h⟩ f).symm
    rw [hfiber]
    exact (Finset.prod_subset
      (fun w hw => (mem_globalCFT_fiberPlaces (K := K) (L := L) (v := v) (w := w)).mpr (by
        have h1 : globalCFT_placeUnder (K := K) (L := L) w = v := (Finset.mem_filter.mp hw).2
        rw [← h1]
        exact liesOver_globalCFT_placeUnder w))
      (fun w hw hw' => by
        by_cases hwS : w ∈ S
        · refine absurd (Finset.mem_filter.mpr ⟨hwS, ?_⟩) hw'
          exact Inclusion.globalCFT_liesOver_unique (liesOver_globalCFT_placeUnder w)
            ((mem_globalCFT_fiberPlaces (K := K) (L := L) (v := v) (w := w)).mp hw)
        · exact hSout w hwS)).symm
  rw [Idele.abs_apply, Idele.abs_apply]
  calc ∏ᶠ v : Place K, Idele.localAbs K v ((Idele.normIdeleHom K L x) v)
      = ∏ᶠ v : Place K,
          ∏ w ∈ S.filter (fun w => globalCFT_placeUnder (K := K) (L := L) w = v), f w :=
        finprod_congr hterm
    _ = ∏ w ∈ S, f w := finprod_prod_filter (globalCFT_placeUnder (K := K) (L := L)) S f
    _ = ∏ᶠ w : Place L, f w := (finprod_eq_prod_of_mulSupport_subset f hSsub).symm
    _ = ∏ᶠ w : Place L, Idele.localAbs L w (x w) := by
        refine finprod_congr (fun w => ?_); rfl

end NK.GlobalCFT.Norm

end
