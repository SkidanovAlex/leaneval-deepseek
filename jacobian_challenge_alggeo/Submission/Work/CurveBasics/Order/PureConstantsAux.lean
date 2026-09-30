import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The "pure constants" step for a smooth curve (auxiliary module)

The lemma `Work.CurveBasics.Order.exists_finite_pure_constants_fixed` proved here is *the*
mathematical content of the requested lemma `Work.CurveBasics.Order.exists_finite_pure_constants`
(see `Submission/Work/CurveBasics/Order/exists_finite_pure_constants.lean`, whose statement is
*not* provable as written: its existential binder `∃ (F : Type*)` introduces a universe level
`u₃` independent of the levels of `k` and `L`, whereas `F` has to be an extension field of `L`).

The only difference is the universe of `F`: here `L : Type u` and `F : Type u`.  Everything else
(including the hypothesis `Transcendental k x`) is verbatim.

## Proof outline

* `K = k(x)` is `IntermediateField.adjoin k {x}`; `L/K` is finite and purely inseparable, so the
  exponent of the extension (`IsPurelyInseparable.HasExponent`) gives a single `Q = ringExpChar K ^ e`
  with `y ^ Q ∈ K` for every `y : L`.
* A finite generating set `T₀` of `L` over `K` (`Module.Finite.fg_top`) is chosen; for `y ∈ T₀`,
  `IntermediateField.mem_adjoin_simple_iff` writes `y ^ Q = r(x)/s(x)` with `r, s : k[X]`.
* `F = AlgebraicClosure L` (same universe as `L`) contains a `Q`-th root `s₀` of `x` and `Q`-th
  roots `rootf a` of all coefficients of all these polynomials; `E` is the subfield of `F`
  generated over `k` by those finitely many roots, hence finite dimensional over `k`.
* `x = s₀ ^ Q` holds by construction, and for `y ∈ T₀` the `Q`-th power of
  `∑ᵢ rootf (r.coeff i) * s₀ ^ i` is `r(s₀ ^ Q) = r(x)` (Frobenius is additive: `Finset.sum_pow_char`
  style lemma `sum_pow_expChar`), which yields `y ∈ E(s₀)`.  Since `k(x) ⊆ E(s₀)` and the
  `T₀` span `L` over `K`, all of `L` lies in `E(s₀)`.
-/

namespace Work.CurveBasics.Order

open Polynomial IntermediateField

section Helpers

/-- In an algebraically closed field, every element has a `Q`-th root for `Q > 0`. -/
lemma exists_pow_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] (a : K) {Q : ℕ}
    (hQ : 0 < Q) : ∃ s : K, s ^ Q = a := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root (X ^ Q - C a) (by
    rw [degree_X_pow_sub_C hQ, Nat.cast_ne_zero]
    exact hQ.ne')
  exact ⟨s, by simpa [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hs⟩

/-- In exponential characteristic `q`, the `q ^ N`-th power map is additive. -/
lemma sub_pow_expChar {R : Type*} [CommRing R] (q N : ℕ) [ExpChar R q] (x y : R) :
    (x - y) ^ (q ^ N) = x ^ (q ^ N) - y ^ (q ^ N) := by
  rw [← iterateFrobenius_def, ← iterateFrobenius_def, ← iterateFrobenius_def, map_sub]

/-- In exponential characteristic `q`, the `q ^ N`-th power map commutes with finite sums. -/
lemma sum_pow_expChar {R : Type*} [CommSemiring R] (q N : ℕ) [ExpChar R q] {ι : Type*}
    (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ (q ^ N) = ∑ i ∈ s, (f i) ^ (q ^ N) := by
  rw [← iterateFrobenius_def, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [iterateFrobenius_def]

/-- In exponential characteristic `q`, the `q ^ N`-th power map is injective on a field. -/
lemma pow_expChar_injective {R : Type*} [Field R] (q N : ℕ) [ExpChar R q] :
    Function.Injective fun x : R => x ^ (q ^ N) := by
  intro x y h
  have h' : x ^ (q ^ N) = y ^ (q ^ N) := h
  have h0 : (x - y) ^ (q ^ N) = 0 := by rw [sub_pow_expChar, h', sub_self]
  have hz : x - y = 0 := by
    by_contra hne
    exact pow_ne_zero (q ^ N) hne h0
  exact sub_eq_zero.mp hz

/-- The key computation: for `rootf a ^ (q ^ N) = a` and `s₀ ^ (q ^ N) = x`, the
`q ^ N`-th power of the "rational function in `s₀`" built from the coefficients of a
polynomial `r` is the evaluation of `r` at `s₀ ^ (q ^ N)`. -/
lemma sum_root_pow {k L F : Type*} [Field k] [Field L] [Field F]
    [Algebra k L] [Algebra L F] [Algebra k F] [IsScalarTower k L F]
    (q N : ℕ) [ExpChar F q] (x : L) (s₀ : F) (rootf : k → F)
    (hrootf : ∀ a : k, rootf a ^ (q ^ N) = algebraMap k F a)
    (hs₀ : s₀ ^ (q ^ N) = algebraMap L F x) (r : k[X]) :
    (∑ i ∈ r.support, rootf (r.coeff i) * s₀ ^ i) ^ (q ^ N)
      = aeval (algebraMap L F x) r := by
  have h1 : (∑ i ∈ r.support, rootf (r.coeff i) * s₀ ^ i) ^ (q ^ N)
      = ∑ i ∈ r.support, algebraMap k F (r.coeff i) * s₀ ^ (q ^ N * i) := by
    rw [sum_pow_expChar]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hrootf, ← pow_mul, mul_comm i (q ^ N)]
  have h2 : aeval (algebraMap L F x) r
      = ∑ i ∈ r.support, algebraMap k F (r.coeff i) * s₀ ^ (q ^ N * i) := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hs₀, ← pow_mul]
  rw [h1, h2]

end Helpers

universe u v

/-- **Corrected version of `exists_finite_pure_constants`.**

The only change with respect to the requested statement is that the existential field `F` is
placed in the universe of `L` (rather than in a fresh, unrelated universe).  This is what the
intended statement is: `F` has to be an extension field of `L`, so it cannot live in a smaller
universe. -/
theorem exists_finite_pure_constants_fixed {k : Type v} [Field k] {L : Type u} [Field L]
    [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    [IsPurelyInseparable (IntermediateField.adjoin k ({x} : Set L)) L] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra k F) (_ : Algebra L F) (_ : IsScalarTower k L F)
      (q : ℕ) (s : F) (E : IntermediateField k F),
      algebraMap L F x = s ^ q ∧
      FiniteDimensional k ↥E ∧
      (∀ y : L, algebraMap L F y ∈ IntermediateField.adjoin ↥E ({s} : Set F)) := by
  classical
  -- `K = k(x)` as a subfield of `L`.
  set K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L) with hK
  -- A uniform exponent for the purely inseparable extension `L / K`.
  obtain ⟨e, he⟩ := (IsPurelyInseparable.hasExponent_iff K L).mp
    (inferInstance : IsPurelyInseparable.HasExponent K L)
  let Q : ℕ := ringExpChar K ^ e
  have hQpos : 0 < Q := expChar_pow_pos K (ringExpChar K) e
  have hQmem : ∀ y : L, y ^ Q ∈ K := by
    intro y
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (he y)
    exact hc.symm ▸ c.2
  -- A finite generating set of `L` over `K`.
  obtain ⟨T₀, hT₀⟩ : ∃ T : Finset L, Submodule.span K (T : Set L) = ⊤ := by
    have hfg : (⊤ : Submodule K L).FG := Module.Finite.fg_top
    rw [Submodule.fg_iff_exists_fin_generating_family] at hfg
    obtain ⟨n, f, hf⟩ := hfg
    exact ⟨Finset.univ.image f, by simpa [Finset.coe_image] using hf⟩
  -- Every `y ∈ T₀` has `y ^ Q` a rational function in `x`.
  have hexpr : ∀ y ∈ T₀, ∃ r sr : k[X], y ^ Q = aeval x r / aeval x sr := by
    intro y hy
    have hyK : y ^ Q ∈ K := hQmem y
    rw [hK] at hyK
    exact (IntermediateField.mem_adjoin_simple_iff k (y ^ Q)).mp hyK
  let rfun : T₀ → k[X] := fun y => Classical.choose (hexpr y y.2)
  let sfun : T₀ → k[X] := fun y => Classical.choose (Classical.choose_spec (hexpr y y.2))
  have hrfun : ∀ y : T₀, (y : L) ^ Q = aeval x (rfun y) / aeval x (sfun y) :=
    fun y => Classical.choose_spec (Classical.choose_spec (hexpr y y.2))
  -- The finite set of coefficients of all these rational functions.
  let T : Finset k := T₀.attach.biUnion fun y =>
    (rfun y).support.image (rfun y).coeff ∪ (sfun y).support.image (sfun y).coeff
  have hcoeffr : ∀ (y : T₀) (i : ℕ), i ∈ (rfun y).support → (rfun y).coeff i ∈ T := by
    intro y i hi
    refine Finset.mem_biUnion.mpr ⟨y, Finset.mem_attach T₀ y, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hcoeffs : ∀ (y : T₀) (i : ℕ), i ∈ (sfun y).support → (sfun y).coeff i ∈ T := by
    intro y i hi
    refine Finset.mem_biUnion.mpr ⟨y, Finset.mem_attach T₀ y, ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  -- A big field containing `L`, a `Q`-th root `s₀` of `x`, and `Q`-th roots of the coefficients.
  let F := AlgebraicClosure L
  let rootf : k → F := fun a =>
    Classical.choose (exists_pow_eq_of_isAlgClosed (algebraMap k F a) hQpos)
  have hrootf : ∀ a : k, rootf a ^ Q = algebraMap k F a := fun a =>
    Classical.choose_spec (exists_pow_eq_of_isAlgClosed (algebraMap k F a) hQpos)
  let E : IntermediateField k F := IntermediateField.adjoin k (rootf '' (T : Set k))
  let s₀ : F := Classical.choose (exists_pow_eq_of_isAlgClosed (algebraMap L F x) hQpos)
  have hs₀ : s₀ ^ Q = algebraMap L F x :=
    Classical.choose_spec (exists_pow_eq_of_isAlgClosed (algebraMap L F x) hQpos)
  haveI hqF : ExpChar F (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K F).injective (ringExpChar K)
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, Q, s₀, E,
    hs₀.symm, ?_, ?_⟩
  · -- `E` is finite dimensional over `k`
    haveI : (rootf '' (T : Set k)).Finite := T.finite_toSet.image rootf
    refine IntermediateField.finiteDimensional_adjoin (S := rootf '' (T : Set k)) fun z hz => ?_
    obtain ⟨a, _ha, rfl⟩ := hz
    exact ⟨X ^ Q - C a, monic_X_pow_sub_C a hQpos.ne',
      by simp [eval₂_sub, eval₂_pow, hrootf a]⟩
  · -- all of `L` lands in the subfield generated by `E` and `s₀`
    intro y
    let B : IntermediateField k F :=
      IntermediateField.restrictScalars k (IntermediateField.adjoin E ({s₀} : Set F))
    let A : IntermediateField k L := B.comap (IsScalarTower.toAlgHom k L F)
    have hmemA : ∀ u : L, u ∈ A ↔
        algebraMap L F u ∈ IntermediateField.adjoin E ({s₀} : Set F) := fun u => Iff.rfl
    -- `x ∈ A`, hence `K ⊆ A`
    have hxA : x ∈ A := by
      change algebraMap L F x ∈ IntermediateField.adjoin E ({s₀} : Set F)
      rw [← hs₀]
      exact Subfield.pow_mem _ (subset_adjoin E _ (Set.mem_singleton s₀)) Q
    have hKA : K ≤ A := by
      rw [hK, IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hxA
    -- `T₀ ⊆ A`
    have hT₀A : (T₀ : Set L) ⊆ (A : Set L) := by
      intro z hz
      have hred : z ^ Q = aeval x (rfun ⟨z, hz⟩) / aeval x (sfun ⟨z, hz⟩) := hrfun ⟨z, hz⟩
      set vr : F := ∑ i ∈ (rfun ⟨z, hz⟩).support, rootf ((rfun ⟨z, hz⟩).coeff i) * s₀ ^ i
        with hvr_def
      set vs : F := ∑ i ∈ (sfun ⟨z, hz⟩).support, rootf ((sfun ⟨z, hz⟩).coeff i) * s₀ ^ i
        with hvs_def
      have hvr : vr ∈ IntermediateField.adjoin E ({s₀} : Set F) := by
        rw [hvr_def]
        apply Subfield.sum_mem (IntermediateField.adjoin E ({s₀} : Set F)).toSubfield
        intro i hi
        apply mul_mem
        · have h1 : rootf ((rfun ⟨z, hz⟩).coeff i) ∈ E :=
            subset_adjoin k _ (Set.mem_image_of_mem rootf (hcoeffr ⟨z, hz⟩ i hi))
          exact set_range_subset
            (S := IntermediateField.adjoin E ({s₀} : Set F)) ⟨⟨_, h1⟩, rfl⟩
        · exact Subfield.pow_mem _ (subset_adjoin E _ (Set.mem_singleton s₀)) i
      have hvs : vs ∈ IntermediateField.adjoin E ({s₀} : Set F) := by
        rw [hvs_def]
        apply Subfield.sum_mem (IntermediateField.adjoin E ({s₀} : Set F)).toSubfield
        intro i hi
        apply mul_mem
        · have h1 : rootf ((sfun ⟨z, hz⟩).coeff i) ∈ E :=
            subset_adjoin k _ (Set.mem_image_of_mem rootf (hcoeffs ⟨z, hz⟩ i hi))
          exact set_range_subset
            (S := IntermediateField.adjoin E ({s₀} : Set F)) ⟨⟨_, h1⟩, rfl⟩
        · exact Subfield.pow_mem _ (subset_adjoin E _ (Set.mem_singleton s₀)) i
      have hpowr : vr ^ Q = aeval (algebraMap L F x) (rfun ⟨z, hz⟩) := by
        rw [hvr_def]
        exact sum_root_pow (ringExpChar K) e x s₀ rootf hrootf hs₀ _
      have hpows : vs ^ Q = aeval (algebraMap L F x) (sfun ⟨z, hz⟩) := by
        rw [hvs_def]
        exact sum_root_pow (ringExpChar K) e x s₀ rootf hrootf hs₀ _
      change algebraMap L F z ∈ IntermediateField.adjoin E ({s₀} : Set F)
      by_cases hden : aeval x (sfun ⟨z, hz⟩) = 0
      · -- the denominator vanishes in `L`, so `z ^ Q = 0`
        have hzQ0 : z ^ Q = 0 := by rw [hred, hden, div_zero]
        have hz0 : z = 0 := (pow_eq_zero_iff hQpos.ne').mp hzQ0
        rw [hz0, map_zero]
        exact zero_mem _
      · -- the denominator is nonzero
        have hzQ : z ^ Q * aeval x (sfun ⟨z, hz⟩) = aeval x (rfun ⟨z, hz⟩) := by
          rw [hred]
          exact div_mul_cancel₀ _ hden
        have hkey : (algebraMap L F z * vs) ^ Q = vr ^ Q := by
          rw [mul_pow, ← map_pow, hpows, aeval_algebraMap_apply, ← map_mul, hzQ,
            ← aeval_algebraMap_apply, ← hpowr]
        have hEq : algebraMap L F z * vs = vr :=
          pow_expChar_injective (ringExpChar K) e hkey
        have hvs0 : vs ≠ 0 := by
          intro hvs0
          have h0 : vs ^ Q = 0 := by rw [hvs0, zero_pow hQpos.ne']
          rw [hpows, aeval_algebraMap_apply] at h0
          exact hden ((map_eq_zero_iff (algebraMap L F) (algebraMap L F).injective).mp h0)
        have hz_eq : algebraMap L F z = vr / vs := (eq_div_iff hvs0).mpr hEq
        rw [hz_eq]
        exact div_mem hvr hvs
    -- conclude that `A = ⊤`
    have htopK : (IntermediateField.adjoin K (T₀ : Set L)) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      have h1 : (⊤ : Submodule K L) ≤
          (IntermediateField.adjoin K (T₀ : Set L)).toSubmodule := by
        rw [← hT₀]
        exact Submodule.span_le.mpr fun v hv => IntermediateField.subset_adjoin K _ hv
      exact h1 trivial
    have htop : (IntermediateField.adjoin k ((K : Set L) ∪ (T₀ : Set L))) = ⊤ := by
      rw [← IntermediateField.adjoin_adjoin_left k (K : Set L) (T₀ : Set L),
        IntermediateField.adjoin_self k K, htopK, IntermediateField.restrictScalars_top]
    have hle : (⊤ : IntermediateField k L) ≤ A := by
      rw [← htop]
      exact IntermediateField.adjoin_le_iff.mpr (Set.union_subset hKA hT₀A)
    have hy : y ∈ A := hle trivial
    change algebraMap L F y ∈ IntermediateField.adjoin E ({s₀} : Set F) at hy
    exact hy

end Work.CurveBasics.Order
