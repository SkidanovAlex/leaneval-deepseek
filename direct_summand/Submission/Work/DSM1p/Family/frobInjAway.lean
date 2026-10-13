import Mathlib
import Submission.Work.DSM1p.Family

namespace Work.DSM1p.Family

universe u

/-! ## The abstract core of `frobInjAway`

The Frobenius-injectivity statement of `frobInj` (`Submission/Work/DSM1p/Family/frobInj.lean`)
is proved from the abstract pattern

> `S` a commutative ring, `ϖ₀ : S` with `ϖ₀ ^ p = p · v` for a unit `v`, `p` a non-zero-divisor
> of `S`, and `S` `p`-root-closed in the localisation `S[1/p]` (every `z : S[1/p]` with
> `z ^ p` in the image of `S` already lies in the image of `S`); then `y ^ p ∈ (p)` implies
> `y ∈ (ϖ₀)`.

Everything used by that argument lives in the localisation `S[1/p]` — indeed the proof of the
finite computation `frobInj_core_pow` never uses that the target ring is a *fraction* ring;
it only uses that it is an `S`-algebra and that `ϖ₀` becomes a unit.  The present file makes
that explicit: the same argument, with `FractionRing S` replaced by `Localization.Away p`.

The proof: write `y ^ p = p · t`.  Since `φ ϖ₀ ^ p = φ p · φ v` is a product of units
(`φ p` is a unit in `S[1/p]` and `φ v` is a unit because `v` is), `φ ϖ₀` is a unit, so
`z := (φ ϖ₀)⁻¹ · φ y` makes sense.  Then `z ^ p = φ (v⁻¹ · t)` lies in the image of `S`, hence
`z = φ w` by `p`-root-closedness; applying the injective map `φ` (injective because `p` is a
non-zero-divisor) to `φ y = φ ϖ₀ · z = φ (ϖ₀ · w)` yields `y = ϖ₀ · w`. -/

/-- The finite computation behind `frobInjAway_core`: with `u` the unit `φ ϖ₀` and
`z := u⁻¹ · φ y`, one has `z ^ p = φ (v⁻¹ · t)` whenever `φ ϖ₀ ^ p = φ p · φ v` and
`φ (y ^ p) = φ p · φ t`.  (This is the localisation-agnostic part of the argument; the only
hypothesis on the target ring is that it is a commutative `S`-algebra.) -/
private lemma frobInjAway_core_pow {S K : Type*} [CommRing S] [CommRing K] [Algebra S K]
    (p : ℕ) (y ϖ0 : S) (v : Sˣ) (hv : ϖ0 ^ p = (p : S) * (v : S))
    (t : S) (ht : y ^ p = (p : S) * t)
    (hu : IsUnit (algebraMap S K ϖ0)) :
    ((↑(hu.unit⁻¹) : K) * algebraMap S K y) ^ p
      = algebraMap S K (((v⁻¹ : Sˣ) : S) * t) := by
  set f : S →* K := (algebraMap S K).toMonoidHom with hf
  set V : Kˣ := Units.map f v with hV
  have hVc : (↑V : K) = algebraMap S K (↑v) := by rw [hV, Units.coe_map]; rfl
  have h1 : (↑(hu.unit ^ p) : K) = algebraMap S K (p : S) * ↑V := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hv, map_mul, hVc]
  have hP : algebraMap S K (p : S) = (↑(hu.unit ^ p) : K) * ↑(V⁻¹) := by
    rw [h1, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hVm : V⁻¹ = Units.map f (v⁻¹) := by rw [hV, ← map_inv]
  have hVi : (↑(V⁻¹) : K) = algebraMap S K (((v⁻¹ : Sˣ) : S)) := by
    rw [hVm, Units.coe_map]; rfl
  rw [show ((↑(hu.unit⁻¹) : K) * algebraMap S K y) ^ p
      = ↑((hu.unit ^ p)⁻¹) * (algebraMap S K (p : S) * algebraMap S K t) by
    rw [mul_pow, ← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, ht, map_mul]]
  rw [hP, hVi, mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
    ← map_mul]

/-- **The abstract Frobenius-injectivity statement, localised at `p`.**  Let `S` be a
commutative ring, `p` a non-zero-divisor of `S`, `ϖ₀ : S` with `ϖ₀ ^ p = p · v` for a unit `v`,
and suppose that `S` is `p`-root-closed in `S[1/p]`: every `z : Localization.Away p` with
`z ^ p` in the image of `S` already lies in the image of `S`.  Then `y ^ p ∈ (p)` implies
`y ∈ (ϖ₀)`. -/
private lemma frobInjAway_core {S : Type u} [CommRing S] (p : ℕ) (hpne : p ≠ 0) (ϖ0 : S)
    (v : Sˣ) (hv : ϖ0 ^ p = (p : S) * (v : S))
    (hreg : IsSMulRegular S (p : S))
    (hclosed : ∀ z : Localization.Away (p : S),
      z ^ p ∈ (algebraMap S (Localization.Away (p : S))).range →
      z ∈ (algebraMap S (Localization.Away (p : S))).range)
    (y : S) (hy : y ^ p ∈ Ideal.span {(p : S)}) : y ∈ Ideal.span {ϖ0} := by
  -- `p` is a non-zero-divisor, i.e. a regular element
  have hpmem : (p : S) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact hreg (show (p : S) • a = (p : S) • (0 : S) by
      rw [smul_eq_mul, smul_eq_mul, ha, mul_zero])
  -- the localisation `S → S[1/p]` is injective precisely because `p` is regular
  have hφinj : Function.Injective (algebraMap S (Localization.Away (p : S))) :=
    IsLocalization.injective (Localization.Away (p : S))
      (by rw [Submonoid.powers_le]; exact hpmem)
  -- `φ p` and `φ v` are units in `S[1/p]`, so `φ ϖ₀` is a unit
  have hφp_unit : IsUnit (algebraMap S (Localization.Away (p : S)) (p : S)) :=
    IsLocalization.Away.algebraMap_isUnit (p : S)
  have hφv_unit : IsUnit (algebraMap S (Localization.Away (p : S)) (v : S)) :=
    (Units.isUnit v).map (algebraMap S (Localization.Away (p : S)))
  have hφϖpow : (algebraMap S (Localization.Away (p : S)) ϖ0) ^ p =
      algebraMap S (Localization.Away (p : S)) (p : S) *
        algebraMap S (Localization.Away (p : S)) (v : S) := by
    rw [← map_pow, hv, map_mul]
  have hu : IsUnit (algebraMap S (Localization.Away (p : S)) ϖ0) := by
    have h2 : IsUnit ((algebraMap S (Localization.Away (p : S)) ϖ0) ^ p) := by
      rw [hφϖpow]
      exact hφp_unit.mul hφv_unit
    exact (isUnit_pow_iff hpne).mp h2
  -- `y ^ p = p · t`
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hy
  -- `z := (φ ϖ₀)⁻¹ · φ y` has `p`-th power in the image of `S`
  have hzpow : ((↑(hu.unit⁻¹) : Localization.Away (p : S)) *
      algebraMap S (Localization.Away (p : S)) y) ^ p
      = algebraMap S (Localization.Away (p : S)) (((v⁻¹ : Sˣ) : S) * w) :=
    frobInjAway_core_pow p y ϖ0 v hv w hw hu
  have hzcl : ((↑(hu.unit⁻¹) : Localization.Away (p : S)) *
      algebraMap S (Localization.Away (p : S)) y) ∈
      (algebraMap S (Localization.Away (p : S))).range := by
    apply hclosed
    rw [hzpow]
    exact Set.mem_range_self _
  obtain ⟨w', hw'⟩ := hzcl
  -- hence `y = ϖ₀ · w'`
  refine Ideal.mem_span_singleton.mpr ⟨w', ?_⟩
  apply hφinj
  calc algebraMap S (Localization.Away (p : S)) y
      = (↑hu.unit * ↑(hu.unit⁻¹)) * algebraMap S (Localization.Away (p : S)) y := by
        rw [Units.mul_inv, one_mul]
    _ = ↑hu.unit * (↑(hu.unit⁻¹) * algebraMap S (Localization.Away (p : S)) y) := by
        rw [mul_assoc]
    _ = algebraMap S (Localization.Away (p : S)) ϖ0 *
          algebraMap S (Localization.Away (p : S)) w' := by rw [hu.unit_spec, ← hw']
    _ = algebraMap S (Localization.Away (p : S)) (ϖ0 * w') := (map_mul _ _ _).symm

theorem frobInjAway (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (p : ℕ) [Fact p.Prime]
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (htf : IsSMulRegular (Work.DSM1p.FamCompletion R p x)
      (p : Work.DSM1p.FamCompletion R p x))
    (ϖ : ℕ → Work.DSM1p.FamCompletion R p x) (hϖ : ∀ k, ϖ (k + 1) ^ p = ϖ k)
    (hunit : ∃ v : (Work.DSM1p.FamCompletion R p x)ˣ,
      ϖ 0 ^ p = (p : Work.DSM1p.FamCompletion R p x) * v)
    (hclosed : ∀ z : Localization.Away (p : Work.DSM1p.FamCompletion R p x),
      z ^ p ∈ (algebraMap (Work.DSM1p.FamCompletion R p x)
        (Localization.Away (p : Work.DSM1p.FamCompletion R p x))).range →
      z ∈ (algebraMap (Work.DSM1p.FamCompletion R p x)
        (Localization.Away (p : Work.DSM1p.FamCompletion R p x))).range)
    (y : Work.DSM1p.FamCompletion R p x)
    (hy : y ^ p ∈ Ideal.span {(p : Work.DSM1p.FamCompletion R p x)}) :
    y ∈ Ideal.span {ϖ 0} := by
  obtain ⟨v, hv⟩ := hunit
  exact frobInjAway_core p (Fact.out : p.Prime).ne_zero (ϖ 0) v hv htf hclosed y hy

end Work.DSM1p.Family
