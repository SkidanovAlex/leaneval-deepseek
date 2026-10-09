import Mathlib
import Submission.Work.Kummer.Correspondence
import Submission.Work.Kummer.kummerCharacter_apply_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

open IntermediateField

universe u v

section Helpers

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- Every `n`-th root of unity in `L` is fixed by every `K`-automorphism of `L`: since `ζ ∈ K` is a
primitive `n`-th root of unity, every `n`-th root of unity of `L` comes from `K`. -/
lemma algEquiv_apply_of_mem_rootsOfUnity (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K)) {u : Lˣ}
    (hu : u ∈ rootsOfUnity n L) : (σ : L ≃ₐ[K] L) (u : L) = (u : L) := by
  have h1 : (u : L) ^ n = 1 := (mem_rootsOfUnity' n u).mp hu
  obtain ⟨i, _hi, h⟩ := exists_primRootUnit_pow_eq_of_pow_eq_one hζ h1
  rw [h, Units.coe_map]
  exact AlgEquiv.commutes (σ : L ≃ₐ[K] L) _

/-- The Kummer character of `a` at `σ` is trivial iff `σ` fixes the chosen `n`-th root
`kummerRoot a`. -/
lemma kummerCharacter_eq_one_iff_apply_kummerRoot_eq (hζ : IsPrimitiveRoot ζ n)
    (a : kummerSubgroup n K L) (σ : Gal(L/K)) :
    kummerCharacter hζ a σ = 1 ↔ (σ : L ≃ₐ[K] L) (kummerRoot a : L) = (kummerRoot a : L) := by
  constructor
  · intro h
    have hm := map_kummerCharacter_apply hζ a σ
    rw [h] at hm
    have hratio : kummerRatio σ (kummerRoot a) = 1 := by simpa using hm.symm
    have h2 : algEquivUnitsMap (σ : L ≃ₐ[K] L) (kummerRoot a) = kummerRoot a :=
      div_eq_one.mp hratio
    simpa [algEquivUnitsMap_coe] using congrArg (fun v : Lˣ => (v : L)) h2
  · intro h
    have h2 : algEquivUnitsMap (σ : L ≃ₐ[K] L) (kummerRoot a) = kummerRoot a := by
      apply Units.ext
      simpa [algEquivUnitsMap_coe] using h
    have hratio : kummerRatio σ (kummerRoot a) = 1 := by
      rw [kummerRatio, h2, div_self']
    have hm := map_kummerCharacter_apply hζ a σ
    rw [hratio] at hm
    exact Subtype.ext (Units.map_injective (algebraMap K L).injective (by simpa using hm))

/-- If `x ^ n = y ^ n` and `σ` fixes the nonzero element `y`, then `σ` fixes `x`: the ratio
`x / y` is an `n`-th root of unity in `L`, hence fixed by `σ`. -/
lemma algEquiv_apply_eq_of_pow_eq_of_apply_eq (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K))
    {x y : L} (hy : y ≠ 0) (hxy : x ^ n = y ^ n) (hσy : (σ : L ≃ₐ[K] L) y = y) :
    (σ : L ≃ₐ[K] L) x = x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (NeZero.ne n)] at hxy
    exact hy ((pow_eq_zero_iff (NeZero.ne n)).mp hxy.symm)
  set u : Lˣ := Units.mk0 (x / y) (div_ne_zero hx0 hy) with hu
  have huval : (u : L) = x / y := Units.val_mk0 _
  have humem : u ∈ rootsOfUnity n L := by
    rw [mem_rootsOfUnity' n u, huval, div_pow, hxy, div_self (pow_ne_zero n hy)]
  have hufix : (σ : L ≃ₐ[K] L) (u : L) = (u : L) :=
    algEquiv_apply_of_mem_rootsOfUnity hζ σ humem
  have hxuy : y * (u : L) = x := by rw [huval, mul_div_cancel₀ x hy]
  calc (σ : L ≃ₐ[K] L) x
      = (σ : L ≃ₐ[K] L) (y * (u : L)) := by rw [hxuy]
    _ = (σ : L ≃ₐ[K] L) y * (σ : L ≃ₐ[K] L) (u : L) := by rw [map_mul]
    _ = y * (x / y) := by rw [hσy, hufix, huval]
    _ = x := mul_div_cancel₀ x hy

end Helpers

/-- **Kummer correspondence, orthogonality form.** Let `L/K` be a finite Galois extension, `K`
containing a primitive `n`-th root of unity `ζ`, and let `Δ ≤ (Kˣ ∩ (Lˣ)^n)/(Kˣ)^n`. Then the
subgroup of `Gal(L/K)` fixing the Kummer subextension `kummerAdjoin n K L Δ` is exactly the
annihilator of `Δ` under the Kummer pairing: a `K`-automorphism fixes `kummerAdjoin n K L Δ` iff it
acts trivially in the pairing on every element of `Δ`. -/
theorem fixingSubgroup_kummerAdjoin {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (Δ : Subgroup (kummerQuotient n K L)) :
    (kummerAdjoin n K L Δ).fixingSubgroup =
      {σ : Gal(L/K) | ∀ a : kummerQuotient n K L, a ∈ Δ → kummerPairing hζ a σ = 1} := by
  have _hexp : Monoid.exponent Gal(L/K) ∣ n := hexp
  have key : ∀ σ : Gal(L/K), σ ∈ (kummerAdjoin n K L Δ).fixingSubgroup ↔
      (∀ a : kummerQuotient n K L, a ∈ Δ → kummerPairing hζ a σ = 1) := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · -- A `K`-automorphism fixing the Kummer subextension acts trivially on `Δ`.
      intro hfix a ha
      obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective
        ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a
      rw [kummerPairing_mk, kummerCharacter_eq_one_iff_apply_kummerRoot_eq]
      exact hfix _ (kummerQuotient_mk_mem_kummerAdjoin Δ a' ha (kummerRoot_pow_val a'))
    · -- A `K`-automorphism acting trivially on `Δ` fixes the generators of `kummerAdjoin`.
      intro hpair x hx
      have hx' : x ∈ IntermediateField.adjoin K
          {y : L | ∃ a : kummerSubgroup n K L,
            QuotientGroup.mk' _ a ∈ Δ ∧ y ^ n = algebraMap K L (((a : Kˣ) : K))} := hx
      refine IntermediateField.adjoin_induction K
        (s := {y : L | ∃ a : kummerSubgroup n K L,
            QuotientGroup.mk' _ a ∈ Δ ∧ y ^ n = algebraMap K L (((a : Kˣ) : K))})
        (p := fun y _ => (σ : L ≃ₐ[K] L) y = y) ?_ ?_ ?_ ?_ ?_ hx'
      · intro y hy
        obtain ⟨a, ha, hya⟩ := hy
        have hchar : kummerCharacter hζ a σ = 1 := by
          have h := hpair (QuotientGroup.mk' _ a) ha
          rwa [kummerPairing_mk] at h
        have hroot : (σ : L ≃ₐ[K] L) (kummerRoot a : L) = (kummerRoot a : L) :=
          (kummerCharacter_eq_one_iff_apply_kummerRoot_eq hζ a σ).mp hchar
        have hy2 : y ^ n = ((kummerRoot a : Lˣ) : L) ^ n := by
          rw [hya, kummerRoot_pow_val a]
        exact algEquiv_apply_eq_of_pow_eq_of_apply_eq hζ σ (Units.ne_zero (kummerRoot a)) hy2 hroot
      · intro c
        exact (σ : L ≃ₐ[K] L).commutes c
      · intro y z _ _ ihy ihz
        rw [map_add, ihy, ihz]
      · intro y _ ihy
        rw [map_inv₀, ihy]
      · intro y z _ _ ihy ihz
        rw [map_mul, ihy, ihz]
  ext σ
  rw [Set.mem_ofPred_eq]
  exact key σ

end Work.Kummer
