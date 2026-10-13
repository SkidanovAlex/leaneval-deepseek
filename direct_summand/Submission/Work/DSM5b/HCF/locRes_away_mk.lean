import Mathlib
import Submission.Work.DSMap.Mix2

/-!
# `Work.DSM5b.HCF.locRes_away_mk`

Computation of the localisation map `DSMap.Mix2.locRes t h : W_{t_S} →ₐ[W] W_{t_T}` (`S ⊆ T`) on the
"principal fractions" `c / t_S ^k`: in `W_{t_T}` they become `c * t_{T\\S} ^k / t_T ^k`, i.e. the
denominator `t_S ^k` is expanded to the common denominator `t_T ^k = (t_S * t_{T\\S})^k`.

The proof is the standard "unit cancellation" one, run twice:

* `locRes t h` is `W`-linear, so applying it to `IsLocalization.mk'_spec` of
  `mk' c ⟨t_S^k, _⟩ ∈ W_{t_S}` gives
  `locRes t h (mk' …) * algebraMap (t_S^k) = algebraMap c` in `W_{t_T}`;
* `IsLocalization.mk'_spec` for `mk' (c * t_{T\\S}^k) ⟨t_T^k,_⟩ ∈ W_{t_T}` together with
  `t_T^k = t_{T\\S}^k * t_S^k` gives
  `mk' (c * t_{T\\S}^k) ⟨t_T^k,_⟩ * (algebraMap t_S^k) * algebraMap (t_{T\\S}^k)
     = algebraMap c * algebraMap (t_{T\\S}^k)`,
  and `algebraMap (t_{T\\S}^k)` is a unit of `W_{t_T}` because `t_{T\\S} ∣ t_T` and `t_T` is a unit;
* finally `algebraMap (t_S^k)` is a unit (`t_S ∣ t_T`), which gives the desired equality.
-/

namespace Work.DSM5b.HCF

universe u

/-- **Naturality of `IsLocalization.mk'` under a map of `R`-algebras out of a localisation.**

Let `S'` be the localisation of `R` at the submonoid `M` and let `φ : S' →ₐ[R] T'` be an
`R`-algebra map; then `φ` sends `x / y` (`y ∈ M`) to `φ x / φ y` in the weak sense that
`φ (x / y) * φ y = φ x`.  (Only `R`-linearity of `φ` is used, not that `T'` is a localisation.) -/
lemma mk'_algebraMap_eq {R S' T' : Type*} [CommRing R] [CommRing S'] [CommRing T']
    [Algebra R S'] [Algebra R T'] {M : Submonoid R} [IsLocalization M S']
    (φ : S' →ₐ[R] T') (x : R) (y : M) :
    φ (IsLocalization.mk' S' x y) * algebraMap R T' (y : R) = algebraMap R T' x := by
  have h := congrArg φ (IsLocalization.mk'_spec (M := M) S' x y)
  simpa only [map_mul, AlgHom.commutes] using h

theorem locRes_away_mk {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι]
    (t : ι → W) {S T : Finset ι} (h : S ⊆ T) (c : W) (k : ℕ) :
    DSMap.Mix2.locRes t h
        (IsLocalization.mk' (Localization.Away (DSMap.Mix2.tS t S)) c
          ⟨(DSMap.Mix2.tS t S) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩) =
      IsLocalization.mk' (Localization.Away (DSMap.Mix2.tS t T)) (c * (DSMap.Mix2.tS t (T \ S)) ^ k)
        ⟨(DSMap.Mix2.tS t T) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ := by
  set a := DSMap.Mix2.tS t S with ha
  set b := DSMap.Mix2.tS t (T \ S) with hb
  set B := DSMap.Mix2.tS t T with hB
  -- `t_T = t_{T\S} * t_S`
  have hba : b * a = B := by
    rw [ha, hb, hB]
    exact Finset.prod_sdiff h
  have hdvd_a : a ∣ B := by rw [ha, hB]; exact DSMap.Mix2.tS_dvd t h
  have hdvd_b : b ∣ B := by rw [hb, hB]; exact DSMap.Mix2.tS_dvd t (Finset.sdiff_subset)
  -- the relevant images in `W_{t_T}` are units, since `a ∣ B` and `b ∣ B` and `t_T` is a unit
  have hunit_a : IsUnit (algebraMap W (Localization.Away B) a) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap W (Localization.Away B)) hdvd_a)
      (IsLocalization.Away.algebraMap_isUnit B)
  have hunit_b : IsUnit (algebraMap W (Localization.Away B) b) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap W (Localization.Away B)) hdvd_b)
      (IsLocalization.Away.algebraMap_isUnit B)
  have hunitA : IsUnit (algebraMap W (Localization.Away B) (a ^ k)) := by
    rw [map_pow]; exact hunit_a.pow k
  have hunitb : IsUnit (algebraMap W (Localization.Away B) (b ^ k)) := by
    rw [map_pow]; exact hunit_b.pow k
  -- the left hand side, multiplied by `algebraMap (a^k)`, is `algebraMap c`
  have hL : DSMap.Mix2.locRes t h
      (IsLocalization.mk' (Localization.Away a) c ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩)
      * algebraMap W (Localization.Away B) (a ^ k) = algebraMap W (Localization.Away B) c :=
    mk'_algebraMap_eq (DSMap.Mix2.locRes t h) c ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩
  -- the right hand side, multiplied by `algebraMap (a^k)`, is `algebraMap c` as well
  have hBk : B ^ k = b ^ k * a ^ k := by rw [← hba, mul_pow]
  have hspec := IsLocalization.mk'_spec (M := Submonoid.powers B) (Localization.Away B) (c * b ^ k)
    ⟨B ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩
  have h1 : IsLocalization.mk' (Localization.Away B) (c * b ^ k)
        ⟨B ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ *
        (algebraMap W (Localization.Away B) (b ^ k) * algebraMap W (Localization.Away B) (a ^ k))
      = algebraMap W (Localization.Away B) c * algebraMap W (Localization.Away B) (b ^ k) := by
    rw [← map_mul, ← hBk, hspec, map_mul]
  have hY : IsLocalization.mk' (Localization.Away B) (c * b ^ k)
        ⟨B ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ *
        algebraMap W (Localization.Away B) (a ^ k) = algebraMap W (Localization.Away B) c := by
    refine hunitb.mul_right_cancel ?_
    calc (IsLocalization.mk' (Localization.Away B) (c * b ^ k)
            ⟨B ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ *
            algebraMap W (Localization.Away B) (a ^ k)) * algebraMap W (Localization.Away B) (b ^ k)
        = IsLocalization.mk' (Localization.Away B) (c * b ^ k)
            ⟨B ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ *
            (algebraMap W (Localization.Away B) (b ^ k) * algebraMap W (Localization.Away B) (a ^ k)) := by
              ring
      _ = algebraMap W (Localization.Away B) c * algebraMap W (Localization.Away B) (b ^ k) := h1
  exact hunitA.mul_right_cancel (hL.trans hY.symm)

end Work.DSM5b.HCF
