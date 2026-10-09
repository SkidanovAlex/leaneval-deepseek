/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The completion at a prime above `v` is an algebra over the completion at `v`

For number fields `K ⊆ L`, a finite prime `v` of `K` and a finite prime `w` of `L` lying over `v`,
the inclusion `K → L` extends continuously to the completions, giving an algebra structure
`Algebra K_v L_w`.  This is the basic local input used to speak about the local Galois group at
`w` as the decomposition group `D_w`.

We prove the two ingredients:

* `valuation_isEquiv_of_liesOver`: if `w` lies over `v`, then the `w`-adic valuation of `L`,
  restricted to `K`, is equivalent to the `v`-adic valuation of `K`.
* `completionMap_nonempty`: from an equivalence of valuations one produces a ring homomorphism
  between the completions (via the universal property of the uniform space completion).

## Main results

* `Work.LocalFields.valuation_isEquiv_of_liesOver`
* `Work.LocalFields.completionMap_nonempty`
* `Work.LocalFields.exists_algebra_completion`
-/
import Mathlib
import Submission.Work.LocalFields.Basic

namespace Work.LocalFields

open MonoidWithZeroHom
open IsDedekindDomain HeightOneSpectrum
open scoped NumberField WithZero Valued

/-- If `v : Valuation K Γ₀` is nontrivial and `v.IsEquiv v'`, then the value group of `v'` is
unbounded below: for every `g ≠ 0` there is `y` with `0 < v' y < g`. -/
theorem exists_val_lt_of_isEquiv {K : Type*} [Field K]
    {v v' : Valuation K (WithZero (Multiplicative ℤ))}
    (h : v.IsEquiv v') (hv : v.IsNontrivial) {g : WithZero (Multiplicative ℤ)} (hg : g ≠ 0) :
    ∃ y : K, v' y ≠ 0 ∧ v' y < g := by
  -- Powers of a value `< 1` become arbitrarily small.
  have pow_lt : ∀ {u : WithZero (Multiplicative ℤ)}, u ≠ 0 → u < 1 →
      ∃ n : ℕ, u ^ n < g := by
    intro u hu hu1
    have hu' : WithZero.unzero hu < 1 :=
      (WithZero.coe_lt_coe).mp (by rw [WithZero.coe_unzero]; exact hu1)
    obtain ⟨n, hn⟩ := exists_pow_lt hu' (WithZero.unzero hg)
    refine ⟨n, ?_⟩
    have h1 : (↑(WithZero.unzero hu ^ n) : WithZero (Multiplicative ℤ)) = u ^ n := by
      rw [WithZero.coe_pow, WithZero.coe_unzero]
    rw [← h1, ← WithZero.coe_unzero hg]
    exact (WithZero.coe_lt_coe).mpr hn
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  have hx0' : v' x ≠ 0 := fun h0 => hx0 (h.eq_zero.mpr h0)
  have hx1' : v' x ≠ 1 := fun h1 => hx1 (h.eq_one_iff_eq_one.mpr h1)
  rcases lt_trichotomy (v' x) 1 with hlt | heq' | hgt
  · obtain ⟨n, hn⟩ := pow_lt hx0' hlt
    exact ⟨x ^ n, by rw [map_pow]; exact pow_ne_zero n hx0', by rw [map_pow]; exact hn⟩
  · exact absurd heq' hx1'
  · have hinv0 : v' x⁻¹ ≠ 0 := by rw [map_inv₀]; exact inv_ne_zero hx0'
    have hinv1 : v' x⁻¹ < 1 := by
      have h1 : 1 < v' x := hgt
      have hunzero : (1 : Multiplicative ℤ) < WithZero.unzero hx0' :=
        (WithZero.coe_lt_coe).mp (by rw [WithZero.coe_unzero, WithZero.coe_one]; exact h1)
      have hinv : (v' x)⁻¹ = ↑((WithZero.unzero hx0')⁻¹) := by
        rw [WithZero.coe_inv, WithZero.coe_unzero hx0']
      rw [map_inv₀, hinv, ← WithZero.coe_one, WithZero.coe_lt_coe]
      exact (inv_lt_one_iff_one_lt).mpr hunzero
    obtain ⟨n, hn⟩ := pow_lt hinv0 hinv1
    exact ⟨(x⁻¹) ^ n, by rw [map_pow]; exact pow_ne_zero n hinv0, by rw [map_pow]; exact hn⟩

/-- **The `w`-adic valuation restricted to `K` is equivalent to the `v`-adic valuation** when `w`
lies over `v`. -/
theorem valuation_isEquiv_of_liesOver {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] :
    (v.valuation K).IsEquiv ((w.valuation L).comap (algebraMap K L)) := by
  have : Ring.KrullDimLE 1 ↥((v.valuation K).valuationSubring) :=
    (HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := K) v) ▸ inferInstance
  rw [Valuation.isEquiv_iff_valuationSubring]
  -- `V ≤ V'`, and `V' ≠ ⊤`; both are valuation subrings of `K`, whence `V = V'` for a
  -- Krull-dimension-one `V`.
  refine ValuationSubring.eq_of_le_of_ne_top ((v.valuation K).valuationSubring) ?_ ?_
  · -- easy direction: `(𝓞 K)_v ⊆ (𝓞 L)_w ∩ K`
    intro x hx
    rw [Valuation.mem_valuationSubring_iff] at hx ⊢
    rw [Valuation.comap_apply]
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := K) v x hx
    have h2 := congrArg (algebraMap K L) hnd
    simp only [map_mul] at h2
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L] at h2
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L] at h2
    have key : (w.valuation L) (algebraMap K L x) *
        (w.valuation L) ((algebraMap (𝓞 L) L) ((algebraMap (𝓞 K) (𝓞 L)) ↑d))
        = (w.valuation L) ((algebraMap (𝓞 L) L) ((algebraMap (𝓞 K) (𝓞 L)) n)) := by
      rw [← map_mul, h2]
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap] at key
    have hopen : v.asIdeal = w.asIdeal.under (𝓞 K) := Ideal.LiesOver.over
    have hd : ((algebraMap (𝓞 K) (𝓞 L)) ↑d) ∉ w.asIdeal := by
      intro hmem
      have h1 : (d : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) :=
        (Ideal.mem_under (𝓞 K) w.asIdeal).mpr hmem
      exact d.2 (le_of_eq hopen.symm h1)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.mpr hd, mul_one] at key
    rw [key]
    exact HeightOneSpectrum.intValuation_le_one w _
  · -- `V' ≠ ⊤`, using that a uniformizer of `v` has positive `w`-adic valuation
    intro htop
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer' K v
    have hopen : v.asIdeal = w.asIdeal.under (𝓞 K) := Ideal.LiesOver.over
    have hπmem : (algebraMap (𝓞 K) (𝓞 L)) π ∈ w.asIdeal := by
      refine (Ideal.mem_under (𝓞 K) w.asIdeal).mp ?_
      rw [← hopen]
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem,
        ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      rw [hπ]
      exact (WithZero.coe_lt_coe).mpr (by norm_num : (-1 : ℤ) < 0)
    have hlt : ((w.valuation L).comap (algebraMap K L)) (algebraMap (𝓞 K) K π) < 1 := by
      rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply (𝓞 K) K L,
          IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
          HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hπmem
    have hπ0 : π ≠ 0 := by
      have h1 : (v.valuation K) (π : K) ≠ 0 := by rw [hπ]; exact WithZero.coe_ne_zero
      have h2 : (π : K) ≠ 0 := (Valuation.ne_zero_iff _).mp h1
      exact fun h => h2 (by rw [h]; exact map_zero _)
    have hu0 : algebraMap (𝓞 K) K π ≠ 0 := fun h =>
      hπ0 ((IsFractionRing.injective (𝓞 K) K) h)
    have h2 : 1 ≤ ((w.valuation L).comap (algebraMap K L)) (algebraMap (𝓞 K) K π) := by
      have : (algebraMap (𝓞 K) K π)⁻¹ ∈
          (((w.valuation L).comap (algebraMap K L)).valuationSubring) := by
        rw [htop]; exact Subring.mem_top _
      rw [Valuation.mem_valuationSubring_iff] at this
      have h3 := (Valuation.val_le_one_iff _ (inv_ne_zero hu0)).mp this
      simpa using h3
    exact absurd h2 (not_le.mpr hlt)

/-- **The completion map.**  If the `w`-adic valuation of `L` restricts to a valuation on `K`
equivalent to the `v`-adic valuation, then there is a ring homomorphism `K_v →+* L_w` between the
completions, obtained from the universal property of the uniform space completion. -/
theorem completionMap_nonempty {K L : Type*} [Field K] [Field L] [Algebra K L]
    {vK : Valuation K (WithZero (Multiplicative ℤ))}
    {wL : Valuation L (WithZero (Multiplicative ℤ))}
    (h : vK.IsEquiv (wL.comap (algebraMap K L))) (hv : vK.IsNontrivial) :
    Nonempty (vK.Completion →+* wL.Completion) := by
  -- the canonical map `L → L_w`
  let emb : L →+* wL.Completion :=
    (UniformSpace.Completion.coeRingHom).comp ((WithVal.equiv wL).symm.toRingHom)
  have hval : ∀ y : L, Valued.v (R := wL.Completion) (emb y) = wL y := by
    intro y
    have h1 : emb y = (↑((WithVal.equiv wL).symm y) : wL.Completion) := rfl
    rw [h1, Valued.valuedCompletion_apply, WithVal.equiv_symm_apply, WithVal.valued_toVal]
  let g : K →+* wL.Completion := emb.comp (algebraMap K L)
  have gval : ∀ x : K, Valued.v (R := wL.Completion) (g x) = wL (algebraMap K L x) := fun x =>
    hval (algebraMap K L x)
  let g' : WithVal vK →+* wL.Completion := g.comp (WithVal.equiv vK).toRingHom
  have g'val : ∀ x : WithVal vK,
      Valued.v (R := wL.Completion) (g' x) = wL (algebraMap K L x.ofVal) := fun x =>
    gval x.ofVal
  have hcont : Continuous g' := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Filter.tendsto_def]
    intro s hs
    rw [Valued.mem_nhds] at hs ⊢
    obtain ⟨γ, hγ⟩ := hs
    set g₀ : WithZero (Multiplicative ℤ) :=
      ValueGroup₀.embedding (f := ((Valued.v (R := wL.Completion) : Valuation wL.Completion (WithZero (Multiplicative ℤ))) : wL.Completion →*₀ WithZero (Multiplicative ℤ)))
        (γ : (((Valued.v (R := wL.Completion) : Valuation wL.Completion (WithZero (Multiplicative ℤ))) : wL.Completion →*₀ WithZero (Multiplicative ℤ))).ValueGroup₀) with hg₀
    have hg₀ne : g₀ ≠ 0 := by
      rw [hg₀]
      exact fun h0 => Units.ne_zero γ (ValueGroup₀.embedding_injective (by rw [h0, map_zero]))
    obtain ⟨y, hy0, hylt⟩ := exists_val_lt_of_isEquiv h hv hg₀ne
    refine ⟨Units.mk0 ((Valued.v (R := WithVal vK)).restrict (WithVal.toVal vK y)) ?_, ?_⟩
    · have hz0 : Valued.v (R := WithVal vK) (WithVal.toVal vK y) ≠ 0 := by
        rw [WithVal.valued_toVal]
        intro h0
        exact hy0 ((h.eq_zero).mp h0)
      intro h0
      exact hz0 ((Valuation.restrict_eq_zero_iff (Valued.v (R := WithVal vK))).mp h0)
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      rw [Units.val_mk0] at hz
      rw [Valuation.restrict_lt_iff] at hz
      simp only [WithVal.valued_toVal] at hz
      have h1 : (wL.comap (algebraMap K L)) (z.ofVal - x.ofVal)
          < (wL.comap (algebraMap K L)) y := (h.lt_iff_lt).mp hz
      have h2 : (Valued.v (R := wL.Completion)) (g' (z - x)) < g₀ := by
        rw [show g' (z - x) = g (z.ofVal - x.ofVal) from by
              simp [g', WithVal.ofVal_sub, WithVal.equiv_apply]]
        rw [gval]
        exact lt_trans h1 hylt
      exact hγ (by
        simp only [Set.mem_ofPred_eq]
        rw [← map_sub, Valuation.restrict_lt_iff_lt_embedding, ← hg₀]
        exact h2)
  exact ⟨UniformSpace.Completion.extensionHom g' hcont⟩

theorem exists_algebra_completion {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nonempty (Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)) := by
  have h := valuation_isEquiv_of_liesOver v w
  obtain ⟨F⟩ := completionMap_nonempty h (inferInstance : (v.valuation K).IsNontrivial)
  exact ⟨RingHom.toAlgebra (((adicCompletion.equiv L w).symm.toRingHom).comp
    (F.comp (adicCompletion.equiv K v).toRingHom))⟩

end Work.LocalFields
