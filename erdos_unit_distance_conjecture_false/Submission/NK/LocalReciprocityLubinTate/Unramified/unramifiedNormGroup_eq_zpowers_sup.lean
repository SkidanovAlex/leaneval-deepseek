import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools

/-!
# The norm group of the unramified level is `⟨π^m⟩ · U⁰`

This file proves

`NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m = ⟨π^m⟩ · U⁰`

for an arbitrary uniformiser `π` of the completion `F = Q.adicCompletion K` of a number field at a
finite place: the group `⟨π^m⟩ · U⁰` does not depend on the chosen uniformiser, and it agrees with
the definition `unramifiedNormGroup K Q m = ⟨π_Q^m⟩ · U⁰` built from the canonical (Henselian)
uniformiser `π_Q = uniformizerUnit K Q`.

The definitional form `unramifiedNormGroup K Q m = Subgroup.zpowers (uniformizerUnit K Q ^ m) ⊔
adicUnits K Q` uses `adicUnits`, the group of units of the ring of integers
`Q.adicCompletionIntegers K` described by the `Valued.v`-valuation, whereas `higherUnits F 0` is
formulated with the `ValuativeRel` structure of `F` (`𝒪[F] = (ValuativeRel.valuation F).integer`).
The two valuations are *equivalent* (they induce the same topology of `F`), so the corresponding
groups of units of the two rings of integers coincide; establishing this is the formal content of
`valued_v_le_one_iff` below, proved through the characterisation of `{x | v x < 1}` as the set of
topologically nilpotent elements for both valuations.

## Main results

* `valued_v_le_one_iff`, `valued_v_eq_one_iff`, `isEquiv_valued_valuation` — the two valuations on
  the completion are equivalent;
* `adicUnits_eq_higherUnits_zero_aux` — `U⁰` is the same subgroup in both descriptions;
* `valuation_uniformizerUnit_eq` — every uniformiser has the valuation of the canonical one;
* `unramifiedNormGroup_eq_zpowers_sup` — the norm group of the unramified level of degree `m`.
-/



open scoped ValuativeRel Topology
open IsDedekindDomain.HeightOneSpectrum
open Filter

namespace NK.LocalReciprocityLubinTate.Unramified
open NK.LocalReciprocityLubinTate

universe u
noncomputable section

private lemma exists_lt_one_of_nontrivial {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [Nontrivial G] : ∃ g : G, g < 1 := by
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial G).exists_pair_ne
  have hne : a * b⁻¹ ≠ (1 : G) := by
    intro h
    refine hab ?_
    have h2 : (a * b⁻¹) * b = 1 * b := by rw [h]
    simpa using h2
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := ⟨a * b⁻¹, hne⟩
  rcases lt_or_gt_of_ne hg with h | h
  · exact ⟨g, h⟩
  · exact ⟨g⁻¹, by rw [Left.inv_lt_one_iff]; exact h⟩

private lemma exists_pow_lt_of_lt_one {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [IsCyclic G] [Nontrivial G] {a b : G} (ha : a < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a ^ n < b := by
  obtain ⟨g, hgzp⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot] at hgzp
    exact absurd hgzp.symm
      ((Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup G)).mp inferInstance)
  rcases lt_or_gt_of_ne hg1 with hglt | hggt
  · have hg := hglt; have hzg := hgzp
    obtain ⟨k, hk⟩ : ∃ k : ℤ, g ^ k = a :=
      Subgroup.mem_zpowers_iff.mp (hzg ▸ Subgroup.mem_top a)
    have hkpos : 0 < k := by
      by_contra hk0
      push Not at hk0
      have hle : g ^ (0 : ℤ) ≤ g ^ k := (zpow_right_strictAnti hg).antitone hk0
      rw [zpow_zero] at hle
      exact absurd (hk ▸ hle) (not_le.mpr ha)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, g ^ m = b :=
      Subgroup.mem_zpowers_iff.mp (hzg ▸ Subgroup.mem_top b)
    have hk1 : 1 ≤ k := hkpos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m < k * (n : ℤ) := by
      refine ⟨(m.toNat : ℕ) + 1, fun n hn => ?_⟩
      have hn' : (m.toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
      have hmle : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
      have hkn : (n : ℤ) ≤ k * (n : ℤ) := by nlinarith [Int.natCast_nonneg n]
      omega
    refine ⟨N, fun n hn => ?_⟩
    have hmn : m < k * (n : ℤ) := hN n hn
    rw [← hk, ← hm, ← zpow_natCast, ← zpow_mul]
    exact (zpow_right_strictAnti hg) hmn
  · set g' : G := g⁻¹ with hg'def
    have hg' : g' < 1 := by rw [hg'def, Left.inv_lt_one_iff]; exact hggt
    have hzg' : Subgroup.zpowers g' = ⊤ := by rw [hg'def, Subgroup.zpowers_inv, hgzp]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, g' ^ k = a :=
      Subgroup.mem_zpowers_iff.mp (hzg' ▸ Subgroup.mem_top a)
    have hkpos : 0 < k := by
      by_contra hk0
      push Not at hk0
      have hle : g' ^ (0 : ℤ) ≤ g' ^ k := (zpow_right_strictAnti hg').antitone hk0
      rw [zpow_zero] at hle
      exact absurd (hk ▸ hle) (not_le.mpr ha)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, g' ^ m = b :=
      Subgroup.mem_zpowers_iff.mp (hzg' ▸ Subgroup.mem_top b)
    have hk1 : 1 ≤ k := hkpos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m < k * (n : ℤ) := by
      refine ⟨(m.toNat : ℕ) + 1, fun n hn => ?_⟩
      have hn' : (m.toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
      have hmle : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
      have hkn : (n : ℤ) ≤ k * (n : ℤ) := by nlinarith [Int.natCast_nonneg n]
      omega
    refine ⟨N, fun n hn => ?_⟩
    have hmn : m < k * (n : ℤ) := hN n hn
    rw [← hk, ← hm, ← zpow_natCast, ← zpow_mul]
    exact (zpow_right_strictAnti hg') hmn

/-! ### 2. Nilpotence in the valuative topology -/

private lemma tendsto_pow_nhds_zero_iff_vlt_one {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsValuativeTopology F]
    [IsCyclic (ValuativeRel.ValueGroupWithZero F)ˣ]
    [Nontrivial (ValuativeRel.ValueGroupWithZero F)ˣ] (y : F) :
    Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔ (ValuativeRel.valuation F) y < 1 := by
  set v := ValuativeRel.valuation F with hv
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hvy : v y ≠ 0 := fun h0 => absurd (h0 ▸ hcon) (by norm_num)
    obtain ⟨γ, hγ⟩ := exists_lt_one_of_nontrivial
      (G := (ValuativeRel.ValueGroupWithZero F)ˣ)
    have hball : ({z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)}) ∈ 𝓝 (0 : F) :=
      (IsValuativeTopology.mem_nhds_iff (x := (0 : F))).mpr
        ⟨γ, fun z hz => by
          rcases hz with ⟨w, hw, hzw⟩
          rw [← hzw]
          simpa using hw⟩
    have hpow : ∀ n : ℕ, 1 ≤ n → (1 : ValuativeRel.ValueGroupWithZero F) ≤ (v y) ^ n := by
      intro n _
      have h1 : (1 : (ValuativeRel.ValueGroupWithZero F)ˣ) ≤ Units.mk0 (v y) hvy := by
        rw [← Units.val_le_val]
        simpa [Units.mk0_val] using hcon
      have h2 : (1 : (ValuativeRel.ValueGroupWithZero F)ˣ) ^ n ≤ (Units.mk0 (v y) hvy) ^ n :=
        pow_le_pow_left' h1 n
      rw [one_pow] at h2
      rw [← Units.val_le_val] at h2
      simpa [Units.val_pow_eq_pow_val, Units.mk0_val] using h2
    have hnot : ¬ (∀ᶠ n : ℕ in atTop,
        y ^ n ∈ ({z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)})) := by
      intro hev
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      have hn1 : 1 ≤ max N 1 := le_max_right _ _
      have hmem := hN (max N 1) (le_max_left _ _)
      have hlt : v (y ^ max N 1) < (γ : ValuativeRel.ValueGroupWithZero F) := hmem
      have hge : (1 : ValuativeRel.ValueGroupWithZero F) ≤ v (y ^ max N 1) := by
        rw [map_pow]; exact hpow _ hn1
      have hγv : (γ : ValuativeRel.ValueGroupWithZero F) < 1 := by
        simpa using ((Units.val_lt_val (a := γ) (b := (1 : (ValuativeRel.ValueGroupWithZero F)ˣ))).mpr hγ)
      exact not_lt_of_ge (le_of_lt hlt) (lt_of_lt_of_le hγv hge)
    exact hnot (h.eventually hball)
  · intro h s hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff (x := (0 : F))).mp hs
    have hγ' : {z : F | v z < (γ : ValuativeRel.ValueGroupWithZero F)} ⊆ s :=
      fun z hz => hγ ⟨z, hz, by simp⟩
    have hgoal : ∀ᶠ n : ℕ in atTop, v (y ^ n) < (γ : ValuativeRel.ValueGroupWithZero F) := by
      rcases eq_or_ne y 0 with hy0 | hy
      · rw [hy0]
        refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
        rw [zero_pow (by omega : n ≠ 0)]
        exact zero_lt_iff.mpr (Units.ne_zero γ)
      · have hvy : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr hy
        have ha : Units.mk0 (v y) hvy < 1 := by
          rw [← Units.val_lt_val]; simpa [Units.mk0_val] using h
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
          (G := (ValuativeRel.ValueGroupWithZero F)ˣ) ha (b := γ)
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have h2 := hN n hn
        rw [← Units.val_lt_val] at h2
        simp only [Units.val_pow_eq_pow_val, Units.mk0_val] at h2
        simpa [map_pow] using h2
    exact hgoal.mono fun n hn => hγ' hn

/-! ### The bridge between `Valued.v` and the valuative relation -/

private theorem valued_v_le_one_iff {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : Q.adicCompletion K) :
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x ≤ 1 ↔
      (ValuativeRel.valuation (Q.adicCompletion K)) x ≤ 1 := by
  haveI hnt : Nontrivial (ValuativeRel.ValueGroupWithZero (Q.adicCompletion K))ˣ :=
    ValuativeRel.isNontrivial_iff_nontrivial_units.mp
      (inferInstance : ValuativeRel.IsNontrivial (Q.adicCompletion K))
  set v := ValuativeRel.valuation (Q.adicCompletion K) with hv
  have hsv : ∀ y : Q.adicCompletion K,
      Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔
        (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) y < 1 := by
    intro y
    rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    exact Valued.toNormedField.norm_lt_one_iff ..
  have hvlt : ∀ y : Q.adicCompletion K,
      Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) ↔ v y < 1 :=
    fun y => tendsto_pow_nhds_zero_iff_vlt_one y
  have hiff : ∀ y : Q.adicCompletion K,
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) y < 1 ↔ v y < 1 :=
    fun y => (hsv y).symm.trans (hvlt y)
  constructor
  · intro hx
    rcases lt_or_eq_of_le hx with h | h
    · exact le_of_lt ((hiff x).mp h)
    · have hxne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact one_ne_zero h.symm
      have hvu : (ValuativeRel.valuation (Q.adicCompletion K)) x ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hxne
      have hinv : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x⁻¹ = 1 := by
        rw [map_inv₀, h, inv_one]
      have hnot : ¬ ((ValuativeRel.valuation (Q.adicCompletion K)) x⁻¹ < 1) := by
        rw [← hiff x⁻¹]
        rw [hinv]
        exact lt_irrefl 1
      rw [map_inv₀] at hnot
      exact (one_le_inv₀ (zero_lt_iff.mpr hvu)).mp (not_lt.mp hnot)
  · intro hx
    rcases lt_or_eq_of_le hx with h | h
    · exact le_of_lt ((hiff x).mpr h)
    · have hxne : x ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact one_ne_zero h.symm
      have hvu : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hxne
      have hinv : (ValuativeRel.valuation (Q.adicCompletion K)) x⁻¹ = 1 := by
        rw [map_inv₀, h, inv_one]
      have hnot : ¬ ((Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) x⁻¹ < 1) := by
        rw [hiff x⁻¹]
        rw [hinv]
        exact lt_irrefl 1
      rw [map_inv₀] at hnot
      exact (one_le_inv₀ (zero_lt_iff.mpr hvu)).mp (not_lt.mp hnot)

private theorem valued_v_eq_one_iff {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (Q.adicCompletion K)ˣ) :
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) (u : Q.adicCompletion K) = 1 ↔
      (ValuativeRel.valuation (Q.adicCompletion K)) (u : Q.adicCompletion K) = 1 := by
  have h := fun x => valued_v_le_one_iff Q x
  have hu0 : (u : Q.adicCompletion K) ≠ 0 := Units.ne_zero u
  have hsvu : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)) (u : Q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hu0
  have hvu : (ValuativeRel.valuation (Q.adicCompletion K)) (u : Q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hu0
  constructor
  · intro h1
    have h2 : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0))
        ((u⁻¹ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have h3 := (h _).mp (le_of_eq h2)
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h3
    exact le_antisymm ((h _).mp (le_of_eq h1)) ((inv_le_one₀ (zero_lt_iff.mpr hvu)).mp h3)
  · intro h1
    have h2 : (ValuativeRel.valuation (Q.adicCompletion K))
        ((u⁻¹ : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have h3 := (h _).mpr (le_of_eq h2)
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h3
    exact le_antisymm ((h _).mpr (le_of_eq h1)) ((inv_le_one₀ (zero_lt_iff.mpr hsvu)).mp h3)


/-! ### The units of the completion -/

private lemma map_units_subtype_top {M : Type*} [Monoid M] (S : Submonoid M) :
    Subgroup.map (Units.map S.subtype) ⊤ = S.units := by
  ext u
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, hy⟩
    rw [Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [← hy]; simp
    · rw [← hy, ← map_inv]; simp
  · intro hu
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff S u).mp hu
    refine ⟨Units.mk ⟨(u : M), h1⟩ ⟨((u⁻¹ : Mˣ) : M), h2⟩ (Subtype.ext (by simp))
      (Subtype.ext (by simp)), Subgroup.mem_top _, ?_⟩
    exact Units.ext rfl

private lemma higherUnits_zero_eq_ker {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    higherUnits F 0 = (NK.LocalReciprocityLubinTate.Units.valUnits F).ker := by
  rw [higherUnits_zero F, ← NK.LocalReciprocityLubinTate.Units.ker_valUnits F]

private theorem adicUnits_eq_higherUnits_zero_aux {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    adicUnits K Q = higherUnits (Q.adicCompletion K) 0 := by
  have hadic : adicUnits K Q = (Q.adicCompletionIntegers K).units := by
    rw [adicUnits]
    exact map_units_subtype_top (Q.adicCompletionIntegers K).toSubmonoid
  rw [hadic, higherUnits_zero_eq_ker]
  ext u
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
    MonoidHom.mem_ker]
  rw [← Units.val_inj, Units.val_one]
  have hcoe : (↑(NK.LocalReciprocityLubinTate.Units.valUnits (Q.adicCompletion K) u) :
      ValuativeRel.ValueGroupWithZero (Q.adicCompletion K)) =
      (ValuativeRel.valuation (Q.adicCompletion K)) (u : Q.adicCompletion K) := rfl
  rw [hcoe]
  exact valued_v_eq_one_iff Q u

/-! ### Uniformisers have the same valuation -/

private lemma le_of_mem_zpowers_of_lt_one {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] {g a : G} (hg : g < 1) (ha : a ∈ Subgroup.zpowers g) (ha1 : a < 1) :
    a ≤ g := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h0 : g ^ n < g ^ (0 : ℤ) := by rw [zpow_zero, hn]; exact ha1
  have hn' : 0 < n := by
    by_contra h
    push Not at h
    exact absurd ((zpow_right_strictAnti hg).antitone h) (not_le.mpr h0)
  have hle : g ^ n ≤ g ^ (1 : ℤ) := (zpow_right_strictAnti hg).antitone (by omega)
  rw [zpow_one, hn] at hle
  exact hle

private lemma val_uniformizerUnit {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0))
      ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
  simp only [uniformizerUnit, Units.val_mk0]
  exact Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q

private theorem isEquiv_valued_valuation {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)).IsEquiv
      (ValuativeRel.valuation (Q.adicCompletion K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  exact valued_v_le_one_iff Q x

private theorem valuation_uniformizerUnit_eq {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    (ValuativeRel.valuation (Q.adicCompletion K)) (π : Q.adicCompletion K) =
      (ValuativeRel.valuation (Q.adicCompletion K))
        ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) := by
  haveI hnt : Nontrivial (ValuativeRel.ValueGroupWithZero (Q.adicCompletion K))ˣ :=
    ValuativeRel.isNontrivial_iff_nontrivial_units.mp
      (inferInstance : ValuativeRel.IsNontrivial (Q.adicCompletion K))
  have heq : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)).IsEquiv
      (ValuativeRel.valuation (Q.adicCompletion K)) := isEquiv_valued_valuation Q
  have hπsv : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0))
      (π : Q.adicCompletion K) < 1 := (heq.lt_one_iff_lt_one).mpr hπ.val_lt_one
  have hπ₀sv : (Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0))
      ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) < 1 := by
    rw [val_uniformizerUnit Q]
    rw [show (1 : Zstar0) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hπ₀lt : (ValuativeRel.valuation (Q.adicCompletion K))
      ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) < 1 :=
    (heq.lt_one_iff_lt_one).mp hπ₀sv
  have hπ₀ne : (ValuativeRel.valuation (Q.adicCompletion K))
      ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have hmem : Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K))
        ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) hπ₀ne ∈
      Subgroup.zpowers (Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K))
        (π : Q.adicCompletion K)) hπ.val_ne_zero) := by
    rw [← Valuation.IsUniformizer.zpowers_eq_valueGroup hπ]
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨(uniformizerUnit K Q : (Q.adicCompletion K)ˣ),
      by simp⟩
  refine le_antisymm ?_ ?_
  · rw [← heq (π : Q.adicCompletion K)
      ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)]
    rw [val_uniformizerUnit Q]
    exact Commons.RingTheory.Henselian.lt_one_le_exp_neg_one hπsv
  · have hunits : Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K))
          ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) hπ₀ne ≤
        Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K)) (π : Q.adicCompletion K))
          hπ.val_ne_zero :=
      le_of_mem_zpowers_of_lt_one
        (g := Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K))
          (π : Q.adicCompletion K)) hπ.val_ne_zero)
        (a := Units.mk0 ((ValuativeRel.valuation (Q.adicCompletion K))
          ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) hπ₀ne)
        (by rw [← Units.val_lt_val]; simpa [Units.mk0_val] using hπ.val_lt_one)
        hmem
        (by rw [← Units.val_lt_val]; simpa [Units.mk0_val] using hπ₀lt)
    rw [← Units.val_le_val] at hunits
    simpa [Units.mk0_val] using hunits

private lemma valUnits_uniformizerUnit_eq {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    NK.LocalReciprocityLubinTate.Units.valUnits (Q.adicCompletion K)
        (uniformizerUnit K Q) =
      NK.LocalReciprocityLubinTate.Units.valUnits (Q.adicCompletion K) π :=
  Units.ext (valuation_uniformizerUnit_eq Q hπ).symm

/-! ### Equal values give equal norm groups modulo `U^0` -/

private lemma zpowers_sup_higherUnits_eq_of_valUnits_eq {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {a b : Fˣ}
    (h : NK.LocalReciprocityLubinTate.Units.valUnits F a =
      NK.LocalReciprocityLubinTate.Units.valUnits F b) (m : ℕ) :
    Subgroup.zpowers (a ^ m) ⊔ higherUnits F 0 =
      Subgroup.zpowers (b ^ m) ⊔ higherUnits F 0 := by
  have hab : a * b⁻¹ ∈ higherUnits F 0 := by
    rw [higherUnits_zero_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hba : b * a⁻¹ ∈ higherUnits F 0 := by
    rw [higherUnits_zero_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hconj : ∀ x y : Fˣ, y * (x * y⁻¹) = x := by
    intro x y
    rw [mul_comm y (x * y⁻¹), mul_assoc, inv_mul_cancel, mul_one]
  have hkey : ∀ x y : Fˣ, y ^ m * (x ^ m * (y ^ m)⁻¹) = x ^ m := by
    intro x y
    calc y ^ m * (x ^ m * (y ^ m)⁻¹)
        = y ^ m * (x * y⁻¹) ^ m := by rw [mul_pow, inv_pow]
      _ = (y * (x * y⁻¹)) ^ m := by rw [← mul_pow]
      _ = x ^ m := by rw [hconj x y]
  have hpow : ∀ x y : Fˣ, (x * y⁻¹) ^ m = x ^ m * (y ^ m)⁻¹ := by
    intro x y
    rw [mul_pow, inv_pow]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_sup.mpr ⟨b ^ m, Subgroup.mem_zpowers _, a ^ m * (b ^ m)⁻¹, ?_, ?_⟩
    · rw [← hpow a b]
      exact Subgroup.pow_mem _ hab m
    · rw [hkey a b]
  · refine sup_le ?_ le_sup_right
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_sup.mpr ⟨a ^ m, Subgroup.mem_zpowers _, b ^ m * (a ^ m)⁻¹, ?_, ?_⟩
    · rw [← hpow b a]
      exact Subgroup.pow_mem _ hba m
    · rw [hkey b a]

/-! ## The main theorem -/

/-- **The norm group of the unramified level of degree `m` of `Q.adicCompletion K`** is
`⟨π^m⟩ · U⁰` for every uniformiser `π` of the completion. -/
theorem unramifiedNormGroup_eq_zpowers_sup {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (Q.adicCompletion K)ˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (m : ℕ) :
    NK.LocalReciprocityLubinTate.unramifiedNormGroup K Q m =
      Subgroup.zpowers (π ^ m) ⊔
        NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K) 0 := by
  rw [unramifiedNormGroup, adicUnits_eq_higherUnits_zero_aux Q]
  exact zpowers_sup_higherUnits_eq_of_valUnits_eq (valUnits_uniformizerUnit_eq Q hπ) m

end

end NK.LocalReciprocityLubinTate.Unramified

