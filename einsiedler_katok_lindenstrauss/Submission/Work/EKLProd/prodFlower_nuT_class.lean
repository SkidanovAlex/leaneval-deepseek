import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.nuT_class_of_mem_shape
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLC6Core.shape_mass_pos

/-!
# The class of `νT` is constant along the `H`-plaques of a product-box flower

`Work.EKLProd.prodFlower_nuT_class` is the *flower* version of the Pisa Prop. 8.5 step
(the analogue, for the product-box flowers of `Work.EKLProd.ProdFlowerFam`, of the already
proved ball-plaque lemma `Work.EKLProd.nuT_class_of_mem_shape`).

The substance of the proof is factored out into the private lemma `conull_aDiag_inv_set`
(exact invariance of `νT` on a conull set) and `densitySets_conull` (the density sets of the
Birkhoff argument), and into the general plaque-algebra statement
`Work.EKLProd.prodFlower_nuT_class_gen`.  Only the latter's shape hypothesis is used: the
argument never needs the geometric description of the shape — it uses only that
`shape m H x ⊆ H`, that the atoms of a plaque algebra are contained in its carrier `Z`, and
the leafwise transfer `Work.EKLProd.leafwise_null_transfer_gen` for the a.e. null set.
The target lemma is then the instantiation at `Z = hf.Z n`, `m = hf.mH n`.
-/

open MeasureTheory Filter Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false


namespace Work.EKLProd

open Work.EKLContract

/-- A conull set `G ⊆ XT` on which a leafwise system for a horospherical subgroup `T` is
exactly invariant under **all** powers of a diagonal element `aDiag t` commuting with `T`.

This is the "one common set" form of `Work.EKLProd.nuT_aDiag_pow_invariant`: the good set for
each exponent `n` is conull, and there are countably many of them. -/
private theorem conull_aDiag_inv_set {μ : Measure X3} [IsProbabilityMeasure μ]
    (hLeaf : P_Leafwise) (hmu : IsAInvariant μ) {T : Subgroup SL3} (hT : IsHoro T)
    {νT : X3 → Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, aDiag t * g = g * aDiag t) :
    ∃ G : Set X3, G ⊆ XT ∧ μ Gᶜ = 0 ∧ ∀ z ∈ G, ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z := by
  have hpow : ∀ᵐ z ∂μ, ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z :=
    ae_all_iff.mpr (fun n => nuT_aDiag_pow_invariant hLeaf hmu hT hνT t hcent n)
  refine ⟨XT ∩ {z : X3 | ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z}, Set.inter_subset_left, ?_, ?_⟩
  · have h2 : μ {z : X3 | ¬ (∀ n : ℕ, νT (aDiag t ^ n • z) = νT z)} = 0 := by
      rw [← ae_iff]; exact hpow
    refine le_antisymm ?_ bot_le
    calc μ (XT ∩ {z : X3 | ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z})ᶜ
        ≤ μ (XTᶜ ∪ {z : X3 | ¬ (∀ n : ℕ, νT (aDiag t ^ n • z) = νT z)}) := by
          refine measure_mono ?_
          intro z hz
          by_cases h : z ∈ XT
          · exact Or.inr (fun hall => hz ⟨h, hall⟩)
          · exact Or.inl h
      _ ≤ μ XTᶜ + μ {z : X3 | ¬ (∀ n : ℕ, νT (aDiag t ^ n • z) = νT z)} :=
          measure_union_le _ _
      _ = 0 := by rw [hνT.conull, h2, add_zero]
  · intro z hz n
    exact hz.2 n

/-- The density sets of the Birkhoff argument: a monotone family `Ym` with conull union on
which the orbit of `a` visits `K m` with density at least `2/3`.

This is the packaged form of the construction used in `Work.EKLProd.nuT_class_of_mem_shape`;
the only input is the Hopf maximal inequality in the shape of
`Work.EKLProd.densitySet_compl_measure_le`. -/
private theorem densitySets_conull {μ : Measure X3} [IsProbabilityMeasure μ] {a : SL3}
    (hmp : MeasurePreserving (fun x : X3 => a • x) μ μ) (K : ℕ → Set X3)
    (hKc : ∀ m, IsCompact (K m)) (hKmono : Monotone K)
    (hKsmall : ∀ m, μ (K m)ᶜ < ((m + 1 : ℕ) : ENNReal)⁻¹) :
    ∃ Ym : ℕ → Set X3, Monotone Ym ∧ μ (⋃ m, Ym m)ᶜ = 0 ∧
      ∀ m, ∀ x ∈ Ym m, ∀ n : ℕ, 0 < n →
        (∑ j ∈ Finset.range n, ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (a ^ j • x)) ≤ (1/3) * n := by
  classical
  set Ym : ℕ → Set X3 := fun m => {x : X3 | ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range n, ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (a ^ j • x)) ≤ (1/3) * n}
    with hYm
  have hYm_mono : Monotone Ym := by
    intro m m' hmm x hx
    rw [hYm] at hx ⊢
    intro n hn
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hx n hn)
    by_cases h : a ^ j • x ∈ (K m')ᶜ
    · rw [Set.indicator_of_mem h]
      by_cases h2 : a ^ j • x ∈ (K m)ᶜ
      · rw [Set.indicator_of_mem h2]
      · exact absurd (hKmono hmm (by simpa using h2)) (by simpa using h)
    · rw [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hYm_compl : ∀ m, μ (Ym m)ᶜ ≤ ENNReal.ofReal (3 * (μ (K m)ᶜ).toReal) := by
    intro m
    have h := densitySet_compl_measure_le (μ := μ) (a := a) hmp (hKc m).measurableSet
    simpa only [hYm] using h
  have hconull : μ (⋃ m, Ym m)ᶜ = 0 := by
    refine le_antisymm ?_ bot_le
    have hbound : ∀ m : ℕ, μ (⋃ m, Ym m)ᶜ ≤ ENNReal.ofReal (3 * ((m : ℝ) + 1)⁻¹) := by
      intro m
      refine le_trans (measure_mono ?_) (le_trans (hYm_compl m) (ENNReal.ofReal_le_ofReal ?_))
      · intro x hx h
        exact hx (Set.mem_iUnion.mpr ⟨m, h⟩)
      · have h2 : (μ (K m)ᶜ).toReal < ((((m + 1 : ℕ) : ENNReal))⁻¹).toReal :=
          (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
            (ENNReal.inv_ne_top.mpr (by simp))).mpr (hKsmall m)
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at h2
        have h2' : (μ (K m)ᶜ).toReal < ((m : ℝ) + 1)⁻¹ := by simpa using h2
        linarith
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (3 * ((m : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m : ℕ => (3 : ℝ) * ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 : ℝ)
        rw [mul_zero] at h
        simpa only [one_div] using h
      simpa using ENNReal.tendsto_ofReal h0
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
  exact ⟨Ym, hYm_mono, hconull, fun m x hx n hn => by rw [hYm] at hx; exact hx n hn⟩

/-- **The class of `νT` is constant along the `H`-plaques of an arbitrary plaque algebra.**

The plaque-algebra version of `Work.EKLProd.nuT_class_of_mem_shape`: the role of the orbit
plaque is played by an arbitrary plaque algebra `(Z, mH)` for `H` whose shape has finite
positive `νH x`-mass a.e.  The proof is the one of `nuT_class_of_mem_shape` with the
plaque-specific inputs (`isPlaqueAlgebra_orbitPlaque`, `leafwise_null_local`, the freeness of
the base orbits, the shape formula) replaced by `leafwise_null_transfer_gen`, the a.e. mass
hypothesis, and the abstract fact that the atom of a plaque algebra is contained in its
carrier. -/
theorem prodFlower_nuT_class_gen {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hX3 : P_X3) (hLeaf : P_Leafwise) (hmu : IsAInvariant μ)
    {H T U : Subgroup SL3} (hH : IsHoro H) (hT : IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ g ∈ H, ∃ a ∈ T, ∃ b ∈ U, g = a * b) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {νH : X3 → MeasureTheory.Measure SL3} {XH : Set X3} (hνH : IsLeafwise μ H νH XH)
    {νT : X3 → MeasureTheory.Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    {Z : Set X3} {mH : MeasurableSpace X3} (hmH : IsPlaqueAlgebra H Z mH)
    (hmass : ∀ᵐ x ∂(μ.restrict Z),
      0 < (νH x) (shape mH H x) ∧ (νH x) (shape mH H x) < ⊤)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, aDiag t * g = g * aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂(μ.restrict Z), (νH x) {y : SL3 | y ∈ shape mH H x ∧
      ¬ (∀ g ∈ T, g⁻¹ * y ∈ U → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
          νT (y • x) = c • (νT x).map (fun g' => g' * g⁻¹))} = 0 := by
  classical
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  haveI : T2Space X3 := hX3.1
  -- Luzin compactness and `A`-covariance of `νT` from the frozen interface
  obtain ⟨t₀, ht₀⟩ := hT.2.2
  have hmp₀ : MeasurePreserving (fun x : X3 => aDiag t₀ • x) μ μ := hmu t₀
  obtain ⟨-, -, -, -, -, hU6, hU7, -, -⟩ := (hLeaf μ T hT t₀ hmp₀ ht₀).2 νT XT hνT
  obtain ⟨K, hKc, hKXT, hKmono, hKsmall, hKcont⟩ := exists_compact_family (μ := μ) hU6
  -- the conull set of exact `aDiag t`-invariance, and the density sets
  obtain ⟨G, hGXT, hGconull, hGinv⟩ := conull_aDiag_inv_set hLeaf hmu hT hνT t hcent
  obtain ⟨Ym, hYm_mono, hX0conull, hYmmem⟩ :=
    densitySets_conull (μ := μ) (a := aDiag t) (hmu t) K hKc hKmono hKsmall
  set X0 : Set X3 := ⋃ m, Ym m with hX0def
  have hX0conull' : μ X0ᶜ = 0 := by rw [hX0def]; exact hX0conull
  -- the `μ`-null set `N` of all bad points
  set N : Set X3 := Gᶜ ∪ X0ᶜ with hNdef
  have hN_null : μ N = 0 := by
    rw [hNdef]; exact measure_union_null hGconull hX0conull'
  have hNrestrict : (μ.restrict Z) N = 0 :=
    le_antisymm (le_trans (Measure.restrict_apply_le Z N) (le_of_eq hN_null)) bot_le
  -- transfer of nullity to the leafwise measures of the plaque algebra
  have htransfer := leafwise_null_transfer_gen hνH hmH hmass hNrestrict
  have hNaeμ : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    rw [show {a : X3 | ¬ (a ∉ N)} = N from by ext a; by_cases h : a ∈ N <;> simp [h]]
    exact hN_null
  have hNae : ∀ᵐ x ∂(μ.restrict Z), x ∉ N := ae_restrict_of_ae hNaeμ
  filter_upwards [htransfer, hNae] with x hxNtrans hxN
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hxNtrans)) bot_le
  intro y hy
  obtain ⟨hyshape, hybad⟩ := hy
  refine ⟨hyshape, ?_⟩
  -- if `y • x` is good, the dynamical core gives the proportionality, contradicting `hybad`
  by_contra hyxN
  have hyxG : y • x ∈ G := by
    by_contra h; exact hyxN (Or.inl h)
  have hyxX0 : y • x ∈ X0 := by
    by_contra h; exact hyxN (Or.inr h)
  have hxG : x ∈ G := by
    by_contra h; exact hxN (Or.inl h)
  have hxX0 : x ∈ X0 := by
    by_contra h; exact hxN (Or.inr h)
  obtain ⟨m₁, hm₁⟩ := Set.mem_iUnion.mp hyxX0
  obtain ⟨m₂, hm₂⟩ := Set.mem_iUnion.mp hxX0
  have hmemx : x ∈ Ym (max m₁ m₂) := hYm_mono (le_max_right _ _) hm₂
  have hmemz : y • x ∈ Ym (max m₁ m₂) := hYm_mono (le_max_left _ _) hm₁
  have hretx : ∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n,
      ((K (max m₁ m₂))ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n :=
    fun n hn => hYmmem _ x hmemx n hn
  have hretz : ∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n,
      ((K (max m₁ m₂))ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • (y • x))) ≤ (1/3) * n :=
    fun n hn => hYmmem _ (y • x) hmemz n hn
  have hret := returns_from_density (a := aDiag t) (K := K (max m₁ m₂)) (x := x) (z := y • x)
    hretx hretz
  -- the `T`-part of `y`
  have hyH : y ∈ H := hyshape.1
  obtain ⟨a, haT, b, hbU, hyab⟩ := hcop y hyH
  have huniq : ∀ g ∈ T, g⁻¹ * y ∈ U → g = a := by
    intro g hgT hgy
    have h2 : g⁻¹ * a * b ∈ U := by
      have hgy' : g⁻¹ * a * b = g⁻¹ * y := by rw [hyab, mul_assoc]
      rw [hgy']; exact hgy
    have h1 : g⁻¹ * a ∈ U := by
      have h3 : (g⁻¹ * a * b) * b⁻¹ ∈ U := U.mul_mem h2 (U.inv_mem hbU)
      have h4 : (g⁻¹ * a * b) * b⁻¹ = g⁻¹ * a := by group
      rwa [h4] at h3
    have h3 : g⁻¹ * a ∈ T := T.mul_mem (T.inv_mem hgT) haT
    have h4 : g⁻¹ * a = 1 := hdisj _ h3 h1
    calc g = g * (g⁻¹ * a) := by rw [h4, mul_one]
      _ = (g * g⁻¹) * a := by rw [mul_assoc]
      _ = a := by rw [mul_inv_cancel, one_mul]
  have hcomm' : ∀ n : ℕ, aDiag t ^ n * a = a * aDiag t ^ n :=
    fun n => pow_mul_eq_mul_pow (hcent a haT) n
  have hret' : ∀ N : ℕ, ∃ n, n ≥ N ∧ aDiag t ^ n • x ∈ K (max m₁ m₂) ∧
      aDiag t ^ n • ((a * b) • x) ∈ K (max m₁ m₂) := by
    intro N
    obtain ⟨n, hn, h1, h2⟩ := hret N
    exact ⟨n, hn, h1, by rwa [hyab] at h2⟩
  obtain ⟨c, hc0, hct, hceq⟩ := class_of_return (K := K (max m₁ m₂)) (g := a) (u := b) hνT
    (hKc (max m₁ m₂)) (hKXT (max m₁ m₂)) (hKcont (max m₁ m₂)) hGXT hGinv haT hxG
    (by rw [← hyab]; exact hyxG) hret' hcomm' (hcontr b hbU)
  exact hybad (fun g hgT hgy => by
    have hga : g = a := huniq g hgT hgy
    refine ⟨c, hc0, hct, ?_⟩
    rw [hga, hyab]
    exact hceq)

theorem prodFlower_nuT_class (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) (n : ℕ) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), (νH x) {y : Work.EKLContract.SL3 | y ∈ Work.EKLContract.shape (hf.mH n) H x ∧ ¬ (∀ g ∈ T, g⁻¹ * y ∈ U → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ νT (y • x) = c • (νT x).map (fun g' => g' * g⁻¹))} = 0 := by
  refine prodFlower_nuT_class_gen (μ := μ) hX3 hLeaf hmu hH hT hTH hUH hnorm hcop hdisj
    hνH hνT (Z := hf.Z n) (mH := hf.mH n) (hf.plaqH n) (prodFlower_shape_mass hf hνH n)
    t hcent hcontr


end Work.EKLProd
