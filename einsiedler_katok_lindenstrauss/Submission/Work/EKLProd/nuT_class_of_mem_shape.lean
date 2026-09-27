import Mathlib
import Submission.Work.EKLComp.PlaqueToolkit
import Submission.Work.EKLProd.nuT_aDiag_pow_invariant
import Submission.Work.EKLProd.null_transfer
import Submission.Work.EKLComp.Hopf_inequality
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.ClassAux
import Submission.Work.EKLProd.pow_smul_mul_smul
import Submission.Work.EKLProd.returns_from_density
import Submission.Work.EKLProd.densitySet_compl_measure_le
import Submission.Work.EKLProd.exists_compact_family
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# The class of `νT` is constant along the `U`-foliation (Pisa Prop. 8.5, restricted form)

`Work.EKLProd.nuT_class_of_mem_shape`: for `μ`-a.e. `x` in the `H`-orbit plaque, the `νH x`-measure
of the set of `y` in the `H`-shape of the plaque algebra for which `νT (y • x)` is *not* the
right translate (by the `T`-part of `y`) of `νT x` up to proportionality is zero.

The proof follows Pisa §8.7.  The dynamical input is `Work.EKLProd.class_of_return`: along a
sequence of times at which both `a^n • x` and `a^n • (y • x)` are back in a Luzin compact `K`, a
subsequence of `a^n • x` converges to `x₀ ∈ K`; continuity of `z ↦ ∫ f dνT z` on `K` together
with the exact `a`-invariance of `νT` on the conull set `G` gives `νT x = νT x₀` and
`νT (y • x) = νT (y • x₀)`, and the equivariance of `νT` under `T` at `x₀` gives the claimed
proportionality.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- **The dynamical core.**  Given a compact `K ⊆ XT` on which every leafwise average is
continuous, a set `G ⊆ XT` on which the `T`-leafwise measures are exactly invariant under the
forward powers of `a = aDiag t`, points `x` and `(g * u) • x` in `G` whose `a`-orbits return to
`K` simultaneously at arbitrarily large times, with `g ∈ T` commuting with `a` and `u` contracted
by `a`, we have `νT ((g * u) • x) ∝ (νT x).map (· * g⁻¹)`. -/
theorem class_of_return {μ : Measure X3} [IsProbabilityMeasure μ]
    {T : Subgroup SL3} {νT : X3 → Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    {K : Set X3} (hK : IsCompact K) (hKT : K ⊆ XT)
    (hcont : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, ContinuousOn (fun x => ∫ g, f g ∂(νT x)) K)
    {G : Set X3} {t : Fin 3 → ℝ} (hGT : G ⊆ XT)
    (hG : ∀ z ∈ G, ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z)
    {g u : SL3} (hg : g ∈ T) {x : X3}
    (hxG : x ∈ G) (hzG : (g * u) • x ∈ G)
    (hret : ∀ N : ℕ, ∃ n, n ≥ N ∧ aDiag t ^ n • x ∈ K ∧ aDiag t ^ n • ((g * u) • x) ∈ K)
    (hcomm : ∀ n : ℕ, aDiag t ^ n * g = g * aDiag t ^ n)
    (hconv : Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) :
    PropEq ((νT x).map (fun g' => g' * g⁻¹)) (νT ((g * u) • x)) := by
  classical
  -- Step 1: a strictly increasing sequence of simultaneous return times.
  let φ : ℕ → ℕ := fun N => Nat.rec (Classical.choose (hret 0))
      (fun _ prev => Classical.choose (hret (prev + 1))) N
  have hφ_zero : φ 0 = Classical.choose (hret 0) := rfl
  have hφ_succ : ∀ N, φ (N + 1) = Classical.choose (hret (φ N + 1)) := fun N => rfl
  have hφP : ∀ N, aDiag t ^ (φ N) • x ∈ K ∧ aDiag t ^ (φ N) • ((g * u) • x) ∈ K := by
    intro N; induction N with
    | zero => exact (Classical.choose_spec (hret 0)).2
    | succ N _ => exact (Classical.choose_spec (hret (φ N + 1))).2
  have hφ_lt : ∀ N, φ N < φ (N + 1) := by
    intro N
    rw [hφ_succ]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Classical.choose_spec (hret (φ N + 1))).1
  have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ hφ_lt
  -- Step 2: a convergent subsequence, with limit in `K`.
  obtain ⟨x₀, hx₀K, ψ, hψ_strict, hψ_tend⟩ :=
    IsCompact.tendsto_subseq hK (fun N => (hφP N).1)
  have hx₀XT : x₀ ∈ XT := hKT hx₀K
  have hψ_atTop : Tendsto ψ atTop atTop := hψ_strict.tendsto_atTop
  have hφψ_atTop : Tendsto (fun i => φ (ψ i)) atTop atTop := hφ_strict.tendsto_atTop.comp hψ_atTop
  have hconv_sub : Tendsto (fun i => aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹) atTop (𝓝 1) :=
    hconv.comp hφψ_atTop
  -- Step 3: the second orbit also converges, to `g • x₀`.
  have hsmul_tend : Tendsto
      (fun i => (aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹) • (aDiag t ^ (φ (ψ i)) • x))
      atTop (𝓝 x₀) := by
    have hpair : Tendsto (fun i => (aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹,
        aDiag t ^ (φ (ψ i)) • x)) atTop (𝓝 ((1 : SL3), x₀)) := by
      rw [nhds_prod_eq]
      exact hconv_sub.prodMk hψ_tend
    have h := ((continuous_smul).tendsto ((1 : SL3), x₀)).comp hpair
    simp only [Prod.fst, Prod.snd, one_smul] at h
    have hF : ((fun p : SL3 × X3 => p.1 • p.2) ∘ (fun i =>
        (aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹, aDiag t ^ (φ (ψ i)) • x)))
        = (fun i => (aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹) •
            (aDiag t ^ (φ (ψ i)) • x)) := rfl
    rw [hF] at h
    exact h
  have hsecond_tend : Tendsto (fun i => aDiag t ^ (φ (ψ i)) • ((g * u) • x)) atTop (𝓝 (g • x₀)) := by
    have h2 : Tendsto (fun i => g • ((aDiag t ^ (φ (ψ i)) * u * (aDiag t ^ (φ (ψ i)))⁻¹) •
        (aDiag t ^ (φ (ψ i)) • x))) atTop (𝓝 (g • x₀)) :=
      ((continuous_const_smul g).tendsto x₀).comp hsmul_tend
    refine h2.congr' ?_
    filter_upwards with i
    exact (pow_smul_mul_smul (φ (ψ i)) (hcomm (φ (ψ i))) x).symm
  have hgx₀K : g • x₀ ∈ K :=
    hK.isClosed.mem_of_tendsto hsecond_tend (Eventually.of_forall (fun i => (hφP (ψ i)).2))
  have hgx₀XT : g • x₀ ∈ XT := hKT hgx₀K
  -- Step 4: the limits of the leafwise averages identify the measures.
  have hint₁ : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g', f g' ∂(νT x) = ∫ g', f g' ∂(νT x₀) := by
    intro f
    have h1 : ContinuousWithinAt (fun z => ∫ g', f g' ∂(νT z)) K x₀ :=
      (hcont f).continuousWithinAt hx₀K
    have h2 : Tendsto (fun i => aDiag t ^ (φ (ψ i)) • x) atTop (𝓝[K] x₀) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hψ_tend, Eventually.of_forall (fun i => (hφP (ψ i)).1)⟩
    have h3 : Tendsto (fun i => ∫ g', f g' ∂(νT (aDiag t ^ (φ (ψ i)) • x))) atTop
        (𝓝 (∫ g', f g' ∂(νT x₀))) := h1.tendsto.comp h2
    have h4 : (fun i => ∫ g', f g' ∂(νT (aDiag t ^ (φ (ψ i)) • x)))
        = fun _ => ∫ g', f g' ∂(νT x) := by
      funext i; rw [hG x hxG (φ (ψ i))]
    rw [h4] at h3
    exact tendsto_nhds_unique tendsto_const_nhds h3
  have hint₂ : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g', f g' ∂(νT ((g * u) • x)) = ∫ g', f g' ∂(νT (g • x₀)) := by
    intro f
    have h1 : ContinuousWithinAt (fun z => ∫ g', f g' ∂(νT z)) K (g • x₀) :=
      (hcont f).continuousWithinAt hgx₀K
    have h2 : Tendsto (fun i => aDiag t ^ (φ (ψ i)) • ((g * u) • x)) atTop (𝓝[K] (g • x₀)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hsecond_tend, Eventually.of_forall (fun i => (hφP (ψ i)).2)⟩
    have h3 : Tendsto (fun i => ∫ g', f g' ∂(νT (aDiag t ^ (φ (ψ i)) • ((g * u) • x)))) atTop
        (𝓝 (∫ g', f g' ∂(νT (g • x₀)))) := h1.tendsto.comp h2
    have h4 : (fun i => ∫ g', f g' ∂(νT (aDiag t ^ (φ (ψ i)) • ((g * u) • x))))
        = fun _ => ∫ g', f g' ∂(νT ((g * u) • x)) := by
      funext i; rw [hG ((g * u) • x) hzG (φ (ψ i))]
    rw [h4] at h3
    exact tendsto_nhds_unique tendsto_const_nhds h3
  haveI hfi₁ : IsFiniteMeasureOnCompacts (νT x) := hνT.radon x (hGT hxG)
  haveI hfi₂ : IsFiniteMeasureOnCompacts (νT x₀) := hνT.radon x₀ hx₀XT
  haveI hfi₃ : IsFiniteMeasureOnCompacts (νT ((g * u) • x)) := hνT.radon _ (hGT hzG)
  haveI hfi₄ : IsFiniteMeasureOnCompacts (νT (g • x₀)) := hνT.radon _ hgx₀XT
  have hmeas₁ : νT x = νT x₀ := Measure.ext_of_integral_eq_on_compactlySupported hint₁
  have hmeas₂ : νT ((g * u) • x) = νT (g • x₀) := Measure.ext_of_integral_eq_on_compactlySupported hint₂
  -- Step 5: equivariance of `νT` under `T` at `x₀`.
  have hx₀' : g⁻¹ • (g • x₀) ∈ XT := by rw [inv_smul_smul]; exact hx₀XT
  obtain ⟨c, hc0, hct, hceq⟩ := hνT.equivariant (g • x₀) hgx₀XT g⁻¹ (T.inv_mem hg) hx₀'
  rw [inv_smul_smul] at hceq
  refine ⟨c, hc0, hct, ?_⟩
  calc νT ((g * u) • x) = νT (g • x₀) := hmeas₂
    _ = c • (νT x₀).map (fun g' => g' * g⁻¹) := hceq
    _ = c • (νT x).map (fun g' => g' * g⁻¹) := by rw [hmeas₁]


/-- **The class of `νT` is constant along the `U`-foliation.**  Restricted to the `H`-orbit
plaque and measured by `νH x`, the set of points `y` of the `H`-shape for which the `T`-leafwise
measure at `y • x` is not the translate of `νT x` by the `T`-part of `y` has `νH x`-measure zero. -/
theorem nuT_class_of_mem_shape (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise)
    (hBirk : Work.EKLContract.P_Birkhoff)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hmu : Work.EKLContract.IsAInvariant μ)
    {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H)
    (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ g ∈ H, ∃ a ∈ T, ∃ b ∈ U, g = a * b) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3}
    (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3}
    (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    {x₀ : Work.EKLContract.X3} {ε : ℝ} (hε : 0 < ε)
    (hinj : ∀ y ∈ H, ∀ z ∈ H, y • x₀ = z • x₀ → y = z)
    (hP : μ (Work.EKLComp.orbitPlaque H x₀ ε) ≠ 0)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      νH x {y : Work.EKLContract.SL3 | y ∈ Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x ∧
        ¬ (∀ g ∈ T, g⁻¹ * y ∈ U → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
            νT (y • x) = c • (νT x).map (fun g' => g' * g⁻¹))} = 0 := by
  classical
  haveI : T2Space X3 := hX3.1
  have hHcl : IsClosed (H : Set SL3) := hH.1
  have hplaH : IsPlaqueAlgebra H (Work.EKLComp.orbitPlaque H x₀ ε)
      (Work.EKLComp.plaqueSigma H x₀ ε) :=
    Work.EKLComp.isPlaqueAlgebra_orbitPlaque hHcl hε hinj
  have hPmeas : MeasurableSet (Work.EKLComp.orbitPlaque H x₀ ε) := hplaH.1 _ hplaH.2.2.1
  have hatomP : ∀ x ∈ Work.EKLComp.orbitPlaque H x₀ ε,
      atom (Work.EKLComp.plaqueSigma H x₀ ε) x = Work.EKLComp.orbitPlaque H x₀ ε :=
    fun x hx => Work.EKLProd.atom_generateFrom_singleton _ x hx
  -- Luzin and `A`-covariance clauses of the frozen interface
  obtain ⟨t₀, ht₀⟩ := hT.2.2
  have hmp₀ : MeasurePreserving (fun x : X3 => aDiag t₀ • x) μ μ := hmu t₀
  obtain ⟨-, -, -, -, -, hU6, hU7, -, -⟩ := (hLeaf μ T hT t₀ hmp₀ ht₀).2 νT XT hνT
  obtain ⟨K, hKc, hKXT, hKmono, hKsmall, hKcont⟩ := Work.EKLProd.exists_compact_family (μ := μ) hU6
  obtain ⟨X'', hX''sub, hX''meas, hX''conull, hX''cov⟩ := hU7 hmu
  -- exact `a`-invariance of `νT` at the points of `X''`
  have hstep : ∀ z ∈ X'', aDiag t • z ∈ X'' → νT (aDiag t • z) = νT z := by
    intro z hz hz'
    obtain ⟨c, hc0, hct, hceq⟩ := hX''cov t z hz hz'
    have hcar : (νT z).map (fun g => aDiag t * g * (aDiag t)⁻¹) = νT z :=
      Work.EKLProd.map_conj_eq_of_carried_of_comm hcent (hνT.carried z (hX''sub hz))
    have h1 : νT (aDiag t • z) (Box1 T) = c * νT z (Box1 T) := by
      rw [hceq, Measure.smul_apply, hcar, smul_eq_mul]
    rw [hνT.normalised (aDiag t • z) (hX''sub hz'), hνT.normalised z (hX''sub hz), mul_one] at h1
    calc νT (aDiag t • z) = c • (νT z).map (fun g => aDiag t * g * (aDiag t)⁻¹) := hceq
      _ = c • νT z := by rw [hcar]
      _ = νT z := by rw [h1.symm, one_smul]
  -- the measurable conull set `G` on which `νT` is `a`-invariant
  have hmpn : ∀ n : ℕ, MeasurePreserving (fun x : X3 => aDiag t ^ n • x) μ μ := by
    intro n
    rw [← Work.EKLProd.aDiag_nsmul]
    exact hmu (n • t)
  set G : Set X3 := ⋂ n : ℕ, (fun x : X3 => aDiag t ^ n • x) ⁻¹' X'' with hGdef
  have hGmeas : MeasurableSet G := by
    rw [hGdef]
    exact MeasurableSet.iInter (fun n => hX''meas.preimage (hmpn n).measurable)
  have hGconull : μ Gᶜ = 0 := by
    rw [hGdef, Set.compl_iInter]
    refine measure_iUnion_null (fun n => ?_)
    rw [← Set.preimage_compl, ← Measure.map_apply (hmpn n).measurable hX''meas.compl,
      (hmpn n).map_eq]
    exact hX''conull
  have hGXT : G ⊆ XT := by
    intro x hx
    have h0 : x ∈ (fun x : X3 => aDiag t ^ 0 • x) ⁻¹' X'' := Set.mem_iInter.mp hx 0
    exact hX''sub (by simpa using h0)
  have hGinv : ∀ z ∈ G, ∀ n : ℕ, νT (aDiag t ^ n • z) = νT z := by
    intro z hz n
    have hzall : ∀ k : ℕ, aDiag t ^ k • z ∈ X'' := fun k => Set.mem_iInter.mp hz k
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : aDiag t ^ (n + 1) • z = aDiag t • (aDiag t ^ n • z) := by
        rw [pow_succ', mul_smul]
      rw [h2, hstep _ (hzall n) (h2 ▸ hzall (n + 1)), ih]
  -- the density sets `Ym m`
  set Ym : ℕ → Set X3 := fun m => {x : X3 | ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range n, ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n}
    with hYm
  have hYm_meas : ∀ m, MeasurableSet (Ym m) := by
    intro m
    have hEq : Ym m = ⋂ n : ℕ, {x : X3 | 0 < n →
        (∑ j ∈ Finset.range n, ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x))
          ≤ (1/3) * n} := by
      rw [hYm]; ext x; simp [Set.mem_iInter]
    rw [hEq]
    refine MeasurableSet.iInter (fun n : ℕ => ?_)
    have hsum : Measurable (fun x : X3 =>
        ∑ j ∈ Finset.range n, ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) := by
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact (Measurable.indicator measurable_const (hKc m).measurableSet.compl).comp
        (hmpn j).measurable
    by_cases hn : 0 < n
    · have hset : {x : X3 | 0 < n → (∑ j ∈ Finset.range n,
          ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n}
          = {x : X3 | (∑ j ∈ Finset.range n,
          ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n} := by
        ext x; simp [hn]
      rw [hset]
      exact measurableSet_le hsum measurable_const
    · have hset : {x : X3 | 0 < n → (∑ j ∈ Finset.range n,
          ((K m)ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n} = Set.univ := by
        ext x; simp [hn]
      rw [hset]; exact MeasurableSet.univ
  have hYm_compl : ∀ m, μ (Ym m)ᶜ ≤ ENNReal.ofReal (3 * (μ (K m)ᶜ).toReal) := by
    intro m
    have h := Work.EKLProd.densitySet_compl_measure_le (μ := μ) (a := aDiag t) (hmu t)
      (hKc m).measurableSet
    simpa only [hYm] using h
  have hYm_mono : Monotone Ym := by
    intro m m' hmm x hx
    rw [hYm] at hx ⊢
    intro n hn
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hx n hn)
    by_cases h : aDiag t ^ j • x ∈ (K m')ᶜ
    · rw [Set.indicator_of_mem h]
      by_cases h2 : aDiag t ^ j • x ∈ (K m)ᶜ
      · rw [Set.indicator_of_mem h2]
      · exact absurd (hKmono hmm (by simpa using h2)) (by simpa using h)
    · rw [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  -- the conull good set `X0`
  set X0 : Set X3 := ⋃ m, Ym m with hX0
  have hX0_meas : MeasurableSet X0 := by
    rw [hX0]; exact MeasurableSet.iUnion hYm_meas
  have hX0_conull : μ X0ᶜ = 0 := by
    have hbound : ∀ m : ℕ, μ X0ᶜ ≤ ENNReal.ofReal (3 * ((m : ℝ) + 1)⁻¹) := by
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
    refine le_antisymm ?_ bot_le
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (3 * ((m : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun m : ℕ => (3 : ℝ) * ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 : ℝ)
        rw [mul_zero] at h
        simpa only [one_div] using h
      simpa using ENNReal.tendsto_ofReal h0
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
  -- the null set `N` and the leafwise transfer
  set N : Set X3 := Gᶜ ∪ X0ᶜ with hNdef
  have hN_meas : MeasurableSet N := by
    rw [hNdef]; exact hGmeas.compl.union hX0_meas.compl
  have hN_null : μ N = 0 := by
    rw [hNdef, measure_union_null_iff]; exact ⟨hGconull, hX0_conull⟩
  have htransfer : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      νH x {u : SL3 | u • x ∈ N ∩ Work.EKLComp.orbitPlaque H x₀ ε} = 0 :=
    Work.EKLComp.leafwise_null_local hνH hε hHcl hinj hP hN_meas hN_null
  have hNaeμ : ∀ᵐ x ∂μ, x ∉ N := by
    rw [MeasureTheory.ae_iff]
    rw [show {a : X3 | ¬ (a ∉ N)} = N from by
      ext a; by_cases h : a ∈ N <;> simp [h]]
    exact hN_null
  have hNae : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)), x ∉ N :=
    MeasureTheory.ae_restrict_of_ae hNaeμ
  have hPae : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      x ∈ Work.EKLComp.orbitPlaque H x₀ ε :=
    (MeasureTheory.ae_restrict_iff' hPmeas).mpr (Eventually.of_forall (fun _ hx => hx))
  filter_upwards [htransfer, hNae, hPae] with x hxNtrans hxN hxP
  refine le_antisymm (le_trans (measure_mono ?_) (le_of_eq hxNtrans)) bot_le
  intro y hy
  obtain ⟨hyshape, hybad⟩ := hy
  have hyH : y ∈ H := hyshape.1
  obtain ⟨a, haT, b, hbU, hyab⟩ := hcop y hyH
  have hyxP : y • x ∈ Work.EKLComp.orbitPlaque H x₀ ε :=
    hatomP x hxP ▸ hyshape.2
  refine ⟨?_, hyxP⟩
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
      ((K (max m₁ m₂))ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • x)) ≤ (1/3) * n := by
    have h := hmemx; rw [hYm] at h; exact h
  have hretz : ∀ n : ℕ, 0 < n → (∑ j ∈ Finset.range n,
      ((K (max m₁ m₂))ᶜ.indicator (fun _ => (1 : ℝ))) (aDiag t ^ j • (y • x))) ≤ (1/3) * n := by
    have h := hmemz; rw [hYm] at h; exact h
  have hret := Work.EKLProd.returns_from_density (a := aDiag t) (K := K (max m₁ m₂))
    (x := x) (z := y • x) hretx hretz
  -- the `T`-part of `y` is `a`
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
    fun n => Work.EKLProd.pow_mul_eq_mul_pow (hcent a haT) n
  have hret' : ∀ N : ℕ, ∃ n, n ≥ N ∧ aDiag t ^ n • x ∈ K (max m₁ m₂) ∧
      aDiag t ^ n • ((a * b) • x) ∈ K (max m₁ m₂) := by
    intro N
    obtain ⟨n, hn, h1, h2⟩ := hret N
    exact ⟨n, hn, h1, by rwa [hyab] at h2⟩
  obtain ⟨c, hc0, hct, hceq⟩ := class_of_return (K := K (max m₁ m₂)) (g := a) (u := b) hνT
    (hKc _) (hKXT _) (hKcont _) hGXT hGinv haT hxG (by rw [← hyab]; exact hyxG) hret' hcomm'
    (hcontr b hbU)
  exact hybad (fun g hgT hgy => by
    have hga : g = a := huniq g hgT hgy
    refine ⟨c, hc0, hct, ?_⟩
    rw [hga, hyab]
    exact hceq)

end Work.EKLProd
