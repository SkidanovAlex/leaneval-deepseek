import Mathlib
import Submission.Work.BourgainPlan.Assembly.Defs
import Submission.Work.BourgainPlan.Assembly.tendsto_of_eventually_close

/-!
# The oscillation inequality implies almost everywhere convergence

Bourgain's oscillation method: `HasOsc` (an `o(J)` bound, uniform over *every* strictly
increasing block structure `k`, on the sum of the squared `L²` norms of the `J` block
oscillations) forces a.e. convergence of the sequence.

The classical proof is the greedy ("quantile") argument.  Suppose for some `η > 0` that the set
`S` of points carrying infinitely many oscillations of size `η` has positive measure.  One
builds a *single* block structure `k` as follows: given the anchor `k j`, the next anchor
`k (j+1)` is chosen so that at least half of `S` (in measure) is "captured" by the block
`[k j, k (j+1))`, i.e. carries an index `i` of that block with `|u i - u_{k j}| ≥ η/2`.  This
is possible because every point of `S` has oscillations arbitrarily far out, so the capture
sets increase to `S`.  Since each of the `J` blocks then contributes at least
`(η/2)² · μ S / 2` to the oscillation sum, that sum is bounded below by a constant times `J`,
contradicting `HasOsc` with `ε = (η/2)² (μ S)/2 / (2 (C+1))`.

Consequently the oscillation set is null for every `η > 0`; taking `η = 1/(m+1)` shows that
for a.e. `x` and every `m` the tail of `(u i x)` has diameter at most `1/(m+1)`, i.e. is
Cauchy, so the sequence converges a.e.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Assembly

/-- The set of points at which the sequence `u` has infinitely many oscillations of size `η`:
for every `N` there are indices `N ≤ i < j` with `|u j - u i| > η`. -/
private def OscSet {X : Type*} (u : ℕ → X → ℝ) (η : ℝ) : Set X :=
  {x | ∀ N : ℕ, ∃ i j : ℕ, N ≤ i ∧ i < j ∧ ENNReal.ofReal η < ‖u j x - u i x‖ₑ}

/-- The `n`-th "capture set" of the block structure anchored at `t`: the points where some
index of `[t, n)` already differs from the anchor by at least `η/2`. -/
private def BlockOsc {X : Type*} (u : ℕ → X → ℝ) (η : ℝ) (t n : ℕ) : Set X :=
  ⋃ i ∈ Finset.Ico t n, {x | ENNReal.ofReal (η / 2) ≤ ‖u i x - u t x‖ₑ}

private lemma blockOsc_mono {X : Type*} (u : ℕ → X → ℝ) (η : ℝ) (t : ℕ) :
    Monotone (BlockOsc u η t) := by
  intro n n' hnn' x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp hx
  refine Set.mem_iUnion₂.mpr ⟨i, ?_, hix⟩
  rw [Finset.mem_Ico] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 hnn'⟩

private lemma blockOsc_eq_empty_of_le {X : Type*} (u : ℕ → X → ℝ) (η : ℝ) {t n : ℕ}
    (h : n ≤ t) : BlockOsc u η t n = ∅ := by
  rw [BlockOsc, Finset.Ico_eq_empty (not_lt.mpr h)]
  simp

private lemma oscSet_subset_blockOsc_union {X : Type*} (u : ℕ → X → ℝ) {η : ℝ} (hη : 0 < η)
    (t : ℕ) : OscSet u η ⊆ ⋃ n, BlockOsc u η t n := by
  intro x hx
  obtain ⟨i, j, hti, hij, hbig⟩ := hx t
  by_cases h : ENNReal.ofReal (η / 2) ≤ ‖u j x - u t x‖ₑ
  · exact Set.mem_iUnion.mpr ⟨j + 1, Set.mem_iUnion₂.mpr ⟨j, by rw [Finset.mem_Ico]; omega, h⟩⟩
  · have h2 : ENNReal.ofReal (η / 2) ≤ ‖u i x - u t x‖ₑ := by
      by_contra hcon
      have hj : |u j x - u t x| < η / 2 := by
        have hh := not_le.mp h
        rw [Real.enorm_eq_ofReal_abs] at hh
        rwa [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < η / 2)] at hh
      have hi : |u t x - u i x| < η / 2 := by
        have hh := not_le.mp hcon
        rw [Real.enorm_eq_ofReal_abs] at hh
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < η / 2)] at hh
        rwa [abs_sub_comm] at hh
      have hji : η < |u j x - u i x| := by
        have hh := hbig
        rw [Real.enorm_eq_ofReal_abs] at hh
        exact (ENNReal.ofReal_lt_ofReal_iff').mp hh |>.1
      have h4 : |u j x - u i x| ≤ |u j x - u t x| + |u t x - u i x| := abs_sub_le _ _ _
      linarith
    exact Set.mem_iUnion.mpr ⟨j + 1, Set.mem_iUnion₂.mpr ⟨i, by rw [Finset.mem_Ico]; omega, h2⟩⟩

/-- The elementary arithmetic behind the contradiction: with `ε = a/(2 (C.toReal + 1))` the
`HasOsc` upper bound `ofReal (ε J) * C` is strictly smaller than `J * ofReal a`, for `J ≥ 1`
and `a > 0`. -/
private lemma ofReal_mul_lt_nat_mul {C : ℝ≥0∞} (hC : C < ⊤) {J : ℕ} (hJ : 1 ≤ J) {a : ℝ}
    (ha : 0 < a) :
    ENNReal.ofReal (a / (2 * (C.toReal + 1)) * J) * C < (J : ℝ≥0∞) * ENNReal.ofReal a := by
  have hCtop : C ≠ ⊤ := ne_of_lt hC
  have hc0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  have hlhs : (ENNReal.ofReal (a / (2 * (C.toReal + 1)) * (J : ℝ)) * C).toReal
      = a / (2 * (C.toReal + 1)) * (J : ℝ) * C.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hrhs : ((J : ℝ≥0∞) * ENNReal.ofReal a).toReal = (J : ℝ) * a := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (le_of_lt ha)]
  rw [hlhs, hrhs]
  have h2 : a / (2 * (C.toReal + 1)) * (J : ℝ) * C.toReal ≤ a / 2 * J := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (C.toReal + 1))]
    nlinarith [mul_pos ha hJpos, mul_nonneg (le_of_lt ha) hc0, mul_nonneg (le_of_lt hJpos) hc0,
      le_of_lt (mul_pos ha hJpos)]
  have h3 : a / 2 * (J : ℝ) < a * (J : ℝ) := by nlinarith
  linarith

/-- **Key lemma.**  If the oscillation inequality `HasOsc` holds with a finite constant, then
for every `η > 0` the set of points with infinitely many oscillations of size `η` is null. -/
private theorem measure_oscSet_eq_zero {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {u : ℕ → X → ℝ} {C : ENNReal} (hC : C < ⊤)
    (hmeas : ∀ i, Measurable (u i)) (hosc : HasOsc μ u C) {η : ℝ} (hη : 0 < η) :
    μ (OscSet u η) = 0 := by
  classical
  by_contra hne
  have hSpos : 0 < μ (OscSet u η) := pos_iff_ne_zero.mpr hne
  have hSlt : μ (OscSet u η) < ⊤ := measure_lt_top μ (OscSet u η)
  have hsRpos : 0 < (μ (OscSet u η)).toReal := ENNReal.toReal_pos hne (ne_of_lt hSlt)
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  have hSsub : ∀ t : ℕ, OscSet u η ⊆ ⋃ n, BlockOsc u η t n :=
    fun t => oscSet_subset_blockOsc_union u hη t
  -- the quantile choice of the next anchor
  have hex : ∀ t : ℕ, ∃ n : ℕ,
      ENNReal.ofReal ((μ (OscSet u η)).toReal / 2) ≤ μ (OscSet u η ∩ BlockOsc u η t n) := by
    intro t
    have hlim : Tendsto (fun n => μ (OscSet u η ∩ BlockOsc u η t n)) atTop
        (𝓝 (μ (OscSet u η))) := by
      have h0 := tendsto_measure_iUnion_atTop (μ := μ)
        (s := fun n => OscSet u η ∩ BlockOsc u η t n)
        (fun m n hmn => Set.inter_subset_inter_right _ (blockOsc_mono u η t hmn))
      have hunion : (⋃ n, OscSet u η ∩ BlockOsc u η t n) = OscSet u η := by
        exact Set.Subset.antisymm (Set.iUnion_subset (fun n => Set.inter_subset_left)) (fun x hx => by
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hSsub t hx)
          exact Set.mem_iUnion.mpr ⟨n, hx, hn⟩)
      rwa [hunion] at h0
    have hlt : ENNReal.ofReal ((μ (OscSet u η)).toReal / 2) < μ (OscSet u η) := by
      calc ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)
          < ENNReal.ofReal ((μ (OscSet u η)).toReal) :=
            (ENNReal.ofReal_lt_ofReal_iff hsRpos).mpr (by linarith)
        _ = μ (OscSet u η) := ENNReal.ofReal_toReal (ne_of_lt hSlt)
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hlt)).exists
    exact ⟨n, le_of_lt hn⟩
  let φ : ℕ → ℕ := fun t => Nat.find (hex t)
  have hφspec : ∀ t : ℕ, ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)
      ≤ μ (OscSet u η ∩ BlockOsc u η t (φ t)) := fun t => Nat.find_spec (hex t)
  have hφgt : ∀ t : ℕ, t < φ t := by
    intro t
    by_contra hle
    have hle' : φ t ≤ t := not_lt.mp hle
    have hemp : BlockOsc u η t (φ t) = ∅ := blockOsc_eq_empty_of_le u η hle'
    have h0 : μ (OscSet u η ∩ BlockOsc u η t (φ t)) = 0 := by
      rw [hemp, Set.inter_empty, measure_empty]
    have h1 := hφspec t
    rw [h0] at h1
    have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal ((μ (OscSet u η)).toReal / 2) :=
      ENNReal.ofReal_pos.mpr (by linarith)
    exact absurd h1 (not_le.mpr h2)
  let k : ℕ → ℕ := fun j => (φ^[j]) 0
  have hk_succ : ∀ j : ℕ, k (j + 1) = φ (k j) := fun j => Function.iterate_succ_apply' φ j 0
  have hk_mono : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hk_succ]
    exact hφgt (k n)
  -- each block captures at least half of `S`, giving a linear lower bound
  have hterm : ∀ j : ℕ, ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)
      ≤ ∫⁻ x, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) ∂μ := by
    intro j
    have hA : ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)
        ≤ μ (OscSet u η ∩ BlockOsc u η (k j) (k (j + 1))) := by
      have h := hφspec (k j)
      simpa only [hk_succ j] using h
    have hmg : Measurable (fun x : X =>
        (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ)) :=
      (Measurable.iSup (fun i => Measurable.iSup_Prop (i ∈ Finset.Ico (k j) (k (j + 1)))
        (((hmeas i).sub (hmeas (k j))).enorm))).pow measurable_const
    have hpt : ∀ x ∈ OscSet u η ∩ BlockOsc u η (k j) (k (j + 1)),
        ENNReal.ofReal ((η / 2) ^ 2)
          ≤ (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) := by
      intro x hx
      obtain ⟨i, hi, hile⟩ := Set.mem_iUnion₂.mp hx.2
      have hsup : ‖u i x - u (k j) x‖ₑ
          ≤ ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ :=
        le_iSup₂ (f := fun i (_ : i ∈ Finset.Ico (k j) (k (j + 1))) => ‖u i x - u (k j) x‖ₑ) i hi
      have h1 : ENNReal.ofReal ((η / 2) ^ 2) = (ENNReal.ofReal (η / 2)) ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ η / 2)]
        exact (ENNReal.rpow_two _).symm
      rw [h1]
      exact ENNReal.rpow_le_rpow (le_trans hile hsup) (by norm_num)
    calc ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)
        ≤ ENNReal.ofReal ((η / 2) ^ 2) * μ (OscSet u η ∩ BlockOsc u η (k j) (k (j + 1))) :=
          (mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((η / 2) ^ 2)))
      _ = ∫⁻ x in (OscSet u η ∩ BlockOsc u η (k j) (k (j + 1))),
            ENNReal.ofReal ((η / 2) ^ 2) ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in (OscSet u η ∩ BlockOsc u η (k j) (k (j + 1))),
            (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) ∂μ :=
          setLIntegral_mono hmg hpt
      _ ≤ ∫⁻ x, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) ∂μ :=
          setLIntegral_le_lintegral _ _
  have hεpos : 0 < ((η / 2) ^ 2 * ((μ (OscSet u η)).toReal / 2)) / (2 * (C.toReal + 1)) := by
    positivity
  obtain ⟨J₀, hJ₀⟩ := hosc (((η / 2) ^ 2 * ((μ (OscSet u η)).toReal / 2)) / (2 * (C.toReal + 1)))
    hεpos
  have hJge : J₀ ≤ max J₀ 1 := le_max_left _ _
  have hJ1 : 1 ≤ max J₀ 1 := le_max_right _ _
  have hupper := hJ₀ (max J₀ 1) hJge k hk_mono
  have hlower : ((max J₀ 1 : ℕ) : ℝ≥0∞)
      * (ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2))
      ≤ ∑ j ∈ Finset.range (max J₀ 1),
          ∫⁻ x, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖u i x - u (k j) x‖ₑ) ^ (2 : ℝ) ∂μ := by
    have h1 : ((max J₀ 1 : ℕ) : ℝ≥0∞)
        * (ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2))
        = ∑ _j ∈ Finset.range (max J₀ 1),
            ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have harith : ENNReal.ofReal (((η / 2) ^ 2 * ((μ (OscSet u η)).toReal / 2))
        / (2 * (C.toReal + 1)) * (max J₀ 1 : ℕ)) * C
      < ((max J₀ 1 : ℕ) : ℝ≥0∞)
        * (ENNReal.ofReal ((η / 2) ^ 2) * ENNReal.ofReal ((μ (OscSet u η)).toReal / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (η / 2) ^ 2)]
    exact ofReal_mul_lt_nat_mul hC hJ1 (by positivity)
  exact absurd (lt_of_le_of_lt (le_trans hlower hupper) harith) (lt_irrefl _)

/-- The oscillation inequality `HasOsc` (finitely many blocks, error `o(J)`, uniformly over
every strictly increasing block structure) forces almost everywhere convergence of the
sequence. -/
theorem lacunary_ae_of_osc {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {u : ℕ → X → ℝ} {C : ENNReal} (hC : C < ⊤)
    (hmeas : ∀ i, Measurable (u i)) (hosc : HasOsc μ u C) : LacConv μ u := by
  classical
  have hnull : ∀ m : ℕ, μ (OscSet u (1 / ((m : ℝ) + 1))) = 0 := fun m =>
    measure_oscSet_eq_zero hC hmeas hosc (by positivity)
  have hnullU : μ (⋃ m : ℕ, OscSet u (1 / ((m : ℝ) + 1))) = 0 := measure_iUnion_null hnull
  have hgood : ∀ x : X, x ∉ ⋃ m : ℕ, OscSet u (1 / ((m : ℝ) + 1)) →
      ∃ L : ℝ, Tendsto (fun i => u i x) atTop (nhds L) := by
    intro x hx
    have hclose : ∀ m : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
        |u i x - u j x| ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      have hxm : x ∉ OscSet u (1 / ((m : ℝ) + 1)) := fun h => hx (Set.mem_iUnion.mpr ⟨m, h⟩)
      simp only [OscSet, Set.mem_ofPred_eq] at hxm
      push Not at hxm
      obtain ⟨N, hN⟩ := hxm
      refine ⟨N, fun i j hi hj => ?_⟩
      have key : ∀ a b : ℕ, N ≤ a → a < b → |u b x - u a x| ≤ 1 / ((m : ℝ) + 1) := by
        intro a b ha hab
        have hh := hN a b ha hab
        rw [Real.enorm_eq_ofReal_abs] at hh
        rwa [ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1))] at hh
      rcases lt_trichotomy i j with hlt | heq | hgt
      · rw [abs_sub_comm]; exact key i j hi hlt
      · rw [heq, sub_self, abs_zero]; positivity
      · exact key j i hj hgt
    obtain ⟨L, hL⟩ := tendsto_of_eventually_close (fun i => u i x) hclose
    exact ⟨L, hL⟩
  refine ⟨fun x : X =>
    if h : (∃ L : ℝ, Tendsto (fun i => u i x) atTop (nhds L)) then h.choose else 0, ?_⟩
  rw [ae_iff]
  apply measure_mono_null _ hnullU
  intro x hbad
  by_contra hx
  have hg := hgood x hx
  refine hbad ?_
  simp only [dif_pos hg]
  exact hg.choose_spec

end Work.BourgainPlan.Assembly
