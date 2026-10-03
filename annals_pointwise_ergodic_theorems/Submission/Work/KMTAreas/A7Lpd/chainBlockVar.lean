/-
# The single-chain block square function of the low-pass Ionescu--Wainger family

This module isolates, in a precise and *provable* form, the difference between

* the bound **for each chain** of the `ℓ²`-square function of the jumps of the low-pass family
  `T m = kmtProj ρ l (-(m₀+m))`, and
* the bound for the **supremum over chains** (`Work.KMTAreas.A7MixedG.chainLe` /
  `Work.KMTAreas.A7Hi.LowpassChainLe`, the crux of `Work.KMTAreas.A7.LowpassVarDyadic`).

The jumps of a chain `N` are `T (N (i+1)) f - T (N i) f = ∑_{n ∈ [N i, N (i+1))} Δ n f`
(`Δ n = T (n+1) - T n`), i.e. the *block sums* of the annuli over the consecutive blocks
`[N i, N (i+1))`.  Those blocks are pairwise disjoint, so a signed sum of block sums **is** a
signed sum of annuli, and the PROVED uniform-in-signs bound
`Work.KMTAreas.A7G.annuliUniformSigns` (arbitrary finitely supported `U`, arbitrary signs,
`l`-free constant) applies verbatim.  Feeding it into the Khintchine linearisation
`Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin` gives

  `‖ (∑'_i ‖T (N (i+1)) f - T (N i) f‖²)^{1/2} ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}`

with a constant `C` **independent of the level `l`, of the base level `m₀` and of the chain `N`**.

Consequently the single-chain `ℓ^r`-sum (`2 ≤ r`) is bounded as well
(`ℓ^r ⊆ ℓ²` on the finitely many jumps).  What is *not* obtained, and what is the genuine
content of `chainLe`, is the **supremum over chains**: `eLpNorm` does not commute with an
uncountable `⨆`, and the exponent-`2` version of the sup-over-chains bound is the (false)
exponent-2 variation of the family (see `NOTES_A7_LowpassVarDyadic_SESSION5.md` §2).  The
lemmas below therefore pinpoint the remaining gap exactly: it is a Lépingle-type upgrading from a
*uniform-in-the-chain* bound to a bound for the *sup over chains*.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Lpd.bandSquareAll
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Lpd

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The consecutive block `[N i, N (i+1))` of the chain `N`. -/
private def chainBlock (N : ℕ → ℕ) (i : ℕ) : Finset ℕ := Finset.Ico (N i) (N (i + 1))

/-- The blocks of a monotone chain are pairwise disjoint half-open intervals. -/
private lemma chainBlock_disjoint (N : ℕ → ℕ) (hN : Monotone N) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (chainBlock N i) (chainBlock N j) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [chainBlock, Finset.mem_Ico] at hn hn'
  rcases lt_or_gt_of_ne hij with h | h
  · have h1 : N (i + 1) ≤ N j := hN (by omega)
    omega
  · have h1 : N (j + 1) ≤ N i := hN (by omega)
    omega

/-- The blocks of a monotone chain are pairwise disjoint, as a `PairwiseDisjoint` statement. -/
private lemma chainBlock_pairwiseDisjoint (N : ℕ → ℕ) (hN : Monotone N) (U : Finset ℕ) :
    (U : Set ℕ).PairwiseDisjoint (chainBlock N) :=
  fun i _ j _ hij => chainBlock_disjoint N hN hij

/-- **The single-chain block square function of the low-pass family is bounded in `ℓᵖ`.**

For every level `l`, base `m₀` with good major arcs, every `f : ℤ → ℂ`, every number of blocks `J`
and every monotone chain `N`, the `ℓ²`-square function of the (finitely many) jumps of the chain,
bounded by `C‖f‖_{ℓᵖ}` with `C` independent of `l, m₀, J, N`. -/
theorem singleChain_blockSqSum_le_of_uniformSigns (ρ : ℝ) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (Cρ : ℝ) (C : ℝ) (hCpos : 0 < C)
    (hAnn : ∀ (l m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n + 1 : ℕ) : ℤ))) g x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (n : ℤ))) g x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (l m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
        MeasureTheory.eLpNorm (fun x : ℤ => (∑' i : ℕ, if i < J then
            ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0)
            ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  -- the Khintchine linearisation
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨K, hKpos, hKhi⟩ := Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin p.toReal hp1
  have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hp0r : (0 : ℝ) < p.toReal := lt_trans zero_lt_one hp1
  refine ⟨(K * C ^ p.toReal) ^ (1 / p.toReal), Real.rpow_pos_of_pos
    (mul_pos hKpos (Real.rpow_pos_of_pos hCpos _)) _, ?_⟩
  intro l m₀ hgood f J N hN
  -- the block operators
  set T : ℕ → (ℤ → ℂ) → ℤ → ℂ := fun i g x =>
    if i < J then ∑ n ∈ chainBlock N i,
      (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x)
    else 0 with hTdef
  -- measurability
  have hmeas : ∀ (i : ℕ) (g : ℤ → ℂ), AEMeasurable (T i g) MeasureTheory.Measure.count :=
    fun i g => (measurable_of_countable _).aemeasurable
  -- the uniform-in-signs hypothesis for the block operators
  have hTbound : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      ∫⁻ x : ℤ, ‖∑ i ∈ U, (if ω i then (1 : ℂ) else -1) * T i g x‖ₑ ^ p.toReal
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ p.toReal) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count := by
    intro U ω g
    -- the union of the blocks of `U` inside `[0,J)`
    set U' : Finset ℕ := (U.filter (fun i => i < J)).biUnion (chainBlock N) with hU'def
    -- the merged sign pattern
    set ω' : ℕ → Bool := fun n =>
      if h : ∃ i ∈ U.filter (fun i => i < J), n ∈ chainBlock N i then ω (Classical.choose h)
      else false with hω'def
    -- the pointwise identity
    have hmerge : (fun x : ℤ => ∑ i ∈ U, (if ω i then (1 : ℂ) else -1) * T i g x)
        = fun x : ℤ => ∑ n ∈ U', (if ω' n then (1 : ℂ) else -1) *
            (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x) := by
      funext x
      rw [hTdef]
      -- remove the `i ≥ J` terms
      have hzero : ∀ i ∈ U, i ∉ U.filter (fun i => i < J) → (if ω i then (1 : ℂ) else -1) *
          (if i < J then (∑ n ∈ chainBlock N i,
            (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x))
           else 0) = 0 := by
        intro i hiU hiFil
        have hge : ¬ i < J := fun hlt => hiFil (Finset.mem_filter.mpr ⟨hiU, hlt⟩)
        rw [if_neg hge, mul_zero]
      rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
      -- now the sum is over `U.filter (· < J)`, whose terms are block sums
      have hstep : ∀ i ∈ U.filter (fun i => i < J), (if ω i then (1 : ℂ) else -1) *
          (∑ n ∈ chainBlock N i, (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x))
          = ∑ n ∈ chainBlock N i, (if ω i then (1 : ℂ) else -1) *
              (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x) := by
        intro i _
        rw [Finset.mul_sum]
      have hstep0 : ∀ i ∈ U.filter (fun i => i < J), (if ω i then (1 : ℂ) else -1) *
          (if i < J then (∑ n ∈ chainBlock N i, (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x)) else 0)
          = (if ω i then (1 : ℂ) else -1) *
            (∑ n ∈ chainBlock N i, (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x)) := by
        intro i hi
        rw [if_pos (Finset.mem_filter.mp hi).2]
      rw [Finset.sum_congr rfl hstep0]
      rw [Finset.sum_congr rfl hstep]
      -- merge the disjoint blocks
      rw [hU'def, Finset.sum_biUnion (chainBlock_pairwiseDisjoint N hN _)]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hiU : i ∈ U.filter (fun i => i < J) := hi
      have hex : ∃ i' ∈ U.filter (fun i' => i' < J), n ∈ chainBlock N i' := ⟨i, hiU, hn⟩
      have hchoice : Classical.choose hex = i := by
        by_contra hne
        have hspec := Classical.choose_spec hex
        exact (Finset.disjoint_left.mp (chainBlock_disjoint N hN hne) hspec.2) hn
      have hω'val : ω' n = ω i := by
        rw [hω'def]
        dsimp only
        rw [dif_pos hex, hchoice]
      rw [hω'val]
    -- the uniform-in-signs bound for the annuli, applied to the merged pattern
    have hbound := hAnn l m₀ hgood U' ω' g
    rw [← hpq] at hbound
    -- convert the `eLpNorm` bound into the `lintegral` form
    have hconv := Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow
      (fun x : ℤ => ∑ n ∈ U', (if ω' n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x)) hp0r
    have hconvf := Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g hp0r
    have hlg : (∫⁻ x : ℤ, ‖∑ i ∈ U, (if ω i then (1 : ℂ) else -1) * T i g x‖ₑ ^ p.toReal
          ∂MeasureTheory.Measure.count)
        = ∫⁻ x : ℤ, ‖∑ n ∈ U', (if ω' n then (1 : ℂ) else -1) *
            (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x
              - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x)‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count :=
      lintegral_congr (fun x => by rw [congrFun hmerge x])
    rw [hlg, hconv, hconvf]
    calc (MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U', (if ω' n then (1 : ℂ) else -1) *
            (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) g x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n g x))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) ^ p.toReal
        ≤ (ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count) ^ p.toReal :=
          ENNReal.rpow_le_rpow hbound hp0r.le
      _ = ENNReal.ofReal (C ^ p.toReal) *
            (MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count)
              ^ p.toReal := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0r.le,
            ENNReal.ofReal_rpow_of_nonneg hCpos.le hp0r.le]
  -- the Khintchine step
  have hK := hKhi T hmeas C hCpos.le hTbound f
  -- conversion to the `eLpNorm` of the real-valued square function
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  set z : ℕ → ℤ → ℂ := fun i x => if i < J then
      Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
        - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x else 0 with hzdef
  have hzeq : (fun x : ℤ => (∑' i : ℕ, if i < J then
        ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x‖ ^ (2 : ℝ) else 0) ^ (1 / 2 : ℝ))
      = fun x : ℤ => (∑' i : ℕ, ‖z i x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    funext x
    congr 1
    refine tsum_congr (fun i => ?_)
    by_cases hi : i < J
    · rw [hzdef]; simp only [hi, ↓reduceIte]
    · rw [hzdef]; simp only [hi, ↓reduceIte, norm_zero]
      exact (Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)).symm
  rw [hzeq]
  refine (eLpNorm_sqSum_le_eLpNorm_ennSqSum p hpne0 (ne_of_lt hptop) z).trans ?_
  have hsum : ∀ x : ℤ, (∑' i : ℕ, ‖z i x‖ₑ ^ (2 : ℝ))
      = ∑' i : ℕ, ‖T i f x‖ₑ ^ (2 : ℝ) := by
    intro x
    refine tsum_congr (fun i => ?_)
    by_cases hi : i < J
    · have htel : (∑ n ∈ chainBlock N i,
          (Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x))
          = Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
            - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x :=
        Finset.sum_Ico_sub (fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x) (hN (by omega))
      have hzi : z i x = Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x := by
        rw [hzdef]; simp only [hi, ↓reduceIte]
      have hTi : T i f x = Work.KMTAreas.A7Hi.lpf ρ l m₀ (N (i + 1)) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ (N i) f x := by
        rw [hTdef]; simp only [hi, ↓reduceIte]; exact htel
      rw [hzi, hTi]
    · have hzi : z i x = 0 := by rw [hzdef]; simp only [hi, ↓reduceIte]
      have hTi : T i f x = 0 := by rw [hTdef]; simp only [hi, ↓reduceIte]
      rw [hzi, hTi]
  have hL : MeasureTheory.eLpNorm (fun x : ℤ => (∑' i : ℕ, ‖z i x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        p MeasureTheory.Measure.count
      = (∫⁻ x : ℤ, (∑' i : ℕ, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (p.toReal / 2)
          ∂MeasureTheory.Measure.count) ^ (1 / p.toReal) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne0 (ne_of_lt hptop)]
    refine congrArg (fun u : ℝ≥0∞ => u ^ (1 / p.toReal)) ?_
    refine lintegral_congr (fun x => ?_)
    rw [enorm_eq_self, hsum x, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hR : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      = (∫⁻ x : ℤ, ‖f x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count) ^ (1 / p.toReal) :=
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne0 (ne_of_lt hptop)
  rw [hL, hR]
  calc (∫⁻ x : ℤ, (∑' i : ℕ, ‖T i f x‖ₑ ^ (2 : ℝ)) ^ (p.toReal / 2)
          ∂MeasureTheory.Measure.count) ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal (K * C ^ p.toReal) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hK (by positivity)
    _ = ENNReal.ofReal ((K * C ^ p.toReal) ^ (1 / p.toReal)) *
          (∫⁻ x : ℤ, ‖f x‖ₑ ^ p.toReal ∂MeasureTheory.Measure.count) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hKpos.le (Real.rpow_nonneg hCpos.le _))
            (by positivity)]

end

end Work.KMTAreas.A7Lpd
