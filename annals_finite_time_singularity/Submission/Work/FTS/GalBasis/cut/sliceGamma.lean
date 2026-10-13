/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `γ`-weighted slice Hardy inequality `Work.FTS.GalBasis.cut.sliceGamma`

For `γ > 1` there is a universal constant `C` with

  `∫_0^{π/2} G² sin(2θ)^{-γ} ≤ C ∫_0^{π/2} (G')² sin(2θ)^{2-γ}`

for every `G` of class `C¹` on `(0, π/2)` whose `(1-γ)`-trace `sin(2θ)^{1-γ}·G²` vanishes
at both endpoints (as a *limit*, which is what makes the inequality true: with endpoint
*values* only, `G = 1` near `0` with the values patched to `0` is a counterexample) and whose
two weighted integrals are integrable.

## The proof (completion of squares)

Write `s = sin 2θ`, `c = cos 2θ`, and put `β = γ - 1 > 0`, `b = β/2 > 0`,

  `Φ(θ) = -2b·c/s`,   `A(θ) = Φ(θ)·s^{2-γ} = -2b·c·s^{1-γ}`,   `w = s^{2-γ}`,  `w₀ = s^{-γ}`.

Since `s² + c² = 1` and `β - b = b` (`b = β/2`),

  `A' = Φ·A + (4b s² + 4b²c²)·w₀ ≥ Φ·A + 4·min(b, b²)·w₀`     on `(0, π/2)`.

Integrating the pointwise identity `G'²w = (G' + GΦ)²w + G²(A' - ΦA) - (G²A)'` over
`[α, β] ⊂ (0, π/2)` (fundamental theorem of calculus for the flux `A·G²`) drops the square
term and yields

  `4·min(b, b²) · ∫_α^β G²w₀ ≤ ∫_α^β (G')²w + [A·G²]_α^β`,

which is `sliceGamma_core` (module `Submission.Work.FTS.GalBasis.cut.SliceGammaCore`) for
`b = (γ-1)/2`.  The boundary terms tend to `0` as `α ↓ 0`, `β ↑ π/2` by the two trace
hypotheses, and the `∫⁻` form of the estimate (monotone convergence along the cover
`Icc α_n β_n ↑ (0, π/2)`, with all integrands non-negative so that the junk conventions are
neutralised) gives the claim with `C = 1/(4·min(b, b²))`.

The vocabulary (`sgS`, `sgW`, `sgA`, …) is in the module
`Submission.Work.FTS.GalBasis.cut.SliceGammaDefs`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cut.SliceGammaDefs
import Submission.Work.FTS.GalBasis.cut.SliceGammaCore
import Submission.Work.FTS.GalBasis.cut.sliceGammaMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The measure-theoretic helpers -/

/-- The `∫⁻` of `volume.restrict (Icc 0 (π/2))` and of `volume.restrict (Ioo 0 (π/2))` agree,
the two sets differing by the null set `{0, π/2}`. -/
private theorem lintegral_Icc_eq_lintegral_Ioo (g : ℝ → ENNReal) :
    ∫⁻ θ in Set.Icc 0 (Real.pi / 2), g θ = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), g θ := by
  have hnull1 : volume (Set.Icc (0 : ℝ) (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2)) = 0 := by
    refine measure_mono_null ?_
      (((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)).measure_zero volume)
    intro θ hθ
    rw [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, not_and_or] at hθ
    obtain ⟨⟨h0, h2⟩, h | h⟩ := hθ
    · exact Or.inl (le_antisymm (not_lt.mp h) h0)
    · exact Or.inr (le_antisymm h2 (not_lt.mp h))
  have hnull2 : volume (Set.Ioo (0 : ℝ) (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2)) = 0 := by
    have hemp : Set.Ioo (0 : ℝ) (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_sdiff, Set.mem_Ioo, Set.mem_Icc] at hx
      exact hx.2 ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩
    rw [hemp, measure_empty]
  have hset : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    MeasureTheory.ae_eq_set.mpr ⟨hnull1, hnull2⟩
  rw [Measure.restrict_congr_set hset]

/-- The limiting argument: if the `∫⁻` of `ofReal f` over the increasing cover
`[1/(n+1), π/2 - 1/(n+1)] ↑ (0, π/2)` is bounded by a constant `B` plus an error term
`ofReal (c n)` with `c n → 0`, then the `∫⁻` over `Icc 0 (π/2)` is bounded by `B`. -/
private theorem sgLim_aux {f : ℝ → ℝ} {C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds 0))
    (h : ∀ n : ℕ, ∫⁻ θ in Set.Icc (1 / ((n : ℝ) + 1)) (Real.pi / 2 - 1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (f θ) ≤ ENNReal.ofReal C * ENNReal.ofReal K + ENNReal.ofReal (c n)) :
    ∫⁻ θ in Set.Icc 0 (Real.pi / 2), ENNReal.ofReal (f θ)
      ≤ ENNReal.ofReal C * ENNReal.ofReal K := by
  set g : ℝ → ENNReal := fun θ => ENNReal.ofReal (f θ) with hg
  set s : ℕ → Set ℝ := fun n => Set.Icc (1 / ((n : ℝ) + 1)) (Real.pi / 2 - 1 / ((n : ℝ) + 1))
    with hs
  have hmono : Monotone s := by
    intro n m hnm
    intro x hx
    simp only [hs, Set.mem_Icc] at hx ⊢
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hnm'
    constructor <;> linarith [hx.1, hx.2, hle]
  have hcover : (⋃ n, s n) = Set.Ioo 0 (Real.pi / 2) := by
    ext θ
    constructor
    · intro hθ
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hθ
      simp only [hs, Set.mem_Icc] at hn
      have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith [hn.1, h1], by linarith [hn.2, h1]⟩
    · intro hθ
      obtain ⟨hθ0, hθ1⟩ := hθ
      obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (show (0 : ℝ) < θ by linarith)
      obtain ⟨n2, hn2⟩ := exists_nat_one_div_lt (show (0 : ℝ) < Real.pi / 2 - θ by linarith)
      have hn1' : 1 / ((n1 : ℝ) + 1) < θ := by simpa only [Nat.cast_add, Nat.cast_one] using hn1
      have hn2' : 1 / ((n2 : ℝ) + 1) < Real.pi / 2 - θ := by
        simpa only [Nat.cast_add, Nat.cast_one] using hn2
      refine Set.mem_iUnion.mpr ⟨max n1 n2, ?_⟩
      simp only [hs, Set.mem_Icc]
      have hle1 : 1 / (((max n1 n2 : ℕ) : ℝ) + 1) ≤ 1 / ((n1 : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : (n1 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast le_max_left n1 n2
        linarith
      have hle2 : 1 / (((max n1 n2 : ℕ) : ℝ) + 1) ≤ 1 / ((n2 : ℝ) + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : (n2 : ℝ) ≤ ((max n1 n2 : ℕ) : ℝ) := by exact_mod_cast le_max_right n1 n2
        linarith
      exact ⟨le_of_lt (lt_of_le_of_lt hle1 hn1'),
        le_of_lt (by linarith [lt_of_le_of_lt hle2 hn2'])⟩
  have hlin : ∫⁻ θ in (⋃ n, s n), g θ = ⨆ n, ∫⁻ θ in s n, g θ :=
    setLIntegral_iUnion_of_directed g hmono.directed_le
  have hIcc : ∫⁻ θ in Set.Icc 0 (Real.pi / 2), g θ = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), g θ :=
    lintegral_Icc_eq_lintegral_Ioo g
  rw [hIcc, ← hcover, hlin]
  refine iSup_le (fun n => ?_)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hc.eventually (isOpen_Iio.mem_nhds hεR))
  have hNm : c (max n N) < (ε : ℝ) := hN (max n N) (le_max_right n N)
  have hnm : s n ⊆ s (max n N) := hmono (le_max_left n N)
  have hstep : (∫⁻ θ in s n, g θ) ≤ ∫⁻ θ in s (max n N), g θ := lintegral_mono_set hnm
  have hstep2 : (∫⁻ θ in s (max n N), g θ)
      ≤ ENNReal.ofReal C * ENNReal.ofReal K + ENNReal.ofReal (c (max n N)) := by
    simpa only [hs] using h (max n N)
  have hstep3 : ENNReal.ofReal (c (max n N)) ≤ (↑ε : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := ε)]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hNm)
  calc (∫⁻ θ in s n, g θ) ≤ ∫⁻ θ in s (max n N), g θ := hstep
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal K + ENNReal.ofReal (c (max n N)) := hstep2
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal K + ↑ε := add_le_add le_rfl hstep3

/-- Almost-everywhere strong measurability of the two weighted integrands. -/
private theorem sgMeas_aux {γ : ℝ} {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (sgF γ G) (volume.restrict (Set.Icc 0 (Real.pi / 2))) ∧
    AEStronglyMeasurable (sgD γ G) (volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  obtain ⟨h1, h2⟩ := sliceGammaMeas (γ := γ) (G := G) hG
  refine ⟨?_, ?_⟩
  · change AEStronglyMeasurable (fun θ => (G θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      (volume.restrict (Set.Icc 0 (Real.pi / 2)))
    exact h1
  · change AEStronglyMeasurable (fun θ => (deriv G θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      (volume.restrict (Set.Icc 0 (Real.pi / 2)))
    exact h2

private theorem ofReal_intervalIntegral_eq_lintegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfint : IntegrableOn f (Set.Icc a b)) (hfnn : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint
    ((ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall (fun x hx => hfnn x hx)))

private theorem sgF_continuousOn {γ : ℝ} {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) : ContinuousOn (sgF γ G) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx =>
    ⟨by linarith [hx.1, ha], by linarith [hx.2, hb, Real.pi_pos]⟩
  have hGs : ContinuousOn G (Set.Icc a b) := hG.continuousOn.mono hsub
  have hsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Icc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsne : ∀ x ∈ Set.Icc a b, Real.sin (2 * x) ≠ 0 := fun x hx => by
    have h : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1])
      (by linarith [h.2, Real.pi_pos]))
  have hw0 : ContinuousOn (sgW0 γ) (Set.Icc a b) := by
    unfold sgW0
    exact hsin.rpow_const (fun x hx => Or.inl (hsne x hx))
  unfold sgF
  exact (hGs.pow 2).mul hw0

/-! ## The main theorem -/

theorem sliceGamma {γ : ℝ} (hγ : 1 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Set.Ioo 0 (π / 2)) →
      Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - γ) * (G θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - γ) * (G θ) ^ 2)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ => (deriv G θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        (Set.Icc 0 (π / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (G θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        (Set.Icc 0 (π / 2)) ∧
      (∫ θ in Set.Icc 0 (π / 2), (G θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        ≤ C * (∫ θ in Set.Icc 0 (π / 2),
            (deriv G θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  set b : ℝ := (γ - 1) / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hbγ : 0 < γ - 1 - b := by rw [hbdef]; linarith
  have hκ : 0 < 4 * min b (b * (γ - 1 - b)) := by
    have h1 : 0 < b * (γ - 1 - b) := mul_pos hb hbγ
    have h2 : 0 < min b (b * (γ - 1 - b)) := lt_min hb h1
    linarith
  have hCpos : 0 < 1 / (4 * min b (b * (γ - 1 - b))) := one_div_pos.mpr hκ
  refine ⟨1 / (4 * min b (b * (γ - 1 - b))), hCpos, ?_⟩
  intro G hG ht0 htπ hintg
  have hintg' : IntegrableOn (sgD γ G) (Set.Icc 0 (Real.pi / 2)) := by
    unfold sgD sgW
    exact hintg
  have ht0' : Tendsto (sgE γ G) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := ht0
  have htπ' : Tendsto (sgE γ G) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    htπ
  -- the interval estimate
  have hcore : ∀ α β : ℝ, 0 < α → α ≤ β → β < Real.pi / 2 →
      (4 * min b (b * (γ - 1 - b))) * (∫ θ in α..β, sgF γ G θ)
        ≤ (∫ θ in α..β, sgD γ G θ) + sgCfun γ b G β - sgCfun γ b G α :=
    fun _ _ hα hαβ hβ => sliceGamma_core hb hbγ hG hα hαβ hβ
  -- the reference quantity
  set K : ℝ := ∫ θ in Set.Icc 0 (Real.pi / 2), sgD γ G θ with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sgW_nonneg_of_Icc hθ))
  -- the boundary terms tend to zero
  have hfun_eq : ∀ θ : ℝ, sgCfun γ b G θ = (-2 * b * Real.cos (2 * θ)) * sgE γ G θ := by
    intro θ
    unfold sgCfun sgA sgE
    ring
  have hcos_tend0 : Tendsto (fun θ : ℝ => -2 * b * Real.cos (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-2 * b)) := by
    have hc : ContinuousAt (fun θ : ℝ => -2 * b * Real.cos (2 * θ)) 0 := by fun_prop
    have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
    have h := hc.tendsto.mono_left hle
    simpa using h
  have hcos_tendπ : Tendsto (fun θ : ℝ => -2 * b * Real.cos (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (2 * b)) := by
    have hc : ContinuousAt (fun θ : ℝ => -2 * b * Real.cos (2 * θ)) (Real.pi / 2) := by
      fun_prop
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2) :=
      nhdsWithin_le_nhds
    have h := hc.tendsto.mono_left hle
    have hcos : Real.cos (2 * (Real.pi / 2)) = -1 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]
    simpa [hcos] using h
  have hAlpha_tend : Tendsto sgAlpha atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [sgAlpha, Set.mem_Ioi]; positivity)
  have hBeta_tend : Tendsto sgBeta atTop (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · change Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 1)) atTop (nhds (Real.pi / 2))
      have h : Tendsto (fun _ : ℕ => Real.pi / 2) atTop (nhds (Real.pi / 2)) :=
        tendsto_const_nhds
      have h2 := h.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa only [sub_zero] using h2
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [sgBeta, Set.mem_Iio]
        have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
  have hlimBeta : Tendsto (fun n => sgCfun γ b G (sgBeta n)) atTop (nhds 0) := by
    have hfun : (fun n => sgCfun γ b G (sgBeta n))
        = fun n => (-2 * b * Real.cos (2 * sgBeta n)) * sgE γ G (sgBeta n) :=
      funext fun n => hfun_eq (sgBeta n)
    rw [hfun]
    simpa only [Function.comp_def, mul_zero] using (hcos_tendπ.mul htπ').comp hBeta_tend
  have hlimAlpha : Tendsto (fun n => sgCfun γ b G (sgAlpha n)) atTop (nhds 0) := by
    have hfun : (fun n => sgCfun γ b G (sgAlpha n))
        = fun n => (-2 * b * Real.cos (2 * sgAlpha n)) * sgE γ G (sgAlpha n) :=
      funext fun n => hfun_eq (sgAlpha n)
    rw [hfun]
    simpa only [Function.comp_def, mul_zero] using (hcos_tend0.mul ht0').comp hAlpha_tend
  have hFlux_tend : Tendsto (sgFlux γ b G) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => |sgA γ b (sgBeta n) * (G (sgBeta n)) ^ 2|) atTop (nhds 0) := by
      simpa only [sgCfun, abs_zero] using hlimBeta.abs
    have h2 : Tendsto (fun n => |sgA γ b (sgAlpha n) * (G (sgAlpha n)) ^ 2|) atTop (nhds 0) := by
      simpa only [sgCfun, abs_zero] using hlimAlpha.abs
    unfold sgFlux
    simpa using h1.add h2
  -- the truncated `∫⁻` bound
  have hbound : ∀ n : ℕ,
      ∫⁻ θ in Set.Icc (sgAlpha n) (sgBeta n), ENNReal.ofReal (sgF γ G θ)
        ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b))))
          * ENNReal.ofReal (K + sgFlux γ b G n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hempty : Set.Icc (sgAlpha 0) (sgBeta 0) = (∅ : Set ℝ) := by
        refine Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
        simp only [Set.mem_Icc, sgAlpha, sgBeta] at hx
        norm_num at hx
        linarith [Real.pi_lt_four]
      rw [hempty, MeasureTheory.setLIntegral_empty]
      positivity
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hαn : 0 < sgAlpha n := by simp only [sgAlpha]; positivity
      have hβn : sgBeta n < Real.pi / 2 := by
        simp only [sgBeta]
        have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hαβn : sgAlpha n ≤ sgBeta n := by
        simp only [sgAlpha, sgBeta]
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hn2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          linarith
        have hπ : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
        have h2 : 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) ≤ Real.pi / 2 := by
          have := hpos
          field_simp
          nlinarith [hn2, hπ]
        linarith
      have hintF : IntegrableOn (sgF γ G) (Set.Icc (sgAlpha n) (sgBeta n)) :=
        ContinuousOn.integrableOn_compact isCompact_Icc (sgF_continuousOn hG hαn hβn)
      have hFnn : ∀ x ∈ Set.Icc (sgAlpha n) (sgBeta n), 0 ≤ sgF γ G x := by
        intro x hx
        have hxO : x ∈ Set.Ioo 0 (Real.pi / 2) :=
          ⟨by linarith [hx.1, hαn], by linarith [hx.2, hβn]⟩
        unfold sgF
        exact mul_nonneg (sq_nonneg _) (le_of_lt (sgW0_pos hxO))
      -- the derivative-weight mass is bounded by `K`
      have hDY : (∫ θ in sgAlpha n..sgBeta n, sgD γ G θ) ≤ K := by
        rw [hK, intervalIntegral.integral_of_le hαβn]
        refine MeasureTheory.setIntegral_mono_set hintg' ?_ ?_
        · refine (ae_restrict_iff' measurableSet_Icc).mpr
            (Filter.Eventually.of_forall (fun θ hθ => ?_))
          exact mul_nonneg (sq_nonneg _) (sgW_nonneg_of_Icc hθ)
        · exact Filter.Eventually.of_forall (fun θ hθ =>
            ⟨by linarith [hαn, hθ.1], by linarith [hβn, hθ.2]⟩)
      -- the interval estimate with the flux bounded by `sgFlux`
      have hstep : (4 * min b (b * (γ - 1 - b))) * (∫ θ in sgAlpha n..sgBeta n, sgF γ G θ)
          ≤ K + sgFlux γ b G n := by
        have hc := hcore (sgAlpha n) (sgBeta n) hαn hαβn hβn
        have hflux : sgCfun γ b G (sgBeta n) - sgCfun γ b G (sgAlpha n) ≤ sgFlux γ b G n := by
          unfold sgCfun sgFlux
          have h1 := le_abs_self (sgA γ b (sgBeta n) * (G (sgBeta n)) ^ 2)
          have h2 := neg_le_abs (sgA γ b (sgAlpha n) * (G (sgAlpha n)) ^ 2)
          linarith
        linarith
      have hXY : (∫ θ in sgAlpha n..sgBeta n, sgF γ G θ)
          ≤ 1 / (4 * min b (b * (γ - 1 - b))) * (K + sgFlux γ b G n) := by
        have hd : (K + sgFlux γ b G n) / (4 * min b (b * (γ - 1 - b)))
            = 1 / (4 * min b (b * (γ - 1 - b))) * (K + sgFlux γ b G n) := by ring
        rw [← hd]
        exact (le_div_iff₀ hκ).mpr (by rw [mul_comm]; exact hstep)
      calc ∫⁻ θ in Set.Icc (sgAlpha n) (sgBeta n), ENNReal.ofReal (sgF γ G θ)
          = ENNReal.ofReal (∫ θ in sgAlpha n..sgBeta n, sgF γ G θ) :=
            (ofReal_intervalIntegral_eq_lintegral hαβn hintF hFnn).symm
        _ ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b))) * (K + sgFlux γ b G n)) :=
            ENNReal.ofReal_le_ofReal hXY
        _ = ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b))))
              * ENNReal.ofReal (K + sgFlux γ b G n) :=
            ENNReal.ofReal_mul (le_of_lt hCpos)
  -- the limit
  have hctend : Tendsto (fun n => (1 / (4 * min b (b * (γ - 1 - b)))) * sgFlux γ b G n)
      atTop (nhds 0) := by
    have h := hFlux_tend.const_mul (1 / (4 * min b (b * (γ - 1 - b))))
    simpa using h
  have hbound' : ∀ n : ℕ,
      ∫⁻ θ in Set.Icc (sgAlpha n) (sgBeta n), ENNReal.ofReal (sgF γ G θ)
        ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b)))) * ENNReal.ofReal K
          + ENNReal.ofReal ((1 / (4 * min b (b * (γ - 1 - b)))) * sgFlux γ b G n) := by
    intro n
    calc ∫⁻ θ in Set.Icc (sgAlpha n) (sgBeta n), ENNReal.ofReal (sgF γ G θ)
        ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b))))
            * ENNReal.ofReal (K + sgFlux γ b G n) := hbound n
      _ ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b))))
            * (ENNReal.ofReal K + ENNReal.ofReal (sgFlux γ b G n)) :=
          mul_le_mul_right ENNReal.ofReal_add_le _
      _ = ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b)))) * ENNReal.ofReal K
            + ENNReal.ofReal ((1 / (4 * min b (b * (γ - 1 - b)))) * sgFlux γ b G n) := by
          rw [mul_add]
          congr 1
          exact (ENNReal.ofReal_mul (le_of_lt hCpos)).symm
  have hfin : ∫⁻ θ in Set.Icc 0 (Real.pi / 2), ENNReal.ofReal (sgF γ G θ)
      ≤ ENNReal.ofReal (1 / (4 * min b (b * (γ - 1 - b)))) * ENNReal.ofReal K :=
    sgLim_aux hCpos hKnn hctend
      (fun n => by simpa only [sgAlpha, sgBeta] using hbound' n)
  -- measurability
  obtain ⟨hmeasF, _hmeasD⟩ := sgMeas_aux hG
  have hFnn_ae : 0 ≤ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] sgF γ G :=
    (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (sgW0_nonneg_of_Icc hθ)))
  -- integrability of the function-weight mass
  have hFint : IntegrableOn (sgF γ G) (Set.Icc 0 (Real.pi / 2)) := by
    refine ⟨hmeasF, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hFnn_ae]
    exact lt_of_le_of_lt hfin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- the final comparison
  have hFle : (∫ θ in Set.Icc 0 (Real.pi / 2), sgF γ G θ)
      ≤ 1 / (4 * min b (b * (γ - 1 - b))) * K := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hFnn_ae hmeasF]
    refine le_trans (ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne hfin) ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hCpos), ENNReal.toReal_ofReal hKnn]
  refine ⟨?_, ?_⟩
  · unfold sgF sgW0 at hFint
    exact hFint
  · refine le_trans hFle (le_of_eq ?_)
    rw [hK]
    unfold sgD sgW
    rfl

end Work.FTS.GalBasis.cut
