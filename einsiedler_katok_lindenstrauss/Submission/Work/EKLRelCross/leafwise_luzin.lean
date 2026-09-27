import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.lusin_alt
import Submission.Work.EKLRelCross.cc_dense_family

/-!
# `Work.EKLRelCross.leafwise_luzin` — (U6): Luzin's theorem for a leafwise system

The frozen contract asks: for a leafwise system `(μ, U, ν, X')` and every `ε > 0` there is a
compact `K ⊆ X'` with `μ Kᶜ < ε` on which every function `x ↦ ∫ g, f g ∂(ν x)` (`f` compactly
supported continuous on `SL₃(ℝ)`) is continuous.

The only field of `IsLeafwise` that enters is measurability of the maps
`x ↦ ∫ g, f g ∂(ν x)`; the mass bound needed to pass from a *countable* dense family of test
functions to *all* test functions is obtained from the exhaustion of `SL₃(ℝ)` by compact sets
`L n` and the *levelly* bounded masses `ν x (L n) ≤ N n`, which can be imposed on a set of
almost full measure because `ν x` is finite on compacts on `X'`.

Two external inputs are used (both proved in sibling modules of this directory):

* `Work.EKLRelCross.lusin_compact` — Luzin's theorem, in the form needed here;
* `Work.EKLRelCross.cc_dense_family` — a countable, level-controlled sup-norm dense family of
  compactly supported functions on `SL₃(ℝ)`.

They are taken as explicit hypotheses of `leafwise_luzin_aux` below, so that this file can be
developed and checked independently of them; `leafwise_luzin` is then the immediate instance.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract
open Work.EKLContract.Lemmas

/-! ## Elementary facts about compactly supported functions -/

/-- A compactly supported continuous function on the (locally compact) group `SL₃(ℝ)` is
bounded. -/
lemma exists_abs_bound_cc (u : CompactlySupportedContinuousMap SL3 ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |u x| ≤ B := by
  obtain ⟨B, hB⟩ := (show IsCompact (tsupport (u : SL3 → ℝ) ) from u.hasCompactSupport)
    |>.exists_bound_of_continuousOn u.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (u : SL3 → ℝ)
  · calc |u x| = ‖u x‖ := (Real.norm_eq_abs _).symm
      _ ≤ B := hB x hx
      _ ≤ max B 0 := le_max_left _ _
  · have h0 : u x = 0 := by
      by_contra h
      exact hx (subset_tsupport (u : SL3 → ℝ) (by simpa [Function.mem_support] using h))
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- A function vanishing off a compact subset of an increasing open cover of `SL₃(ℝ)` vanishes
off one level of the cover. -/
lemma exists_level_superset {L : ℕ → Set SL3} (hmono : Monotone L)
    (hint : ∀ n, L n ⊆ interior (L (n+1))) (huniv : ⋃ n, L n = Set.univ)
    {A : Set SL3} (hA : IsCompact A) : ∃ n, A ⊆ L n := by
  have hcover : A ⊆ ⋃ n, interior (L n) := by
    intro x hx
    have hx' : x ∈ ⋃ n, L n := by rw [huniv]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx'
    exact mem_iUnion.mpr ⟨n+1, hint n hn⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun n => interior (L n)) (fun _ => isOpen_interior)
    hcover
  refine ⟨t.sup id, fun x hx => ?_⟩
  obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (ht hx)
  exact hmono (Finset.le_sup (f := id) hit) (interior_subset hxi)

/-! ## The main argument, with the two external inputs as hypotheses -/

theorem leafwise_luzin_aux (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hLuzin : ∀ (F : ℕ → X3 → ℝ), (∀ n, Measurable (F n)) → (B : Set X3) →
      MeasurableSet B → (∀ n, ∃ C : ℝ, ∀ x ∈ B, |F n x| ≤ C) → ∀ {δ : ℝ}, 0 < δ →
      ∃ K : Set X3, K ⊆ B ∧ IsCompact K ∧ μ (B \ K) < ENNReal.ofReal δ ∧
        ∀ n, ContinuousOn (F n) K)
    (hFam : ∃ (L : ℕ → Set SL3) (χ : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
        (Fam : ℕ → ℕ → CompactlySupportedContinuousMap SL3 ℝ),
        (∀ n, IsCompact (L n)) ∧ Monotone L ∧ (⋃ n, L n = Set.univ) ∧
        (∀ n, L n ⊆ interior (L (n+1))) ∧
        (∀ n x, x ∈ L n → χ n x = 1) ∧
        (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
        (∀ n, Function.support (χ n) ⊆ L (n+1)) ∧
        (∀ n j, Function.support (Fam n j) ⊆ L (n+1)) ∧
        (∀ (u : CompactlySupportedContinuousMap SL3 ℝ) (n : ℕ),
          Function.support u ⊆ L n → ∀ η > 0, ∃ j, ∀ x, |u x - Fam n j x| ≤ η)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X3, IsCompact K ∧ K ⊆ X' ∧ μ Kᶜ < ε ∧
        ∀ f : CompactlySupportedContinuousMap SL3 ℝ, ContinuousOn (fun x => ∫ g, f g ∂(ν x)) K := by
  obtain ⟨L, χ, Fam, hLcpt, hLmono, hLuniv, hLint, hχ1, hχ01, hχsupp, hFamsupp, hFamdens⟩ := hFam
  haveI : T2Space X3 := h2.1
  haveI : PolishSpace X3 := h2.2.1
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · subst htop
    refine ⟨∅, isCompact_empty, Set.empty_subset _, ?_, fun f => continuousOn_empty _⟩
    rw [Set.compl_empty, measure_univ]
    exact ENNReal.one_lt_top
  · set e : ℝ := ε.toReal with he
    have hepos : 0 < e := by
      rw [he]; exact ENNReal.toReal_pos_iff.mpr ⟨hε, lt_top_iff_ne_top.mpr htop⟩
    have hεof : ε = ENNReal.ofReal e := by rw [he]; exact (ENNReal.ofReal_toReal htop).symm
    -- per-level budgets
    set β : ℕ → ℝ := fun n => (e / 8) * ((1 / 2 : ℝ) ^ n) with hβ
    have hβpos : ∀ n, 0 < β n := by
      intro n
      exact mul_pos (by linarith) (pow_pos (by norm_num) n)
    -- the mass probes
    set Φ : ℕ → X3 → ℝ := fun n x => ∫ g, χ (n + 1) g ∂(ν x) with hΦ
    have hΦmeas : ∀ n, Measurable (Φ n) := fun n => by
      simpa only [hΦ] using hL.measurable (χ (n + 1))
    -- choose the mass bounds
    have hchoice : ∀ n : ℕ, ∃ M : ℕ,
        μ ((X' ∩ {x | Φ n x ≤ (M : ℝ)})ᶜ) < ENNReal.ofReal (β n) := by
      intro n
      have hSmeas : ∀ M : ℕ, MeasurableSet (X' ∩ {x | (M : ℝ) < Φ n x}) := fun M =>
        hL.meas_dom.inter (measurableSet_lt measurable_const (hΦmeas n))
      have hSanti : Antitone (fun M : ℕ => X' ∩ {x | (M : ℝ) < Φ n x}) := by
        intro M M' hMM' x hx
        refine ⟨hx.1, ?_⟩
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact lt_of_le_of_lt (by exact_mod_cast hMM') hx.2
      have hinter : (⋂ M : ℕ, (X' ∩ {x | (M : ℝ) < Φ n x})) = ∅ := by
        ext x
        constructor
        · intro hx
          exact absurd (mem_iInter.mp hx (⌈Φ n x⌉₊)).2 (not_lt.mpr (Nat.le_ceil (Φ n x)))
        · intro hx; exact hx.elim
      have hfin : ∃ M : ℕ, μ (X' ∩ {x | (M : ℝ) < Φ n x}) ≠ ⊤ := by
        refine ⟨0, ?_⟩
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        refine le_trans (measure_mono (Set.subset_univ _)) ?_
        rw [measure_univ]
      have htend : Tendsto (fun M : ℕ => μ (X' ∩ {x | (M : ℝ) < Φ n x})) atTop (𝓝 0) := by
        have h := tendsto_measure_iInter_atTop (μ := μ)
          (s := fun M : ℕ => X' ∩ {x | (M : ℝ) < Φ n x})
          (fun M => (hSmeas M).nullMeasurableSet) hSanti hfin
        simpa only [Function.comp_def, hinter, measure_empty] using h
      obtain ⟨M, hM⟩ :=
        (htend.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (hβpos n)))).exists
      refine ⟨M, ?_⟩
      have hsub : (X' ∩ {x | Φ n x ≤ (M : ℝ)})ᶜ ⊆ X'ᶜ ∪ (X' ∩ {x | (M : ℝ) < Φ n x}) := by
        intro x hx
        by_cases hx' : x ∈ X'
        · refine Or.inr ⟨hx', ?_⟩
          by_contra hle
          simp only [Set.mem_setOf_eq] at hle
          exact hx ⟨hx', not_lt.mp hle⟩
        · exact Or.inl hx'
      calc μ ((X' ∩ {x | Φ n x ≤ (M : ℝ)})ᶜ)
          ≤ μ (X'ᶜ ∪ (X' ∩ {x | (M : ℝ) < Φ n x})) := measure_mono hsub
        _ ≤ μ X'ᶜ + μ (X' ∩ {x | (M : ℝ) < Φ n x}) := measure_union_le _ _
        _ = μ (X' ∩ {x | (M : ℝ) < Φ n x}) := by rw [hL.conull, zero_add]
        _ < ENNReal.ofReal (β n) := hM
    choose M hM using hchoice
    set B : ℕ → Set X3 := fun n => X' ∩ {x | Φ n x ≤ (M n : ℝ)} with hB
    have hBmeas : ∀ n, MeasurableSet (B n) := fun n =>
      hL.meas_dom.inter (measurableSet_le (hΦmeas n) measurable_const)
    have hBcompl : ∀ n, μ ((B n)ᶜ) < ENNReal.ofReal (β n) := fun n => hM n
    -- the mass bound on the constraint sets
    have hmass : ∀ n, ∀ x ∈ B n, ν x (L (n + 1)) ≤ ENNReal.ofReal (M n) := by
      intro n x hx
      obtain ⟨hxX', hxle⟩ := hx
      haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
      have hpt : ∀ g : SL3, (L (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) g
          ≤ ENNReal.ofReal (χ (n + 1) g) := by
        intro g
        by_cases hg : g ∈ L (n + 1)
        · rw [Set.indicator_of_mem hg, hχ1 (n + 1) g hg]
          simp
        · rw [Set.indicator_of_notMem hg]
          simp
      calc ν x (L (n + 1))
          = ∫⁻ g, (L (n + 1)).indicator (fun _ => (1 : ℝ≥0∞)) g ∂(ν x) :=
            (lintegral_indicator_one (hLcpt (n + 1)).measurableSet).symm
        _ ≤ ∫⁻ g, ENNReal.ofReal (χ (n + 1) g) ∂(ν x) := lintegral_mono hpt
        _ = ENNReal.ofReal (∫ g, χ (n + 1) g ∂(ν x)) :=
            (ofReal_integral_eq_lintegral_ofReal (μ := ν x)
              ((χ (n + 1)).continuous.integrable_of_hasCompactSupport (χ (n + 1)).hasCompactSupport)
              (ae_of_all _ (fun g => (hχ01 (n + 1) g).1))).symm
        _ ≤ ENNReal.ofReal (M n) := ENNReal.ofReal_le_ofReal hxle
    -- the budget series
    have hβeq : ∀ n : ℕ, 2 * β n = (e / 4) * ((1 / 2 : ℝ) ^ n) := by
      intro n
      rw [hβ]
      ring
    have hsumm : Summable (fun n : ℕ => 2 * β n) := by
      rw [show (fun n : ℕ => 2 * β n) = fun n => (e / 4) * ((1 / 2 : ℝ) ^ n) from funext hβeq]
      exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
    have htsum : (∑' n : ℕ, 2 * β n) = e / 2 := by
      have h1 : (∑' n : ℕ, 2 * β n) = (e / 4) * (∑' n : ℕ, ((1 / 2 : ℝ) ^ n)) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun n => hβeq n)
      rw [h1, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    -- boundedness of the test functions on the constraint sets
    have hbdd : ∀ n j, ∃ C : ℝ, ∀ x ∈ B n, |∫ g, Fam n j g ∂(ν x)| ≤ C := by
      intro n j
      obtain ⟨Bnd, hBnd0, hBnd⟩ := exists_abs_bound_cc (Fam n j)
      refine ⟨Bnd * (M n : ℝ), fun x hx => ?_⟩
      have hxX' : x ∈ X' := hx.1
      haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
      have hmass' := hmass n x hx
      have hpt : ∀ g : SL3, ENNReal.ofReal ‖Fam n j g‖
          ≤ ENNReal.ofReal Bnd * (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g := by
        intro g
        by_cases hg : g ∈ L (n + 1)
        · rw [Set.indicator_of_mem hg]
          have h1 : ‖Fam n j g‖ ≤ Bnd := by
            rw [Real.norm_eq_abs]; exact hBnd g
          calc ENNReal.ofReal ‖Fam n j g‖ ≤ ENNReal.ofReal Bnd := ENNReal.ofReal_le_ofReal h1
            _ = ENNReal.ofReal Bnd * 1 := (mul_one _).symm
        · have h0 : Fam n j g = 0 := by
            by_contra hcon
            exact hg (hFamsupp n j (by simpa [Function.mem_support] using hcon))
          rw [Set.indicator_of_notMem hg, h0, norm_zero, ENNReal.ofReal_zero]
          positivity
      have hlint : ∫⁻ g, ENNReal.ofReal ‖Fam n j g‖ ∂(ν x)
          ≤ ENNReal.ofReal Bnd * ENNReal.ofReal (M n) := by
        calc ∫⁻ g, ENNReal.ofReal ‖Fam n j g‖ ∂(ν x)
            ≤ ∫⁻ g, ENNReal.ofReal Bnd * (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g
                ∂(ν x) := lintegral_mono hpt
          _ = ENNReal.ofReal Bnd
                * ∫⁻ g, (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g ∂(ν x) :=
              lintegral_const_mul _ (measurable_const.indicator (hLcpt (n + 1)).measurableSet)
          _ = ENNReal.ofReal Bnd * ν x (L (n + 1)) := by
              rw [lintegral_indicator_one (hLcpt (n + 1)).measurableSet]
          _ ≤ ENNReal.ofReal Bnd * ENNReal.ofReal (M n) := by gcongr
      have hfin : ENNReal.ofReal Bnd * ENNReal.ofReal (M n) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      calc |∫ g, Fam n j g ∂(ν x)| = ‖∫ g, Fam n j g ∂(ν x)‖ := (Real.norm_eq_abs _).symm
        _ ≤ (∫⁻ g, ENNReal.ofReal ‖Fam n j g‖ ∂(ν x)).toReal := norm_integral_le_lintegral_norm _
        _ ≤ (ENNReal.ofReal Bnd * ENNReal.ofReal (M n)).toReal := ENNReal.toReal_mono hfin hlint
        _ = Bnd * (M n : ℝ) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnd0,
              ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
    -- Luzin's theorem at each level
    have hluz : ∀ n : ℕ, ∃ C : Set X3, C ⊆ B n ∧ IsCompact C ∧
        μ (B n \ C) < ENNReal.ofReal (β n) ∧
        ∀ j, ContinuousOn (fun x => ∫ g, Fam n j g ∂(ν x)) C :=
      fun n => hLuzin (fun (j : ℕ) (x : X3) => ∫ g, Fam n j g ∂(ν x))
        (fun j => hL.measurable (Fam n j)) (B n) (hBmeas n) (hbdd n) (hβpos n)
    choose C hCsub hCcpt hCmeas hCcont using hluz
    refine ⟨⋂ n, C n, ?_, ?_, ?_, ?_⟩
    · refine (hCcpt 0).of_isClosed_subset (isClosed_iInter fun n => (hCcpt n).isClosed) ?_
      exact Set.iInter_subset _ 0
    · intro x hx
      exact (hCsub 0 (mem_iInter.mp hx 0)).1
    · calc μ (⋂ n, C n)ᶜ = μ (⋃ n, (C n)ᶜ) := by rw [Set.compl_iInter]
        _ ≤ ∑' n, μ ((C n)ᶜ) := measure_iUnion_le _
        _ ≤ ∑' n, ENNReal.ofReal (2 * β n) := by
            apply ENNReal.tsum_le_tsum
            intro n
            have h1 : μ ((C n)ᶜ) ≤ μ ((B n)ᶜ) + μ (B n \ C n) := by
              have hsub : (C n)ᶜ ⊆ (B n)ᶜ ∪ (B n \ C n) := by
                intro x hx
                by_cases hxB : x ∈ B n
                · exact Or.inr ⟨hxB, hx⟩
                · exact Or.inl hxB
              calc μ ((C n)ᶜ) ≤ μ ((B n)ᶜ ∪ (B n \ C n)) := measure_mono hsub
                _ ≤ μ ((B n)ᶜ) + μ (B n \ C n) := measure_union_le _ _
            have h2 : μ ((C n)ᶜ) < ENNReal.ofReal (2 * β n) := by
              calc μ ((C n)ᶜ) ≤ μ ((B n)ᶜ) + μ (B n \ C n) := h1
                _ < ENNReal.ofReal (β n) + ENNReal.ofReal (β n) :=
                    ENNReal.add_lt_add (hBcompl n) (hCmeas n)
                _ = ENNReal.ofReal (2 * β n) := by
                    rw [← ENNReal.ofReal_add (hβpos n).le (hβpos n).le]
                    ring_nf
            exact le_of_lt h2
        _ = ENNReal.ofReal (e / 2) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm, htsum]
        _ < ENNReal.ofReal e := (ENNReal.ofReal_lt_ofReal_iff hepos).mpr (by linarith)
        _ = ε := hεof.symm
    · intro f
      obtain ⟨n, hn⟩ := exists_level_superset hLmono hLint hLuniv f.hasCompactSupport
      have hfsupp : Function.support f ⊆ L n := subset_trans (subset_tsupport f) hn
      -- an approximating sequence in the level-`n` dense family
      have hex : ∀ k : ℕ, ∃ j : ℕ,
          ∀ x : SL3, |f x - Fam n j x| ≤ 1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)) := by
        intro k
        refine hFamdens f n hfsupp _ ?_
        positivity
      set J : ℕ → ℕ := fun k => Classical.choose (hex k) with hJ
      have hJspec : ∀ k x, |f x - Fam n (J k) x| ≤
          1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)) := fun k => Classical.choose_spec (hex k)
      -- uniform convergence on the compact set
      have hconv : TendstoUniformlyOn (fun (k : ℕ) (x : X3) => ∫ g, Fam n (J k) g ∂(ν x))
          (fun x : X3 => ∫ g, f g ∂(ν x)) atTop (⋂ n, C n) := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ρ hρ
        obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hρ
        filter_upwards [eventually_ge_atTop k₀] with k hk x hx
        have hxB : x ∈ B n := hCsub n (mem_iInter.mp hx n)
        have hmx : ν x (L (n + 1)) ≤ ENNReal.ofReal (M n) := hmass n x hxB
        have hxX' : x ∈ X' := hxB.1
        haveI : IsFiniteMeasureOnCompacts (ν x) := hL.radon x hxX'
        have hηpos : (0 : ℝ) < 1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)) := by positivity
        -- pointwise domination of the difference
        have hpt : ∀ g : SL3, ENNReal.ofReal ‖(f - Fam n (J k)) g‖
            ≤ ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
              * (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g := by
          intro g
          by_cases hg : g ∈ L (n + 1)
          · rw [Set.indicator_of_mem hg]
            have h1 : ‖(f - Fam n (J k)) g‖ ≤
                1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)) := by
              rw [Real.norm_eq_abs]
              exact hJspec k g
            calc ENNReal.ofReal ‖(f - Fam n (J k)) g‖
                ≤ ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1))) :=
                  ENNReal.ofReal_le_ofReal h1
              _ = ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1))) * 1 :=
                  (mul_one _).symm
          · have h0 : (f - Fam n (J k)) g = 0 := by
              change f g - Fam n (J k) g = 0
              have hf0 : f g = 0 := by
                have hg' : g ∉ L n := fun h => hg (interior_subset (hLint n h))
                by_contra hcon
                exact hg' (hfsupp (by simpa [Function.mem_support] using hcon))
              have hF0 : Fam n (J k) g = 0 := by
                by_contra hcon
                exact hg (hFamsupp n (J k) (by simpa [Function.mem_support] using hcon))
              rw [hf0, hF0, sub_zero]
            rw [Set.indicator_of_notMem hg, h0, norm_zero, ENNReal.ofReal_zero]
            positivity
        have hlint : ∫⁻ g, ENNReal.ofReal ‖(f - Fam n (J k)) g‖ ∂(ν x)
            ≤ ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
              * ENNReal.ofReal (M n) := by
          calc ∫⁻ g, ENNReal.ofReal ‖(f - Fam n (J k)) g‖ ∂(ν x)
              ≤ ∫⁻ g, ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
                  * (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g ∂(ν x) := lintegral_mono hpt
            _ = ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
                  * ∫⁻ g, (L (n + 1)).indicator (1 : SL3 → ℝ≥0∞) g ∂(ν x) :=
                lintegral_const_mul _ (measurable_const.indicator (hLcpt (n + 1)).measurableSet)
            _ = ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
                  * ν x (L (n + 1)) := by
                rw [lintegral_indicator_one (hLcpt (n + 1)).measurableSet]
            _ ≤ ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
                  * ENNReal.ofReal (M n) :=
                mul_le_mul_of_nonneg_left hmx (by positivity)
        have hfin : ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
            * ENNReal.ofReal (M n) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        have hid : ∫ g, f g ∂(ν x) - ∫ g, Fam n (J k) g ∂(ν x)
            = ∫ g, (f - Fam n (J k)) g ∂(ν x) :=
          (integral_sub (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
            ((Fam n (J k)).continuous.integrable_of_hasCompactSupport
              (Fam n (J k)).hasCompactSupport)).symm
        rw [Real.dist_eq]
        calc |∫ g, f g ∂(ν x) - ∫ g, Fam n (J k) g ∂(ν x)|
            = ‖∫ g, f g ∂(ν x) - ∫ g, Fam n (J k) g ∂(ν x)‖ := (Real.norm_eq_abs _).symm
          _ = ‖∫ g, (f - Fam n (J k)) g ∂(ν x)‖ := by rw [hid]
          _ ≤ (∫⁻ g, ENNReal.ofReal ‖(f - Fam n (J k)) g‖ ∂(ν x)).toReal :=
              norm_integral_le_lintegral_norm _
          _ ≤ (ENNReal.ofReal (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1)))
                * ENNReal.ofReal (M n)).toReal := ENNReal.toReal_mono hfin hlint
          _ = (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1))) * (M n : ℝ) := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hηpos.le,
                ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
          _ ≤ 1 / ((k : ℝ) + 1) := by
              have hMnn : (0 : ℝ) ≤ (M n : ℝ) := Nat.cast_nonneg _
              have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
              have hM1 : (0 : ℝ) < (M n : ℝ) + 1 := by positivity
              have hle : (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1))) * (M n : ℝ)
                  ≤ (1 / (((k : ℝ) + 1) * ((M n : ℝ) + 1))) * ((M n : ℝ) + 1) := by
                exact mul_le_mul_of_nonneg_left (by linarith) hηpos.le
              refine hle.trans (le_of_eq ?_)
              field_simp
          _ < ρ := by
              have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) := by
                apply one_div_le_one_div_of_le (by positivity)
                exact_mod_cast Nat.succ_le_succ hk
              linarith
      exact TendstoUniformlyOn.continuousOn hconv
        (Filter.Eventually.of_forall (fun k => (hCcont n (J k)).mono (Set.iInter_subset _ n))).frequently

/-- The countable form of Lusin's theorem (on `X₃`) follows from the single-function form by
intersecting the compacts obtained with radii `(δ / 4) * (1 / 2) ^ n`.  The two external inputs
`Work.EKLRelCross.lusin_compact` and `Work.EKLRelCross.lusin_single` are the countable and the
single-function form of Lusin's theorem; this lemma makes the two interchangeable. -/
theorem countable_of_single (μ : Measure X3) [IsFiniteMeasure μ] [T2Space X3]
    (hSingle : ∀ (f : X3 → ℝ), Measurable f → ∀ (B : Set X3), MeasurableSet B →
      (∃ C : ℝ, ∀ x ∈ B, |f x| ≤ C) → ∀ δ : ℝ, 0 < δ →
      ∃ K : Set X3, K ⊆ B ∧ IsCompact K ∧ μ (B \ K) < ENNReal.ofReal δ ∧ ContinuousOn f K)
    {F : ℕ → X3 → ℝ} (hF : ∀ n, Measurable (F n)) {B : Set X3} (hB : MeasurableSet B)
    (hbdd : ∀ n, ∃ C : ℝ, ∀ x ∈ B, |F n x| ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set X3, K ⊆ B ∧ IsCompact K ∧ μ (B \ K) < ENNReal.ofReal δ ∧
      ∀ n, ContinuousOn (F n) K := by
  set r : ℕ → ℝ := fun n => (δ / 4) * ((1 / 2 : ℝ) ^ n) with hr
  have hrpos : ∀ n : ℕ, 0 < r n :=
    fun n => mul_pos (by linarith) (pow_pos (by norm_num) n)
  choose K hKsub hKcpt hKmeas hKcont using
    fun n => hSingle (F n) (hF n) B hB (hbdd n) (r n) (hrpos n)
  refine ⟨⋂ n, K n, fun x hx => hKsub 0 (mem_iInter.mp hx 0),
    (hKcpt 0).of_isClosed_subset (isClosed_iInter fun n => (hKcpt n).isClosed)
      (Set.iInter_subset _ 0), ?_, fun n => (hKcont n).mono (Set.iInter_subset _ n)⟩
  have hsumm : Summable r := by
    rw [hr]
    exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have htsum : (∑' n : ℕ, r n) = δ / 2 := by
    rw [hr, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  calc μ (B \ ⋂ n, K n) = μ (⋃ n, (B \ K n)) := by rw [Set.sdiff_iInter]
    _ ≤ ∑' n, μ (B \ K n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (r n) := ENNReal.tsum_le_tsum fun n => (hKmeas n).le
    _ = ENNReal.ofReal (δ / 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hrpos n).le) hsumm, htsum]
    _ < ENNReal.ofReal δ := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith)
/-- **(U6) Luzin** (EKL p.14, Federer 2.3.5): on a compact subset of `X'` of almost full measure,
all the test-function integrals `x ↦ ∫ g, f g ∂(ν x)` are continuous. -/
theorem leafwise_luzin (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∀ ε : ENNReal, 0 < ε → ∃ K : Set Work.EKLContract.X3, IsCompact K ∧ K ⊆ X' ∧ μ Kᶜ < ε ∧
        ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ, ContinuousOn (fun x => ∫ g, f g ∂(ν x)) K := by
  haveI : PolishSpace X3 := h2.2.1
  haveI : T2Space X3 := h2.1
  exact leafwise_luzin_aux h2 μ U hU t0 ht0 hcontr ν X' hL
    (fun F hF B hB hbdd δ hδ =>
      countable_of_single μ (F := F) (B := B) (δ := δ)
        (fun f hf B' hB' hbdd' δ' hδ' => lusin_alt μ hf hB' hbdd' hδ') hF hB hbdd hδ)
    cc_dense_family


end Work.EKLRelCross
