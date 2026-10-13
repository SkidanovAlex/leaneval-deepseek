import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.badArcAux
import Submission.Work.WilE3.Taylor.CaseII.badArcSetup
import Submission.Work.WilE3.Loj.curve_selection
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.badSeqOnPolarSet

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **(T3) `badArc_fixedBall`** — the fixed-ball
  bad-arc lemma of the replacement route of `cbc/wilkies_e3_caseII.md` §3.

  The estimates and the Lagrange (Step A/B) input are in `badArcSetup` (`badArc_setup`); this module
  performs the pigeonhole over the finitely many pivots and the analytic curve selection of
  `Work.WilE3.Loj.curveSel_full` inside the basic semianalytic sets `FInt`/`GInt` (interior case) and
  `FBnd`/`GBnd` (boundary case) of `badArcAux`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

theorem badArc_fixedBall {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) {p q : ℕ}
    (hk : 0 < k) (hpq : p < q)
    (hbad : ∀ ρ : ℝ, 0 < ρ → ∃ x : Fin k → ℝ, dist x y < ρ ∧ 0 < WilkiesDesign.E.eaEval c Φ x ∧
      (∑ l, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) x) ^ 2) ^ q < (WilkiesDesign.E.eaEval c Φ x) ^ (2 * p))
    (hyΦ : WilkiesDesign.E.eaEval c Φ y = 0)
    (v : Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (y' : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (C : ℝ), 0 < C ∧
      AnalyticAt ℝ γ 0 ∧ γ 0 = y' ∧ WilkiesDesign.E.eaEval c Φ y' = 0 ∧
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < WilkiesDesign.E.eaEval c Φ (γ t) ∧
        (∑ l, (WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) (γ t)) ^ 2) ^ q < C * (WilkiesDesign.E.eaEval c Φ (γ t)) ^ (2 * p)) ∧
      ((∃ i₀ : Fin k, ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i₀ Φ) (γ t) ≠ 0 ∧
          ∀ i : Fin k, i ≠ i₀ → WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor c Φ v i₀ i) (γ t) = 0) ∨
       (∃ i₀ j₀ : Fin k, i₀ ≠ j₀ ∧ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.sphereP y (δ ^ 2)) (γ t) = 0 ∧
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i₀ Φ) (γ t) * (γ t j₀ - y j₀)
            - WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j₀ Φ) (γ t) * (γ t i₀ - y i₀) ≠ 0 ∧
          ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ →
            WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor3 c Φ v y i₀ j₀ l) (γ t) = 0)) := by
  classical
  have _hpq := hpq
  obtain ⟨x, u, Cs, hCs_pos, huLev, hxtend, huBall, hbad_u, hcase⟩ :=
    badArc_setup c Φ y hk hbad hyΦ v δ hδ
  have hΦcont : Continuous (fun z : Fin k → ℝ => eaEval c Φ z) :=
    continuous_iff_continuousAt.mpr fun x => (eaEval_analytic c Φ x).continuousAt
  have hcases : ∃ᶠ n : ℕ in atTop, ∃ a : CIdx k, u n ∈ CSet c Φ v y Cs δ p q a :=
    hcase.frequently
  obtain ⟨a₀, ha₀⟩ := frequently_exists_of_finite hcases
  rcases a₀ with i₀ | ⟨⟨i₀, j₀⟩, hij⟩
  · -- ### the interior case
    obtain ⟨φ, hφmono, hφP⟩ := extraction_of_frequently_atTop ha₀
    have hball : ∀ n : ℕ, u (φ n) ∈ Metric.closedBall y δ := fun n => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖u (φ n) - y‖ ≤ Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) := by
        simpa [Pi.sub_apply] using Work.WilE3.Taylor.Grad.norm_le_sqrt_sumSq (u (φ n) - y)
      have h2 : Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) ≤ δ := by
        rw [← Real.sqrt_sq hδ.le]
        exact Real.sqrt_le_sqrt (huBall (φ n))
      linarith
    obtain ⟨y', -, ψ, hψmono, htend⟩ := (isCompact_closedBall y δ).tendsto_subseq hball
    set χ : ℕ → ℕ := fun n => φ (ψ n) with hχdef
    have hχmono : StrictMono χ := hφmono.comp hψmono
    have hχP : ∀ n : ℕ, IntWit c Φ v y Cs p q i₀ (u (χ n)) := fun n => by
      simpa only [CSet, hχdef, Set.mem_ofPred_eq] using hφP (ψ n)
    have hχtend : Tendsto (fun n : ℕ => u (χ n)) atTop (𝓝 y') := htend
    have hΦy' : eaEval c Φ y' = 0 := by
      have h1 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 (eaEval c Φ y')) :=
        (hΦcont.tendsto y').comp hχtend
      have h2 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 0) := by
        have heq' : (fun n : ℕ => eaEval c Φ (u (χ n))) = fun n => eaEval c Φ (x (χ n)) := by
          funext n; rw [huLev (χ n)]
        rw [heq']
        have h3 : Tendsto (fun n : ℕ => x (χ n)) atTop (𝓝 y) := hxtend.comp hχmono.tendsto_atTop
        have h4 : Tendsto (fun n : ℕ => eaEval c Φ (x (χ n))) atTop (𝓝 (eaEval c Φ y)) :=
          (hΦcont.tendsto y).comp h3
        rw [hyΦ] at h4
        exact h4
      exact tendsto_nhds_unique h1 h2
    have hmem : ∀ n : ℕ, u (χ n) ∈ WilkiesDesign.CG.C4a.BasicSA
        (fun z => FInt c Φ v i₀ z) (GInt c Φ i₀ Cs p q) := by
      intro n
      obtain ⟨hpos, hbadn, hi, hmin'⟩ := hχP n
      refine ⟨?_, ?_⟩
      · show FInt c Φ v i₀ (u (χ n)) = 0
        unfold FInt
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases eq_or_ne i i₀ with h | h
        · subst h
          rw [eaEval_pertMinor]; ring
        · rw [hmin' i h]; ring
      · intro j
        fin_cases j
        · change 0 < GInt c Φ i₀ Cs p q 0 (u (χ n))
          rw [GInt_zero]; exact hpos
        · change 0 < GInt c Φ i₀ Cs p q 1 (u (χ n))
          rw [GInt_one]
          exact sub_pos.mpr hbadn
        · change 0 < GInt c Φ i₀ Cs p q 2 (u (χ n))
          rw [GInt_two]
          simpa using sq_pos_of_ne_zero hi
    have hy'cl : y' ∈ closure (WilkiesDesign.CG.C4a.BasicSA
        (fun z => FInt c Φ v i₀ z) (GInt c Φ i₀ Cs p q)) :=
      mem_closure_of_tendsto hχtend (Eventually.of_forall hmem)
    obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
      Work.WilE3.Loj.curveSel_full k 3 (fun z => FInt c Φ v i₀ z) (GInt c Φ i₀ Cs p q) y'
        (analyticAt_FInt c Φ v i₀ y') (fun j => analyticAt_GInt c Φ i₀ Cs p q y' j) hy'cl
    have hnb : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hεpos))
    refine ⟨y', γ, Cs, hCs_pos, hγan, hγ0, hΦy', ?_, Or.inl ⟨i₀, ?_⟩⟩
    · filter_upwards [hnb] with t ht
      have hΦpos : 0 < eaEval c Φ (γ t) := by
        have h := (hγε t ht).2 0
        change 0 < GInt c Φ i₀ Cs p q 0 (γ t) at h
        rw [GInt_zero] at h
        exact h
      have hineq : 0 < Cs * (eaEval c Φ (γ t)) ^ (2 * p)
          - (∑ l : Fin k, (eaEval c (eaD c l Φ) (γ t)) ^ 2) ^ q := by
        have h := (hγε t ht).2 1
        change 0 < GInt c Φ i₀ Cs p q 1 (γ t) at h
        rw [GInt_one] at h
        exact h
      exact ⟨hΦpos, sub_pos.mp hineq⟩
    · filter_upwards [hnb] with t ht
      have hF0 : FInt c Φ v i₀ (γ t) = 0 := (hγε t ht).1
      have hne : eaEval c (eaD c i₀ Φ) (γ t) ≠ 0 := by
        have h := (hγε t ht).2 2
        change 0 < GInt c Φ i₀ Cs p q 2 (γ t) at h
        rw [GInt_two] at h
        intro h0
        have h3 : (fun z => eaEval c (eaD c i₀ Φ) z ^ 2) (γ t) = 0 := by simp [h0]
        rw [h3] at h
        exact lt_irrefl 0 h
      refine ⟨hne, fun i _ => ?_⟩
      exact eq_zero_of_sum_sq_eq_zero (fun i => eaEval c (pertMinor c Φ v i₀ i) (γ t))
        (by rw [← FInt]; exact hF0) i
  · -- ### the boundary case
    obtain ⟨φ, hφmono, hφP⟩ := extraction_of_frequently_atTop ha₀
    have hball : ∀ n : ℕ, u (φ n) ∈ Metric.closedBall y δ := fun n => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖u (φ n) - y‖ ≤ Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) := by
        simpa [Pi.sub_apply] using Work.WilE3.Taylor.Grad.norm_le_sqrt_sumSq (u (φ n) - y)
      have h2 : Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) ≤ δ := by
        rw [← Real.sqrt_sq hδ.le]
        exact Real.sqrt_le_sqrt (huBall (φ n))
      linarith
    obtain ⟨y', -, ψ, hψmono, htend⟩ := (isCompact_closedBall y δ).tendsto_subseq hball
    set χ : ℕ → ℕ := fun n => φ (ψ n) with hχdef
    have hχmono : StrictMono χ := hφmono.comp hψmono
    have hχP : ∀ n : ℕ, BndWit c Φ v y Cs δ p q i₀ j₀ (u (χ n)) := fun n => by
      simpa only [CSet, hχdef, Set.mem_ofPred_eq] using hφP (ψ n)
    have hχtend : Tendsto (fun n : ℕ => u (χ n)) atTop (𝓝 y') := htend
    have hΦy' : eaEval c Φ y' = 0 := by
      have h1 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 (eaEval c Φ y')) :=
        (hΦcont.tendsto y').comp hχtend
      have h2 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 0) := by
        have heq' : (fun n : ℕ => eaEval c Φ (u (χ n))) = fun n => eaEval c Φ (x (χ n)) := by
          funext n; rw [huLev (χ n)]
        rw [heq']
        have h3 : Tendsto (fun n : ℕ => x (χ n)) atTop (𝓝 y) := hxtend.comp hχmono.tendsto_atTop
        have h4 : Tendsto (fun n : ℕ => eaEval c Φ (x (χ n))) atTop (𝓝 (eaEval c Φ y)) :=
          (hΦcont.tendsto y).comp h3
        rw [hyΦ] at h4
        exact h4
      exact tendsto_nhds_unique h1 h2
    have hmem : ∀ n : ℕ, u (χ n) ∈ WilkiesDesign.CG.C4a.BasicSA
        (fun z => FBnd c Φ v y (δ ^ 2) i₀ j₀ z) (GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀) := by
      intro n
      obtain ⟨hpos, hbadn, hsph, hne_piv, hmu, hmin3⟩ := hχP n
      refine ⟨?_, ?_⟩
      · show FBnd c Φ v y (δ ^ 2) i₀ j₀ (u (χ n)) = 0
        unfold FBnd
        have h1 : ((∑ i : Fin k, (u (χ n) i - y i) ^ 2) - δ ^ 2) ^ 2 = 0 := by
          rw [hsph]; ring
        have h2 : ∑ l : Fin k, (eaEval c (pertMinor3 c Φ v y i₀ j₀ l) (u (χ n))) ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          rcases eq_or_ne l i₀ with hl | hl
          · rw [hl, (eaEval_pertMinor3_self c Φ v y i₀ j₀ (u (χ n))).1]; ring
          · rcases eq_or_ne l j₀ with hl' | hl'
            · rw [hl', (eaEval_pertMinor3_self c Φ v y i₀ j₀ (u (χ n))).2]; ring
            · rw [hmin3 l hl hl']; ring
        rw [h1, h2, add_zero]
      · intro j
        fin_cases j
        · change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 0 (u (χ n))
          rw [GBnd_zero]; exact hpos
        · change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 1 (u (χ n))
          rw [GBnd_one]
          exact sub_pos.mpr hbadn
        · change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 2 (u (χ n))
          rw [GBnd_two]
          have h2 : muP c Φ y i₀ j₀ (u (χ n)) ≠ 0 := by
            simpa only [muP] using hmu
          simpa using sq_pos_of_ne_zero h2
    have hy'cl : y' ∈ closure (WilkiesDesign.CG.C4a.BasicSA
        (fun z => FBnd c Φ v y (δ ^ 2) i₀ j₀ z) (GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀)) :=
      mem_closure_of_tendsto hχtend (Eventually.of_forall hmem)
    obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
      Work.WilE3.Loj.curveSel_full k 3 (fun z => FBnd c Φ v y (δ ^ 2) i₀ j₀ z)
        (GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀) y'
        (analyticAt_FBnd c Φ v y (δ ^ 2) i₀ j₀ y')
        (fun j => analyticAt_GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ y' j) hy'cl
    have hnb : Set.Ioo (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hεpos))
    refine ⟨y', γ, Cs, hCs_pos, hγan, hγ0, hΦy', ?_, Or.inr ⟨i₀, j₀, hij, ?_⟩⟩
    · filter_upwards [hnb] with t ht
      have hΦpos : 0 < eaEval c Φ (γ t) := by
        have h := (hγε t ht).2 0
        change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 0 (γ t) at h
        rw [GBnd_zero] at h
        exact h
      have hineq : 0 < Cs * (eaEval c Φ (γ t)) ^ (2 * p)
          - (∑ l : Fin k, (eaEval c (eaD c l Φ) (γ t)) ^ 2) ^ q := by
        have h := (hγε t ht).2 1
        change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 1 (γ t) at h
        rw [GBnd_one] at h
        exact h
      exact ⟨hΦpos, sub_pos.mp hineq⟩
    · filter_upwards [hnb] with t ht
      have hF0 : FBnd c Φ v y (δ ^ 2) i₀ j₀ (γ t) = 0 := (hγε t ht).1
      have hsplit : ((∑ i : Fin k, (γ t i - y i) ^ 2) - δ ^ 2) ^ 2 = 0 ∧
          ∑ l : Fin k, (eaEval c (pertMinor3 c Φ v y i₀ j₀ l) (γ t)) ^ 2 = 0 := by
        have h' := hF0
        unfold FBnd at h'
        exact add_eq_zero_iff_of_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun l _ => sq_nonneg _) |>.mp h'
      have hsph : (∑ i : Fin k, (γ t i - y i) ^ 2) = δ ^ 2 := by
        have h := hsplit.1
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        linarith
      have hmu : eaEval c (eaD c i₀ Φ) (γ t) * (γ t j₀ - y j₀)
          - eaEval c (eaD c j₀ Φ) (γ t) * (γ t i₀ - y i₀) ≠ 0 := by
        have h := (hγε t ht).2 2
        change 0 < GBnd c Φ y Cs (δ ^ 2) p q i₀ j₀ 2 (γ t) at h
        rw [GBnd_two] at h
        have h2 : muP c Φ y i₀ j₀ (γ t) ≠ 0 := by
          intro h0
          have h3 : (fun z => muP c Φ y i₀ j₀ z ^ 2) (γ t) = 0 := by simp [h0]
          rw [h3] at h
          exact lt_irrefl 0 h
        simpa only [muP] using h2
      refine ⟨?_, hmu, fun l hl1 hl2 => ?_⟩
      · rw [eaEval_sphereP, hsph]; ring
      · exact eq_zero_of_sum_sq_eq_zero
          (fun l => eaEval c (pertMinor3 c Φ v y i₀ j₀ l) (γ t)) hsplit.2 l

end Work.WilE3.Taylor.CaseII
