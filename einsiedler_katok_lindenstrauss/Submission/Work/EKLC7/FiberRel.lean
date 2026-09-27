import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLC7.CoordTripDefs
import Submission.Work.EKLC7.CoordTripAux
import Submission.Work.EKLC7.SepL2
import Submission.Work.EKLC7.SepL2c
import Submission.Work.EKLC7.SupportFacts
import Submission.Work.EKLC7.CoordTest
import Submission.Work.EKLC7.IterTrip
import Submission.Work.EKLC7.TentDetermine
import Submission.Work.EKLC7.ShiftIntegralMeas

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-! ## Compactness and integrability helpers -/

theorem fr_isFiniteMeasureOnCompacts_prod {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [SFinite ν] :
    IsFiniteMeasureOnCompacts (μ.prod ν) := by
  refine ⟨fun K hK => ?_⟩
  calc (μ.prod ν) K ≤ (μ.prod ν) ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) :=
        measure_mono fun z hz => Set.mem_prod.mpr
          ⟨Set.mem_image_of_mem _ hz, Set.mem_image_of_mem _ hz⟩
    _ = μ (Prod.fst '' K) * ν (Prod.snd '' K) := Measure.prod_prod _ _
    _ < ⊤ := ENNReal.mul_lt_top (hK.image continuous_fst).measure_lt_top
        (hK.image continuous_snd).measure_lt_top

theorem fr_hasCompactSupport_of_lex {ψ : ℝ × ℝ × ℝ → SL3} (hψ : Continuous ψ)
    (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x, (∀ a b : Fin 3, |toMat (ψ x) a b| ≤ M) →
      |x.1| ≤ M' ∧ |x.2.1| ≤ M' ∧ |x.2.2| ≤ M')
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => f (ψ x)) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_entry_bound (tsupport f) f.hasCompactSupport
  obtain ⟨M', hM'⟩ := hlex M
  have hbox : IsCompact (Set.Icc (-M') M' ×ˢ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M')) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hclosed : IsClosed (ψ ⁻¹' tsupport f) :=
    (f.hasCompactSupport.isCompact.isClosed).preimage hψ
  have hsub : Function.support (fun x : ℝ × ℝ × ℝ => f (ψ x))
      ⊆ (ψ ⁻¹' tsupport f) ∩ (Set.Icc (-M') M' ×ˢ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M')) := by
    intro x hx
    have hx' : ψ x ∈ tsupport f := subset_tsupport f hx
    obtain ⟨e1, e2, e3⟩ := hM' x (hM (ψ x) hx')
    refine ⟨hx', ?_⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨abs_le.mp e1, abs_le.mp e2, abs_le.mp e3⟩
  have hcb : IsClosed ((ψ ⁻¹' tsupport f) ∩
      (Set.Icc (-M') M' ×ˢ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M'))) :=
    hclosed.inter hbox.isClosed
  have hcc : IsCompact ((ψ ⁻¹' tsupport f) ∩
      (Set.Icc (-M') M' ×ˢ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M'))) :=
    IsCompact.of_isClosed_subset hbox hcb Set.inter_subset_right
  rw [hasCompactSupport_def]
  exact IsCompact.of_isClosed_subset hcc isClosed_closure (closure_minimal hsub hcb)

theorem fr_hasCompactSupport_of_lex₂ {ψ : ℝ × ℝ → SL3} (hψ : Continuous ψ)
    (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x : ℝ × ℝ, (∀ a b : Fin 3, |toMat (ψ x) a b| ≤ M) →
      |x.1| ≤ M' ∧ |x.2| ≤ M')
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    HasCompactSupport (fun x : ℝ × ℝ => f (ψ x)) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_entry_bound (tsupport f) f.hasCompactSupport
  obtain ⟨M', hM'⟩ := hlex M
  have hbox : IsCompact (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M') :=
    isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed (ψ ⁻¹' tsupport f) :=
    (f.hasCompactSupport.isCompact.isClosed).preimage hψ
  have hsub : Function.support (fun x : ℝ × ℝ => f (ψ x))
      ⊆ (ψ ⁻¹' tsupport f) ∩ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M') := by
    intro x hx
    have hx' : ψ x ∈ tsupport f := subset_tsupport f hx
    obtain ⟨e1, e2⟩ := hM' x (hM (ψ x) hx')
    refine ⟨hx', ?_⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨abs_le.mp e1, abs_le.mp e2⟩
  have hcb : IsClosed ((ψ ⁻¹' tsupport f) ∩ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M')) :=
    hclosed.inter hbox.isClosed
  have hcc : IsCompact ((ψ ⁻¹' tsupport f) ∩ (Set.Icc (-M') M' ×ˢ Set.Icc (-M') M')) :=
    IsCompact.of_isClosed_subset hbox hcb Set.inter_subset_right
  rw [hasCompactSupport_def]
  exact IsCompact.of_isClosed_subset hcc isClosed_closure (closure_minimal hsub hcb)

theorem fr_hasCompactSupport_heisA (f : CompactlySupportedContinuousMap SL3 ℝ)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => f (heisA hij hjk hik x)) :=
  fr_hasCompactSupport_of_lex (continuous_heisA hij hjk hik) (heisA_lex hij hjk hik) f

theorem fr_hasCompactSupport_heisB (f : CompactlySupportedContinuousMap SL3 ℝ)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => f (heisB hij hjk hik x)) :=
  fr_hasCompactSupport_of_lex (continuous_heisB hij hjk hik) (heisB_lex hij hjk hik) f

theorem fr_hasCompactSupport_heisA_snd (f : CompactlySupportedContinuousMap SL3 ℝ)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p : ℝ) :
    HasCompactSupport (fun w : ℝ × ℝ => f (heisA hij hjk hik (p, w))) := by
  have hψ : Continuous fun w : ℝ × ℝ => heisA hij hjk hik (p, w) :=
    (continuous_heisA hij hjk hik).comp (continuous_const.prodMk continuous_id)
  refine fr_hasCompactSupport_of_lex₂ hψ ?_ f
  intro M
  refine ⟨M + M ^ 2 + 1, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := abs_le_of_abs_heisA hij hjk hik (x := (p, x)) hx
  constructor
  · nlinarith [sq_nonneg M]
  · nlinarith [sq_nonneg M]

theorem fr_hasCompactSupport_heisB_snd (f : CompactlySupportedContinuousMap SL3 ℝ)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r : ℝ) :
    HasCompactSupport (fun w : ℝ × ℝ => f (heisB hij hjk hik (r, w))) := by
  have hψ : Continuous fun w : ℝ × ℝ => heisB hij hjk hik (r, w) :=
    (continuous_heisB hij hjk hik).comp (continuous_const.prodMk continuous_id)
  refine fr_hasCompactSupport_of_lex₂ hψ ?_ f
  intro M
  refine ⟨M + M ^ 2 + 1, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := abs_le_of_abs_heisB hij hjk hik (x := (r, x)) hx
  constructor
  · nlinarith [sq_nonneg M]
  · nlinarith [sq_nonneg M]

theorem fr_integrable_of_bound_compactSupport {f : ℝ × ℝ → ℝ}
    {μ ν : Measure ℝ} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hs : HasCompactSupport f)
    {C : ℝ} (hC : ∀ z, z ∈ tsupport f → |f z| ≤ C) : Integrable f (μ.prod ν) := by
  haveI : SFinite ν := inferInstance
  haveI : IsFiniteMeasureOnCompacts (μ.prod ν) := fr_isFiniteMeasureOnCompacts_prod
  refine MeasureTheory.Integrable.mono' (g := fun z : ℝ × ℝ => C * (tsupport f).indicator (fun _ => (1 : ℝ)) z) ?_ hf ?_
  · have h0 : Integrable ((tsupport f).indicator (fun _ : ℝ × ℝ => (1 : ℝ))) (μ.prod ν) := by
      rw [MeasureTheory.integrable_indicator_iff hs.isCompact.isClosed.measurableSet]
      exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := tsupport f)
        (hs := hs.measure_lt_top.ne)
    exact h0.const_mul C
  · refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ tsupport f
    · rw [Set.indicator_of_mem hz, mul_one]
      exact hC z hz
    · rw [Set.indicator_of_notMem hz, mul_zero, Real.norm_eq_abs,
        image_eq_zero_of_notMem_tsupport hz, abs_zero]


/-! ## The trapezoid test functions -/

theorem fr_continuous_tent (a b : ℚ) (n : ℕ) : Continuous (tent a b n) := by
  unfold tent
  fun_prop

theorem fr_hasCompactSupport_tent (a b : ℚ) (n : ℕ) : HasCompactSupport (tent a b n) := by
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ) + 1)) isClosed_closure ?_
  refine closure_minimal ?_ (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ) + 1)).isClosed
  intro t ht
  simp only [Function.mem_support, ne_eq] at ht
  simp only [Set.mem_Icc]
  rcases lt_or_ge t (a : ℝ) with hlt | hge
  · have hzero : tent a b n t = 0 := by
      unfold tent
      have hle : (n : ℝ) * (t - (a : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
      have hmin : min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t)) ≤ 0 :=
        le_trans (min_le_left _ _) hle
      exact max_eq_left (le_trans (min_le_right _ _) hmin)
    exact absurd hzero ht
  · by_cases hle : t ≤ (b : ℝ) + 1
    · exact ⟨hge, hle⟩
    · have hzero : tent a b n t = 0 := by
        unfold tent
        have hmin : min ((n : ℝ) * (t - (a : ℝ))) (1 + (n : ℝ) * ((b : ℝ) - t)) ≤ 0 := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn; simp
          · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
            have h2 : 1 + (n : ℝ) * ((b : ℝ) - t) ≤ 0 := by
              have h3 : (n : ℝ) * ((b : ℝ) - t) ≤ (n : ℝ) * (-1) :=
                mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
              linarith
            exact le_trans (min_le_right _ _) h2
        exact max_eq_left (le_trans (min_le_right _ _) hmin)
      exact absurd hzero ht

def fr_tentCC (a b : ℚ) (n : ℕ) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨tent a b n, fr_continuous_tent a b n⟩, fr_hasCompactSupport_tent a b n⟩


/-! ## A test function on `ℝ³` of product form -/

theorem fr_continuous_mkG (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
    (h : CompactlySupportedContinuousMap ℝ ℝ) :
    Continuous (fun y : ℝ × ℝ × ℝ => F (y.1, y.2.2) * h y.2.1) :=
  (F.continuous.comp (continuous_fst.prodMk continuous_snd.snd)).mul
    (h.continuous.comp continuous_snd.fst)

theorem fr_hasCompactSupport_mkG (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
    (h : CompactlySupportedContinuousMap ℝ ℝ) :
    HasCompactSupport (fun y : ℝ × ℝ × ℝ => F (y.1, y.2.2) * h y.2.1) := by
  obtain ⟨M, hM0, hM⟩ := isCompact_exists_abs_bound_prod (tsupport F) F.hasCompactSupport
  obtain ⟨N, hN0, hN⟩ := isCompact_exists_abs_bound (tsupport h) h.hasCompactSupport
  have hbox : IsCompact (Set.Icc (-M) M ×ˢ (Set.Icc (-N) N ×ˢ Set.Icc (-M) M)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset hbox isClosed_closure (closure_minimal ?_ hbox.isClosed)
  intro y hy
  simp only [Function.mem_support, ne_eq] at hy
  have hy1 : F (y.1, y.2.2) ≠ 0 := fun h0 => hy (by rw [h0, zero_mul])
  have hy2 : h y.2.1 ≠ 0 := fun h0 => hy (by rw [h0, mul_zero])
  have e1 : |y.1| ≤ M := (hM (y.1, y.2.2) (subset_tsupport F hy1)).1
  have e3 : |y.2.2| ≤ M := (hM (y.1, y.2.2) (subset_tsupport F hy1)).2
  have e2 : |y.2.1| ≤ N := hN y.2.1 (subset_tsupport h hy2)
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨abs_le.mp e1, abs_le.mp e2, abs_le.mp e3⟩

/-- The test function `(p,q,r) ↦ F (p,r) * h q` on `ℝ³`, for `F ∈ C_c(ℝ²)`, `h ∈ C_c(ℝ)`. -/
def fr_mkG (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
    (h : CompactlySupportedContinuousMap ℝ ℝ) :
    CompactlySupportedContinuousMap (ℝ × ℝ × ℝ) ℝ :=
  ⟨⟨fun y : ℝ × ℝ × ℝ => F (y.1, y.2.2) * h y.2.1, fr_continuous_mkG F h⟩,
    fr_hasCompactSupport_mkG F h⟩

theorem fr_uij_add {i j : Fin 3} (hij : i ≠ j) (a b : ℝ) :
    uij hij (a + b) = uij hij a * uij hij b :=
  Matrix.SpecialLinearGroup.transvection_add hij a b

/-! ## The measured fiber lemma -/

theorem fr_fiber_of_integral {Ap Bp Cp : Measure ℝ}
    [IsFiniteMeasureOnCompacts Ap] [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hE : ∀ (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
        (h : CompactlySupportedContinuousMap ℝ ℝ),
      cA * (∫ p, ∫ r, ∫ q, (F (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, F (p, r) ∂Bp ∂Ap)) :
    ∀ᵐ z ∂(Ap.prod Bp), Cp.map (fun q => z.1 * z.2 + q) = ENNReal.ofReal (cB / cA) • Cp := by
  classical
  haveI : SFinite Ap := inferInstance
  haveI : SFinite Bp := inferInstance
  haveI : SFinite Cp := inferInstance
  haveI hfinAB : IsFiniteMeasureOnCompacts (Ap.prod Bp) := fr_isFiniteMeasureOnCompacts_prod
  have hlam : (0 : ℝ) < cB / cA := div_pos hcB hcA
  -- bumps localising to large boxes
  have hbump : ∀ n : ℕ, ∃ χ : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ,
      (∀ z ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ Set.Icc (-(n : ℝ)) (n : ℝ), χ z = 1) ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) := by
    intro n
    obtain ⟨f, hf1, -, hfs, hfr⟩ := exists_continuous_one_zero_of_isCompact
      (s := Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ Set.Icc (-(n : ℝ)) (n : ℝ)) (t := ∅)
      (isCompact_Icc.prod isCompact_Icc) isClosed_empty (Set.disjoint_empty _)
    exact ⟨⟨f, hfs⟩, hf1, fun z => (hfr z).1, fun z => (hfr z).2⟩
  choose χ hχ1 hχ0 hχle using hbump
  -- the a.e. statement for a single test function `h`
  have key : ∀ (n : ℕ) (h : CompactlySupportedContinuousMap ℝ ℝ), ∀ᵐ z ∂(Ap.prod Bp),
      χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
        - (cB / cA) * (∫ q, (h : ℝ → ℝ) q ∂Cp)) = 0 := by
    intro n h
    obtain ⟨hΨmeas, hΨbdd⟩ := ShiftIntegralMeas h Cp
    obtain ⟨M, hM0, hM⟩ :=
      isCompact_exists_abs_bound_prod (tsupport (χ n)) (χ n).hasCompactSupport
    obtain ⟨C, hC⟩ := hΨbdd M
    set c : ℝ := (cB / cA) * (∫ q, (h : ℝ → ℝ) q ∂Cp) with hcdef
    set Φ : ℝ × ℝ → ℝ :=
      fun z => χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c) with hΦdef
    have hΦmeas : Measurable Φ :=
      (map_continuous (χ n)).measurable.mul (hΨmeas.sub measurable_const)
    have hΦbdd : ∃ C', ∀ z, |Φ z| ≤ C' := by
      refine ⟨max (C + |c|) 0, fun z => ?_⟩
      by_cases hz : z ∈ tsupport (χ n)
      · obtain ⟨hz1, hz2⟩ := hM z hz
        have h1 : |χ n z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ0 n z], hχle n z⟩
        have h3 : |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| ≤ C := hC z hz1 hz2
        have h2 : |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c| ≤ C + |c| := by
          have habs : |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c|
              ≤ |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |c| := by
            calc |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c|
                = |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) + (-c)| := by ring_nf
              _ ≤ |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |-c| := abs_add_le _ _
              _ = |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |c| := by rw [abs_neg]
          linarith
        rw [hΦdef]
        calc |χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)|
            = |χ n z| * |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c| := abs_mul _ _
          _ ≤ 1 * (C + |c|) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
          _ ≤ max (C + |c|) 0 := by rw [one_mul]; exact le_max_left _ _
      · have hz0 : χ n z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [hΦdef]
        simp [hz0]
    refine SepL2 (Ap.prod Bp) Φ hΦmeas hΦbdd ?_
    intro F
    have hE' := hE (F * χ n) h
    have hIntFχ : Integrable (fun z : ℝ × ℝ => (F * χ n) z) (Ap.prod Bp) :=
      (map_continuous (F * χ n)).integrable_of_hasCompactSupport (F * χ n).hasCompactSupport
    obtain ⟨D, hD0, hD⟩ := isCompact_exists_abs_bound (Set.image F (tsupport F))
      (F.hasCompactSupport.image F.continuous)
    have hD' : ∀ z ∈ tsupport F, |F z| ≤ D := fun z hz => hD (F z) ⟨z, hz, rfl⟩
    have hIntFχΨ : Integrable
        (fun z : ℝ × ℝ => (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp))
        (Ap.prod Bp) := by
      refine fr_integrable_of_bound_compactSupport (C := D * C + 1) ?_ ?_ ?_
      · exact ((map_continuous (F * χ n)).measurable.mul hΨmeas).aestronglyMeasurable
      · rw [hasCompactSupport_def]
        refine IsCompact.of_isClosed_subset (F.hasCompactSupport.isCompact.inter
          (χ n).hasCompactSupport.isCompact) isClosed_closure ?_
        refine closure_minimal ?_ ((F.hasCompactSupport.isCompact.inter
          (χ n).hasCompactSupport.isCompact).isClosed)
        intro z hz
        simp only [Function.mem_support, ne_eq] at hz
        have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
        have h2 : F z ≠ 0 := fun h0 =>
          h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, zero_mul])
        have h3 : χ n z ≠ 0 := fun h0 =>
          h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, mul_zero])
        exact ⟨subset_tsupport F h2, subset_tsupport (χ n) h3⟩
      · have hsubχ : tsupport (fun z : ℝ × ℝ => (F * χ n) z *
            (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)) ⊆ tsupport (χ n) := by
          refine closure_minimal ?_ ((χ n).hasCompactSupport.isCompact.isClosed)
          intro z hz
          simp only [Function.mem_support, ne_eq] at hz
          have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
          exact subset_tsupport (χ n) (fun h0 =>
            h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, mul_zero]))
        have hsubF : tsupport (fun z : ℝ × ℝ => (F * χ n) z *
            (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)) ⊆ tsupport F := by
          refine closure_minimal ?_ (F.hasCompactSupport.isCompact.isClosed)
          intro z hz
          simp only [Function.mem_support, ne_eq] at hz
          have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
          exact subset_tsupport F (fun h0 =>
            h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, zero_mul]))
        intro z hz
        obtain ⟨hz1, hz2⟩ := hM z (hsubχ hz)
        have hboundF : |F z| ≤ D := hD' z (hsubF hz)
        have hboundχ : |χ n z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ0 n z], hχle n z⟩
        have hboundΨ : |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| ≤ C := hC z hz1 hz2
        have hboundFχ : |(F * χ n) z| ≤ D := by
          rw [CompactlySupportedContinuousMap.mul_apply, abs_mul]
          calc |F z| * |χ n z| ≤ D * 1 := mul_le_mul hboundF hboundχ (abs_nonneg _) hD0
            _ = D := mul_one D
        calc |(F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)|
            = |(F * χ n) z| * |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| := abs_mul _ _
          _ ≤ D * |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| :=
              mul_le_mul_of_nonneg_right hboundFχ (abs_nonneg _)
          _ ≤ D * C := mul_le_mul_of_nonneg_left hboundΨ hD0
          _ ≤ D * C + 1 := by linarith
    have hA2 : Integrable (fun z : ℝ × ℝ => (F * χ n) z * c) (Ap.prod Bp) := hIntFχ.mul_const c
    have step1 : ∫ z, F z * Φ z ∂(Ap.prod Bp)
        = ∫ z, (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
            ∂(Ap.prod Bp) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show F z * (χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c))
          = (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
      rw [CompactlySupportedContinuousMap.mul_apply]
      ring
    rw [step1]
    have step2 : ∫ z, (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
          ∂(Ap.prod Bp)
        = (∫ z, (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
              ∂(Ap.prod Bp))
          - (∫ z, (F * χ n) z * c ∂(Ap.prod Bp)) := by
      rw [show (fun z : ℝ × ℝ => (F * χ n) z *
            ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c))
          = fun z : ℝ × ℝ => (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
              - (F * χ n) z * c from funext fun z => by ring,
        MeasureTheory.integral_sub hIntFχΨ hA2]
    rw [step2]
    have e1 : ∫ z, (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
          ∂(Ap.prod Bp)
        = ∫ p, ∫ r, ∫ q, ((F * χ n) (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap := by
      rw [MeasureTheory.integral_prod _ hIntFχΨ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      exact (MeasureTheory.integral_const_mul _ _).symm
    have e2 : ∫ z, (F * χ n) z * c ∂(Ap.prod Bp)
        = c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap) := by
      rw [MeasureTheory.integral_prod _ hA2]
      simp only [MeasureTheory.integral_mul_const]
      exact mul_comm _ _
    rw [e1, e2]
    have hmul : cA * (c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap))
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap) := by
      have hA0 : cA ≠ 0 := ne_of_gt hcA
      rw [hcdef]
      field_simp
    have hcancel : cA * (∫ p, ∫ r, ∫ q, ((F * χ n) (p, r)) * (h (p * r + q))
          ∂Cp ∂Bp ∂Ap)
        = cA * (c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap)) := by
      rw [hE', hmul]
    exact sub_eq_zero.mpr (mul_left_cancel₀ (ne_of_gt hcA) hcancel)
  -- combine over the countable family of test functions
  have hcomb : ∀ᵐ z ∂(Ap.prod Bp), ∀ (i : ℕ × (ℚ × ℚ × ℕ)),
      χ i.1 z * ((∫ q, tent i.2.1 i.2.2.1 i.2.2.2 (z.1 * z.2 + q) ∂Cp)
        - (cB / cA) * (∫ q, tent i.2.1 i.2.2.1 i.2.2.2 q ∂Cp)) = 0 := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    exact key i.1 (fr_tentCC i.2.1 i.2.2.1 i.2.2.2)
  filter_upwards [hcomb] with z hz
  have hmain : ∀ (a b : ℚ) (n : ℕ),
      ∫ t, tent a b n t ∂(Cp.map (fun q => z.1 * z.2 + q))
        = ∫ t, tent a b n t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
    intro a b n
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, χ n₀ z = 1 := by
      refine ⟨Nat.ceil (max |z.1| |z.2|) + 1, hχ1 _ z ?_⟩
      have h1 : |z.1| ≤ (Nat.ceil (max |z.1| |z.2|) : ℝ) :=
        le_trans (le_max_left _ _) (Nat.le_ceil _)
      have h2 : |z.2| ≤ (Nat.ceil (max |z.1| |z.2|) : ℝ) :=
        le_trans (le_max_right _ _) (Nat.le_ceil _)
      have e1 := abs_le.mp h1
      have e2 := abs_le.mp h2
      simp only [Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> · push_cast; linarith [e1.1, e1.2, e2.1, e2.2]
    have hz0 := hz (n₀, (a, b, n))
    rw [hn₀, one_mul, sub_eq_zero] at hz0
    rw [MeasureTheory.integral_map
      (by fun_prop : AEMeasurable (fun q : ℝ => z.1 * z.2 + q) Cp)
      ((fr_continuous_tent a b n).aestronglyMeasurable)]
    rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hlam.le, smul_eq_mul]
    exact hz0
  haveI hγfin : IsFiniteMeasureOnCompacts (Cp.map (fun q => z.1 * z.2 + q)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (by fun_prop : Measurable fun q : ℝ => z.1 * z.2 + q)
      hK.measurableSet]
    have heq : (fun q : ℝ => z.1 * z.2 + q) ⁻¹' K = (fun q : ℝ => q - z.1 * z.2) '' K := by
      ext q
      constructor
      · intro hq; exact ⟨z.1 * z.2 + q, hq, by ring⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [heq]
    exact (hK.image (by fun_prop)).measure_lt_top
  haveI hδfin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (cB / cA) • Cp) :=
    IsFiniteMeasureOnCompacts.smul Cp ENNReal.ofReal_ne_top
  exact TentDetermine (γ := Cp.map (fun q => z.1 * z.2 + q))
    (δ := ENNReal.ofReal (cB / cA) • Cp) hmain


/-! ## The main theorem -/

theorem FiberRel :
    ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik νN : MeasureTheory.Measure Work.EKLContract.SL3) (cA cB : ℝ),
      MeasureTheory.IsFiniteMeasureOnCompacts νij → MeasureTheory.IsFiniteMeasureOnCompacts νjk →
      MeasureTheory.IsFiniteMeasureOnCompacts νik →
      νij (Work.EKLContract.Uij hij)ᶜ = 0 → νjk (Work.EKLContract.Uij hjk)ᶜ = 0 →
      νik (Work.EKLContract.Uij hik)ᶜ = 0 →
      0 < cA → 0 < cB →
      Work.EKLC7.TripleA νN νij νjk νik cA → Work.EKLC7.TripleB νN νij νjk νik cB →
      ∀ᵐ z ∂(νij.prod νjk),
        (νik).map (fun g => g * Work.EKLC7.comm z.1 z.2)
          = ENNReal.ofReal (cB / cA) • νik := by
  intro i j k hij hjk hik νij νjk νik νN cA cB hfij hfjk hfik hcij hcjk hcik hcA hcB hA hB
  classical
  haveI : IsFiniteMeasureOnCompacts νij := hfij
  haveI : IsFiniteMeasureOnCompacts νjk := hfjk
  haveI : IsFiniteMeasureOnCompacts νik := hfik
  haveI : SFinite νij := inferInstance
  haveI : SFinite νjk := inferInstance
  haveI : SFinite νik := inferInstance
  -- parameter (root-group) measures
  set Ap : Measure ℝ := νij.map (fun g : SL3 => toMat g i j) with hApdef
  set Bp : Measure ℝ := νjk.map (fun g : SL3 => toMat g j k) with hBpdef
  set Cp : Measure ℝ := νik.map (fun g : SL3 => toMat g i k) with hCpdef
  haveI hApfin : IsFiniteMeasureOnCompacts Ap := by
    rw [hApdef]; exact isFiniteMeasureOnCompacts_map_entry hij hcij
  haveI hBpfin : IsFiniteMeasureOnCompacts Bp := by
    rw [hBpdef]; exact isFiniteMeasureOnCompacts_map_entry hjk hcjk
  haveI hCpfin : IsFiniteMeasureOnCompacts Cp := by
    rw [hCpdef]; exact isFiniteMeasureOnCompacts_map_entry hik hcik
  haveI : SFinite Ap := inferInstance
  haveI : SFinite Bp := inferInstance
  haveI : SFinite Cp := inferInstance
  haveI : SFinite (Bp.prod Cp) := inferInstance
  haveI : SFinite (Ap.prod Cp) := inferInstance
  have hAp : νij = Ap.map (fun s : ℝ => uij hij s) := by
    rw [hApdef]; exact measure_eq_map_uij_entry hij hcij
  have hBp : νjk = Bp.map (fun s : ℝ => uij hjk s) := by
    rw [hBpdef]; exact measure_eq_map_uij_entry hjk hcjk
  have hCp : νik = Cp.map (fun s : ℝ => uij hik s) := by
    rw [hCpdef]; exact measure_eq_map_uij_entry hik hcik
  -- Step 1: the two iterated integrals in coordinates
  have hE : ∀ (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
      (h : CompactlySupportedContinuousMap ℝ ℝ),
      cA * (∫ p, ∫ r, ∫ q, (F (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, F (p, r) ∂Bp ∂Ap) := by
    intro F h
    obtain ⟨f, hf⟩ := CoordTest hij hjk hik (fun z : ℝ × ℝ => F z) (fun t : ℝ => h t)
      F.continuous h.continuous F.hasCompactSupport h.hasCompactSupport
    have hAform : (∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νjk ∂νij)
        = ∫ p, ∫ r, ∫ q, F (p, r) * h (p * r + q) ∂Cp ∂Bp ∂Ap := by
      rw [IterTrip (Work.EKLContract.Lemmas.horoUij_cont hij) (Work.EKLContract.Lemmas.horoUij_cont hjk) (Work.EKLContract.Lemmas.horoUij_cont hik)
        (continuous_heisA hij hjk hik) (prod_heisA hij hjk hik) (heisA_lex hij hjk hik)
        hAp hBp hCp f]
      rw [show (νij.prod (νjk.prod νik)).map
            (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2)
          = (Ap.prod (Bp.prod Cp)).map (heisA hij hjk hik) from
        rhoA_eq hij hjk hik hAp hBp hCp]
      rw [show (∫ g, f g ∂((Ap.prod (Bp.prod Cp)).map (heisA hij hjk hik)))
          = ∫ x : ℝ × ℝ × ℝ, f (heisA hij hjk hik x) ∂(Ap.prod (Bp.prod Cp)) from
        MeasureTheory.integral_map (continuous_heisA hij hjk hik).aemeasurable
          f.continuous.aestronglyMeasurable]
      rw [show (fun x : ℝ × ℝ × ℝ => f (heisA hij hjk hik x))
          = fun x => (fr_mkG F h) (shearA x) from funext fun x => by
            change f (heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1)
              = F (x.1, x.2.1) * h (x.1 * x.2.1 + x.2.2)
            exact hf _ _ _]
      rw [fubini_shearA (Ap := Ap) (Bp := Bp) (Cp := Cp) (fr_mkG F h)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      rfl
    have hBform : (∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νij ∂νjk)
        = ∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp := by
      rw [IterTrip (Work.EKLContract.Lemmas.horoUij_cont hjk) (Work.EKLContract.Lemmas.horoUij_cont hij) (Work.EKLContract.Lemmas.horoUij_cont hik)
        (continuous_heisB hij hjk hik) (prod_heisB hij hjk hik) (heisB_lex hij hjk hik)
        hBp hAp hCp f]
      rw [show (νjk.prod (νij.prod νik)).map
            (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2)
          = (Bp.prod (Ap.prod Cp)).map (heisB hij hjk hik) from
        rhoB_eq hij hjk hik hAp hBp hCp]
      rw [show (∫ g, f g ∂((Bp.prod (Ap.prod Cp)).map (heisB hij hjk hik)))
          = ∫ x : ℝ × ℝ × ℝ, f (heisB hij hjk hik x) ∂(Bp.prod (Ap.prod Cp)) from
        MeasureTheory.integral_map (continuous_heisB hij hjk hik).aemeasurable
          f.continuous.aestronglyMeasurable]
      haveI : IsFiniteMeasureOnCompacts (Ap.prod Cp) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Ap) (ν := Cp)
      haveI : IsFiniteMeasureOnCompacts (Bp.prod (Ap.prod Cp)) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Bp) (ν := Ap.prod Cp)
      rw [MeasureTheory.integral_prod (fun x : ℝ × ℝ × ℝ => f (heisB hij hjk hik x))
        ((f.continuous.comp (continuous_heisB hij hjk hik)).integrable_of_hasCompactSupport
          (fr_hasCompactSupport_heisB f hij hjk hik))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      show ∫ w : ℝ × ℝ, f (heisB hij hjk hik (r, w)) ∂(Ap.prod Cp)
          = ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap
      rw [MeasureTheory.integral_prod (fun w : ℝ × ℝ => f (heisB hij hjk hik (r, w)))
        ((f.continuous.comp ((continuous_heisB hij hjk hik).comp
            (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
          (fr_hasCompactSupport_heisB_snd f hij hjk hik r))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [heisB]
      rw [hf]
    have hAB : cA * (∫ p, ∫ r, ∫ q, F (p, r) * h (p * r + q) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp) := by
      rw [← hAform, ← hBform]
      exact (hA f).symm.trans (hB f)
    have hBfac : (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp)
        = (∫ q, h q ∂Cp) * (∫ r, ∫ p, F (p, r) ∂Ap ∂Bp) := by
      have h1 : ∀ r : ℝ, (∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap)
          = (∫ q, h q ∂Cp) * (∫ p, F (p, r) ∂Ap) := by
        intro r
        rw [show (∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap)
            = ∫ p, F (p, r) * (∫ q, h q ∂Cp) ∂Ap from ?_,
          MeasureTheory.integral_mul_const]
        · ring
        · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact MeasureTheory.integral_const_mul _ _
      rw [show (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp)
          = ∫ r, (∫ q, h q ∂Cp) * (∫ p, F (p, r) ∂Ap) ∂Bp from ?_,
        MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => h1 r)
    have hswap : (∫ r, ∫ p, F (p, r) ∂Ap ∂Bp) = ∫ p, ∫ r, F (p, r) ∂Bp ∂Ap := by
      haveI : IsFiniteMeasureOnCompacts (Ap.prod Bp) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Ap) (ν := Bp)
      have hIntF : Integrable (fun z : ℝ × ℝ => F z) (Ap.prod Bp) :=
        F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport
      rw [← MeasureTheory.integral_prod_symm (fun z : ℝ × ℝ => F z) hIntF,
        MeasureTheory.integral_prod (fun z : ℝ × ℝ => F z) hIntF]
    rw [hAB, hBfac, hswap]
    ring
  -- Step 2: the a.e. fiber relation at the level of `ℝ`
  have hgood := fr_fiber_of_integral (Ap := Ap) (Bp := Bp) (Cp := Cp) hcA hcB hE
  -- Step 3: transfer to `SL₃(ℝ)`
  have hlam : (0 : ℝ) < cB / cA := div_pos hcB hcA
  set T : SL3 × SL3 → ℝ × ℝ := fun z => (toMat z.1 i j, toMat z.2 j k) with hTdef
  have hTmeas : Measurable T := by
    rw [hTdef]
    exact (((continuous_toMat_entry i j).comp continuous_fst).measurable).prodMk
      (((continuous_toMat_entry j k).comp continuous_snd).measurable)
  have hmapT : (νij.prod νjk).map T = Ap.prod Bp := by
    rw [hTdef, hApdef, hBpdef]
    exact (Measure.map_prod_map νij νjk (continuous_toMat_entry i j).measurable
      (continuous_toMat_entry j k).measurable).symm
  set Bad : Set (ℝ × ℝ) := ⋃ (a : ℚ × ℚ × ℕ),
    {y : ℝ × ℝ | ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp
      ≠ ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)} with hBad
  have hBadmeas : MeasurableSet Bad := by
    rw [hBad]
    refine MeasurableSet.iUnion fun a => ?_
    have hfm : Measurable (fun y : ℝ × ℝ =>
        ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp) :=
      (ShiftIntegralMeas (fr_tentCC a.1 a.2.1 a.2.2) Cp).1
    have : {y : ℝ × ℝ | ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp
        ≠ ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)}
        = (fun y : ℝ × ℝ => ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp) ⁻¹'
            ({∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)}ᶜ) := rfl
    rw [this]
    exact hfm (measurableSet_singleton _).compl
  have hBadnull : (Ap.prod Bp) Bad = 0 := by
    rw [hBad]
    refine measure_iUnion_null fun a => ?_
    have hfl : ∀ᵐ y ∂(Ap.prod Bp),
        (∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp)
          = ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
      filter_upwards [hgood] with y hy
      rw [← MeasureTheory.integral_map
        (by fun_prop : AEMeasurable (fun q : ℝ => y.1 * y.2 + q) Cp)
        ((fr_continuous_tent a.1 a.2.1 a.2.2).aestronglyMeasurable), hy]
    exact MeasureTheory.ae_iff.mp hfl
  have hpre : (νij.prod νjk) (T ⁻¹' Bad) = 0 := by
    rw [← Measure.map_apply hTmeas hBadmeas, hmapT]
    exact hBadnull
  have hSnull : (νij.prod νjk) ((Uij hij ×ˢ Uij hjk)ᶜ) = 0 := by
    have hsub : ((Uij hij ×ˢ Uij hjk)ᶜ : Set (SL3 × SL3))
        ⊆ ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ) := by
      intro z hz
      rw [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hz
      rcases hz with h1 | h2
      · exact Set.mem_union_left _ (Set.mem_prod.mpr ⟨h1, Set.mem_univ _⟩)
      · exact Set.mem_union_right _ (Set.mem_prod.mpr ⟨Set.mem_univ _, h2⟩)
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ bot_le
    calc (νij.prod νjk) ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ)
          ≤ (νij.prod νjk) ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ)
              + (νij.prod νjk) (Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ) := measure_union_le _ _
        _ = νij (Uij hij)ᶜ * νjk Set.univ + νij Set.univ * νjk (Uij hjk)ᶜ := by
              rw [Measure.prod_prod, Measure.prod_prod]
        _ = 0 := by rw [hcij, hcjk]; simp
  rw [MeasureTheory.ae_iff]
  have hsub : {z : SL3 × SL3 | ¬ ((νik).map (fun g => g * comm z.1 z.2)
        = ENNReal.ofReal (cB / cA) • νik)}
      ⊆ (T ⁻¹' Bad ∪ (Uij hij ×ˢ Uij hjk)ᶜ) := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hzbad, hzS⟩ := hcon
    obtain ⟨hz1mem, hz2mem⟩ := Set.mem_prod.mp hzS
    set p : ℝ := toMat z.1 i j with hpdef
    set r : ℝ := toMat z.2 j k with hrdef
    have hz1eq : uij hij p = z.1 := by
      rw [hpdef]
      exact uij_of_mem_pcoord hij hjk hik hz1mem
    have hz2eq : uij hjk r = z.2 := by
      rw [hrdef]
      exact uij_of_mem_rcoord hij hjk hik hz2mem
    have hcomm : comm z.1 z.2 = uij hik (p * r) := by
      rw [← hz1eq, ← hz2eq]
      exact uij_commutator hij hjk hik p r
    have hTz : T z = (p, r) := by
      rw [hTdef, hpdef, hrdef]
    rw [hBad] at hzbad
    have huniv : ∀ a : ℚ × ℚ × ℕ,
        ∫ t, tent a.1 a.2.1 a.2.2 t ∂(Cp.map (fun q => p * r + q))
          = ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
      intro a
      rw [MeasureTheory.integral_map
        (by fun_prop : AEMeasurable (fun q : ℝ => p * r + q) Cp)
        ((fr_continuous_tent a.1 a.2.1 a.2.2).aestronglyMeasurable)]
      by_contra hne
      refine hzbad (Set.mem_iUnion.mpr ⟨a, ?_⟩)
      simp only [Set.mem_ofPred_eq, hTz]
      exact hne
    haveI hγfin : IsFiniteMeasureOnCompacts (Cp.map (fun q => p * r + q)) := by
      refine ⟨fun K hK => ?_⟩
      rw [Measure.map_apply (by fun_prop : Measurable fun q : ℝ => p * r + q)
        hK.measurableSet]
      have heq : (fun q : ℝ => p * r + q) ⁻¹' K = (fun q : ℝ => q - p * r) '' K := by
        ext q
        constructor
        · intro hq; exact ⟨p * r + q, hq, by ring⟩
        · rintro ⟨y, hy, rfl⟩; simpa using hy
      rw [heq]
      exact (hK.image (by fun_prop)).measure_lt_top
    haveI hδfin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (cB / cA) • Cp) :=
      IsFiniteMeasureOnCompacts.smul Cp ENNReal.ofReal_ne_top
    have hgoodz : Cp.map (fun q => p * r + q) = ENNReal.ofReal (cB / cA) • Cp :=
      TentDetermine (γ := Cp.map (fun q => p * r + q))
        (δ := ENNReal.ofReal (cB / cA) • Cp) (fun a b n => huniv (a, b, n))
    have hgoal : (νik).map (fun g => g * comm z.1 z.2)
        = ENNReal.ofReal (cB / cA) • νik := by
      rw [hcomm]
      calc (νik).map (fun g => g * uij hik (p * r))
          = Measure.map (fun g : SL3 => g * uij hik (p * r))
              (Measure.map (fun s : ℝ => uij hik s) Cp) := by rw [hCp]
        _ = Measure.map ((fun g : SL3 => g * uij hik (p * r)) ∘ (fun s : ℝ => uij hik s)) Cp :=
              Measure.map_map ((continuous_id.mul continuous_const).measurable)
                (Work.EKLContract.Lemmas.horoUij_cont hik).measurable
        _ = Measure.map (fun q : ℝ => uij hik (p * r + q)) Cp := by
              congr 1
              funext q
              simp only [Function.comp_apply]
              rw [← fr_uij_add hik q (p * r), add_comm]
        _ = Measure.map (fun s : ℝ => uij hik s) (Measure.map (fun q : ℝ => p * r + q) Cp) :=
              (Measure.map_map (Work.EKLContract.Lemmas.horoUij_cont hik).measurable
                (by fun_prop : Measurable fun q : ℝ => p * r + q)).symm
        _ = ENNReal.ofReal (cB / cA) • νik := by
              rw [hCp, ← Measure.map_smul _ (Work.EKLContract.Lemmas.horoUij_cont hik).measurable.aemeasurable, ← hgoodz]
    exact absurd hgoal hz
  refine measure_mono_null hsub ?_
  refine le_antisymm ?_ bot_le
  calc (νij.prod νjk) (T ⁻¹' Bad ∪ (Uij hij ×ˢ Uij hjk)ᶜ)
      ≤ (νij.prod νjk) (T ⁻¹' Bad) + (νij.prod νjk) ((Uij hij ×ˢ Uij hjk)ᶜ) :=
        measure_union_le _ _
    _ = 0 := by rw [hpre, hSnull]; simp

end Work.EKLC7
