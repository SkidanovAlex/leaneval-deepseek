import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.LocUnif.FinalAssembly
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_ofReal_level6
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## Non-negativity of the level-6 pieces -/

theorem level6Z_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ level6Z α g z θ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem level6T_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ level6T α g z θ :=
  sq_nonneg _

/-- The Fatou direction of `liminf` for `ℝ≥0∞`-valued sequences: the sum of the `liminf`s is at
most the `liminf` of the sums. -/
private theorem liminf_add_le_ennreal (u v : ℕ → ℝ≥0∞) :
    Filter.liminf u Filter.atTop + Filter.liminf v Filter.atTop
      ≤ Filter.liminf (fun n => u n + v n) Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add]
  refine iSup_le fun N => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun M => ?_
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_iSup_of_le (max N M) ?_
  refine le_iInf fun n => le_iInf fun hn => ?_
  have h1 : (⨅ i, ⨅ (_ : i ≥ N), u i) ≤ u n :=
    le_trans (iInf_le _ n) (iInf_le _ (le_trans (le_max_left _ _) hn))
  have h2 : (⨅ i, ⨅ (_ : i ≥ M), v i) ≤ v n :=
    le_trans (iInf_le _ n) (iInf_le _ (le_trans (le_max_right _ _) hn))
  exact add_le_add h1 h2

/-- Splitting `∫⁻ ofReal (HkIntegrand α 6 g)` along the level-6 identities, for an arbitrary
integration domain. -/
theorem lintegral_HkIntegrand_six_split {α : ℝ} {g : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (h5m : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 g p.1 p.2)) (MeasureTheory.volume.restrict s))
    (hZm : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (level6Z α g p.1 p.2)) (MeasureTheory.volume.restrict s)) :
    ∫⁻ p in s, ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 g p.1 p.2)
      = (∫⁻ p in s, ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 g p.1 p.2))
        + ((∫⁻ p in s, ENNReal.ofReal (level6Z α g p.1 p.2))
          + ∫⁻ p in s, ENNReal.ofReal (level6T α g p.1 p.2)) := by
  rw [← lintegral_add_left' hZm, ← lintegral_add_left' h5m]
  refine lintegral_congr fun p => ?_
  have h5 := Work.Spaces.HkIntegrand_nonneg α 5 g p.1 p.2
  have hZ := level6Z_nonneg α g p.1 p.2
  have hT := level6T_nonneg α g p.1 p.2
  rw [show Work.Spaces.HkIntegrand α 6 g p.1 p.2
      = Work.Spaces.HkIntegrand α 5 g p.1 p.2 + (level6Z α g p.1 p.2 + level6T α g p.1 p.2)
      from by rw [(level6_identities α).1 g p.1 p.2, add_assoc]]
  rw [ENNReal.ofReal_add h5 (add_nonneg hZ hT), ENNReal.ofReal_add hZ hT]

/-! ## The monotone family of boxes exhausting the quadrant -/

/-- The boxes `[1/(k+2), k+2] × [1/(k+2), π/2 - 1/(k+2)]`, an increasing family of rectangles
with `0 < a < b`, `0 < c < d < π/2` whose union is the open quadrant. -/
def cbox (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (1 / ((k : ℝ) + 2)) ((k : ℝ) + 2) ×ˢ
    Set.Icc (1 / ((k : ℝ) + 2)) (π / 2 - 1 / ((k : ℝ) + 2))

theorem cbox_mono : Monotone cbox := by
  intro k j hkj
  have hkj' : (k : ℝ) + 2 ≤ (j : ℝ) + 2 := by
    have h : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hle1 : 1 / ((j : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) := one_div_le_one_div_of_le hpos hkj'
  intro p hp
  simp only [cbox, Set.mem_prod, Set.mem_Icc] at hp ⊢
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem iUnion_cbox : (⋃ k, cbox k) = Q0 := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    rw [cbox, Set.mem_prod, Set.mem_Icc] at hk
    have hk2 : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    exact ⟨lt_of_lt_of_le hk2 hk.1.1, lt_of_lt_of_le hk2 hk.2.1,
      lt_of_le_of_lt hk.2.2 (by linarith [hk2])⟩
  · rintro ⟨hz, hθ₁, hθ₂⟩
    have hπ : 0 < π / 2 - p.2 := by linarith [Real.pi_pos]
    obtain ⟨k₁, hk₁⟩ := exists_nat_gt (1 / p.1)
    obtain ⟨k₂, hk₂⟩ := exists_nat_gt p.1
    obtain ⟨k₃, hk₃⟩ := exists_nat_gt (1 / p.2)
    obtain ⟨k₄, hk₄⟩ := exists_nat_gt (1 / (π / 2 - p.2))
    set K : ℕ := max (max k₁ k₃) (max k₂ k₄) with hK
    have h1 : k₁ ≤ K := by rw [hK]; exact le_trans (le_max_left k₁ k₃) (le_max_left _ _)
    have h2 : k₂ ≤ K := by rw [hK]; exact le_trans (le_max_left k₂ k₄) (le_max_right _ _)
    have h3 : k₃ ≤ K := by rw [hK]; exact le_trans (le_max_right k₁ k₃) (le_max_left _ _)
    have h4 : k₄ ≤ K := by rw [hK]; exact le_trans (le_max_right k₂ k₄) (le_max_right _ _)
    have h1' : (k₁ : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
    have h2' : (k₂ : ℝ) ≤ (K : ℝ) := by exact_mod_cast h2
    have h3' : (k₃ : ℝ) ≤ (K : ℝ) := by exact_mod_cast h3
    have h4' : (k₄ : ℝ) ≤ (K : ℝ) := by exact_mod_cast h4
    have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    refine Set.mem_iUnion.mpr ⟨K, ?_⟩
    rw [cbox, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [div_le_iff₀ hK2]
      have hlt : 1 / p.1 < (K : ℝ) + 2 := by linarith
      rw [div_lt_iff₀ hz] at hlt
      nlinarith [hlt]
    · linarith
    · rw [div_le_iff₀ hK2]
      have hlt : 1 / p.2 < (K : ℝ) + 2 := by linarith
      rw [div_lt_iff₀ hθ₁] at hlt
      nlinarith [hlt]
    · have hle : 1 / ((K : ℝ) + 2) ≤ π / 2 - p.2 := by
        rw [div_le_iff₀ hK2]
        have hlt : 1 / (π / 2 - p.2) < (K : ℝ) + 2 := by linarith
        rw [div_lt_iff₀ hπ] at hlt
        nlinarith [hlt]
      linarith

theorem cbox_subset_Q0 (k : ℕ) : cbox k ⊆ Q0 := fun _ hp => by
  rw [← iUnion_cbox]
  exact Set.mem_iUnion.mpr ⟨k, hp⟩

theorem isCompact_cbox (k : ℕ) : IsCompact (cbox k) := isCompact_Icc.prod isCompact_Icc

/-! ## The box bound for the measurable majorant -/

theorem box_bound {α B : ℝ}
    {G : ℕ → ℝ → ℝ → ℝ} {Φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Q0)
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G (Φ n)))
    (hbsq : ∀ n : ℕ, Work.Spaces.HkSq α 6 (G (Φ n)) ≤ B ^ 2)
    {a b c d ε ε' : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hd : d < π / 2) (hε : 0 < ε) (hε' : 0 < ε')
    (hlo : 0 < a - ε) (hcε : 0 < c - ε') (hdε : d + ε' < π / 2)
    (hc2 : 0 < c - ε' - ε') (hd2 : d + ε' + ε' < π / 2) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
        (V5 α (fun n => G (Φ n)) p + (V6z α f p + V6t α f p))
      ≤ ENNReal.ofReal (B ^ 2) := by
  classical
  have hC'Q : Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε') ⊆ Q0 := box_subset_Q0 ha hcε hdε
  have hDzQ : Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε') ⊆ Q0 :=
    box_subset_Q0 hlo hcε hdε
  have hDtQ : Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε') ⊆ Q0 :=
    box_subset_Q0 ha hc2 hd2
  have hDQ : Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε') ⊆ Q0 :=
    box_subset_Q0 hlo hc2 hd2
  have hcontF : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Q0 :=
    fun n j i => continuousOn_mixed_Q0 (fun k => hsm (Φ n) k) j i
  have hf5 : ∀ (j i : ℕ), j + i = 5 → AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (MeasureTheory.volume.restrict Q0) :=
    fun j i hji => aemeasurable_mixed_five hcontF hconv5 hji
  -- inclusions between the various boxes
  have hC'D : Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')
      ⊆ Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε') :=
    Set.prod_mono (Set.Icc_subset_Icc (by linarith) (by linarith))
      (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hDzD : Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')
      ⊆ Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε') :=
    Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hDtD : Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')
      ⊆ Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε') :=
    Set.prod_mono (Set.Icc_subset_Icc (by linarith) (by linarith)) subset_rfl
  have hKmono : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε') :=
    Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) (by linarith))
  -- measurability of the majorant on the box used for `V5`/`V6z`
  have hV5m : AEMeasurable (V5 α (fun n => G (Φ n)))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε'))) := by
    show AEMeasurable (fun p : ℝ × ℝ => Filter.liminf (fun n : ℕ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2)) Filter.atTop)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')))
    exact AEMeasurable.liminf (fun n => aemeasurable_ofReal_HkIntegrand
      (α := α) (k := 5) (fun j i => (hcontF n j i).mono hC'Q) ha hcε hdε)
  have hV6m : AEMeasurable (V6z α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε'))) ∧
      AEMeasurable (V6t α f)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε'))) :=
    aemeasurable_V6 (α := α) (f := f) (a := a) (b := b) (c := c - ε') (d := d + ε')
      ha hcε hdε hf5
  -- the three Fatou bounds
  have hV5le : ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
        V5 α (fun n => G (Φ n)) p
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2)) Filter.atTop :=
    lintegral_V5_le_liminf (α := α) (a := a) (b := b) (c := c - ε') (d := d + ε')
      (fun n => aemeasurable_ofReal_HkIntegrand
        (α := α) (k := 5) (fun j i => (hcontF n j i).mono hC'Q) ha hcε hdε)
  have hV6zle : ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')), V6z α f p
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in
            (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2)) Filter.atTop :=
    V6z_box_le (F := fun n => G (Φ n)) (f := f)
      (fun n k => hsm (Φ n) k) hcontF hconv5 hab hcd hε hε' hlo hcε hdε
  have hV6tle : ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')), V6t α f p
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in
            (Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
          ENNReal.ofReal (level6T α (G (Φ n)) p.1 p.2)) Filter.atTop :=
    V6t_box_le (F := fun n => G (Φ n)) (f := f) (a := a) (b := b) (c := c - ε')
      (d := d + ε') (ε' := ε') (fun n k => hsm (Φ n) k) hcontF hconv5 hab
      (by linarith) hε' ha hc2 hd2
  -- the per-`n` bound on the common box
  have hpointwise : ∀ n : ℕ,
      (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2))
        + ((∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
              ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2))
          + (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
              ENNReal.ofReal (level6T α (G (Φ n)) p.1 p.2)))
      ≤ ∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) p.1 p.2) := by
    intro n
    have h5mD : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2))
        (MeasureTheory.volume.restrict
          (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε'))) :=
      aemeasurable_ofReal_HkIntegrand (α := α) (k := 5)
        (fun j i => (hcontF n j i).mono hDQ) hlo hc2 hd2
    have hZmD : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2))
        (MeasureTheory.volume.restrict
          (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε'))) :=
      (aemeasurable_ofReal_level6 (α := α) (g := G (Φ n))
        (fun j i => (hcontF n j i).mono hDQ) hlo hc2 hd2).1
    rw [lintegral_HkIntegrand_six_split h5mD hZmD]
    exact add_le_add (lintegral_mono_set hC'D)
      (add_le_add (lintegral_mono_set hDzD) (lintegral_mono_set hDtD))
  -- the per-`n` bound by the energy of the sequence member
  have hrle : ∀ n : ℕ,
      (∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) p.1 p.2))
      ≤ ENNReal.ofReal (B ^ 2) := by
    intro n
    have hDsub : Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')
        ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
      refine Set.prod_mono (fun z hz => le_trans (le_of_lt hlo) hz.1)
        (Set.Icc_subset_Icc (by linarith) (by linarith))
    have hpr : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        = MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.prod_restrict, ← Measure.volume_eq_prod]
    have h1 : (∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) p.1 p.2))
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) z θ) := by
      refine le_trans (lintegral_mono_set hDsub) ?_
      rw [← hpr]
      exact MeasureTheory.lintegral_prod_le _
    have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) z θ))
        = ENNReal.ofReal (Work.Spaces.HkSq α 6 (G (Φ n))) := by
      have hinner : ∀ z ∈ Work.Spaces.Iz,
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 (G (Φ n)) z θ))
            = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 6 (G (Φ n)) z θ) := fun z hz =>
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n).1 z hz)
          (Filter.Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α 6 (G (Φ n)) z θ)).symm
      have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
      rw [setLIntegral_congr_fun (s := Work.Spaces.Iz) hIz hinner]
      rw [Work.Spaces.HkSq]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem n).2
        (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 6 (G (Φ n)) z θ)).symm
    exact h1.trans (h3.trans_le (ENNReal.ofReal_le_ofReal (hbsq n)))
  -- assembly
  refine le_trans (lintegral_mono_set hKmono) ?_
  rw [lintegral_add_left' hV5m, lintegral_add_left' hV6m.1]
  refine le_trans (add_le_add hV5le (add_le_add hV6zle hV6tle)) ?_
  refine le_trans ?_ (Filter.liminf_le_of_frequently_le' (f := Filter.atTop)
    (Filter.Frequently.of_forall fun n => (hpointwise n).trans (hrle n)))
  calc Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2)) Filter.atTop
        + (Filter.liminf (fun n : ℕ => ∫⁻ p in
              (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
            ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2)) Filter.atTop
          + Filter.liminf (fun n : ℕ => ∫⁻ p in
              (Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
            ENNReal.ofReal (level6T α (G (Φ n)) p.1 p.2)) Filter.atTop)
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2)) Filter.atTop
        + Filter.liminf (fun n : ℕ =>
            (∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
              ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2))
            + (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
              ENNReal.ofReal (level6T α (G (Φ n)) p.1 p.2))) Filter.atTop :=
        add_le_add le_rfl (liminf_add_le_ennreal _ _)
    _ ≤ Filter.liminf (fun n : ℕ =>
          (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (G (Φ n)) p.1 p.2))
          + ((∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
              ENNReal.ofReal (level6Z α (G (Φ n)) p.1 p.2))
            + (∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε' - ε') (d + ε' + ε')),
              ENNReal.ofReal (level6T α (G (Φ n)) p.1 p.2)))) Filter.atTop :=
        liminf_add_le_ennreal _ _

end Work.FTS.StrongEps.LocUnif
