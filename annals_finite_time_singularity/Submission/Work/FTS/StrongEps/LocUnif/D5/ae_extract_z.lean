import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.LocUnif.D5.subseq_tendsto_ae_of_cauchy_L1
import Submission.Work.FTS.StrongEps.LocUnif.D5.slice_interval_tendsto_of_L1
import Submission.Work.FTS.StrongEps.LocUnif.D5.ae_integrableOn_slice_of_bounds
import Submission.Work.FTS.StrongEps.LocUnif.D5.ae_limit_eq_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Extraction of an a.e.-convergent subsequence of the `∂_z`-family (1-D engine)

`Work.FTS.StrongEps.LocUnif.D5.ae_extract_z`: from a sequence `L n` with a uniform Cauchy bound
in weighted `L¹` for the first `z`-derivatives, uniform convergence to `Llim`, and `L²` bounds on
the first derivatives, extract a subsequence along which `∂_z (L n)` converges a.e. to the
(totalised) `z`-derivative of `Llim`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- Uniform convergence is preserved by passing to a subsequence. -/
theorem tendstoUniformlyOn_subseq {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β}
    {s : Set α} {ν : ℕ → ℕ} (hν : StrictMono ν)
    (h : TendstoUniformlyOn F f Filter.atTop s) :
    TendstoUniformlyOn (fun n => F (ν n)) f Filter.atTop s := by
  intro u hu
  exact (hν.tendsto_atTop.eventually (h u hu))

theorem ae_extract_z {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hc : 0 < c) (hcd : c < d) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcontdz : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hslice : ∀ n, ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => L n z θ) (Set.Ioo a₀ b₀))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε)
    (h1 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
        Filter.Tendsto (fun n => Work.Spaces.pz (L (φ' n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.pz Llim p.1 p.2)) := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have ha₀b₀ : a₀ ≤ b₀ := le_of_lt (lt_trans ha₀a (lt_trans hab hbb₀))
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩
  -- the clamped family: globally continuous, agreeing with `∂_z (L n)` on the box
  set Wc : ℕ → ℝ × ℝ → ℝ := fun n p =>
    Work.Spaces.pz (L n) (Set.projIcc a₀ b₀ ha₀b₀ p.1) (Set.projIcc c d hcd' p.2) with hWcdef
  have hWccont : ∀ n, Continuous (fun p : ℝ × ℝ => Wc n p) := by
    intro n
    have h1a : Continuous fun p : ℝ × ℝ =>
        ((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := a₀) (b := b₀) (h := ha₀b₀)).comp continuous_fst)
    have h1b : Continuous fun p : ℝ × ℝ => ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ) :=
      continuous_subtype_val.comp
        ((continuous_projIcc (a := c) (b := d) (h := hcd')).comp continuous_snd)
    have h1 : Continuous fun p : ℝ × ℝ =>
        (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := h1a.prodMk h1b
    have h2 : ∀ p : ℝ × ℝ,
        (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
         ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      fun p => Set.mem_prod.mpr ⟨(Set.projIcc a₀ b₀ ha₀b₀ p.1).2, (Set.projIcc c d hcd' p.2).2⟩
    have h4 : (fun p : ℝ × ℝ => Wc n p) = (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2) ∘
        fun p : ℝ × ℝ =>
          (((Set.projIcc a₀ b₀ ha₀b₀ p.1 : Set.Icc a₀ b₀) : ℝ),
           ((Set.projIcc c d hcd' p.2 : Set.Icc c d) : ℝ)) := by
      funext p
      simp only [Function.comp_apply, hWcdef]
    rw [h4]
    exact (hcontdz n).comp_continuous h1 h2
  have hWceq : ∀ n, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      Wc n p = Work.Spaces.pz (L n) p.1 p.2 := by
    intro n p hp
    simp only [hWcdef, Set.projIcc_of_mem ha₀b₀ (⟨by linarith [hp.1.1, ha₀a],
      by linarith [hp.1.2, hbb₀]⟩ : p.1 ∈ Set.Icc a₀ b₀),
      Set.projIcc_of_mem hcd' hp.2, Subtype.coe_mk]
  have hWcaesm : ∀ n, AEStronglyMeasurable (Wc n) (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun n => (hWccont n).aestronglyMeasurable
  have hcauchy' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |Wc n x - Wc m x| ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
        ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    have h1c : (fun x : ℝ × ℝ => ENNReal.ofReal |Wc n x - Wc m x|)
        =ᵐ[volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)]
        (fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|) := by
      refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
      simp only [hWceq n p hp, hWceq m p hp]
    rw [lintegral_congr_ae h1c]
    exact hN n m hn hm
  obtain ⟨φ, hφ, w, hwmeas, hae, hL1⟩ :=
    subseq_tendsto_ae_of_cauchy_L1 (μ := volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      hWcaesm hcauchy'
  have hL1tend : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |Wc (φ k) p - w p|) Filter.atTop (nhds 0) := by
    rw [tendsto_order]
    refine ⟨fun b hb => absurd hb (not_lt.mpr (zero_le : (0 : ℝ≥0∞) ≤ b)), fun b hb => ?_⟩
    obtain ⟨ε, hεpos, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < b := by
      obtain ⟨q, -, hqpos, hqb⟩ := (ENNReal.lt_iff_exists_real_btwn (a := 0) (b := b)).mp hb
      exact ⟨q, ENNReal.ofReal_pos.mp hqpos, hqb⟩
    obtain ⟨K, hK⟩ := hL1 ε hεpos
    refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
    exact lt_of_le_of_lt (hK k hk) hεb
  have hL1tend' : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      ENNReal.ofReal |(fun z θ => Wc (φ k) (z, θ)) p.1 p.2 - (fun z θ => w (z, θ)) p.1 p.2|)
      Filter.atTop (nhds 0) := hL1tend
  obtain ⟨ψ, hψ, hsliceconv⟩ :=
    slice_interval_tendsto_of_L1 (W := fun k z θ => Wc (φ k) (z, θ))
      (w := fun z θ => w (z, θ)) hab' hcd'
      (fun k => (hWccont (φ k)).aemeasurable)
      hwmeas.aemeasurable hL1tend'
  have hsliceconv' : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)), ∀ z ∈ Set.Icc a b,
      ∀ z₀ ∈ Set.Icc a b,
      Filter.Tendsto (fun k => ∫ u in z..z₀, Wc (φ (ψ k)) (u, θ)) Filter.atTop
        (nhds (∫ u in z..z₀, w (u, θ))) := by
    filter_upwards [hsliceconv] with θ hθ z hz z₀ hz₀
    exact hθ z hz z₀ hz₀
  have hwint : ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      IntegrableOn (fun z => w (z, θ)) (Set.Icc a b) volume := by
    obtain ⟨K, hK⟩ := hL1 1 one_pos
    have hW2 : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Wc (φ K) p) ^ 2) ≤ ENNReal.ofReal M := by
      have h1c : (fun p : ℝ × ℝ => ENNReal.ofReal ((Wc (φ K) p) ^ 2))
          =ᵐ[volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)]
          (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pz (L (φ K)) p.1 p.2) ^ 2)) := by
        refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
        simp only [hWceq (φ K) p hp]
      rw [lintegral_congr_ae h1c]
      refine le_trans (MeasureTheory.lintegral_mono_set ?_) (h1 (φ K))
      exact Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    have hdiff : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Wc (φ K) p - w p| ≤ ENNReal.ofReal 1 := hK K le_rfl
    exact ae_integrableOn_slice_of_bounds (W := fun z θ => Wc (φ K) (z, θ))
      (w := fun z θ => w (z, θ)) hab' hcd' hM zero_le_one
      ((hWccont (φ K)).aemeasurable) hwmeas.aemeasurable hW2 hdiff
  have hident := ae_limit_eq_deriv (L := fun k => L (φ (ψ k))) (Llim := Llim)
    (W := fun k => Wc (φ (ψ k))) (w := w) ha₀ ha₀a hab hbb₀ hcd
    (fun k => hcont (φ (ψ k)))
    (fun k θ hθ => hslice (φ (ψ k)) θ hθ)
    (fun k p hp => hWceq (φ (ψ k)) p hp)
    (tendstoUniformlyOn_subseq (hφ.comp hψ) hconv)
    hwmeas hsliceconv' hwint
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  filter_upwards [hae, hident, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)]
    with p hp1 hp2 hpbox
  have hp1' : Filter.Tendsto (fun k => Wc (φ (ψ k)) p) Filter.atTop (nhds (w p)) :=
    hp1.comp (hψ.tendsto_atTop)
  rw [hp2] at hp1'
  refine hp1'.congr' (Filter.Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]
  exact hWceq (φ (ψ k)) p hpbox

/-! ## The `θ`-direction engine

The same extraction with the two coordinate boxes exchanged: the `z`-family `pz (L n)` becomes
the `θ`-family `pth (L n)`, the data box `Icc a b ×ˢ Icc c₀ d₀` becomes `Icc c₀ d₀ ×ˢ Icc a b`
and the conclusion box `Icc a b ×ˢ Icc c d` becomes `Icc c d ×ˢ Icc a b`.  The proof is a
transposition of `ae_extract_z` along the measure-preserving involution `Prod.swap` (whose
measure-preservation on the boxes is `Measure.prod_swap`). -/

/-- `Prod.swap` sends the measure of the rectangle `[a,b] × [c,d]` to that of the rectangle
`[c,d] × [a,b]`. -/
lemma map_swap_box (a b c d : ℝ) :
    Measure.map Prod.swap (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      = volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) := by
  have h₁ : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)) := by
    have h : (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) : Measure (ℝ × ℝ))
        = (volume.prod volume).restrict (Set.Icc a b ×ˢ Set.Icc c d) :=
      congrArg (fun (m : Measure (ℝ × ℝ)) => m.restrict (Set.Icc a b ×ˢ Set.Icc c d))
        (Measure.volume_eq_prod ℝ ℝ)
    rw [h, Measure.prod_restrict]
  have h₂ : (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Icc a b)) := by
    have h : (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b) : Measure (ℝ × ℝ))
        = (volume.prod volume).restrict (Set.Icc c d ×ˢ Set.Icc a b) :=
      congrArg (fun (m : Measure (ℝ × ℝ)) => m.restrict (Set.Icc c d ×ˢ Set.Icc a b))
        (Measure.volume_eq_prod ℝ ℝ)
    rw [h, Measure.prod_restrict]
  rw [h₁, h₂, Measure.prod_swap]

/-- The `lintegral` over the swapped rectangle, pulled back along `Prod.swap`. -/
lemma lintegral_swap_box {a b c d : ℝ} (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, f p
      = ∫⁻ q in Set.Icc c d ×ˢ Set.Icc a b, f (Prod.swap q) := by
  have hmp : MeasurePreserving Prod.swap
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b))
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ⟨measurable_swap, map_swap_box c d a b⟩
  have hg : (⇑(MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)) = Prod.swap := by
    funext p
    rfl
  have h := hmp.lintegral_map_equiv f MeasurableEquiv.prodComm
  rw [hg] at h
  exact h

theorem ae_extract_theta {a b c c₀ d d₀ M : ℝ} (ha : 0 < a) (hab : a < b)
    (hc₀ : 0 < c₀) (hc₀c : c₀ < c) (hcd : c < d) (hdd₀ : d < d₀) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcontth : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hslice : ∀ n, ∀ z ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun θ => L n z θ) (Set.Ioo c₀ d₀))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a b ×ˢ Set.Icc c₀ d₀))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε)
    (h1 : ∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c₀ d₀,
        ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)),
        Filter.Tendsto (fun n => Work.Spaces.pth (L (φ' n)) p.1 p.2) Filter.atTop
          (nhds (Work.Spaces.pth Llim p.1 p.2)) := by
  classical
  have hcont' : ∀ n, ContinuousOn (fun p : ℝ × ℝ => L n p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := fun n =>
    (hcont n).comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hcontdz' : ∀ n, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (L n) p.2 p.1)
      (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := fun n =>
    (hcontth n).comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hslice' : ∀ n, ∀ y ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun x => L n y x) (Set.Ioo c₀ d₀) :=
    fun n y hy => hslice n y hy
  have hconv' : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.2 p.1) (fun p => Llim p.2 p.1)
      Filter.atTop (Set.Icc c₀ d₀ ×ˢ Set.Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn p hp
    exact hn (Prod.swap p) ⟨hp.2, hp.1⟩
  have hcauchy' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc c d ×ˢ Set.Icc a b,
        ENNReal.ofReal
          |Work.Spaces.pth (L n) p.2 p.1 - Work.Spaces.pth (L m) p.2 p.1|
          ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n m hn hm => ?_⟩
    have hgoal : ∫⁻ q in Set.Icc c d ×ˢ Set.Icc a b,
        (fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|) (Prod.swap q)
        ≤ ENNReal.ofReal ε := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c) (d := d)
        (f := fun p : ℝ × ℝ => ENNReal.ofReal
          |Work.Spaces.pth (L n) p.1 p.2 - Work.Spaces.pth (L m) p.1 p.2|)]
      exact hN n m hn hm
    exact hgoal
  have h1' : ∀ n, ∫⁻ p in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
      ENNReal.ofReal ((Work.Spaces.pth (L n) p.2 p.1) ^ 2) ≤ ENNReal.ofReal M := by
    intro n
    have hgoal : ∫⁻ q in Set.Icc c₀ d₀ ×ˢ Set.Icc a b,
        (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2))
          (Prod.swap q) ≤ ENNReal.ofReal M := by
      rw [← lintegral_swap_box (a := a) (b := b) (c := c₀) (d := d₀)
        (f := fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth (L n) p.1 p.2) ^ 2))]
      exact h1 n
    exact hgoal
  obtain ⟨φ', hφ', hae⟩ :=
    ae_extract_z (L := fun n x y => L n y x) (Llim := fun x y => Llim y x)
      (a := c) (b := d) (a₀ := c₀) (b₀ := d₀) (c := a) (d := b) (M := M)
      hc₀ hc₀c hcd hdd₀ ha hab hM hcont' hcontdz' hslice' hconv' hcauchy' h1'
  refine ⟨φ', hφ', ?_⟩
  have hmp : MeasurePreserving Prod.swap
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b)) :=
    ⟨measurable_swap, map_swap_box a b c d⟩
  rw [MeasureTheory.ae_iff] at hae ⊢
  exact hmp.preimage_null hae

end Work.FTS.StrongEps.LocUnif.D5
