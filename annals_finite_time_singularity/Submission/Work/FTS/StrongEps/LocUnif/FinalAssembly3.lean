import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.V5Defs
import Submission.Work.FTS.StrongEps.LocUnif.V6Defs
import Submission.Work.FTS.StrongEps.LocUnif.V5_eq_ae
import Submission.Work.FTS.StrongEps.LocUnif.ofReal_HkIntegrand_six_le
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_ofReal_HkIntegrand
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_V6
import Submission.Work.FTS.StrongEps.LocUnif.FinalAssembly
import Submission.Work.FTS.StrongEps.LocUnif.FinalAssembly2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The energy bound `HkSq α 6 f ≤ B ^ 2`

Final step of the energy half of `Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6`.

With `Vtot = V5 + (V6z + V6t)` the (a.e. measurable) majorant of
`ofReal ∘ HkIntegrand α 6 f`:

* `Vtot` is a.e. measurable on `Q0` (glued from the boxes `cbox k`) and on the closed quadrant
  `Iz ×ˢ Iθ` (`Q0` and `Iz ×ˢ Iθ` differ by three coordinate lines);
* `∫⁻_{Q0} Vtot ≤ ofReal (B ^ 2)` by the monotone exhaustion `Q0 = ⋃ k, cbox k` and the box
  bound `box_bound` for each `cbox k`;
* the pointwise a.e. majorisation is sliced (`Measure.ae_ae_of_ae_prod`) and integrated, and
  Tonelli (`Measure.setLIntegral_prod`) turns the iterated integral into the two-dimensional one;
* finally the Bochner integral defining `HkSq` is compared with the iterated lintegral, the
  `z`-slice of `HkIntegrand α 6 f` being handled by a case split on its integrability.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The measurable majorant of `ofReal ∘ HkIntegrand α 6 f`: the level `≤ 5` part handled by
Fatou along the sequence plus the two difference-quotient majorants of the level-6 slots. -/
def Vtot (α : ℝ) (F : ℕ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  V5 α F p + (V6z α f p + V6t α f p)

/-- `Vtot` is a.e. measurable on each box `cbox k`. -/
theorem aemeasurable_Vtot_cbox {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hcontF : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2) Q0)
    (hf5 : ∀ (j i : ℕ), j + i = 5 → AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (MeasureTheory.volume.restrict Q0)) (k : ℕ) :
    AEMeasurable (Vtot α F f) (MeasureTheory.volume.restrict (cbox k)) := by
  have ht : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  have hd1 : π / 2 - 1 / ((k : ℝ) + 2) < π / 2 := by linarith
  have h1 : AEMeasurable (V5 α F) (MeasureTheory.volume.restrict (cbox k)) := by
    show AEMeasurable (fun p : ℝ × ℝ => Filter.liminf (fun n : ℕ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (F n) p.1 p.2)) Filter.atTop)
      (MeasureTheory.volume.restrict (cbox k))
    exact AEMeasurable.liminf (fun n => aemeasurable_ofReal_HkIntegrand
      (α := α) (k := 5) (fun j i => (hcontF n j i).mono (cbox_subset_Q0 k)) ht ht hd1)
  have h2 := aemeasurable_V6 (α := α) (f := f) (a := 1 / ((k : ℝ) + 2))
    (b := (k : ℝ) + 2) (c := 1 / ((k : ℝ) + 2)) (d := π / 2 - 1 / ((k : ℝ) + 2))
    ht ht hd1 hf5
  show AEMeasurable (fun p : ℝ × ℝ =>
    V5 α F p + (V6z α f p + V6t α f p)) (MeasureTheory.volume.restrict (cbox k))
  exact h1.add (h2.1.add h2.2)

/-- `Iz ×ˢ Iθ` and `Q0` differ by three coordinate lines, hence by a null set. -/
theorem volume_Iz_prod_Iθ_sdiff_Q0 :
    MeasureTheory.volume (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ \ Q0 : Set (ℝ × ℝ)) = 0 := by
  have hLz : MeasureTheory.volume ({0} ×ˢ (Set.univ : Set ℝ) : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hL0 : MeasureTheory.volume ((Set.univ : Set ℝ) ×ˢ {0} : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hLpi : MeasureTheory.volume
      ((Set.univ : Set ℝ) ×ˢ ({π / 2} : Set ℝ) : Set (ℝ × ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hsub : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ \ Q0 : Set (ℝ × ℝ)) ⊆
      ({0} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ {0}) ∪
        ((Set.univ : Set ℝ) ×ˢ {π / 2}) := by
    rintro p hp
    obtain ⟨⟨hz, hθ⟩, hQ⟩ := hp
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hQ
    simp only [Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true,
      true_and]
    rcases eq_or_lt_of_le hz with h | h
    · exact Or.inl (Or.inl h.symm)
    · rcases eq_or_lt_of_le hθ.1 with h2 | h2
      · exact Or.inl (Or.inr h2.symm)
      · rcases lt_or_eq_of_le hθ.2 with h3 | h3
        · exact absurd ⟨h, h2, h3⟩ hQ
        · exact Or.inr h3
  exact measure_mono_null hsub (measure_union_null (measure_union_null hLz hL0) hLpi)

theorem restrict_Iz_prod_Iθ_eq_restrict_Q0 :
    MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict Q0 := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨volume_Iz_prod_Iθ_sdiff_Q0, ?_⟩
  rw [Set.sdiff_eq_empty.mpr ?_]
  · simp
  · rintro ⟨z, θ⟩ hp
    rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    obtain ⟨hz, hθ1, hθ2⟩ := hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Work.Spaces.Iz]; exact le_of_lt hz
    · rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ1, le_of_lt hθ2⟩

/-- **The energy bound.**  The `H ^ 6`-energy of the limit is bounded by `B ^ 2`. -/
theorem HkSq_le {α B : ℝ} {G : ℕ → ℝ → ℝ → ℝ} {Φ : ℕ → ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Q0)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G (Φ n)))
    (hbsq : ∀ n : ℕ, Work.Spaces.HkSq α 6 (G (Φ n)) ≤ B ^ 2) :
    Work.Spaces.HkSq α 6 f ≤ B ^ 2 := by
  classical
  have hcontF : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (G (Φ n)) p.1 p.2) Q0 :=
    fun n j i => continuousOn_mixed_Q0 (fun k => hsm (Φ n) k) j i
  have hf5 : ∀ (j i : ℕ), j + i = 5 → AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (MeasureTheory.volume.restrict Q0) :=
    fun j i hji => aemeasurable_mixed_five hcontF hconv5 hji
  have hmeasQ0 : AEMeasurable (Vtot α (fun n => G (Φ n)) f)
      (MeasureTheory.volume.restrict Q0) := by
    rw [← iUnion_cbox]
    exact aemeasurable_iUnion_iff.mpr fun k =>
      aemeasurable_Vtot_cbox (α := α) hcontF hf5 k
  have hmeasIz : AEMeasurable (Vtot α (fun n => G (Φ n)) f)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [restrict_Iz_prod_Iθ_eq_restrict_Q0]; exact hmeasQ0
  -- the bound on the open quadrant
  have hbox : ∀ k : ℕ, ∫⁻ p in cbox k, Vtot α (fun n => G (Φ n)) f p
      ≤ ENNReal.ofReal (B ^ 2) := by
    intro k
    have ht : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hlt2 : 1 / ((k : ℝ) + 2) < (k : ℝ) + 2 := by
      have h2 : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
        linarith
      linarith
    have hltpi : 1 / ((k : ℝ) + 2) < π / 2 - 1 / ((k : ℝ) + 2) := by
      have h2 : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)]
        linarith
      linarith [Real.pi_gt_three]
    have hd1 : π / 2 - 1 / ((k : ℝ) + 2) < π / 2 := by linarith
    exact box_bound (α := α) (B := B) (G := G) (Φ := Φ) (f := f) hsm hconv5 hmem hbsq
      (a := 1 / ((k : ℝ) + 2)) (b := (k : ℝ) + 2) (c := 1 / ((k : ℝ) + 2))
      (d := π / 2 - 1 / ((k : ℝ) + 2)) (ε := (1 / ((k : ℝ) + 2)) / 2)
      (ε' := (1 / ((k : ℝ) + 2)) / 4)
      ht hlt2 ht hltpi hd1 (by positivity) (by positivity)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hQ0bound : ∫⁻ p in Q0, Vtot α (fun n => G (Φ n)) f p ≤ ENNReal.ofReal (B ^ 2) := by
    rw [← iUnion_cbox]
    rw [setLIntegral_iUnion_of_directed (s := cbox)
      (Vtot α (fun n => G (Φ n)) f) cbox_mono.directed_le]
    exact iSup_le hbox
  have h2D : ∫⁻ p in (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ),
      Vtot α (fun n => G (Φ n)) f p ≤ ENNReal.ofReal (B ^ 2) := by
    rw [restrict_Iz_prod_Iθ_eq_restrict_Q0]; exact hQ0bound
  -- the a.e. majorisation, first on the quadrant, then sliced
  have hperk : ∀ k : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict (cbox k)),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        ≤ Vtot α (fun n => G (Φ n)) f p := by
    intro k
    have ht : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
    have hd1 : π / 2 - 1 / ((k : ℝ) + 2) < π / 2 := by linarith
    have hV5 : V5 α (fun n => G (Φ n)) =ᵐ[MeasureTheory.volume.restrict (cbox k)]
        (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)) :=
      V5_eq_ae (α := α) (fn := fun n => G (Φ n)) (f := f) (a := 1 / ((k : ℝ) + 2))
        (b := (k : ℝ) + 2) (c := 1 / ((k : ℝ) + 2)) (d := π / 2 - 1 / ((k : ℝ) + 2))
        (fun p hp j i hji => (hconv4 j i hji (cbox k) (isCompact_cbox k)
          (cbox_subset_Q0 k)).tendsto_at hp)
        (ae_restrict_box (a := 1 / ((k : ℝ) + 2)) (b := (k : ℝ) + 2)
          (c := 1 / ((k : ℝ) + 2)) (d := π / 2 - 1 / ((k : ℝ) + 2)) ht ht hd1 hconv5)
    filter_upwards [hV5] with p hp
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2) + V6z α f p + V6t α f p :=
          ofReal_HkIntegrand_six_le α f p
      _ = V5 α (fun n => G (Φ n)) p + (V6z α f p + V6t α f p) := by
          rw [← hp, add_assoc]
  have haeQ0 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        ≤ Vtot α (fun n => G (Φ n)) f p := by
    rw [← iUnion_cbox]
    exact (ae_restrict_iUnion_iff cbox (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        ≤ Vtot α (fun n => G (Φ n)) f p)).mpr hperk
  have haeIz : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
        ≤ Vtot α (fun n => G (Φ n)) f p := by
    rw [restrict_Iz_prod_Iθ_eq_restrict_Q0]; exact haeQ0
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f z θ)
          ≤ Vtot α (fun n => G (Φ n)) f (z, θ) := by
    have hpr : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hae' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
          ≤ Vtot α (fun n => G (Φ n)) f p := by
      rw [← hpr]; exact haeIz
    exact Measure.ae_ae_of_ae_prod hae'
  -- the iterated bound
  have hiter : ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f z θ) ≤ ENNReal.ofReal (B ^ 2) := by
    have hmono : ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            Vtot α (fun n => G (Φ n)) f (z, θ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hslice] with z hz
      exact lintegral_mono_ae hz
    have hton : ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          Vtot α (fun n => G (Φ n)) f (z, θ)
        = ∫⁻ p in (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ), Vtot α (fun n => G (Φ n)) f p :=
      (setLIntegral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (Vtot α (fun n => G (Φ n)) f)
        hmeasIz).symm
    exact hmono.trans (hton ▸ h2D)
  by_cases hint : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz
  · have h1 : Work.Spaces.HkSq α 6 f
        = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)).toReal := by
      rw [Work.Spaces.HkSq]
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 6 f z θ) hint.aestronglyMeasurable
    have hpt : ∀ z : ℝ, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f z θ) := by
      intro z
      by_cases hz : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ
      · exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hz
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ))
      · rw [integral_undef hz]; simp
    rw [h1]
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)).toReal
        ≤ (ENNReal.ofReal (B ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top ((lintegral_mono hpt).trans hiter)
      _ = B ^ 2 := ENNReal.toReal_ofReal (sq_nonneg B)
  · have h0 : Work.Spaces.HkSq α 6 f = 0 := by
      rw [Work.Spaces.HkSq]
      exact integral_undef hint
    rw [h0]
    exact sq_nonneg B

end Work.FTS.StrongEps.LocUnif
