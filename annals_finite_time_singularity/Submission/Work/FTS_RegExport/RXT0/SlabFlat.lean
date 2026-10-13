import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.slabC1Flat`

An abstract regularity export on the slab `(0,∞) × (0,π/2) × [0,S]`.

If `f z θ τ = f z θ 0 + ∫_σ A z θ σ` on the slab, if the `(z,θ)`-slices `(z,θ) ↦ f z θ τ` are
Fréchet differentiable with derivative `L (z,θ,τ)`, and if `A` and `L` are continuous on the slab,
then `(z,θ,τ) ↦ f z θ τ` is `C¹` on the slab and the `τ`-derivative of `s ↦ f z θ s` is
`A z θ τ`.

The proof decomposes `f z θ τ = φ(z,θ) + ∫_{τ₀}^{τ} A z θ σ` on the slab (with `φ` the `τ₀`-slice
of `f`, `τ₀` being the base point), differentiates the two summands and adds.  The `(z,θ)`-part is
exactly the hypothesis `hd`; the integral part is differentiable because it is `o` in the `(z,θ)`
directions and its `τ`-derivative is the (continuous) integrand.
-/

open scoped Real Topology ContDiff
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

/-- The slab `(0,∞) × (0,π/2) × [0,S]`. -/
def SlabF (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

lemma mem_Slab {S : ℝ} {y : ℝ × ℝ × ℝ} :
    y ∈ SlabF S ↔
      0 < y.1 ∧ 0 < y.2.1 ∧ y.2.1 < Real.pi / 2 ∧ 0 ≤ y.2.2 ∧ y.2.2 ≤ S := by
  simp [SlabF, and_assoc]

/-- Projection `(z,θ,τ) ↦ (z,θ)`. -/
noncomputable def projZθ : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

/-- Projection `(z,θ,τ) ↦ τ`. -/
noncomputable def projT : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The candidate derivative of `(z,θ,τ) ↦ f z θ τ` at `p`: the `(z,θ)`-part is `L p` and the
`τ`-part is the integrand `A p`. -/
noncomputable def slabD (L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (A : ℝ → ℝ → ℝ → ℝ)
    (p : ℝ × ℝ × ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (L p).comp projZθ + (A p.1 p.2.1 p.2.2) • projT

@[simp] lemma projZθ_apply (v : ℝ × ℝ × ℝ) : projZθ v = (v.1, v.2.1) := rfl
@[simp] lemma projT_apply (v : ℝ × ℝ × ℝ) : projT v = v.2.2 := rfl

lemma uIcc_subset_Icc_of_mem {a b S : ℝ} (ha : a ∈ Set.Icc (0:ℝ) S) (hb : b ∈ Set.Icc (0:ℝ) S) :
    Set.uIcc a b ⊆ Set.Icc (0:ℝ) S := by
  intro σ hσ
  rw [Set.mem_uIcc] at hσ
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans ha.1 h1, le_trans h2 hb.2⟩
  · exact ⟨le_trans hb.1 h1, le_trans h2 ha.2⟩

/-- For `y` in the slab and `t ⊆ [0,S]`, the `σ`-slice `σ ↦ A y.1 y.2.1 σ` is continuous on
`t`. -/
lemma slabA_continuousOn_of_subset {S : ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    {y : ℝ × ℝ × ℝ} (hy : y ∈ SlabF S) {t : Set ℝ} (ht : t ⊆ Set.Icc (0:ℝ) S) :
    ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) t := by
  have hyy := mem_Slab.mp hy
  have hmap : MapsTo (fun σ : ℝ => (y.1, y.2.1, σ)) t (SlabF S) := by
    intro σ hσ
    exact mem_Slab.mpr ⟨hyy.1, hyy.2.1, hyy.2.2.1, (ht hσ).1, (ht hσ).2⟩
  have hcont' := hA.comp (g := fun q : ℝ × ℝ × ℝ => A q.1 q.2.1 q.2.2)
    ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmap
  convert hcont' using 1
  ext σ
  rfl

lemma Ioo_subset_Icc {S : ℝ} : Set.Ioo (0:ℝ) S ⊆ Set.Icc (0:ℝ) S :=
  fun _ hσ => ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩

/-- **The integral part.**  For `A` continuous on the slab and `p` in the slab, the map
`y ↦ ∫_{p.2.2}^{y.2.2} A y.1 y.2.1 σ` has Fréchet derivative `A p • projT` at `p` within the slab:
it is `o` in the `(z,θ)`-directions, and its `τ`-derivative is the integrand. -/
lemma slabIntegral_hasFDerivWithinAt {S : ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => ∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ)
      ((A p.1 p.2.1 p.2.2) • projT) (SlabF S) p := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcont : ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => A q.1 q.2.1 q.2.2) (SlabF S) p :=
    hA.continuousWithinAt hp
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, H⟩ := hcont (c/2) (by linarith)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds p hδ)]
    with y hyT hyball
  rw [Metric.mem_ball] at hyball
  have hyp := mem_Slab.mp hyT
  have hyy := mem_Slab.mp hp
  simp only [Prod.dist_eq] at hyball
  have hd1 : dist y.1 p.1 < δ := (max_lt_iff.mp hyball).1
  have hd2 : max (dist y.2.1 p.2.1) (dist y.2.2 p.2.2) < δ := (max_lt_iff.mp hyball).2
  have hd21 : dist y.2.1 p.2.1 < δ := (max_lt_iff.mp hd2).1
  have hd22 : dist y.2.2 p.2.2 < δ := (max_lt_iff.mp hd2).2
  have hle : |y.2.2 - p.2.2| ≤ ‖y - p‖ := by
    have h1 : ‖(y - p).2.2‖ ≤ ‖y - p‖ :=
      le_trans (norm_snd_le (y - p).2) (norm_snd_le (y - p))
    simpa [Real.norm_eq_abs] using h1
  have hbdd : ∀ σ ∈ Set.uIoc p.2.2 y.2.2, ‖A y.1 y.2.1 σ - A p.1 p.2.1 p.2.2‖ ≤ c/2 := by
    intro σ hσ
    rw [Set.mem_uIoc] at hσ
    have h0σ : 0 ≤ σ := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_trans hyy.2.2.2.1 (le_of_lt h1)
      · exact le_trans hyp.2.2.2.1 (le_of_lt h1)
    have hσS : σ ≤ S := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_trans h2 hyp.2.2.2.2
      · exact le_trans h2 hyy.2.2.2.2
    have habs : |σ - p.2.2| ≤ |y.2.2 - p.2.2| := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have hdistσ : dist (y.1, y.2.1, σ) p < δ := by
      simp only [Prod.dist_eq]
      rw [max_lt_iff]
      refine ⟨hd1, ?_⟩
      rw [max_lt_iff]
      refine ⟨hd21, ?_⟩
      rw [Real.dist_eq]
      exact lt_of_le_of_lt habs (by rwa [Real.dist_eq] at hd22)
    have hmem : (y.1, y.2.1, σ) ∈ SlabF S := mem_Slab.mpr ⟨hyp.1, hyp.2.1, hyp.2.2.1, h0σ, hσS⟩
    have hH := H hmem hdistσ
    rw [Real.dist_eq] at hH
    rw [Real.norm_eq_abs]
    linarith
  have hline : ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) (Set.uIcc p.2.2 y.2.2) :=
    slabA_continuousOn_of_subset hA hyT
      (uIcc_subset_Icc_of_mem ⟨hyy.2.2.2.1, hyy.2.2.2.2⟩ ⟨hyp.2.2.2.1, hyp.2.2.2.2⟩)
  have hint1 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume p.2.2 y.2.2 :=
    hline.intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => A p.1 p.2.1 p.2.2) volume p.2.2 y.2.2 :=
    intervalIntegrable_const
  have heq : (∫ σ in p.2.2..y.2.2, (A y.1 y.2.1 σ - A p.1 p.2.1 p.2.2))
      = (∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ) - A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2) := by
    rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hgoal : ‖(∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ) - A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2)‖
      ≤ c * ‖y - p‖ := by
    rw [← heq]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbdd) ?_
    calc (c/2) * |y.2.2 - p.2.2| ≤ (c/2) * ‖y - p‖ :=
          mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ c * ‖y - p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hKp : (∫ σ in p.2.2..p.2.2, A p.1 p.2.1 σ) = 0 := intervalIntegral.integral_same
  have hf' : ((A p.1 p.2.1 p.2.2) • projT) (y - p) = A p.1 p.2.1 p.2.2 * (y.2.2 - p.2.2) := by
    simp [projT]
  simpa only [hKp, hf', sub_zero] using hgoal

/-- Splitting the integral identity at the base point `p`. -/
lemma slab_split {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    {p y : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) (hy : y ∈ SlabF S) :
    f y.1 y.2.1 y.2.2 = f y.1 y.2.1 p.2.2 + ∫ σ in p.2.2..y.2.2, A y.1 y.2.1 σ := by
  have hyy := mem_Slab.mp hy
  have hypp := mem_Slab.mp hp
  have h1 := hId y.1 y.2.1 y.2.2 hyy.1 hyy.2.1 hyy.2.2.1 hyy.2.2.2.1 hyy.2.2.2.2
  have h2 := hId y.1 y.2.1 p.2.2 hyy.1 hyy.2.1 hyy.2.2.1 hypp.2.2.2.1 hypp.2.2.2.2
  have hcontS : ContinuousOn (fun σ : ℝ => A y.1 y.2.1 σ) (Set.Icc (0:ℝ) S) :=
    slabA_continuousOn_of_subset hA hy (Subset.refl _)
  have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hpI : p.2.2 ∈ Set.Icc (0:ℝ) S := ⟨hypp.2.2.2.1, hypp.2.2.2.2⟩
  have hyI : y.2.2 ∈ Set.Icc (0:ℝ) S := ⟨hyy.2.2.2.1, hyy.2.2.2.2⟩
  have hI1 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume (0:ℝ) p.2.2 :=
    (hcontS.mono (uIcc_subset_Icc_of_mem h0I hpI)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun σ : ℝ => A y.1 y.2.1 σ) volume p.2.2 y.2.2 :=
    (hcontS.mono (uIcc_subset_Icc_of_mem hpI hyI)).intervalIntegrable
  have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  rw [h1, h2, ← hadj]
  ring

/-- The `(z,θ)`-part: the `τ₀`-slice of `f`, lifted to the slab. -/
lemma slab_slice_hasFDerivWithinAt {S : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hd : ∀ p ∈ SlabF S, HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => f y.1 y.2.1 p.2.2)
      ((L p).comp projZθ) (SlabF S) p := by
  refine ((hd p hp).comp p projZθ.hasFDerivAt).hasFDerivWithinAt.congr ?_ ?_
  · intro y hy
    rfl
  · rfl

/-- **Differentiability of `(z,θ,τ) ↦ f z θ τ` on the slab.** -/
lemma slab_hasFDerivWithinAt {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    (hd : ∀ p ∈ SlabF S, HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    {p : ℝ × ℝ × ℝ} (hp : p ∈ SlabF S) :
    HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => f y.1 y.2.1 y.2.2) (slabD L A p) (SlabF S) p := by
  have hsum := (slab_slice_hasFDerivWithinAt hd hp).add (slabIntegral_hasFDerivWithinAt hA hp)
  exact hsum.congr (fun y hy => slab_split hS hA hId hp hy) (slab_split hS hA hId hp hp)

/-- **Continuity of the candidate derivative on the slab.** -/
lemma slabD_continuousOn {S : ℝ} {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hL : ContinuousOn L (SlabF S))
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S)) :
    ContinuousOn (slabD L A) (SlabF S) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (L p).comp projZθ) (SlabF S) :=
    hL.clm_comp (continuousOn_const (c := projZθ))
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (A p.1 p.2.1 p.2.2) • projT) (SlabF S) :=
    hA.smul (continuousOn_const (c := projT))
  unfold slabD
  exact h1.add h2

/-- The `τ`-derivative, from the integral representation (fundamental theorem of calculus). -/
lemma slab_tau_hasDerivAt {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2) (SlabF S))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    {z θ τ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) (hτ : 0 < τ) (hτS : τ < S) :
    HasDerivAt (fun s => f z θ s) (A z θ τ) τ := by
  have hp : (z, θ, τ) ∈ SlabF S :=
    mem_Slab.mpr ⟨hz, hθ, hθ2, le_of_lt hτ, le_of_lt hτS⟩
  have hcIoo : ContinuousOn (fun σ : ℝ => A z θ σ) (Set.Ioo (0:ℝ) S) :=
    slabA_continuousOn_of_subset hA hp Ioo_subset_Icc
  have hcτ : ContinuousAt (fun σ : ℝ => A z θ σ) τ :=
    hcIoo.continuousAt (isOpen_Ioo.mem_nhds ⟨hτ, hτS⟩)
  have hsm : StronglyMeasurableAtFilter (fun σ : ℝ => A z θ σ) (𝓝 τ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcIoo τ ⟨hτ, hτS⟩
  have hII : IntervalIntegrable (fun σ : ℝ => A z θ σ) volume (0:ℝ) τ :=
    (slabA_continuousOn_of_subset hA hp (uIcc_subset_Icc_of_mem ⟨le_refl 0, le_of_lt hS⟩
      ⟨le_of_lt hτ, le_of_lt hτS⟩)).intervalIntegrable
  have hderiv : HasDerivAt (fun s : ℝ => ∫ σ in (0:ℝ)..s, A z θ σ) (A z θ τ) τ :=
    intervalIntegral.integral_hasDerivAt_right hII hsm hcτ
  have hfull : HasDerivAt (fun s : ℝ => f z θ 0 + ∫ σ in (0:ℝ)..s, A z θ σ) (A z θ τ) τ := by
    have h := (hasDerivAt_const τ (f z θ 0)).add hderiv
    rw [zero_add] at h
    exact h
  refine hfull.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨hτ, hτS⟩] with s hs
  exact hId z θ s hz hθ hθ2 (le_of_lt hs.1) (le_of_lt hs.2)

theorem slabC1Flat {S : ℝ} (hS : 0 < S) {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
    {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    (hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ)
    (hd : ∀ p ∈ Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S),
      HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1))
    (hL : ContinuousOn L (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ < S →
      HasDerivAt (fun s => f z θ s) (A z θ τ) τ := by
  constructor
  · rw [show (1 : ℕ∞ω) = (0 : ℕ∞ω) + 1 from (zero_add 1).symm]
    rw [contDiffOn_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := (0 : ℕ∞ω)) (by simp)]
    intro x hx
    refine ⟨SlabF S, ?_, ?_, slabD L A, ?_, ?_⟩
    · rw [insert_eq_of_mem hx]
      exact self_mem_nhdsWithin
    · intro h
      exact absurd h (by simp)
    · intro y hy
      exact slab_hasFDerivWithinAt hS hA hId hd hy
    · rw [contDiffOn_zero]
      exact slabD_continuousOn hL hA
  · intro z θ τ hz hθ hθ2 hτ hτS
    exact slab_tau_hasDerivAt hS hA hId hz hθ hθ2 hτ hτS

end Work.FTS_RegExport.RXT0
