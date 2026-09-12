import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.MeasureTheory.pair_cyl_twoDim_core_upper

set_option maxHeartbeats 1000000
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

noncomputable section

namespace Commons.Analysis.MeasureTheory

/-! # Cylindrical coordinate change of variables on ℝ × W -/

private abbrev cylIt : Type := {t : ℝ // t ∈ Set.Ioo (-1) 1}

/-- positivity: for t ∈ (-1,1), s > 0: 0 < s * sqrt (1 - t^2). -/
private lemma cylSqrt_pos (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) (s : ℝ) (hs : 0 < s) :
    0 < s * Real.sqrt (1 - t ^ 2) := by
  have h1 : -1 < t := ht.1
  have h2 : t < 1 := ht.2
  have hsq : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  exact mul_pos hs (Real.sqrt_pos.2 hsq)

/-- The full cylindrical map. -/
private def cylLambda {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ((cylIt × Metric.sphere (0 : W) 1) × Set.Ioi (0 : ℝ)) → ℝ × W := fun q =>
      (q.2.1 * (q.1.1 : cylIt).1,
        (q.2.1 * Real.sqrt (1 - ((q.1.1 : cylIt).1) ^ 2)) •
          ((q.1.2 : Metric.sphere (0 : W) 1) : W))

/-- ((x,y),z) ↦ ((x,z),y) -/
private def cylE1 (α β γ : Type*) : ((α × β) × γ) → (α × γ) × β :=
  fun q => ((q.1.1, q.2), q.1.2)

/-- ψ : (t,s) ↦ (s t, s √(1-t²)) -/
private def cylPsi : cylIt × Set.Ioi (0 : ℝ) → ℝ × Set.Ioi (0 : ℝ) := fun q =>
  ((q.2 : Set.Ioi (0 : ℝ)).1 * (q.1 : cylIt).1,
    ⟨(q.2 : Set.Ioi (0 : ℝ)).1 * Real.sqrt (1 - ((q.1 : cylIt).1) ^ 2),
      cylSqrt_pos (q.1 : cylIt).1 (q.1.2) (q.2 : Set.Ioi (0 : ℝ)).1 (q.2.2)⟩)

/-- ((x,y),z) ↦ (x,(z,y)) -/
private def cylE2 (α β γ : Type*) : ((α × β) × γ) → α × (γ × β) :=
  fun q => (q.1.1, (q.2, q.1.2))

/-- (ℝ×Ioi)×SW → ℝ×W0, ((a,q),ω) ↦ (a, H⁻¹(ω,q)) -/
private def cylPolar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    (ℝ × Set.Ioi (0 : ℝ)) × Metric.sphere (0 : W) 1 → ℝ × ({0}ᶜ : Set W) := fun q =>
  (q.1.1, (homeomorphUnitSphereProd W).symm (q.2, q.1.2))

/-- ℝ×W0 → ℝ×W -/
private def cylIncl {W : Type*} [NormedAddCommGroup W] :
    ℝ × ({0}ᶜ : Set W) → ℝ × W := fun q => (q.1, (q.2 : W))

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- Λ = incl ∘ polar ∘ (ψ × id) ∘ e1 pointwise. -/
private lemma cylLambda_eq :
    cylLambda (W := W) = cylIncl ∘ cylPolar ∘ (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) ∘
        cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)) := by
  funext q
  rcases q with ⟨⟨t, ω⟩, s⟩
  change (s.1 * (t : ℝ), (s.1 * Real.sqrt (1 - (t : ℝ) ^ 2)) • ((ω : Metric.sphere (0 : W) 1) : W)) =
    (s.1 * (t : ℝ), ((homeomorphUnitSphereProd W).symm
      (ω, ⟨s.1 * Real.sqrt (1 - (t : ℝ) ^ 2), cylSqrt_pos (t : ℝ) t.2 s.1 s.2⟩) : W))
  apply Prod.ext
  · rfl
  · rw [homeomorphUnitSphereProd_symm_apply_coe (E := W)
      (x := (ω, ⟨s.1 * Real.sqrt (1 - (t : ℝ) ^ 2), cylSqrt_pos (t : ℝ) t.2 s.1 s.2⟩))]

/-- `Measure.comap` along the subtype inclusion of a measurable set is s-finite
whenever the original measure is. -/
private lemma cylCoord_sfinite_comap_subtype {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) {μ : Measure α} [SFinite μ] :
    SFinite (μ.comap (Subtype.val : s → α)) := by
  let m : ℕ → Measure s := fun n => (sfiniteSeq μ n).comap (Subtype.val : s → α)
  have hfin : ∀ n, IsFiniteMeasure (m n) := by
    intro n; dsimp [m]; infer_instance
  have hsum : μ.comap (Subtype.val : s → α) = Measure.sum m := by
    ext A hA
    rw [Measure.sum_apply _ hA]
    simp_rw [m]
    rw [show (fun n : ℕ => (sfiniteSeq μ n).comap (Subtype.val : s → α) A) =
        fun n : ℕ => (sfiniteSeq μ n) ((Subtype.val : s → α) '' A) by
          funext n
          exact comap_subtype_coe_apply hs (sfiniteSeq μ n) A]
    rw [← Measure.sum_apply_of_countable]
    rw [sum_sfiniteSeq]
    exact comap_subtype_coe_apply hs μ A
  exact ⟨m, hfin, hsum⟩

private lemma cylCoord_map_R1 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    Measure.map (cylE1 α β γ) ((μ.prod ν).prod τ) = (μ.prod τ).prod ν := by
  let A : ((α × β) × γ) → α × β × γ := ⇑(MeasurableEquiv.prodAssoc (α := α) (β := β) (γ := γ))
  let Mid : α × β × γ → α × γ × β := Prod.map (@id α) (@Prod.swap β γ)
  let B : α × γ × β → (α × γ) × β := ⇑((MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm)
  have hAmeas : Measurable A := by dsimp [A]; fun_prop
  have hMidmeas : Measurable Mid := by dsimp [Mid]; fun_prop
  have hBmeas : Measurable B := by dsimp [B]; fun_prop
  have h_func : cylE1 α β γ = B ∘ Mid ∘ A := by
    funext q
    rcases q with ⟨⟨x, y⟩, z⟩
    rfl
  have hA : Measure.map A ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) := by
    simpa [A] using (Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := τ))
  have hMid : Measure.map Mid (μ.prod (ν.prod τ)) = μ.prod (τ.prod ν) := by
    calc
      Measure.map (Prod.map (@id α) (@Prod.swap β γ)) (μ.prod (ν.prod τ))
          = (Measure.map (@id α) μ).prod (Measure.map (@Prod.swap β γ) (ν.prod τ)) := by
            rw [Measure.map_prod_map (μa := μ) (μc := ν.prod τ) (f := @id α) (g := @Prod.swap β γ)
              (by fun_prop) (by fun_prop)]
      _ = μ.prod (τ.prod ν) := by
            rw [Measure.map_id]
            rw [Measure.prod_swap (μ := ν) (ν := τ)]
  have hB : Measure.map B (μ.prod (τ.prod ν)) = (μ.prod τ).prod ν := by
    have hAssocMP : Measure.map (⇑(MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)))
        ((μ.prod τ).prod ν) = μ.prod (τ.prod ν) :=
      Measure.prodAssoc_prod (μ := μ) (ν := τ) (τ := ν)
    have hid : (⇑((MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm) ∘
          ⇑(MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β))) = id := by
      funext q
      rfl
    calc
      Measure.map B (μ.prod (τ.prod ν))
          = Measure.map (⇑((MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm))
              (Measure.map (⇑(MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)))
                ((μ.prod τ).prod ν)) := by
                rw [← hAssocMP]
      _ = Measure.map ((⇑((MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)).symm)) ∘
              (⇑(MeasurableEquiv.prodAssoc (α := α) (β := γ) (γ := β)))) ((μ.prod τ).prod ν) := by
                rw [Measure.map_map (hg := by fun_prop) (hf := by fun_prop)]
      _ = Measure.map id ((μ.prod τ).prod ν) := by rw [hid]
      _ = (μ.prod τ).prod ν := Measure.map_id
  calc
    Measure.map (cylE1 α β γ) ((μ.prod ν).prod τ)
        = Measure.map (B ∘ Mid ∘ A) ((μ.prod ν).prod τ) := by rw [h_func]
    _ = Measure.map B (Measure.map (Mid ∘ A) ((μ.prod ν).prod τ)) := by
          rw [← Measure.map_map (hg := hBmeas) (hf := hMidmeas.comp hAmeas)]
    _ = Measure.map B (Measure.map Mid (Measure.map A ((μ.prod ν).prod τ))) := by
          rw [← Measure.map_map (hg := hMidmeas) (hf := hAmeas)]
    _ = Measure.map B (Measure.map Mid (μ.prod (ν.prod τ))) := by rw [hA]
    _ = Measure.map B (μ.prod (τ.prod ν)) := by rw [hMid]
    _ = (μ.prod τ).prod ν := hB

private lemma cylCoord_map_R2 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (τ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    Measure.map (cylE2 α β γ) ((μ.prod ν).prod τ) = μ.prod (τ.prod ν) := by
  let A : ((α × β) × γ) → α × β × γ := ⇑(MeasurableEquiv.prodAssoc (α := α) (β := β) (γ := γ))
  let Mid : α × β × γ → α × γ × β := Prod.map (@id α) (@Prod.swap β γ)
  have hAmeas : Measurable A := by dsimp [A]; fun_prop
  have hMidmeas : Measurable Mid := by dsimp [Mid]; fun_prop
  have h_func : cylE2 α β γ = Mid ∘ A := by
    funext q
    rcases q with ⟨⟨x, y⟩, z⟩
    rfl
  have hA : Measure.map A ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) := by
    simpa [A] using (Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := τ))
  have hMid : Measure.map Mid (μ.prod (ν.prod τ)) = μ.prod (τ.prod ν) := by
    calc
      Measure.map (Prod.map (@id α) (@Prod.swap β γ)) (μ.prod (ν.prod τ))
          = (Measure.map (@id α) μ).prod (Measure.map (@Prod.swap β γ) (ν.prod τ)) := by
            rw [Measure.map_prod_map (μa := μ) (μc := ν.prod τ) (f := @id α) (g := @Prod.swap β γ)
              (by fun_prop) (by fun_prop)]
      _ = μ.prod (τ.prod ν) := by
            rw [Measure.map_id]
            rw [Measure.prod_swap (μ := ν) (ν := τ)]
  calc
    Measure.map (cylE2 α β γ) ((μ.prod ν).prod τ)
        = Measure.map (Mid ∘ A) ((μ.prod ν).prod τ) := by rw [h_func]
    _ = Measure.map Mid (Measure.map A ((μ.prod ν).prod τ)) := by
          rw [← Measure.map_map (hg := hMidmeas) (hf := hAmeas)]
    _ = Measure.map Mid (μ.prod (ν.prod τ)) := by rw [hA]
    _ = μ.prod (τ.prod ν) := hMid

end Commons.Analysis.MeasureTheory

namespace Commons.Analysis.MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

-- measurability facts -------------------------------------------------

private lemma cylMeas_e1 : Measurable (cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ))) := by
  unfold cylE1
  fun_prop

private lemma cylMeas_psi : Measurable (cylPsi) := by
  unfold cylPsi
  fun_prop

private lemma cylMeas_prod_psi_id :
    Measurable (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) := by
  unfold cylPsi
  fun_prop

private lemma cylMeas_R2 :
    Measurable (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) := by
  unfold cylE2
  fun_prop

private lemma cylMeas_polar : Measurable (cylPolar (W := W)) := by
  unfold cylPolar
  fun_prop

private lemma cylMeas_incl : Measurable (cylIncl (W := W)) := by
  unfold cylIncl
  fun_prop

private lemma cylMeas_lam : Measurable (cylLambda (W := W)) := by
  unfold cylLambda
  fun_prop

end Commons.Analysis.MeasureTheory

namespace Commons.Analysis.MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- The τ measure on ℝ (density (1-t²)^((d-2)/2) on (-1,1)). -/
private abbrev cylTau (d : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (-1) 1)).withDensity
    (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ (((d : ℝ) - 2) / 2)))

/-- The It-measure: pullback of τ along the interval subtype. -/
private abbrev cylMuIt (d : ℕ) : Measure cylIt :=
  (cylTau d).comap (Subtype.val : cylIt → ℝ)

/-- The sphere measure. -/
private abbrev cylSigma : Measure (Metric.sphere (0 : W) 1) := volume.toSphere

/-- the radial measure on (0,∞) with density x^n. -/
private abbrev cylNu (n : ℕ) : Measure (Set.Ioi (0 : ℝ)) := Measure.volumeIoiPow n

/-- ℝ-measure on the subtype `W0 := {0}ᶜ` pulled back from volume. -/
private abbrev cylVolW0 : Measure ({0}ᶜ : Set W) :=
  volume.comap (Subtype.val : ({0}ᶜ : Set W) → W)

/-- Step A: move the sphere factor outward: ((μIt×σ)×νd) ↦ (μIt×νd)×σ. -/
private lemma cylCoord_stepA (d : ℕ) [SFinite (cylMuIt d)] :
    Measure.map (cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)))
      (((cylMuIt d).prod cylSigma).prod (cylNu d)) =
        ((cylMuIt d).prod (cylNu d)).prod cylSigma := by
  exact cylCoord_map_R1 (μ := cylMuIt d) (ν := cylSigma) (τ := cylNu d)

/-- Step B: push the (t,s) part while leaving the sphere factor alone. -/
private lemma cylCoord_stepB (d : ℕ) [SFinite (cylMuIt d)] :
    Measure.map (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1)))
      (((cylMuIt d).prod (cylNu d)).prod cylSigma) =
        ((Measure.map cylPsi ((cylMuIt d).prod (cylNu d))).prod cylSigma) := by
  have h1 : Measure.map (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1)))
        (((cylMuIt d).prod (cylNu d)).prod cylSigma) =
      (Measure.map cylPsi ((cylMuIt d).prod (cylNu d))).prod
        (Measure.map (@id (Metric.sphere (0 : W) 1)) cylSigma) := by
    exact (Measure.map_prod_map (μa := (cylMuIt d).prod (cylNu d)) (μc := cylSigma)
      (f := cylPsi) (g := @id (Metric.sphere (0 : W) 1)) (cylMeas_psi) (by fun_prop)).symm
  have h2 : (Measure.map cylPsi ((cylMuIt d).prod (cylNu d))).prod
        (Measure.map (@id (Metric.sphere (0 : W) 1)) cylSigma) =
      (Measure.map cylPsi ((cylMuIt d).prod (cylNu d))).prod cylSigma := by
    exact congrArg (fun X : Measure (Metric.sphere (0 : W) 1) =>
      (Measure.map cylPsi ((cylMuIt d).prod (cylNu d))).prod X)
      (Measure.map_id (μ := cylSigma))
  exact h1.trans h2

private lemma cyl_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) {g : β → ℝ≥0∞} (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) = (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, MeasureTheory.withDensity_apply _ (hf hs),
    MeasureTheory.withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
  simp only [Function.comp_apply]

private lemma cylMeas_ofReal_rpow (d : ℕ) :
    Measurable (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ (((d : ℝ) - 2) / 2))) := by
  apply ENNReal.measurable_ofReal.comp
  fun_prop

private lemma cylMeas_ofReal_pow (n : ℕ) :
    Measurable (fun s : ℝ => ENNReal.ofReal (s ^ n)) := by
  apply ENNReal.measurable_ofReal.comp
  fun_prop

-- subtype -> ambient maps
private def cylJ1 : cylIt × Set.Ioi (0 : ℝ) → ℝ × ℝ :=
  Prod.map (Subtype.val : cylIt → ℝ) (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)
private def cylJ2 : ℝ × Set.Ioi (0 : ℝ) → ℝ × ℝ :=
  Prod.map (@id ℝ) (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)
private def cylF : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 * p.1, p.2 * Real.sqrt (1 - p.1 ^ 2))
private def cylU : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Ioo (-1) 1 ∧ 0 < p.2}
private def cylV : Set (ℝ × ℝ) := {p | 0 < p.2}
private def cylDensL (d : ℕ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p => ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2) * p.2 ^ d)
private def cylDensR (d : ℕ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (p.2 ^ (d - 1))

private lemma cylMeas_J1 : Measurable cylJ1 := by unfold cylJ1; fun_prop
private lemma cylMeas_J2 : Measurable cylJ2 := by unfold cylJ2; fun_prop
private lemma cylMeas_F : Measurable cylF := by unfold cylF; fun_prop
private lemma cylMeas_DensL (d : ℕ) : Measurable (cylDensL d) := by
  unfold cylDensL; apply ENNReal.measurable_ofReal.comp; fun_prop
private lemma cylMeas_DensR (d : ℕ) : Measurable (cylDensR d) := by
  unfold cylDensR; apply ENNReal.measurable_ofReal.comp; fun_prop

private lemma cylLift_muIt (d : ℕ) :
    Measure.map (Subtype.val : cylIt → ℝ) (cylMuIt d) = cylTau d := by
  have hf : MeasurableEmbedding (Subtype.val : cylIt → ℝ) :=
    MeasurableEmbedding.subtype_coe (s := (Set.Ioo (-1 : ℝ) 1)) measurableSet_Ioo
  calc
    Measure.map (Subtype.val : cylIt → ℝ) (cylMuIt d)
        = (cylTau d).restrict (Set.range (Subtype.val : cylIt → ℝ)) := by
          dsimp [cylMuIt]
          exact hf.map_comap (cylTau d)
    _ = cylTau d := by
          have hrange : Set.range (Subtype.val : cylIt → ℝ) = Set.Ioo (-1 : ℝ) 1 := by
            ext x; simp
          rw [hrange]
          dsimp [cylTau]
          rw [MeasureTheory.restrict_withDensity measurableSet_Ioo]
          rw [Measure.restrict_restrict (μ := (volume : Measure ℝ))
            (s := Set.Ioo (-1 : ℝ) 1) (t := Set.Ioo (-1 : ℝ) 1) measurableSet_Ioo]
          rw [Set.inter_self]

/-- 1D fact: pushforward of `volumeIoiPow n` by the ray inclusion. -/
private lemma cylLift_nu (n : ℕ) :
    Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (cylNu n) =
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun s : ℝ => ENNReal.ofReal (s ^ n)) := by
  have hf : MeasurableEmbedding (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) :=
    MeasurableEmbedding.subtype_coe (s := (Set.Ioi (0 : ℝ))) measurableSet_Ioi
  have hcomp : cylNu n
      = (volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)).withDensity
          ((fun s : ℝ => ENNReal.ofReal (s ^ n)) ∘ (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)) := rfl
  calc
    Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (cylNu n)
        = Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)
            ((volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)).withDensity
              ((fun s : ℝ => ENNReal.ofReal (s ^ n)) ∘ (Subtype.val : Set.Ioi (0 : ℝ) → ℝ))) := by
            rw [hcomp]
    _ = (Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)
          (volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ))).withDensity
            (fun s : ℝ => ENNReal.ofReal (s ^ n)) := by
            exact cyl_map_withDensity_comp
              (Measure.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))
              (f := (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)) (by fun_prop)
              (g := fun s : ℝ => ENNReal.ofReal (s ^ n)) (cylMeas_ofReal_pow n)
    _ = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun s : ℝ => ENNReal.ofReal (s ^ n)) := by
            rw [hf.map_comap (volume : Measure ℝ)]
            congr 2
            ext x; simp

private lemma cylJ2_emb : MeasurableEmbedding cylJ2 := by
  unfold cylJ2
  exact MeasurableEmbedding.prodMap
    (MeasurableEmbedding.id (α := ℝ))
    (MeasurableEmbedding.subtype_coe (s := (Set.Ioi (0 : ℝ))) measurableSet_Ioi)

/-- lift of the 2D substitution to the subtype measures: the domain side. -/
private lemma cylLift1 (d : ℕ) :
    Measure.map cylJ1 ((cylMuIt d).prod (cylNu d)) =
      (volume.restrict cylU).withDensity (cylDensL d) := by
  haveI : SFinite (cylMuIt d) :=
    cylCoord_sfinite_comap_subtype (s := (Set.Ioo (-1 : ℝ) 1)) (hs := measurableSet_Ioo)
      (μ := cylTau d)
  have h1 := cylLift_muIt d
  have h2 := cylLift_nu d
  have hmp := (Measure.map_prod_map (μa := cylMuIt d) (μc := cylNu d)
    (f := (Subtype.val : cylIt → ℝ)) (g := (Subtype.val : Set.Ioi (0 : ℝ) → ℝ))
    (by fun_prop) (by fun_prop)).symm
  have hUeq : (Set.Ioo (-1 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ)) = cylU := by
    ext p; simp [cylU, Prod.ext_iff, Set.mem_Ioo, Set.mem_Ioi]
  calc
    Measure.map cylJ1 ((cylMuIt d).prod (cylNu d))
        = (Measure.map (Subtype.val : cylIt → ℝ) (cylMuIt d)).prod
            (Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (cylNu d)) := by
          simpa [cylJ1] using hmp
    _ = (cylTau d).prod ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun s : ℝ => ENNReal.ofReal (s ^ d))) := by rw [h1, h2]
    _ = ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
          (fun t : ℝ => ENNReal.ofReal ((1 - t ^ 2) ^ (((d : ℝ) - 2) / 2)))).prod
          ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun s : ℝ => ENNReal.ofReal (s ^ d))) := rfl
    _ = ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod (volume.restrict (Set.Ioi (0 : ℝ)))).withDensity
          (fun p : ℝ × ℝ => ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2))
            * ENNReal.ofReal (p.2 ^ d)) := by
          rw [MeasureTheory.prod_withDensity (hf := cylMeas_ofReal_rpow d) (hg := cylMeas_ofReal_pow d)]
    _ = (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          ((Set.Ioo (-1 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ)))).withDensity
          (fun p : ℝ × ℝ => ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2))
            * ENNReal.ofReal (p.2 ^ d)) := by
          rw [Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
            (s := Set.Ioo (-1 : ℝ) 1) (t := Set.Ioi (0 : ℝ))]
    _ = (volume.restrict cylU).withDensity (cylDensL d) := by
          rw [hUeq]
          apply MeasureTheory.withDensity_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_Ioo.prod measurableSet_Ioi)] with p hp
          have hp1 : p.1 ∈ Set.Ioo (-1 : ℝ) 1 := hp.1
          have hp2 : 0 < p.2 := hp.2
          have hbase : 0 < 1 - p.1 ^ 2 := by
            have h1' : -1 < p.1 := hp1.1
            have h2' : p.1 < 1 := hp1.2
            nlinarith [sq_nonneg p.1]
          have ha : 0 ≤ (1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2) :=
            Real.rpow_nonneg hbase.le _
          have hb : 0 ≤ p.2 ^ d := pow_nonneg hp2.le d
          dsimp [cylDensL]
          rw [← ENNReal.ofReal_mul ha]

/-- lift of the 2D substitution to the subtype measures: the target side. -/
private lemma cylLift3 (d : ℕ) :
    Measure.map cylJ2 ((volume : Measure ℝ).prod (cylNu (d - 1))) =
      (volume.restrict cylV).withDensity (cylDensR d) := by
  have h2 := cylLift_nu (d - 1)
  have hmp := (Measure.map_prod_map (μa := (volume : Measure ℝ)) (μc := cylNu (d - 1))
    (f := @id ℝ) (g := (Subtype.val : Set.Ioi (0 : ℝ) → ℝ))
    (by fun_prop) (by fun_prop)).symm
  have hVeq : (univ : Set ℝ) ×ˢ (Set.Ioi (0 : ℝ)) = cylV := by
    ext p; simp [cylV, Prod.ext_iff, Set.mem_Ioi]
  calc
    Measure.map cylJ2 ((volume : Measure ℝ).prod (cylNu (d - 1)))
        = (Measure.map (@id ℝ) (volume : Measure ℝ)).prod
            (Measure.map (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (cylNu (d - 1))) := by
          simpa [cylJ2] using hmp
    _ = (volume : Measure ℝ).prod ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun s : ℝ => ENNReal.ofReal (s ^ (d - 1)))) := by rw [Measure.map_id, h2]
    _ = ((volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ)))).withDensity
          (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (d - 1))) := by
          rw [MeasureTheory.prod_withDensity_right (hg := cylMeas_ofReal_pow (d - 1))]
    _ = (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (univ ×ˢ (Set.Ioi (0 : ℝ)))).withDensity
          (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (d - 1))) := by
          have hpr : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
              = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
                  (univ ×ˢ (Set.Ioi (0 : ℝ))) := by
            simpa using (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
              (s := univ) (t := Set.Ioi (0 : ℝ)))
          exact congrArg (fun X : Measure (ℝ × ℝ) =>
            X.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (d - 1)))) hpr
    _ = (volume.restrict cylV).withDensity (cylDensR d) := by
          rw [hVeq]
          rfl

/-- Step C: the two-dimensional substitution (the analytic core), assembled from
the ℝ² change of variables and the subtype inclusions. -/
private lemma cylCoord_stepC (d : ℕ) (hd : 1 ≤ d) :
    Measure.map cylPsi ((cylMuIt d).prod (cylNu d)) =
      (volume : Measure ℝ).prod (cylNu (d - 1)) := by
  have hL1 := cylLift1 d
  have hcore := pair_cyl_twoDim_core_upper d hd
  have hL3 := cylLift3 d
  have hpoint : ∀ x : cylIt × Set.Ioi (0 : ℝ), cylF (cylJ1 x) = cylJ2 (cylPsi x) := by
    rintro ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
    simp only [cylF, cylJ1, cylJ2, cylPsi, Prod.map_apply, id_eq]
  have hmaps : Measure.map cylJ2 (Measure.map cylPsi ((cylMuIt d).prod (cylNu d))) =
      Measure.map cylJ2 ((volume : Measure ℝ).prod (cylNu (d - 1))) := by
    calc
      Measure.map cylJ2 (Measure.map cylPsi ((cylMuIt d).prod (cylNu d)))
          = Measure.map (cylJ2 ∘ cylPsi) ((cylMuIt d).prod (cylNu d)) := by
              rw [Measure.map_map (hg := cylMeas_J2) (hf := cylMeas_psi)]
      _ = Measure.map (cylF ∘ cylJ1) ((cylMuIt d).prod (cylNu d)) := by
              rw [show (cylJ2 ∘ cylPsi) = (cylF ∘ cylJ1) from funext (fun x => (hpoint x).symm)]
      _ = Measure.map cylF (Measure.map cylJ1 ((cylMuIt d).prod (cylNu d))) := by
              rw [← Measure.map_map (hg := cylMeas_F) (hf := cylMeas_J1)]
      _ = Measure.map cylF ((volume.restrict cylU).withDensity (cylDensL d)) := by rw [hL1]
      _ = (volume.restrict cylV).withDensity (cylDensR d) := hcore
      _ = Measure.map cylJ2 ((volume : Measure ℝ).prod (cylNu (d - 1))) := hL3.symm
  exact (cylJ2_emb.map_injective) hmaps


/-- Step D: reassociate ((a,q),ω) ↦ (a,(ω,q)) on the polar-side product. -/
private lemma cylCoord_stepD (d : ℕ) :
    Measure.map (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1))
      (((volume : Measure ℝ).prod (cylNu (d - 1))).prod cylSigma) =
        (volume : Measure ℝ).prod (cylSigma.prod (cylNu (d - 1))) := by
  exact cylCoord_map_R2 (μ := (volume : Measure ℝ)) (ν := cylNu (d - 1)) (τ := cylSigma)

end Commons.Analysis.MeasureTheory

namespace Commons.Analysis.MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- The polar decomposition on the W-factor, reversed:
H⁻¹ : (ω, r) ↦ r • ω pushes σ × ν_{d-1} to the pulled-back volume on W∖{0}. -/
private lemma cylCoord_polar_rev :
    Measure.map (⇑(homeomorphUnitSphereProd W).symm)
      (cylSigma.prod (cylNu (Module.finrank ℝ W - 1))) = cylVolW0 := by
  have h := Measure.measurePreserving_homeomorphUnitSphereProd (μ := volume) (E := W)
  have hmap := h.map_eq
  calc
    Measure.map (⇑(homeomorphUnitSphereProd W).symm)
        (cylSigma.prod (cylNu (Module.finrank ℝ W - 1)))
        = Measure.map (⇑(homeomorphUnitSphereProd W).symm)
            (Measure.map (homeomorphUnitSphereProd W) (volume.comap (Subtype.val : ({0}ᶜ : Set W) → W))) := by
            rw [hmap]
    _ = Measure.map ((⇑(homeomorphUnitSphereProd W).symm) ∘ (homeomorphUnitSphereProd W))
            (volume.comap (Subtype.val : ({0}ᶜ : Set W) → W)) := by
            rw [Measure.map_map (hg := by fun_prop) (hf := by fun_prop)]
    _ = Measure.map id (volume.comap (Subtype.val : ({0}ᶜ : Set W) → W)) := by
            congr 2
            funext x
            exact (homeomorphUnitSphereProd W).symm_apply_apply x
    _ = cylVolW0 := by
            rw [Measure.map_id]

/-- measurability of H⁻¹. -/
private lemma cylMeas_HSymm : Measurable (⇑(homeomorphUnitSphereProd W).symm) := by
  fun_prop

/-- Step E: apply the polar decomposition inside the ℝ-coordinate:
(id × H⁻¹) pushes ℝ × (σ × ν_{d-1}) to ℝ × (volume on W∖{0}). -/
private lemma cylCoord_stepE :
    Measure.map (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm))
      ((volume : Measure ℝ).prod (cylSigma.prod (cylNu (Module.finrank ℝ W - 1)))) =
        (volume : Measure ℝ).prod cylVolW0 := by
  calc
    Measure.map (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm))
        ((volume : Measure ℝ).prod (cylSigma.prod (cylNu (Module.finrank ℝ W - 1))))
        = (Measure.map (@id ℝ) (volume : Measure ℝ)).prod
            (Measure.map (⇑(homeomorphUnitSphereProd W).symm)
              (cylSigma.prod (cylNu (Module.finrank ℝ W - 1)))) := by
            rw [← Measure.map_prod_map (μa := (volume : Measure ℝ))
              (μc := cylSigma.prod (cylNu (Module.finrank ℝ W - 1)))
              (f := @id ℝ) (g := ⇑(homeomorphUnitSphereProd W).symm) (by fun_prop) (by fun_prop)]
    _ = (volume : Measure ℝ).prod
          (Measure.map (⇑(homeomorphUnitSphereProd W).symm)
            (cylSigma.prod (cylNu (Module.finrank ℝ W - 1)))) := by
            rw [Measure.map_id]
    _ = (volume : Measure ℝ).prod cylVolW0 := by
            rw [cylCoord_polar_rev]

/-- the measure on the subtype {w ≠ 0}: pushed by inclusion it is volume.restrict {w ≠ 0}. -/
private lemma cylCoord_map_val_comap :
    Measure.map (Subtype.val : ({0}ᶜ : Set W) → W) (volume.comap (Subtype.val : ({0}ᶜ : Set W) → W)) =
      (volume : Measure W).restrict {w : W | w ≠ (0 : W)} := by
  have hf : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set W) → W) :=
    MeasurableEmbedding.subtype_coe ((measurableSet_singleton (0 : W)).compl)
  have h := hf.map_comap (μ := (volume : Measure W))
  -- h : map val (comap val volume) = volume.restrict (range val)
  rw [h]
  congr 1
  ext w
  simp

/-- Step F: inclusion ℝ×W0 ↪ ℝ×W pushes ℝ×(vol on W0) to vol.restrict {p.2 ≠ 0}. -/
private lemma cylCoord_stepF :
    Measure.map (Prod.map (@id ℝ) (Subtype.val : ({0}ᶜ : Set W) → W))
      ((volume : Measure ℝ).prod cylVolW0) =
        (volume : Measure (ℝ × W)).restrict {p : ℝ × W | p.2 ≠ (0 : W)} := by
  haveI : SFinite cylVolW0 := by
    dsimp [cylVolW0]
    exact cylCoord_sfinite_comap_subtype (s := ({0}ᶜ : Set W))
      (hs := (measurableSet_singleton (0 : W)).compl) (μ := (volume : Measure W))
  calc
    Measure.map (Prod.map (@id ℝ) (Subtype.val : ({0}ᶜ : Set W) → W))
        ((volume : Measure ℝ).prod cylVolW0)
        = (Measure.map (@id ℝ) (volume : Measure ℝ)).prod
            (Measure.map (Subtype.val : ({0}ᶜ : Set W) → W) cylVolW0) := by
            rw [← Measure.map_prod_map (μa := (volume : Measure ℝ))
              (μc := cylVolW0) (f := @id ℝ)
              (g := (Subtype.val : ({0}ᶜ : Set W) → W)) (by fun_prop) (by fun_prop)]
    _ = (volume : Measure ℝ).prod
          ((volume : Measure W).restrict {w : W | w ≠ (0 : W)}) := by
            rw [Measure.map_id]
            rw [cylCoord_map_val_comap]
    _ = (volume : Measure ℝ).prod
          ((volume : Measure W).restrict {w : W | w ≠ (0 : W)}) := rfl
    _ = (volume : Measure (ℝ × W)).restrict (univ ×ˢ {w : W | w ≠ (0 : W)}) := by
            rw [← Measure.restrict_univ (μ := (volume : Measure ℝ))]
            rw [Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure W))
              (s := univ) (t := {w : W | w ≠ (0 : W)})]
            rfl
    _ = (volume : Measure (ℝ × W)).restrict {p : ℝ × W | p.2 ≠ (0 : W)} := by
            congr 2
            ext p
            simp

end Commons.Analysis.MeasureTheory

namespace Commons.Analysis.MeasureTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

/-- polar = (id × H⁻¹) ∘ E2 pointwise. -/
private lemma cylPolar_eq :
    cylPolar (W := W) = (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) ∘
        (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) := by
  funext q
  rcases q with ⟨⟨a, qq⟩, ω⟩
  rfl

private lemma cylMeas_idHSymm :
    Measurable (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) := by
  unfold homeomorphUnitSphereProd
  fun_prop

/-- The main measure identity, with all definitions spelled out (same as the theorem). -/
private lemma cylCoord_main
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    let d : ℕ := Module.finrank ℝ W
    let expo : ℝ := (((d : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let tau : Measure ℝ :=
      (volume.restrict (Set.Ioo (-1) 1)).withDensity (fun t => ENNReal.ofReal (rho t))
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let SW := Metric.sphere (0 : W) 1
    let μ : Measure ((It × SW) × Set.Ioi (0 : ℝ)) :=
      ((tau.comap (Subtype.val : It → ℝ)).prod volume.toSphere).prod
        (Measure.volumeIoiPow d)
    let Λ : (It × SW) × Set.Ioi (0 : ℝ) → ℝ × W := fun q =>
      let t : ℝ := (q.1.1 : It).1
      let ω : W := (q.1.2 : SW)
      let s : ℝ := (q.2 : Set.Ioi (0 : ℝ)).1
      (s * t, (s * Real.sqrt (1 - t ^ 2)) • ω)
    Measure.map Λ μ = (volume : Measure (ℝ × W)).restrict
      {p : ℝ × W | p.2 ≠ (0 : W)} := by
  dsimp only
  -- now the goal is fully unfolded; re-introduce names and prove by the chain
  let d : ℕ := Module.finrank ℝ W
  let μ0 : Measure ((cylIt × Metric.sphere (0 : W) 1) × Set.Ioi (0 : ℝ)) :=
    (((cylTau d).comap (Subtype.val : cylIt → ℝ)).prod cylSigma).prod (cylNu d)
  let μ1 : Measure ((cylIt × Set.Ioi (0 : ℝ)) × Metric.sphere (0 : W) 1) :=
    (((cylTau d).comap (Subtype.val : cylIt → ℝ)).prod (cylNu d)).prod cylSigma
  let μ2 : Measure ((ℝ × Set.Ioi (0 : ℝ)) × Metric.sphere (0 : W) 1) :=
    (Measure.map cylPsi (((cylTau d).comap (Subtype.val : cylIt → ℝ)).prod (cylNu d))).prod cylSigma
  let μ3 : Measure ((ℝ × Set.Ioi (0 : ℝ)) × Metric.sphere (0 : W) 1) :=
    ((volume : Measure ℝ).prod (cylNu (d - 1))).prod cylSigma
  let μ4 : Measure (ℝ × (Metric.sphere (0 : W) 1 × Set.Ioi (0 : ℝ))) :=
    (volume : Measure ℝ).prod (cylSigma.prod (cylNu (d - 1)))
  let μ5 : Measure (ℝ × ({0}ᶜ : Set W)) :=
    (volume : Measure ℝ).prod cylVolW0
  haveI : SFinite (cylTau d) := by dsimp [cylTau]; infer_instance
  haveI : SFinite ((cylTau d).comap (Subtype.val : cylIt → ℝ)) :=
    cylCoord_sfinite_comap_subtype (s := (Set.Ioo (-1 : ℝ) 1))
      (hs := measurableSet_Ioo) (μ := cylTau d)
  -- measure chain
  have hA : μ1 = Measure.map (cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ))) μ0 := by
    dsimp [μ0, μ1]
    exact (cylCoord_stepA d).symm
  have hB : μ2 = Measure.map (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) μ1 := by
    dsimp [μ1, μ2]
    exact (cylCoord_stepB d).symm
  have hC : μ2 = μ3 := by
    dsimp [μ2, μ3]
    rw [cylCoord_stepC d (by
      have hdpos : 0 < Module.finrank ℝ W := Module.finrank_pos (R := ℝ) (M := W)
      omega)]
  have hD : μ4 = Measure.map (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) μ3 := by
    dsimp [μ3, μ4]
    exact (cylCoord_stepD d).symm
  have hE : μ5 = Measure.map (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) μ4 := by
    dsimp [μ4, μ5]
    exact cylCoord_stepE.symm
  have hF : (volume : Measure (ℝ × W)).restrict {p : ℝ × W | p.2 ≠ (0 : W)} =
      Measure.map (cylIncl (W := W)) μ5 := by
    dsimp [μ5]
    exact cylCoord_stepF.symm
  -- function factorisation
  have hLam : cylLambda (W := W) = cylIncl ∘ cylPolar ∘
      (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) ∘
        cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)) := cylLambda_eq
  -- measurable components
  have hme : Measurable (cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ))) := cylMeas_e1
  have hmp : Measurable (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) := cylMeas_prod_psi_id
  have hmpolar : Measurable (cylPolar (W := W)) := cylMeas_polar
  have hmincl : Measurable (cylIncl (W := W)) := cylMeas_incl
  have hmE2 : Measurable (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) := cylMeas_R2
  have hmHS : Measurable (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) := cylMeas_idHSymm
  have hpolar_eq : cylPolar (W := W) = (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) ∘
      (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) := cylPolar_eq
  -- assemble
  calc
    Measure.map (fun q : (cylIt × Metric.sphere (0 : W) 1) × Set.Ioi (0 : ℝ) =>
        (q.2.1 * (q.1.1 : cylIt).1,
          (q.2.1 * Real.sqrt (1 - ((q.1.1 : cylIt).1) ^ 2)) •
            ((q.1.2 : Metric.sphere (0 : W) 1) : W))) μ0
        = Measure.map cylLambda μ0 := by rfl
    _ = Measure.map (cylIncl ∘ cylPolar ∘ (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) ∘
          cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ))) μ0 := by
          rw [hLam]
    _ = Measure.map cylIncl (Measure.map cylPolar
          (Measure.map (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1)))
            (Measure.map (cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ))) μ0))) := by
          rw [← Measure.map_map (g := cylIncl)
            (f := cylPolar ∘ (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) ∘
              cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)))
            (hg := hmincl) (hf := hmpolar.comp (hmp.comp hme))]
          rw [← Measure.map_map (g := cylPolar)
            (f := (Prod.map cylPsi (@id (Metric.sphere (0 : W) 1))) ∘
              cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)))
            (hg := hmpolar) (hf := hmp.comp hme)]
          rw [← Measure.map_map (g := Prod.map cylPsi (@id (Metric.sphere (0 : W) 1)))
            (f := cylE1 cylIt (Metric.sphere (0 : W) 1) (Set.Ioi (0 : ℝ)))
            (hg := hmp) (hf := hme)]
    _ = Measure.map cylIncl (Measure.map cylPolar μ2) := by
          rw [← hA, ← hB]
    _ = Measure.map cylIncl (Measure.map cylPolar μ3) := by rw [hC]
    _ = Measure.map cylIncl (Measure.map (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm))
          (Measure.map (cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) μ3)) := by
          rw [hpolar_eq]
          rw [← Measure.map_map (g := Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm))
            (f := cylE2 ℝ (Set.Ioi (0 : ℝ)) (Metric.sphere (0 : W) 1)) (hg := hmHS) (hf := hmE2)]
    _ = Measure.map cylIncl (Measure.map (Prod.map (@id ℝ) (⇑(homeomorphUnitSphereProd W).symm)) μ4) := by
          rw [← hD]
    _ = Measure.map cylIncl μ5 := by rw [← hE]
    _ = (volume : Measure (ℝ × W)).restrict {p : ℝ × W | p.2 ≠ (0 : W)} := by rw [hF]

end Commons.Analysis.MeasureTheory

namespace Commons.Analysis.MeasureTheory

/-- The cylindrical-coordinate change of variables for Lebesgue measure on the
product `ℝ × W`, where `W` is a nontrivial finite-dimensional real inner-product
space (dimension `d`).

`It = Ioo (-1) 1`, `SW` = the unit sphere of `W`, and for `(t, ω, s)` with
`t ∈ It`, `ω ∈ SW`, `s > 0` write `Λ (t, ω, s) = (s·t, s·√(1-t²)·ω) ∈ ℝ × W`
(cone coordinates: every `(a, w)` with `w ≠ 0` has a unique representation
`(a, w) = Λ (a/√(a²+‖w‖²), w/‖w‖, √(a²+‖w‖²))`).

Claim: `Λ` pushes the measure
`((τ ⊗ volume.toSphere₌W) ⊗ volumeIoiPow d)` forward to the product Lebesgue
measure on `ℝ × W` restricted to `{p | p.2 ≠ 0}`, where
`τ = volume.restrict (Ioo (-1) 1)` with density `t ↦ (1-t²)^((d-2)/2)` and
`volumeIoiPow d` is Mathlib's measure on `Ioi (0,∞)` with density `s ↦ s^d`
(`MeasureTheory.Measure.volumeIoiPow`).

This is the classical "polar/cylindrical coordinates around the first axis" —
the change of variables element is `da dvol_W(w) = s^d (1-t²)^((d-2)/2) dt dσ_W(ω) ds`.
A natural proof: (1) restrict to `w ≠ 0` and use Mathlib's polar decomposition
in the `W`-factor (`MeasureTheory.measurePreserving_homeomorphUnitSphereProd` on
`W`, inverse map `(q, ω) ↦ q·ω` pushes `volumeIoiPow (d-1) ⊗ σ_W` to
`volume.restrict {w ≠ 0}`); (2) perform the two-dimensional substitution
`(a, q) = (s·t, s·√(1-t²))` on `ℝ × Ioi (0,∞)` (equivalently `da dq =
(s/√(1-t²)) dt ds`, the latitude parametrization of the upper half plane by
angle `t = cos φ`), possibly via `intervalIntegral.integral_comp_mul_deriv`
or `MeasureTheory.Measure`-level substitution, then combine with the
`q^{d-1}` factor; (3) reassemble with Fubini / `Measure.map` / `Measure.prod`
bookkeeping (`MeasureTheory.Measure.map_prod_map`, `Measure.prod_prod`,
`Measure.map_map`, `MeasureTheory.MeasurePreserving.comp`), noting
`volumeIoiPow d` restricted to `Ioi (0, 1)` has total `1/(d+1)`. -/
theorem pair_cyl_coord_measure
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    let d : ℕ := Module.finrank ℝ W
    let expo : ℝ := (((d : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let tau : MeasureTheory.Measure ℝ :=
      (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal (rho t))
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let SW := Metric.sphere (0 : W) 1
    let μ : MeasureTheory.Measure ((It × SW) × Set.Ioi (0 : ℝ)) :=
      ((tau.comap (Subtype.val : It → ℝ)).prod MeasureTheory.volume.toSphere).prod
        (MeasureTheory.Measure.volumeIoiPow d)
    let Λ : (It × SW) × Set.Ioi (0 : ℝ) → ℝ × W := fun q =>
      let t : ℝ := (q.1.1 : It).1
      let ω : W := (q.1.2 : SW)
      let s : ℝ := (q.2 : Set.Ioi (0 : ℝ)).1
      (s * t, (s * Real.sqrt (1 - t ^ 2)) • ω)
    MeasureTheory.Measure.map Λ μ = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × W)).restrict
      {p : ℝ × W | p.2 ≠ (0 : W)} := by
  exact cylCoord_main

end Commons.Analysis.MeasureTheory