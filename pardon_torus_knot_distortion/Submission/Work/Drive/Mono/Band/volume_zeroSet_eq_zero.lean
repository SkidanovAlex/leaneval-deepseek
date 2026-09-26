import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

/-! ## Auxiliary facts about `Fin.insertNth` -/

private lemma fin_insertNth_eq_add_smul {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (t : ℝ) :
    (i.insertNth t y : Fin (n+1) → ℝ) = (i.insertNth 0 y) + t • (Pi.single i (1 : ℝ)) := by
  funext k
  have h : ∀ k : Fin (n+1),
      (i.insertNth t y : Fin (n+1) → ℝ) k
        = (((i.insertNth 0 y) + t • (Pi.single i (1 : ℝ))) : Fin (n+1) → ℝ) k := by
    rw [Fin.forall_iff_succAbove i]
    constructor
    · rw [Fin.insertNth_apply_same, Pi.add_apply, Pi.smul_apply, Fin.insertNth_apply_same,
        Pi.single_eq_same]
      ring
    · intro j
      rw [Fin.insertNth_apply_succAbove, Pi.add_apply, Pi.smul_apply, Fin.insertNth_apply_succAbove,
        Pi.single_eq_of_ne (Fin.succAbove_ne i j)]
      ring
  exact h k

private lemma continuous_fin_insertNth {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    Continuous (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ)) := by
  rw [show (fun t : ℝ => (i.insertNth t y : Fin (n+1) → ℝ))
      = (fun t : ℝ => (i.insertNth 0 y) + t • (Pi.single i (1 : ℝ)))
      from funext (fun t => fin_insertNth_eq_add_smul i y t)]
  exact continuous_const.add (continuous_id.smul continuous_const)

private lemma convex_fin_insertNth_preimage {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ)
    {K : Set (Fin (n+1) → ℝ)} (hK : Convex ℝ K) :
    Convex ℝ {t : ℝ | i.insertNth t y ∈ K} := by
  intro t₁ ht₁ t₂ ht₂ a b ha hb hab
  simp only [Set.mem_ofPred_eq] at ht₁ ht₂ ⊢
  rw [fin_insertNth_eq_add_smul i y t₁] at ht₁
  rw [fin_insertNth_eq_add_smul i y t₂] at ht₂
  rw [fin_insertNth_eq_add_smul i y (a • t₁ + b • t₂)]
  have hmem := hK ht₁ ht₂ ha hb hab
  have heq : a • ((i.insertNth 0 y) + t₁ • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ))
      + b • ((i.insertNth 0 y) + t₂ • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ))
      = (i.insertNth 0 y) + (a • t₁ + b • t₂) • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ) := by
    rw [smul_add, smul_add, smul_smul, smul_smul]
    rw [show a • (i.insertNth 0 y) + (a * t₁) • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ)
          + (b • (i.insertNth 0 y) + (b * t₂) • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ))
        = (a • (i.insertNth 0 y) + b • (i.insertNth 0 y))
          + ((a * t₁) • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ)
             + (b * t₂) • (Pi.single i (1:ℝ) : Fin (n+1) → ℝ))
        from by abel]
    rw [← add_smul, ← add_smul, hab, one_smul]
    rfl
  rw [heq] at hmem
  exact hmem

/-- A linear functional on `Fin 3 → ℝ` vanishing on all the basis vectors is zero. -/
private lemma clm_eq_zero_of_forall_single (f : (Fin 3 → ℝ) →L[ℝ] ℝ)
    (hf : ∀ i, f (Pi.single i (1:ℝ)) = 0) : f = 0 := by
  ext v
  have hv : (∑ i : Fin 3, v i • (Pi.single i (1:ℝ) : Fin 3 → ℝ)) = v := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hv, map_sum]
  simp [hf]

/-! ## The local statement: a closed ball on which the `i`-th partial derivative never vanishes -/

private lemma volume_closedBall_inter_zeroSet_eq_zero (i : Fin 3) (c : Fin 3 → ℝ) (r : ℝ)
    {g : (Fin 3 → ℝ) → ℝ}
    (hc : ContinuousOn g (Metric.closedBall c r))
    (hdiff : ∀ x ∈ Metric.closedBall c r, HasFDerivAt g (fderiv ℝ g x) x)
    (hgrad : ∀ x ∈ Metric.closedBall c r, fderiv ℝ g x (Pi.single i (1:ℝ)) ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      (Metric.closedBall c r ∩ {x | g x = 0}) = 0 := by
  classical
  set s : Set (Fin 3 → ℝ) := Metric.closedBall c r ∩ {x | g x = 0} with hs
  have hsmeas : MeasurableSet s := by
    have h1 : IsClosed (Metric.closedBall c r ∩ g ⁻¹' {0}) :=
      hc.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton
    rw [show s = Metric.closedBall c r ∩ g ⁻¹' {0} from by
      ext x
      simp [hs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]]
    exact h1.measurableSet
  let e : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hmp : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ i
  have himg : e '' s = e.symm ⁻¹' s := by
    ext z
    constructor
    · rintro ⟨x, hx, hxz⟩
      rw [← hxz]
      simpa using hx
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  have heimg : MeasurableSet (e '' s) := by
    rw [himg]
    exact e.symm.measurable hsmeas
  have hvol : volume s = volume (e '' s) := by
    rw [himg]
    exact (hmp.symm.measure_preimage hsmeas.nullMeasurableSet).symm
  have hfib : ∀ y : Fin 2 → ℝ, volume {t : ℝ | (t, y) ∈ e '' s} = 0 := by
    intro y
    have hset : {t : ℝ | (t, y) ∈ e '' s}
        = {t : ℝ | i.insertNth t y ∈ Metric.closedBall c r}
          ∩ {t : ℝ | g (i.insertNth t y) = 0} := by
      ext t
      have hsyme : e.symm (t, y) = i.insertNth t y := by
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl
      rw [himg]
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsyme, hs, Set.mem_inter_iff]
    rw [hset]
    set D : Set ℝ := {t : ℝ | i.insertNth t y ∈ Metric.closedBall c r} with hD
    have hconvD : Convex ℝ D := convex_fin_insertNth_preimage i y (convex_closedBall c r)
    have hcontφ : ContinuousOn (fun t : ℝ => g (i.insertNth t y)) D :=
      hc.comp (continuous_fin_insertNth i y).continuousOn (fun t ht => ht)
    have hderiv : ∀ t ∈ D, deriv (fun t : ℝ => g (i.insertNth t y)) t
        = (fderiv ℝ g (i.insertNth t y)) (Pi.single i (1:ℝ)) := by
      intro t ht
      have hd : HasDerivAt (fun s : ℝ => (i.insertNth s y : Fin 3 → ℝ))
          (Pi.single i (1:ℝ)) t := by
        rw [show (fun s : ℝ => (i.insertNth s y : Fin 3 → ℝ))
            = (fun s : ℝ => (i.insertNth 0 y) + s • (Pi.single i (1:ℝ) : Fin 3 → ℝ))
            from funext (fun s => fin_insertNth_eq_add_smul i y s)]
        have h1 : HasDerivAt (fun s : ℝ => s • (Pi.single i (1:ℝ) : Fin 3 → ℝ))
            (Pi.single i (1:ℝ)) t := by
          simpa using (hasDerivAt_id t).smul_const (Pi.single i (1:ℝ) : Fin 3 → ℝ)
        exact h1.const_add (i.insertNth 0 y)
      exact ((hdiff _ ht).comp_hasDerivAt t hd).deriv
    have hsub : (D ∩ {t : ℝ | g (i.insertNth t y) = 0}).Subsingleton := by
      intro t₁ ht₁ t₂ ht₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hIcc : Set.Icc t₁ t₂ ⊆ D := by
          rw [← segment_eq_Icc hlt.le]
          exact hconvD.segment_subset ht₁.1 ht₂.1
        obtain ⟨c, hcIoo, hc0⟩ :=
          exists_deriv_eq_zero hlt (hcontφ.mono hIcc) (by rw [ht₁.2, ht₂.2])
        have hcD : c ∈ D := hIcc (Set.Ioo_subset_Icc_self hcIoo)
        rw [hderiv c hcD] at hc0
        exact hgrad (i.insertNth c y) hcD hc0
      · have hIcc : Set.Icc t₂ t₁ ⊆ D := by
          rw [← segment_eq_Icc hlt.le]
          exact hconvD.segment_subset ht₂.1 ht₁.1
        obtain ⟨c, hcIoo, hc0⟩ :=
          exists_deriv_eq_zero hlt (hcontφ.mono hIcc) (by rw [ht₁.2, ht₂.2])
        have hcD : c ∈ D := hIcc (Set.Ioo_subset_Icc_self hcIoo)
        rw [hderiv c hcD] at hc0
        exact hgrad (i.insertNth c y) hcD hc0
    exact hsub.measure_zero volume
  calc volume s = volume (e '' s) := hvol
    _ = (volume.prod volume) (e '' s) := by
        rw [MeasureTheory.Measure.volume_eq_prod]
    _ = ∫⁻ y, volume {t : ℝ | (t, y) ∈ e '' s} ∂volume := Measure.prod_apply_symm heimg
    _ = 0 := by
        have hfun : (fun y : Fin 2 → ℝ => volume {t : ℝ | (t, y) ∈ e '' s}) = fun _ => (0:ENNReal) :=
          funext hfib
        rw [hfun]
        simp

/-! ## The global statement in `Fin 3 → ℝ` -/

private theorem volume_zeroSet_eq_zero_pi {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    {g : (Fin 3 → ℝ) → ℝ} (hg : ContDiffOn ℝ 1 g U)
    (h : ∀ x ∈ U, g x = 0 → fderiv ℝ g x ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) (U ∩ {x | g x = 0}) = 0 := by
  classical
  have hUc : ContinuousOn g U := hg.continuousOn
  have hfderiv_cont : ContinuousOn (fun x => fderiv ℝ g x) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have hφ : ∀ i : Fin 3, ContinuousOn
      (fun x : Fin 3 → ℝ => fderiv ℝ g x (Pi.single i (1:ℝ))) U :=
    fun i => hfderiv_cont.clm_apply continuousOn_const
  -- the piece of `U ∩ {g = 0}` where the `i`-th partial derivative has constant non-zero sign
  have hpiece : ∀ (i : Fin 3) (W : Set (Fin 3 → ℝ)), IsOpen W → W ⊆ U →
      (∀ x ∈ W, fderiv ℝ g x (Pi.single i (1:ℝ)) ≠ 0) →
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) (W ∩ {x | g x = 0}) = 0 := by
    intro i W hW hWU hWne
    have hcov : ∀ x : W, ∃ r : ℝ, 0 < r ∧ Metric.closedBall (x : Fin 3 → ℝ) r ⊆ W := by
      intro x
      rcases Metric.isOpen_iff.1 hW (x : Fin 3 → ℝ) x.2 with ⟨ε, hε, hεW⟩
      exact ⟨ε / 2, half_pos hε, fun y hy => hεW (lt_of_le_of_lt hy (half_lt_self hε))⟩
    choose r hrpos hrW using hcov
    have hcover : (⋃ x : W, Metric.ball (x : Fin 3 → ℝ) (r x)) = W := by
      refine subset_antisymm (Set.iUnion_subset fun x => (Metric.ball_subset_closedBall).trans (hrW x)) ?_
      intro y hy
      exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simpa using hrpos ⟨y, hy⟩⟩
    obtain ⟨T, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_iUnion_countable (fun x : W => Metric.ball (x : Fin 3 → ℝ) (r x))
        (fun _ => Metric.isOpen_ball)
    have hnull : (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
        (⋃ x ∈ T, (Metric.closedBall (x : Fin 3 → ℝ) (r x) ∩ {x | g x = 0})) = 0 := by
      rw [MeasureTheory.measure_biUnion_null_iff hTc]
      intro x _
      refine volume_closedBall_inter_zeroSet_eq_zero i (x : Fin 3 → ℝ) (r x) ?_ ?_ ?_
      · exact hUc.mono (fun y hy => hWU (hrW x hy))
      · intro y hy
        exact ((hg.contDiffAt (hU.mem_nhds (hWU (hrW x hy)))).differentiableAt
          (by norm_num)).hasFDerivAt
      · intro y hy
        exact hWne y (hrW x hy)
    have hsub : W ∩ {x | g x = 0} ⊆
        ⋃ x ∈ T, (Metric.closedBall (x : Fin 3 → ℝ) (r x) ∩ {x | g x = 0}) := by
      intro y hy
      have hy' : y ∈ ⋃ x : W, Metric.ball (x : Fin 3 → ℝ) (r x) := by
        rw [hcover]
        exact hy.1
      rw [← hTeq] at hy'
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy' ⊢
      obtain ⟨x, hxT, hbxy⟩ := hy'
      exact ⟨x, hxT, Metric.ball_subset_closedBall hbxy, hy.2⟩
    exact MeasureTheory.measure_mono_null hsub hnull
  have hne : ∀ x ∈ U, g x = 0 → ∃ i : Fin 3, fderiv ℝ g x (Pi.single i (1:ℝ)) ≠ 0 := by
    intro x hxU hx0
    by_contra hc
    push Not at hc
    exact h x hxU hx0 (clm_eq_zero_of_forall_single _ hc)
  have hdecomp : U ∩ {x | g x = 0} = ⋃ i : Fin 3,
      ((U ∩ {x | 0 < fderiv ℝ g x (Pi.single i (1:ℝ))} ∩ {x | g x = 0})
        ∪ (U ∩ {x | fderiv ℝ g x (Pi.single i (1:ℝ)) < 0} ∩ {x | g x = 0})) := by
    ext x
    constructor
    · rintro ⟨hxU, hx0⟩
      obtain ⟨i, hi⟩ := hne x hxU hx0
      rcases lt_trichotomy (fderiv ℝ g x (Pi.single i (1:ℝ))) 0 with hlt | heq | hgt
      · exact Set.mem_iUnion.2 ⟨i, Or.inr ⟨⟨hxU, hlt⟩, hx0⟩⟩
      · exact absurd heq hi
      · exact Set.mem_iUnion.2 ⟨i, Or.inl ⟨⟨hxU, hgt⟩, hx0⟩⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      rcases hi with ⟨hi, hx0⟩ | ⟨hi, hx0⟩
      · exact ⟨hi.1, hx0⟩
      · exact ⟨hi.1, hx0⟩
  rw [hdecomp]
  refine MeasureTheory.measure_iUnion_null (fun i => ?_)
  exact MeasureTheory.measure_union_null
    (hpiece i (U ∩ {x | 0 < fderiv ℝ g x (Pi.single i (1:ℝ))})
      ((hφ i).isOpen_inter_preimage hU isOpen_Ioi) Set.inter_subset_left
      (fun x hx => ne_of_gt hx.2))
    (hpiece i (U ∩ {x | fderiv ℝ g x (Pi.single i (1:ℝ)) < 0})
      ((hφ i).isOpen_inter_preimage hU isOpen_Iio) Set.inter_subset_left
      (fun x hx => ne_of_lt hx.2))

/-! ## The requested statement -/

/-- The zero set of a `C¹` function on an open set, on which its gradient never vanishes, is
Lebesgue-null.  (Route: at every point of the zero set choose a coordinate direction `i` in which
the partial derivative is non-zero; the set is covered by countably many open boxes on which `∂_i g`
has constant sign and there the restriction of `g` to every line parallel to `e_i` is strictly
monotone, so the zero set meets each such line in at most one point; Fubini.  Alternatively: the
zero set is locally the graph of a `C¹` function of two variables (via the local inverse of
`x ↦ (Q x, g x)`, with `Q` the projection forgetting the coordinate `i`), hence of Hausdorff
dimension at most `2`; then `μH[3]` of it vanishes and
`Measure.absolutelyContinuous_isAddHaarMeasure` converts that into Lebesgue-nullity.) -/
theorem volume_zeroSet_eq_zero {U : Set (LeanEval.KnotTheory.PardonDistortion.R3)}
    (hU : IsOpen U) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ}
    (hg : ContDiffOn ℝ 1 g U) (h : ∀ x ∈ U, g x = 0 → fderiv ℝ g x ≠ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure LeanEval.KnotTheory.PardonDistortion.R3)
      (U ∩ {x | g x = 0}) = 0 := by
  classical
  have htoLp_cont : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous
    rwa [PiLp.coe_symm_continuousLinearEquiv] at h
  have htoLp_diff : ContDiff ℝ 1 (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) :=
    PiLp.contDiff_toLp
  have hU' : IsOpen (WithLp.toLp 2 ⁻¹' U) := htoLp_cont.isOpen_preimage U hU
  have hg' : ContDiffOn ℝ 1 (g ∘ WithLp.toLp 2) (WithLp.toLp 2 ⁻¹' U) := by
    refine hg.comp htoLp_diff.contDiffOn ?_
    intro x hx
    exact hx
  have h' : ∀ y ∈ (WithLp.toLp 2 ⁻¹' U), (g ∘ WithLp.toLp 2) y = 0 →
      fderiv ℝ (g ∘ WithLp.toLp 2) y ≠ 0 := by
    intro y hy hgy hzero
    have htyU : WithLp.toLp 2 y ∈ U := hy
    have hgy0 : g (WithLp.toLp 2 y) = 0 := hgy
    refine h (WithLp.toLp 2 y) htyU hgy0 ?_
    have hdiffg : HasFDerivAt g (fderiv ℝ g (WithLp.toLp 2 y)) (WithLp.toLp 2 y) :=
      ((hg.contDiffAt (hU.mem_nhds htyU)).differentiableAt (by norm_num)).hasFDerivAt
    have htoLc := PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 y
    have hcomp := hdiffg.comp y htoLc
    have hfderiv : fderiv ℝ (g ∘ WithLp.toLp 2) y
        = (fderiv ℝ g (WithLp.toLp 2 y)).comp
          ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm : (Fin 3 → ℝ) →L[ℝ] R3) :=
      hcomp.fderiv
    rw [hfderiv] at hzero
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h2 := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (WithLp.ofLp v)) hzero
    simpa [PiLp.coe_symm_continuousLinearEquiv] using h2
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      ((WithLp.toLp 2 ⁻¹' U) ∩ {x : Fin 3 → ℝ | (g ∘ WithLp.toLp 2) x = 0}) = 0 :=
    volume_zeroSet_eq_zero_pi hU' hg' h'
  have hpre : (WithLp.ofLp : R3 → (Fin 3 → ℝ)) ⁻¹'
        ((WithLp.toLp 2 ⁻¹' U) ∩ {x : Fin 3 → ℝ | (g ∘ WithLp.toLp 2) x = 0})
      = U ∩ {x : R3 | g x = 0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
  have hprenull : (MeasureTheory.volume : MeasureTheory.Measure R3)
      ((WithLp.ofLp : R3 → (Fin 3 → ℝ)) ⁻¹'
        ((WithLp.toLp 2 ⁻¹' U) ∩ {x : Fin 3 → ℝ | (g ∘ WithLp.toLp 2) x = 0})) = 0 :=
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.preimage_null hnull
  rw [hpre] at hprenull
  exact hprenull

end Work.Drive.Mono.Band
