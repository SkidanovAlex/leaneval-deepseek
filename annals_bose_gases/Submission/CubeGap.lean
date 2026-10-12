import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import ChallengeDeps
import Submission.CubeDev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real ENNReal

namespace Submission.BoseGases

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev cgF3 := Fin 3 → ℝ
abbrev cgF2 := Fin 2 → ℝ

/-- restricted measure on the function-space cube `Fin d → ℝ` -/
noncomputable def cgPi (d : ℕ) (L : ℝ) : Measure (Fin d → ℝ) :=
  (volume : Measure (Fin d → ℝ)).restrict (cubeF d L)

lemma cg_peel3_mp (L : ℝ) (k : Fin 3) :
    MeasurePreserving (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k))
      (cgPi 3 L)
      (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
  rw [cgPi, cgPi, restrict_cubeF_eq_pi 3 L, restrict_cubeF_eq_pi 2 L]
  have h := measurePreserving_piFinSuccAbove (μ := fun _ : Fin 3 => (volume : Measure ℝ).restrict (CI L)) k
  simpa using h

/-- insertion of the `k`-th coordinate -/
noncomputable def cgIns (k : Fin 3) : ℝ × cgF2 ≃ᵐ cgF3 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k).symm

lemma cg_ins_mp (L : ℝ) (k : Fin 3) : MeasurePreserving (⇑(cgIns k))
    (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) (cgPi 3 L) := by
  dsimp [cgIns]
  exact (MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) k) (cg_peel3_mp L k))

lemma cg_ins_coord (k : Fin 3) (t : ℝ) (c : cgF2) : (cgIns k (t, c)) k = t := by
  dsimp [cgIns]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma cg_ins_succ (k : Fin 3) (t : ℝ) (c : cgF2) (j : Fin 2) :
    (cgIns k (t, c)) (k.succAbove j) = c j := by
  dsimp [cgIns]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma cg_update_ins (k : Fin 3) (t s : ℝ) (c : cgF2) :
    Function.update (cgIns k (t, c)) k s = cgIns k (s, c) := by
  funext j
  by_cases hj : j = k
  · subst j
    simp [Function.update, cg_ins_coord]
  · rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
    rw [← hz]
    simp [Function.update, cg_ins_succ]

/-- inserting `(t,c)` and then reading coordinate `j ≠ k` gives the value stored in `c` -/
lemma cg_ins_other (k : Fin 3) (t : ℝ) (c : cgF2) {j : Fin 3} (hj : j ≠ k) :
    ∃ z : Fin 2, (cgIns k (t, c)) j = c z := by
  rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← hz]
  exact cg_ins_succ k t c z

/-- transport between the function cube and the Euclidean cube -/
noncomputable def cgEuc : cgF3 ≃ᵐ ℝ³ := MeasurableEquiv.toLp 2 (cgF3)

lemma cg_euc_mp : MeasurePreserving (⇑cgEuc) (volume : Measure cgF3)
    (volume : Measure ℝ³) := by
  dsimp [cgEuc]
  simpa [MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (Fin 3))

/-- `cube L` in E3 is the image of the function-space cube. -/
lemma cg_cube_eq_image_cubeF (L : ℝ) : cube L = cgEuc '' cubeF 3 L := by
  ext y
  constructor
  · intro hy
    refine ⟨cgEuc.symm y, ?_, ?_⟩
    · intro k
      have hyk : y k ∈ CI L := hy k
      simpa [cgEuc, cubeF, CI] using hyk
    · simp [cgEuc]
  · rintro ⟨x, hx, rfl⟩
    intro k
    simpa [cgEuc, cubeF, CI] using hx k

/-- restricted cube measures agree under the transport -/
lemma cg_restrict_cube_eq_map (L : ℝ) :
    (volume : Measure ℝ³).restrict (cube L) =
      Measure.map (⇑cgEuc) ((volume : Measure cgF3).restrict (cubeF 3 L)) := by
  have hmap := cg_euc_mp.map_eq
  rw [← hmap, cg_cube_eq_image_cubeF]
  have hs : MeasurableSet (cgEuc '' cubeF 3 L) := (cgEuc.measurableSet_image).2 (cubeF_measurable 3 L)
  rw [Measure.restrict_map (by measurability : Measurable (⇑cgEuc)) hs]
  rw [Set.preimage_image_eq _ (MeasurableEquiv.injective cgEuc)]

/-- measure-preserving transport of the cube-restricted measures -/
lemma cg_euc_mp_restrict (L : ℝ) : MeasurePreserving (⇑cgEuc)
    ((volume : Measure cgF3).restrict (cubeF 3 L))
    ((volume : Measure ℝ³).restrict (cube L)) := by
  refine MeasurePreserving.mk cgEuc.measurable ?_
  exact (cg_restrict_cube_eq_map L).symm

/-- cube real integral equals function-space real integral -/
lemma cg_integral_cube_eq_cubeF {L : ℝ} {g : ℝ³ → ℝ} :
    (∫ y in cube L, g y) = ∫ x : cgF3, g (cgEuc x) ∂(cgPi 3 L) := by
  have hmp := cg_euc_mp_restrict L
  have h := hmp.integral_comp cgEuc.measurableEmbedding g
  -- h : ∫ x : cgF3, g (cgEuc x) ∂restrict_cubeF = ∫ y : ℝ³, g y ∂restrict_cube
  simpa [cgPi] using h.symm

/-- the function-space cube is compact -/
lemma cg_cubeF_compact (d : ℕ) (L : ℝ) : IsCompact (cubeF d L) := by
  have h := isCompact_pi_infinite (s := fun _ : Fin d => (Set.Icc (0 : ℝ) L))
    (by intro i; exact isCompact_Icc)
  simpa [cubeF, CI] using h

/-- cubeF is measurable -/
lemma cg_cubeF_meas (d : ℕ) (L : ℝ) : MeasurableSet (cubeF d L) := cubeF_measurable d L

/-- restricted cube measure on `Fin d → ℝ` has finite total mass -/
lemma cg_pi_finite {d : ℕ} {L : ℝ} (hL : 0 < L) : (cgPi d L) Set.univ < (⊤ : ℝ≥0∞) := by
  dsimp [cgPi]
  rw [Measure.restrict_apply_univ]
  exact IsCompact.measure_lt_top (cg_cubeF_compact d L)

/-- constant functions are integrable w.r.t. the restricted cube measure -/
lemma cg_integrable_const_pi {d : ℕ} {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Integrable (fun _ : Fin d → ℝ => c) (cgPi d L) := by
  have hfin : IsFiniteMeasure (cgPi d L) := ⟨cg_pi_finite (d := d) hL⟩
  letI : IsFiniteMeasure (cgPi d L) := hfin
  exact (integrable_const_iff).2 (Or.inr hfin)

/-- a function bounded by a constant a.e. is integrable on the restricted cube -/
lemma cg_integrable_of_ae_bound {d : ℕ} {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℝ}
    (hm : AEStronglyMeasurable f (cgPi d L)) {C : ℝ} (hC : ∀ᵐ x ∂(cgPi d L), |f x| ≤ C) :
    Integrable f (cgPi d L) := by
  exact Integrable.mono' (cg_integrable_const_pi (d := d) hL C) hm hC



/-! ## Fibre means and slice derivatives on the function-space cube -/

/-- fibre mean over coordinate `k` (average over the interval `[0,L]`) -/
noncomputable def cgMean (L : ℝ) (k : Fin 3) (f : cgF3 → ℝ) : cgF3 → ℝ :=
  fun x => (1 / L) * (∫ s in (0 : ℝ)..L, f (Function.update x k s))

/-- slice derivative in coordinate `k` -/
noncomputable def cgSlice (k : Fin 3) (f : cgF3 → ℝ) : cgF3 → ℝ :=
  fun x => deriv (fun s : ℝ => f (Function.update x k s)) (x k)

lemma cg_slice_at_ins (k : Fin 3) (f : cgF3 → ℝ) (t : ℝ) (c : cgF2) :
    cgSlice k f (cgIns k (t, c)) = deriv (fun s : ℝ => f (cgIns k (s, c))) t := by
  dsimp [cgSlice]
  rw [cg_ins_coord]
  congr 1
  rw [show (fun s : ℝ => f (Function.update (cgIns k (t, c)) k s)) =
      fun s : ℝ => f (cgIns k (s, c)) by
    funext s
    rw [cg_update_ins]]

lemma cg_mean_at_ins (L : ℝ) (k : Fin 3) (f : cgF3 → ℝ) (t : ℝ) (c : cgF2) :
    cgMean L k f (cgIns k (t, c)) = (1 / L) * (∫ s in (0 : ℝ)..L, f (cgIns k (s, c))) := by
  dsimp [cgMean]
  congr 1
  rw [show (fun s : ℝ => f (Function.update (cgIns k (t, c)) k s)) =
      fun s : ℝ => f (cgIns k (s, c)) by
    funext s
    rw [cg_update_ins]]

/-- `s ↦ Function.update x k s` is smooth -/
lemma cg_update_contDiff {n : ℕ∞ω} (k : Fin 3) (x : cgF3) :
    ContDiff ℝ n (fun s : ℝ => Function.update x k s) :=
  contDiff_update (𝕜 := ℝ) (ι := Fin 3) (F' := fun _ : Fin 3 => ℝ) (k := n) x k

/-- the fibre function `s ↦ f (update x k s)` is C¹ when `f` is -/
lemma cg_fibre_contDiff {k : Fin 3} {f : cgF3 → ℝ} (hf : ContDiff ℝ 1 f) (x : cgF3) :
    ContDiff ℝ 1 (fun s : ℝ => f (Function.update x k s)) := by
  change ContDiff ℝ 1 (f ∘ (fun s : ℝ => Function.update x k s))
  exact ContDiff.comp hf (cg_update_contDiff (n := (1 : ℕ∞ω)) k x)

/-- the fibre function is continuous -/
lemma cg_fibre_cont {k : Fin 3} {f : cgF3 → ℝ} (hf : Continuous f) (x : cgF3) :
    Continuous (fun s : ℝ => f (Function.update x k s)) := by
  exact hf.comp (cg_update_contDiff (n := (0 : ℕ∞ω)) k x).continuous

/-- the fibre integrand is interval-integrable -/
lemma cg_fibre_intervalInt {L : ℝ} {k : Fin 3} {f : cgF3 → ℝ} (hf : Continuous f) (x : cgF3) :
    IntervalIntegrable (fun s : ℝ => f (Function.update x k s)) volume 0 L := by
  exact (cg_fibre_cont (k := k) hf x).intervalIntegrable 0 L

/-- mean of the fibre difference is zero -/
lemma cg_mean_zero_fibre {L : ℝ} (hL : 0 < L) {k : Fin 3} {f : cgF3 → ℝ}
    (hf : Continuous f) (x : cgF3) :
    (∫ s in (0 : ℝ)..L, (f (Function.update x k s) - cgMean L k f x)) = 0 := by
  have hfi : IntervalIntegrable (fun s : ℝ => f (Function.update x k s)) volume 0 L :=
    cg_fibre_intervalInt (L := L) hf x
  have hsub := intervalIntegral.integral_sub (μ := volume) (f := fun s : ℝ => f (Function.update x k s))
    (g := fun _ : ℝ => cgMean L k f x) hfi (intervalIntegrable_const (μ := volume))
  rw [hsub]
  dsimp [cgMean]
  rw [intervalIntegral.integral_const]
  simp
  field_simp [ne_of_gt hL]
  ring



/-- coordinate unit vector of the function space -/
noncomputable def cgDir (k : Fin 3) : cgF3 := Function.update (0 : cgF3) k (1 : ℝ)

lemma cg_dir_apply (k : Fin 3) (j : Fin 3) : cgDir k j = if j = k then 1 else 0 := by
  by_cases hj : j = k
  · subst j
    simp [cgDir]
  · simp [cgDir, hj]

lemma cg_add_dir_update (x : cgF3) (k : Fin 3) (t : ℝ) :
    x + t • cgDir k = Function.update x k (x k + t) := by
  funext j
  simp [cgDir, Pi.add_apply, Pi.smul_apply]
  by_cases hj : j = k
  · subst j
    simp [Function.update]
  · simp [Function.update, hj]

lemma cg_update_add (x : cgF3) (k : Fin 3) (s : ℝ) :
    Function.update x k s = x + (s - x k) • cgDir k := by
  rw [show x + (s - x k) • cgDir k = Function.update x k (x k + (s - x k)) by
    exact (cg_add_dir_update (x := x) (k := k) (t := s - x k))]
  congr 1
  ring

/-- the slice derivative equals the derivative of `f` in the coordinate direction -/
lemma cg_slice_eq_fderiv {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : cgF3) (k : Fin 3) :
    cgSlice k f x = fderiv ℝ f x (cgDir k) := by
  have hpath : (fun s : ℝ => Function.update x k s) = fun s : ℝ => x + (s - x k) • cgDir k := by
    funext s
    exact cg_update_add x k s
  have hcomp : (fun s : ℝ => f (Function.update x k s)) = fun s : ℝ => f (x + (s - x k) • cgDir k) := by
    funext s
    rw [cg_update_add]
  -- derivative of the path at `s = x k`
  have h1 : HasDerivAt (fun s : ℝ => x + (s - x k) • cgDir k) (cgDir k) (x k) := by
    let base : cgF3 := x + (-(x k)) • cgDir k
    have hb : HasDerivAt (fun _ : ℝ => base) 0 (x k) := hasDerivAt_const _ _
    have hid2 : HasDerivAt (fun t : ℝ => t • cgDir k) (cgDir k) (x k) := by
      simpa using (hasDerivAt_id (x k)).smul_const (cgDir k)
    have ht := hb.add hid2
    have hfun : (fun _ : ℝ => base) + (fun t : ℝ => t • cgDir k) =
        fun s : ℝ => x + (s - x k) • cgDir k := by
      funext s
      dsimp [base]
      simp [sub_eq_add_neg, add_smul, smul_add]
      abel
    rw [show (fun _ : ℝ => base) + (fun t : ℝ => t • cgDir k) =
        fun s : ℝ => x + (s - x k) • cgDir k by exact hfun] at ht
    simpa using ht
  have hpt : x + (x k - x k) • cgDir k = x := by simp
  have hfd : DifferentiableAt ℝ f (x + (x k - x k) • cgDir k) := by
    simpa [hpt] using (hf.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) x)
  have hmain := HasFDerivAt.comp_hasDerivAt (x k) hfd.hasFDerivAt h1
  -- hmain : HasDerivAt (fun s => f (x + (s - xk) • dir)) (fderiv ℝ f (x + 0•dir) dir) (x k)
  have hder : deriv (fun s : ℝ => f (x + (s - x k) • cgDir k)) (x k) = fderiv ℝ f x (cgDir k) := by
    change deriv (f ∘ (fun s : ℝ => x + (s - x k) • cgDir k)) (x k) = fderiv ℝ f x (cgDir k)
    simpa [hpt] using hmain.deriv
  dsimp [cgSlice]
  rw [hcomp]
  exact hder

/-- `x ↦ fderiv f x u` is smooth for smooth `f` -/
lemma cg_firstDir_contDiff {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) (u : cgF3) :
    ContDiff ℝ ∞ (fun x : cgF3 => fderiv ℝ f x u) := by
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := ContDiff.fderiv_right (m := ∞) hf (by simp)
  exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (cgF3 →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff).comp hf1

/-- the slice derivative is smooth -/
lemma cg_slice_contDiff {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) (k : Fin 3) :
    ContDiff ℝ ∞ (cgSlice k f) := by
  have h : cgSlice k f = fun x : cgF3 => fderiv ℝ f x (cgDir k) := by
    funext x
    exact cg_slice_eq_fderiv hf x k
  rw [h]
  exact cg_firstDir_contDiff hf (cgDir k)

/-- the mean over a fibre is continuous on the cube -/
lemma cg_mean_continuousOn {L : ℝ} (hL0 : 0 ≤ L) {k : Fin 3} {f : cgF3 → ℝ}
    (hf : Continuous f) : ContinuousOn (cgMean L k f) (cubeF 3 L) := by
  -- bound of f on the compact cube
  obtain ⟨C, hC⟩ := (cg_cubeF_compact 3 L).exists_bound_of_continuousOn
    (fun x hx => hf.continuousOn x hx)
  -- express the interval integral as a measure integral over `Ioc 0 L`
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) L)
  have hfInt : ∀ x ∈ cubeF 3 L, AEStronglyMeasurable (fun s : ℝ => f (Function.update x k s)) μ := by
    intro x hx
    exact (cg_fibre_cont (k := k) hf x).aestronglyMeasurable
  have hbnd : ∀ x ∈ cubeF 3 L, ∀ᵐ s ∂μ, |f (Function.update x k s)| ≤ C := by
    intro x hx
    rw [ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) L))]
    apply ae_of_all
    intro s hs
    have hxup : Function.update x k s ∈ cubeF 3 L := by
      intro j
      by_cases hj : j = k
      · subst j
        simp [Function.update, CI]
        exact ⟨le_of_lt hs.1, hs.2⟩
      · have hxj : x j ∈ CI L := hx j
        simpa [Function.update, hj] using hxj
    exact hC (Function.update x k s) hxup
  have hcont : ∀ᵐ s ∂μ, ContinuousOn (fun x : cgF3 => f (Function.update x k s)) (cubeF 3 L) := by
    apply ae_of_all
    intro s
    exact (hf.comp (by fun_prop : Continuous (fun x : cgF3 => Function.update x k s))).continuousOn
  have hbndint : Integrable (fun _ : ℝ => C) μ := by
    have hfin : μ Set.univ < (⊤ : ℝ≥0∞) := by
      dsimp [μ]
      rw [Measure.restrict_apply_univ]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hfinM : IsFiniteMeasure μ := ⟨hfin⟩
    letI : IsFiniteMeasure μ := hfinM
    exact (integrable_const_iff).2 (Or.inr hfinM)
  have hcontI : ContinuousOn (fun x : cgF3 => (∫ s : ℝ, f (Function.update x k s) ∂μ)) (cubeF 3 L) :=
    continuousOn_of_dominated (μ := μ) (s := cubeF 3 L) (F := fun (x : cgF3) (s : ℝ) =>
      f (Function.update x k s)) (bound := fun _ : ℝ => C) hfInt hbnd hbndint hcont
  have hfin2 : ContinuousOn (fun x : cgF3 => (1 / L) * (∫ s : ℝ, f (Function.update x k s) ∂μ)) (cubeF 3 L) := by
    exact hcontI.const_mul (1 / L)
  convert hfin2 using 1
  funext x
  dsimp [cgMean]
  rw [intervalIntegral.integral_of_le hL0]

/-! ## Interval-integral conversions and 1D fibre Poincaré -/

/-- integral over `CI L` (restricted measure) equals the interval integral -/
lemma cg_interval_eq_restrict {L : ℝ} (hL0 : 0 ≤ L) (g : ℝ → ℝ) :
    (∫ t : ℝ, g t ∂((volume : Measure ℝ).restrict (CI L))) = ∫ t in (0 : ℝ)..L, g t := by
  rw [← integral_Icc_eq_interval hL0 g]
  rfl

/-- integrable w.r.t. the restricted cube measure for functions continuous on the cube -/
lemma cg_integrable_pi_of_contOn {d : ℕ} {L : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContinuousOn f (cubeF d L)) : Integrable f (cgPi d L) := by
  dsimp [cgPi]
  exact ContinuousOn.integrableOn_compact (cg_cubeF_compact d L) hf

/-- fibre Poincaré per fixed `c` (interval-integral form) -/
lemma cg_fp_fibre_interval {L : ℝ} (hL : 0 < L) (k : Fin 3) {f : cgF3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : cgF2) :
    (∫ x in (0 : ℝ)..L, (f (cgIns k (x, c)) - cgMean L k f (cgIns k (0, c))) ^ 2) ≤
      L ^ 2 * (∫ x in (0 : ℝ)..L, (cgSlice k f (cgIns k (x, c))) ^ 2) := by
  let f0 : ℝ → ℝ := fun s => f (cgIns k (s, c))
  let m0 : ℝ := cgMean L k f (cgIns k (0, c))
  have hf0 : ContDiff ℝ 1 f0 := by
    have hfib : ContDiff ℝ 1 (fun s : ℝ => f (Function.update (cgIns k (0, c)) k s)) :=
      cg_fibre_contDiff (k := k) (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))) (cgIns k (0, c))
    have hfeq : f0 = fun s : ℝ => f (Function.update (cgIns k (0, c)) k s) := by
      funext s
      dsimp [f0]
      rw [cg_update_ins]
    rw [hfeq]
    exact hfib
  have hm : (∫ x in (0 : ℝ)..L, (f0 x - m0)) = 0 := by
    have hm0 := cg_mean_zero_fibre (L := L) hL (k := k) hf.continuous (cgIns k (0, c))
    dsimp [f0, m0]
    rw [show (fun x : ℝ => f (cgIns k (x, c)) - cgMean L k f (cgIns k (0, c))) =
        fun x : ℝ => f (Function.update (cgIns k (0, c)) k x) - cgMean L k f (cgIns k (0, c)) by
      funext x
      congr 1
      rw [cg_update_ins]]
    exact hm0
  have hI := mean_zero_poincare_interval hL hf0 hm
  calc
    (∫ x in (0 : ℝ)..L, (f (cgIns k (x, c)) - cgMean L k f (cgIns k (0, c))) ^ 2)
        ≤ L ^ 2 * (∫ x in (0 : ℝ)..L, (deriv f0 x) ^ 2) := by
          simpa [f0, m0] using hI
    _ = L ^ 2 * (∫ x in (0 : ℝ)..L, (cgSlice k f (cgIns k (x, c))) ^ 2) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp [f0]
          exact congrArg (fun y : ℝ => y ^ 2) (cg_slice_at_ins k f x c).symm

/-- integrand of the fibre Poincaré LHS, as a function of the peeled pair -/
noncomputable def cgFpA (L : ℝ) (k : Fin 3) (f : cgF3 → ℝ) : ℝ × cgF2 → ℝ :=
  fun p => (f (cgIns k p) - cgMean L k f (cgIns k (0, p.2))) ^ 2

/-- integrand of the fibre Poincaré RHS, as a function of the peeled pair -/
noncomputable def cgFpB (k : Fin 3) (f : cgF3 → ℝ) : ℝ × cgF2 → ℝ :=
  fun p => (cgSlice k f (cgIns k p)) ^ 2

/-- `cgIns k` is continuous -/
lemma cg_ins_cont (k : Fin 3) : Continuous (fun p : ℝ × cgF2 => cgIns k p) := by
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    have hfun : (fun p : ℝ × cgF2 => (cgIns k p) k) = fun p : ℝ × cgF2 => p.1 := by
      funext p
      exact cg_ins_coord k p.1 p.2
    rw [hfun]
    exact continuous_fst
  · rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
    rw [← hz]
    have hfun : (fun p : ℝ × cgF2 => (cgIns k p) (k.succAbove z)) = fun p : ℝ × cgF2 => p.2 z := by
      funext p
      exact cg_ins_succ k p.1 p.2 z
    rw [hfun]
    exact (continuous_apply z).comp continuous_snd

/-- `c ↦ cgIns k (0, c)` is continuous -/
lemma cg_ins0_cont (k : Fin 3) : Continuous (fun c : cgF2 => cgIns k (0, c)) := by
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    have hfun : (fun c : cgF2 => (cgIns k (0, c)) k) = fun _ : cgF2 => (0 : ℝ) := by
      funext c
      exact cg_ins_coord k 0 c
    rw [hfun]
    exact continuous_const
  · rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
    rw [← hz]
    have hfun : (fun c : cgF2 => (cgIns k (0, c)) (k.succAbove z)) = fun c : cgF2 => c z := by
      funext c
      exact cg_ins_succ k 0 c z
    rw [hfun]
    exact continuous_apply z

lemma cg_ins0_maps_param {L : ℝ} (hL0 : 0 ≤ L) {k : Fin 3} {c : cgF2} (hc : c ∈ cubeF 2 L) :
    cgIns k (0, c) ∈ cubeF 3 L := by
  intro j
  by_cases hj : j = k
  · subst j
    have hz : c (0 : Fin 2) ∈ CI L := hc 0
    simp [cg_ins_coord, CI, hL0]
  · rcases Fin.exists_succAbove_eq hj with ⟨z, hz⟩
    rw [← hz]
    have hx2 : c z ∈ CI L := hc z
    simpa [cg_ins_succ] using hx2

/-- continuity of the mean over the fibre, pulled back to the parameter cube -/
lemma cg_mean_contOn_param {L : ℝ} (hL0 : 0 ≤ L) {k : Fin 3} {f : cgF3 → ℝ}
    (hf : Continuous f) :
    ContinuousOn (fun c : cgF2 => cgMean L k f (cgIns k (0, c))) (cubeF 2 L) := by
  have hmean := cg_mean_continuousOn (L := L) hL0 (k := k) hf
  exact hmean.comp (cg_ins0_cont k).continuousOn (fun x hx => cg_ins0_maps_param (L := L) hL0 (k := k) hx)

/-- the fibre Poincaré LHS integrand is continuous on the peeled cube -/
lemma cg_fpA_contOn {L : ℝ} (hL0 : 0 ≤ L) (k : Fin 3) {f : cgF3 → ℝ}
    (hf : Continuous f) : ContinuousOn (cgFpA L k f) ((CI L) ×ˢ (cubeF 2 L)) := by
  have h1 : ContinuousOn (fun p : ℝ × cgF2 => f (cgIns k p)) ((CI L) ×ˢ (cubeF 2 L)) :=
    (hf.comp (cg_ins_cont k)).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × cgF2 => cgMean L k f (cgIns k (0, p.2)))
      ((CI L) ×ˢ (cubeF 2 L)) := by
    have hpar := cg_mean_contOn_param (L := L) hL0 (k := k) hf
    exact hpar.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hsub : ContinuousOn (fun p : ℝ × cgF2 =>
      f (cgIns k p) - cgMean L k f (cgIns k (0, p.2))) ((CI L) ×ˢ (cubeF 2 L)) := h1.sub h2
  have hsq : ContinuousOn (fun p : ℝ × cgF2 =>
      (f (cgIns k p) - cgMean L k f (cgIns k (0, p.2))) ^ 2) ((CI L) ×ˢ (cubeF 2 L)) :=
    hsub.pow 2
  exact hsq

/-- the fibre Poincaré RHS integrand is continuous on the peeled cube -/
lemma cg_fpB_contOn {L : ℝ} (k : Fin 3) {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (cgFpB k f) ((CI L) ×ˢ (cubeF 2 L)) := by
  have hcont : Continuous (fun p : ℝ × cgF2 => cgSlice k f (cgIns k p)) :=
    (cg_slice_contDiff hf k).continuous.comp (cg_ins_cont k)
  change ContinuousOn (fun p : ℝ × cgF2 => (cgSlice k f (cgIns k p)) ^ 2) ((CI L) ×ˢ (cubeF 2 L))
  exact hcont.continuousOn.pow 2

/-- integrability of the peeled Poincaré integrand -/
lemma cg_fpA_integrable {L : ℝ} (hL0 : 0 ≤ L) (k : Fin 3) {f : cgF3 → ℝ} (hf : Continuous f) :
    Integrable (cgFpA L k f) (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
  rw [cgPi, Measure.prod_restrict]
  exact ContinuousOn.integrableOn_compact
    (IsCompact.prod isCompact_Icc (cg_cubeF_compact 2 L)) (cg_fpA_contOn hL0 (k := k) hf)

/-- integrability of the peeled derivative integrand -/
lemma cg_fpB_integrable {L : ℝ} (k : Fin 3) {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    Integrable (cgFpB k f) (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
  rw [cgPi, Measure.prod_restrict]
  exact ContinuousOn.integrableOn_compact
    (IsCompact.prod isCompact_Icc (cg_cubeF_compact 2 L)) (cg_fpB_contOn (L := L) k hf)

instance cg_pi_sfinite (d : ℕ) (L : ℝ) : SFinite (cgPi d L) := by
  dsimp [cgPi]
  infer_instance

instance cg_restrict_CI_sfinite (L : ℝ) : SFinite ((volume : Measure ℝ).restrict (CI L)) := by
  dsimp [CI]
  infer_instance

instance cg_restrict_cubeF_sfinite (d : ℕ) (L : ℝ) :
    SFinite ((volume : Measure (Fin d → ℝ)).restrict (cubeF d L)) := by
  infer_instance

/-- Fubini: integral over the peeled product equals iterated integral (outer = parameter) -/
lemma cg_fubini_param {L : ℝ} {F : ℝ × cgF2 → ℝ} (hF : Integrable F
    (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) :
    (∫ p : ℝ × cgF2, F p ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      ∫ c : cgF2, (∫ t : ℝ, F (t, c) ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L) := by
  exact integral_prod_symm F hF

/-- cube integral expressed through the peel -/
lemma cg_integral_peel {L : ℝ} (k : Fin 3) (g : cgF3 → ℝ) :
    (∫ x : cgF3, g x ∂(cgPi 3 L)) =
      ∫ p : ℝ × cgF2, g (cgIns k p)
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
  exact (MeasurePreserving.integral_comp' (cg_ins_mp L k) g).symm

/-! ## Fibre Poincaré (full cube) -/

/-- the mean is constant along the peeled fibre -/
lemma cg_mean_ins_const {L : ℝ} (k : Fin 3) (f : cgF3 → ℝ) (t : ℝ) (c : cgF2) :
    cgMean L k f (cgIns k (t, c)) = cgMean L k f (cgIns k (0, c)) := by
  rw [cg_mean_at_ins, cg_mean_at_ins]

/-- peeled LHS integrand of the fibre Poincaré -/
lemma cg_fpA_peel {L : ℝ} (k : Fin 3) (f : cgF3 → ℝ) :
    (fun p : ℝ × cgF2 => (f (cgIns k p) - cgMean L k f (cgIns k p)) ^ 2) = cgFpA L k f := by
  funext p
  dsimp [cgFpA]
  rw [cg_mean_ins_const (L := L) k f p.1 p.2]

/-- the peeled derivative integrand matches the definition -/
lemma cg_fpB_peel (k : Fin 3) (f : cgF3 → ℝ) :
    (fun p : ℝ × cgF2 => (cgSlice k f (cgIns k p)) ^ 2) = cgFpB k f := by
  funext p
  rfl

/-- per-`c` fibre Poincaré in ν-integral form -/
lemma cg_fp_fibre_restrict {L : ℝ} (hL : 0 < L) (k : Fin 3) {f : cgF3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : cgF2) :
    (∫ t : ℝ, cgFpA L k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) ≤
      L ^ 2 * (∫ t : ℝ, cgFpB k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) := by
  have hI := cg_fp_fibre_interval (L := L) hL k hf c
  -- rewrite both sides from interval to restricted-measure integrals
  have h1 : (∫ t : ℝ, cgFpA L k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) =
      (∫ x in (0 : ℝ)..L, (f (cgIns k (x, c)) - cgMean L k f (cgIns k (0, c))) ^ 2) := by
    dsimp [cgFpA]
    exact cg_interval_eq_restrict hL.le (fun t : ℝ => (f (cgIns k (t, c)) - cgMean L k f (cgIns k (0, c))) ^ 2)
  have h2 : (∫ t : ℝ, cgFpB k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) =
      (∫ x in (0 : ℝ)..L, (cgSlice k f (cgIns k (x, c))) ^ 2) := by
    dsimp [cgFpB]
    exact cg_interval_eq_restrict hL.le (fun t : ℝ => (cgSlice k f (cgIns k (t, c))) ^ 2)
  rw [h1, h2]
  exact hI

/-- fibre Poincaré for smooth `f` on the function cube -/
lemma cg_fp {L : ℝ} (hL : 0 < L) (k : Fin 3) {f : cgF3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    (∫ x : cgF3, (f x - cgMean L k f x) ^ 2 ∂(cgPi 3 L)) ≤
      L ^ 2 * (∫ x : cgF3, (cgSlice k f x) ^ 2 ∂(cgPi 3 L)) := by
  -- integrability of the peeled integrands
  have hAint : Integrable (cgFpA L k f)
      (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := cg_fpA_integrable hL.le k hf.continuous
  have hBint : Integrable (cgFpB k f)
      (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := cg_fpB_integrable (L := L) k hf
  -- peel the LHS
  have hpeelA : (∫ x : cgF3, (f x - cgMean L k f x) ^ 2 ∂(cgPi 3 L)) =
      ∫ p : ℝ × cgF2, cgFpA L k f p
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
    calc
      (∫ x : cgF3, (f x - cgMean L k f x) ^ 2 ∂(cgPi 3 L))
          = ∫ p : ℝ × cgF2, (f (cgIns k p) - cgMean L k f (cgIns k p)) ^ 2
              ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
            rw [cg_integral_peel]
      _ = ∫ p : ℝ × cgF2, cgFpA L k f p
              ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
            rw [cg_fpA_peel]
  -- fubini the LHS
  have hfubA : (∫ p : ℝ × cgF2, cgFpA L k f p
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      ∫ c : cgF2, (∫ t : ℝ, cgFpA L k f (t, c)
          ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L) := by
    exact integral_prod_symm (cgFpA L k f) hAint
  -- fubini the RHS peeled derivative integrand
  have hfubB : (∫ p : ℝ × cgF2, cgFpB k f p
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      ∫ c : cgF2, (∫ t : ℝ, cgFpB k f (t, c)
          ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L) := by
    exact integral_prod_symm (cgFpB k f) hBint
  -- integrability of the c ↦ ∫_t B(t,c) function
  have hpartB : Integrable (fun c : cgF2 => ∫ t : ℝ, cgFpB k f (t, c)
      ∂((volume : Measure ℝ).restrict (CI L))) (cgPi 2 L) := by
    have hnorm := Integrable.integral_norm_prod_right (μ := (volume : Measure ℝ).restrict (CI L))
      (ν := cgPi 2 L) (f := fun p : ℝ × cgF2 => cgFpB k f (p.1, p.2)) hBint
    -- hnorm : Integrable (fun c => ∫ t, ‖cgFpB k f (t, c)‖ ∂μ) (cgPi 2 L)
    convert hnorm using 1
    funext c
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.norm_eq_abs]
    simp [cgFpB]
  -- per-c inequality and monotonicity over the parameter
  have hineq_c : ∀ c : cgF2,
      (∫ t : ℝ, cgFpA L k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) ≤
        L ^ 2 * (∫ t : ℝ, cgFpB k f (t, c) ∂((volume : Measure ℝ).restrict (CI L))) := by
    intro c
    exact cg_fp_fibre_restrict (L := L) hL k hf c
  have hmono : (∫ c : cgF2, (∫ t : ℝ, cgFpA L k f (t, c)
        ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L)) ≤
      (∫ c : cgF2, (L ^ 2 * (∫ t : ℝ, cgFpB k f (t, c)
        ∂((volume : Measure ℝ).restrict (CI L)))) ∂(cgPi 2 L)) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact ae_of_all _ (fun c => integral_nonneg (fun t => sq_nonneg _))
    · exact hpartB.const_mul (L ^ 2)
    · exact ae_of_all _ hineq_c
  -- the RHS over c equals the peeled RHS
  have hRHS : (∫ c : cgF2, (L ^ 2 * (∫ t : ℝ, cgFpB k f (t, c)
        ∂((volume : Measure ℝ).restrict (CI L)))) ∂(cgPi 2 L)) =
      L ^ 2 * (∫ p : ℝ × cgF2, cgFpB k f p
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) := by
    rw [hfubB]
    rw [integral_const_mul]
  -- peel the RHS back to the cube
  have hpeelB : (∫ p : ℝ × cgF2, cgFpB k f p
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      (∫ x : cgF3, (cgSlice k f x) ^ 2 ∂(cgPi 3 L)) := by
    calc
      (∫ p : ℝ × cgF2, cgFpB k f p
          ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)))
          = ∫ p : ℝ × cgF2, (cgSlice k f (cgIns k p)) ^ 2
              ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
            rw [cg_fpB_peel]
      _ = (∫ x : cgF3, (cgSlice k f x) ^ 2 ∂(cgPi 3 L)) := by
            rw [cg_integral_peel (k := k) (g := fun x : cgF3 => (cgSlice k f x) ^ 2)]
  calc
    (∫ x : cgF3, (f x - cgMean L k f x) ^ 2 ∂(cgPi 3 L))
        ≤ L ^ 2 * (∫ x : cgF3, (cgSlice k f x) ^ 2 ∂(cgPi 3 L)) := by
      rw [hpeelA, hfubA]
      calc
        (∫ c : cgF2, (∫ t : ℝ, cgFpA L k f (t, c)
            ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L))
            ≤ (∫ c : cgF2, (L ^ 2 * (∫ t : ℝ, cgFpB k f (t, c)
                ∂((volume : Measure ℝ).restrict (CI L)))) ∂(cgPi 2 L)) := hmono
        _ = L ^ 2 * (∫ x : cgF3, (cgSlice k f x) ^ 2 ∂(cgPi 3 L)) := by
              rw [hRHS, hpeelB]

/-! ## Contraction (Jensen) for the fibre means -/

/-- continuous functions on the peeled product are integrable -/
lemma cg_integrable_prod_cont {L : ℝ} {F : ℝ × cgF2 → ℝ} (hF : Continuous F) :
    Integrable F (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
  rw [cgPi, Measure.prod_restrict]
  change Integrable F (((volume : Measure ℝ).prod (volume : Measure cgF2)).restrict
    ((CI L) ×ˢ (cubeF 2 L)))
  exact ContinuousOn.integrableOn_compact
    (IsCompact.prod isCompact_Icc (cg_cubeF_compact 2 L)) hF.continuousOn

/-- Jensen inequality for the fibre average (interval form) -/
lemma cg_jensen_interval {L : ℝ} (hL : 0 < L) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) L)) :
    ((1 / L) * (∫ x in (0 : ℝ)..L, u x)) ^ 2 ≤
      (1 / L) * (∫ x in (0 : ℝ)..L, (u x) ^ 2) := by
  have hcs := cs_interval hL.le (h := fun x : ℝ => |u x|)
    (by simpa using hu.abs) (fun x => abs_nonneg (u x))
  -- (∫|u|)^2 ≤ L * ∫ u²
  have h1 : (∫ x in (0 : ℝ)..L, |u x|) ^ 2 ≤ L * (∫ x in (0 : ℝ)..L, (u x) ^ 2) := by
    simpa [sq_abs] using hcs
  have h2 : (∫ x in (0 : ℝ)..L, u x) ^ 2 ≤ L * (∫ x in (0 : ℝ)..L, (u x) ^ 2) := by
    calc
      (∫ x in (0 : ℝ)..L, u x) ^ 2 = |∫ x in (0 : ℝ)..L, u x| ^ 2 := by rw [sq_abs]
      _ ≤ (∫ x in (0 : ℝ)..L, |u x|) ^ 2 := by
            exact pow_le_pow_left₀ (abs_nonneg _)
              (intervalIntegral.abs_integral_le_integral_abs hL.le) 2
      _ ≤ L * (∫ x in (0 : ℝ)..L, (u x) ^ 2) := h1
  calc
    ((1 / L) * (∫ x in (0 : ℝ)..L, u x)) ^ 2
        = (1 / L ^ 2) * (∫ x in (0 : ℝ)..L, u x) ^ 2 := by ring
    _ ≤ (1 / L ^ 2) * (L * (∫ x in (0 : ℝ)..L, (u x) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 / L) * (∫ x in (0 : ℝ)..L, (u x) ^ 2) := by
          field_simp [ne_of_gt hL]

/-- pointwise Jensen: the mean of `h` squared is at most the mean of `h²` -/
lemma cg_jensen_point {L : ℝ} (hL : 0 < L) {k : Fin 3} {h : cgF3 → ℝ}
    (hh : Continuous h) (x : cgF3) :
    (cgMean L k h x) ^ 2 ≤ cgMean L k (fun y => (h y) ^ 2) x := by
  have hu : ContinuousOn (fun s : ℝ => h (Function.update x k s)) (Set.Icc (0 : ℝ) L) :=
    (cg_fibre_cont (k := k) hh x).continuousOn
  have hJ := cg_jensen_interval hL hu
  -- hJ : ((1/L)*∫_s h(update x k s))² ≤ (1/L)∫_s (h(update x k s))²
  dsimp [cgMean]
  simpa using hJ

/-- the L² norm of the fibre mean is at most the norm of the function -/
lemma cg_contraction {L : ℝ} (hL : 0 < L) (k : Fin 3) {h : cgF3 → ℝ}
    (hh : Continuous h) :
    (∫ x : cgF3, (cgMean L k h x) ^ 2 ∂(cgPi 3 L)) ≤
      (∫ x : cgF3, (h x) ^ 2 ∂(cgPi 3 L)) := by
  -- peeled integrability and per-c Jensen
  have hJpt : ∀ x : cgF3, (cgMean L k h x) ^ 2 ≤ cgMean L k (fun y => (h y) ^ 2) x :=
    cg_jensen_point hL (k := k) hh
  -- LHS is integrable in peeled form
  have hpeel : (∫ x : cgF3, (cgMean L k h x) ^ 2 ∂(cgPi 3 L)) =
      ∫ p : ℝ × cgF2, (cgMean L k h (cgIns k p)) ^ 2
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) := by
    rw [cg_integral_peel (k := k) (g := fun x : cgF3 => (cgMean L k h x) ^ 2)]
  have hFconst : (fun p : ℝ × cgF2 => (cgMean L k h (cgIns k p)) ^ 2) =
      fun p : ℝ × cgF2 => (cgMean L k h (cgIns k (0, p.2))) ^ 2 := by
    funext p
    rw [cg_mean_ins_const (L := L) k h p.1 p.2]
  -- the LHS factors L times the mean-square over the parameter
  have hfac : (∫ p : ℝ × cgF2, (cgMean L k h (cgIns k p)) ^ 2
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      (∫ c : cgF2, (cgMean L k h (cgIns k (0, c))) ^ 2 ∂(cgPi 2 L)) * L := by
    rw [hFconst]
    have hfs := integral_fun_snd (μ := (volume : Measure ℝ).restrict (CI L)) (ν := cgPi 2 L)
      (f := fun c : cgF2 => (cgMean L k h (cgIns k (0, c))) ^ 2)
    rw [hfs]
    have hvol : ((volume : Measure ℝ).restrict (CI L)).real Set.univ = L := by
      rw [measureReal_def, Measure.restrict_apply_univ]
      rw [CI, Real.volume_Icc]
      rw [show L - 0 = L by ring]
      rw [ENNReal.toReal_ofReal hL.le]
    rw [hvol]
    simp [mul_comm, smul_eq_mul]
  -- per-c Jensen (ν form) and monotonicity over the parameter
  have hJc : ∀ c : cgF2,
      (cgMean L k h (cgIns k (0, c))) ^ 2 ≤
        (1 / L) * (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
          ∂((volume : Measure ℝ).restrict (CI L))) := by
    intro c
    have hJ := cg_jensen_point hL (k := k) hh (cgIns k (0, c))
    -- hJ : (cgMean (ins(0,c)))² ≤ cgMean L k (h²) (ins(0,c))
    have hJrhs : cgMean L k (fun y : cgF3 => (h y) ^ 2) (cgIns k (0, c)) =
        (1 / L) * (∫ s in (0 : ℝ)..L, (h (cgIns k (s, c))) ^ 2) := by
      rw [cg_mean_at_ins]
    rw [hJrhs] at hJ
    rw [show (1 / L) * (∫ s in (0 : ℝ)..L, (h (cgIns k (s, c))) ^ 2) =
        (1 / L) * (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
          ∂((volume : Measure ℝ).restrict (CI L))) by
      congr 1
      rw [cg_interval_eq_restrict hL.le (fun s : ℝ => (h (cgIns k (s, c))) ^ 2)]] at hJ
    exact hJ
  have hJc' : ∀ c : cgF2,
      L * (cgMean L k h (cgIns k (0, c))) ^ 2 ≤
        (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
          ∂((volume : Measure ℝ).restrict (CI L))) := by
    intro c
    have h1 := hJc c
    -- multiply by L
    have hL0 : 0 ≤ L := hL.le
    calc
      L * (cgMean L k h (cgIns k (0, c))) ^ 2
          ≤ L * ((1 / L) * (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
              ∂((volume : Measure ℝ).restrict (CI L)))) :=
            mul_le_mul_of_nonneg_left h1 hL0
      _ = (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
              ∂((volume : Measure ℝ).restrict (CI L))) := by
            field_simp [ne_of_gt hL]
  -- integrability of the bound function over the parameter
  have hCont2 : Continuous (fun p : ℝ × cgF2 => (h (cgIns k p)) ^ 2) :=
    (hh.comp (cg_ins_cont k)).pow 2
  have hBint : Integrable (fun p : ℝ × cgF2 => (h (cgIns k p)) ^ 2)
      (((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L)) :=
    cg_integrable_prod_cont hCont2
  have hJν_int : Integrable (fun c : cgF2 => ∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
      ∂((volume : Measure ℝ).restrict (CI L))) (cgPi 2 L) := by
    have hnorm := Integrable.integral_norm_prod_right (μ := (volume : Measure ℝ).restrict (CI L))
      (ν := cgPi 2 L) (f := fun p : ℝ × cgF2 => (h (cgIns k p)) ^ 2) hBint
    convert hnorm using 1
    funext c
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.norm_eq_abs]
    simp
  have hmono : (∫ c : cgF2, L * (cgMean L k h (cgIns k (0, c))) ^ 2 ∂(cgPi 2 L)) ≤
      (∫ c : cgF2, (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
        ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L)) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact ae_of_all _ (fun c => mul_nonneg hL.le (sq_nonneg _))
    · exact hJν_int
    · exact ae_of_all _ hJc'
  -- fubini + peel back
  have hfub : (∫ c : cgF2, (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
        ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L)) =
      (∫ p : ℝ × cgF2, (h (cgIns k p)) ^ 2
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) := by
    exact (integral_prod_symm (μ := (volume : Measure ℝ).restrict (CI L)) (ν := cgPi 2 L)
      (fun p : ℝ × cgF2 => (h (cgIns k p)) ^ 2) hBint).symm
  have hback : (∫ p : ℝ × cgF2, (h (cgIns k p)) ^ 2
        ∂(((volume : Measure ℝ).restrict (CI L)).prod (cgPi 2 L))) =
      (∫ x : cgF3, (h x) ^ 2 ∂(cgPi 3 L)) := by
    rw [cg_integral_peel (k := k) (g := fun x : cgF3 => (h x) ^ 2)]
  calc
    (∫ x : cgF3, (cgMean L k h x) ^ 2 ∂(cgPi 3 L))
        = (∫ c : cgF2, (cgMean L k h (cgIns k (0, c))) ^ 2 ∂(cgPi 2 L)) * L := by
          rw [hpeel, hfac]
    _ = (∫ c : cgF2, L * (cgMean L k h (cgIns k (0, c))) ^ 2 ∂(cgPi 2 L)) := by
          rw [integral_const_mul L (fun c : cgF2 => (cgMean L k h (cgIns k (0, c))) ^ 2)]
          ring
    _ ≤ (∫ x : cgF3, (h x) ^ 2 ∂(cgPi 3 L)) := by
          calc
            (∫ c : cgF2, L * (cgMean L k h (cgIns k (0, c))) ^ 2 ∂(cgPi 2 L))
                ≤ (∫ c : cgF2, (∫ s : ℝ, (h (cgIns k (s, c))) ^ 2
                    ∂((volume : Measure ℝ).restrict (CI L))) ∂(cgPi 2 L)) := hmono
            _ = (∫ x : cgF3, (h x) ^ 2 ∂(cgPi 3 L)) := by
                  rw [hfub, hback]

/-! ## Algebra of the fibre means: linearity, constants, telescoping -/

/-- updates in different coordinates commute -/
lemma cg_update_comm {j k : Fin 3} (hjk : j ≠ k) (x : cgF3) (t s : ℝ) :
    Function.update (Function.update x j t) k s = Function.update (Function.update x k s) j t := by
  exact (Function.update_comm (α := Fin 3) (β := fun _ : Fin 3 => ℝ) hjk t s x)

/-- `x ↦ Function.update x k s` is continuous -/
lemma cg_update_fixed_cont {k : Fin 3} (s : ℝ) : Continuous (fun x : cgF3 => Function.update x k s) := by
  apply continuous_pi
  intro j
  by_cases hj : j = k
  · subst j
    have hfun : (fun x : cgF3 => Function.update x k s k) = fun _ : cgF3 => s := by
      funext x
      simp [Function.update]
    rw [hfun]
    exact continuous_const
  · have hfun : (fun x : cgF3 => Function.update x k s j) = fun x : cgF3 => x j := by
      funext x
      simp [Function.update, hj]
    rw [hfun]
    exact continuous_apply j

/-- the mean over a fibre is continuous everywhere (for continuous `f`, `0 ≤ L`) -/
lemma cg_mean_continuous {L : ℝ} (hL0 : 0 ≤ L) {k : Fin 3} {f : cgF3 → ℝ} (hf : Continuous f) :
    Continuous (cgMean L k f) := by
  rw [continuous_iff_continuousAt]
  intro x0
  -- localise to a large closed ball (a neighbourhood of x0)
  let R : ℝ := ‖x0‖ + 1
  let K : Set cgF3 := Metric.closedBall 0 R
  have hK : K ∈ 𝓝 x0 := by
    rw [Metric.mem_nhds_iff]
    refine ⟨1, by norm_num, ?_⟩
    intro y hy
    dsimp [K, R]
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    rw [sub_zero]
    have hy' : ‖y - x0‖ < 1 := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hy)
    calc
      ‖y‖ = ‖(y - x0) + x0‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x0‖ + ‖x0‖ := norm_add_le _ _
      _ ≤ ‖x0‖ + 1 := by linarith
  have hx0K : x0 ∈ K := by
    dsimp [K, R]
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    rw [sub_zero]
    linarith
  -- bound of f on the compact set covered by the segments
  let S : Set (ℝ × cgF3) := (Set.Icc (0 : ℝ) L) ×ˢ K
  have hScomp : IsCompact S := IsCompact.prod isCompact_Icc (ProperSpace.isCompact_closedBall 0 R)
  have hupd : Continuous (fun p : ℝ × cgF3 => Function.update p.2 k p.1) := by
    apply continuous_pi
    intro j
    by_cases hj : j = k
    · subst j
      have hfun : (fun p : ℝ × cgF3 => Function.update p.2 k p.1 k) = fun p : ℝ × cgF3 => p.1 := by
        funext p
        simp [Function.update]
      rw [hfun]
      exact continuous_fst
    · have hfun : (fun p : ℝ × cgF3 => Function.update p.2 k p.1 j) = fun p : ℝ × cgF3 => p.2 j := by
        funext p
        simp [Function.update, hj]
      rw [hfun]
      exact (continuous_apply j).comp continuous_snd
  have hcontS : ContinuousOn (fun p : ℝ × cgF3 => f (Function.update p.2 k p.1)) S :=
    (hf.comp hupd).continuousOn
  obtain ⟨C, hC⟩ := hScomp.exists_bound_of_continuousOn hcontS
  -- continuity on K via dominated convergence over the fibre
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) L)
  have hbnd : ∀ x ∈ K, ∀ᵐ s ∂μ, |f (Function.update x k s)| ≤ C := by
    intro x hx
    rw [ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) L))]
    apply ae_of_all
    intro s hs
    exact hC (s, x) ⟨⟨le_of_lt hs.1, hs.2⟩, hx⟩
  have hbndint : Integrable (fun _ : ℝ => C) μ := by
    have hfin : μ Set.univ < (⊤ : ℝ≥0∞) := by
      dsimp [μ]
      rw [Measure.restrict_apply_univ]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have hfinM : IsFiniteMeasure μ := ⟨hfin⟩
    letI : IsFiniteMeasure μ := hfinM
    exact (integrable_const_iff).2 (Or.inr hfinM)
  have hmeas : ∀ x ∈ K, AEStronglyMeasurable (fun s : ℝ => f (Function.update x k s)) μ := by
    intro x hx
    exact (cg_fibre_cont (k := k) hf x).aestronglyMeasurable
  have hcont2 : ∀ᵐ s ∂μ, ContinuousOn (fun x : cgF3 => f (Function.update x k s)) K := by
    apply ae_of_all
    intro s
    exact (hf.comp (cg_update_fixed_cont (k := k) s)).continuousOn
  have hcontI : ContinuousOn (fun x : cgF3 => (∫ s : ℝ, f (Function.update x k s) ∂μ)) K :=
    continuousOn_of_dominated (μ := μ) (s := K) (F := fun (x : cgF3) (s : ℝ) =>
      f (Function.update x k s)) (bound := fun _ : ℝ => C) hmeas hbnd hbndint hcont2
  -- cgMean is (1/L) times this integral
  have hmain : ContinuousOn (cgMean L k f) K := by
    convert hcontI.const_mul (1 / L) using 1
    funext x
    dsimp [cgMean]
    rw [intervalIntegral.integral_of_le hL0]
  -- continuity at x0
  exact ContinuousOn.continuousAt hmain hK

/-- the mean is linear over subtraction -/
lemma cgMean_sub {L : ℝ} {k : Fin 3} {f g : cgF3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    cgMean L k (fun y : cgF3 => f y - g y) = fun x : cgF3 => cgMean L k f x - cgMean L k g x := by
  funext x
  dsimp [cgMean]
  have hfi : IntervalIntegrable (fun s : ℝ => f (Function.update x k s)) volume 0 L :=
    cg_fibre_intervalInt hf x
  have hgi : IntervalIntegrable (fun s : ℝ => g (Function.update x k s)) volume 0 L :=
    cg_fibre_intervalInt hg x
  rw [intervalIntegral.integral_sub (μ := volume) (f := fun s : ℝ => f (Function.update x k s))
    (g := fun s : ℝ => g (Function.update x k s)) hfi hgi]
  ring

/-- the mean is constant in its own coordinate -/
lemma cgMean_constInCoord {L : ℝ} {k : Fin 3} (f : cgF3 → ℝ) (x : cgF3) (t : ℝ) :
    cgMean L k f (Function.update x k t) = cgMean L k f x := by
  dsimp [cgMean]
  congr 1
  rw [show (fun s : ℝ => f (Function.update (Function.update x k t) k s)) =
      fun s : ℝ => f (Function.update x k s) by
    funext s
    congr 1
    rw [Function.update_idem]]

/-- the mean preserves constancy in other coordinates -/
lemma cgMean_preserves_const {L : ℝ} {k j : Fin 3} (hkj : j ≠ k)
    {g : cgF3 → ℝ} (hg : ∀ x t, g (Function.update x j t) = g x) :
    ∀ x t, cgMean L k g (Function.update x j t) = cgMean L k g x := by
  intro x t
  dsimp [cgMean]
  congr 1
  rw [show (fun s : ℝ => g (Function.update (Function.update x j t) k s)) =
      fun s : ℝ => g (Function.update x k s) by
    funext s
    rw [cg_update_comm hkj]
    rw [hg]]

/-- composition of the three means is constant -/
lemma cg_cst_const {L : ℝ} (Φ : cgF3 → ℝ) (x y : cgF3) :
    cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) x = cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) y := by
  let cst : cgF3 → ℝ := cgMean L 2 (cgMean L 1 (cgMean L 0 Φ))
  let x1 := Function.update x 0 (y 0)
  let x2 := Function.update x1 1 (y 1)
  have hy : y = Function.update x2 2 (y 2) := by
    ext j
    by_cases hj : j = 2
    · subst j
      simp [x2, x1, Function.update]
    · by_cases hj0 : j = 0
      · subst j
        simp [x2, x1, Function.update]
      · by_cases hj1 : j = 1
        · subst j
          simp [x2, x1, Function.update]
        · exfalso
          fin_cases j <;> simp at hj0 hj1 hj
  have hconst0 : ∀ z t, cgMean L 1 (cgMean L 0 Φ) (Function.update z 0 t) =
      cgMean L 1 (cgMean L 0 Φ) z := by
    intro z t
    apply cgMean_preserves_const (L := L) (k := 1) (j := 0) (by decide : (0 : Fin 3) ≠ 1)
    intro w s
    exact cgMean_constInCoord (k := 0) Φ w s
  have h0 : cst x = cst x1 := by
    dsimp [cst, x1]
    exact (cgMean_preserves_const (L := L) (k := 2) (j := 0) (by decide : (0 : Fin 3) ≠ 2)
      hconst0 x (y 0)).symm
  have h1 : cst x1 = cst x2 := by
    dsimp [cst, x2]
    exact (cgMean_preserves_const (L := L) (k := 2) (j := 1) (by decide : (1 : Fin 3) ≠ 2)
      (fun z t => cgMean_constInCoord (k := 1) (cgMean L 0 Φ) z t) x1 (y 1)).symm
  have h2 : cst x2 = cst y := by
    rw [hy]
    dsimp [cst]
    exact (cgMean_constInCoord (k := 2) (cgMean L 1 (cgMean L 0 Φ)) x2 (y 2)).symm
  calc
    cst x = cst x1 := h0
    _ = cst x2 := h1
    _ = cst y := h2

/-- the telescoping identity (function form) -/
lemma cg_decomp {L : ℝ} (hL0 : 0 ≤ L) {Φ : cgF3 → ℝ} (hΦc : ContDiff ℝ ∞ Φ) :
    (fun x : cgF3 => Φ x - (cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) x)) =
      (fun x : cgF3 => (Φ x - cgMean L 2 Φ x) +
        (cgMean L 2 (fun y : cgF3 => Φ y - cgMean L 1 Φ y) x) +
        (cgMean L 2 (cgMean L 1 (fun y : cgF3 => Φ y - cgMean L 0 Φ y)) x)) := by
  funext x
  -- continuity of the auxiliary functions (all fibre means of smooth functions)
  have hM0c : Continuous (cgMean L 0 Φ) := cg_mean_continuous (L := L) hL0 (k := 0) hΦc.continuous
  have hM1c : Continuous (cgMean L 1 Φ) := cg_mean_continuous (L := L) hL0 (k := 1) hΦc.continuous
  have hM1M0c : Continuous (cgMean L 1 (cgMean L 0 Φ)) :=
    cg_mean_continuous (L := L) hL0 (k := 1) hM0c
  have hB : cgMean L 2 (fun y : cgF3 => Φ y - cgMean L 1 Φ y) x =
      cgMean L 2 Φ x - cgMean L 2 (cgMean L 1 Φ) x := by
    have hlin := cgMean_sub (L := L) (k := 2) hΦc.continuous hM1c
    exact congrFun hlin x
  have hC1 : cgMean L 1 (fun y : cgF3 => Φ y - cgMean L 0 Φ y) =
      fun y : cgF3 => cgMean L 1 Φ y - cgMean L 1 (cgMean L 0 Φ) y := by
    exact cgMean_sub (L := L) (k := 1) hΦc.continuous hM0c
  have hC : cgMean L 2 (cgMean L 1 (fun y : cgF3 => Φ y - cgMean L 0 Φ y)) x =
      cgMean L 2 (cgMean L 1 Φ) x - cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) x := by
    have hlin2 := cgMean_sub (L := L) (k := 2) hM1c hM1M0c
    have h := congrFun hlin2 x
    -- h : cgMean L 2 (M₁Φ − M₁M₀Φ) x = M₂(M₁Φ) x − M₂(M₁M₀Φ) x
    rw [← hC1] at h
    exact h
  rw [hB, hC]
  ring

/-! ## Assembly of the cube gap on the function cube -/

/-- elementary (a+b+c)² ≤ 3(a²+b²+c²) -/
lemma cg_three_sq (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- total volume of the function cube -/
lemma cg_pi3_vol {L : ℝ} (hL0 : 0 ≤ L) : (cgPi 3 L Set.univ).toReal = L ^ 3 := by
  dsimp [cgPi]
  rw [Measure.restrict_apply_univ]
  rw [volume_cubeF 3 L hL0]
  rw [ENNReal.toReal_ofReal (pow_nonneg hL0 3)]

instance cg_pi_isFinite (d : ℕ) (L : ℝ) : IsFiniteMeasure (cgPi d L) := ⟨ by
  dsimp [cgPi]
  rw [Measure.restrict_apply_univ]
  exact IsCompact.measure_lt_top (cg_cubeF_compact d L)⟩

/-- `(f x − a)²` is integrable if `f` and `f²` are -/
lemma cg_integrable_sq_shift {μ : Measure cgF3} [IsFiniteMeasure μ] {Φ : cgF3 → ℝ}
    (hΦ2i : Integrable (fun x => (Φ x) ^ 2) μ) (hΦi : Integrable Φ μ) (a : ℝ) :
    Integrable (fun x => (Φ x - a) ^ 2) μ := by
  have hlin : (fun x : cgF3 => (Φ x - a) ^ 2) =
      fun x => (Φ x) ^ 2 - 2 * a * Φ x + a ^ 2 := by
    funext x
    ring
  rw [hlin]
  exact Integrable.add (Integrable.sub hΦ2i (hΦi.const_mul (2 * a)))
    ((integrable_const_iff).2 (Or.inr inferInstance))

/-- the mean over the cube minimizes the squared distance to constants -/
lemma cg_variance_bound {L : ℝ} (hL : 0 < L) {Φ : cgF3 → ℝ}
    (hΦi : Integrable Φ (cgPi 3 L)) (hΦ2i : Integrable (fun x => (Φ x) ^ 2) (cgPi 3 L)) :
    ∀ c : ℝ, (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L)) ≤
      (∫ x : cgF3, (Φ x - c) ^ 2 ∂(cgPi 3 L)) := by
  intro c
  let m : ℝ := (1 / L ^ 3) * (∫ x : cgF3, Φ x ∂(cgPi 3 L))
  have hmdef : m = (1 / L ^ 3) * (∫ x : cgF3, Φ x ∂(cgPi 3 L)) := rfl
  let vol : ℝ := (cgPi 3 L Set.univ).toReal
  have hvol : vol = L ^ 3 := by
    dsimp [vol]
    exact cg_pi3_vol hL.le
  have hconst_eq : ∀ a : ℝ, (∫ x : cgF3, (fun _ : cgF3 => a) x ∂(cgPi 3 L)) = a * vol := by
    intro a
    rw [integral_const]
    rw [measureReal_def]
    dsimp [vol]
    ring
  have hconst_int : Integrable (fun _ : cgF3 => m) (cgPi 3 L) :=
    (integrable_const_iff).2 (Or.inr inferInstance)
  have hmzero : (∫ x : cgF3, (Φ x - m) ∂(cgPi 3 L)) = 0 := by
    have hsub := integral_sub hΦi hconst_int
    rw [hsub, hconst_eq m]
    dsimp [m]
    rw [hvol]
    have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hL)
    field_simp [hL3]
    ring
  have hm2i : Integrable (fun x => (Φ x - m) ^ 2) (cgPi 3 L) :=
    cg_integrable_sq_shift hΦ2i hΦi m
  -- the three terms
  let FA : cgF3 → ℝ := fun x => (Φ x - m) ^ 2
  let FB : cgF3 → ℝ := fun x => (2 * (m - c)) * (Φ x - m)
  let FC : cgF3 → ℝ := fun _ => (m - c) ^ 2
  have hFB : Integrable FB (cgPi 3 L) := (hΦi.sub hconst_int).const_mul (2 * (m - c))
  have hFC : Integrable FC (cgPi 3 L) := (integrable_const_iff).2 (Or.inr inferInstance)
  have hFB0 : (∫ x : cgF3, FB x ∂(cgPi 3 L)) = 0 := by
    dsimp [FB]
    rw [integral_const_mul (2 * (m - c)) (fun x : cgF3 => Φ x - m)]
    rw [hmzero]
    ring
  have hFCv : (∫ x : cgF3, FC x ∂(cgPi 3 L)) = (m - c) ^ 2 * vol := by
    dsimp [FC]
    exact hconst_eq ((m - c) ^ 2)
  have hsq : ∀ x : cgF3, (Φ x - c) ^ 2 = FA x + FB x + FC x := by
    intro x
    dsimp [FA, FB, FC]
    ring
  have hsplit : (∫ x : cgF3, FA x + FB x + FC x ∂(cgPi 3 L)) =
      (∫ x : cgF3, FA x ∂(cgPi 3 L)) + (∫ x : cgF3, FB x ∂(cgPi 3 L)) +
        (∫ x : cgF3, FC x ∂(cgPi 3 L)) := by
    calc
      (∫ x : cgF3, FA x + FB x + FC x ∂(cgPi 3 L)) = (∫ x : cgF3, (FA + FB) x + FC x ∂(cgPi 3 L)) := by
            rw [show (fun x : cgF3 => FA x + FB x + FC x) =
                fun x : cgF3 => (FA + FB) x + FC x by funext x; rfl]
      _ = (∫ x : cgF3, (FA + FB) x ∂(cgPi 3 L)) + (∫ x : cgF3, FC x ∂(cgPi 3 L)) := by
            rw [integral_add (hm2i.add hFB) hFC]
      _ = ((∫ x : cgF3, FA x ∂(cgPi 3 L)) + (∫ x : cgF3, FB x ∂(cgPi 3 L))) +
          (∫ x : cgF3, FC x ∂(cgPi 3 L)) := by
            rw [show (fun x : cgF3 => (FA + FB) x) = fun x : cgF3 => FA x + FB x by funext x; rfl]
            rw [integral_add hm2i hFB]
  have hmain : (∫ x : cgF3, (Φ x - c) ^ 2 ∂(cgPi 3 L)) =
      (∫ x : cgF3, (Φ x - m) ^ 2 ∂(cgPi 3 L)) + (m - c) ^ 2 * vol := by
    calc
      (∫ x : cgF3, (Φ x - c) ^ 2 ∂(cgPi 3 L))
          = ∫ x : cgF3, FA x + FB x + FC x ∂(cgPi 3 L) := by
            apply integral_congr_ae
            filter_upwards with x
            exact hsq x
      _ = (∫ x : cgF3, FA x ∂(cgPi 3 L)) + (∫ x : cgF3, FB x ∂(cgPi 3 L)) +
          (∫ x : cgF3, FC x ∂(cgPi 3 L)) := hsplit
      _ = (∫ x : cgF3, FA x ∂(cgPi 3 L)) + (m - c) ^ 2 * vol := by
            rw [hFB0, hFCv]
            ring
  change (∫ x : cgF3, (Φ x - m) ^ 2 ∂(cgPi 3 L)) ≤ (∫ x : cgF3, (Φ x - c) ^ 2 ∂(cgPi 3 L))
  calc
    (∫ x : cgF3, (Φ x - m) ^ 2 ∂(cgPi 3 L))
        ≤ (∫ x : cgF3, (Φ x - m) ^ 2 ∂(cgPi 3 L)) + (m - c) ^ 2 * vol := by
          exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by
            rw [hvol]
            exact pow_nonneg hL.le 3))
    _ = (∫ x : cgF3, (Φ x - c) ^ 2 ∂(cgPi 3 L)) := hmain.symm
/-! ## The three-coordinate gap -/

/-- additivity of the integral for a sum of three functions -/
lemma cg_integral_add3 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g h : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, f x + g x + h x ∂μ) = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) + (∫ x, h x ∂μ) := by
  calc
    (∫ x, f x + g x + h x ∂μ) = (∫ x, (f + g) x + h x ∂μ) := by
          rw [show (fun x : α => f x + g x + h x) = fun x : α => (f + g) x + h x by funext x; rfl]
    _ = (∫ x, (f + g) x ∂μ) + (∫ x, h x ∂μ) := by
          rw [integral_add (hf.add hg) hh]
    _ = ((∫ x, f x ∂μ) + (∫ x, g x ∂μ)) + (∫ x, h x ∂μ) := by
          rw [show (fun x : α => (f + g) x) = fun x : α => f x + g x by funext x; rfl]
          rw [integral_add hf hg]

/-- continuity of the auxiliary mean expressions used in the telescoping -/
lemma cg_gap3_cont {L : ℝ} (hL0 : 0 ≤ L) {Φ : cgF3 → ℝ} (hΦc : ContDiff ℝ ∞ Φ) (j : Fin 3) :
    Continuous (cgMean L j Φ) := cg_mean_continuous (L := L) hL0 (k := j) hΦc.continuous

/-- the full three-axis gap for a smooth function on the function cube -/
lemma cg_gap3 {L : ℝ} (hL : 0 < L) {Φ : cgF3 → ℝ} (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L)) ≤
      (36 : ℝ) * L ^ 2 *
        (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂(cgPi 3 L)) := by
  let μ : Measure cgF3 := cgPi 3 L
  let mF : ℝ := (1 / L ^ 3) * (∫ x : cgF3, Φ x ∂μ)
  let c0 : ℝ := cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) (0 : cgF3)
  let A : cgF3 → ℝ := fun x => Φ x - cgMean L 2 Φ x
  let B : cgF3 → ℝ := fun x => cgMean L 2 (fun y => Φ y - cgMean L 1 Φ y) x
  let C : cgF3 → ℝ := fun x => cgMean L 2 (cgMean L 1 (fun y => Φ y - cgMean L 0 Φ y)) x
  let sl : Fin 3 → cgF3 → ℝ := fun k x => (cgSlice k Φ x) ^ 2
  have hΦcont : Continuous Φ := hΦc.continuous
  have hM0c : Continuous (cgMean L 0 Φ) := cg_mean_continuous hL.le (k := 0) hΦcont
  have hM1c : Continuous (cgMean L 1 Φ) := cg_mean_continuous hL.le (k := 1) hΦcont
  have hM2c : Continuous (cgMean L 2 Φ) := cg_mean_continuous hL.le (k := 2) hΦcont
  have hAc : Continuous A := by
    dsimp [A]
    exact hΦcont.sub hM2c
  have hBc : Continuous B := by
    dsimp [B]
    exact cg_mean_continuous hL.le (k := 2) (hΦcont.sub hM1c)
  have hCc : Continuous C := by
    dsimp [C]
    exact cg_mean_continuous hL.le (k := 2) (cg_mean_continuous hL.le (k := 1) (hΦcont.sub hM0c))
  have hAmc : Continuous (fun x => Φ x - cgMean L 1 Φ x) := hΦcont.sub hM1c
  have hCmc : Continuous (fun x => Φ x - cgMean L 0 Φ x) := hΦcont.sub hM0c
  have hM1Cmc : Continuous (cgMean L 1 (fun x => Φ x - cgMean L 0 Φ x)) :=
    cg_mean_continuous hL.le (k := 1) hCmc
  have hΦi : Integrable Φ μ := by
    dsimp [μ]
    exact cg_integrable_pi_of_contOn hΦcont.continuousOn
  have hΦ2i : Integrable (fun x => (Φ x) ^ 2) μ := by
    dsimp [μ]
    exact cg_integrable_pi_of_contOn (hΦcont.pow 2).continuousOn
  have hA2i : Integrable (fun x => A x ^ 2) μ := by
    dsimp [μ]
    exact cg_integrable_pi_of_contOn (hAc.pow 2).continuousOn
  have hB2i : Integrable (fun x => B x ^ 2) μ := by
    dsimp [μ]
    exact cg_integrable_pi_of_contOn (hBc.pow 2).continuousOn
  have hC2i : Integrable (fun x => C x ^ 2) μ := by
    dsimp [μ]
    exact cg_integrable_pi_of_contOn (hCc.pow 2).continuousOn
  have h3i : Integrable (fun x => 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2)) μ := by
    refine (hA2i.add hB2i).add hC2i |>.const_mul 3
  have hsl_i (k : Fin 3) : Integrable (sl k) μ := by
    dsimp [μ, sl]
    exact cg_integrable_pi_of_contOn ((cg_slice_contDiff hΦc k).continuous.pow 2).continuousOn
  -- decomposition and constancy of the triple mean
  have hcst : ∀ x : cgF3, cgMean L 2 (cgMean L 1 (cgMean L 0 Φ)) x = c0 := by
    intro x
    exact cg_cst_const Φ x 0
  have hdec := cg_decomp (L := L) hL.le hΦc
  have hdec0 : ∀ x : cgF3, Φ x - c0 = A x + B x + C x := by
    intro x
    have hx := congrFun hdec x
    -- hx : Φ x − M₂M₁M₀Φ x = (Φ x − M₂Φ x) + M₂(Φ−M₁Φ) x + M₂M₁(Φ−M₀Φ) x
    rw [hcst x] at hx
    simpa [A, B, C] using hx
  have hpt : ∀ x : cgF3, (Φ x - c0) ^ 2 ≤ 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) := by
    intro x
    calc
      (Φ x - c0) ^ 2 = (A x + B x + C x) ^ 2 := by rw [hdec0 x]
      _ ≤ 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) := cg_three_sq (A x) (B x) (C x)
  have hint0 : (∫ x : cgF3, (Φ x - c0) ^ 2 ∂μ) ≤
      (∫ x : cgF3, 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) ∂μ) := by
    refine integral_mono_of_nonneg ?_ h3i ?_
    · exact ae_of_all _ (fun x => sq_nonneg _)
    · exact ae_of_all _ hpt
  have hsplit : (∫ x : cgF3, 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) ∂μ) =
      3 * ((∫ x : cgF3, A x ^ 2 ∂μ) + (∫ x : cgF3, B x ^ 2 ∂μ) + (∫ x : cgF3, C x ^ 2 ∂μ)) := by
    calc
      (∫ x : cgF3, 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) ∂μ)
          = 3 * (∫ x : cgF3, A x ^ 2 + B x ^ 2 + C x ^ 2 ∂μ) := by
            rw [integral_const_mul 3 (fun x => A x ^ 2 + B x ^ 2 + C x ^ 2)]
      _ = 3 * ((∫ x : cgF3, A x ^ 2 ∂μ) + (∫ x : cgF3, B x ^ 2 ∂μ) + (∫ x : cgF3, C x ^ 2 ∂μ)) := by
            rw [cg_integral_add3 μ (fun x => A x ^ 2) (fun x => B x ^ 2) (fun x => C x ^ 2) hA2i hB2i hC2i]
  -- individual bounds
  have hFP2 : (∫ x : cgF3, (Φ x - cgMean L 2 Φ x) ^ 2 ∂μ) ≤
      L ^ 2 * (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ) := cg_fp (L := L) hL 2 hΦc
  have hFP1 : (∫ x : cgF3, (Φ x - cgMean L 1 Φ x) ^ 2 ∂μ) ≤
      L ^ 2 * (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) := cg_fp (L := L) hL 1 hΦc
  have hFP0 : (∫ x : cgF3, (Φ x - cgMean L 0 Φ x) ^ 2 ∂μ) ≤
      L ^ 2 * (∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) := cg_fp (L := L) hL 0 hΦc
  have hBnd : (∫ x : cgF3, B x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) := by
    have h1 := cg_contraction (L := L) hL 2 hAmc
    exact le_trans h1 hFP1
  have hCnd : (∫ x : cgF3, C x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) := by
    have h1 := cg_contraction (L := L) hL 2 hM1Cmc
    have h2 := cg_contraction (L := L) hL 1 hCmc
    exact le_trans (le_trans h1 h2) hFP0
  have hAn : (∫ x : cgF3, A x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ) := by
    simpa [A] using hFP2
  -- combine: 3·(Σ ∫ pieces) ≤ 3·L²·(Σ_k ∫ slice²)
  have hpieces : (∫ x : cgF3, A x ^ 2 ∂μ) + (∫ x : cgF3, B x ^ 2 ∂μ) + (∫ x : cgF3, C x ^ 2 ∂μ) ≤
      L ^ 2 * ((∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) + (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) +
        (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ)) := by
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    -- sum of the three bounds
    have hsumA : (∫ x : cgF3, A x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ) := hAn
    have hsumB : (∫ x : cgF3, B x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) := hBnd
    have hsumC : (∫ x : cgF3, C x ^ 2 ∂μ) ≤ L ^ 2 * (∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) := hCnd
    nlinarith
  -- identify the sum of the three integrals with the integral of the sum over Fin 3
  have hsum0 : (∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) + (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) +
        (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ) =
      (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := by
    have hJ : (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) =
        ∑ k : Fin 3, (∫ x : cgF3, (cgSlice k Φ x) ^ 2 ∂μ) := by
      have hfs := integral_finset_sum (Finset.univ : Finset (Fin 3))
        (f := fun k x => (cgSlice k Φ x) ^ 2) (by intro k hk; exact hsl_i k)
      simpa using hfs
    rw [hJ]
    rw [Fin.sum_univ_three]
  -- variance bound
  have hvar : (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L)) ≤
      (∫ x : cgF3, (Φ x - c0) ^ 2 ∂(cgPi 3 L)) := by
    exact cg_variance_bound hL hΦi hΦ2i c0
  have hmain0 : (∫ x : cgF3, (Φ x - c0) ^ 2 ∂μ) ≤
      (36 : ℝ) * L ^ 2 * (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := by
    have hJ0 : 0 ≤ (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := by
      refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun k hk => sq_nonneg _)
    calc
      (∫ x : cgF3, (Φ x - c0) ^ 2 ∂μ)
          ≤ (∫ x : cgF3, 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) ∂μ) := hint0
      _ = 3 * ((∫ x : cgF3, A x ^ 2 ∂μ) + (∫ x : cgF3, B x ^ 2 ∂μ) + (∫ x : cgF3, C x ^ 2 ∂μ)) := hsplit
      _ ≤ 3 * (L ^ 2 * ((∫ x : cgF3, (cgSlice 0 Φ x) ^ 2 ∂μ) + (∫ x : cgF3, (cgSlice 1 Φ x) ^ 2 ∂μ) +
            (∫ x : cgF3, (cgSlice 2 Φ x) ^ 2 ∂μ))) := by
            exact mul_le_mul_of_nonneg_left hpieces (by norm_num : (0 : ℝ) ≤ 3)
      _ = (3 * L ^ 2) * (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := by
            rw [hsum0]
            ring
      _ ≤ (36 : ℝ) * L ^ 2 * (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := by
            nlinarith [hJ0, sq_nonneg L]
  -- put everything together
  calc
    (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L))
        ≤ (∫ x : cgF3, (Φ x - c0) ^ 2 ∂(cgPi 3 L)) := hvar
    _ = (∫ x : cgF3, (Φ x - c0) ^ 2 ∂μ) := by rfl
    _ ≤ (36 : ℝ) * L ^ 2 * (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂μ) := hmain0
    _ = (36 : ℝ) * L ^ 2 * (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂(cgPi 3 L)) := by rfl
/-! ## Transport to the Euclidean cube -/

/-- the transport map `toLp` is smooth -/
lemma cg_euc_contDiff : ContDiff ℝ (∞ : ℕ∞ω) (fun x : cgF3 => cgEuc x) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  change ContDiff ℝ (∞ : ℕ∞ω) (fun x : cgF3 => WithLp.toLp (2 : ℝ≥0∞) x)
  simpa using (PiLp.contDiff_toLp (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ) (p := (2 : ℝ≥0∞)) (n := (∞ : ℕ∞ω)))

/-- the transport map is linear (addition) -/
lemma cg_euc_add (x v : cgF3) : cgEuc (x + v) = cgEuc x + cgEuc v := by
  ext i
  simp [cgEuc]

/-- the transport map is linear (scalar multiplication) -/
lemma cg_euc_smul (t : ℝ) (v : cgF3) : cgEuc (t • v) = t • cgEuc v := by
  ext i
  simp [cgEuc]

/-- the coordinate unit vector maps to the `k`-th Euclidean unit vector -/
lemma cg_euc_dir (k : Fin 3) : cgEuc (cgDir k) = EuclideanSpace.single k (1 : ℝ) := by
  ext j
  simp [cgEuc, cgDir]
  by_cases hj : j = k <;> simp [hj]

/-- pullback of a smooth function is smooth -/
lemma cg_pullback_contDiff {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun w : cgF3 => φ (cgEuc w)) :=
  hφc.comp cg_euc_contDiff

/-- the coordinate slice derivative of the pullback equals the directional derivative along
the `k`-th Euclidean unit vector -/
lemma cg_slice_fderiv_single {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ) (x : cgF3) (k : Fin 3) :
    cgSlice k (fun w : cgF3 => φ (cgEuc w)) x = fderiv ℝ φ (cgEuc x) (EuclideanSpace.single k (1 : ℝ)) := by
  -- path and its derivative
  let u : ℝ³ := EuclideanSpace.single k (1 : ℝ)
  have hu : cgEuc (cgDir k) = u := cg_euc_dir k
  have hpath : (fun s : ℝ => cgEuc (Function.update x k s)) =
      fun s : ℝ => cgEuc x + (s - x k) • u := by
    funext s
    rw [cg_update_add]
    rw [cg_euc_add]
    rw [cg_euc_smul]
    rw [hu]
  -- derivative of the path
  have hderiv : HasDerivAt (fun s : ℝ => cgEuc x + (s - x k) • u) u (x k) := by
    let base : ℝ³ := cgEuc x + (-(x k)) • u
    have h1 : HasDerivAt (fun s : ℝ => base + s • u) u (x k) := by
      have hcst : HasDerivAt (fun _ : ℝ => base) 0 (x k) := hasDerivAt_const _ _
      have hid2 : HasDerivAt (fun t : ℝ => t • u) u (x k) := by
        simpa using (hasDerivAt_id (x k)).smul_const u
      have htotal := hcst.add hid2
      rw [zero_add] at htotal
      exact htotal
    have hbase_eq : (fun s : ℝ => cgEuc x + (s - x k) • u) = fun s : ℝ => base + s • u := by
      funext s
      dsimp [base]
      simp [sub_eq_add_neg, add_smul, add_comm, add_left_comm, add_assoc]
    rwa [hbase_eq]
  -- the composed derivative
  have hpt : cgEuc x + (x k - x k) • u = cgEuc x := by simp
  have hfdiff : DifferentiableAt ℝ φ (cgEuc x + (x k - x k) • u) := by
    simpa using (hφc.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) (cgEuc x))
  have hmain := HasFDerivAt.comp_hasDerivAt (x k) hfdiff.hasFDerivAt hderiv
  have hcomp' : (fun s : ℝ => φ (cgEuc (Function.update x k s))) =
      fun s : ℝ => φ (cgEuc x + (s - x k) • u) := by
    funext s
    rw [show cgEuc (Function.update x k s) = cgEuc x + (s - x k) • u by
      change (fun t : ℝ => cgEuc (Function.update x k t)) s = (fun t : ℝ => cgEuc x + (t - x k) • u) s
      rw [hpath]]
  have hder : deriv (fun s : ℝ => φ (cgEuc (Function.update x k s))) (x k) =
      fderiv ℝ φ (cgEuc x) u := by
    rw [hcomp']
    change deriv (φ ∘ (fun s : ℝ => cgEuc x + (s - x k) • u)) (x k) = fderiv ℝ φ (cgEuc x) u
    simpa [hpt] using hmain.deriv
  dsimp [cgSlice]
  rw [hder]
/-- sums of squared directional derivatives are independent of the orthonormal basis -/
lemma cg_onb_sum_eq {φ : ℝ³ → ℝ} (y : ℝ³) :
    (∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) =
      (∑ k : Fin 3, (fderiv ℝ φ y (EuclideanSpace.basisFun (Fin 3) ℝ k)) ^ 2) := by
  have h1 := OrthonormalBasis.norm_dual euclBasis3 (fderiv ℝ φ y)
  have h2 := OrthonormalBasis.norm_dual (EuclideanSpace.basisFun (Fin 3) ℝ) (fderiv ℝ φ y)
  rw [← h1]
  exact h2

/-- **Neumann gap above constants in the cube** -/
theorem cube_gap (L : ℝ) (hL : 0 < L) {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ) :
    (∫ y in cube L, (φ y - (1 / L ^ 3) * (∫ z in cube L, φ z)) ^ 2) ≤
      (36 : ℝ) * L ^ 2 *
        (∫ y in cube L, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) := by
  let Φ : cgF3 → ℝ := fun x => φ (cgEuc x)
  have hΦc : ContDiff ℝ ∞ Φ := by
    dsimp [Φ]
    exact cg_pullback_contDiff hφc
  have hg := cg_gap3 (L := L) hL (Φ := Φ) hΦc
  have hmean : (∫ z in cube L, φ z) = (∫ x : cgF3, Φ x ∂(cgPi 3 L)) := by
    simpa [Φ] using (cg_integral_cube_eq_cubeF (L := L) (g := φ))
  have hLHS : (∫ y in cube L, (φ y - (1 / L ^ 3) * (∫ z in cube L, φ z)) ^ 2) =
      (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L)) := by
    rw [cg_integral_cube_eq_cubeF (L := L)
      (g := fun y : ℝ³ => (φ y - (1 / L ^ 3) * (∫ z in cube L, φ z)) ^ 2)]
    rw [hmean]
  have hR : (∫ y in cube L, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) =
      (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂(cgPi 3 L)) := by
    calc
      (∫ y in cube L, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2)
          = ∫ x : cgF3, (∑ k : Fin 3, (fderiv ℝ φ (cgEuc x) (euclBasis3 k)) ^ 2) ∂(cgPi 3 L) := by
            rw [cg_integral_cube_eq_cubeF (L := L)
              (g := fun y : ℝ³ => ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2)]
      _ = ∫ x : cgF3, (∑ k : Fin 3, (fderiv ℝ φ (cgEuc x) (EuclideanSpace.basisFun (Fin 3) ℝ k)) ^ 2)
            ∂(cgPi 3 L) := by
            apply integral_congr_ae
            filter_upwards with x
            exact cg_onb_sum_eq (φ := φ) (cgEuc x)
      _ = ∫ x : cgF3, (∑ k : Fin 3, (cgSlice k Φ x) ^ 2) ∂(cgPi 3 L) := by
            apply integral_congr_ae
            filter_upwards with x
            apply Finset.sum_congr rfl
            intro k hk
            rw [EuclideanSpace.basisFun_apply]
            change (fderiv ℝ φ (cgEuc x) (EuclideanSpace.single k (1 : ℝ))) ^ 2 =
              (cgSlice k Φ x) ^ 2
            rw [cg_slice_fderiv_single (φ := φ) hφc x k]
  calc
    (∫ y in cube L, (φ y - (1 / L ^ 3) * (∫ z in cube L, φ z)) ^ 2)
        = (∫ x : cgF3, (Φ x - (1 / L ^ 3) * (∫ z : cgF3, Φ z ∂(cgPi 3 L))) ^ 2 ∂(cgPi 3 L)) := hLHS
    _ ≤ (36 : ℝ) * L ^ 2 *
          (∫ x : cgF3, ∑ k : Fin 3, (cgSlice k Φ x) ^ 2 ∂(cgPi 3 L)) := hg
    _ = (36 : ℝ) * L ^ 2 *
          (∫ y in cube L, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) := by
          rw [hR]

end Submission.BoseGases
