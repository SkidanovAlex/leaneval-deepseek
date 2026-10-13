import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp2
import Submission.Work.FTS.PressureOn.offPlanes.IbpProd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.OffPlanes

open MeasureTheory FiniteTimeSingularity Set Filter Topology
open scoped Topology

/-- Evaluation at a fixed vector of `ℝ³`, as a continuous linear map on the dual `ℝ³ →L[ℝ] ℝ`. -/
noncomputable def evalCLM (v : R3) : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (E := R3)) v

-- Design probe `offPlanes_ibp_R3_probe` of `Submission/Work/FTS/PressureOn/_wc_probe.lean`.
-- Integration by parts for a function differentiable only off the two coordinate planes.
--
-- HINTS (all in this workspace):
-- * `Submission/Work/FTS/PressureOn/offPlanes/IbpProd.lean` (PROVED) has
--   `Work.FTS.PressureOn.offPlanes.ibp_off_plane_prod` : the `(E × ℝ)` Fubini lift of the 1D
--   integration by parts with the single exceptional hyperplane `{t = 0}`
--   (`offPlanes/Ibp1D.lean`, `ibp_except_zero`), which is exactly the fibre statement needed for
--   the planes `x 0 = 0` and `x 2 = 0`; its fibrewise hypotheses are: a.e. fibre continuity,
--   a.e. fibre differentiability (everywhere for `Ψ`, off `t = 0` for `G`), integrability of both
--   products and vanishing of `G * Ψ` at `±∞` (free here from `HasCompactSupport`).
-- * the decomposition `ℝ³ ≃ᵐ ℝ × ℝ²` and `MeasureTheory.volume_preserving_piFinSuccAbove`
--   (Mathlib) turn the 3D integral into an iterated one; the exceptional set meets a.e. fibre of
--   each coordinate line in at most one point (for `i = 1` the only bad lines are those with
--   `x 0 = 0` or `x 2 = 0`, a null set); `volume_hyperplane_eq_zero`
--   (`Submission/Work/CoreResiduals/DifferentiableOffPlanes/volume_inter_boxes_eq_zero.lean`)
--   gives the nullity of a coordinate plane.
-- * `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` is the one-dimensional FTC on an
--   interval with differentiability only on the *open* interval (so the halves of each line can be
--   handled separately); the two boundary terms at the exceptional point cancel by continuity.
theorem offPlanes_ibp {g ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (i : Fin 3)
    (hgcont : Continuous g) (hgcs : HasCompactSupport g)
    (hgdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt g (fderiv ℝ g x) x)
    (hgint : MeasureTheory.LocallyIntegrable (fderiv ℝ g))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, ψ x * fderiv ℝ g x (FiniteTimeSingularity.e i)
      = -∫ x, g x * fderiv ℝ ψ x (FiniteTimeSingularity.e i) := by
  -- The coordinate point `X (y, t)`: `i`-th coordinate `t`, remaining coordinates `y`.
  let X : (Fin 2 → ℝ) × ℝ → R3 := fun p => toLpCLE (i.insertNth p.2 p.1)
  -- The same map written as a composite with the coordinate swap, which is how its
  -- measure preservation is proved.
  let φ : (Fin 2 → ℝ) × ℝ → R3 :=
    fun p => toLpCLE ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm p.swap)
  have hMP : MeasurePreserving φ (volume.prod volume) volume := by
    have h1 : MeasurePreserving (Prod.swap : (Fin 2 → ℝ) × ℝ → ℝ × (Fin 2 → ℝ))
        (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
    have h2 : MeasurePreserving ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm)
        ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm
    exact toLpCLE_measurePreserving.comp (h2.comp h1)
  have hEmb : MeasurableEmbedding φ :=
    toLpCLE_measurableEmbedding.comp
      ((MeasurableEquiv.measurableEmbedding
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm).comp
        (show MeasurableEmbedding (fun p : (Fin 2 → ℝ) × ℝ => p.swap) from
          MeasurableEquiv.prodComm.measurableEmbedding))
  have hφX : ∀ p, φ p = X p := by
    intro p
    simp only [φ, X, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Prod.fst_swap, Prod.snd_swap]
  let G : (Fin 2 → ℝ) × ℝ → ℝ := fun p => g (X p)
  let Gp : (Fin 2 → ℝ) × ℝ → ℝ := fun p => fderiv ℝ g (X p) (e i)
  let Ψ : (Fin 2 → ℝ) × ℝ → ℝ := fun p => ψ (X p)
  let Ψp : (Fin 2 → ℝ) × ℝ → ℝ := fun p => fderiv ℝ ψ (X p) (e i)
  -- The `i`-insertion is affine in the inserted coordinate.
  have hdecomp : ∀ (y : Fin 2 → ℝ) (s : ℝ),
      i.insertNth s y = (i.insertNth (0:ℝ) y : Fin 3 → ℝ) + s • Pi.single i (1:ℝ) := by
    intro y s
    funext k
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; simp [Fin.insertNth_apply_same]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [Fin.insertNth_apply_succAbove]
  have hXeq : ∀ y : Fin 2 → ℝ, (fun s : ℝ => X (y,s)) = fun s : ℝ => X (y,0) + s • (e i) := by
    intro y
    funext s
    show toLpCLE (i.insertNth s y) = toLpCLE (i.insertNth (0:ℝ) y) + s • e i
    rw [hdecomp y s, map_add, map_smul]
    rfl
  have hcontX : ∀ y : Fin 2 → ℝ, Continuous (fun t : ℝ => X (y,t)) := by
    intro y
    rw [hXeq y]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have haff : ∀ (y : Fin 2 → ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => X (y,s)) (e i) t := by
    intro y t
    rw [hXeq y]
    have hh := (hasDerivAt_id (x := t)).smul_const (e i)
    simpa using (hh.const_add (X (y,0)))
  -- The good base points: neither of the two remaining coordinates vanishes.  Their
  -- complement is a union of two hyperplanes in `Fin 2 → ℝ`, hence null.
  have hyzon : ∀ᵐ y : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), y 0 ≠ 0 ∧ y 1 ≠ 0 := by
    have h0 : ∀ᵐ y : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), y 0 ≠ 0 :=
      Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 0
    have h1 : ∀ᵐ y : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), y 1 ≠ 0 :=
      Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 1 0
    filter_upwards [h0, h1] with y hy0 hy1
    exact ⟨hy0, hy1⟩
  have hGd : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)), ∀ t, t ≠ 0 →
      HasDerivAt (fun s => G (y,s)) (Gp (y,t)) t := by
    filter_upwards [hyzon] with y hy
    have hyall : ∀ j : Fin 2, y j ≠ 0 := by
      intro j
      fin_cases j
      · exact hy.1
      · exact hy.2
    intro t ht
    have hkey : ∀ k : Fin 3, (i.insertNth t y : Fin 3 → ℝ) k ≠ 0 := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa [Fin.insertNth_apply_same] using ht
      · obtain ⟨j, hjk⟩ := Fin.exists_succAbove_eq hk
        rw [← hjk, Fin.insertNth_apply_succAbove]
        exact hyall j
    have h0 : X (y,t) 0 ≠ 0 := by simpa [X] using hkey 0
    have h2 : X (y,t) 2 ≠ 0 := by simpa [X] using hkey 2
    exact (hgdiff (X (y,t)) h0 h2).comp_hasDerivAt t (haff y t)
  have hGc : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)), Continuous (fun t => G (y,t)) :=
    Filter.Eventually.of_forall fun y => by
      simpa only [G, Function.comp_def] using hgcont.comp (hcontX y)
  have hΨc : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)), Continuous (fun t => Ψ (y,t)) :=
    Filter.Eventually.of_forall fun y => by
      simpa only [Ψ, Function.comp_def] using hψ.continuous.comp (hcontX y)
  have hΨd : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)),
      ∀ t, HasDerivAt (fun s => Ψ (y,s)) (Ψp (y,t)) t := by
    refine Filter.Eventually.of_forall fun y t => ?_
    have hd : HasFDerivAt ψ (fderiv ℝ ψ (X (y,t))) (X (y,t)) :=
      (hψ.differentiable one_ne_zero).differentiableAt.hasFDerivAt
    simpa only [Ψ, Ψp, Function.comp_def] using hd.comp_hasDerivAt t (haff y t)
  -- The boundary terms vanish along each fibre because `ψ * g` has compact support.
  have hRbound : ∃ R : ℝ, ∀ x ∈ tsupport (ψ * g), ‖x‖ ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
      ((show HasCompactSupport (ψ * g) from hgcs.mul_left (f := ψ)).isBounded)
    exact ⟨R, hR⟩
  obtain ⟨R, hR⟩ := hRbound
  set R0 : ℝ := |R| + 1 with hR0def
  have hR0 : ∀ x ∈ tsupport (ψ * g), ‖x‖ ≤ R0 := fun x hx => by
    have := hR x hx
    rw [hR0def]; linarith [le_abs_self R]
  have hR0pos : 0 < R0 := by rw [hR0def]; positivity
  have hvan : ∀ (y : Fin 2 → ℝ) (t : ℝ), R0 < |t| → ψ (X (y,t)) * g (X (y,t)) = 0 := by
    intro y t ht
    have hle : |t| ≤ ‖X (y,t)‖ := by
      have h1 : (X (y,t)) i = t := by
        rw [show X (y,t) = toLpCLE (i.insertNth t y : Fin 3 → ℝ) from rfl]
        exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) i t y
      calc |t| = |(X (y,t)) i| := by rw [h1]
        _ ≤ ‖X (y,t)‖ := by simpa using PiLp.norm_apply_le (X (y,t)) i
    have hmem : X (y,t) ∉ tsupport (ψ * g) := fun hmem =>
      absurd (hR0 _ hmem) (not_le.mpr (lt_of_lt_of_le ht hle))
    simpa only [Pi.mul_apply] using image_eq_zero_of_notMem_tsupport hmem
  have hbot : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)),
      Tendsto (fun t => Ψ (y,t) * G (y,t)) atBot (𝓝 0) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have hp : (fun t : ℝ => Ψ (y,t) * G (y,t)) =ᶠ[atBot] (fun _ => (0:ℝ)) := by
      refine eventually_atBot.mpr ⟨-(R0+1), fun t ht => ?_⟩
      have htR : R0 < |t| := by
        have h2 : t < 0 := by linarith
        rw [abs_of_neg h2]; linarith
      simpa only [Ψ, G] using hvan y t htR
    exact tendsto_const_nhds.congr' hp.symm
  have htop : ∀ᵐ y ∂(volume : Measure (Fin 2 → ℝ)),
      Tendsto (fun t => Ψ (y,t) * G (y,t)) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have hp : (fun t : ℝ => Ψ (y,t) * G (y,t)) =ᶠ[atTop] (fun _ => (0:ℝ)) := by
      refine eventually_atTop.mpr ⟨R0+1, fun t ht => ?_⟩
      have htR : R0 < |t| := by
        have h2 : 0 < t := by linarith
        rw [abs_of_pos h2]; linarith
      simpa only [Ψ, G] using hvan y t htR
    exact tendsto_const_nhds.congr' hp.symm
  -- Integrability of the two products on `ℝ³`.
  have hIntA : Integrable (fun x : R3 => ψ x * fderiv ℝ g x (e i)) := by
    have h1 : Integrable (fun x : R3 => ψ x • fderiv ℝ g x) :=
      hgint.integrable_smul_left_of_hasCompactSupport hψ.continuous hψcs
    have h2 := (evalCLM (e i)).integrable_comp h1
    simpa [evalCLM, smul_apply, smul_eq_mul] using h2
  have hIntB : Integrable (fun x : R3 => fderiv ℝ ψ x (e i) * g x) := by
    have hcontF : Continuous (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      (hψ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
    have hcsF : HasCompactSupport (fun x : R3 => fderiv ℝ ψ x (e i)) :=
      hasCompactSupport_fderiv_apply_e hψcs i
    have hloc : LocallyIntegrable g (volume : Measure R3) := hgcont.locallyIntegrable
    have h := hloc.integrable_smul_right_of_hasCompactSupport hcontF hcsF
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    exact mul_comm _ _
  -- Transfer along the measure preserving coordinate map.
  have hΨGp : Integrable (fun p : (Fin 2 → ℝ) × ℝ => Ψ p * Gp p) (volume.prod volume) := by
    have h := (hMP.integrable_comp_emb hEmb
      (g := fun x : R3 => ψ x * fderiv ℝ g x (e i))).mpr hIntA
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hφX p, Ψ, Gp]
  have hΨpG : Integrable (fun p : (Fin 2 → ℝ) × ℝ => Ψp p * G p) (volume.prod volume) := by
    have h := (hMP.integrable_comp_emb hEmb
      (g := fun x : R3 => fderiv ℝ ψ x (e i) * g x)).mpr hIntB
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hφX p, Ψp, G]
  have hibp := Work.FTS.PressureOn.offPlanes.ibp_off_plane_prod (E := Fin 2 → ℝ)
    (μ := (volume : Measure (Fin 2 → ℝ))) hΨGp hΨpG hGc hΨc hΨd hGd hbot htop
  have h1 : ∫ x : R3, ψ x * fderiv ℝ g x (e i)
      = ∫ p : (Fin 2 → ℝ) × ℝ, Ψ p * Gp p ∂(volume.prod volume) := by
    have h := hMP.integral_comp hEmb (g := fun x : R3 => ψ x * fderiv ℝ g x (e i))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [hφX p, Ψ, Gp])
  have h2 : ∫ x : R3, g x * fderiv ℝ ψ x (e i)
      = ∫ p : (Fin 2 → ℝ) × ℝ, G p * Ψp p ∂(volume.prod volume) := by
    have h := hMP.integral_comp hEmb (g := fun x : R3 => g x * fderiv ℝ ψ x (e i))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [hφX p, G, Ψp])
  rw [h1, h2, hibp]
  rw [show (∫ p : (Fin 2 → ℝ) × ℝ, Ψp p * G p ∂(volume.prod volume))
      = ∫ p : (Fin 2 → ℝ) × ℝ, G p * Ψp p ∂(volume.prod volume) from
        integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)]

end Work.FTS.PressureOn.OffPlanes
