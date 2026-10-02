import Mathlib
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.Thom.exists_path_GL_pos_linear

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology
open Filter

namespace Work.PTGeometric

open Work.PTGeometric.HOF

noncomputable section

variable {N : ℕ}

/-! ## Auxiliary lemmas for the germ statement

The proof of `Work.PTGeometric.eucFam_germ_ball` proceeds in the standard way:

* the germ lemma `Work.PTGeometric.germ_small` computes the induced map on the *small* ball,
  by homotoping `F` to its linear part `z ↦ b + A (z - a)` (the derivative estimate
  `Work.PTGeometric.germ_estimate`), then the linear part to the translation `z ↦ z + (b - a)`
  along the path of invertible maps `Work.Thom.exists_path_GL_pos_linear`, and finally using
  translation invariance `Work.PTGeometric.HOF.eucFam_translation` (in the form
  `eucFam_translation'`);
* the passage from the small ball back to the ball of radius `ρ` of the statement is excision
  (`Work.PTGeometric.HOF.excE_symm_incl`). -/

/-- **A positive-determinant endomorphism of `ℝ^N` is bijective.** -/
theorem bijective_of_det_pos (A : Euc N →L[ℝ] Euc N) (hdet : 0 < LinearMap.det A.toLinearMap) :
    Function.Bijective A := by
  have hne : LinearMap.det A.toLinearMap ≠ 0 := ne_of_gt hdet
  have hker : A.toLinearMap.ker = ⊥ := by
    by_contra hc
    exact hne ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hc)
  have hinj : Function.Injective A := by
    intro x y hxy
    have h2 : x - y = 0 := by
      have hmem : x - y ∈ A.toLinearMap.ker := by
        rw [LinearMap.mem_ker]
        rw [map_sub]
        rw [show A.toLinearMap x = A.toLinearMap y from hxy]
        rw [sub_self]
      rw [hker] at hmem
      simpa using hmem
    exact sub_eq_zero.mp h2
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap) rfl).mp
    hinj⟩

/-- **The norm lower bound for an invertible endomorphism of `ℝ^N`.** -/
theorem exists_pos_mul_norm_le_of_bijective' (A : Euc N →L[ℝ] Euc N)
    (hA : Function.Bijective A) : ∃ c : ℝ, 0 < c ∧ ∀ w : Euc N, c * ‖w‖ ≤ ‖A w‖ := by
  let e₀ : Euc N ≃ₗ[ℝ] Euc N := LinearEquiv.ofBijective (A : Euc N →ₗ[ℝ] Euc N) hA
  let e : Euc N ≃L[ℝ] Euc N := e₀.toContinuousLinearEquiv
  have hle : ∀ z : Euc N, e z = A z := by
    intro z
    have h1 : e z = e₀ z := rfl
    have h2 : e₀ z = (A : Euc N →ₗ[ℝ] Euc N) z := by
      rw [LinearEquiv.ofBijective_apply]
    exact h1.trans h2
  have hMz : ∀ z : Euc N, ‖z‖ ≤ ‖(e.symm : Euc N →L[ℝ] Euc N)‖ * ‖A z‖ := by
    intro z
    have hsym : (e.symm : Euc N →L[ℝ] Euc N) (e z) = z := by
      simp only [← ContinuousLinearEquiv.coe_toLinearEquiv]
      exact ContinuousLinearEquiv.symm_apply_apply e z
    calc ‖z‖ = ‖(e.symm : Euc N →L[ℝ] Euc N) (e z)‖ := by rw [hsym]
      _ = ‖(e.symm : Euc N →L[ℝ] Euc N) (A z)‖ := by rw [hle z]
      _ ≤ ‖(e.symm : Euc N →L[ℝ] Euc N)‖ * ‖A z‖ := ContinuousLinearMap.le_opNorm _ _
  refine ⟨(max ‖(e.symm : Euc N →L[ℝ] Euc N)‖ 1)⁻¹,
    inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _)), fun z => ?_⟩
  rw [inv_mul_le_iff₀ (lt_of_lt_of_le one_pos (le_max_right ‖(e.symm : Euc N →L[ℝ] Euc N)‖ 1))]
  calc ‖z‖ ≤ ‖(e.symm : Euc N →L[ℝ] Euc N)‖ * ‖A z‖ := hMz z
    _ ≤ max ‖(e.symm : Euc N →L[ℝ] Euc N)‖ 1 * ‖A z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **The derivative estimate.**  If `F` is differentiable at `a` with bijective derivative `A`
and `F a = b`, then near `a` the difference `F - (b + A (− - a))` is dominated by `A/2`; this is what
makes the straight-line homotopy from `F` to its linear part avoid the value `b` away from `a`. -/
theorem germ_estimate (F : Euc N → Euc N) (A : Euc N →L[ℝ] Euc N) (a b : Euc N)
    (hd : HasFDerivAt F A a) (hFa : F a = b) (hA : Function.Bijective A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euc N, ‖z - a‖ ≤ δ →
      ‖(F z - b) - A (z - a)‖ ≤ (1/2) * ‖A (z - a)‖ := by
  obtain ⟨c, hc, hcA⟩ := exists_pos_mul_norm_le_of_bijective' A hA
  have hlit : (fun w : Euc N => F (w + a) - b - A w) =o[𝓝 (0 : Euc N)] fun w => w := by
    have h1 : Tendsto (fun w : Euc N => w + a) (𝓝 (0 : Euc N)) (𝓝 (0 + a)) := by
      simpa only [id_eq] using (tendsto_id.add (tendsto_const_nhds (x := a)))
    rw [zero_add] at h1
    have h2 := hd.isLittleO.comp_tendsto h1
    refine h2.congr' (Filter.EventuallyEq.of_eq (funext fun w => ?_))
      (Filter.EventuallyEq.of_eq (funext fun w => ?_))
    · simp only [Function.comp_apply, hFa, map_add, map_sub, add_sub_cancel_right]
    · simp only [Function.comp_apply, add_sub_cancel_right]
  have hev : ∀ᶠ w in 𝓝 (0 : Euc N), ‖F (w + a) - b - A w‖ ≤ (c/2) * ‖w‖ :=
    hlit.def (c := c/2) (by linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ/2, by linarith, fun z hz => ?_⟩
  have hz' : ‖z - a‖ < δ := by linarith
  have hmem : z - a ∈ Metric.ball (0 : Euc N) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz'
  have h1 : ‖F ((z - a) + a) - b - A (z - a)‖ ≤ (c/2) * ‖z - a‖ := hδsub hmem
  rw [sub_add_cancel] at h1
  have h2 : c * ‖z - a‖ ≤ ‖A (z - a)‖ := hcA (z - a)
  calc ‖(F z - b) - A (z - a)‖ ≤ (c/2) * ‖z - a‖ := h1
    _ ≤ (1/2) * ‖A (z - a)‖ := by linarith

/-- **Translation invariance of the Euclidean family, in the form needed below**: the target
excluded set is an arbitrary singleton `{w}` with `w = v + c`. -/
theorem eucFam_translation' (hN : 1 ≤ N) (c v w : Euc N) (hw : w = v + c)
    (hf : ∀ x : Euc N, x ∉ ({v} : Set (Euc N)) → eucSub c x ∉ ({w} : Set (Euc N))) :
    (RelHmapOf N (eucSub c) ({v} : Set (Euc N)) ({w} : Set (Euc N)) hf) (eucFam N hN v)
      = eucFam N hN w := by
  subst hw
  rw [RelHmapOf_congr (f := eucSub c) (f' := eucSub c) rfl hf (eucSub_mem c v)]
  exact eucFam_translation N hN c v

/-- **The germ lemma on a ball where the derivative estimate holds.**  If `F` is continuous on the
ball of radius `r` around `a`, maps `a` to `b`, has no other preimage of `b` in the ball, and is
close to its linear part `z ↦ b + A (z - a)` (with `A` bijective of positive determinant) in the
sense of `hest`, then the induced map on local homology carries the local generator at `a` to the
local generator at `b`. -/
theorem germ_small (hN : 1 ≤ N) (a b : Euc N) (r : ℝ) (hr : 0 < r)
    (F : Euc N → Euc N)
    (hFc : Continuous fun z : ↥(Metric.ball (α := Euc N) a r) => F z)
    (hnz : ∀ z ∈ Metric.ball (α := Euc N) a r, z ≠ a → F z ≠ b)
    (A : Euc N →L[ℝ] Euc N) (hdet : 0 < LinearMap.det A.toLinearMap)
    (hd : HasFDerivAt F A a) (hAbij : Function.Bijective A)
    (hest : ∀ z : Euc N, ‖z - a‖ ≤ r → ‖(F z - b) - A (z - a)‖ ≤ (1/2) * ‖A (z - a)‖) :
    RelHmapOf N (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Euc N) a r) => F z, hFc⟩)
        (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N))
        (fun z hz => hnz (z : Euc N) z.2 (fun h => hz h))
        ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
          (Metric.mem_ball_self hr) isClosed_singleton).symm (eucFam N hN a))
      = eucFam N hN b := by
  classical
  have haV : a ∈ Metric.ball (α := Euc N) a r := Metric.mem_ball_self hr
  have hLcont : Continuous fun z : ↥(Metric.ball (α := Euc N) a r) => b + A ((z : Euc N) - a) :=
    continuous_const.add (A.continuous.comp (continuous_subtype_val.sub continuous_const))
  let Fm : TopCat.of ↥(Metric.ball (α := Euc N) a r) ⟶ TopCat.of (Euc N) :=
    TopCat.ofHom ⟨fun z => F (z : Euc N), hFc⟩
  let Lm : TopCat.of ↥(Metric.ball (α := Euc N) a r) ⟶ TopCat.of (Euc N) :=
    TopCat.ofHom ⟨fun z => b + A ((z : Euc N) - a), hLcont⟩
  let Tm : TopCat.of ↥(Metric.ball (α := Euc N) a r) ⟶ TopCat.of (Euc N) :=
    Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) ≫ eucSub (b - a)
  have hf : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) z
        ∉ ({a} : Set (Euc N)) :=
    fun z hz => hz
  have hpSub : ∀ x : Euc N, x ∉ ({a} : Set (Euc N)) →
      eucSub (b - a) x ∉ ({b} : Set (Euc N)) := fun x hx => by
    simp only [Set.mem_singleton_iff] at hx ⊢
    intro h
    have h' : x + (b - a) = b := h
    exact hx (sub_eq_zero.mp (by
      rw [show x - a = (x + (b - a)) - b from by abel, h', sub_self]))
  have hpF : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      Fm z ∉ ({b} : Set (Euc N)) := fun z hz => hnz (z : Euc N) z.2 (fun h => hz h)
  have hpL : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      Lm z ∉ ({b} : Set (Euc N)) := by
    intro z hz
    have hz' : (z : Euc N) ≠ a := fun h => hz h
    show b + A ((z : Euc N) - a) ≠ b
    intro h
    have hX : A ((z : Euc N) - a) = 0 :=
      add_left_cancel (h.trans (add_zero b).symm)
    have hw : (z : Euc N) - a = 0 := hAbij.1 (by rw [hX, map_zero])
    exact hz' (sub_eq_zero.mp hw)
  have hpT : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      Tm z ∉ ({b} : Set (Euc N)) := fun z hz => hpSub (z : Euc N) (fun h => hz h)
  obtain ⟨γ, hγ0, hγ1, hγbij⟩ := Work.Thom.exists_path_GL_pos_linear N A hdet
  let H1fun : unitInterval × ↥(Metric.ball (α := Euc N) a r) → Euc N :=
    fun p => b + ((1 - (p.1 : ℝ)) • (F (p.2 : Euc N) - b) + (p.1 : ℝ) • (A ((p.2 : Euc N) - a)))
  have ht : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) => (p.2 : Euc N) :=
    continuous_subtype_val.comp continuous_snd
  have hFp : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) => F (p.2 : Euc N) :=
    hFc.comp continuous_snd
  have hH1fun : Continuous H1fun := by
    have haux : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) =>
        (1 - (p.1 : ℝ)) • (F (p.2 : Euc N) - b) + (p.1 : ℝ) • (A ((p.2 : Euc N) - a)) :=
      ((continuous_const.sub ht).smul (hFp.sub continuous_const)).add
        (ht.smul (A.continuous.comp (hz.sub continuous_const)))
    exact continuous_const.add haux
  let H1 : TopCat.Homotopy Fm Lm :=
    ContinuousMap.Homotopy.mk ⟨H1fun, hH1fun⟩
      (fun z => by
        show b + ((1 - ((0 : unitInterval) : ℝ)) • (F (z : Euc N) - b)
          + ((0 : unitInterval) : ℝ) • (A ((z : Euc N) - a))) = F (z : Euc N)
        simp)
      (fun z => by
        show b + ((1 - ((1 : unitInterval) : ℝ)) • (F (z : Euc N) - b)
          + ((1 : unitInterval) : ℝ) • (A ((z : Euc N) - a))) = b + A ((z : Euc N) - a)
        simp)
  have hH1mem : ∀ t z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      H1 (t, z) ∉ ({b} : Set (Euc N)) := by
    intro t z hz'
    have hz'' : (z : Euc N) ≠ a := fun h => hz' h
    have hzr : ‖(z : Euc N) - a‖ ≤ r := le_of_lt (by
      have h := z.2
      rwa [Metric.mem_ball, dist_eq_norm] at h)
    have hestz := hest (z : Euc N) hzr
    have hAw : A ((z : Euc N) - a) ≠ 0 := by
      intro h
      have hw : (z : Euc N) - a = 0 := hAbij.1 (by rw [h, map_zero])
      exact hz'' (sub_eq_zero.mp hw)
    intro hzero
    have hzero' : b + ((1 - (t : ℝ)) • (F (z : Euc N) - b)
        + (t : ℝ) • (A ((z : Euc N) - a))) = b := hzero
    have hX : (1 - (t : ℝ)) • (F (z : Euc N) - b) + (t : ℝ) • (A ((z : Euc N) - a)) = 0 :=
      add_left_cancel (hzero'.trans (add_zero b).symm)
    have hsub : (F (z : Euc N) - b)
        = A ((z : Euc N) - a) + ((F (z : Euc N) - b) - A ((z : Euc N) - a)) := by abel
    rw [hsub] at hX
    have key : (1 - (t : ℝ)) • (A ((z : Euc N) - a)
          + ((F (z : Euc N) - b) - A ((z : Euc N) - a)))
        + (t : ℝ) • (A ((z : Euc N) - a))
        = A ((z : Euc N) - a) + (1 - (t : ℝ)) • ((F (z : Euc N) - b) - A ((z : Euc N) - a)) := by
      module
    rw [key] at hX
    have hnorm : ‖A ((z : Euc N) - a)‖ ≤ (1/2) * ‖A ((z : Euc N) - a)‖ := by
      have hE : ‖(1 - (t : ℝ)) • ((F (z : Euc N) - b) - A ((z : Euc N) - a))‖
          = ‖A ((z : Euc N) - a)‖ := by
        have hneg : A ((z : Euc N) - a)
            = -((1 - (t : ℝ)) • ((F (z : Euc N) - b) - A ((z : Euc N) - a))) :=
          (eq_neg_iff_add_eq_zero).mpr hX
        conv_rhs => rw [hneg]
        rw [norm_neg]
      calc ‖A ((z : Euc N) - a)‖
          = ‖(1 - (t : ℝ)) • ((F (z : Euc N) - b) - A ((z : Euc N) - a))‖ := hE.symm
        _ = |1 - (t : ℝ)| * ‖(F (z : Euc N) - b) - A ((z : Euc N) - a)‖ := norm_smul _ _
        _ ≤ 1 * ‖(F (z : Euc N) - b) - A ((z : Euc N) - a)‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              rw [abs_le]
              exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
        _ = ‖(F (z : Euc N) - b) - A ((z : Euc N) - a)‖ := one_mul _
        _ ≤ (1/2) * ‖A ((z : Euc N) - a)‖ := hestz
    have hpos : 0 < ‖A ((z : Euc N) - a)‖ := norm_pos_iff.mpr hAw
    linarith
  have h1 : RelHmapOf N Fm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
      ({b} : Set (Euc N)) hpF
      = RelHmapOf N Lm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpL :=
    RelHmapOf_homotopic hpF hpL H1 hH1mem
  let H2fun : unitInterval × ↥(Metric.ball (α := Euc N) a r) → Euc N :=
    fun p => b + (γ p.1) ((p.2 : Euc N) - a)
  have hH2fun : Continuous H2fun := by
    have h1 : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) =>
        (p.2 : Euc N) - a := (continuous_subtype_val.comp continuous_snd).sub continuous_const
    have h2 : Continuous fun p : unitInterval × ↥(Metric.ball (α := Euc N) a r) =>
        (γ p.1) ((p.2 : Euc N) - a) := (γ.continuous.comp continuous_fst).clm_apply h1
    exact continuous_const.add h2
  let H2 : TopCat.Homotopy Lm Tm :=
    ContinuousMap.Homotopy.mk ⟨H2fun, hH2fun⟩
      (fun z => by
        show b + (γ 0) ((z : Euc N) - a) = b + A ((z : Euc N) - a)
        rw [hγ0])
      (fun z => by
        show b + (γ 1) ((z : Euc N) - a) = (z : Euc N) + (b - a)
        rw [hγ1]
        simp only [one_apply_eq_self]
        abel)
  have hH2mem : ∀ t z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      H2 (t, z) ∉ ({b} : Set (Euc N)) := by
    intro t z hz'
    have hz'' : (z : Euc N) ≠ a := fun h => hz' h
    have hw : (z : Euc N) - a ≠ 0 := sub_ne_zero.mpr hz''
    intro hzero
    have hzero' : b + (γ t) ((z : Euc N) - a) = b := hzero
    have hX : (γ t) ((z : Euc N) - a) = 0 := add_left_cancel (hzero'.trans (add_zero b).symm)
    exact hw ((hγbij t).1 (by rw [hX, map_zero]))
  have h2 : RelHmapOf N Lm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
      ({b} : Set (Euc N)) hpL
      = RelHmapOf N Tm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpT :=
    RelHmapOf_homotopic hpL hpT H2 hH2mem
  have hstep : RelHmapOf N Tm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpT
      = (RelHmapOf N (eucSub (b - a)) ({a} : Set (Euc N)) ({b} : Set (Euc N)) hpSub).comp
          (excM (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) ({a} : Set (Euc N))) := by
    have h := RelHmapOf_comp (n := N)
      (f := Work.Cohomology.subtypeIncl (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r))
      (g := eucSub (b - a))
      (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
      (K' := ({a} : Set (Euc N))) (K'' := ({b} : Set (Euc N))) hf hpSub hpT
    rw [← h]
    rfl
  have hpi : excM (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) ({a} : Set (Euc N))
      ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
        haV isClosed_singleton).symm (eucFam N hN a)) = eucFam N hN a :=
    punctIso_excM_symm (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
      haV isClosed_singleton (eucFam N hN a)
  have h3 : RelHmapOf N Tm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
      ({b} : Set (Euc N)) hpT
      ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
        haV isClosed_singleton).symm (eucFam N hN a)) = eucFam N hN b := by
    rw [hstep, LinearMap.comp_apply, hpi]
    exact eucFam_translation' hN (b - a) a b (by abel) hpSub
  change RelHmapOf N Fm (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpF
        ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
          (Metric.mem_ball_self hr) isClosed_singleton).symm (eucFam N hN a)) = eucFam N hN b
  rw [h1, h2]
  exact h3

theorem eucFam_germ_ball (N : ℕ) (hN : 1 ≤ N) (a b : Work.PTGeometric.HOF.Euc N) (ρ : ℝ) (hρ : 0 < ρ)
    (F : Work.PTGeometric.HOF.Euc N → Work.PTGeometric.HOF.Euc N)
    (hFc : Continuous fun z : ↥(Metric.ball (α := Work.PTGeometric.HOF.Euc N) a ρ) => F z)
    (hFa : F a = b)
    (hnz : ∀ z ∈ Metric.ball (α := Work.PTGeometric.HOF.Euc N) a ρ, z ≠ a → F z ≠ b)
    (A : Work.PTGeometric.HOF.Euc N →L[ℝ] Work.PTGeometric.HOF.Euc N) (hd : HasFDerivAt F A a)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    Work.PTGeometric.HOF.RelHmapOf N
      (TopCat.ofHom ⟨fun z : ↥(Metric.ball (α := Work.PTGeometric.HOF.Euc N) a ρ) => F z, hFc⟩)
      (Work.PTGeometric.HOF.punctSet (TopCat.of (Work.PTGeometric.HOF.Euc N)) (Metric.ball (α := Work.PTGeometric.HOF.Euc N) a ρ) a)
      ({b} : Set (Work.PTGeometric.HOF.Euc N))
      (fun z hz => hnz (z : Work.PTGeometric.HOF.Euc N) z.2 (fun h => hz h))
      ((Work.PTGeometric.HOF.punctIso (TopCat.of (Work.PTGeometric.HOF.Euc N)) N (Metric.ball (α := Work.PTGeometric.HOF.Euc N) a ρ)
          Metric.isOpen_ball a (Metric.mem_ball_self hρ) isClosed_singleton).symm
        (Work.PTGeometric.HOF.eucFam N hN a))
      = Work.PTGeometric.HOF.eucFam N hN b := by
  classical
  have hAbij : Function.Bijective A := bijective_of_det_pos A hdet
  obtain ⟨δ, hδpos, hδest⟩ := germ_estimate F A a b hd hFa hAbij
  set r : ℝ := min ρ δ with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact lt_min hρ hδpos
  have hrρ : r ≤ ρ := by rw [hrdef]; exact min_le_left _ _
  have hrδ : r ≤ δ := by rw [hrdef]; exact min_le_right _ _
  have hsub : Metric.ball (α := Euc N) a r ⊆ Metric.ball (α := Euc N) a ρ :=
    Metric.ball_subset_ball hrρ
  have hFcr : Continuous fun z : ↥(Metric.ball (α := Euc N) a r) => F z :=
    hFc.comp (Continuous.subtype_mk continuous_subtype_val (fun z => hsub z.2))
  have hest : ∀ z : Euc N, ‖z - a‖ ≤ r → ‖(F z - b) - A (z - a)‖ ≤ (1/2) * ‖A (z - a)‖ :=
    fun z hz => hδest z (le_trans hz hrδ)
  have hnzr : ∀ z ∈ Metric.ball (α := Euc N) a r, z ≠ a → F z ≠ b :=
    fun z hz => hnz z (hsub hz)
  have hsmall := germ_small hN a b r hrpos F hFcr hnzr A hdet hd hAbij hest
  have haB : a ∈ Metric.ball (α := Euc N) a r := Metric.mem_ball_self hrpos
  have haU : a ∈ Metric.ball (α := Euc N) a ρ := Metric.mem_ball_self hρ
  let inc : TopCat.of ↥(Metric.ball (α := Euc N) a r) ⟶
      TopCat.of ↥(Metric.ball (α := Euc N) a ρ) :=
    inclSub (Metric.ball (α := Euc N) a r) (Metric.ball (α := Euc N) a ρ) hsub
  let Fbig : TopCat.of ↥(Metric.ball (α := Euc N) a ρ) ⟶ TopCat.of (Euc N) :=
    TopCat.ofHom ⟨fun z => F (z : Euc N), hFc⟩
  let Fsmall : TopCat.of ↥(Metric.ball (α := Euc N) a r) ⟶ TopCat.of (Euc N) :=
    TopCat.ofHom ⟨fun z => F (z : Euc N), hFcr⟩
  have hpBig : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a ρ) a →
      Fbig z ∉ ({b} : Set (Euc N)) := fun z hz => hnz (z : Euc N) z.2 (fun h => hz h)
  have hpSmall : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      Fsmall z ∉ ({b} : Set (Euc N)) :=
    fun z hz => hnz (z : Euc N) (hsub z.2) (fun h => hz h)
  have hinc : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      inc z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a ρ) a := fun z hz => hz
  have hgf : ∀ z, z ∉ punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a →
      (inc ≫ Fbig) z ∉ ({b} : Set (Euc N)) := fun z hz => hpBig (inc z) (hinc z hz)
  have hmap : inc ≫ Fbig = Fsmall := by
    apply TopCat.ext
    intro z
    rfl
  have hcomp := RelHmapOf_comp (n := N) (f := inc) (g := Fbig)
    (K := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
    (K' := punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a ρ) a)
    (K'' := ({b} : Set (Euc N))) hinc hpBig hgf
  have hrestat : RelHmapOf N (inc ≫ Fbig)
        (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hgf
      = RelHmapOf N Fsmall (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpSmall :=
    RelHmapOf_congr hmap hgf hpSmall
  have hexc : (punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a ρ) Metric.isOpen_ball a
        haU isClosed_singleton).symm (eucFam N hN a)
      = RelHmapOf N inc (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
          (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a ρ) a) hinc
          ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
            haB isClosed_singleton).symm (eucFam N hN a)) := by
    have h := excE_symm_incl (X := TopCat.of (Euc N)) (B := Metric.ball (α := Euc N) a r)
      (U := Metric.ball (α := Euc N) a ρ) hsub Metric.isOpen_ball Metric.isOpen_ball
      (K := ({a} : Set (Euc N))) (Set.singleton_subset_iff.mpr haB)
      (Set.singleton_subset_iff.mpr haU) isClosed_singleton (eucFam N hN a)
    exact h.symm
  have hgoal : RelHmapOf N Fbig (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a ρ) a)
        ({b} : Set (Euc N)) hpBig
        ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a ρ) Metric.isOpen_ball a
          haU isClosed_singleton).symm (eucFam N hN a))
      = RelHmapOf N Fsmall (punctSet (TopCat.of (Euc N)) (Metric.ball (α := Euc N) a r) a)
        ({b} : Set (Euc N)) hpSmall
        ((punctIso (TopCat.of (Euc N)) N (Metric.ball (α := Euc N) a r) Metric.isOpen_ball a
          haB isClosed_singleton).symm (eucFam N hN a)) := by
    rw [hexc, ← LinearMap.comp_apply, hcomp, hrestat]
  exact hgoal.trans hsmall

end

end Work.PTGeometric
