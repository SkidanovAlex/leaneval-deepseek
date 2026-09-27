import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.gH_eq_zero_iff
import Submission.Work.Mostow.ballConvex
import Submission.Work.Mostow.segfunHasDerivAt
import Submission.Work.Mostow.segfunSpeed
import Submission.Work.Mostow.localInverseDini
import Submission.Work.Mostow.propagate
import Submission.Work.Mostow.hdistIsCompact
import Submission.Work.Mostow.hdistContinuous

set_option maxHeartbeats 2000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Distance `≤` arclength for a curve of unit hyperbolic speed -/

theorem localInverseCurve_aux {n : ℕ} (γ : ℝ → E n) (a b : ℝ) (hab : a ≤ b)
    (hcont : Continuous (fun p : E n × E n => hdist p.1 p.2))
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (hder : ∀ t ∈ Set.Icc a b, HasDerivAt γ (deriv γ t) t)
    (hsp : ∀ t ∈ Set.Icc a b, gH (γ t) (deriv γ t) = 1) :
    hdist (γ a) (γ b) ≤ b - a := by
  refine propagate a b hab γ ?_ htri ?_
  · have hγ : ContinuousOn γ (Set.Icc a b) :=
      fun t ht => (hder t ht).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => ((γ a), γ t)) (Set.Icc a b) :=
      ContinuousOn.prodMk continuousOn_const hγ
    have h3 : ContinuousOn (fun t : ℝ => ((fun p : E n × E n => hdist p.1 p.2) ((γ a), γ t)))
        (Set.Icc a b) :=
      hcont.comp_continuousOn h2
    simpa using h3
  · intro t ht ε hε
    exact localInverseDini γ t (deriv γ t) (hder t ⟨ht.1, le_of_lt ht.2⟩)
      (hsp t ⟨ht.1, le_of_lt ht.2⟩) ε hε

/-! ## A hyperbolic ball is a Euclidean neighbourhood of its centre -/

theorem localInverseNhds_aux {n : ℕ} (u : E n) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : E n, hdist u x < δ → dist x u < ε := by
  intro ε hε
  have hS : IsCompact ({x : E n | hdist u x ≤ 1} ∩ {x : E n | ε ≤ dist x u}) :=
    (hdistIsCompact n u 1).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hpos : ∀ y ∈ ({x : E n | hdist u x ≤ 1} ∩ {x : E n | ε ≤ dist x u}),
      0 < hdist u y := by
    intro y hy
    rcases eq_or_ne y u with h | h
    · exfalso
      have hy2 : ε ≤ dist y u := hy.2
      rw [h] at hy2
      rw [dist_self] at hy2
      linarith
    · exact hdist_pos_of_ne h.symm
  obtain ⟨δ, hδpos, hδ⟩ := hS.exists_forall_le'
    ((hdistContinuous n).comp (continuous_const.prodMk continuous_id)).continuousOn hpos
  refine ⟨min δ 1, lt_min hδpos one_pos, fun x hx => ?_⟩
  by_contra hcon
  have hxS : x ∈ ({x : E n | hdist u x ≤ 1} ∩ {x : E n | ε ≤ dist x u}) :=
    ⟨le_of_lt (lt_of_lt_of_le hx (min_le_right _ _)), le_of_not_gt hcon⟩
  have h1 : δ ≤ hdist u x := hδ x hxS
  have h2 : hdist u x < δ := lt_of_lt_of_le hx (min_le_left _ _)
  linarith

/-! ## Endpoints of the explicit geodesic segment -/

theorem segfun_zero_aux {n : ℕ} (p q : E n) (hd : hdist p q ≠ 0) : segfun p q 0 = p := by
  simp only [segfun, sub_zero, Real.sinh_zero, zero_div, zero_smul, add_zero]
  rw [div_self (fun h => hd (Real.sinh_eq_zero.mp h)), one_smul]

theorem segfun_end_aux {n : ℕ} (p q : E n) (hd : hdist p q ≠ 0) :
    segfun p q (hdist p q) = q := by
  simp only [segfun, sub_self, Real.sinh_zero, zero_div, zero_smul, zero_add]
  rw [div_self (fun h => hd (Real.sinh_eq_zero.mp h)), one_smul]

/-! ## The local inverse -/

theorem localInverse {n : ℕ} (F : E n → E n) (hF : ContDiff ℝ 1 F)
    (hiso : ∀ u v, gH (F u) (fderiv ℝ F u v) = gH u v)
    (hcont : Continuous (fun p : E n × E n => hdist p.1 p.2))
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (h1lip : ∀ u v, hdist (F u) (F v) ≤ hdist u v) (u : E n) :
    ∃ (ρ : ℝ) (G : E n → E n), 0 < ρ ∧ G (F u) = u ∧
      (∀ x, hdist u x < ρ → G (F x) = x) ∧
      (∀ x, hdist (F u) x < ρ → F (G x) = x) ∧
      (∀ x y, hdist (F u) x < ρ → hdist (F u) y < ρ → hdist (G x) (G y) ≤ hdist x y) := by
  -- 1. `F` is strictly differentiable, with injective differential everywhere
  have hstr : ∀ z : E n, HasStrictFDerivAt F (fderiv ℝ F z) z := by
    intro z
    exact hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
      (Filter.Eventually.of_forall fun y =>
        ((hF.differentiable (by norm_num)).differentiableAt).hasFDerivAt)
      ((hF.continuous_fderiv (by norm_num)).continuousAt)
  have hinj : ∀ z : E n, Function.Injective (fderiv ℝ F z) := by
    intro z a b hab
    have h2 : fderiv ℝ F z a - fderiv ℝ F z b = 0 := sub_eq_zero.mpr hab
    have h : gH z (a - b) = 0 := by
      rw [← hiso z (a - b), map_sub, h2]
      simp [gH]
    exact sub_eq_zero.mp ((gH_eq_zero_iff z (a - b)).mp h)
  -- 2. the differential as a continuous linear equivalence
  let e : E n → E n ≃L[ℝ] E n := fun z =>
    (LinearMap.linearEquivOfInjective (fderiv ℝ F z).toLinearMap (hinj z) rfl).toContinuousLinearEquiv
  have he : ∀ z, (e z : E n →L[ℝ] E n) = fderiv ℝ F z := by
    intro z
    refine ContinuousLinearMap.ext fun v => ?_
    exact LinearMap.linearEquivOfInjective_apply (hinj z) rfl v
  -- 3. the inverse function theorem at `u`
  have hsu : HasStrictFDerivAt F ((e u : E n →L[ℝ] E n)) u := by
    rw [he u]
    exact hstr u
  set φ : OpenPartialHomeomorph (E n) (E n) := hsu.toOpenPartialHomeomorph F with hφ
  set G : E n → E n := fun x => φ.symm x with hG
  have hsrc : u ∈ φ.source := hsu.mem_toOpenPartialHomeomorph_source
  have htgt : F u ∈ φ.target := hsu.image_mem_toOpenPartialHomeomorph_target
  have hcoe : ∀ x : E n, φ x = F x := fun x =>
    congrFun (HasStrictFDerivAt.toOpenPartialHomeomorph_coe (f := F) (f' := e u) hsu) x
  -- 4. `G` maps the target to the source and is a two-sided inverse of `F` there
  have hGF : ∀ x ∈ φ.source, G (F x) = x := by
    intro x hx
    simp only [hG]
    rw [← hcoe x]
    exact φ.left_inv hx
  have hFG : ∀ y ∈ φ.target, F (G y) = y := by
    intro y hy
    simp only [hG]
    rw [← hcoe (φ.symm y)]
    exact φ.right_inv hy
  -- 5. the derivative of `G` is the inverse of the (isometric) derivative of `F`
  have hGderiv : ∀ p ∈ φ.target, HasStrictFDerivAt G ((e (G p)).symm : E n →L[ℝ] E n) p := by
    intro p hp
    have hz : G p ∈ φ.source := φ.map_target hp
    have hFEq : F (G p) = p := hFG p hp
    have hg : ∀ᶠ x in nhds (G p), G (F x) = x :=
      Filter.mem_of_superset (IsOpen.mem_nhds φ.open_source hz) fun x hx => hGF x hx
    have hst : HasStrictFDerivAt F ((e (G p) : E n →L[ℝ] E n)) (G p) := by
      rw [he (G p)]
      exact hstr (G p)
    have h := hst.to_local_left_inverse hg
    rwa [hFEq] at h
  -- 6. consequently the derivative of `G` is isometric for `gH`
  have hGiso : ∀ z ∈ φ.source, ∀ w : E n, gH (F z) w = gH z ((e z).symm w) := by
    intro z hz w
    have hv : (e z : E n →L[ℝ] E n) ((e z).symm w) = w := (e z).apply_symm_apply w
    calc gH (F z) w
        = gH (F z) ((e z : E n →L[ℝ] E n) ((e z).symm w)) := by rw [hv]
      _ = gH z ((e z).symm w) := by rw [he z]; exact hiso z ((e z).symm w)
  -- 7. the radii: a hyperbolic ball at `u` inside the source, at `F u` inside the target
  obtain ⟨εS, hεS, hSS⟩ := Metric.isOpen_iff.mp φ.open_source u hsrc
  obtain ⟨εT, hεT, hTT⟩ := Metric.isOpen_iff.mp φ.open_target (F u) htgt
  obtain ⟨δS, hδS, hδhS⟩ := localInverseNhds_aux u εS hεS
  obtain ⟨δT, hδT, hδhT⟩ := localInverseNhds_aux (F u) εT hεT
  -- 8. assembly
  refine ⟨min δS δT, G, lt_min hδS hδT, hGF u hsrc, ?_, ?_, ?_⟩
  · intro x hx
    exact hGF x (hSS (Metric.mem_ball.mpr (hδhS x (lt_of_lt_of_le hx (min_le_left _ _)))))
  · intro x hx
    exact hFG x (hTT (Metric.mem_ball.mpr (hδhT x (lt_of_lt_of_le hx (min_le_right _ _)))))
  · -- the local inverse is `1`-Lipschitz on the ball around `F u`
    intro x y hx hy
    rcases eq_or_ne x y with hxy | hxy
    · subst hxy
      exact le_of_eq (by rw [(hdist_eq_zero_iff (G x) (G x)).mpr rfl,
        (hdist_eq_zero_iff x x).mpr rfl])
    · have hd : 0 < hdist x y := hdist_pos_of_ne hxy
      have hdne : hdist x y ≠ 0 := ne_of_gt hd
      have hmax : max (hdist (F u) x) (hdist (F u) y) < min δS δT := max_lt hx hy
      -- the whole geodesic from `x` to `y` stays in the target of `φ`
      have hσmem : ∀ t ∈ Set.Icc (0:ℝ) (hdist x y), segfun x y t ∈ φ.target := by
        intro t ht
        have h1 : hdist (F u) (segfun x y t) ≤ max (hdist (F u) x) (hdist (F u) y) :=
          ballConvex x y (F u) hxy t ht
        exact hTT (Metric.mem_ball.mpr
          (hδhT _ (lt_of_lt_of_le (lt_of_le_of_lt h1 hmax) (min_le_right _ _))))
      -- the explicit tangent vector of the segment
      set w : ℝ → E n := fun t =>
        (- Real.cosh (hdist x y - t) / Real.sinh (hdist x y)) • x +
          (Real.cosh t / Real.sinh (hdist x y)) • y with hw
      -- derivative of the composite curve
      have hchain : ∀ t ∈ Set.Icc (0:ℝ) (hdist x y),
          HasDerivAt (fun s => G (segfun x y s)) ((e (G (segfun x y t))).symm (w t)) t := by
        intro t ht
        exact ((hGderiv (segfun x y t) (hσmem t ht)).hasFDerivAt).comp_hasDerivAt t
          (segfunHasDerivAt x y hxy t ht)
      -- the composite curve has unit `gH`-speed
      have hspeed : ∀ t ∈ Set.Icc (0:ℝ) (hdist x y),
          gH (G (segfun x y t)) ((e (G (segfun x y t))).symm (w t)) = 1 := by
        intro t ht
        have hz : G (segfun x y t) ∈ φ.source := φ.map_target (hσmem t ht)
        have hFz : F (G (segfun x y t)) = segfun x y t := hFG (segfun x y t) (hσmem t ht)
        have hone : gH (segfun x y t) (w t) = 1 := segfunSpeed x y hxy t ht
        calc gH (G (segfun x y t)) ((e (G (segfun x y t))).symm (w t))
            = gH (F (G (segfun x y t))) (w t) := (hGiso (G (segfun x y t)) hz (w t)).symm
          _ = gH (segfun x y t) (w t) := by rw [hFz]
          _ = 1 := hone
      have hder : ∀ t ∈ Set.Icc (0:ℝ) (hdist x y),
          HasDerivAt (fun s => G (segfun x y s)) (deriv (fun s => G (segfun x y s)) t) t := by
        intro t ht
        have h := hchain t ht
        rw [h.deriv]
        exact h
      have hsp : ∀ t ∈ Set.Icc (0:ℝ) (hdist x y),
          gH ((fun s => G (segfun x y s)) t) (deriv (fun s => G (segfun x y s)) t) = 1 := by
        intro t ht
        have h := hchain t ht
        rw [h.deriv]
        exact hspeed t ht
      have hmain := localInverseCurve_aux (fun s => G (segfun x y s)) 0 (hdist x y) hd.le
        hcont htri hder hsp
      rw [segfun_zero_aux x y hdne, segfun_end_aux x y hdne, sub_zero] at hmain
      exact hmain

end Work.Mostow
