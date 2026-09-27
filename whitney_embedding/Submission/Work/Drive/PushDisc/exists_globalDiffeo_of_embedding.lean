import Mathlib
import Submission.Work.Drive.PushDisc.localIsotopyGlobalisation
import Submission.Work.PushDisc.localIsotopyGlobalisationTrail
import Submission.Work.Drive.Whitney.pathThroughGLofFixedLine
import Submission.Work.Drive.N2.contDiff_parametric_intervalIntegral
import Submission.Work.Drive.PushDisc.localInverseFamilyTwoSidedRepair
import Submission.Work.Drive.N2.contDiff_parametric_intervalIntegral
import Submission.Work.Whitney.CutPush.arc_unknotting
import Submission.Work.Drive.PushDisc.exists_diffeo_of_localFamily_compact

/-!
# Extending a local diffeomorphism of a neighbourhood of a compact star-convex set

We prove `Work.Drive.PushDisc.exists_globalDiffeo_of_embedding`: given an orientation preserving
local diffeomorphism `θ` on an open set `O` of `ℝ^m`, injective there, and a compact star-convex set
`C ⊆ O`, there is a global `C^∞` diffeomorphism `Θ` of `ℝ^m` (with inverse `Φ`) agreeing with `θ`
on an open neighbourhood of `C`.

The construction is the classical Alexander/reparametrisation method:

* the "reparametrised family" `fam θ ξ₀ β t x = θ ξ₀ + ∫₀¹ dθ(ξ₀ + s·σ(t)·(x-ξ₀))(x-ξ₀) ds`
  (`σ = smoothTransition`) is a family of local diffeomorphisms with `fam · · · 0 =` the affine map
  `x ↦ θ ξ₀ + dθ(ξ₀)(x-ξ₀)` and `fam · · · 1 = θ`;
* the local isotopy globalisation engine turns such a family into a global diffeomorphism `A` with
  `A (fam 0 x) = fam 1 x = θ x` on a compact set;
* composing with the affine map `x ↦ θ ξ₀ + dθ(ξ₀)(x-ξ₀)` gives the required `Θ`.
-/

namespace Work.Drive.PushDisc

open Set Metric
open Filter MeasureTheory
open scoped Topology
open scoped ContDiff

variable {m : ℕ}
variable {ξ₀ : EuclideanSpace ℝ (Fin m)}

/-- The straight segment point `ξ₀ + (s·σ t)•(x - ξ₀)`, written out for readability. -/
noncomputable def seg (ξ₀ : EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (s : ℝ) : EuclideanSpace ℝ (Fin m) :=
  ξ₀ + (s * Real.smoothTransition t) • (x - ξ₀)

/-- The reparametrised family of `θ` along the segments from `ξ₀`: for `t > 0` it is
`x ↦ θ ξ₀ + (θ(ξ₀ + σ t·(x - ξ₀)) - θ ξ₀)/(σ t)`, and at `t = 0` it degenerates to the affine map
`x ↦ θ ξ₀ + dθ(ξ₀)(x - ξ₀)`.  The integral form below exhibits its joint smoothness. -/
noncomputable def fam (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  θ ξ₀ + ∫ s in (0 : ℝ)..1,
    β (seg ξ₀ t x s) • ((fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀))

/-- **The segment from `ξ₀` to `ξ₀ + λ(x - ξ₀)` stays close to `C`.**  If `C` is star-convex about
`ξ₀` and `c ∈ C` is a near point of `x`, then the point `ξ₀ + λ(x - ξ₀)` is within `λ·dist x c` of
`C`. -/
lemma infDist_segment_le {C : Set (EuclideanSpace ℝ (Fin m))}
    {ξ₀ c x : EuclideanSpace ℝ (Fin m)} (hC : StarConvex ℝ ξ₀ C) (hc : c ∈ C)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Metric.infDist (ξ₀ + a • (x - ξ₀)) C ≤ a * dist x c := by
  have hq : ξ₀ + a • (c - ξ₀) ∈ C := by
    have h := hC hc (show (0:ℝ) ≤ 1 - a by linarith) ha0 (show (1 - a) + a = 1 by ring)
    have heq : (1 - a) • ξ₀ + a • c = ξ₀ + a • (c - ξ₀) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rwa [heq] at h
  calc Metric.infDist (ξ₀ + a • (x - ξ₀)) C
      ≤ dist (ξ₀ + a • (x - ξ₀)) (ξ₀ + a • (c - ξ₀)) := Metric.infDist_le_dist_of_mem hq
    _ = ‖(ξ₀ + a • (x - ξ₀)) - (ξ₀ + a • (c - ξ₀))‖ := by rw [dist_eq_norm]
    _ = ‖a • (x - c)‖ := by
          rw [show (ξ₀ + a • (x - ξ₀)) - (ξ₀ + a • (c - ξ₀)) = a • (x - c) by
                simp only [smul_sub]; abel]
    _ = a * dist x c := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, dist_eq_norm]

/-- The integrand of `fam` is `C^∞` on all of `(ℝ × E) × ℝ`. -/
lemma fam_zero (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ) (hβ : β ξ₀ = 1)
    (x : EuclideanSpace ℝ (Fin m)) :
    fam θ ξ₀ β 0 x = θ ξ₀ + (fderiv ℝ θ ξ₀) (x - ξ₀) := by
  have hseg : ∀ s : ℝ, seg ξ₀ 0 x s = ξ₀ := by
    intro s
    simp [seg, Real.smoothTransition.zero]
  simp only [fam, hseg]
  rw [intervalIntegral.integral_const, sub_zero, one_smul, hβ, one_smul]
lemma bijective_fderiv_of_det_pos {θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin m)} (h : 0 < (fderiv ℝ θ y).toLinearMap.det) :
    Function.Bijective (fderiv ℝ θ y) := by
  have hdet : (fderiv ℝ θ y).toLinearMap.det ≠ 0 := ne_of_gt h
  have hker : (fderiv ℝ θ y).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hk)
  have hinj : Function.Injective (fderiv ℝ θ y).toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective (fderiv ℝ θ y).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  exact ⟨fun a b hab => hinj hab, fun b => hsurj b⟩

/-- **Every point of the segment `[ξ₀, x]` (parametrised as `seg ξ₀ t x s`) is within `r` of `C`**
when `x` is within `r` of `C`.  This is what makes the family `fam` well defined and smooth: the
whole segment stays inside any set containing `cthickening r C`. -/
lemma seg_mem_cthickening {C : Set (EuclideanSpace ℝ (Fin m))} (hC : StarConvex ℝ ξ₀ C)
    {x : EuclideanSpace ℝ (Fin m)} {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hx : x ∈ Metric.thickening r C) {t s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    seg ξ₀ t x s ∈ Metric.cthickening R C := by
  obtain ⟨c, hc, hxc⟩ := Metric.mem_thickening_iff.mp hx
  have hξC : ξ₀ ∈ C := hC.mem ⟨c, hc⟩
  have ha0 : 0 ≤ s * Real.smoothTransition t :=
    mul_nonneg hs.1 (Real.smoothTransition.nonneg t)
  have ha1 : s * Real.smoothTransition t ≤ 1 :=
    mul_le_one₀ hs.2 (Real.smoothTransition.nonneg t) (Real.smoothTransition.le_one t)
  have hdist : Metric.infDist (seg ξ₀ t x s) C ≤ s * Real.smoothTransition t * dist x c := by
    have h := infDist_segment_le (ξ₀ := ξ₀) (x := x) hC hc
      (a := s * Real.smoothTransition t) ha0 ha1
    simpa [seg] using h
  have hlt : Metric.infDist (seg ξ₀ t x s) C < R := by
    have h1 : s * Real.smoothTransition t * dist x c ≤ dist x c := by
      have h2 : s * Real.smoothTransition t * dist x c ≤ 1 * dist x c :=
        mul_le_mul_of_nonneg_right ha1 dist_nonneg
      simpa using h2
    linarith
  have hRpos : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt dist_nonneg hxc) hR
  have hmem : seg ξ₀ t x s ∈ Metric.thickening R C :=
    Metric.mem_thickening_iff_infDist_lt ⟨ξ₀, hξC⟩ |>.mpr hlt
  rw [← closure_thickening hRpos C]
  exact subset_closure hmem


/-- **The family at `t = 0` is the affine map `x ↦ θ ξ₀ + dθ(ξ₀)(x - ξ₀)`**, provided
`β ξ₀ = 1`. -/
lemma contDiff_integrand (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    {O V : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O) (hVO : closure V ⊆ O)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O)
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβV : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ =>
        β (seg ξ₀ q.1.1 q.1.2 q.2) •
          ((fderiv ℝ θ (seg ξ₀ q.1.1 q.1.2 q.2)) (q.1.2 - ξ₀))) := by
  have hseg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ => seg ξ₀ q.1.1 q.1.2 q.2) := by
    unfold seg; fun_prop
  have hUopen : IsOpen {q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ |
      seg ξ₀ q.1.1 q.1.2 q.2 ∈ O} := hO.preimage hseg.continuous
  have hfderiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ θ) O :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hO).mp hθ |>.2
  -- the evaluation factor
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ =>
        (fderiv ℝ θ (seg ξ₀ q.1.1 q.1.2 q.2)) (q.1.2 - ξ₀))
      {q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ | seg ξ₀ q.1.1 q.1.2 q.2 ∈ O} := by
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ =>
          (fderiv ℝ θ (seg ξ₀ q.1.1 q.1.2 q.2), q.1.2 - ξ₀))
        {q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ | seg ξ₀ q.1.1 q.1.2 q.2 ∈ O} :=
      (hfderiv.comp hseg.contDiffOn (fun q hq => hq)).prodMk
        ((contDiff_fst.snd.sub contDiff_const).contDiffOn)
    have hbil : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) ×
          EuclideanSpace ℝ (Fin m) => p.1 p.2) :=
      isBoundedBilinearMap_apply.contDiff
    exact hbil.contDiffOn.comp hpair (fun q _ => Set.mem_univ _)
  refine Work.Whitney.CutPush.contDiff_smul_of_tsupport (f := fun q : (ℝ ×
      EuclideanSpace ℝ (Fin m)) × ℝ => β (seg ξ₀ q.1.1 q.1.2 q.2)) (g := fun q =>
      (fderiv ℝ θ (seg ξ₀ q.1.1 q.1.2 q.2)) (q.1.2 - ξ₀))
    (U := {q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ | seg ξ₀ q.1.1 q.1.2 q.2 ∈ O})
    (hβ.comp hseg) hg hUopen ?_
  intro q hq
  have hsub : Function.support (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ =>
      β (seg ξ₀ q.1.1 q.1.2 q.2)) ⊆
      (fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ => seg ξ₀ q.1.1 q.1.2 q.2) ⁻¹' tsupport β :=
    fun q hq => subset_tsupport β hq
  exact (closure_mono hsub).trans ((closure_mono (Set.preimage_mono hβV)).trans
    ((hseg.continuous.closure_preimage_subset V).trans (Set.preimage_mono hVO))) hq

/-- **`fam` is jointly `C^∞`.** -/
lemma contDiff_fam_aux (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    {O V : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O) (hVO : closure V ⊆ O)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O)
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβV : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => fam θ ξ₀ β p.1 p.2) := by
  have h := Work.Drive.N2.contDiff_parametric_intervalIntegral
    (E := ℝ × EuclideanSpace ℝ (Fin m)) (F := EuclideanSpace ℝ (Fin m))
    (f := fun q : (ℝ × EuclideanSpace ℝ (Fin m)) × ℝ =>
      β (seg ξ₀ q.1.1 q.1.2 q.2) • ((fderiv ℝ θ (seg ξ₀ q.1.1 q.1.2 q.2)) (q.1.2 - ξ₀)))
    (a := (0:ℝ)) (b := 1) (contDiff_integrand θ ξ₀ β hO hVO hθ hβ hβV)
  simpa [fam] using (contDiff_const.add h)


/-- **The closed form of `fam` for positive `t`.**  Where `β ≡ 1` on the segments from `ξ₀` (and
those segments stay in `O`), `fam θ ξ₀ β t x = θ ξ₀ + (σ t)⁻¹ • (θ(ξ₀ + σ t • (x - ξ₀)) - θ ξ₀)`. -/
lemma fam_eqOn_aux (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    {O Ω : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O)
    {t : ℝ} (ht : 0 < t)
    (hβ1 : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, β (seg ξ₀ t x s) = 1)
    (hsegO : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, seg ξ₀ t x s ∈ O) :
    Set.EqOn (fun x => fam θ ξ₀ β t x)
      (fun x => θ ξ₀ + (Real.smoothTransition t)⁻¹ •
        (θ (ξ₀ + Real.smoothTransition t • (x - ξ₀)) - θ ξ₀)) Ω := by
  intro x hx
  set σ : ℝ := Real.smoothTransition t with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact Real.smoothTransition.pos_of_pos ht
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  let F : ℝ → EuclideanSpace ℝ (Fin m) :=
    fun u => (fderiv ℝ θ (ξ₀ + u • (x - ξ₀))) (x - ξ₀)
  have hmemO : ∀ u ∈ Set.Icc (0:ℝ) σ, ξ₀ + u • (x - ξ₀) ∈ O := by
    intro u hu
    have hs : u / σ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hu.1 hσpos.le, (div_le_one hσpos).mpr hu.2⟩
    have heq : ξ₀ + u • (x - ξ₀) = seg ξ₀ t x (u / σ) := by
      simp only [seg]
      rw [← hσdef, div_mul_cancel₀ u hσne]
    rw [heq]
    exact hsegO x hx (u / σ) hs
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) σ,
      HasDerivAt (fun u : ℝ => θ (ξ₀ + u • (x - ξ₀))) (F u) u := by
    intro u hu
    have huI : u ∈ Set.Icc (0:ℝ) σ := by rwa [Set.uIcc_of_le hσpos.le] at hu
    have hlin : HasDerivAt (fun u : ℝ => ξ₀ + u • (x - ξ₀)) (x - ξ₀) u := by
      have h1 : HasDerivAt (fun u : ℝ => u) (1:ℝ) u := hasDerivAt_id u
      simpa using (h1.smul_const (x - ξ₀)).const_add ξ₀
    have hfd : HasFDerivAt θ (fderiv ℝ θ (ξ₀ + u • (x - ξ₀))) (ξ₀ + u • (x - ξ₀)) :=
      ((hθ.contDiffAt (hO.mem_nhds (hmemO u huI))).differentiableAt (by simp)).hasFDerivAt
    exact hfd.comp_hasDerivAt u hlin
  have hint : IntervalIntegrable F volume (0:ℝ) σ := by
    refine ContinuousOn.intervalIntegrable ?_
    have hcont : ContinuousOn (fun u : ℝ => fderiv ℝ θ (ξ₀ + u • (x - ξ₀)))
        (Set.uIcc (0:ℝ) σ) := by
      have h1 : ContinuousOn (fun u : ℝ => ξ₀ + u • (x - ξ₀)) (Set.uIcc (0:ℝ) σ) := by fun_prop
      have h2 : ContinuousOn (fderiv ℝ θ) O := hθ.continuousOn_fderiv_of_isOpen hO (by simp)
      exact h2.comp h1 (fun u hu => hmemO u (by rwa [Set.uIcc_of_le hσpos.le] at hu))
    exact hcont.clm_apply continuousOn_const
  have hIntEq : ∫ s in (0:ℝ)..1, (fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀)
      = σ⁻¹ • (θ (ξ₀ + σ • (x - ξ₀)) - θ ξ₀) := by
    have hcongr : ∫ s in (0:ℝ)..1, (fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀)
        = ∫ s in (0:ℝ)..1, F (σ * s) := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [F, seg, ← hσdef, mul_comm]
    rw [hcongr, intervalIntegral.integral_comp_mul_left F hσne]
    simp only [mul_zero, mul_one]
    congr 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa using hFTC
  have hstep1 : ∫ s in (0:ℝ)..1,
        β (seg ξ₀ t x s) • ((fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀))
      = ∫ s in (0:ℝ)..1, (fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [hβ1 x hx s (by rwa [Set.uIcc_of_le zero_le_one] at hs), one_smul]
  change θ ξ₀ + ∫ s in (0:ℝ)..1,
      β (seg ξ₀ t x s) • ((fderiv ℝ θ (seg ξ₀ t x s)) (x - ξ₀))
    = θ ξ₀ + σ⁻¹ • (θ (ξ₀ + σ • (x - ξ₀)) - θ ξ₀)
  rw [hstep1, hIntEq]



/-- The derivative of `y ↦ y - ξ₀` is the identity. -/
lemma fderiv_self_sub_const (ξ₀ : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => y - ξ₀) x
      = (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
  rw [fderiv_sub_const, show (fun y : EuclideanSpace ℝ (Fin m) => y) = id from rfl, fderiv_id]
  rfl

/-- The derivative in `x` of the closed form `y ↦ θ ξ₀ + σ⁻¹ • (θ (ξ₀ + σ • (y - ξ₀)) - θ ξ₀)`. -/
lemma fderiv_closedForm (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : σ ≠ 0) {x : EuclideanSpace ℝ (Fin m)}
    (hθat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ (ξ₀ + σ • (x - ξ₀))) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) =>
        θ ξ₀ + σ⁻¹ • (θ (ξ₀ + σ • (y - ξ₀)) - θ ξ₀)) x
      = fderiv ℝ θ (ξ₀ + σ • (x - ξ₀)) := by
  have hdθ : DifferentiableAt ℝ θ (ξ₀ + σ • (x - ξ₀)) := hθat.differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin m) => ξ₀ + σ • (y - ξ₀)) x := by
    fun_prop
  have hdiff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ (Fin m) => θ (ξ₀ + σ • (y - ξ₀)) - θ ξ₀) x :=
    (hdθ.comp x hg).sub (differentiableAt_const _)
  rw [fderiv_const_add,
    show (fun y : EuclideanSpace ℝ (Fin m) => σ⁻¹ • (θ (ξ₀ + σ • (y - ξ₀)) - θ ξ₀))
      = σ⁻¹ • (fun y : EuclideanSpace ℝ (Fin m) => θ (ξ₀ + σ • (y - ξ₀)) - θ ξ₀) from rfl,
    fderiv_const_smul hdiff (σ⁻¹), fderiv_sub_const]
  have hcomp : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => θ (ξ₀ + σ • (y - ξ₀))) x
      = (fderiv ℝ θ (ξ₀ + σ • (x - ξ₀))).comp (σ • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m))) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin m) => θ (ξ₀ + σ • (y - ξ₀)))
        = θ ∘ (fun y : EuclideanSpace ℝ (Fin m) => ξ₀ + σ • (y - ξ₀)) from rfl,
      fderiv_comp x hdθ hg]
    congr 1
    rw [fderiv_const_add,
      show (fun y : EuclideanSpace ℝ (Fin m) => σ • (y - ξ₀))
        = σ • (fun y : EuclideanSpace ℝ (Fin m) => y - ξ₀) from rfl,
      fderiv_const_smul (by fun_prop : DifferentiableAt ℝ
        (fun y : EuclideanSpace ℝ (Fin m) => y - ξ₀) x) σ, fderiv_self_sub_const]
  rw [hcomp]
  rw [show (fderiv ℝ θ (ξ₀ + σ • (x - ξ₀))).comp
      (σ • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
      = σ • fderiv ℝ θ (ξ₀ + σ • (x - ξ₀)) from by
        ext v
        simp [ContinuousLinearMap.comp_apply]]
  rw [smul_smul, inv_mul_cancel₀ hσ, one_smul]

/-- **The derivative of `fam` in the space variable.** -/
lemma fam_fderiv (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    {O Ω : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O)
    {t : ℝ} (ht : 0 ≤ t)
    (hβ1 : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, β (seg ξ₀ t x s) = 1)
    (hsegO : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, seg ξ₀ t x s ∈ O)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ Ω) :
    fderiv ℝ (fun y => fam θ ξ₀ β t y) x
      = fderiv ℝ θ (ξ₀ + Real.smoothTransition t • (x - ξ₀)) := by
  rcases eq_or_lt_of_le ht with h0 | htpos
  · subst h0
    have hβ₀ : β ξ₀ = 1 := by
      have := hβ1 x hx 0 (Set.left_mem_Icc.mpr zero_le_one)
      simpa [seg, Real.smoothTransition.zero] using this
    have hfun : (fun y => fam θ ξ₀ β 0 y) =
        fun y => θ ξ₀ + (fderiv ℝ θ ξ₀) (y - ξ₀) := funext (fam_zero θ ξ₀ β hβ₀)
    rw [hfun]
    have haff : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) =>
        θ ξ₀ + (fderiv ℝ θ ξ₀) (y - ξ₀)) x = fderiv ℝ θ ξ₀ := by
      rw [fderiv_const_add,
        show (fun y : EuclideanSpace ℝ (Fin m) => (fderiv ℝ θ ξ₀) (y - ξ₀))
          = (fderiv ℝ θ ξ₀) ∘ (fun y : EuclideanSpace ℝ (Fin m) => y - ξ₀) from rfl,
        fderiv_comp x (fderiv ℝ θ ξ₀).differentiableAt (by fun_prop :
          DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin m) => y - ξ₀) x),
        fderiv_self_sub_const, ContinuousLinearMap.fderiv]
      ext v
      simp
    rw [haff]
    simp [Real.smoothTransition.zero]
  · have hσne : Real.smoothTransition t ≠ 0 := ne_of_gt (Real.smoothTransition.pos_of_pos htpos)
    have heq : (fun y => fam θ ξ₀ β t y) =ᶠ[𝓝 x]
        (fun y => θ ξ₀ + (Real.smoothTransition t)⁻¹ •
          (θ (ξ₀ + Real.smoothTransition t • (y - ξ₀)) - θ ξ₀)) :=
      Filter.eventually_of_mem (hΩ.mem_nhds hx)
        (fun y hy => fam_eqOn_aux θ ξ₀ β hO hθ htpos hβ1 hsegO hy)
    rw [heq.fderiv_eq]
    have hmem : ξ₀ + Real.smoothTransition t • (x - ξ₀) ∈ O := by
      have := hsegO x hx 1 (Set.right_mem_Icc.mpr zero_le_one)
      simpa [seg] using this
    have hθat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ
        (ξ₀ + Real.smoothTransition t • (x - ξ₀)) :=
      hθ.contDiffAt (hO.mem_nhds hmem)
    exact fderiv_closedForm θ ξ₀ hσne hθat

/-- **`fam` is injective on `Ω` for `t ∈ [0,1]`.** -/
lemma fam_injOn (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (β : EuclideanSpace ℝ (Fin m) → ℝ)
    {O Ω : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O)
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O) (hθinj : Set.InjOn θ O)
    (hdet : 0 < (fderiv ℝ θ ξ₀).toLinearMap.det)
    {t : ℝ} (ht : 0 ≤ t)
    (hβ1 : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, β (seg ξ₀ t x s) = 1)
    (hsegO : ∀ x ∈ Ω, ∀ s ∈ Set.Icc (0:ℝ) 1, seg ξ₀ t x s ∈ O) :
    Set.InjOn (fun x => fam θ ξ₀ β t x) Ω := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le ht with h0 | htpos
  · subst h0
    have hβ₀ : β ξ₀ = 1 := by
      have := hβ1 x hx 0 (Set.left_mem_Icc.mpr zero_le_one)
      simpa [seg, Real.smoothTransition.zero] using this
    change fam θ ξ₀ β 0 x = fam θ ξ₀ β 0 y at hxy
    rw [fam_zero θ ξ₀ β hβ₀ x, fam_zero θ ξ₀ β hβ₀ y] at hxy
    exact sub_left_inj.mp ((bijective_fderiv_of_det_pos hdet).1 (add_left_cancel hxy))
  · have hσne : Real.smoothTransition t ≠ 0 := ne_of_gt (Real.smoothTransition.pos_of_pos htpos)
    have h1 : θ (ξ₀ + Real.smoothTransition t • (x - ξ₀))
        = θ (ξ₀ + Real.smoothTransition t • (y - ξ₀)) := by
      have hx' := fam_eqOn_aux θ ξ₀ β hO hθ htpos hβ1 hsegO hx
      have hy' := fam_eqOn_aux θ ξ₀ β hO hθ htpos hβ1 hsegO hy
      rw [hx', hy'] at hxy
      exact sub_left_inj.mp (smul_right_injective _ (inv_ne_zero hσne) (add_left_cancel hxy))
    have hxO : ξ₀ + Real.smoothTransition t • (x - ξ₀) ∈ O := by
      have := hsegO x hx 1 (Set.right_mem_Icc.mpr zero_le_one); simpa [seg] using this
    have hyO : ξ₀ + Real.smoothTransition t • (y - ξ₀) ∈ O := by
      have := hsegO y hy 1 (Set.right_mem_Icc.mpr zero_le_one); simpa [seg] using this
    have h3 := smul_right_injective _ hσne (add_left_cancel (hθinj hxO hyO h1))
    exact sub_left_inj.mp h3

theorem exists_globalDiffeo_of_embedding {m : ℕ}
    (ξ₀ : EuclideanSpace ℝ (Fin m)) (C : Set (EuclideanSpace ℝ (Fin m)))
    (hC : IsCompact C) (hCstar : StarConvex ℝ ξ₀ C)
    (O : Set (EuclideanSpace ℝ (Fin m))) (hO : IsOpen O) (hCO : C ⊆ O)
    (θ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hθ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ O)
    (hθinj : Set.InjOn θ O)
    (hθdet : ∀ ξ ∈ O, 0 < (fderiv ℝ θ ξ).toLinearMap.det) :
    ∃ Θ Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      Function.LeftInverse Φ Θ ∧ Function.RightInverse Φ Θ ∧
      ∃ O' : Set (EuclideanSpace ℝ (Fin m)), IsOpen O' ∧ C ⊆ O' ∧ O' ⊆ O ∧
        ∀ ξ ∈ O', Θ ξ = θ ξ := by
  classical
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · subst hC0
    exact ⟨id, id, contDiff_id, contDiff_id, fun x => rfl, fun x => rfl, ∅, isOpen_empty,
      Set.empty_subset _, Set.empty_subset _, fun ξ hξ => absurd hξ (Set.notMem_empty ξ)⟩
  · have hξC : ξ₀ ∈ C := hCstar.mem hCne
    have hξO : ξ₀ ∈ O := hCO hξC
    obtain ⟨δ, hδpos, hδsub⟩ := hC.exists_cthickening_subset_open hO hCO
    -- the cutoff bump
    have hsub₀ : Metric.cthickening (δ/2) C ⊆ Metric.thickening (3*δ/4) C := by
      have hδhalf : (0:ℝ) ≤ δ/2 := by linarith
      obtain ⟨ε, hε⟩ : ∃ ε : NNReal, (ε : ℝ) = δ/2 := ⟨⟨δ/2, hδhalf⟩, rfl⟩
      have hlt : (ε : ℝ) < 3*δ/4 := by rw [hε]; linarith
      have h' := Metric.cthickening_subset_thickening (δ₁ := ε) (δ₂ := 3*δ/4) hlt C
      rwa [hε] at h'
    obtain ⟨β, hβsm, _hβnn, ⟨δβ, hδβpos, hβone⟩, hβsupp, _hβcs⟩ :=
      exists_contDiff_bump_compact (Metric.cthickening (δ/2) C) (hC.cthickening)
        (Metric.thickening (3*δ/4) C) Metric.isOpen_thickening hsub₀
    -- the geometric sets
    set Ω : Set (EuclideanSpace ℝ (Fin m)) := Metric.thickening (δ/4) C with hΩdef
    set K : Set (EuclideanSpace ℝ (Fin m)) := Metric.cthickening (δ/8) C with hKdef
    set Op : Set (EuclideanSpace ℝ (Fin m)) := Metric.thickening (δ/8) C with hOpdef
    set Vb : Set (EuclideanSpace ℝ (Fin m)) := Metric.thickening (3*δ/4) C with hVbdef
    have hΩopen : IsOpen Ω := by rw [hΩdef]; exact Metric.isOpen_thickening
    have hKcompact : IsCompact K := by rw [hKdef]; exact hC.cthickening
    have hKΩ : K ⊆ Ω := by
      have hδ8 : (0:ℝ) ≤ δ/8 := by linarith
      obtain ⟨ε, hε⟩ : ∃ ε : NNReal, (ε : ℝ) = δ/8 := ⟨⟨δ/8, hδ8⟩, rfl⟩
      have hlt : (ε : ℝ) < δ/4 := by rw [hε]; linarith
      have h' := Metric.cthickening_subset_thickening (δ₁ := ε) (δ₂ := δ/4) hlt C
      rw [hε] at h'
      rw [hKdef, hΩdef]
      exact h'
    have hOpopen : IsOpen Op := by rw [hOpdef]; exact Metric.isOpen_thickening
    have hCOp : C ⊆ Op := by
      rw [hOpdef]
      exact fun x hx => Metric.self_subset_thickening (by linarith : (0:ℝ) < δ/8) C hx
    have hOpO : Op ⊆ O := by
      rw [hOpdef]
      exact (Metric.thickening_subset_cthickening (δ/8) C).trans
        ((Metric.cthickening_mono (by linarith) C).trans hδsub)
    have hOpK : Op ⊆ K := by
      rw [hOpdef, hKdef]; exact Metric.thickening_subset_cthickening (δ/8) C
    have hVO : closure Vb ⊆ O := by
      rw [hVbdef, closure_thickening (by linarith : (0:ℝ) < 3*δ/4) C]
      exact (Metric.cthickening_mono (by linarith) C).trans hδsub
    have hβVb : tsupport β ⊆ Vb := by rw [hVbdef]; exact hβsupp
    -- the two geometric rows for the family
    have hsegO : ∀ (t : ℝ) x, x ∈ Ω → ∀ s ∈ Set.Icc (0:ℝ) 1, seg ξ₀ t x s ∈ O := by
      intro t x hx s hs
      refine hδsub (seg_mem_cthickening hCstar (r := δ/4) (R := δ) (by linarith) (by linarith) ?_ hs)
      rw [hΩdef] at hx; exact hx
    have hβ1 : ∀ (t : ℝ) x, x ∈ Ω → ∀ s ∈ Set.Icc (0:ℝ) 1, β (seg ξ₀ t x s) = 1 := by
      intro t x hx s hs
      refine hβone _ (Metric.self_subset_thickening hδβpos _ ?_)
      refine seg_mem_cthickening hCstar (r := δ/4) (R := δ/2) (by linarith) (by linarith) ?_ hs
      rw [hΩdef] at hx; exact hx
    have hβ₀ : β ξ₀ = 1 := by
      refine hβone _ (Metric.self_subset_thickening hδβpos _ ?_)
      exact Metric.thickening_subset_cthickening (δ/2) C
        (Metric.self_subset_thickening (by linarith : (0:ℝ) < δ/2) C hξC)
    have hfam0 : ∀ x : EuclideanSpace ℝ (Fin m),
        fam θ ξ₀ β 0 x = θ ξ₀ + (fderiv ℝ θ ξ₀) (x - ξ₀) := fam_zero θ ξ₀ β hβ₀
    have hfam1 : ∀ x ∈ Op, fam θ ξ₀ β 1 x = θ x := by
      intro x hx
      have h := fam_eqOn_aux (t := 1) θ ξ₀ β hO hθ one_pos (hβ1 1) (hsegO 1)
        (Metric.thickening_mono (δ₁ := δ/8) (by linarith) C (by rw [hOpdef] at hx; exact hx))
      have h' : fam θ ξ₀ β 1 x = θ ξ₀ + (Real.smoothTransition 1)⁻¹ •
          (θ (ξ₀ + Real.smoothTransition 1 • (x - ξ₀)) - θ ξ₀) := h
      rw [h', Real.smoothTransition.one]
      simp
    -- ## the local inverse data at each point of the compact trail
    have hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin m) => fam θ ξ₀ β q.1 q.2) :=
      contDiff_fam_aux θ ξ₀ β hO hVO hθ hβsm hβVb
    have hpt : ∀ p : ↥(Set.Icc (0:ℝ) 1 ×ˢ K),
        ∃ (Ob : Set ℝ) (Ub : Set (EuclideanSpace ℝ (Fin m)))
          (Wb : Set (EuclideanSpace ℝ (Fin m)))
          (par : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
          IsOpen Ob ∧ (p : ℝ × EuclideanSpace ℝ (Fin m)).1 ∈ Ob ∧ IsOpen Ub ∧
          (p : ℝ × EuclideanSpace ℝ (Fin m)).2 ∈ Ub ∧ Ub ⊆ Ω ∧ IsOpen Wb ∧
          fam θ ξ₀ β (p : ℝ × EuclideanSpace ℝ (Fin m)).1
            (p : ℝ × EuclideanSpace ℝ (Fin m)).2 ∈ Wb ∧
          ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry par) (Ob ×ˢ Wb) ∧
          (∀ s ∈ Ob, ∀ z ∈ Wb, par s z ∈ Ub ∧ fam θ ξ₀ β s (par s z) = z) := by
      intro p
      obtain ⟨hp1, hp2⟩ := p.2
      have hxp : (p : ℝ × EuclideanSpace ℝ (Fin m)).2 ∈ Ω := hKΩ hp2
      have hmem : ξ₀ + Real.smoothTransition (p : ℝ × EuclideanSpace ℝ (Fin m)).1 •
          ((p : ℝ × EuclideanSpace ℝ (Fin m)).2 - ξ₀) ∈ O := by
        have h := hsegO (p : ℝ × EuclideanSpace ℝ (Fin m)).1 (p : ℝ × EuclideanSpace ℝ (Fin m)).2
          hxp 1 (Set.right_mem_Icc.mpr zero_le_one)
        simpa [seg] using h
      have hbij : Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => fam θ ξ₀ β q.1 q.2)
            ((p : ℝ × EuclideanSpace ℝ (Fin m)).1, (p : ℝ × EuclideanSpace ℝ (Fin m)).2)
            (0, v)) := by
        have heq : (fun v : EuclideanSpace ℝ (Fin m) =>
            fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => fam θ ξ₀ β q.1 q.2)
              ((p : ℝ × EuclideanSpace ℝ (Fin m)).1, (p : ℝ × EuclideanSpace ℝ (Fin m)).2)
              (0, v))
            = fun v => fderiv ℝ (fun y => fam θ ξ₀ β (p : ℝ × EuclideanSpace ℝ (Fin m)).1 y)
                (p : ℝ × EuclideanSpace ℝ (Fin m)).2 v := by
          funext v
          exact fderiv_uncurry_snd _
            ((hGsm.differentiable (by simp)).differentiableAt) v
        rw [heq, fam_fderiv θ ξ₀ β hO hΩopen hθ hp1.1 (hβ1 _) (hsegO _) hxp]
        exact bijective_fderiv_of_det_pos (hθdet _ hmem)
      obtain ⟨Ob, Ub, Wb, par, hOb, hmp1, hUb, hmp2, hUbΩ, hWb, hmpW, hparsm, _hparL, hparR⟩ :=
        localInverseFamilyTwoSided_repair
          (fun q : ℝ × EuclideanSpace ℝ (Fin m) => fam θ ξ₀ β q.1 q.2)
          Set.univ isOpen_univ (p : ℝ × EuclideanSpace ℝ (Fin m)).1
          (p : ℝ × EuclideanSpace ℝ (Fin m)).2 (Set.mem_univ _)
          (hGsm.contDiffOn (s := Set.univ)) hbij Ω hΩopen hxp
      exact ⟨Ob, Ub, Wb, par, hOb, hmp1, hUb, hmp2, hUbΩ, hWb, hmpW, hparsm, hparR⟩
    choose Ob Ub Wb par hOb hmp1 hUb hmp2 hUbΩ hWb hmpW hparsm hparR using hpt
    -- ## finite cover of the trail
    set cover : ↥(Set.Icc (0:ℝ) 1 ×ˢ K) → Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
      fun p => {q | q.1 ∈ Ob p ∧ fam θ ξ₀ β q.1 q.2 ∈ Wb p} with hcoverdef
    have hcoveropen : ∀ p, IsOpen (cover p) := by
      intro p
      have h1 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin m) | q.1 ∈ Ob p} :=
        (hOb p).preimage continuous_fst
      have h2 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin m) | fam θ ξ₀ β q.1 q.2 ∈ Wb p} :=
        (hWb p).preimage hGsm.continuous
      exact h1.inter h2
    have hcoversub : (Set.Icc (0:ℝ) 1 ×ˢ K) ⊆ ⋃ p, cover p := by
      rintro ⟨lam, y⟩ ⟨hlam, hy⟩
      refine Set.mem_iUnion.mpr ⟨⟨(lam, y), ⟨hlam, hy⟩⟩, ?_⟩
      exact ⟨hmp1 _, hmpW _⟩
    obtain ⟨s, hs⟩ := (isCompact_Icc.prod hKcompact).elim_finite_subcover cover hcoveropen hcoversub
    -- ## the engine
    obtain ⟨A, Ainv, hAsm, hAinvsm, hleft, hright, _hoff, hagree⟩ :=
      exists_diffeo_of_localFamily_compact (fun t x => fam θ ξ₀ β t x) K hKcompact Set.univ
        isOpen_univ hGsm (fun lam hlam y hy => Set.mem_univ _) Ω hΩopen hKΩ
        (fun lam hlam => fam_injOn θ ξ₀ β hO hθ hθinj (hθdet ξ₀ hξO) hlam.1 (hβ1 lam) (hsegO lam))
        (ι := ↥s) (fun j => Ob j) (fun j => Ub j) (fun j => Wb j) (fun j => par j)
        (fun j => hOb j) (fun j => hUb j) (fun j => hWb j) (fun j => hUbΩ j)
        (fun j => hparsm j) (fun j => hparR j)
        (by
          intro lam hlam y hy
          have hmem : (lam, y) ∈ ⋃ p ∈ s, cover p := hs ⟨hlam, hy⟩
          rcases Set.mem_iUnion.mp hmem with ⟨p, hp⟩
          rcases Set.mem_iUnion.mp hp with ⟨hps, hpc⟩
          exact ⟨⟨p, hps⟩, hpc.1, hpc.2⟩)
    -- ## the affine map and its inverse
    have hbij₀ : Function.Bijective (fderiv ℝ θ ξ₀) := bijective_fderiv_of_det_pos (hθdet ξ₀ hξO)
    let L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
      ContinuousLinearEquiv.ofBijective (fderiv ℝ θ ξ₀)
        (LinearMap.ker_eq_bot.mpr hbij₀.1) (LinearMap.range_eq_top.mpr hbij₀.2)
    have hLcoe : (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        = fderiv ℝ θ ξ₀ := ContinuousLinearEquiv.coe_ofBijective _ _ _
    refine ⟨fun x => A (θ ξ₀ + (fderiv ℝ θ ξ₀) (x - ξ₀)),
      fun z => ξ₀ + (L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        (Ainv z - θ ξ₀), ?_, ?_, ?_, ?_, Op, hOpopen, hCOp, hOpO, ?_⟩
    · exact hAsm.comp ((contDiff_const.add
        ((fderiv ℝ θ ξ₀).contDiff.comp (contDiff_id.sub contDiff_const))))
    · exact (contDiff_const.add
        ((L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)).contDiff.comp
          (hAinvsm.sub contDiff_const)))
    · intro x
      dsimp only
      rw [hleft (θ ξ₀ + (fderiv ℝ θ ξ₀) (x - ξ₀))]
      simp only [add_sub_cancel_left]
      rw [← hLcoe]
      rw [show (L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
          ((L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (x - ξ₀)) = x - ξ₀
        from ContinuousLinearEquiv.symm_apply_apply L (x - ξ₀)]
      abel
    · intro z
      dsimp only
      rw [show ξ₀ + (L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        (Ainv z - θ ξ₀) - ξ₀ = (L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m)) (Ainv z - θ ξ₀) by abel]
      rw [← hLcoe]
      rw [show (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
          ((L.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
            (Ainv z - θ ξ₀)) = Ainv z - θ ξ₀
        from ContinuousLinearEquiv.apply_symm_apply L (Ainv z - θ ξ₀)]
      rw [show θ ξ₀ + (Ainv z - θ ξ₀) = Ainv z by abel]
      exact hright z
    · intro ξ hξOp
      have hξK : ξ ∈ K := hOpK hξOp
      have h1 : A (fam θ ξ₀ β 0 ξ) = fam θ ξ₀ β 1 ξ := hagree ξ hξK
      dsimp only
      rw [← hfam0 ξ, h1]
      exact hfam1 ξ hξOp
end Work.Drive.PushDisc
