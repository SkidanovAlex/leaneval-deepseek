import Mathlib
import Submission.Work.Cofibre.HopfSetup

open scoped Topology
open Filter

namespace Work.Cofibre

open Submission.Cofibre
open Submission.Sphere

noncomputable section

/-- A bounded (indeed norm-one) function times a scalar that vanishes at a point is continuous at
that point: the scalar factor forces the product to tend to `0`. -/
lemma continuousAt_smul_of_norm_eq_one {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → ℝ} {g : X → E} {x : X}
    (hf : ContinuousAt f x) (hg : ∀ y, ‖g y‖ = 1) (hfx : f x = 0) :
    ContinuousAt (fun y => f y • g y) x := by
  change Tendsto (fun y => f y • g y) (𝓝 x) (𝓝 (f x • g x))
  rw [hfx, zero_smul]
  refine squeeze_zero_norm' (a := fun y => ‖f y‖) (Eventually.of_forall (fun y => ?_)) ?_
  · rw [norm_smul, hg y, mul_one]
  · have h : Tendsto (fun y => ‖f y‖) (𝓝 x) (𝓝 ‖f x‖) := hf.norm
    simpa [hfx] using h

/-- The norm of `μ` applied to two normalised vectors is one (it lands on the unit sphere). -/
lemma norm_muSphere (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d)) (u v : Euc d) :
    ‖(μ (sphVec d u, sphVec d v) : Euc d)‖ = 1 := by
  have h := Metric.mem_sphere.mp (μ (sphVec d u, sphVec d v)).2
  rwa [dist_eq_norm, sub_zero] at h

/-- `unitVec` is continuous away from the origin. -/
lemma continuousOn_unitVec (d : ℕ) :
    ContinuousOn (unitVec d) {v : Euc d | v ≠ 0} := by
  have h : unitVec d = fun v : Euc d => ‖v‖⁻¹ • v := rfl
  rw [h]
  exact (continuous_norm.continuousOn.inv₀ (fun v hv => norm_ne_zero_iff.mpr hv)).smul
    continuousOn_id

/-- `sphVec` is continuous away from the origin. -/
lemma continuousOn_sphVec (d : ℕ) :
    ContinuousOn (sphVec d) {v : Euc d | v ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hp : ∀ x : {v : Euc d // v ≠ 0},
      unitVec d (x : Euc d) ∈ Metric.sphere (0 : Euc d) 1 := fun x => by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_unitVec d x.2
  have hΦ : Continuous (fun x : {v : Euc d // v ≠ 0} =>
      (⟨unitVec d (x : Euc d), hp x⟩ : ↥(Metric.sphere (0 : Euc d) 1))) :=
    Continuous.subtype_mk (continuousOn_unitVec d).domRestrict hp
  have heq : {v : Euc d | v ≠ 0}.domRestrict (sphVec d) =
      (fun x : {v : Euc d // v ≠ 0} =>
        (⟨unitVec d (x : Euc d), hp x⟩ : ↥(Metric.sphere (0 : Euc d) 1))) := by
    funext x
    show sphVec d (x : Euc d) = _
    rw [sphVec, dif_neg x.2]
  rw [heq]
  exact hΦ

/-- `sphVec` is continuous at every nonzero vector. -/
lemma continuousAt_sphVec (d : ℕ) {v : Euc d} (hv : v ≠ 0) :
    ContinuousAt (sphVec d) v :=
  (continuousOn_sphVec d).continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hv))

/-- The raw Hopf formula `(u,v) ↦ 2‖u‖‖v‖ · μ(û, v̂)`, as a function on `Euc d × Euc d`. -/
lemma continuous_hopfProduct (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d)) :
    Continuous (fun p : Euc d × Euc d =>
      (2 * ‖p.1‖ * ‖p.2‖) • (μ (sphVec d p.1, sphVec d p.2) : Euc d)) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 2 * ‖p.1‖ * ‖p.2‖ = 0
  · refine continuousAt_smul_of_norm_eq_one
      (f := fun q : Euc d × Euc d => 2 * ‖q.1‖ * ‖q.2‖)
      (g := fun q : Euc d × Euc d => (μ (sphVec d q.1, sphVec d q.2) : Euc d)) ?_ ?_ hp
    · exact (continuousAt_const.mul continuous_fst.continuousAt.norm).mul
        continuous_snd.continuousAt.norm
    · intro q
      exact norm_muSphere d μ q.1 q.2
  · have h1 : p.1 ≠ 0 := by
      intro h; exact hp (by rw [h]; simp)
    have h2 : p.2 ≠ 0 := by
      intro h; exact hp (by rw [h]; simp)
    have hg : ContinuousAt (fun q : Euc d × Euc d =>
        (μ (sphVec d q.1, sphVec d q.2) : Euc d)) p := by
      have hpair : ContinuousAt (fun q : Euc d × Euc d => (sphVec d q.1, sphVec d q.2)) p :=
        ((continuousAt_sphVec d h1).comp continuous_fst.continuousAt).prodMk
          ((continuousAt_sphVec d h2).comp continuous_snd.continuousAt)
      exact continuous_subtype_val.continuousAt.comp (μ.continuous.continuousAt.comp hpair)
    have hf : ContinuousAt (fun q : Euc d × Euc d => 2 * ‖q.1‖ * ‖q.2‖) p :=
      (continuousAt_const.mul continuous_fst.continuousAt.norm).mul
        continuous_snd.continuousAt.norm
    exact hf.smul hg

/-- The first coordinate of the Hopf construction is continuous. -/
lemma continuous_hopfFst (d : ℕ) (μ : ContinuousMap (Sph d × Sph d) (Sph d)) :
    Continuous (hopfFst d μ) := by
  have hfst : Continuous (fun x : WithLp 2 (Euc d × Euc d) => x.fst) :=
    WithLp.continuous_fst 2 (Euc d) (Euc d)
  have hsnd : Continuous (fun x : WithLp 2 (Euc d × Euc d) => x.snd) :=
    WithLp.continuous_snd 2 (Euc d) (Euc d)
  have hφ : Continuous (fun x : WithLp 2 (Euc d × Euc d) => (x.fst, x.snd)) :=
    hfst.prodMk hsnd
  have hF := (continuous_hopfProduct d μ).comp hφ
  convert hF using 1
  funext x
  simp only [hopfFst, muSph, Function.comp_apply]

/-- The second coordinate of the Hopf construction is continuous. -/
lemma continuous_hopfSnd (d : ℕ) : Continuous (hopfSnd d) := by
  have h1 : Continuous (fun x : WithLp 2 (Euc d × Euc d) => ‖x.snd‖ ^ 2) :=
    (WithLp.continuous_snd 2 (Euc d) (Euc d)).norm.pow 2
  have h2 : Continuous (fun x : WithLp 2 (Euc d × Euc d) => ‖x.fst‖ ^ 2) :=
    (WithLp.continuous_fst 2 (Euc d) (Euc d)).norm.pow 2
  convert h1.sub h2 using 1
  funext x
  simp only [hopfSnd, Pi.sub_apply]

theorem continuous_hopfRaw (d : ℕ)
    (μ : ContinuousMap (Submission.Sphere.Sph d × Submission.Sphere.Sph d)
      (Submission.Sphere.Sph d)) :
    Continuous (Submission.Cofibre.hopfRaw d μ) := by
  have hpair : Continuous
      (fun x : WithLp 2 (Euc d × Euc d) => (hopfFst d μ x, hopfSnd d x)) :=
    (continuous_hopfFst d μ).prodMk (continuous_hopfSnd d)
  have htoLp : Continuous (WithLp.toLp 2 : Euc d × ℝ → WithLp 2 (Euc d × ℝ)) :=
    WithLp.prod_continuous_toLp 2 (Euc d) ℝ
  have h := htoLp.comp hpair
  convert h using 1
  funext x
  simp only [hopfRaw, Function.comp_apply]

end

end Work.Cofibre
