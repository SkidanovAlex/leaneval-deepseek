import Mathlib
import Submission.Work.RPCore.Port.PushDisc.conicalFluxMachinery
import Submission.Work.RPCore.Port.PushDisc.conicalFamilies
import Submission.Work.RPCore.Port.PushDisc.smoothObstruction
import Submission.Work.RPCore.Port.PushDisc.exists_smooth_avoiding_homotopy_general

/-!
# The degree function on a sphere

The homotopy relation on self-maps of `E = EuclideanSpace ℝ (Fin d)` (the relation occurring in
`Work.RPCore.Port.PushDisc.SphereDegree`), its basic properties (symmetry, transitivity, collapse of the
reflexive-transitive closure), and the resulting `ℤ`-valued degree function.  On the *even* spheres
(odd `d`) the identity and the antipodal map are not homotopic, which makes the two special cases of
the degree function mutually exclusive.
-/

namespace Work.RPCore.Port.PushDisc

open scoped Matrix Topology
open MeasureTheory Filter
open Classical

/-- The radial extension of a time-dependent family, `p ↦ ‖p.2‖ • F (p.1, p.2/‖p.2‖)`.  It agrees
with `F` on the unit sphere and is bounded by `‖p.2‖` whenever `F` is sphere-valued on the sphere.
Its use is that two homotopies of sphere-valued maps that agree at a time also agree *everywhere*
after radial extension, which makes the concatenation of homotopies continuous on all of
`ℝ × E` — this is what makes the homotopy relation transitive. -/
noncomputable def radExt {d : ℕ}
    (F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℝ × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ‖p.2‖ • F (p.1, unitize p.2)

lemma norm_radExt_le {d : ℕ} {F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hs : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖F (t, x)‖ = 1)
    (p : ℝ × EuclideanSpace ℝ (Fin d)) : ‖radExt F p‖ ≤ ‖p.2‖ := by
  rw [radExt, norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
  rcases eq_or_ne p.2 0 with h | h
  · rw [h, norm_zero, zero_mul]
  · rw [hs p.1 (unitize p.2) (norm_unitize h), mul_one]

lemma radExt_of_norm_one {d : ℕ} (F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ = 1) (t : ℝ) : radExt F (t, y) = F (t, y) := by
  rw [radExt, hy, unitize_of_norm_one hy, one_smul]

lemma continuous_radExt {d : ℕ} {F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hF : Continuous F)
    (hs : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖F (t, x)‖ = 1) :
    Continuous (radExt F) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_ne p.2 0 with h | h
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun q hq => ?_⟩
    have h1 : ‖radExt F q‖ ≤ ‖q.2‖ := norm_radExt_le hs q
    have h2 : radExt F p = 0 := by rw [radExt, h, norm_zero, zero_smul]
    rw [dist_eq_norm, h2, sub_zero]
    calc ‖radExt F q‖ ≤ ‖q.2‖ := h1
      _ = ‖q.2 - p.2‖ := by rw [h, sub_zero]
      _ ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε := hq
  · have hopen : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} :=
      isOpen_compl_singleton.preimage continuous_snd
    have hunit : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => unitize q.2)
        {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} := by
      have h1 : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (‖q.2‖)⁻¹)
          {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} := by
        refine ContinuousOn.inv₀ ((continuous_norm.comp continuous_snd).continuousOn) ?_
        intro q hq
        exact norm_ne_zero_iff.mpr hq
      have := h1.smul continuous_snd.continuousOn
      have hfun : (fun q : ℝ × EuclideanSpace ℝ (Fin d) => unitize q.2)
          = (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (‖q.2‖)⁻¹) •
            fun q : ℝ × EuclideanSpace ℝ (Fin d) => q.2 := rfl
      rw [hfun]
      exact this
    have hpair : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (q.1, unitize q.2))
        {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} :=
      continuousOn_fst.prodMk hunit
    have hcomp : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => F (q.1, unitize q.2))
        {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} :=
      (by simpa only [Function.comp_def] using hF.comp_continuousOn hpair)
    have hn : ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin d) => ‖q.2‖)
        {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} :=
      (continuous_norm.comp continuous_snd).continuousOn
    have := hn.smul hcomp
    have hfun : radExt F = fun q : ℝ × EuclideanSpace ℝ (Fin d) => ‖q.2‖ • F (q.1, unitize q.2) := rfl
    rw [hfun]
    exact (this.continuousAt (hopen.mem_nhds h))

/-- Two self-maps of the unit sphere of `E` are homotopic when they are the two end slices of a
continuous sphere-valued homotopy.  This is exactly the relation occurring in
`Work.RPCore.Port.PushDisc.SphereDegree`. -/
def sphHomotopic {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    Continuous F ∧
    (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (0, x) = f x) ∧
    (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (1, x) = g x) ∧
    (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖F (t, x)‖ = 1)

/-- The antipodal self-map. -/
def negMap {d : ℕ} : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => -x

lemma sphHomotopic_symm {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : sphHomotopic f g) : sphHomotopic g f := by
  obtain ⟨F, hF, h0, h1, hs⟩ := h
  exact ⟨fun p => F (1 - p.1, p.2),
    hF.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd),
    fun x => by simpa using h1 x, fun x => by simpa using h0 x, fun t x hx => by simpa using hs _ x hx⟩

lemma sphHomotopic_trans {d : ℕ} {f g h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h₁ : sphHomotopic f g) (h₂ : sphHomotopic g h) : sphHomotopic f h := by
  obtain ⟨K, hK, hK0, hK1, hKs⟩ := h₁
  obtain ⟨L, hL, hL0, hL1, hLs⟩ := h₂
  refine ⟨fun p => if p.1 ≤ 1 / 2 then radExt K (2 * p.1, p.2) else radExt L (2 * p.1 - 1, p.2),
    ?_, ?_, ?_, ?_⟩
  · refine Continuous.if_le
      ((continuous_radExt hK hKs).comp
        ((continuous_const.mul continuous_fst).prodMk continuous_snd))
      ((continuous_radExt hL hLs).comp
        (((continuous_const.mul continuous_fst).sub continuous_const).prodMk continuous_snd))
      continuous_fst continuous_const ?_
    intro p hp
    have h1 : 2 * p.1 = 1 := by rw [hp]; norm_num
    have h0 : 2 * p.1 - 1 = (0 : ℝ) := by rw [hp]; norm_num
    rw [h0, h1]
    rcases eq_or_ne p.2 0 with hy | hy
    · rw [hy, radExt, radExt, norm_zero, zero_smul, zero_smul]
    · rw [radExt, radExt, hK1 (unitize p.2) (norm_unitize hy), hL0 (unitize p.2) (norm_unitize hy)]
  · intro x hx
    simp only [mul_zero, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [radExt_of_norm_one K hx 0]
    exact hK0 x hx
  · intro x hx
    have h2 : 2 * (1 : ℝ) - 1 = 1 := by norm_num
    simp only [h2, if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2))]
    rw [radExt_of_norm_one L hx 1]
    exact hL1 x hx
  · intro t x hx
    by_cases ht : t ≤ 1 / 2
    · simp only [if_pos ht]
      rw [radExt_of_norm_one K hx (2 * t)]
      exact hKs (2 * t) x hx
    · simp only [if_neg ht]
      rw [radExt_of_norm_one L hx (2 * t - 1)]
      exact hLs (2 * t - 1) x hx

lemma sph_transGen_collapse {d : ℕ} {a b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : Relation.TransGen sphHomotopic a b) : sphHomotopic a b := by
  induction h with
  | single hab => exact hab
  | tail _ hbc ih => exact sphHomotopic_trans ih hbc

lemma sph_reflTransGen_eq_or {d : ℕ} {a b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : Relation.ReflTransGen sphHomotopic a b) : a = b ∨ sphHomotopic a b := by
  rcases (Relation.reflTransGen_iff_eq_or_transGen.mp h) with hba | htrans
  · exact Or.inl hba.symm
  · exact Or.inr (sph_transGen_collapse htrans)

/-- The antipodal map is not the identity (on a nontrivial space). -/
lemma negMap_ne_id {d : ℕ} (hd : 1 ≤ d) :
    (negMap : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ≠ id := by
  intro h
  have h1 := congrFun h (stdV ⟨0, hd⟩ : EuclideanSpace ℝ (Fin d))
  have h2 := congrArg (fun y : EuclideanSpace ℝ (Fin d) => (y : Fin d → ℝ) ⟨0, hd⟩) h1
  simp only [negMap, WithLp.ofLp_neg, id_eq, stdV, PiLp.single_apply] at h2
  norm_num at h2

/-- **The continuous obstruction.**  For odd `d` the identity and the antipodal map of the unit
sphere of `ℝ^d` are not homotopic. -/
theorem no_continuous_homotopy_of_odd {d : ℕ} (hodd : Odd d) :
    ¬ ∃ F : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        Continuous F ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (0, x) = x) ∧
        (∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 → F (1, x) = -x) ∧
        (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), ‖x‖ = 1 → ‖F (t, x)‖ = 1) :=
  fun h => no_smooth_avoiding_of_odd hodd (exists_smooth_avoiding_homotopy_general d h)

/-- The degree of a self-map, by cases on whether the map is homotopic to the identity or to the
antipodal map; every other map is given the value `0`.  The hypothesis `h` is the (true, on the
even spheres) statement that the identity and the antipodal map are not homotopic; it is what makes
the two special cases mutually exclusive. -/
noncomputable def degFn {d : ℕ}
    (h : ¬ sphHomotopic (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) negMap)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℤ :=
  if Relation.ReflTransGen sphHomotopic f id then 1
  else if Relation.ReflTransGen sphHomotopic f negMap then -1 else 0

lemma degFn_id {d : ℕ}
    (h : ¬ sphHomotopic (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) negMap) :
    degFn h (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = 1 := by
  unfold degFn
  rw [if_pos Relation.ReflTransGen.refl]

lemma degFn_neg {d : ℕ} (hd : 1 ≤ d)
    (h : ¬ sphHomotopic (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) negMap) :
    degFn h (negMap : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = -1 := by
  have hne : ¬ Relation.ReflTransGen sphHomotopic
      (negMap : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) id := by
    intro hr
    rcases sph_reflTransGen_eq_or hr with h' | h'
    · exact negMap_ne_id hd h'
    · exact h (sphHomotopic_symm h')
  unfold degFn
  rw [if_neg hne, if_pos Relation.ReflTransGen.refl]

lemma degFn_congr {d : ℕ}
    (h : ¬ sphHomotopic (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) negMap)
    {f g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hfg : sphHomotopic f g) : degFn h f = degFn h g := by
  have key : ∀ a : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (Relation.ReflTransGen sphHomotopic f a ↔ Relation.ReflTransGen sphHomotopic g a) := by
    intro a
    constructor
    · intro hfa
      exact (Relation.ReflTransGen.single (sphHomotopic_symm hfg)).trans hfa
    · intro hga
      exact (Relation.ReflTransGen.single hfg).trans hga
  unfold degFn
  by_cases h1 : Relation.ReflTransGen sphHomotopic f (id : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
  · rw [if_pos h1, if_pos ((key _).mp h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((key _).mpr hc))]
    by_cases h2 : Relation.ReflTransGen sphHomotopic f
        (negMap : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    · rw [if_pos h2, if_pos ((key _).mp h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 ((key _).mpr hc))]

end Work.RPCore.Port.PushDisc
