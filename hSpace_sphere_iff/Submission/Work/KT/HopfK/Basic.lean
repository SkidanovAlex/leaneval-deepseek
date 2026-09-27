/-
# The Hopf construction in the `K`-theory of spheres (node `hopf_K`)

Given an `HSpace` structure `hS` on `S^{2m-1}` (as `Sph (Eu m)`), the **Hopf construction** is the
map

`f : Sph (Eu m × Eu m) = S^{4m-1} ⟶ Tgt m = S^{2m}`

given, on the boundary `∂(D × D) = S^{2m-1} × D ∪ D × S^{2m-1}` of the ball `D × D` of
`Eu m × Eu m` (sup norm), by the two formulas

* `f (x, y) = (‖x‖ • μ (x̂, y),  √(1 - ‖x‖²))`  when `‖y‖ = 1`,
* `f (x, y) = (‖y‖ • μ (x, ŷ), -√(1 - ‖y‖²))`  when `‖x‖ = 1`,

which agree when `‖x‖ = ‖y‖ = 1`.  Both cases are the two branches of the single formula

`f (x, y) = (min ‖x‖ ‖y‖ • μ (x̂, ŷ), ±√|‖y‖² - ‖x‖²|)`,

the sign being that of `‖y‖² - ‖x‖²`; this formula is manifestly continuous, and the first factor
`min ‖x‖ ‖y‖` vanishes where the normalisation `x̂` (resp. `ŷ`) is undefined.

This file contains the definitions and their elementary point-set properties.  The main point is
that `f` lands in the unit sphere (`hopfRaw_norm`: the raw formula is radial, of norm
`max ‖x‖ ‖y‖`), and that `f` maps the two halves of the boundary into the two contractible caps
`{height ≥ -1/2}`, `{height ≤ 1/2}` of `Tgt m`.
-/
import Mathlib
import Submission.Work.KT.Defs

open scoped Topology
open Filter

namespace Work.KT

noncomputable section

/-! ## The target `Tgt m = S^{2m}` and its height function -/

/-- `ℝ^{2m} × ℝ` with the `ℓ²`-norm, identified with the Euclidean space `ℝ^{2m+1}`; this is the
model of the target of the Hopf construction on which the "height" coordinate is the second
component of the pair. -/
def euclTgtIso (m : ℕ) : WithLp 2 (Eu m × ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m + 1)) := by
  have hdim : Module.finrank ℝ (WithLp 2 (Eu m × ℝ)) = 2 * m + 1 := by
    rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Eu m × ℝ)), Module.finrank_prod,
      finrank_euclideanSpace_fin, Module.finrank_self]
  exact ((stdOrthonormalBasis ℝ (WithLp 2 (Eu m × ℝ))).reindex (finCongr hdim)).repr

/-- The "height" coordinate of a point of `Tgt m = S^{2m}` (the join coordinate of the Hopf
construction). -/
def tgtHeight (m : ℕ) (x : Tgt m) : ℝ :=
  (WithLp.ofLp ((euclTgtIso m).symm (x : EuclideanSpace ℝ (Fin (2 * m + 1))))).2

/-- The closed cap `T₊' = {height ≥ -1/2}` of `Tgt m`. -/
def capTplus (m : ℕ) : Set (Tgt m) := {x | tgtHeight m x ≥ -(1 / 2)}

/-- The closed cap `T₋' = {height ≤ 1/2}` of `Tgt m`. -/
def capTminus (m : ℕ) : Set (Tgt m) := {x | tgtHeight m x ≤ 1 / 2}

/-- The "south pole" `(0, -1)` of the target sphere, where the cone is based. -/
def southPt (m : ℕ) : Tgt m :=
  ⟨euclTgtIso m (WithLp.toLp 2 ((0 : Eu m), (-1 : ℝ))), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map]
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((0 : Eu m), (-1 : ℝ)))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_zero, norm_neg, norm_one] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : Eu m), (-1 : ℝ)))]⟩

/-! ## The raw Hopf construction on `Eu m × Eu m` -/

/-- `‖v‖⁻¹ • v`, with the junk value `0` at `v = 0`. -/
def unitV {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) : V := ‖v‖⁻¹ • v

lemma norm_unitV {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {v : V} (hv : v ≠ 0) :
    ‖unitV v‖ = 1 := by
  rw [unitV, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- A nonzero vector, normalised to a point of the unit sphere. -/
def normPt (m : ℕ) (v : {v : Eu m // v ≠ 0}) : Sph (Eu m) :=
  ⟨unitV v.1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_unitV v.2⟩

lemma continuous_normPt (m : ℕ) : Continuous (normPt m) := by
  have h1 : Continuous fun v : {v : Eu m // v ≠ 0} => unitV v.1 := by
    have : Continuous fun v : {v : Eu m // v ≠ 0} => (‖v.1‖)⁻¹ • v.1 :=
      (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.2)).smul
        continuous_subtype_val
    simpa [unitV] using this
  exact Continuous.subtype_mk h1 _

/-- The multiplication of the `H-space` structure, applied to the normalised arguments, with the
junk value `0` when one of the arguments vanishes (where it is multiplied by `0` anyway). -/
def muNorm (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (x y : Eu m) : Eu m :=
  if _ : x = 0 ∨ y = 0 then 0
  else (μ (normPt m ⟨x, by tauto⟩, normPt m ⟨y, by tauto⟩) : Eu m)

lemma norm_muNorm_le_one (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (x y : Eu m) :
    ‖muNorm m μ x y‖ ≤ 1 := by
  unfold muNorm
  split
  · simp
  · rename_i h
    push Not at h
    have := Metric.mem_sphere.mp (μ (normPt m ⟨x, h.1⟩, normPt m ⟨y, h.2⟩)).2
    rw [dist_eq_norm, sub_zero] at this
    rw [this]

lemma norm_muNorm_eq_one (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) {x y : Eu m}
    (hx : x ≠ 0) (hy : y ≠ 0) : ‖muNorm m μ x y‖ = 1 := by
  unfold muNorm
  rw [dif_neg (by push Not; exact ⟨hx, hy⟩)]
  have := Metric.mem_sphere.mp (μ (normPt m ⟨x, hx⟩, normPt m ⟨y, hy⟩)).2
  rwa [dist_eq_norm, sub_zero] at this

/-- The first (`Eu m`-valued) coordinate of the Hopf construction. -/
def hopfFst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (z : Eu m × Eu m) : Eu m :=
  min ‖z.1‖ ‖z.2‖ • muNorm m μ z.1 z.2

/-- The second (`ℝ`-valued) coordinate of the Hopf construction. -/
def hopfSnd (m : ℕ) (z : Eu m × Eu m) : ℝ :=
  Real.sqrt (max (‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) 0) - Real.sqrt (max (‖z.1‖ ^ 2 - ‖z.2‖ ^ 2) 0)

/-- **The Hopf construction**, as a raw formula on `Eu m × Eu m` with values in
`ℝ^{2m} × ℝ` with the `ℓ²`-norm. -/
def hopfRaw (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (z : Eu m × Eu m) :
    WithLp 2 (Eu m × ℝ) :=
  WithLp.toLp 2 (hopfFst m μ z, hopfSnd m z)

lemma norm_hopfFst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (z : Eu m × Eu m) :
    ‖hopfFst m μ z‖ = min ‖z.1‖ ‖z.2‖ := by
  rw [hopfFst, norm_smul, Real.norm_of_nonneg (le_min (norm_nonneg _) (norm_nonneg _))]
  rcases eq_or_lt_of_le (le_min (norm_nonneg z.1) (norm_nonneg z.2)) with h | h
  · rw [← h, zero_mul]
  · have h1 : z.1 ≠ 0 := fun hc => by
      have hlt : (0 : ℝ) < ‖z.1‖ := lt_of_lt_of_le h (min_le_left _ _)
      rw [hc, norm_zero] at hlt
      exact lt_irrefl 0 hlt
    have h2 : z.2 ≠ 0 := fun hc => by
      have hlt : (0 : ℝ) < ‖z.2‖ := lt_of_lt_of_le h (min_le_right _ _)
      rw [hc, norm_zero] at hlt
      exact lt_irrefl 0 hlt
    rw [norm_muNorm_eq_one m μ h1 h2, mul_one]

/-! ## Elementary properties of the second coordinate -/

lemma hopfSnd_of_le (m : ℕ) {z : Eu m × Eu m} (h : ‖z.1‖ ≤ ‖z.2‖) :
    hopfSnd m z = Real.sqrt (‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) := by
  have h1 : (0 : ℝ) ≤ ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2 := by nlinarith [norm_nonneg z.1, norm_nonneg z.2]
  have h2 : ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg z.1, norm_nonneg z.2]
  unfold hopfSnd
  rw [max_eq_left h1, max_eq_right h2, Real.sqrt_zero, sub_zero]

lemma hopfSnd_of_ge (m : ℕ) {z : Eu m × Eu m} (h : ‖z.2‖ ≤ ‖z.1‖) :
    hopfSnd m z = -Real.sqrt (‖z.1‖ ^ 2 - ‖z.2‖ ^ 2) := by
  have h1 : (0 : ℝ) ≤ ‖z.1‖ ^ 2 - ‖z.2‖ ^ 2 := by nlinarith [norm_nonneg z.1, norm_nonneg z.2]
  have h2 : ‖z.2‖ ^ 2 - ‖z.1‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg z.1, norm_nonneg z.2]
  unfold hopfSnd
  rw [max_eq_right h2, max_eq_left h1, Real.sqrt_zero, zero_sub]

lemma hopfSnd_sq (m : ℕ) (z : Eu m × Eu m) :
    hopfSnd m z ^ 2 = ‖z‖ ^ 2 - (min ‖z.1‖ ‖z.2‖) ^ 2 := by
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [hopfSnd_of_le m h, Real.sq_sqrt (by nlinarith [norm_nonneg z.1, norm_nonneg z.2]),
      min_eq_left h, Prod.norm_def, max_eq_right h]
  · rw [hopfSnd_of_ge m h, neg_sq,
      Real.sq_sqrt (by nlinarith [norm_nonneg z.1, norm_nonneg z.2]),
      min_eq_right h, Prod.norm_def, max_eq_left h]

/-- The raw Hopf construction is radial: its norm is the norm of the argument. -/
lemma hopfRaw_norm (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (z : Eu m × Eu m) :
    ‖hopfRaw m μ z‖ = ‖z‖ := by
  have hsq : ‖hopfRaw m μ z‖ ^ 2 = (min ‖z.1‖ ‖z.2‖) ^ 2 + hopfSnd m z ^ 2 := by
    rw [hopfRaw, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, norm_hopfFst]
  rw [hopfSnd_sq] at hsq
  have h2 : ‖hopfRaw m μ z‖ ^ 2 = ‖z‖ ^ 2 := by rw [hsq]; ring
  nlinarith [norm_nonneg (hopfRaw m μ z), norm_nonneg z]


/-! ## Continuity of the Hopf construction -/

/-- If `f` vanishes at `x` and `g` is bounded by `1`, then `f • g` is continuous at `x`. -/
lemma continuousAt_smul_of_norm_le_one {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → ℝ} {g : X → E} {x : X}
    (hf : ContinuousAt f x) (hg : ∀ y, ‖g y‖ ≤ 1) (hfx : f x = 0) :
    ContinuousAt (fun y => f y • g y) x := by
  change Tendsto (fun y => f y • g y) (𝓝 x) (𝓝 (f x • g x))
  rw [hfx, zero_smul]
  refine squeeze_zero_norm' (a := fun y => ‖f y‖) (Eventually.of_forall (fun y => ?_)) ?_
  · calc ‖f y • g y‖ = ‖f y‖ * ‖g y‖ := norm_smul _ _
      _ ≤ ‖f y‖ * 1 := by gcongr; exact hg y
      _ = ‖f y‖ := mul_one _
  · have h : Tendsto (fun y => ‖f y‖) (𝓝 x) (𝓝 ‖f x‖) := hf.norm
    simpa only [hfx, norm_zero] using h

lemma continuousOn_muNorm (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) :
    ContinuousOn (fun z : Eu m × Eu m => muNorm m μ z.1 z.2) {z | z.1 ≠ 0 ∧ z.2 ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : {z : Eu m × Eu m | z.1 ≠ 0 ∧ z.2 ≠ 0}.domRestrict
        (fun z => muNorm m μ z.1 z.2) =
      fun z : {z : Eu m × Eu m // z.1 ≠ 0 ∧ z.2 ≠ 0} =>
        (μ (normPt m ⟨z.1.1, z.2.1⟩, normPt m ⟨z.1.2, z.2.2⟩) : Eu m) := by
    funext z
    show muNorm m μ z.1.1 z.1.2 = _
    rw [muNorm, dif_neg (by push Not; exact ⟨z.2.1, z.2.2⟩)]
  rw [hfun]
  have hf : Continuous fun z : {z : Eu m × Eu m // z.1 ≠ 0 ∧ z.2 ≠ 0} => z.1.1 :=
    continuous_subtype_val.fst
  have hg : Continuous fun z : {z : Eu m × Eu m // z.1 ≠ 0 ∧ z.2 ≠ 0} => z.1.2 :=
    continuous_subtype_val.snd
  have hp : Continuous fun z : {z : Eu m × Eu m // z.1 ≠ 0 ∧ z.2 ≠ 0} =>
      normPt m ⟨z.1.1, z.2.1⟩ :=
    (continuous_normPt m).comp (Continuous.subtype_mk hf fun z => z.2.1)
  have hq : Continuous fun z : {z : Eu m × Eu m // z.1 ≠ 0 ∧ z.2 ≠ 0} =>
      normPt m ⟨z.1.2, z.2.2⟩ :=
    (continuous_normPt m).comp (Continuous.subtype_mk hg fun z => z.2.2)
  exact continuous_subtype_val.comp (μ.continuous.comp (hp.prodMk hq))

lemma continuous_hopfFst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) :
    Continuous (hopfFst m μ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.1 ≠ 0 ∧ z.2 ≠ 0
  · have hopen : IsOpen {z : Eu m × Eu m | z.1 ≠ 0 ∧ z.2 ≠ 0} :=
      (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
    have h1 : ContinuousAt (fun z : Eu m × Eu m => min ‖z.1‖ ‖z.2‖) z := by fun_prop
    have h2 : ContinuousAt (fun z : Eu m × Eu m => muNorm m μ z.1 z.2) z :=
      (continuousOn_muNorm m μ).continuousAt (hopen.mem_nhds hz)
    exact h1.smul h2
  · push Not at hz
    have h0 : min ‖z.1‖ ‖z.2‖ = 0 := by
      rcases eq_or_ne z.1 0 with h | h
      · simp [h]
      · rw [hz h]; simp
    exact continuousAt_smul_of_norm_le_one (by fun_prop)
      (fun w => norm_muNorm_le_one m μ w.1 w.2) h0

lemma continuous_hopfSnd (m : ℕ) : Continuous (hopfSnd m) := by
  have h1 : Continuous fun z : Eu m × Eu m => max (‖z.2‖ ^ 2 - ‖z.1‖ ^ 2) 0 := by fun_prop
  have h2 : Continuous fun z : Eu m × Eu m => max (‖z.1‖ ^ 2 - ‖z.2‖ ^ 2) 0 := by fun_prop
  exact (h1.sqrt).sub h2.sqrt

lemma continuous_hopfRaw (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) :
    Continuous (hopfRaw m μ) := by
  have hp : Continuous fun z : Eu m × Eu m => (hopfFst m μ z, hopfSnd m z) :=
    (continuous_hopfFst m μ).prodMk (continuous_hopfSnd m)
  exact (WithLp.prod_continuous_toLp 2 (Eu m) ℝ).comp hp

lemma hopfRaw_mem_sphere (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) :
    euclTgtIso m (hopfRaw m μ x.1) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 1))) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map, hopfRaw_norm]
  have hx := x.2
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
  exact hx

/-- **The Hopf construction** as a continuous map `S^{4m-1} = Sph (Eu m × Eu m) → Tgt m = S^{2m}`,
associated with a multiplication `μ` on `S^{2m-1}`. -/
def hopfKMap (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) :
    C(Sph (Eu m × Eu m), Tgt m) where
  toFun x := ⟨euclTgtIso m (hopfRaw m μ x.1), hopfRaw_mem_sphere m μ x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ (hopfRaw_mem_sphere m μ)
    exact (euclTgtIso m).continuous.comp
      ((continuous_hopfRaw m μ).comp continuous_subtype_val)

/-! ## The height of the Hopf construction, and the two caps -/

lemma tgtHeight_hopfKMap (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) : tgtHeight m (hopfKMap m μ x) = hopfSnd m x.1 := by
  simp only [tgtHeight, hopfKMap, ContinuousMap.coe_mk, LinearIsometryEquiv.symm_apply_apply,
    hopfRaw, WithLp.ofLp_toLp]

lemma norm_fst_le_one (m : ℕ) (x : Sph (Eu m × Eu m)) : ‖x.1.1‖ ≤ 1 := by
  have h := Metric.mem_sphere.mp x.2
  rw [dist_eq_norm, sub_zero] at h
  calc ‖x.1.1‖ ≤ ‖x.1‖ := norm_fst_le x.1
    _ = 1 := h

lemma norm_snd_le_one (m : ℕ) (x : Sph (Eu m × Eu m)) : ‖x.1.2‖ ≤ 1 := by
  have h := Metric.mem_sphere.mp x.2
  rw [dist_eq_norm, sub_zero] at h
  calc ‖x.1.2‖ ≤ ‖x.1‖ := norm_snd_le x.1
    _ = 1 := h

/-- On `D × S` (where `‖y‖ = 1`) the height is `√(1 - ‖x‖²)`: the image lies in the upper cap. -/
lemma tgtHeight_eq_of_norm_snd_eq_one (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) (hx : ‖x.1.2‖ = 1) :
    tgtHeight m (hopfKMap m μ x) = Real.sqrt (1 - ‖x.1.1‖ ^ 2) := by
  rw [tgtHeight_hopfKMap, hopfSnd_of_le m (by rw [hx]; exact norm_fst_le_one m x), hx, one_pow]

/-- On `S × D` (where `‖x‖ = 1`) the height is `-√(1 - ‖y‖²)`: the image lies in the lower cap. -/
lemma tgtHeight_eq_of_norm_fst_eq_one (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) (hx : ‖x.1.1‖ = 1) :
    tgtHeight m (hopfKMap m μ x) = -Real.sqrt (1 - ‖x.1.2‖ ^ 2) := by
  rw [tgtHeight_hopfKMap, hopfSnd_of_ge m (by rw [hx]; exact norm_snd_le_one m x), hx, one_pow]

lemma tgtHeight_nonneg_of_norm_snd_eq_one (m : ℕ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) (hx : ‖x.1.2‖ = 1) : tgtHeight m (hopfKMap m μ x) ≥ 0 := by
  rw [tgtHeight_eq_of_norm_snd_eq_one m μ x hx]
  exact Real.sqrt_nonneg _

lemma tgtHeight_nonpos_of_norm_fst_eq_one (m : ℕ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (x : Sph (Eu m × Eu m)) (hx : ‖x.1.1‖ = 1) : tgtHeight m (hopfKMap m μ x) ≤ 0 := by
  rw [tgtHeight_eq_of_norm_fst_eq_one m μ x hx]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)




/-! ## The diagonal idempotent `diag(1_r, 0)` -/

/-- The diagonal idempotent matrix `diag(1_r, 0)` of size `n`. -/
def diagMat (R : Type) [Ring R] (r n : ℕ) : Mat R :=
  ⟨n, Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then 1 else 0)⟩

lemma diagMat_isIdem (R : Type) [Ring R] (r n : ℕ) : (diagMat R r n).IsIdem := by
  unfold Mat.IsIdem diagMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases h : (i : ℕ) < r <;> simp [h]

/-- A matrix over `ℂ`, regarded as a constant matrix over a `ℂ`-algebra. -/
def matConst (A : Type) [Semiring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) A :=
  M.map (algebraMap ℂ A)

lemma matConst_mul (A : Type) [Semiring A] [Algebra ℂ A] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ) : matConst A (M * N) = matConst A M * matConst A N := by
  simp only [matConst]
  rw [Matrix.map_mul]

lemma matConst_one (A : Type) [Semiring A] [Algebra ℂ A] (n : ℕ) :
    matConst A (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp only [matConst]
  rw [Matrix.map_one (algebraMap ℂ A) (map_zero _) (map_one _)]


namespace HopfK

/-- The unit sphere as a subset of the closed unit ball. -/
def sphToBall {V : Type} [NormedAddCommGroup V] (x : Sph V) : Ball V :=
  ⟨(x : V), by
    have h := Metric.mem_sphere.mp x.2
    rw [dist_eq_norm, sub_zero] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact h.le⟩

@[simp] lemma sphToBall_coe {V : Type} [NormedAddCommGroup V] (x : Sph V) :
    ((sphToBall x : Ball V) : V) = (x : V) := rfl

end HopfK

/-- The radial projection of a nonzero point of the ball onto the unit sphere. -/
def radPt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (z : {z : Ball V // z ≠ 0}) :
    Sph V :=
  ⟨(‖(z.1 : V)‖)⁻¹ • (z.1 : V), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr fun h => z.2 (Subtype.ext h))]⟩

@[simp] lemma radPt_coe {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z : {z : Ball V // z ≠ 0}) : ((radPt z : Sph V) : V) = (‖(z.1 : V)‖)⁻¹ • (z.1 : V) := rfl


/-! ## Evaluations of elements of the mapping cone -/

/-- Evaluation of the "cell" component of an element of the mapping cone at a point of the ball. -/
def evalD (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (z : Ball (Eu m × Eu m)) :
    coneAlg f →ₐ[ℂ] ℂ :=
  (evalC z).comp ((AlgHom.snd ℂ C(Tgt m, ℂ) C(Ball (Eu m × Eu m), ℂ)).comp (coneAlg f).val)

/-- Evaluation of the "base" component of an element of the mapping cone at a point of `Tgt m`. -/
def evalT (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (t : Tgt m) :
    coneAlg f →ₐ[ℂ] ℂ :=
  (evalC t).comp (coneToT f)


/-- The normalisation `z ↦ ‖z‖⁻¹ • z` of a point of the closed unit ball, as a point of the ball
(junk value `0` at the origin). -/
def normPtBall {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (z : Ball V) : Ball V :=
  ⟨(‖(z : V)‖)⁻¹ • (z : V), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    rcases eq_or_ne ‖(z : V)‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]⟩

lemma normPtBall_coe {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (z : Ball V) :
    ((normPtBall z : Ball V) : V) = (‖(z : V)‖)⁻¹ • (z : V) := rfl

lemma normPtBall_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {z : Ball V} (hz : z ≠ 0) : normPtBall z ∈ bdry V := by
  show ‖((normPtBall z : Ball V) : V)‖ = 1
  rw [normPtBall_coe, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr fun h => hz (Subtype.ext h))]


/-- The diagonal idempotent `diag(1_r, 0)` as a matrix over `ℂ` (model for cap conditions). -/
abbrev diagIdemMat (r n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0)

lemma diagIdemMat_isIdem (r n : ℕ) : Mat.IsIdem (⟨n, diagIdemMat r n⟩ : Mat ℂ) :=
  diagMat_isIdem ℂ r n


/-- The point `(0, y)` of the ball `Ball (Eu m × Eu m)`. -/
def zeroFst (m : ℕ) (y : Ball (Eu m)) : Ball (Eu m × Eu m) :=
  ⟨((0 : Eu m), (y : Eu m)), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
    have h := Metric.mem_closedBall.mp y.2
    rwa [dist_eq_norm, sub_zero] at h⟩

/-- The point `(x, 0)` of the ball `Ball (Eu m × Eu m)`. -/
def zeroSnd (m : ℕ) (x : Ball (Eu m)) : Ball (Eu m × Eu m) :=
  ⟨((x : Eu m), (0 : Eu m)), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _)]
    have h := Metric.mem_closedBall.mp x.2
    rwa [dist_eq_norm, sub_zero] at h⟩

end

end Work.KT
