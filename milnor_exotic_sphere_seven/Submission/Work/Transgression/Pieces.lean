import Mathlib
import Submission.Work.Transgression.Gysin
import Submission.Work.Thom.sphereInDisc_homotopyEquiv
import Submission.Work.Thom.TransgressionSquare
import Submission.Work.CharacteristicClasses.Powers
import Submission.Work.Cohomology.CompatTrans.homology_prod_sphere
import Submission.Work.Cohomology.uctDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: the two-chart cover of the punctured total space

The Mayer–Vietoris computation of `Work.Transgression.PuncturedCohCard a b` — that `H⁴` of the
punctured total space `E ∖ 0` of `clutchBundle a b` (a rank-`4` real bundle over
`S⁴ = OnePoint ℝ⁴`) is cyclic of order `|a + b|` — is run on the open cover

  `E ∖ 0 = pU ∪ pV`,   `pU` over `hemi0`, `pV` over `hemi1`,   `pU ∩ pV = pW` over `hemi0 ∩ hemi1`.

This module builds that cover together with the *coordinate maps* through which the two
Mayer–Vietoris restrictions become computable:

* `chart0`, `chart1` — the fibre coordinates of a point of the total space in the two charts
  (the local trivialisations `Z.localTriv false`, `Z.localTriv true` of the gluing data);
* `fibreNorm`, `IsEuclidean` — the hypothesis that the transition functions are isometries, so that
  the normalisations `p ↦ ‖chart0 p‖⁻¹ • chart0 p` are the same in either chart;
* `rhoU : pU → S³`, `rhoV : pV → S³` — the *retractions* `p ↦ normalize (chart_i p)` (the
  deformation retractions of the two pieces onto the equator of the fibre), which are homotopy
  equivalences (`Work.Transgression.rhoU_homotopyEquiv` and friends, in `Homotopy.lean`);
* `rhoW : pW → S³ × S³` — the same in both charts,
  `p ↦ (normalize (coord0 p.1), normalize (chart0 p))`;
* `sW : S³ × S³ → pW` — the explicit section of `rhoW` (base point `↑u` in `hemi0`, fibre
  coordinate `v` in chart `0`), whose existence is what makes `rhoW` a homotopy equivalence;
* `psi : S³ × S³ → S³`, `ψ (u, v) = uᵃ v uᵇ` — the second coordinate of `rhoV ∘ sW`, i.e. the class
  of the clutching on the overlap.  The two identities
  `rhoU (incl p) = prj₂ (rhoW p)` and `rhoV (incl p) = ψ (rhoW p)` (on the nose, for `p ∈ pW`) are
  `Work.Transgression.rhoU_incl_eq` and `Work.Transgression.rhoV_incl_eq`; they are the input of the
  transgression computation, and `ψ*` of the generator of `H³(S³)` is `(a+b)·(class of prj₁) +
  (class of prj₂)` (`Work.Transgression.psi_class`).
-/

namespace Work.Transgression

open Work.TangentClasses CategoryTheory

noncomputable section

/-! ## 1. The cover -/

/-- A point of `S⁴` lies in one of the two hemispheres. -/
lemma hemi0_or_hemi1 (p : Work.Agree.S4) : p ∈ Work.Agree.hemi0 ∨ p ∈ Work.Agree.hemi1 := by
  by_cases hp : p = OnePoint.infty
  · exact Or.inr (fun h => OnePoint.infty_ne_coe (0 : EuclideanSpace ℝ (Fin 4)) (hp ▸ h))
  · exact Or.inl hp

/-- The union of the two hemispheres of `S⁴ = OnePoint ℝ⁴` is everything. -/
lemma hemi0_union_hemi1 : Work.Agree.hemi0 ∪ Work.Agree.hemi1 = Set.univ := by
  ext p
  exact ⟨fun _ => Set.mem_univ p, fun _ => hemi0_or_hemi1 p⟩

/-- The part of `E ∖ 0` lying over `hemi0`. -/
def pU (a b : ℤ) : Set ↥(Work.Thom.zeroComplement (Zb a b)) :=
  {p | (p : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi0}

/-- The part of `E ∖ 0` lying over `hemi1`. -/
def pV (a b : ℤ) : Set ↥(Work.Thom.zeroComplement (Zb a b)) :=
  {p | (p : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi1}

@[simp] lemma mem_pU (a b : ℤ) (p : ↥(Work.Thom.zeroComplement (Zb a b))) :
    p ∈ pU a b ↔ (p : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi0 := Iff.rfl

@[simp] lemma mem_pV (a b : ℤ) (p : ↥(Work.Thom.zeroComplement (Zb a b))) :
    p ∈ pV a b ↔ (p : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi1 := Iff.rfl

theorem isOpen_pU (a b : ℤ) : IsOpen (pU a b) :=
  Work.Agree.isOpen_hemi0.preimage
    ((Zb a b).continuous_proj.comp continuous_subtype_val)

theorem isOpen_pV (a b : ℤ) : IsOpen (pV a b) :=
  Work.Agree.isOpen_hemi1.preimage
    ((Zb a b).continuous_proj.comp continuous_subtype_val)

theorem pU_union_pV (a b : ℤ) : pU a b ∪ pV a b = Set.univ := by
  ext p
  exact ⟨fun _ => Set.mem_univ p, fun _ => hemi0_or_hemi1 _⟩

/-- The topological space `E ∖ 0`, the total space of the chapter's Mayer–Vietoris computation. -/
abbrev Ptop (a b : ℤ) : TopCat := TopCat.of ↥(Work.Thom.zeroComplement (Zb a b))

/-! ## 2. The two chart fibre coordinates -/

/-- The fibre coordinate of a point of the total space in the chart over `hemi0` (the second
component of the local trivialisation `Z.localTriv false`). -/
def chart0 (a b : ℤ) (p : (Zb a b).TotalSpace) : EuclideanSpace ℝ (Fin 4) :=
  ((Zb a b).localTriv false p).2

/-- The fibre coordinate of a point of the total space in the chart over `hemi1`. -/
def chart1 (a b : ℤ) (p : (Zb a b).TotalSpace) : EuclideanSpace ℝ (Fin 4) :=
  ((Zb a b).localTriv true p).2

@[simp] lemma chart0_apply (a b : ℤ) (p : (Zb a b).TotalSpace) :
    chart0 a b p = ((Zb a b).localTriv false p).2 := rfl

@[simp] lemma chart1_apply (a b : ℤ) (p : (Zb a b).TotalSpace) :
    chart1 a b p = ((Zb a b).localTriv true p).2 := rfl

/-- On the chart over `hemi0` the first fibre coordinate is the second component of the point. -/
lemma chart0_of_mem (a b : ℤ) {p : (Zb a b).TotalSpace} (hp : p.1 ∈ Work.Agree.hemi0) :
    chart0 a b p = p.2 := by
  rw [chart0_apply, VectorBundleCore.localTriv_apply]
  have hidx : (Zb a b).indexAt p.1 = false := if_neg hp
  rw [hidx]
  rfl

theorem continuousOn_chart0 (a b : ℤ) :
    ContinuousOn (chart0 a b) {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi0} := by
  have h := ((Zb a b).localTriv false).continuousOn
  have hs : {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi0}
      ⊆ ((Zb a b).localTriv false).source := by
    intro p hp
    rw [VectorBundleCore.mem_localTriv_source]
    exact hp
  have h2 : ContinuousOn (fun q : Work.Agree.S4 × EuclideanSpace ℝ (Fin 4) => q.2) Set.univ :=
    continuous_snd.continuousOn
  have h3 : ContinuousOn (fun p : (Zb a b).TotalSpace => ((Zb a b).localTriv false p).2)
      {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi0} :=
    h2.comp (h.mono hs) (fun _ _ => Set.mem_univ _)
  exact h3

theorem continuousOn_chart1 (a b : ℤ) :
    ContinuousOn (chart1 a b) {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi1} := by
  have h := ((Zb a b).localTriv true).continuousOn
  have hs : {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi1}
      ⊆ ((Zb a b).localTriv true).source := by
    intro p hp
    rw [VectorBundleCore.mem_localTriv_source]
    exact hp
  have h2 : ContinuousOn (fun q : Work.Agree.S4 × EuclideanSpace ℝ (Fin 4) => q.2) Set.univ :=
    continuous_snd.continuousOn
  have h3 : ContinuousOn (fun p : (Zb a b).TotalSpace => ((Zb a b).localTriv true p).2)
      {p : (Zb a b).TotalSpace | p.1 ∈ Work.Agree.hemi1} :=
    h2.comp (h.mono hs) (fun _ _ => Set.mem_univ _)
  exact h3

/-! ## 3. The transition function is an isometry -/

/-- The transition `v ↦ qᵃ v qᵇ` preserves the norm of the fibre. -/
lemma norm_qTwist (a b : ℤ) (q : Quaternion ℝ) (hq : ‖q‖ = 1)
    (v : EuclideanSpace ℝ (Fin 4)) : ‖Work.Agree.qTwist a b q v‖ = ‖v‖ := by
  rw [Work.Agree.qTwist_apply, norm_ofQ, norm_mul, norm_mul, norm_zpow, norm_zpow, hq,
    norm_toQ]
  simp

theorem isEuclidean_clutchBundle (a b : ℤ) : Work.Thom.IsEuclidean (Zb a b) := by
  intro i j x hx v
  have hq : ‖Work.Agree.uDir x‖ = 1 :=
    Submission.Milnor.norm_coe (Submission.Milnor.unitDir (Work.Agree.coord0 x))
  rcases i with _ | _ <;> rcases j with _ | _
  · show ‖(Work.Agree.ct a b false false x) v‖ = ‖v‖
    simp [Work.Agree.ct]
  · show ‖(Work.Agree.ct a b false true x) v‖ = ‖v‖
    rw [Work.Agree.ct_false_true]
    exact norm_qTwist a b _ hq v
  · show ‖(Work.Agree.ct a b true false x) v‖ = ‖v‖
    rw [Work.Agree.ct_true_false]
    exact norm_qTwist (-a) (-b) _ hq v
  · show ‖(Work.Agree.ct a b true true x) v‖ = ‖v‖
    simp [Work.Agree.ct]

/-! ## 4. Normalisation in the fibre, and the fibre norms of the chart coordinates -/

/-- The normalisation `v ↦ ‖v‖⁻¹ • v` of a vector of the fibre model. -/
def nrmlz (v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := (‖v‖)⁻¹ • v

lemma norm_nrmlz {v : EuclideanSpace ℝ (Fin 4)} (hv : v ≠ 0) : ‖nrmlz v‖ = 1 := by
  rw [nrmlz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma nrmlz_mem_sphere {v : EuclideanSpace ℝ (Fin 4)} (hv : v ≠ 0) :
    nrmlz v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]; exact norm_nrmlz hv

lemma nrmlz_of_norm_eq_one {v : EuclideanSpace ℝ (Fin 4)} (hv : ‖v‖ = 1) : nrmlz v = v := by
  rw [nrmlz, hv, inv_one, one_smul]

lemma nrmlz_smul {c : ℝ} (hc : 0 < c) (v : EuclideanSpace ℝ (Fin 4)) :
    nrmlz (c • v) = nrmlz v := by
  have h : (c * ‖v‖)⁻¹ * c = ‖v‖⁻¹ := by
    field_simp
  simp only [nrmlz, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, h]

lemma nrmlz_idem {v : EuclideanSpace ℝ (Fin 4)} (hv : v ≠ 0) : nrmlz (nrmlz v) = nrmlz v := by
  have h : ‖nrmlz v‖ = 1 := norm_nrmlz hv
  rw [nrmlz, h, inv_one, one_smul]

lemma continuousOn_nrmlz :
    ContinuousOn nrmlz {v : EuclideanSpace ℝ (Fin 4) | v ≠ 0} := by
  have hc : ContinuousOn (fun v : EuclideanSpace ℝ (Fin 4) => (‖v‖)⁻¹) {v | v ≠ 0} :=
    continuous_norm.continuousOn.inv₀ (fun v hv => norm_ne_zero_iff.mpr hv)
  exact hc.smul continuousOn_id

/-- A point of `hemi0` lies in the base set of the first chart. -/
lemma mem_baseSet_false {a b : ℤ} {x : Work.Agree.S4} (hx : x ∈ Work.Agree.hemi0) :
    x ∈ (Zb a b).baseSet false := hx

/-- A point of `hemi1` lies in the base set of the second chart. -/
lemma mem_baseSet_true {a b : ℤ} {x : Work.Agree.S4} (hx : x ∈ Work.Agree.hemi1) :
    x ∈ (Zb a b).baseSet true := hx

lemma mem_localTriv_baseSet_false {a b : ℤ} {x : Work.Agree.S4}
    (hx : x ∈ Work.Agree.hemi0) : x ∈ ((Zb a b).localTriv false).baseSet := by
  rw [← VectorBundleCore.baseSet_at]; exact mem_baseSet_false hx

lemma mem_localTriv_baseSet_true {a b : ℤ} {x : Work.Agree.S4}
    (hx : x ∈ Work.Agree.hemi1) : x ∈ ((Zb a b).localTriv true).baseSet := by
  rw [← VectorBundleCore.baseSet_at]; exact mem_baseSet_true hx

/-- The local trivialisation in the chart over `hemi0` is the identity trivialisation. -/
lemma localTriv_false_symm (a b : ℤ) {x : Work.Agree.S4} (hx : x ∈ Work.Agree.hemi0)
    (y : EuclideanSpace ℝ (Fin 4)) :
    ((Zb a b).localTriv false).symm x y = y := by
  have hxy : ((((Zb a b).localTriv false) (⟨x, y⟩ : (Zb a b).TotalSpace) :
      Work.Agree.S4 × EuclideanSpace ℝ (Fin 4))).2 = y := by
    rw [VectorBundleCore.localTriv_apply]
    have hidx : (Zb a b).indexAt x = false := if_neg hx
    rw [hidx]
    rfl
  calc ((Zb a b).localTriv false).symm x y
      = ((Zb a b).localTriv false).symm x
          ((((Zb a b).localTriv false) (⟨x, y⟩ : (Zb a b).TotalSpace) :
            Work.Agree.S4 × EuclideanSpace ℝ (Fin 4))).2 := by rw [hxy]
    _ = y := Bundle.Trivialization.symm_apply_apply_mk ((Zb a b).localTriv false)
        (mem_localTriv_baseSet_false hx) y

/-- The fibrewise norm of a point of the total space above `hemi0` whose chart-`0` fibre
coordinate is `y`. -/
lemma fibreNorm_mk_hemi0 (a b : ℤ) {x : Work.Agree.S4} (hx : x ∈ Work.Agree.hemi0)
    (y : EuclideanSpace ℝ (Fin 4)) :
    Work.Thom.fibreNorm (Zb a b)
      (⟨x, ((Zb a b).localTriv false).symm x y⟩ : (Zb a b).TotalSpace) = ‖y‖ := by
  rw [Work.Thom.fibreNorm_localTriv (isEuclidean_clutchBundle a b) false _ (mem_baseSet_false hx)]
  have h2 : ((Zb a b).localTriv false
      ⟨x, ((Zb a b).localTriv false).symm x y⟩ : Work.Agree.S4 × EuclideanSpace ℝ (Fin 4)).2
      = y := by
    have hh := Bundle.Trivialization.apply_mk_symm ((Zb a b).localTriv false)
      (mem_localTriv_baseSet_false hx) y
    exact congrArg Prod.snd hh
  rw [h2]

lemma norm_chart0 (a b : ℤ) (p : (Zb a b).TotalSpace) (hp : p.1 ∈ Work.Agree.hemi0) :
    ‖chart0 a b p‖ = Work.Thom.fibreNorm (Zb a b) p :=
  (Work.Thom.fibreNorm_localTriv (isEuclidean_clutchBundle a b) false p
    (mem_baseSet_false hp)).symm

lemma norm_chart1 (a b : ℤ) (p : (Zb a b).TotalSpace) (hp : p.1 ∈ Work.Agree.hemi1) :
    ‖chart1 a b p‖ = Work.Thom.fibreNorm (Zb a b) p :=
  (Work.Thom.fibreNorm_localTriv (isEuclidean_clutchBundle a b) true p
    (mem_baseSet_true hp)).symm

theorem chart0_ne_zero (a b : ℤ) (q : ↥(Work.Thom.zeroComplement (Zb a b)))
    (hp : (q : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi0) :
    chart0 a b (q : (Zb a b).TotalSpace) ≠ 0 := by
  intro h
  have h1 : Work.Thom.fibreNorm (Zb a b) (q : (Zb a b).TotalSpace) = 0 := by
    rw [← norm_chart0 a b _ hp, h, norm_zero]
  exact (Work.Thom.SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mp q.2 h1

theorem chart1_ne_zero (a b : ℤ) (q : ↥(Work.Thom.zeroComplement (Zb a b)))
    (hp : (q : (Zb a b).TotalSpace).1 ∈ Work.Agree.hemi1) :
    chart1 a b (q : (Zb a b).TotalSpace) ≠ 0 := by
  intro h
  have h1 : Work.Thom.fibreNorm (Zb a b) (q : (Zb a b).TotalSpace) = 0 := by
    rw [← norm_chart1 a b _ hp, h, norm_zero]
  exact (Work.Thom.SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mp q.2 h1

lemma ofQ_ne_zero (q : Work.CharacteristicClasses.S3) :
    Work.Agree.ofQ (q : Quaternion ℝ) ≠ 0 := by
  intro h
  have h1 : Work.Agree.toQ (Work.Agree.ofQ (q : Quaternion ℝ)) = Work.Agree.toQ 0 := by rw [h]
  rw [Work.Agree.toQ_ofQ, map_zero] at h1
  exact coe_ne_zero_of_s3 h1

/-! ## 5. The two retractions `pU → S³` and `pV → S³` -/

/-- **The retraction of the piece over `hemi0` onto the fibre equator**: the normalised chart-`0`
fibre coordinate, read as a unit quaternion. -/
def rhoU (a b : ℤ) : C(↥(pU a b), Work.CharacteristicClasses.S3) where
  toFun p := ⟨Work.Agree.toQ (nrmlz (chart0 a b (p : (Zb a b).TotalSpace))), by
    rw [Metric.mem_sphere, dist_zero_right, norm_toQ]
    exact norm_nrmlz (chart0_ne_zero a b _ p.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hchart : Continuous
        (fun p : ↥(pU a b) => chart0 a b (p : (Zb a b).TotalSpace)) :=
      (continuousOn_chart0 a b).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2)
    exact Work.Agree.toQ.continuous.comp
      (continuousOn_nrmlz.comp_continuous hchart (fun p => chart0_ne_zero a b _ p.2))

/-- **The retraction of the piece over `hemi1` onto the fibre equator**. -/
def rhoV (a b : ℤ) : C(↥(pV a b), Work.CharacteristicClasses.S3) where
  toFun p := ⟨Work.Agree.toQ (nrmlz (chart1 a b (p : (Zb a b).TotalSpace))), by
    rw [Metric.mem_sphere, dist_zero_right, norm_toQ]
    exact norm_nrmlz (chart1_ne_zero a b _ p.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hchart : Continuous
        (fun p : ↥(pV a b) => chart1 a b (p : (Zb a b).TotalSpace)) :=
      (continuousOn_chart1 a b).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2)
    exact Work.Agree.toQ.continuous.comp
      (continuousOn_nrmlz.comp_continuous hchart (fun p => chart1_ne_zero a b _ p.2))

/-! ## 6. The product retraction `pU ∩ pV → S³ × S³` and its section -/

/-- The overlap of the two pieces. -/
abbrev pW (a b : ℤ) : Set ↥(Work.Thom.zeroComplement (Zb a b)) := pU a b ∩ pV a b

/-- The normalised chart-`0` base coordinate of a point of `hemi0`. -/
def dir0 (y : Work.Agree.S4) : EuclideanSpace ℝ (Fin 4) := nrmlz (Work.Agree.coord0 y)

lemma continuousOn_dir0 : ContinuousOn dir0 (Work.Agree.hemi0 ∩ Work.Agree.hemi1) :=
  continuousOn_nrmlz.comp (Work.Agree.continuousOn_coord0.mono Set.inter_subset_left)
    (fun y hy => Work.Agree.coord0_ne_zero hy.1 hy.2)

/-- **The retraction of the overlap onto `S³ × S³`**: in the chart over `hemi0`, the normalised
base coordinate and the normalised fibre coordinate. -/
def rhoW (a b : ℤ) :
    C(↥(pW a b), Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3) where
  toFun p :=
    (⟨Work.Agree.toQ (dir0 (p : (Zb a b).TotalSpace).1), by
      rw [Metric.mem_sphere, dist_zero_right, norm_toQ]
      exact norm_nrmlz (Work.Agree.coord0_ne_zero p.2.1 p.2.2)⟩,
     ⟨Work.Agree.toQ (nrmlz (chart0 a b (p : (Zb a b).TotalSpace))), by
      rw [Metric.mem_sphere, dist_zero_right, norm_toQ]
      exact norm_nrmlz (chart0_ne_zero a b _ p.2.1)⟩)
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · refine Continuous.subtype_mk ?_ _
      have h : Continuous
          (fun p : ↥(pW a b) => dir0 ((p : (Zb a b).TotalSpace).1)) :=
        continuousOn_dir0.comp_continuous
          ((Zb a b).continuous_proj.comp (continuous_subtype_val.comp continuous_subtype_val))
          (fun p => ⟨p.2.1, p.2.2⟩)
      exact Work.Agree.toQ.continuous.comp h
    · refine Continuous.subtype_mk ?_ _
      have hchart : Continuous
          (fun p : ↥(pW a b) => chart0 a b (p : (Zb a b).TotalSpace)) :=
        (continuousOn_chart0 a b).comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.2.1)
      exact Work.Agree.toQ.continuous.comp
        (continuousOn_nrmlz.comp_continuous hchart (fun p => chart0_ne_zero a b _ p.2.1))

lemma ofQ_hemi1 (q : Work.CharacteristicClasses.S3) :
    (↑(Work.Agree.ofQ (q : Quaternion ℝ)) : Work.Agree.S4) ∈ Work.Agree.hemi1 := by
  intro h
  have h1 : Work.Agree.ofQ (q : Quaternion ℝ) = 0 := OnePoint.coe_injective h
  exact ofQ_ne_zero q h1

/-- The section of `rhoW`: the point over the `hemi0`-point with normalised coordinate `u` whose
chart-`0` fibre coordinate is `v`. -/
def sW (a b : ℤ) :
    C(Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3, ↥(pW a b)) where
  toFun p :=
    ⟨⟨⟨(↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)) : Work.Agree.S4),
        ((Zb a b).localTriv false).symm (↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)))
          (Work.Agree.ofQ (p.2 : Quaternion ℝ))⟩,
      (Work.Thom.SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b) _).mpr (by
        rw [fibreNorm_mk_hemi0 a b (OnePoint.coe_ne_infty _)]
        exact norm_ne_zero_iff.mpr (ofQ_ne_zero p.2))⟩,
      OnePoint.coe_ne_infty _, ofQ_hemi1 p.1⟩
  continuous_toFun := by
    have hcont : Continuous (fun p : Work.CharacteristicClasses.S3 ×
        Work.CharacteristicClasses.S3 =>
        ((↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)) : Work.Agree.S4),
          Work.Agree.ofQ (p.2 : Quaternion ℝ))) :=
      Continuous.prodMk
        (OnePoint.continuous_coe.comp
          (Work.Agree.ofQ.continuous.comp (continuous_subtype_val.comp continuous_fst)))
        (Work.Agree.ofQ.continuous.comp (continuous_subtype_val.comp continuous_snd))
    have hmem : ∀ p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3,
        ((↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)) : Work.Agree.S4),
          Work.Agree.ofQ (p.2 : Quaternion ℝ))
        ∈ ((Zb a b).localTriv false).baseSet ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 4))) :=
      fun p => ⟨mem_localTriv_baseSet_false (OnePoint.coe_ne_infty _), Set.mem_univ _⟩
    exact Continuous.subtype_mk
      (Continuous.subtype_mk
        ((Bundle.Trivialization.continuousOn_symm ((Zb a b).localTriv false)).comp_continuous
          hcont hmem)
        (fun p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3 =>
          (Work.Thom.SphereInDisc.mem_zeroComplement_iff_fibreNorm_ne_zero (Zb a b)
            (⟨(↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)) : Work.Agree.S4),
              ((Zb a b).localTriv false).symm (↑(Work.Agree.ofQ (p.1 : Quaternion ℝ)))
                (Work.Agree.ofQ (p.2 : Quaternion ℝ))⟩ : (Zb a b).TotalSpace)).mpr (by
            rw [fibreNorm_mk_hemi0 a b (OnePoint.coe_ne_infty _)]
            exact norm_ne_zero_iff.mpr (ofQ_ne_zero p.2))))
      (fun p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3 =>
        ⟨OnePoint.coe_ne_infty _, ofQ_hemi1 p.1⟩)

/-! ## 7. The clutching map `ψ (u,v) = uᵃ v uᵇ` on `S³ × S³` -/

/-- **The clutching map on the overlap**: `ψ (u, v) = uᵃ · v · uᵇ` in the quaternion model. -/
def psi (a b : ℤ) : C(Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3,
    Work.CharacteristicClasses.S3) where
  toFun p := ⟨(p.1 : Quaternion ℝ) ^ a * (p.2 : Quaternion ℝ) * (p.1 : Quaternion ℝ) ^ b, by
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, norm_mul, norm_zpow, norm_zpow,
      Submission.Milnor.norm_coe p.1, Submission.Milnor.norm_coe p.2]
    norm_num⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hpowa : ContinuousOn (fun q : Quaternion ℝ => q ^ a) {q : Quaternion ℝ | q ≠ 0} :=
      continuousOn_id.zpow₀ a (fun q hq => Or.inl hq)
    have hpowb : ContinuousOn (fun q : Quaternion ℝ => q ^ b) {q : Quaternion ℝ | q ≠ 0} :=
      continuousOn_id.zpow₀ b (fun q hq => Or.inl hq)
    have h1 : Continuous fun p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3 =>
        (p.1 : Quaternion ℝ) ^ a :=
      hpowa.comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => coe_ne_zero_of_s3)
    have h2 : Continuous fun p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3 =>
        (p.2 : Quaternion ℝ) := continuous_subtype_val.comp continuous_snd
    have h3 : Continuous fun p : Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3 =>
        (p.1 : Quaternion ℝ) ^ b :=
      hpowb.comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => coe_ne_zero_of_s3)
    exact (h1.mul h2).mul h3

/-! ## 8. The two projections and the two factor inclusions of `S³ × S³` -/

/-- The first projection `S³ × S³ → S³`. -/
def prjA : C(Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3,
    Work.CharacteristicClasses.S3) := ⟨Prod.fst, continuous_fst⟩

/-- The second projection `S³ × S³ → S³`. -/
def prjB : C(Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3,
    Work.CharacteristicClasses.S3) := ⟨Prod.snd, continuous_snd⟩

/-- The first factor inclusion `S³ → S³ × S³`, `v ↦ (v, 1)`. -/
def sectA : C(Work.CharacteristicClasses.S3,
    Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3) :=
  ⟨fun v => (v, Work.CharacteristicClasses.s3One), continuous_id.prodMk continuous_const⟩

/-- The second factor inclusion `S³ → S³ × S³`, `v ↦ (1, v)`. -/
def sectB : C(Work.CharacteristicClasses.S3,
    Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3) :=
  ⟨fun v => (Work.CharacteristicClasses.s3One, v), continuous_const.prodMk continuous_id⟩

@[simp] lemma prjA_apply (p) : prjA p = p.1 := rfl
@[simp] lemma prjB_apply (p) : prjB p = p.2 := rfl
@[simp] lemma sectA_apply (v) : sectA v = (v, Work.CharacteristicClasses.s3One) := rfl
@[simp] lemma sectB_apply (v) : sectB v = (Work.CharacteristicClasses.s3One, v) := rfl

end

end Work.Transgression
