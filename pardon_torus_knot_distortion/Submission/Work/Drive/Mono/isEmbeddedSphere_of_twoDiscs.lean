import Mathlib
import Submission.Work.Drive.Mono.isEmbeddedSphere_of_doubleDisc
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.CoreTopology.Disk

/-!
# The union of two discs glued along a common boundary circle

Two injective continuous maps `eA eB : 𝔻 → ℝ³` of the closed unit disc whose images meet
exactly along their (common) boundary circle have union an embedded 2-sphere.

The two discs need not agree *pointwise* on the boundary: the hypotheses say only that the two
boundary curves have the same image and that the images of the discs meet exactly in that set.
So the union is the double of a disc glued by the homeomorphism `φ` of the boundary circle
which matches the two parametrisations.  The sphere map is that of
`isEmbeddedSphere_of_doubleDisc` after reparametrising the second disc by the cone over `φ`,
`z ↦ ‖z‖ • φ(z/‖z‖)`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The closed unit disc of `ℂ`. -/
abbrev UD := Metric.closedBall (0 : ℂ) 1

/-- The unit circle of `ℂ`. -/
abbrev US := Metric.sphere (0 : ℂ) 1

/-! ## The unit circle as a subset of the unit disc -/

/-- The unit circle is contained in the closed unit disc. -/
def sphIncl (u : US) : UD := ⟨(u : ℂ), Metric.sphere_subset_closedBall u.2⟩

theorem sphIncl_coe (u : US) : (sphIncl u : ℂ) = (u : ℂ) := rfl

theorem norm_of_mem_sphere (u : US) : ‖(u : ℂ)‖ = 1 := by
  have h := u.2
  rw [Metric.mem_sphere, dist_zero_right] at h
  exact h

theorem norm_le_one_of_mem_closedBall (z : UD) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- The point `exp (i θ)` of the unit circle, as an element of the circle. -/
def circleUnit (θ : ℝ) : US :=
  ⟨(Work.CoreTopology.circlePoint θ : ℂ), by
    rw [Metric.mem_sphere, dist_zero_right, Work.CoreTopology.circlePoint_coe,
      Complex.norm_exp_ofReal_mul_I]⟩

theorem sphIncl_circleUnit (θ : ℝ) :
    sphIncl (circleUnit θ) = Work.CoreTopology.circlePoint θ := rfl

theorem exists_circleUnit_eq (u : US) : ∃ θ : ℝ, circleUnit θ = u := by
  have hu : ‖(u : ℂ)‖ = 1 := norm_of_mem_sphere u
  obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq (u : ℂ) hu
  exact ⟨θ, Subtype.ext hθ⟩

theorem continuous_sphIncl : Continuous (sphIncl : US → UD) :=
  Continuous.subtype_mk continuous_subtype_val (fun u => Metric.sphere_subset_closedBall u.2)

/-! ## The boundary circle of a disc map -/

/-- The image of the unit circle under `e`, the *boundary circle* of the disc `e`. -/
abbrev Bdry (e : C(UD, R3)) := Set.range (e ∘ Work.CoreTopology.circlePoint)

/-- The boundary circle, parametrised by the unit circle. -/
noncomputable def bdMap (e : C(UD, R3)) (u : US) : Bdry e :=
  ⟨e (sphIncl u), by
    obtain ⟨θ, hθ⟩ := exists_circleUnit_eq u
    exact ⟨θ, by rw [← hθ]; rfl⟩⟩

theorem bdMap_apply (e : C(UD, R3)) (u : US) : (bdMap e u : R3) = e (sphIncl u) := rfl

theorem continuous_bdMap (e : C(UD, R3)) : Continuous (bdMap e) :=
  Continuous.subtype_mk (e.continuous.comp continuous_sphIncl) _

theorem bdMap_injective (e : C(UD, R3)) (he : Function.Injective e) :
    Function.Injective (bdMap e) := by
  intro u v huv
  have h1 : sphIncl u = sphIncl v := he (congrArg (fun x : Bdry e => (x : R3)) huv)
  exact Subtype.ext (congrArg (fun x : UD => (x : ℂ)) h1)

theorem bdMap_surjective (e : C(UD, R3)) : Function.Surjective (bdMap e) := by
  rintro ⟨y, θ, rfl⟩
  exact ⟨circleUnit θ, Subtype.ext rfl⟩

/-- The boundary circle of an injective disc map is a homeomorphic copy of the circle. -/
noncomputable def bdHomeo (e : C(UD, R3)) (he : Function.Injective e) : US ≃ₜ Bdry e :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (bdMap e) ⟨bdMap_injective e he, bdMap_surjective e⟩)
    (continuous_bdMap e)

theorem bdHomeo_apply (e : C(UD, R3)) (he : Function.Injective e) (u : US) :
    (bdHomeo e he u : R3) = e (sphIncl u) := rfl

/-! ## The reparametrisation of the boundary circle -/

/-- The identity-on-points map between two equal subsets of `ℝ³`. -/
def setCoeMap {s t : Set R3} (h : s = t) (x : s) : t := ⟨(x : R3), h ▸ x.2⟩

theorem setCoeMap_coe {s t : Set R3} (h : s = t) (x : s) : (setCoeMap h x : R3) = (x : R3) :=
  rfl

theorem continuous_setCoeMap {s t : Set R3} (h : s = t) : Continuous (setCoeMap h) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem setCoeMap_injective {s t : Set R3} (h : s = t) : Function.Injective (setCoeMap h) := by
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : t => (z : R3)) hxy)

theorem setCoeMap_surjective {s t : Set R3} (h : s = t) : Function.Surjective (setCoeMap h) := by
  intro y
  refine ⟨⟨(y : R3), h.symm ▸ y.2⟩, Subtype.ext rfl⟩

/-- **The boundary reparametrisation.**  If the two boundary circles coincide as sets, the
circle is matched to itself by the homeomorphism carrying the `eB`-parametrisation to the
`eA`-parametrisation. -/
noncomputable def bdryReparam (eA eB : C(UD, R3)) (hAinj : Function.Injective eA)
    (hBinj : Function.Injective eB) (hbd : Bdry eA = Bdry eB) : US → US :=
  fun u => (bdHomeo eB hBinj).symm (setCoeMap hbd (bdHomeo eA hAinj u))

theorem bdryReparam_spec (eA eB : C(UD, R3)) (hAinj : Function.Injective eA)
    (hBinj : Function.Injective eB) (hbd : Bdry eA = Bdry eB) (u : US) :
    eB (sphIncl (bdryReparam eA eB hAinj hBinj hbd u)) = eA (sphIncl u) := by
  have h1 : bdHomeo eB hBinj (bdryReparam eA eB hAinj hBinj hbd u)
      = setCoeMap hbd (bdHomeo eA hAinj u) :=
    (bdHomeo eB hBinj).apply_symm_apply _
  have h2 := congrArg (fun x : Bdry eB => (x : R3)) h1
  rw [setCoeMap_coe, bdHomeo_apply] at h2
  simpa [bdHomeo_apply] using h2

theorem continuous_bdryReparam (eA eB : C(UD, R3)) (hAinj : Function.Injective eA)
    (hBinj : Function.Injective eB) (hbd : Bdry eA = Bdry eB) :
    Continuous (bdryReparam eA eB hAinj hBinj hbd) :=
  ((bdHomeo eB hBinj).symm.continuous).comp
    ((continuous_setCoeMap hbd).comp (bdHomeo eA hAinj).continuous)

theorem bdryReparam_injective (eA eB : C(UD, R3)) (hAinj : Function.Injective eA)
    (hBinj : Function.Injective eB) (hbd : Bdry eA = Bdry eB) :
    Function.Injective (bdryReparam eA eB hAinj hBinj hbd) :=
  (bdHomeo eB hBinj).symm.injective.comp
    ((setCoeMap_injective hbd).comp (bdHomeo eA hAinj).injective)

theorem bdryReparam_surjective (eA eB : C(UD, R3)) (hAinj : Function.Injective eA)
    (hBinj : Function.Injective eB) (hbd : Bdry eA = Bdry eB) :
    Function.Surjective (bdryReparam eA eB hAinj hBinj hbd) :=
  (bdHomeo eB hBinj).symm.surjective.comp
    ((setCoeMap_surjective hbd).comp (bdHomeo eA hAinj).surjective)

/-! ## The cone over a circle map -/

/-- The direction `z/‖z‖` of a non-zero point of the disc lies on the unit circle. -/
theorem div_norm_mem_sphere (z : UD) (h : (z : ℂ) ≠ 0) :
    (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) ∈ US := by
  rw [Metric.mem_sphere, dist_zero_right, norm_div]
  rw [show ‖(((‖(z : ℂ)‖ : ℝ)) : ℂ)‖ = ‖(z : ℂ)‖ by simp]
  exact div_self (norm_ne_zero_iff.mpr h)

/-- The direction of a non-zero point of the disc: the point of the unit circle it lies over. -/
def dirPt (z : UD) (h : (z : ℂ) ≠ 0) : US :=
  ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), div_norm_mem_sphere z h⟩

theorem dirPt_coe (z : UD) (h : (z : ℂ) ≠ 0) :
    (dirPt z h : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_dirPt (z : UD) (h : (z : ℂ) ≠ 0) : ‖(dirPt z h : ℂ)‖ = 1 :=
  norm_of_mem_sphere _

/-- The total extension of `dirPt` by the junk direction `1` at the origin. -/
noncomputable def dirPtAll (z : UD) : US :=
  if h : (z : ℂ) = 0 then circleUnit 0 else dirPt z h

theorem dirPtAll_of_ne (z : UD) (h : (z : ℂ) ≠ 0) : dirPtAll z = dirPt z h := dif_neg h

theorem dirPtAll_zero : dirPtAll 0 = circleUnit 0 := dif_pos rfl

/-- A point of the disc is its direction scaled by its norm. -/
theorem smul_dirPt (z : UD) (h : (z : ℂ) ≠ 0) :
    (‖(z : ℂ)‖) • ((dirPt z h : US) : ℂ) = (z : ℂ) := by
  rw [dirPt_coe, Complex.real_smul, div_eq_mul_inv, ← mul_assoc,
    mul_comm (((‖(z : ℂ)‖ : ℝ)) : ℂ) (z : ℂ), mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)), mul_one]

/-- The direction of a positive multiple of a point of the circle is that point. -/
theorem dirPt_of_smul (u : US) (t : ℝ) (ht : 0 < t) (z : UD)
    (hz : (z : ℂ) = t • (u : ℂ)) (h : (z : ℂ) ≠ 0) : dirPt z h = u := by
  have hne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  refine Subtype.ext ?_
  rw [dirPt_coe, hz, norm_smul, Real.norm_of_nonneg ht.le, norm_of_mem_sphere, mul_one,
    Complex.real_smul]
  exact mul_div_cancel_left₀ (u : ℂ) hne

/-- The cone `z ↦ ‖z‖ • φ(z/‖z‖)` takes values in the disc. -/
theorem cone_mem (φ : US → US) (z : UD) :
    (‖(z : ℂ)‖) • ((φ (dirPtAll z) : US) : ℂ) ∈ UD := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (norm_nonneg _),
    norm_of_mem_sphere, mul_one]
  exact norm_le_one_of_mem_closedBall z

/-- **The cone** over a map of the circle: `z ↦ ‖z‖ • φ(z/‖z‖)` on the closed unit disc,
with the value `0` at the origin. -/
noncomputable def conePt (φ : US → US) (z : UD) : UD :=
  ⟨(‖(z : ℂ)‖) • ((φ (dirPtAll z) : US) : ℂ), cone_mem φ z⟩

theorem conePt_coe (φ : US → US) (z : UD) :
    (conePt φ z : ℂ) = (‖(z : ℂ)‖) • ((φ (dirPtAll z) : US) : ℂ) := rfl

theorem conePt_norm (φ : US → US) (z : UD) : ‖(conePt φ z : ℂ)‖ = ‖(z : ℂ)‖ := by
  rw [conePt_coe, norm_smul, Real.norm_of_nonneg (norm_nonneg _), norm_of_mem_sphere, mul_one]

theorem conePt_coe_of_ne (φ : US → US) (z : UD) (h : (z : ℂ) ≠ 0) :
    (conePt φ z : ℂ) = (‖(z : ℂ)‖) • ((φ (dirPt z h) : US) : ℂ) := by
  rw [conePt_coe, dirPtAll_of_ne z h]

theorem conePt_zero (φ : US → US) : conePt φ 0 = 0 := by
  refine Subtype.ext ?_
  rw [conePt_coe]
  simp

theorem conePt_circleUnit (φ : US → US) (u : US) :
    conePt φ (sphIncl u) = sphIncl (φ u) := by
  have hne : (sphIncl u : ℂ) ≠ 0 := by
    intro h
    have h1 : ‖(sphIncl u : ℂ)‖ = 0 := by rw [h]; simp
    rw [sphIncl_coe, norm_of_mem_sphere u] at h1
    norm_num at h1
  have hdir : dirPt (sphIncl u) hne = u := by
    refine Subtype.ext ?_
    rw [dirPt_coe, sphIncl_coe, norm_of_mem_sphere u, Complex.ofReal_one, div_one]
  refine Subtype.ext ?_
  rw [conePt_coe_of_ne φ (sphIncl u) hne, hdir, sphIncl_coe, norm_of_mem_sphere u,
    one_smul, sphIncl_coe]

theorem conePt_injective (φ : US → US) (hφ : Function.Injective φ) :
    Function.Injective (conePt φ) := by
  intro z w hzw
  have hnorm : ‖(z : ℂ)‖ = ‖(w : ℂ)‖ := by
    rw [← conePt_norm φ z, ← conePt_norm φ w, hzw]
  by_cases hz : (z : ℂ) = 0
  · have hw : (w : ℂ) = 0 := by
      have h0 : ‖(w : ℂ)‖ = 0 := by rw [← hnorm, hz]; simp
      exact norm_eq_zero.mp h0
    exact Subtype.ext (by rw [hz, hw])
  · have hw : (w : ℂ) ≠ 0 := by
      intro h0
      have h1 : ‖(w : ℂ)‖ = 0 := by rw [h0]; simp
      rw [← hnorm] at h1
      exact hz (norm_eq_zero.mp h1)
    have hval : (‖(z : ℂ)‖) • ((φ (dirPt z hz) : US) : ℂ)
        = (‖(w : ℂ)‖) • ((φ (dirPt w hw) : US) : ℂ) := by
      rw [← conePt_coe_of_ne φ z hz, ← conePt_coe_of_ne φ w hw]
      exact congrArg (fun x : UD => (x : ℂ)) hzw
    rw [Complex.real_smul, Complex.real_smul, ← hnorm] at hval
    have hne : (((‖(z : ℂ)‖ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hφeq : φ (dirPt z hz) = φ (dirPt w hw) :=
      Subtype.ext (mul_left_cancel₀ hne hval)
    have hdir : dirPt z hz = dirPt w hw := hφ hφeq
    refine Subtype.ext ?_
    calc (z : ℂ) = (‖(z : ℂ)‖) • ((dirPt z hz : US) : ℂ) := (smul_dirPt z hz).symm
      _ = (‖(w : ℂ)‖) • ((dirPt w hw : US) : ℂ) := by rw [hdir, hnorm]
      _ = (w : ℂ) := smul_dirPt w hw

theorem conePt_surjective (φ : US → US) (hφ : Function.Surjective φ) :
    Function.Surjective (conePt φ) := by
  intro w
  by_cases hw : (w : ℂ) = 0
  · refine ⟨0, ?_⟩
    rw [conePt_zero]
    exact Subtype.ext (by rw [hw]; rfl)
  · obtain ⟨u, hu⟩ := hφ (dirPt w hw)
    have hnw : 0 < ‖(w : ℂ)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr hw))
    have hmem : (‖(w : ℂ)‖) • (u : ℂ) ∈ UD := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (norm_nonneg _), norm_of_mem_sphere, mul_one]
      exact norm_le_one_of_mem_closedBall w
    let z : UD := ⟨(‖(w : ℂ)‖) • (u : ℂ), hmem⟩
    have hzc : (z : ℂ) = (‖(w : ℂ)‖) • (u : ℂ) := rfl
    have hz : (z : ℂ) ≠ 0 := by
      rw [hzc, Complex.real_smul]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hnw))
        (norm_ne_zero_iff.mp (by rw [norm_of_mem_sphere u]; norm_num))
    have hdir : dirPt z hz = u := dirPt_of_smul u (‖(w : ℂ)‖) hnw z hzc hz
    refine ⟨z, ?_⟩
    refine Subtype.ext ?_
    rw [conePt_coe_of_ne φ z hz, hdir, hzc, norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      norm_of_mem_sphere, mul_one, hu]
    exact smul_dirPt w hw

/-! ### Continuity of the cone -/

/-- The value of the cone at a non-zero point of the disc. -/
noncomputable def coneClean (φ : US → US) (y : {z : UD // (z : ℂ) ≠ 0}) : ℂ :=
  (‖(((y : UD) : ℂ))‖) • ((φ (dirPt (y : UD) y.2) : US) : ℂ)

theorem conePt_coe_subtype (φ : US → US) (y : {z : UD // (z : ℂ) ≠ 0}) :
    (conePt φ (y : UD) : ℂ) = coneClean φ y := by
  rw [conePt_coe_of_ne φ (y : UD) y.2]
  rfl

theorem continuous_coneClean (φ : US → US) (hφ : Continuous φ) : Continuous (coneClean φ) := by
  have hval : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} => ((y : UD) : ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hnorm : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} => ‖((y : UD) : ℂ)‖ :=
    continuous_norm.comp hval
  have hcast : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} => ((‖((y : UD) : ℂ)‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hnorm
  have hdiv : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} =>
      ((y : UD) : ℂ) / ((‖((y : UD) : ℂ)‖ : ℝ) : ℂ) :=
    hval.div hcast (fun y => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr y.2))
  have hdir : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} => dirPt (y : UD) y.2 :=
    Continuous.subtype_mk hdiv (fun y => div_norm_mem_sphere (y : UD) y.2)
  exact hnorm.smul (continuous_subtype_val.comp (hφ.comp hdir))

theorem continuous_conePt (φ : US → US) (hφ : Continuous φ) : Continuous (conePt φ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : (z : ℂ) = 0
  · have hz0 : z = 0 := Subtype.ext (by rw [hz]; rfl)
    have hdist : ∀ y : UD, dist (conePt φ y) (conePt φ z) = dist y z := by
      intro y
      rw [hz0, conePt_zero, Subtype.dist_eq, Subtype.dist_eq]
      show dist ((conePt φ y : ℂ)) 0 = dist ((y : ℂ)) 0
      rw [dist_zero_right, dist_zero_right, conePt_norm]
    rw [Metric.continuousAt_iff]
    intro ε hε
    exact ⟨ε, hε, fun y hy => by rw [hdist y]; exact hy⟩
  · have hopen : IsOpen {y : UD | (y : ℂ) ≠ 0} := isOpen_ne.preimage continuous_subtype_val
    have hmem : ∀ y : {z : UD // (z : ℂ) ≠ 0}, coneClean φ y ∈ UD := by
      intro y
      rw [← conePt_coe_subtype φ y]
      exact (conePt φ (y : UD)).2
    have hOn : ContinuousOn (conePt φ) {y : UD | (y : ℂ) ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hclean : Continuous fun y : {z : UD // (z : ℂ) ≠ 0} =>
          (⟨coneClean φ y, hmem y⟩ : UD) :=
        (continuous_coneClean φ hφ).subtype_mk hmem
      exact hclean.congr (fun y => Subtype.ext (conePt_coe_subtype φ y).symm)
    exact hOn.continuousAt (hopen.mem_nhds hz)

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem isEmbeddedSphere_of_twoDiscs
    (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hAinj : Function.Injective eA) (hBinj : Function.Injective eB)
    (hinter : Set.range eA ∩ Set.range eB = Set.range (eA ∘ Work.CoreTopology.circlePoint))
    (hbd : Set.range (eA ∘ Work.CoreTopology.circlePoint) =
      Set.range (eB ∘ Work.CoreTopology.circlePoint)) :
    Work.InnermostDisk.IsEmbeddedSphere (Set.range eA ∪ Set.range eB) := by
  let φ : US → US := bdryReparam eA eB hAinj hBinj hbd
  have hφi : Function.Injective φ := bdryReparam_injective eA eB hAinj hBinj hbd
  have hφs : Function.Surjective φ := bdryReparam_surjective eA eB hAinj hBinj hbd
  have hφc : Continuous φ := continuous_bdryReparam eA eB hAinj hBinj hbd
  have hφsp : ∀ u : US, eB (sphIncl (φ u)) = eA (sphIncl u) :=
    fun u => bdryReparam_spec eA eB hAinj hBinj hbd u
  let K : C(UD, UD) := ⟨conePt φ, continuous_conePt φ hφc⟩
  have hKsurj : Function.Surjective (⇑K) := conePt_surjective φ hφs
  have hbd' : ∀ θ : ℝ,
      eA (Work.CoreTopology.circlePoint θ) = (eB.comp K) (Work.CoreTopology.circlePoint θ) := by
    intro θ
    show eA (Work.CoreTopology.circlePoint θ) = eB (conePt φ (Work.CoreTopology.circlePoint θ))
    have h1 : conePt φ (Work.CoreTopology.circlePoint θ) = sphIncl (φ (circleUnit θ)) := by
      rw [← sphIncl_circleUnit θ, conePt_circleUnit]
    rw [h1, hφsp (circleUnit θ), sphIncl_circleUnit]
  have hB'inj : Function.Injective (eB.comp K) :=
    hBinj.comp (conePt_injective φ hφi)
  have hint' : ∀ z w : UD, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 →
      eA z = (eB.comp K) w → False := by
    intro z w hz _ heq
    have h1 : eA z ∈ Set.range eA ∩ Set.range eB := ⟨⟨z, rfl⟩, ⟨K w, heq.symm⟩⟩
    have h2 : eA z ∈ Set.range (eA ∘ Work.CoreTopology.circlePoint) := by
      rw [← hinter]; exact h1
    obtain ⟨θ, hθ⟩ := h2
    have hz' : z = Work.CoreTopology.circlePoint θ := hAinj hθ.symm
    have hnorm : ‖(z : ℂ)‖ = 1 := by
      rw [hz', Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    linarith
  have hrange : Set.range (eB.comp K) = Set.range eB := by
    rw [ContinuousMap.coe_comp, Set.range_comp]
    have : Set.range (⇑K) = Set.univ := Set.range_eq_univ.mpr hKsurj
    rw [this, Set.image_univ]
  have key := isEmbeddedSphere_of_doubleDisc eA (eB.comp K) hAinj hB'inj hbd' hint'
  rwa [hrange] at key


end

end Work.Drive.Mono
