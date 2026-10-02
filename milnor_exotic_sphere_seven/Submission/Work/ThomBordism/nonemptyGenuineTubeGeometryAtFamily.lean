import Mathlib
import Submission.Work.ThomBordism.genuineTubeData
import Submission.Work.ThomBordism.genuineTubeDataFamily
import Submission.Work.ThomBordism.nonempty_genuineTubeData
import Submission.Work.ThomBordism.genuineTubeData_zero_mem_core
import Submission.Work.ThomBordism.gaussTubeData
import Submission.Work.ThomBordism.tubeConnProved
import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.TubeAmbientGr
import Submission.Work.PTGeometric.AmbientCoords
import Submission.Work.PTGeometric.ProjOfPlane.Defs
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.tubeChart_mono
import Submission.Work.ThomBordism.Grassmann.projOfPlaneEqIff
import Submission.Work.ThomBordism.padGaussFunM
import Submission.Work.ThomBordism.gtdUWith_eq_of_normalData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# The genuine tube geometry of a finite family of connected closed oriented `8`-manifolds

This file produces `Work.PTGeometric.GenuineTubeGeometry` for a family of connected closed oriented
`8`-manifolds at a prescribed odd codimension `k ≥ 11`, from the TUBULAR half
(`Work.ThomBordism.gaussTubeData`) and the radius-monotonicity of tube charts
(`Work.Tubular.tubeChart_mono`), which makes the tube radii of the members *equal*; the coordinate
reading `Work.PTGeometric.GenuineTubeGeometry.coord` of the concrete Thom space is then a single
map: the ambient coordinates of a point of the total space of the tautological bundle, shrunk back
by the inverse `ε / (ε + ‖v‖)` of the blow-up `Work.Tubular.normalBlowUp` used in the collapsing
map (`Work.Tubular.collapseToOnePoint`).
-/

open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- The concrete universal Thom target used by the family producers. -/
abbrev famTarget (k : ℕ) (hk : 11 ≤ k) : ThomTarget k :=
  connTarget k (by omega) (PhiG k (by omega))

/-- **The total-space point underlying a point of the concrete Thom space different from the base
point.** -/
noncomputable def famUnpack (k : ℕ) :
    {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty} →
      (Grassmann.tautologicalBundle k 10).TotalSpace :=
  fun x => Classical.choose (OnePoint.ne_infty_iff_exists.mp x.2)

theorem famUnpack_spec (k : ℕ)
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty}) :
    (OnePoint.some (famUnpack k x) : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) =
      x.1 :=
  Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp x.2)

theorem continuous_famUnpack (k : ℕ) : Continuous (famUnpack k) := by
  have h : (OnePoint.some : (Grassmann.tautologicalBundle k 10).TotalSpace → _) ∘ famUnpack k
      = Subtype.val := by
    funext x
    exact famUnpack_spec k x
  exact (OnePoint.isOpenEmbedding_coe.toIsEmbedding.continuous_iff (f := famUnpack k)).mpr
    (by rw [h]; exact continuous_subtype_val)

theorem famUnpack_eq_of_eq_some (k : ℕ)
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty})
    {p : (Grassmann.tautologicalBundle k 10).TotalSpace}
    (h : (x.1 : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) = OnePoint.some p) :
    famUnpack k x = p := by
  have h1 := famUnpack_spec k x
  rw [h] at h1
  exact Option.some.inj h1

/-- **The ambient coordinate reading of the concrete Thom space**: for a point different from the
base point, the orthogonal projection onto its plane (padded into the ambient space) and the vector
of the plane shrunk back by `ε / (ε + ‖v‖)` — the inverse of the blow-up
`Work.Tubular.normalBlowUp` that the collapse maps of TUBULAR apply to the normal vector. -/
noncomputable def famCoord (k : ℕ) (ε : ℝ) :
    {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty} →
      ((EuclideanSpace ℝ (Fin (k + 10)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 10))) ×
        EuclideanSpace ℝ (Fin (k + 10))) :=
  fun x =>
    (Work.PTGeometric.projOfPlane k 10
        ((Grassmann.tautologicalBundle k 10).proj (famUnpack k x)),
      (ε / (ε + ‖Grassmann.evalVec (famUnpack k x)‖)) • Grassmann.evalVec (famUnpack k x))

/-- The oriented plane of a point of the concrete Thom space different from the base point. -/
noncomputable def famGauss (k : ℕ) :
    {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty} →
      Grassmann.OG k 10 :=
  fun x => (Grassmann.tautologicalBundle k 10).proj (famUnpack k x)

/-- The core of the concrete Thom space: the points whose (shrunk) vector part vanishes. -/
def famCore (k : ℕ) (ε : ℝ) : Set (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) :=
  {x | ∃ h : x ≠ OnePoint.infty, (famCoord k ε ⟨x, h⟩).2 = 0}

theorem continuous_famCoord {k : ℕ} {ε : ℝ} (hε : 0 < ε) : Continuous (famCoord k ε) := by
  refine Continuous.prodMk ?_ ?_
  · exact (Work.PTGeometric.continuous_projOfPlane k 10).comp
      ((Grassmann.tautologicalBundle k 10).continuous_proj.comp (continuous_famUnpack k))
  · have hv : Continuous fun x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace //
        x ≠ OnePoint.infty} => Grassmann.evalVec (famUnpack k x) :=
      Grassmann.continuous_evalVec.comp (continuous_famUnpack k)
    have hc : Continuous fun x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace //
        x ≠ OnePoint.infty} => (ε : ℝ) / (ε + ‖Grassmann.evalVec (famUnpack k x)‖) :=
      Continuous.div continuous_const
        (continuous_const.add (continuous_norm.comp hv))
        (fun x => by
          have h3 : 0 ≤ ‖Grassmann.evalVec (famUnpack k x)‖ := norm_nonneg _
          exact ne_of_gt (by linarith))
    exact hc.smul hv

theorem continuous_famGauss (k : ℕ) : Continuous (famGauss k) :=
  (Grassmann.tautologicalBundle k 10).continuous_proj.comp (continuous_famUnpack k)

theorem famCoord_isProj {k : ℕ} {ε : ℝ}
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty}) :
    (famCoord k ε x).1 ∈ Work.PTGeometric.Gr (k + 10) k :=
  Work.PTGeometric.projOfPlane_mem_Gr k 10 _

theorem famGauss_proj {k : ℕ} {ε : ℝ}
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty}) :
    Work.PTGeometric.projOfPlane k 10 (famGauss k x) = (famCoord k ε x).1 := rfl

theorem famCoord_mem {k : ℕ} {ε : ℝ}
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty}) :
    (famCoord k ε x).1 ((famCoord k ε x).2) = (famCoord k ε x).2 := by
  have hfix : Work.PTGeometric.projOfPlane k 10 (famGauss k x)
      (Grassmann.evalVec (famUnpack k x)) = Grassmann.evalVec (famUnpack k x) :=
    (Work.PTGeometric.projOfPlane_fixed_iff k 10 (famGauss k x) _).mpr
      (Grassmann.evalVec_memPlane (famUnpack k x))
  change Work.PTGeometric.projOfPlane k 10 (famGauss k x)
      ((ε / (ε + ‖Grassmann.evalVec (famUnpack k x)‖)) • Grassmann.evalVec (famUnpack k x)) =
    (ε / (ε + ‖Grassmann.evalVec (famUnpack k x)‖)) • Grassmann.evalVec (famUnpack k x)
  rw [map_smul, hfix]

theorem famCoord_snd_eq_zero_iff {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : {x : OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace // x ≠ OnePoint.infty}) :
    (famCoord k ε x).2 = 0 ↔ Grassmann.evalVec (famUnpack k x) = 0 := by
  have hne : ε / (ε + ‖Grassmann.evalVec (famUnpack k x)‖) ≠ 0 := by
    have h2 : 0 < ε + ‖Grassmann.evalVec (famUnpack k x)‖ := by
      have h3 : 0 ≤ ‖Grassmann.evalVec (famUnpack k x)‖ := norm_nonneg _
      linarith
    exact div_ne_zero (ne_of_gt hε) (ne_of_gt h2)
  constructor
  · intro h
    by_contra hw
    exact hne (by rw [famCoord, smul_eq_zero] at h; exact h.resolve_right hw)
  · intro h
    simp [famCoord, h]

theorem famCore_eq (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    famCore k ε = OnePoint.some ''
      {p : (Grassmann.tautologicalBundle k 10).TotalSpace | Grassmann.evalVec p = 0} := by
  ext x
  constructor
  · rintro ⟨h, hh⟩
    have h1 := famUnpack_spec k ⟨x, h⟩
    have h2 := (famCoord_snd_eq_zero_iff (k := k) hε ⟨x, h⟩).mp hh
    exact ⟨famUnpack k ⟨x, h⟩, h2, h1⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : Grassmann.evalVec p = 0 := hp
    refine ⟨OnePoint.coe_ne_infty p, ?_⟩
    have h1 : famUnpack k ⟨OnePoint.some p, OnePoint.coe_ne_infty p⟩ = p :=
      famUnpack_eq_of_eq_some k _ rfl
    change (ε / (ε + ‖Grassmann.evalVec (famUnpack k ⟨↑p, _⟩)‖)) •
      Grassmann.evalVec (famUnpack k ⟨↑p, _⟩) = 0
    rw [h1, hp', smul_zero]

theorem isClosed_famCore (k : ℕ) (ε : ℝ) (hε : 0 < ε) : IsClosed (famCore k ε) := by
  haveI : CompactSpace (Grassmann.OG k 10) := Grassmann.instCompactSpaceOG k 10
  rw [famCore_eq k hε]
  refine OnePoint.isClosed_image_coe.mpr ⟨?_, ?_⟩
  · exact isClosed_singleton.preimage Grassmann.continuous_evalVec
  · have h1 : {p : (Grassmann.tautologicalBundle k 10).TotalSpace | Grassmann.evalVec p = 0}
        = Set.range (Work.Thom.zeroSection (Grassmann.tautologicalBundle k 10)) := by
      ext p
      constructor
      · intro hp
        obtain ⟨b, v⟩ := p
        have hp' : v = 0 := by
          have h := hp
          rw [Set.mem_ofPred_eq] at h
          rwa [Grassmann.evalVec_eq_zero_iff] at h
        refine ⟨b, ?_⟩
        rw [Work.Thom.zeroSection_apply, hp']
      · rintro ⟨b, rfl⟩
        show Grassmann.evalVec ((Work.Thom.zeroSection _) b) = 0
        rw [Work.Thom.zeroSection_apply]
        exact (Grassmann.evalVec_eq_zero_iff _).mpr rfl
    rw [h1]
    exact isCompact_range (Work.Thom.zeroSection _).continuous

theorem t0_notMem_famCore (k : ℕ) (ε : ℝ) : OnePoint.infty ∉ famCore k ε := by
  rintro ⟨h, -⟩
  exact h rfl

/-- **The family data of the tube charts**: at a common positive radius `ε` and a common box radius
`R`, one embedding, tube chart, normal sphere point and collapsing map per member. -/
theorem exists_familyTubeData {k : ℕ} (hk : 11 ≤ k)
    {ι : Type} [Fintype ι] (F : ι → Man8) (hconn : ∀ i, ConnectedSpace (F i).pt)
    (hE : ∀ i, Nonempty (EmbeddingData (F i) (8 + k))) :
    ∃ (emb : ∀ i, EmbeddingData (F i) (8 + k)) (ε : ℝ) (hε : 0 < ε)
      (chart : ∀ i, Work.Tubular.TubeChart (emb i) ε)
      (q : ∀ i, Work.Tubular.NormalSphSub (emb i) ε)
      (R : ℝ) (hR : 0 ≤ R)
      (hbox : ∀ i, ∀ y ∈ (chart i).U, ∀ j : Fin (8 + k), |y j| < R)
      (g : ∀ i, C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal (emb i))))
      (hg : ∀ i, ∀ y, y ∉ (chart i).openTube → g i (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ i, ∀ y, y ∈ (chart i).openTube →
        g i (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp (emb i) ε
          ((chart i).inv y))),
      True := by
  classical
  haveI : ∀ i, Nonempty (F i).pt := fun i => (hconn i).toNonempty
  let emb : ∀ i, EmbeddingData (F i) (8 + k) := fun i => Classical.choice (hE i)
  choose ε₀ hε₀ hC₀ using fun i => Work.Tubular.hasTubularNeighbourhood (emb i)
  set S : ℝ := ∑ i, (ε₀ i)⁻¹ with hS
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hε₀ i).le)
  have hSpos : 0 < 1 + S := by linarith
  have hε : 0 < 1 / (1 + S) := by positivity
  have hle : ∀ i, 1 / (1 + S) ≤ ε₀ i := by
    intro i
    rw [div_le_iff₀ hSpos]
    have hmem : (ε₀ i)⁻¹ ≤ S := by
      rw [hS]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (ε₀ j)⁻¹)
        (fun j _ => inv_nonneg.mpr (hε₀ j).le) (Finset.mem_univ i)
    have hpos : 0 < ε₀ i := hε₀ i
    have h2 : 1 ≤ ε₀ i * S := by
      calc (1 : ℝ) = ε₀ i * (ε₀ i)⁻¹ := (mul_inv_cancel₀ (ne_of_gt hpos)).symm
        _ ≤ ε₀ i * S := mul_le_mul_of_nonneg_left hmem hpos.le
    nlinarith
  let chart : ∀ i, Work.Tubular.TubeChart (emb i) (1 / (1 + S)) := fun i =>
    Classical.choice (Work.Tubular.tubeChart_mono (Classical.choice (hC₀ i)) hε (hle i))
  haveI : ∀ i, CompactSpace (Work.Tubular.NormalDiscSub (emb i) (1 / (1 + S))) :=
    fun i => Work.Tubular.compactSpace_normalDiscSub (emb i) (1 / (1 + S))
  let q : ∀ i, Work.Tubular.NormalSphSub (emb i) (1 / (1 + S)) := fun i =>
    Classical.choice (Work.Tubular.nonempty_normalSphSub (emb i) hε (by omega))
  let g : ∀ i, C(OnePoint (Work.Tubular.Euc (8 + k)),
      OnePoint (Work.Tubular.NormalTotal (emb i))) := fun i =>
    (Classical.choice (Work.Tubular.collapseToOnePoint (emb i) (chart i) (q i)
      (chart i).isCompact_U)).1
  have hgall : ∀ i, (∀ y, y ∈ (chart i).openTube →
        g i (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp (emb i) (1 / (1 + S))
          ((chart i).inv y))) ∧
      (∀ y, y ∉ (chart i).openTube → g i (OnePoint.some y) = OnePoint.infty) ∧
      g i OnePoint.infty = OnePoint.infty := fun i =>
    (Classical.choice (Work.Tubular.collapseToOnePoint (emb i) (chart i) (q i)
      (chart i).isCompact_U)).2
  choose R hR hbox using fun i => (chart i).exists_box
  refine ⟨emb, 1 / (1 + S), hε, chart, q, 1 + ∑ i, R i, ?_, ?_, g,
    fun i => (hgall i).2.1, fun i => (hgall i).1, trivial⟩
  · exact add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => (hR i).le))
  · intro i y hy j
    have h1 : |y j| < R i := (hbox i) y hy j
    have h2 : R i ≤ ∑ i, R i := Finset.single_le_sum (fun i _ => (hR i).le) (Finset.mem_univ i)
    linarith

/-- **The tie of the produced normal data with the oriented Gauss data** (the filling of the
`tie` field of `Work.PTGeometric.GenuineTubeGeometry`): for the producer's normal data `ND`,
bundle maps `Gc` and classifying maps `J`, the oriented plane `Work.ThomBordism.famGauss` of the
collapse at a tube point is the padded `σ`-corrected Gauss plane
`Work.ThomBordism.padGaussFunM` of the **same** normal data at the foot of the tube point, up to the
global orientation flip `Work.ThomBordism.Grassmann.ogFlip`.

The proof is the comparison of the two `projOfPlane` values
(`Work.ThomBordism.Grassmann.projOfPlaneEqIff`): `coord_collapse`'s pointwise data (`hval`) give
`projOfPlane (famGauss …) = padEndEuc (tubeNormalProj …)`, and
`Work.ThomBordism.projOfPlane_padGaussM` gives the same for the padded Gauss plane — the two
expressions are *definitionally* equal because `Work.PTGeometric.tubeNormalProj` **is**
`padEndEuc` of the orthogonal projection onto the normal space at the foot. -/
theorem gtdTiedGaussNormal {k : ℕ} (hk : 11 ≤ k) {ι : Type} [Fintype ι] (F : ι → Man8)
    (emb : ∀ i, Work.ThomBordism.PontryaginThom.EmbeddingData (F i) (8 + k)) (ε : ℝ)
    (hε : 0 < ε) (chart : ∀ i, Work.Tubular.TubeChart (emb i) ε)
    (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ i, ∀ y ∈ (chart i).U, ∀ j : Fin (8 + k), |y j| < R)
    (g : ∀ i, C(OnePoint (Work.Tubular.Euc (8 + k)),
      OnePoint (Work.Tubular.NormalTotal (emb i))))
    (hg : ∀ i, ∀ y, y ∉ (chart i).openTube → g i (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ i, ∀ y, y ∈ (chart i).openTube →
      g i (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp (emb i) ε
        ((chart i).inv y)))
    (ND : ∀ i, Work.ThomBordism.PontryaginThom.NormalData (F i) k (emb i).e)
    (Gc : ∀ i, C((Work.Tubular.normalBundle (emb i) (ND i)).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ i p, p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle (emb i) (ND i)) →
      Gc i p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (J : ∀ i, C(OnePoint (Work.Tubular.NormalTotal (emb i)), (famTarget k hk).T))
    (hJ : ∀ i, J i OnePoint.infty = (famTarget k hk).t₀)
    (hval : ∀ i (y : Work.Tubular.Euc (8 + k)), y ∈ (chart i).openTube →
      ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
        J i (OnePoint.some (Work.Tubular.normalBlowUp (emb i) ε ((chart i).inv y)))
            = OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p)
          = Work.PTGeometric.padEndEuc k 10 (by norm_num)
              (Work.PTGeometric.tubeNormalProj (emb i) (chart i) y) ∧
        Work.ThomBordism.Grassmann.evalVec p
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.normalBlowUp (emb i) ε ((chart i).inv y)).1.2) :
    ∀ i, Work.PTGeometric.TiedGaussNormal (famTarget k hk) (F i) (emb i) (chart i) R hR
      (hbox i) (J i) (hJ i) (g i) (hg i)
      (Work.ThomBordism.gtdU (emb i) (ND i) (Gc i) (hgm i)) 10 (by norm_num)
      (fun x : {z : (famTarget k hk).T // z ≠ (famTarget k hk).t₀} => famGauss k ⟨x.1, x.2⟩) := by
  intro i
  refine ⟨ND i, Gc i, hgm i, rfl, fun t ht => ?_⟩
  obtain ⟨p, hpJ, hp1, -⟩ := hval i (Work.Tubular.cubeToEuc (8 + k) R t) ht
  have hα : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
      (g i) (hg i) t = OnePoint.some p := by
    show J i (g i (OnePoint.some (Work.Tubular.cubeToEuc (8 + k) R t))) = OnePoint.some p
    rw [hg2 i (Work.Tubular.cubeToEuc (8 + k) R t) ht]
    exact hpJ
  have hne : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
      (g i) (hg i) t ≠ (famTarget k hk).t₀ := by
    rw [hα]
    exact OnePoint.coe_ne_infty p
  refine ⟨hne, ?_⟩
  have hpt : famUnpack k ⟨Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀
      (J i) (hJ i) (g i) (hg i) t, hne⟩ = p :=
    famUnpack_eq_of_eq_some k _ hα
  have hfam : (fun x : {z : (famTarget k hk).T // z ≠ (famTarget k hk).t₀} => famGauss k ⟨x.1, x.2⟩) ⟨Work.Tubular.alphaV (chart i) hR (hbox i)
      (famTarget k hk).t₀ (J i) (hJ i) (g i) (hg i) t, hne⟩
      = (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p := by
    show (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
      (famUnpack k ⟨Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀
        (J i) (hJ i) (g i) (hg i) t, hne⟩) = _
    rw [hpt]
  have h2 : Work.PTGeometric.projOfPlane k 10
      (Work.ThomBordism.padGaussFunM (emb i) (ND i) 10 (by norm_num)
        ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1)
      = Work.PTGeometric.padEndEuc k 10 (by norm_num)
          (((Work.Tubular.normalSpace (emb i)
              ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1).subtypeL).comp
            ((Work.Tubular.normalSpace (emb i)
              ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1).orthogonalProjectionOnto)) :=
    Work.ThomBordism.projOfPlane_padGaussM (emb i) (ND i) 10 (by norm_num) _
  have h3 : Work.PTGeometric.padEndEuc k 10 (by norm_num)
        (((Work.Tubular.normalSpace (emb i)
            ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1).subtypeL).comp
          ((Work.Tubular.normalSpace (emb i)
            ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1).orthogonalProjectionOnto))
      = Work.PTGeometric.padEndEuc k 10 (by norm_num)
        (Work.PTGeometric.tubeNormalProj (emb i) (chart i)
          (Work.Tubular.cubeToEuc (8 + k) R t)) := rfl
  have hproj : Work.PTGeometric.projOfPlane k 10
      ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p)
      = Work.PTGeometric.projOfPlane k 10
        (Work.ThomBordism.padGaussFunM (emb i) (ND i) 10 (by norm_num)
          ((chart i).inv (Work.Tubular.cubeToEuc (8 + k) R t)).1.1) :=
    hp1.trans (h2.trans h3).symm
  have hdisj := (Work.ThomBordism.Grassmann.projOfPlaneEqIff k 10 _ _).mp hproj
  rcases hdisj with h | h
  · exact Or.inl (hfam.trans h)
  · exact Or.inr (hfam.trans h)

/-- **The genuine tube geometry of a finite family of connected closed oriented `8`-manifolds**, at a
prescribed odd codimension `k ≥ 11` above the family's embedding bound. -/
theorem nonemptyGenuineTubeGeometryAtFamily {k : ℕ} (hk : 11 ≤ k) (hodd : Odd k)
    {ι : Type} [Fintype ι] (F : ι → Man8) (hconn : ∀ i, ConnectedSpace (F i).pt)
    (hE : ∀ i, Nonempty (Work.ThomBordism.PontryaginThom.EmbeddingData (F i) (8 + k))) :
    Nonempty (Work.PTGeometric.GenuineTubeGeometry k
      (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) ι F) := by
  classical
  obtain ⟨emb, ε, hε, chart, q, R, hR, hbox, g, hg, hg2, -⟩ := exists_familyTubeData hk F hconn hE
  haveI : ∀ i, CompactSpace (Work.Tubular.NormalDiscSub (emb i) ε) :=
    fun i => Work.Tubular.compactSpace_normalDiscSub (emb i) ε
  have hchild : ∀ i, ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData (F i) k (emb i).e)
      (G : C((Work.Tubular.normalBundle (emb i) ND).TotalSpace,
        (Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle (emb i) ND),
        G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
      (hld : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal (emb i))),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal (emb i)))
          (Work.Tubular.normalNonzero (emb i)) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal (emb i)))
            (Work.Tubular.normalNonzero (emb i)) 8 k x
            (Work.ThomBordism.gtdU (emb i) ND G hgm)))
          (Work.Tubular.collapseRelK8 (chart i) (g i) (hg i) hR (hbox i))
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (F i).pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal (emb i)) ℤ 8).hom x) (F i).c)
      (J : C(OnePoint (Work.Tubular.NormalTotal (emb i)),
        (famTarget k hk).T)) (hJ : J OnePoint.infty = (famTarget k hk).t₀)
      (rep : Work.Tubular.TubeThomRep k (famTarget k hk) (F i)
        (Work.PTGeometric.canonicalNormal (F i))),
      rep.collapse = GenLoop.congr (famTarget k hk).t₀ (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ J hJ (g i) (hg i)) ∧
      (∀ y ∈ (chart i).openTube, ∃ p : (Grassmann.tautologicalBundle k 10).TotalSpace,
        J (OnePoint.some (Work.Tubular.normalBlowUp (emb i) ε ((chart i).inv y))) =
          OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10 ((Grassmann.tautologicalBundle k 10).proj p)
          = Work.PTGeometric.padEndEuc k 10 (by norm_num)
            (Work.PTGeometric.tubeNormalProj (emb i) (chart i) y) ∧
        Grassmann.evalVec p = Work.PTGeometric.padEuc k 10 (by norm_num)
          ((Work.Tubular.normalBlowUp (emb i) ε ((chart i).inv y)).1.2) ∧
        p = G (Work.Tubular.normalToBundle (emb i) ND
          (Work.Tubular.normalBlowUp (emb i) ε ((chart i).inv y)))) ∧
      (∃ (σ : ℤ), (σ = 1 ∨ σ = -1) ∧
        (∀ p : (Work.Tubular.normalBundle (emb i) ND).TotalSpace,
          (Grassmann.tautologicalBundle k 10).proj (G p)
            = (if σ = 1 then id else Grassmann.ogFlip k 10)
              (Grassmann.padGaussFun (emb i) ND p.1)) ∧
        (∀ p : (Work.Tubular.normalBundle (emb i) ND).TotalSpace,
          Grassmann.evalVec (G p) = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal (emb i) ND p)))) := fun i =>
    gaussTubeData hk hodd (emb i) (Work.PTGeometric.canonicalNormal (F i)) hε (chart i) (q i)
      (chart i).isCompact_U hR (hbox i) (g i) (hg i) (hg2 i)
  choose NDfam Gfam hgmFam hldFam J hJ rep hgeom hval hsig using hchild
  let hTD : ∀ i, GenuineTubeData (F i) k (famTarget k hk)
      (Work.PTGeometric.canonicalNormal (F i)) := fun i =>
    { emb := emb i
      ε := ε
      hε := hε
      chart := chart i
      q := q i
      R := R
      hR := hR
      hbox := hbox i
      J := J i
      hJ := hJ i
      g := g i
      hg := hg i
      rep := rep i
      isGeom := hgeom i }
  have hcc : ∀ i (t : Fin (8 + k) → unitInterval),
      Work.Tubular.cubeToEuc (8 + k) R t ∈ (chart i).openTube →
      ∃ hne : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
          (g i) (hg i) t ≠ (famTarget k hk).t₀,
        famCoord k ε ⟨_, hne⟩ =
          (Work.PTGeometric.padEndEuc k 10 (by norm_num)
              (Work.PTGeometric.tubeNormalProj (emb i) (chart i)
                (Work.Tubular.cubeToEuc (8 + k) R t)),
            Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.PTGeometric.tubeNormalCoord (emb i) (chart i)
                (Work.Tubular.cubeToEuc (8 + k) R t))) := by
    intro i t ht
    set y := Work.Tubular.cubeToEuc (8 + k) R t with hy
    obtain ⟨p, hpJ, hp1, hp2, -⟩ := hval i y ht
    have hα : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
        (g i) (hg i) t = OnePoint.some p := by
      show J i (g i (OnePoint.some y)) = OnePoint.some p
      rw [hg2 i y ht, hpJ]
    have hne : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
        (g i) (hg i) t ≠ (famTarget k hk).t₀ := by
      intro h
      exact OnePoint.coe_ne_infty p (hα ▸ h)
    refine ⟨hne, ?_⟩
    have hpt : famUnpack k ⟨Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i)
        (hJ i) (g i) (hg i) t, hne⟩ = p :=
      famUnpack_eq_of_eq_some k _ hα
    rw [famCoord, hpt]
    refine Prod.ext hp1 ?_
    rw [hp2]
    -- the vector part: the shrink cancels the blow-up
    rw [Work.Tubular.normalBlowUp_vec]
    have hr : 0 ≤ ‖((chart i).inv y).1.2‖ := norm_nonneg _
    have hrlt : ‖((chart i).inv y).1.2‖ < ε := by
      have h1 := ht
      rw [Work.Tubular.TubeChart.openTube_eq] at h1
      exact h1.2
    have hbpos : 0 < Work.Tubular.blowCoeff (emb i) ε ((chart i).inv y) :=
      Work.Tubular.blowCoeff_pos hε hrlt
    have hbval : Work.Tubular.blowCoeff (emb i) ε ((chart i).inv y)
        = ε / (ε - ‖((chart i).inv y).1.2‖) := by
      rw [Work.Tubular.blowCoeff, div_eq_mul_inv]
      rfl
    have hkey : (ε / (ε + Work.Tubular.blowCoeff (emb i) ε ((chart i).inv y)
          * ‖((chart i).inv y).1.2‖)) * Work.Tubular.blowCoeff (emb i) ε ((chart i).inv y) = 1 := by
      rw [hbval]
      have h1 : ε - ‖((chart i).inv y).1.2‖ ≠ 0 := by linarith
      have h2 : ε + ε / (ε - ‖((chart i).inv y).1.2‖) * ‖((chart i).inv y).1.2‖ ≠ 0 := by
        have h3 : 0 < ε / (ε - ‖((chart i).inv y).1.2‖) := by positivity
        nlinarith
      field_simp
      rw [sub_add_cancel, div_self hε.ne']
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hbpos, Work.PTGeometric.norm_padEuc,
      smul_smul, hkey, one_smul]
    rfl
  exact ⟨{ rep := fun i => rep i
           emb := emb
           hconn := hconn
           ε := fun _ => ε
           hε := fun _ => hε
           chart := chart
           q := q
           R := R
           hR := hR
           hbox := hbox
           J := J
           hJ := hJ
           g := g
           hg := hg
           hg2 := hg2
           pulledThom := fun i =>
             Work.ThomBordism.gtdU (emb i) (NDfam i) (Gfam i) (hgmFam i)
           localDegree := fun i x => hldFam i x
           isGeom := fun i t => by
             rw [hgeom i]
             refine congrArg (fun (l : Fin (8 + k) → unitInterval) =>
               (Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
                 (g i) (hg i)) l) ?_
             funext m
             exact congrArg t (Fin.ext rfl)
           core := famCore k ε
           zero := fun i t => by
             exact genuineTubeData_zero_mem_core (hTD i) (mU := 10) (by norm_num)
               (famCore k ε) (t0_notMem_famCore k ε) (famCoord k ε)
               (fun x => ⟨fun hx => hx.choose_spec, fun hx => ⟨x.2, hx⟩⟩)
               (fun t ht => hcc i t ht) t
           mU := 10
           hmU := by norm_num
           coord := fun x => famCoord k ε ⟨x.1, x.2⟩
           continuous_coord := (continuous_famCoord (k := k) hε).comp
             (Continuous.subtype_mk continuous_subtype_val _)
           coord_collapse := fun i t ht => hcc i t ht
           core_iff_vec := fun x => ⟨fun hx => hx.choose_spec, fun hx => ⟨x.2, hx⟩⟩
           isClosed_core := isClosed_famCore k ε hε
           t0_notMem_core := t0_notMem_famCore k ε
           coord_isProj := fun x => famCoord_isProj (k := k) (ε := ε) _
           coord_mem := fun x => famCoord_mem (k := k) (ε := ε) _
           gauss := fun x => famGauss k ⟨x.1, x.2⟩
           continuous_gauss := (continuous_famGauss k).comp
             (Continuous.subtype_mk continuous_subtype_val _)
           tie := fun i => gtdTiedGaussNormal (hk := hk) (F := F) (emb := emb) (ε := ε)
             (hε := hε) (chart := chart) (R := R) (hR := hR) (hbox := hbox) (g := g) (hg := hg)
             (hg2 := hg2) (ND := NDfam) (Gc := Gfam) (hgm := hgmFam) (J := J) (hJ := hJ)
             (hval := fun i y hy =>
                let ⟨p, h1, h2, h3, _⟩ := hval i y hy
                ⟨p, h1, h2, h3⟩) i
           pulledThom_gauss := fun i => by
             obtain ⟨sg, hsg, hplane, hvec⟩ := hsig i
             refine ⟨NDfam i, Gfam i, hgmFam i, sg, hsg, rfl, hplane, hvec, ?_⟩
             intro t ht
             obtain ⟨p, hpJ, -, -, hp3⟩ := hval i (Work.Tubular.cubeToEuc (8 + k) R t) ht
             have hα : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i) (hJ i)
                 (g i) (hg i) t = OnePoint.some p := by
               show J i (g i (OnePoint.some (Work.Tubular.cubeToEuc (8 + k) R t)))
                 = OnePoint.some p
               rw [hg2 i (Work.Tubular.cubeToEuc (8 + k) R t) ht, hpJ]
             have hne : Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀ (J i)
                 (hJ i) (g i) (hg i) t ≠ (famTarget k hk).t₀ := by
               rw [hα]
               exact OnePoint.coe_ne_infty p
             refine ⟨hne, ?_⟩
             have hpt : famUnpack k ⟨Work.Tubular.alphaV (chart i) hR (hbox i) (famTarget k hk).t₀
                 (J i) (hJ i) (g i) (hg i) t, hne⟩ = p :=
               famUnpack_eq_of_eq_some k _ hα
             simp only [famGauss]
             rw [hpt, hp3, hplane]
             rw [Work.ThomBordism.padGaussFun_eq_padGaussFunM]
             rfl
           gauss_proj := fun x => famGauss_proj (k := k) (ε := ε) _ }⟩

end

end Work.ThomBordism
