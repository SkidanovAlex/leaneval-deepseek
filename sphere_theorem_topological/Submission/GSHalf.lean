import Submission.GSHalfDisk
import Submission.GSStep1
import Submission.GSSlab
import Submission.Commons.Topology.Sphere.disk_glue_collar

/-!
# The half-disk theorem `{d(p,·) ≤ b} ≃ Dⁿ`

Let `(p,q)` be a diameter pair of a compact Riemannian manifold with `sec ∈ (1,4]` and
`π/2 < D = d(p,q) ≤ 2π/3` (the restricted Grove–Shiohama range).  Then for every `0 < b < D` the
closed metric ball `{d(p,·) ≤ b}` is homeomorphic to the standard disk `Dⁿ`, and the homeomorphism
can be chosen so that the sphere `{d(p,·) = b}` corresponds to the boundary sphere.

Proof: choose `0 < t < b` smaller than the disk radius of `GSDisk`, so that `{d(p,·) ≤ t}` is a disk
(`GSHalfDisk.exists_homeo_closedBall_pair_of_radius_toReal`) and the slab `{t ≤ d(p,·) ≤ b}` is a
collar `{d(p,·) = t} × [0, b-t]` (`GSSlab.homeo_level_region_of_diam_formula`, where the fibre
coordinate is `d(p,·) - t`).  Gluing the disk to the collar along the common level set `{d(p,·) = t}`
(`Commons.Topology.Sphere.disk_glue_collar`) gives the conclusion; the collar's *far* end is the
level `{d(p,·) = b}`, which is where the boundary must go.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSHalf

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The rescaling homeomorphism `[0,c] ≅ [0,1]`, `s ↦ s/c`. -/
noncomputable def iccRescale (c : ℝ) (hc : 0 < c) :
    Set.Icc (0:ℝ) c ≃ₜ Set.Icc (0:ℝ) 1 where
  toFun s := ⟨s.1 / c, div_nonneg s.2.1 hc.le, (div_le_one hc).mpr s.2.2⟩
  invFun u := ⟨u.1 * c, mul_nonneg u.2.1 hc.le, by nlinarith [u.2.2, hc]⟩
  left_inv s := by ext; simp only [Set.mem_Icc]; field_simp
  right_inv u := by ext; simp only [Set.mem_Icc]; field_simp
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.div_const c) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.mul_const c) _

@[simp] lemma iccRescale_coe (c : ℝ) (hc : 0 < c) (s : Set.Icc (0:ℝ) c) :
    ((iccRescale c hc s : Set.Icc (0:ℝ) 1) : ℝ) = (s : ℝ) / c := rfl

lemma iccRescale_eq_one_iff {c : ℝ} (hc : 0 < c) (u : Set.Icc (0:ℝ) c) :
    ((iccRescale c hc u : Set.Icc (0:ℝ) 1) : ℝ) = 1 ↔ (u : ℝ) = c := by
  rw [iccRescale_coe, div_eq_one_iff_eq hc.ne']

lemma iccRescale_eq_zero_iff {c : ℝ} (hc : 0 < c) (u : Set.Icc (0:ℝ) c) :
    ((iccRescale c hc u : Set.Icc (0:ℝ) 1) : ℝ) = 0 ↔ (u : ℝ) = 0 := by
  rw [iccRescale_coe, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hc.ne'
  · intro h; exact Or.inl h

/-- **The half-disk theorem.**  For a diameter pair `(p,q)` with `π/2 < d(p,q) ≤ 2π/3` and
`0 < b < d(p,q)`, the closed ball `{d(p,·) ≤ b}` is a topological disk, with `{d(p,·) = b}`
corresponding to the boundary sphere. -/
theorem exists_homeo_halfdisk
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D b : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hbpos : 0 < b) (hbD : b < D) :
    ∃ e : ↥{y : M | (Manifold.riemannianEDist I p y).toReal ≤ b} ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1,
      e ⁻¹' (Metric.sphere (0 : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
        = {y : ↥{y : M | (Manifold.riemannianEDist I p y).toReal ≤ b} |
            (Manifold.riemannianEDist I p (y : M)).toReal = b} := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  set f : M → ℝ := fun y => (Manifold.riemannianEDist I p y).toReal with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 hfin
  -- the small disk radius
  obtain ⟨ε₀, hε₀, hchart⟩ :=
    Submission.GSHalfDisk.exists_homeo_closedBall_pair_of_radius_toReal (cov := cov) hmet htor p
  set t : ℝ := min ε₀ b / 2 with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos (lt_min hε₀ hbpos) two_pos
  have htε : t < ε₀ := by
    rw [htdef]; have := min_le_left ε₀ b; linarith
  have htb : t < b := by
    rw [htdef]; have := min_le_right ε₀ b; linarith
  obtain ⟨eT, heT⟩ := hchart t ⟨htpos, htε⟩
  -- the collar
  obtain ⟨Φ, hΦ⟩ := Submission.GSSlab.homeo_level_region_of_diam_formula (cov := cov) hmet htor
    hpinch hdiam hDgt hDlt hpq (a' := t/2) (b' := (b + D)/2) (a := t) (b := b)
    (by linarith) (by linarith) (by linarith) (by linarith) htb (by linarith)
  set X : Set M := {y : M | f y ≤ b} with hXdef
  have hXclosed : IsClosed X := isClosed_Iic.preimage hfcont
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXclosed.isCompact
  -- the two pieces
  set A : Set ↥X := {x : ↥X | (x : M) ∈ {y : M | f y ≤ t}} with hAdef
  set C : Set ↥X := {x : ↥X | (x : M) ∈ {y : M | t ≤ f y ∧ f y ≤ b}} with hCdef
  have hAclosed : IsClosed A := isClosed_Iic.preimage (hfcont.comp continuous_subtype_val)
  have hCclosed : IsClosed C :=
    isClosed_Icc.preimage (hfcont.comp continuous_subtype_val)
  have hAC : A ∪ C = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : f (x : M) ≤ t
    · exact Or.inl hx
    · exact Or.inr ⟨le_of_lt (not_le.mp hx), Set.mem_ofPred_eq.mpr x.2⟩
  have hAintC : A ∩ C = {x : ↥X | f (x : M) = t} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact le_antisymm h1 h2
    · intro h
      exact ⟨le_of_eq h, le_of_eq h.symm, x.2⟩
  -- the disk chart on `A`
  have htX : {y : M | f y ≤ t} ⊆ X := fun y hy => le_trans hy htb.le
  let nestA := Submission.GSHalfDisk.subtypeNestHomeomorph (s := X) (t := {y : M | f y ≤ t}) htX
  let eA : ↥A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 :=
    nestA.trans eT.symm
  have hsphereImage : eT '' (Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      = {y : ↥{y : M | f y ≤ t} | f (y : M) = t} := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (Set.ext_iff.mp heT u).mpr hu
    · intro hz
      refine ⟨eT.symm z, (Set.ext_iff.mp heT (eT.symm z)).mp ?_, eT.apply_symm_apply z⟩
      rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
      exact hz
  have hsymm_mem : ∀ z : ↥{y : M | f y ≤ t},
      z ∈ eT '' (Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      ↔ eT.symm z ∈ Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1 := by
    intro z
    constructor
    · rintro ⟨u, hu, huz⟩
      rw [← huz, Homeomorph.symm_apply_apply]
      exact hu
    · intro hz
      exact ⟨eT.symm z, hz, eT.apply_symm_apply z⟩
  have heA_sphere : ∀ a : ↥A, eA a ∈ (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      ↔ f ((a : ↥X) : M) = t := by
    intro a
    have h1 : eA a = eT.symm (nestA a) := rfl
    rw [h1]
    have hval : (nestA a : M) = ((a : ↥X) : M) := rfl
    constructor
    · intro h
      have h2 : nestA a ∈ {y : ↥{y : M | f y ≤ t} | f (y : M) = t} := by
        rw [← hsphereImage]
        exact ⟨eT.symm (nestA a), h, eT.apply_symm_apply (nestA a)⟩
      rw [Set.mem_ofPred_eq, hval] at h2
      exact h2
    · intro h
      have h2 : nestA a ∈ {y : ↥{y : M | f y ≤ t} | f (y : M) = t} := by
        rw [Set.mem_ofPred_eq, hval]; exact h
      rw [← hsphereImage] at h2
      obtain ⟨u, hu, huz⟩ := h2
      rw [← huz, Homeomorph.symm_apply_apply]
      exact hu
  have hAc : A ∩ C = Subtype.val '' (eA ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)) := by
    ext x
    constructor
    · intro hx
      have hxt : f (x : M) = t := by
        have h' := hx
        rw [hAintC] at h'
        exact h'
      exact ⟨⟨x, le_of_eq hxt⟩, (heA_sphere ⟨x, le_of_eq hxt⟩).mpr hxt, rfl⟩
    · rintro ⟨a, ha, hax⟩
      rw [← hax]
      have h1 : f ((a : ↥X) : M) = t := (heA_sphere a).mp ha
      exact ⟨a.2, Set.mem_ofPred_eq.mpr ⟨le_of_eq h1.symm, (a : ↥X).2⟩⟩
  -- the collar chart on `C`
  let PP := Homeomorph.Set.prod {y : M | f y = t} (Set.Icc (0:ℝ) (b - t))
  let homeoI : ↥(Set.Icc (0:ℝ) (b - t)) ≃ₜ ↥(Set.Icc (0:ℝ) 1) :=
    iccRescale (b - t) (sub_pos.mpr htb)
  have hFt : {y : M | f y = t} ⊆ {y : M | f y ≤ t} := fun y hy => le_of_eq hy
  let nestF := Submission.GSHalfDisk.subtypeNestHomeomorph (s := {y : M | f y ≤ t})
    (t := {y : M | f y = t}) hFt
  let homeoF : ↥{y : M | f y = t} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 :=
    nestF.symm.trans (((eT.symm).subtype (p := fun y : ↥{y : M | f y ≤ t} => f (y : M) = t)
      (q := fun u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 =>
        u ∈ Metric.sphere (0 : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      (fun y => (Set.ext_iff.mp hsphereImage y).symm.trans (hsymm_mem y))).trans
      (Commons.Topology.Sphere.TwoDiskStrong.sphEquiv (Module.finrank ℝ E)))
  have htXb : {y : M | t ≤ f y ∧ f y ≤ b} ⊆ X := fun y hy => hy.2
  let nestC := Submission.GSHalfDisk.subtypeNestHomeomorph (s := X)
    (t := {y : M | t ≤ f y ∧ f y ≤ b}) htXb
  let eC : ↥C ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 ×ˢ
      Set.Icc (0 : ℝ) 1) :=
    (nestC.trans Φ.symm).trans (PP.trans ((homeoF.prodCongr homeoI).trans
      (Homeomorph.Set.prod (Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1)
        (Set.Icc (0 : ℝ) 1)).symm))
  -- the collar sends the two ends to the two level sets
  have hΦinv : ∀ z : ↥{y : M | t ≤ f y ∧ f y ≤ b},
      f (z : M) = t + ((Φ.symm z).1.2 : ℝ) := by
    intro z
    have h := hΦ (Φ.symm z)
    rw [Homeomorph.apply_symm_apply] at h
    exact h
  have heCval : ∀ x : ↥C, ((eC x : ↥(Metric.sphere (0 : EuclideanSpace ℝ
        (Fin (Module.finrank ℝ E))) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × ℝ).2
      = ((Φ.symm (nestC x)).1.2 : ℝ) / (b - t) := by
    intro x
    show ((homeoI (PP (Φ.symm (nestC x))).2 : ↥(Set.Icc (0:ℝ) 1)) : ℝ) = _
    rw [iccRescale_coe]
    rfl
  have heCzero : ∀ x : ↥C,
      ((eC x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1
        ×ˢ Set.Icc (0 : ℝ) 1)) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × ℝ).2 = 0
      ↔ f (x : M) = t := by
    intro x
    have hfΦ : f (x : M) = t + ((Φ.symm (nestC x)).1.2 : ℝ) := by
      rw [← hΦinv (nestC x)]; rfl
    rw [heCval x, hfΦ]
    have hb' : 0 < b - t := sub_pos.mpr htb
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hb'.ne'
    · intro h; left; linarith
  have heCone : ∀ x : ↥C,
      ((eC x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1
        ×ˢ Set.Icc (0 : ℝ) 1)) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × ℝ).2 = 1
      ↔ f (x : M) = b := by
    intro x
    have hfΦ : f (x : M) = t + ((Φ.symm (nestC x)).1.2 : ℝ) := by
      rw [← hΦinv (nestC x)]; rfl
    have hb' : 0 < b - t := sub_pos.mpr htb
    rw [heCval x, div_eq_one_iff_eq hb'.ne']
    constructor
    · intro h; rw [hfΦ, h]; ring
    · intro h; rw [hfΦ] at h; linarith
  have hCc : A ∩ C = Subtype.val '' (eC ⁻¹' {p : ↥(Metric.sphere (0 : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E))) 1 ×ˢ Set.Icc (0 : ℝ) 1) |
      (p : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × ℝ).2 = 0}) := by
    ext x
    constructor
    · intro hx
      have hxt : f (x : M) = t := by
        have h' := hx
        rw [hAintC] at h'
        exact h'
      exact ⟨⟨x, hx.2⟩, (heCzero ⟨x, hx.2⟩).mpr hxt, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      rw [← hcx]
      have h1 : f ((c : ↥X) : M) = t := (heCzero c).mp hc
      exact ⟨le_of_eq h1, c.2⟩
  -- assembling
  obtain ⟨e, he⟩ := Commons.Topology.Sphere.disk_glue_collar (n := Module.finrank ℝ E)
    hAclosed hCclosed hAC eA hAc eC hCc
  refine ⟨e, ?_⟩
  rw [he]
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hx
    rw [← hcx]
    exact (heCone c).mp hc
  · intro hx
    have hxb : f (x : M) = b := hx
    have hxC : x ∈ C := Set.mem_ofPred_eq.mpr
      ⟨le_trans htb.le (le_of_eq hxb.symm), le_of_eq hxb⟩
    exact ⟨⟨x, hxC⟩, (heCone ⟨x, hxC⟩).mpr hxb, rfl⟩

end

end Submission.GSHalf
