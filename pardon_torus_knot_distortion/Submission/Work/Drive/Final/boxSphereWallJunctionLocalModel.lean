import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.isLocallyEuclidean_trace_of_wallSphereJunction
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction
import Submission.Work.Drive.Mono.isLocallyArc_max_family_common_derivative
import Submission.Work.Drive.Mono.hdir_of_htrans
import Submission.Work.Drive.Final.dentDeform_homeomorph
import Submission.Work.Drive.Final.exists_dentSurface
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped _root_.Topology

noncomputable section

/-- The closed box `{boxNorm ≤ s}` is the closure of the open box, for `s > 0`. -/
theorem boxNorm_le_iff_mem_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ y ≤ s ↔ y ∈ closure (Submission.PBox s c σ) := by
  rw [Work.Drive.Mono.closure_PBox_eq hs c σ, Work.Smooth.BoxGeneric.boxNorm_le_iff]
  constructor
  · intro h i
    have hi := h i
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_le_iff₀ (Submission.boxSide_pos i)] at hi
    linarith [hi, mul_comm (Submission.boxSide i) s]
  · intro h i
    have hi := h i
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_le_iff₀ (Submission.boxSide_pos i)]
    linarith [hi, mul_comm (Submission.boxSide i) s]

theorem boxSphereWallJunctionLocalModel /-
**The local model of the trace of the *deformed* removed set at a box-sphere point of the dent's
annulus at which the deformed wall passes.**  Put this in `namespace Work.Drive.Final`, in
`Submission/Work/Drive/Final/boxSphereWallJunctionLocalModel.lean`.
(`R3`/`Knot` are written out fully because that file need not open
`LeanEval.KnotTheory.PardonDistortion`.)

Here `D.deform` is `y ↦ y + D.a' * D.χ (‖y - D.centre‖ / D.r) • D.d`, the *dented* surface is
`par ψ' = D.deform ∘ par ψ`, the deformed removed set is
`D.deform ⁻¹' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)` and `x` is a point of the dent's
annulus (`D.r / 2 ≤ ‖x - D.centre‖ ≤ D.r`) on the box sphere (`boxNorm c σ x = s`), strictly inside
the slab, at which the deformed wall passes (`ℓ (D.deform x) = ℓ D.centre`).

PROOF PLAN — copy the proof of the already proved `Work.Drive.Mono.isLocallyEuclidean_trace_of_wallSphereJunction`
(same conclusion for the *undeformed* wall, at a point of the surface rather than one of the dent's
annulus), replacing its wall `lam - ℓ` by `ℓ D.centre - ℓ ∘ D.deform` and deriving its two
frontier/plane-model ingredients as follows.

(a) `Φ := D.deform` is a homeomorphism of `ℝ³` (`Work.Drive.Final.dentDeform_homeomorph` from
`D.κ_pos`, `D.r_pos`, `D.d_norm.le`, `D.χ_diff`, `D.χ_deriv_bound` and `ha`).  Set `z := D.deform x`;
then `boxNorm c σ z = s`, `|slabFn c u v z| < h`, `ℓ z = ℓ D.centre` (`hxs`, `hxslab`, `hxg`; use
`D.box_pres` together with `D.deform = id` off the ball — `Work.Drive.Final.dentDeform_eq_self_of_le`
— for the box norm, and `D.d_orth_v`, i.e. `inner ℝ v (D.deform y) = inner ℝ v y`, for the slab).

(b) Apply `Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction hs hℓne` at the point `z`
with the level `ℓ D.centre`: its `hdir` hypothesis is the one assumed here (with `z = D.deform x`),
and its conclusion characterises `frontier (tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))` on a
neighbourhood `O` of `z` as `boxNorm ≤ s ∧ ℓ ≥ ℓ D.centre ∧ (boxNorm = s ∨ ℓ = ℓ D.centre)`.

(c) Pull the characterisation back along `Φ` (`Work.Drive.Final.frontier_preimage_homeomorph`, and
`Φ '' PBox = PBox` from `D.box_pres` + `deform = id` off the ball together with the fact that `Φ` is a
homeomorphism, which also gives `Φ '' frontier PBox = frontier PBox` and
`Φ '' closure PBox = closure PBox`): for `w` near `x`,

  `w ∈ frontier (D.deform ⁻¹' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ↔`
  `boxNorm c σ w ≤ s ∧ ℓ D.centre ≤ ℓ (D.deform w) ∧ (boxNorm c σ w = s ∨ ℓ (D.deform w) = ℓ D.centre)`.

(d) In the parameter plane near `p` (`hp`): rewrite `boxNorm ∘ par ψ` as the maximum of the tight
faces (`Work.Drive.Mono.eventually_boxNorm_eq_sup_tight`, `tightFaceIdx_nonempty`,
`Work.Drive.Mono.fderiv_tightFace_sub_s_eq hs hxs i.2 hp hB` — all with `hB` playing the role of the
model's `hD`), and `ℓ (D.deform (par ψ q))` as `sweepHeight ψ' ℓ q` (`hpar'`).  Then the trace near
`x` is the image of the zero set of
`max (Finset.sup' tight faces (faceLin c σ i (tightEps c σ x i) (par ψ ·) - s)) (ℓ D.centre - sweepHeight ψ' ℓ ·)`,
which is locally an arc by `Work.Drive.Mono.isLocallyArc_max_family_common_derivative`: the common
derivative of the tight-face functions is `fderiv (boxNorm ∘ par ψ) p ≠ 0` (`hB`), the last function
is `C¹` (`Work.Drive.EpsForm.sweepHeight_contDiff_two ψ' ℓ`), vanishes at `p` (`hp`, `hxg`), and its
derivative is independent of the common one by `hannB` (the side conditions `hρ1`, `hρ2`, `hxs` and
`hxslab` supply `|slabFn| ≤ h` at `q' = p`).

(e) Finish exactly as the model does: the arc is the image under `par ψ` of a parameter
neighbourhood, so `Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param` (with `hZc`:
`carrier ∩ frontier ⊆ torus ψ carrier`, `hPB`, `hident`, `param_local_injective`) gives the local
Euclidean structure of the trace intersected with the image of that neighbourhood, and
`Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen` turns it into an *ambient* open set `V`
containing `x`; the final step (intersecting with the slab neighbourhood and converting
`IsOpenInSet` back to an ambient set) is verbatim in the model. -/
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    {s u h R : ℝ} {c v : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    {ψ' : Submission.Diffeo}
    (hpar' : ∀ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' q = D.deform (Work.BoxShrink.Pinch.par ψ q))
    (hs : 0 < s) (hℓne : ℓ ≠ 0) (ha : D.a' * D.κ < D.r)
    {x : LeanEval.KnotTheory.PardonDistortion.R3}
    (hdir : ∃ δ : ℝ, 0 < δ ∧ ∀ y : LeanEval.KnotTheory.PardonDistortion.R3,
      dist y (D.deform x) < δ → Submission.boxNorm c σ y = s → ℓ y = ℓ D.centre → ∀ ε : ℝ, 0 < ε →
      ∃ y' : LeanEval.KnotTheory.PardonDistortion.R3,
        dist y' y < ε ∧ Submission.boxNorm c σ y' < s ∧ ℓ D.centre ≤ ℓ y')
    {p : ℝ × ℝ} (hp : Work.BoxShrink.Pinch.par ψ p = x)
    (hB : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hannB : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
      Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
      fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
        t • fderiv ℝ (fun q'' : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q')
    (hxc : x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hxs : Submission.boxNorm c σ x = s)
    (hxslab : |Work.Drive.Final.slabFn c u v x| < h)
    (hxg : ℓ (D.deform x) = ℓ D.centre)
    (hρ1 : D.r / 2 ≤ ‖x - D.centre‖) (hρ2 : ‖x - D.centre‖ ≤ D.r) :
    ∃ V : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen V ∧ x ∈ V ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) := by
  classical
  let A : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)
  change ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧
    Work.Smooth.OneManifold.IsLocallyEuclidean
      (V ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' A)))
  -- ## (a) the deformation is a homeomorphism of `ℝ³`
  have ha' : |D.a'| * D.κ < D.r := by rw [abs_of_pos D.a'_pos]; exact ha
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos D.d_norm.le D.χ_diff D.χ_deriv_bound ha'
  have hdeform : ∀ y : R3, D.deform y = Φ y := fun y => (hΦ y).symm
  have hdeformU : ∀ y : R3, dentDeform D.χ D.centre D.d D.r D.a' y = Φ y := fun y => (hΦ y).symm
  have hself : ∀ y : R3, D.r ≤ ‖y - D.centre‖ → D.deform y = y :=
    fun y hy => dentDeform_eq_self_of_le D.r_pos D.χ_eq_zero hy
  have hboxpres : ∀ w : R3, (w ∈ Submission.PBox s c σ ↔ Φ w ∈ Submission.PBox s c σ) := by
    intro w
    by_cases hw : ‖w - D.centre‖ ≤ D.r
    · have h := D.box_pres w hw
      rw [hdeformU w] at h
      exact h
    · have hlt : D.r < ‖w - D.centre‖ := not_le.mp hw
      rw [← hdeform w, hself w hlt.le]
  have hΦPBox : Φ '' Submission.PBox s c σ = Submission.PBox s c σ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hboxpres w).mp hw
    · intro hy
      refine ⟨Φ.symm y, ?_, Φ.apply_symm_apply y⟩
      exact (hboxpres (Φ.symm y)).mpr (by simpa using hy)
  have hΦclos : Φ '' closure (Submission.PBox s c σ) = closure (Submission.PBox s c σ) := by
    rw [Φ.image_closure, hΦPBox]
  have hnorm_leΦ : ∀ y : R3,
      (Submission.boxNorm c σ (Φ y) ≤ s ↔ Submission.boxNorm c σ y ≤ s) := by
    intro y
    rw [boxNorm_le_iff_mem_closure_PBox hs, boxNorm_le_iff_mem_closure_PBox hs]
    have h1 : ∀ z : R3, z ∈ closure (Submission.PBox s c σ) →
        Φ z ∈ closure (Submission.PBox s c σ) := by
      intro z hz
      rw [← hΦclos]
      exact ⟨z, hz, rfl⟩
    have h2 : ∀ z : R3, Φ z ∈ closure (Submission.PBox s c σ) →
        z ∈ closure (Submission.PBox s c σ) := by
      intro z hz
      rw [← hΦclos] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      rwa [Φ.injective hwz] at hw
    exact ⟨h2 y, h1 y⟩
  have hnorm_ltΦ : ∀ y : R3,
      (Submission.boxNorm c σ (Φ y) < s ↔ Submission.boxNorm c σ y < s) :=
    fun y => (Submission.mem_PBox_iff s c σ (Φ y)).symm.trans
      ((hboxpres y).symm.trans (Submission.mem_PBox_iff s c σ y))
  have hnorm_eqΦ : ∀ y : R3,
      (Submission.boxNorm c σ (Φ y) = s ↔ Submission.boxNorm c σ y = s) := by
    intro y
    constructor
    · intro h
      refine le_antisymm ((hnorm_leΦ y).mp (le_of_eq h)) ?_
      by_contra hcon
      push_neg at hcon
      rw [← hnorm_ltΦ y] at hcon
      linarith
    · intro h
      refine le_antisymm ((hnorm_leΦ y).mpr (le_of_eq h)) ?_
      by_contra hcon
      push_neg at hcon
      rw [hnorm_ltΦ y] at hcon
      linarith
  have hnorm_le : ∀ y : R3,
      (Submission.boxNorm c σ (D.deform y) ≤ s ↔ Submission.boxNorm c σ y ≤ s) :=
    fun y => by rw [hdeform y]; exact hnorm_leΦ y
  have hnorm_lt : ∀ y : R3,
      (Submission.boxNorm c σ (D.deform y) < s ↔ Submission.boxNorm c σ y < s) :=
    fun y => by rw [hdeform y]; exact hnorm_ltΦ y
  have hnorm_eq : ∀ y : R3,
      (Submission.boxNorm c σ (D.deform y) = s ↔ Submission.boxNorm c σ y = s) :=
    fun y => by rw [hdeform y]; exact hnorm_eqΦ y
  -- the three facts about `z = D.deform x`
  have hzsphere : Submission.boxNorm c σ (D.deform x) = s := by
    rw [hdeform x]
    exact (hnorm_eqΦ x).mpr hxs
  have hzslab : |inner ℝ v (D.deform x) - (inner ℝ v c + u)| < h := by
    have hinner : inner ℝ v (D.deform x) = inner ℝ v x := by
      simp only [AnyDentDatum.deform, dentDeform, inner_add_right, inner_smul_right,
        D.d_orth_v, mul_zero, add_zero]
    rw [hinner]
    exact hxslab
  have hzl : ℓ (D.deform x) = ℓ D.centre := hxg
  -- ## (b) the frontier characterisation at `z`
  obtain ⟨δ₁, hδ₁pos, hdir₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : R3, dist y (D.deform x) < δ →
      Submission.boxNorm c σ y = s → ℓ y = ℓ D.centre → ∀ ε : ℝ, 0 < ε →
      ∃ y' : R3, dist y' y < ε ∧ Submission.boxNorm c σ y' < s ∧ ℓ D.centre ≤ ℓ y' := by
    obtain ⟨δ, hδ, h⟩ := hdir
    exact ⟨δ, hδ, h⟩
  obtain ⟨O, hOopen, hzO, hchar⟩ :=
    Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction (s := s) (u := u) (h := h)
      (c := c) (v := v) (σ := σ) (ℓ := ℓ) (lam := ℓ D.centre) (z := D.deform x)
      hs hℓne hzsphere hzslab hzl ⟨δ₁, hδ₁pos, hdir₁⟩
  -- ## (c) pull the characterisation back along the deformation
  have hpre_eq : D.deform ⁻¹' A = Φ ⁻¹' A := by
    ext y
    simp only [Set.mem_preimage, hdeform y]
  have hfront_eq : frontier (D.deform ⁻¹' A) = Φ ⁻¹' frontier A := by
    rw [hpre_eq, frontier_preimage_homeomorph Φ A]
  have hmem_front : ∀ w : R3, (w ∈ frontier (D.deform ⁻¹' A) ↔ D.deform w ∈ frontier A) :=
    fun w => by simp only [hfront_eq, Set.mem_preimage, ← hdeform w]
  have hchar' : ∀ w : R3, Φ w ∈ O → (w ∈ frontier (D.deform ⁻¹' A) ↔
      Submission.boxNorm c σ w ≤ s ∧ ℓ (D.deform w) ≥ ℓ D.centre ∧
        (Submission.boxNorm c σ w = s ∨ ℓ (D.deform w) = ℓ D.centre)) := by
    intro w hwO
    rw [hmem_front w]
    have h1 := hchar (Φ w) hwO
    simp only [← hdeform w] at h1
    refine h1.trans ?_
    constructor
    · rintro ⟨hb, hl, hd⟩
      exact ⟨(hnorm_le w).mp hb, hl,
        hd.elim (fun h => Or.inl ((hnorm_eq w).mp h)) (fun h => Or.inr h)⟩
    · rintro ⟨hb, hl, hd⟩
      exact ⟨(hnorm_le w).mpr hb, hl,
        hd.elim (fun h => Or.inl ((hnorm_eq w).mpr h)) (fun h => Or.inr h)⟩
  -- ## (d) the plane model from the tight faces and the deformed wall
  haveI : Nonempty (Work.Drive.Mono.TightFaceIdx c σ s x) :=
    Work.Drive.Mono.tightFaceIdx_nonempty hxs
  set Ψ : Work.Drive.Mono.TightFaceIdx c σ s x → ℝ × ℝ → ℝ := fun i q =>
    Work.Smooth.BoxGeneric.faceLin c σ i.1 (Work.Drive.Mono.tightEps c σ x i.1)
      (Work.BoxShrink.Pinch.par ψ q) - s with hΨdef
  set Gm : ℝ × ℝ → ℝ := fun q => ℓ D.centre - Work.Drive.EpsForm.sweepHeight ψ' ℓ q with hGdef
  have hΨcd : ∀ i, ContDiff ℝ 1 (Ψ i) := by
    intro i
    rw [hΨdef]
    exact ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i.1
      (Work.Drive.Mono.tightEps c σ x i.1)).sub contDiff_const).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞))
  have hΨp : ∀ i, Ψ i p = 0 := by
    intro i
    rw [hΨdef]
    change Work.Smooth.BoxGeneric.faceLin c σ i.1 (Work.Drive.Mono.tightEps c σ x i.1)
      (Work.BoxShrink.Pinch.par ψ p) - s = 0
    rw [hp]
    exact sub_eq_zero.mpr (Work.Drive.Mono.faceLin_tightEps_tight_eq i.2)
  have hΨd : ∀ i, fderiv ℝ (Ψ i) p =
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro i
    rw [hΨdef]
    exact Work.Drive.Mono.fderiv_tightFace_sub_s_eq hs hxs i.2 hp hB
  have hGcd : ContDiff ℝ 1 Gm := by
    rw [hGdef]
    have h1 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (Work.Drive.EpsForm.sweepHeight ψ' ℓ) :=
      (ContinuousLinearMap.contDiff ℓ).comp (Work.Smooth.Morse.param_contDiff ψ')
    exact (contDiff_const.sub h1).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞))
  have hGp : Gm p = 0 := by
    rw [hGdef]
    change ℓ D.centre - Work.Drive.EpsForm.sweepHeight ψ' ℓ p = 0
    rw [show Work.Drive.EpsForm.sweepHeight ψ' ℓ p =
        ℓ (Work.BoxShrink.Pinch.par ψ' p) from rfl, hpar' p, hp, hxg, sub_self]
  have hfdG : fderiv ℝ Gm p = -fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ℓ) p := by
    rw [hGdef]
    exact fderiv_const_sub (ℓ D.centre)
  have hSweep_fderiv : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ℓ) p =
      fderiv ℝ (fun q : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q))) p := by
    have hfun : Work.Drive.EpsForm.sweepHeight ψ' ℓ =
        fun q : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q)) := by
      funext q
      rw [show Work.Drive.EpsForm.sweepHeight ψ' ℓ q =
        ℓ (Work.BoxShrink.Pinch.par ψ' q) from rfl, hpar' q]
    rw [hfun]
  have hannB_p : ∀ t : ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q))) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p :=
    hannB p (by rw [hp]; exact hρ1) (by rw [hp]; exact hρ2)
      (by rw [hp]
          exact Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs c σ (le_of_eq hxs))
      (by rw [hp]; exact le_of_lt hxslab) (by rw [hp]; exact hxs)
  have hGind : ∀ t : ℝ, fderiv ℝ Gm p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro t ht
    have h4 : -fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ' ℓ) p =
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p := by
      rw [← hfdG]; exact ht
    rw [hSweep_fderiv] at h4
    exact hannB_p (-t) ((neg_eq_iff_eq_neg.mp h4).trans (neg_smul t _).symm)
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    Work.Drive.Mono.isLocallyArc_max_family_common_derivative hΨcd hGcd hΨp hGp hΨd hB hGind
  -- ## the neighbourhood of `p` on which the model is the trace
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp
    (Work.Drive.Mono.eventually_boxNorm_eq_sup_tight hs hxs)
  have hcont : Continuous (Work.BoxShrink.Pinch.par ψ) := Work.BoxShrink.Pinch.par_continuous ψ
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  obtain ⟨δ₄, hδ₄pos, hδ₄inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  have hnhds₂ : {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball x δ₂} ∈ 𝓝 p :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by rw [hp]; exact Metric.mem_ball_self hδ₂pos))
  obtain ⟨δ₅, hδ₅pos, hδ₅⟩ := Metric.mem_nhds_iff.mp hnhds₂
  have hnhds₁ : {q : ℝ × ℝ | Φ (Work.BoxShrink.Pinch.par ψ q) ∈ O} ∈ 𝓝 p := by
    refine (Φ.continuous.comp hcont).continuousAt (hOopen.mem_nhds ?_)
    show Φ (Work.BoxShrink.Pinch.par ψ p) ∈ O
    rw [hp, ← hdeform x]
    exact hzO
  obtain ⟨δ₆, hδ₆pos, hδ₆⟩ := Metric.mem_nhds_iff.mp hnhds₁
  set δ : ℝ := min (min δ₃ δ₄) (min δ₅ δ₆) with hδdef
  have hδpos : 0 < δ :=
    lt_min (lt_min hδ₃pos hδ₄pos) (lt_min hδ₅pos hδ₆pos)
  have hδ₃' : δ ≤ δ₃ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₄' : δ ≤ δ₄ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₅' : δ ≤ δ₅ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₆' : δ ≤ δ₆ := le_trans (min_le_right _ _) (min_le_right _ _)
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hpB : p ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
  have hBV : B ⊆ V := fun q hq => hδ₃ (Metric.ball_subset_ball hδ₃' hq)
  have hBinj : Set.InjOn (Work.BoxShrink.Pinch.par ψ) B := fun a ha b hb hab =>
    hδ₄inj (Metric.ball_subset_ball hδ₄' ha) (Metric.ball_subset_ball hδ₄' hb) hab
  have hBbox : ∀ q ∈ B, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) =
      Work.Drive.Mono.tightSup c σ s x hxs (Work.BoxShrink.Pinch.par ψ q) :=
    fun q hq => hδ₂ (hδ₅ (Metric.ball_subset_ball hδ₅' hq))
  have hBO : ∀ q ∈ B, Φ (Work.BoxShrink.Pinch.par ψ q) ∈ O :=
    fun q hq => hδ₆ (Metric.ball_subset_ball hδ₆' hq)
  -- the model set
  set M : Set (ℝ × ℝ) := {q : ℝ × ℝ |
    max (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => Ψ i q)) (Gm q) = 0} with hMdef
  have hsup_eq : ∀ q : ℝ × ℝ,
      (Finset.univ : Finset (Work.Drive.Mono.TightFaceIdx c σ s x)).sup'
        (Work.Drive.Mono.tightIdx_nonempty hxs) (fun i => Ψ i q) =
      Work.Drive.Mono.tightSup c σ s x hxs (Work.BoxShrink.Pinch.par ψ q) - s := by
    intro q
    have h1 : (Finset.univ : Finset (Work.Drive.Mono.TightFaceIdx c σ s x)).sup'
        (Work.Drive.Mono.tightIdx_nonempty hxs) (fun i => Ψ i q) =
        (Finset.univ : Finset (Work.Drive.Mono.TightFaceIdx c σ s x)).sup'
          (Work.Drive.Mono.tightIdx_nonempty hxs)
          (fun i => Work.Smooth.BoxGeneric.faceLin c σ i.1
            (Work.Drive.Mono.tightEps c σ x i.1) (Work.BoxShrink.Pinch.par ψ q) - s) := by
      refine Finset.sup'_congr (Work.Drive.Mono.tightIdx_nonempty hxs) rfl ?_
      intro i _
      rw [hΨdef]
    rw [h1, Work.Drive.Mono.finset_sup_sub_eq, Work.Drive.Mono.tightSup]
  -- the pointwise identification of the trace with the model
  have hpoint : ∀ q ∈ B, (Work.BoxShrink.Pinch.par ψ q ∈ frontier (D.deform ⁻¹' A) ↔ q ∈ M) := by
    intro q hq
    rw [hchar' _ (hBO q hq)]
    have hbox := hBbox q hq
    have hsupq : (Finset.univ : Finset (Work.Drive.Mono.TightFaceIdx c σ s x)).sup'
          Finset.univ_nonempty (fun i => Ψ i q) =
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s := by
      rw [Work.Drive.Mono.finset_sup'_proof_irrel Finset.univ_nonempty
          (Work.Drive.Mono.tightIdx_nonempty hxs) _, hsup_eq q, hbox]
    have hGq : Gm q = ℓ D.centre - ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q)) := by
      rw [hGdef]
      change ℓ D.centre - Work.Drive.EpsForm.sweepHeight ψ' ℓ q =
        ℓ D.centre - ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q))
      rw [show Work.Drive.EpsForm.sweepHeight ψ' ℓ q =
        ℓ (Work.BoxShrink.Pinch.par ψ' q) from rfl, hpar' q]
    rw [hMdef]
    simp only [Set.mem_setOf_eq]
    rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff, hsupq, hGq]
    constructor
    · rintro ⟨hb, hl, hdisj⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases hdisj with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  -- ## (e) transport to the surface
  have hZc : ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹' A)) ⊆
      (Work.Smooth.Morse.torus ψ).carrier := Set.inter_subset_left
  have hPB : B ∩ M ⊆ B := Set.inter_subset_left
  have hloc : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ (B ∩ M)) := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥(V ∩ M) := hVloc
    have h2 : Work.Smooth.SphereJordan.IsLocallyArc ↥((V ∩ M) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen h1 hBopen
    have h3 : (V ∩ M) ∩ B = B ∩ (B ∩ M) := by
      ext q
      constructor
      · rintro ⟨⟨hqV, hqM⟩, hqB⟩
        exact ⟨hqB, hqB, hqM⟩
      · rintro ⟨hqB, -, hqM⟩
        exact ⟨⟨hBV hqB, hqM⟩, hqB⟩
    exact h3 ▸ h2
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.BoxShrink.Pinch.par ψ '' (B' ∩ (B ∩ M)) =
        Work.BoxShrink.Pinch.par ψ '' B' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' A)) := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, ⟨hqB', hqBM⟩, rfl⟩
      exact ⟨⟨q, hqB', rfl⟩, Work.BoxShrink.Pinch.par_mem_carrier ψ q,
        (hpoint q (hB'sub hqB')).mpr hqBM.2⟩
    · rintro ⟨⟨q, hqB', rfl⟩, hy⟩
      exact ⟨q, ⟨hqB', hB'sub hqB', (hpoint q (hB'sub hqB')).mp hy.2⟩, rfl⟩
  have hlocE : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' A))) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param hZc hBopen hPB hident hBinj hloc
  -- the ambient open set
  obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp
    (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen)
  have hWeq' : Subtype.val ⁻¹' W =
      Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' B : Set R3) := hWeq
  have hWcar : (Work.Smooth.Morse.torus ψ).carrier ∩ W = Work.BoxShrink.Pinch.par ψ '' B := by
    ext y
    constructor
    · rintro ⟨hyc, hyW⟩
      have h1 : (⟨y, hyc⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' B) := by
        rw [← hWeq']
        exact hyW
      exact h1
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Work.BoxShrink.Pinch.par_mem_carrier ψ q, ?_⟩
      have h2 : (⟨Work.BoxShrink.Pinch.par ψ q,
          Work.BoxShrink.Pinch.par_mem_carrier ψ q⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' W := by
        rw [hWeq']
        exact ⟨q, hq, rfl⟩
      exact h2
  have hpreO : IsOpen (Φ ⁻¹' O) := hOopen.preimage Φ.continuous
  refine ⟨W ∩ Φ ⁻¹' O, hWopen.inter hpreO, ⟨?_, ?_⟩, ?_⟩
  · have h1 : x ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ W := by
      rw [hWcar]
      exact ⟨p, hpB, hp⟩
    exact h1.2
  · show Φ x ∈ O
    rw [← hdeform x]
    exact hzO
  · have hset : (W ∩ Φ ⁻¹' O) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' A)) =
        (Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' A))) ∩ Φ ⁻¹' O := by
      ext y
      constructor
      · rintro ⟨⟨hyW, hyO⟩, hyZ⟩
        have h2 : y ∈ Work.BoxShrink.Pinch.par ψ '' B := by
          rw [← hWcar]
          exact ⟨hyZ.1, hyW⟩
        exact ⟨⟨h2, hyZ⟩, hyO⟩
      · rintro ⟨⟨hyWB, hyZ⟩, hyO⟩
        have hyW : y ∈ W := by
          have h1 : y ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ W := by
            rw [hWcar]
            exact hyWB
          exact h1.2
        exact ⟨⟨hyW, hyO⟩, hyZ⟩
    rw [hset]
    refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn Set.inter_subset_left ?_ hlocE
    rw [Work.Smooth.OneManifold.IsOpenInSet]
    have hpre : Subtype.val ⁻¹' ((Work.BoxShrink.Pinch.par ψ '' B ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' A))) ∩ Φ ⁻¹' O) =
        {y : ↥(Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' A))) | (y : R3) ∈ Φ ⁻¹' O} := by
      ext y
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨y.2, h⟩
    rw [hpre]
    exact hpreO.preimage continuous_subtype_val

end

end Work.Drive.Final
