import Mathlib
import Submission.Work.Drive.Mono.Residual

/-!
# The trace of the tilted sweep near a point of a slab face

At a point `z` of the box which lies on the **upper face** of the closed tilted slab
(`⟪v,z⟫ = ⟪v,c⟫ + u + h`) and strictly *behind* the wall (`ℓ z < lam`), the frontier of the
level's removed set coincides, near `z`, with the face plane
`{y | ⟪v,y⟫ = ⟪v,c⟫ + u + h}` intersected with the surface.

The removed set is `f = PBox ∖ (S ∩ L)`, where
* `S = {y | |⟪v,y⟫ - (⟪v,c⟫+u)| ≤ h}` is the closed slab and
* `L = {y | ℓ y < lam}` is the open half-space behind the wall.

Because `v ≠ 0` and `h > 0`, the open set

    O := PBox ∩ {y | ⟪v,c⟫ + u < ⟪v,y⟫} ∩ {y | ℓ y < lam}

is a neighbourhood of `z` (`z` sits on the upper face, strictly above the mid-plane
`⟪v,·⟫ = ⟪v,c⟫+u`, and strictly behind the wall), and on `O` one has, for every `y ∈ O`:

* `⟪v,y⟫ > ⟪v,c⟫+u+h`  ⟹  `y ∉ S`, so the *open* set `PBox ∩ {⟪v,·⟫ > ⟪v,c⟫+u+h}` contains `y`
  and lies in `f`: thus `y ∈ interior f`, not a frontier point;
* `⟪v,c⟫+u < ⟪v,y⟫ < ⟪v,c⟫+u+h`  ⟹  `y ∈ interior (S ∩ L) ⊆ interior (fᶜ)`, so `y ∉ closure f`,
  not a frontier point either (here `O`'s lower bound on `⟪v,·⟫` excludes the *lower* face);
* `⟪v,y⟫ = ⟪v,c⟫+u+h`  ⟹  `y ∈ S ∩ L ⊆ fᶜ` (so `y ∉ interior f`, as `interior f ⊆ f`) while the
  ray `y + t·v`, `t > 0` small, lies in `PBox ∩ {⟪v,·⟫ > ⟪v,c⟫+u+h} ⊆ f` and meets every
  neighbourhood of `y`: thus `y ∈ closure f`, i.e. `y ∈ frontier f`.

The last case is the only place where `v ≠ 0` is used (through `⟪v,v⟫ = ‖v‖² > 0`), and the
exclusion of the lower face is where `0 < h` enters.  The point `z` itself is in the frontier of
`f`, the face plane `⟪v,·⟫ = ⟪v,c⟫+u+h` being where the two "sides" meet.

This is the *face* analogue of `Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds` (the local
model of the trace at an interior point of the wall), and one of the local models of the trace of
the tilted sweep (P1) in `Submission/Work/Drive/Mono/NOTES_tiltedTraceDataWExists.md`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Mono

theorem Trace_eq_planeNear_facePoint_holds
    {P : Work.CoreTopology.ParamTorus} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : v ≠ 0) (hh : 0 < h)
    (hz : z ∈ P.carrier) (hzb : z ∈ Submission.PBox s c σ)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z < lam) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      O ∩ (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))
        = O ∩ P.carrier ∩
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | inner ℝ v y = inner ℝ v c + u + h} := by
  classical
  set a : ℝ := inner ℝ v c + u with hadef
  set B : Set R3 := Submission.PBox s c σ with hBdef
  set S : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed a v h with hSdef
  set L : Set R3 := {y : R3 | ℓ y < lam} with hLdef
  set W : Set R3 := {y : R3 | a < inner ℝ v y} with hWdef
  set face : Set R3 := {y : R3 | inner ℝ v y = a + h} with hfacedef
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  have hcontI : Continuous fun y : R3 => inner ℝ v y := continuous_const.inner continuous_id
  have hBopen : IsOpen B := by rw [hBdef]; exact Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hopenL : IsOpen L := by rw [hLdef]; exact isOpen_lt ℓ.continuous continuous_const
  have hWopen : IsOpen W := by rw [hWdef]; exact isOpen_lt continuous_const hcontI
  have hvpos : 0 < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr hv) 2
  have hf_exp : f = B \ (S ∩ L) := by
    simp only [hfdef, hBdef, hSdef, hLdef, hadef, Work.Drive.Mono.tiltedLevelRemoved]
  have hfmem : ∀ y : R3, (y ∈ f ↔ y ∈ B ∧ ¬ (y ∈ S ∧ y ∈ L)) := by
    intro y; simp only [hf_exp, Set.mem_sdiff, Set.mem_inter_iff]
  have hSmem : ∀ y : R3, (y ∈ S ↔ |inner ℝ v y - a| ≤ h) := by
    intro y; simp only [hSdef, Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
  have hLmem : ∀ y : R3, (y ∈ L ↔ ℓ y < lam) := by
    intro y; simp only [hLdef, Set.mem_ofPred_eq]
  have hWmem : ∀ y : R3, (y ∈ W ↔ a < inner ℝ v y) := by
    intro y; simp only [hWdef, Set.mem_ofPred_eq]
  have hfacemem : ∀ y : R3, (y ∈ face ↔ inner ℝ v y = a + h) := by
    intro y; simp only [hfacedef, Set.mem_ofPred_eq]
  have hfr_mem : ∀ y : R3, (y ∈ frontier f ↔ y ∈ closure f ∧ y ∉ interior f) := by
    intro y; simp only [frontier, Set.mem_sdiff]
  -- On `O = B ∩ W ∩ L` the frontier of the removed set is exactly the face plane.
  have key : ∀ y : R3, y ∈ B ∩ W ∩ L → (y ∈ frontier f ↔ y ∈ face) := by
    intro y hyO
    obtain ⟨⟨hyB, hyW⟩, hyL⟩ := hyO
    have hya : a < inner ℝ v y := (hWmem y).mp hyW
    have hylam : ℓ y < lam := (hLmem y).mp hyL
    constructor
    · intro hyfr
      obtain ⟨hycl, hyint⟩ := (hfr_mem y).mp hyfr
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · -- `y` lies strictly inside the slab: it is an interior point of `fᶜ`.
        have hmemS : |inner ℝ v y - a| < h := by
          rw [abs_lt]; exact ⟨by linarith, by linarith⟩
        have hopenT : IsOpen {t : R3 | |inner ℝ v t - a| < h} :=
          isOpen_lt ((hcontI.sub continuous_const).abs) continuous_const
        have hTsub : {t : R3 | |inner ℝ v t - a| < h} ⊆ S := by
          intro t ht; exact (hSmem t).mpr (le_of_lt ht)
        have hyintS : y ∈ interior S := interior_maximal hTsub hopenT hmemS
        have hyintL : y ∈ interior L := interior_maximal (Subset.refl L) hopenL hyL
        have hyintSL : y ∈ interior (S ∩ L) := by
          rw [interior_inter]; exact ⟨hyintS, hyintL⟩
        have hfcompl : S ∩ L ⊆ fᶜ := by
          intro t ht
          rw [Set.mem_compl_iff]
          intro htf
          exact ((hfmem t).mp htf).2 ht
        have hyintfc : y ∈ interior fᶜ :=
          interior_maximal (fun t ht => hfcompl (interior_subset ht)) isOpen_interior hyintSL
        rw [interior_compl] at hyintfc
        exact hyintfc hycl
      · -- `y` lies strictly above the face: it is an interior point of `f`.
        have hopenT : IsOpen (B ∩ {t : R3 | a + h < inner ℝ v t}) :=
          hBopen.inter (isOpen_lt continuous_const hcontI)
        have hTsub : B ∩ {t : R3 | a + h < inner ℝ v t} ⊆ f := by
          rintro t ⟨htB, ht⟩
          have htg : a + h < inner ℝ v t := ht
          rw [hfmem]
          refine ⟨htB, ?_⟩
          intro htS
          have hle : inner ℝ v t - a ≤ h := (abs_le.mp ((hSmem t).mp htS.1)).2
          linarith
        exact hyint (interior_maximal hTsub hopenT ⟨hyB, hgt⟩)
    · intro hyface
      have hval : inner ℝ v y = a + h := (hfacemem y).mp hyface
      refine ⟨?_, ?_⟩
      · -- every neighbourhood of `y` meets `f`, through the ray `y + t • v`
        rw [mem_closure_iff]
        intro V hVopen hyV
        obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp (hVopen.inter hBopen) y ⟨hyV, hyB⟩
        set t : ℝ := δ / (2 * (‖v‖ + 1)) with htdef
        have htpos : 0 < t := by rw [htdef]; positivity
        have htw : t * (‖v‖ + 1) = δ / 2 := by
          rw [htdef, div_mul_eq_mul_div]
          exact mul_div_mul_right δ 2 (by positivity)
        have hball : y + t • v ∈ V ∩ B := by
          apply hδsub
          rw [Metric.mem_ball, dist_eq_norm]
          have h1 : y + t • v - y = t • v := by abel
          rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
          have hle : t * ‖v‖ ≤ t * (‖v‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (le_of_lt htpos)
          rw [htw] at hle
          linarith
        refine ⟨y + t • v, hball.1, ?_⟩
        rw [hfmem]
        refine ⟨hball.2, ?_⟩
        rintro ⟨hyS, -⟩
        have hSz : |inner ℝ v (y + t • v) - a| ≤ h := (hSmem _).mp hyS
        have hval2 : inner ℝ v (y + t • v) - a = h + t * inner ℝ v v := by
          rw [inner_add_right, inner_smul_right, hval]; ring
        have hgt2 : h < |inner ℝ v (y + t • v) - a| := by
          rw [hval2, abs_of_pos (by linarith [mul_pos htpos hvpos])]
          linarith [mul_pos htpos hvpos]
        linarith
      · -- `y` itself is in `S ∩ L`, hence in `fᶜ`, while `interior f ⊆ f`
        intro hyint
        have hyf : y ∈ f := interior_subset hyint
        rw [hfmem] at hyf
        refine hyf.2 ⟨?_, ?_⟩
        · rw [hSmem, hval]
          have : a + h - a = h := by ring
          rw [this, abs_of_pos hh]
        · exact (hLmem y).mpr hylam
  have hOopen : IsOpen (B ∩ W ∩ L) := (hBopen.inter hWopen).inter hopenL
  refine ⟨B ∩ W ∩ L, hOopen, ⟨⟨hzb, ?_⟩, hzl⟩, ?_⟩
  · exact (hWmem z).mpr (by rw [hzface]; linarith [hh])
  · have hOeq : (B ∩ W ∩ L) ∩ frontier f = (B ∩ W ∩ L) ∩ face := by
      ext y; constructor
      · rintro ⟨hyO, hyfr⟩; exact ⟨hyO, (key y hyO).mp hyfr⟩
      · rintro ⟨hyO, hyfr⟩; exact ⟨hyO, (key y hyO).mpr hyfr⟩
    calc (B ∩ W ∩ L) ∩ (P.carrier ∩ frontier f)
        = ((B ∩ W ∩ L) ∩ frontier f) ∩ P.carrier := by
          ext y; simp only [Set.mem_inter_iff]; tauto
      _ = ((B ∩ W ∩ L) ∩ face) ∩ P.carrier := by rw [hOeq]
      _ = (B ∩ W ∩ L) ∩ P.carrier ∩ face := by
          ext y; simp only [Set.mem_inter_iff]; tauto

end Work.Drive.Mono
