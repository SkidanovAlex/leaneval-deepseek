import Mathlib
import Submission.Work.Drive.Mono.JunctionGen
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.TraceLocalModels
import Submission.Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds
import Submission.Work.Drive.Mono.isLocallyEuclidean_trace_spherePoint_outsideSlab
import Submission.Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction
import Submission.Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace
import Submission.Work.Drive.Mono.hdir_of_htrans
import Submission.Work.Drive.Mono.closure_and_uniqueness_of_sphereFace
import Submission.Work.Drive.Mono.corner_locallyEuclidean_of_activeFace
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Topology.SphereSlicing.frontier_PBox

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## 0. Elementary infrastructure for the trace -/

/-- The closed tilted slab is invariant under flipping the normal and the shift. -/
private theorem tiltedSlabClosed_neg (a : ℝ) (v : R3) (h : ℝ) :
    Work.Drive.EpsForm.tiltedSlabClosed (-a) (-v) h =
      Work.Drive.EpsForm.tiltedSlabClosed a v h := by
  ext y
  simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, inner_neg_left]
  rw [show -inner ℝ v y - -a = -(inner ℝ v y - a) from by ring, abs_neg]

/-- The removed set of a level is invariant under flipping the slab normal and the shift. -/
private theorem tiltedLevelRemoved_neg (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    tiltedLevelRemoved s c σ (-u) (-v) h ℓ lam = tiltedLevelRemoved s c σ u v h ℓ lam := by
  rw [tiltedLevelRemoved, tiltedLevelRemoved,
    show inner ℝ (-v) c + -u = -(inner ℝ v c + u) from by
      rw [inner_neg_left]; ring]
  rw [tiltedSlabClosed_neg]

/-- A point of the removed set of a level outside the closed slab and in the box is an interior
point of the removed set. -/
private theorem mem_interior_tiltedLevelRemoved_of_slab_lt {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {y : R3}
    (hy : y ∈ Submission.PBox s c σ)
    (hslab : h < |inner ℝ v y - (inner ℝ v c + u)|) :
    y ∈ interior (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  have hsub : {x : R3 | h < |inner ℝ v x - (inner ℝ v c + u)|} ∩ Submission.PBox s c σ ⊆
      tiltedLevelRemoved s c σ u v h ℓ lam := by
    rintro x ⟨hx1, hx2⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    refine ⟨hx2, ?_⟩
    intro hc
    have hx1' : h < |inner ℝ v x - (inner ℝ v c + u)| := hx1
    have hc' : |inner ℝ v x - (inner ℝ v c + u)| ≤ h := hc.1
    exact absurd hc' (not_le.mpr hx1')
  exact interior_maximal hsub
    ((isOpen_lt continuous_const (continuous_abs.comp
      ((continuous_const.inner continuous_id).sub continuous_const))).inter
        (Work.Topology.SphereSlicing.isOpen_PBox s c σ)) ⟨hslab, hy⟩

/-- A point of the box above the level is an interior point of the removed set. -/
private theorem mem_interior_tiltedLevelRemoved_of_lt {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {y : R3}
    (hy : y ∈ Submission.PBox s c σ) (hyl : lam < ℓ y) :
    y ∈ interior (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  have hsub : {x : R3 | lam < ℓ x} ∩ Submission.PBox s c σ ⊆
      tiltedLevelRemoved s c σ u v h ℓ lam := by
    rintro x ⟨hx1, hx2⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    refine ⟨hx2, ?_⟩
    intro hc
    have hx1' : lam < ℓ x := hx1
    have hc' : ℓ x < lam := hc.2
    exact absurd hx1' (not_lt.mpr (le_of_lt hc'))
  exact interior_maximal hsub
    ((isOpen_lt continuous_const ℓ.continuous).inter
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ)) ⟨hyl, hy⟩

/-- A point strictly inside the slab and strictly below the level is not even in the closure of the
removed set. -/
private theorem notMem_closure_tiltedLevelRemoved_of_slab_below {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {y : R3}
    (hslab : |inner ℝ v y - (inner ℝ v c + u)| < h) (hyl : ℓ y < lam) :
    y ∉ closure (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  have hsub : {x : R3 | |inner ℝ v x - (inner ℝ v c + u)| < h} ∩ {x : R3 | ℓ x < lam} ⊆
      (tiltedLevelRemoved s c σ u v h ℓ lam)ᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxmem
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff] at hxmem
    have hmemS : x ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
      simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]
      exact le_of_lt hx.1
    exact hxmem.2 ⟨hmemS, hx.2⟩
  have hopen : IsOpen ({x : R3 | |inner ℝ v x - (inner ℝ v c + u)| < h} ∩ {x : R3 | ℓ x < lam}) :=
    (isOpen_lt (continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const))
      continuous_const).inter (isOpen_lt ℓ.continuous continuous_const)
  have hyint : y ∈ interior ((tiltedLevelRemoved s c σ u v h ℓ lam)ᶜ) :=
    interior_maximal hsub hopen ⟨hslab, hyl⟩
  rwa [interior_compl] at hyint

/-- A point outside the closure of the box is outside the closure of the removed set. -/
private theorem notMem_closure_tiltedLevelRemoved_of_notMem_closure_PBox {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {y : R3}
    (hy : y ∉ closure (Submission.PBox s c σ)) :
    y ∉ closure (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  intro hcon
  refine hy (closure_mono ?_ hcon)
  intro x hx
  rw [tiltedLevelRemoved] at hx
  exact hx.1

/-- The closure of the box is contained in the sublevel set of the box norm. -/
private theorem closure_PBox_subset_boxNorm_le (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    closure (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} :=
  closure_minimal (fun _ hy => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hy))
    (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const)

/-- A point of the removed set's frontier has box norm `≤ s`. -/
private theorem boxNorm_le_of_mem_frontier_tiltedLevelRemoved {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {y : R3}
    (hy : y ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :
    Submission.boxNorm c σ y ≤ s := by
  refine closure_PBox_subset_boxNorm_le s c σ (closure_mono ?_ (frontier_subset_closure hy))
  intro x hx
  rw [tiltedLevelRemoved] at hx
  exact hx.1

/-- A point in the interior of the removed set is not in its frontier. -/
private theorem notMem_frontier_of_mem_interior {f : Set R3} {y : R3} (hy : y ∈ interior f) :
    y ∉ frontier f := fun hcon => hcon.2 hy

/-- The derivative of the pull-back of a linear functional is constant on the fibres of the
parametrisation. -/
private theorem fderiv_pullback_eq_of_par_eq {ψ : Submission.Diffeo} (φ : R3 →L[ℝ] ℝ) {p p' : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') :
    fderiv ℝ (fun q : ℝ × ℝ => φ (Work.BoxShrink.Pinch.par ψ q)) p =
      fderiv ℝ (fun q : ℝ × ℝ => φ (Work.BoxShrink.Pinch.par ψ q)) p' := by
  have hsw : (fun q : ℝ × ℝ => φ (Work.BoxShrink.Pinch.par ψ q)) =
      Work.Drive.EpsForm.sweepHeight ψ φ := by
    funext q
    simp only [Work.Drive.EpsForm.sweepHeight, Work.Smooth.Morse.pullback,
      Work.BoxShrink.Pinch.par_def]
  rw [hsw]
  obtain ⟨k, m, hk, hm⟩ := (Work.Drive.EpsForm.par_eq_iff ψ p p').mp hp
  have hx : p = (p'.1 - (((-k : ℤ) : ℝ)) * (2 * Real.pi),
      p'.2 - (((-m : ℤ) : ℝ)) * (2 * Real.pi)) := by
    ext
    · rw [hk]; push_cast; ring
    · rw [hm]; push_cast; ring
  rw [hx]
  exact Work.Drive.EpsForm.fderiv_sweepHeight_periodic ψ φ (-k) (-m) p'

/-- **Packaging**: if on an open set `O` the trace of the level (inside the surface `P`) is the
restriction of an open set `C` whose trace at `z` is locally Euclidean, then the trace is locally
Euclidean at `z`. -/
private theorem localModel_of_frontier_eq {P : Set R3} {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {z : R3} {O C : Set R3}
    (hO : IsOpen O) (hzO : z ∈ O)
    (heq : O ∩ (P ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) = O ∩ (P ∩ C))
    (hmodel : ∃ O' : Set R3, IsOpen O' ∧ z ∈ O' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean (O' ∩ (P ∩ C))) :
    ∃ O'' : Set R3, IsOpen O'' ∧ z ∈ O'' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O'' ∩ (P ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨O', hO'open, hzO', hloc⟩ := hmodel
  refine ⟨O ∩ O', hO.inter hO'open, ⟨hzO, hzO'⟩, ?_⟩
  have hset : (O ∩ O') ∩ (P ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
      = (O ∩ O') ∩ (P ∩ C) := by
    ext x
    constructor
    · rintro ⟨⟨hxO, hxO'⟩, hx⟩
      have h1 : x ∈ O ∩ (P ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
        ⟨hxO, hx⟩
      rw [heq] at h1
      exact ⟨⟨hxO, hxO'⟩, h1.2⟩
    · rintro ⟨⟨hxO, hxO'⟩, hx⟩
      have h1 : x ∈ O ∩ (P ∩ C) := ⟨hxO, hx⟩
      rw [← heq] at h1
      exact ⟨⟨hxO, hxO'⟩, h1.2⟩
  rw [hset]
  refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn ?_ ?_ hloc
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.2, hx2⟩
  · show IsOpen (((Subtype.val ⁻¹' ((O ∩ O') ∩ (P ∩ C))) : Set ↥(O' ∩ (P ∩ C))))
    have hV : ((Subtype.val ⁻¹' ((O ∩ O') ∩ (P ∩ C))) : Set ↥(O' ∩ (P ∩ C)))
        = (Subtype.val ⁻¹' O : Set ↥(O' ∩ (P ∩ C))) := by
      ext x
      constructor
      · intro hx; exact hx.1.1
      · intro hx; exact ⟨⟨hx, x.2.1⟩, x.2.2⟩
    rw [hV]
    exact hO.preimage continuous_subtype_val


/-! ## 1. The sign of a face and the uniqueness of the active face -/

/-- The sign of the `σ i`-th coordinate of `z - c`. -/
private def faceSign (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) : ℝ :=
  if 0 ≤ z (σ i) - c (σ i) then 1 else -1

private theorem faceSign_eq_one_or_neg_one (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) :
    faceSign c σ z i = 1 ∨ faceSign c σ z i = -1 := by
  unfold faceSign
  split_ifs <;> simp

/-- The signed face with the sign of the coordinate is the face norm. -/
private theorem faceLin_faceSign (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) :
    Work.Smooth.BoxGeneric.faceLin c σ i (faceSign c σ z i) z =
      Work.Smooth.BoxGeneric.faceNorm c σ i z := by
  have hkey : faceSign c σ z i * (z (σ i) - c (σ i)) = |z (σ i) - c (σ i)| := by
    unfold faceSign
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · push_neg at h; rw [abs_of_neg h]; ring
  rw [Work.Smooth.BoxGeneric.faceLin_apply, Work.Smooth.BoxGeneric.signedFace,
    Work.Smooth.BoxGeneric.faceNorm_apply, ← hkey, mul_div_assoc]

/-- **The active face of the box sphere at a point of the surface at a non-exceptional level is
unique**, by clause (c) of `JunctionGen`. -/
private theorem unique_activeFace_of_junctionGen {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    {z : R3}
    (hJ : JunctionGen ψ s c σ u v h ℓ exc lam0 lam1) (hlam : lam ∈ Set.Icc lam0 lam1)
    (hne : lam ∉ (exc : Set ℝ)) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s) (hzl : ℓ z = lam) :
    ∃ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z ∧
      ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s := by
  obtain ⟨i, hi⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ z
  have hi' : Work.Smooth.BoxGeneric.faceNorm c σ i z = s := by rw [hi, hzS]
  refine ⟨i, faceSign c σ z i, faceSign_eq_one_or_neg_one c σ z i, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [faceLin_faceSign, hi']
    · intro j
      have h1 := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z
      rwa [hzS] at h1
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hj' : Work.Smooth.BoxGeneric.faceNorm c σ j z = s :=
      le_antisymm (by
        have h1 := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z
        rwa [hzS] at h1) hcon
    have hext : ∃ i' j' : Fin 3, i' ≠ j' ∧ |z (σ i') - c (σ i')| = Submission.boxSide i' * s ∧
        |z (σ j') - c (σ j')| = Submission.boxSide j' * s := by
      refine ⟨i, j, hj.symm, ?_, ?_⟩
      · have h2 := hi'
        rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_iff (ne_of_gt (Submission.boxSide_pos i))]
          at h2
        simpa [mul_comm] using h2
      · have h2 := hj'
        rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_iff (ne_of_gt (Submission.boxSide_pos j))]
          at h2
        simpa [mul_comm] using h2
    have := hJ.2.2.1 z hz hext
    rw [hzl] at this
    exact hne this

/-! ## 2. Converting the existential regularity of the face functional to the universal form -/

/-- The pull-back of a linear functional along `par` has the same derivative at any two parameter
points over the same point of the surface.  Consequently an existential regularity statement is a
universal one. -/
private theorem fderiv_inner_par_ne_zero_of_exists {ψ : Submission.Diffeo} {v : R3} {z : R3}
    {p₀ : ℝ × ℝ} (hp₀ : Work.BoxShrink.Pinch.par ψ p₀ = z)
    (h₀ : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀ ≠ 0) :
    ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
  intro p hp
  have hfun : (fun q : ℝ × ℝ => (innerSL ℝ) v (Work.BoxShrink.Pinch.par ψ q))
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) := by
    funext q
    exact innerSL_apply_apply ℝ v _
  have h1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀ := by
    have h := fderiv_pullback_eq_of_par_eq (ψ := ψ) ((innerSL ℝ) v) (p := p) (p' := p₀)
      (by rw [hp, hp₀])
    rwa [hfun] at h
  rw [h1]
  exact h₀

/-! ## 3. The sweep height of the flipped normal -/

private theorem sweepHeight_neg (ψ : Submission.Diffeo) (v : R3) :
    Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (-v))
      = fun q : ℝ × ℝ => -(inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := by
  rw [Work.Drive.EpsForm.sweepHeight_innerSL]
  funext q
  rw [inner_neg_left]

/-! ## 4. The trace at a point of the box sphere where the removed set is locally the box -/

/-- **The trace at a point of the box sphere where the removed set is locally the box.**  If on an
open set `O` around a point `z` of the box sphere the removed set of the level agrees with the box,
then the trace near `z` is the surface's part of the box sphere, which is a single curve of the
slicing: it is locally Euclidean. -/
private theorem localModel_of_eq_PBox {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3} {O : Set R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hO : IsOpen O) (hzO : z ∈ O)
    (heq : tiltedLevelRemoved s c σ u v h ℓ lam ∩ O = Submission.PBox s c σ ∩ O) :
    ∃ O' : Set R3, IsOpen O' ∧ z ∈ O' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  obtain ⟨Sl⟩ := hslice
  obtain ⟨i₀, ρ, hρpos, hball⟩ :=
    exists_ball_inter_eq_range_of_sphereSlicing Sl ⟨hz, hzS⟩
  have hfr0 : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ O =
      Work.BoxShrink.Core.sphereSet c σ s ∩ O :=
    frontier_tiltedLevelRemoved_inter_of_eq_PBox (s := s) (u := u) (c := c) (σ := σ) (v := v)
      (h := h) (ℓ := ℓ) (lam := lam) hs hO heq
  have hfr : frontier (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ (O ∩ Metric.ball z ρ) =
      Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ) := by
    rw [← Set.inter_assoc, hfr0, Set.inter_assoc]
  have hSeq : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Work.BoxShrink.Core.sphereSet c σ s =
      ⋃ i, Set.range (Sl.c i).γ := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        (Work.InnermostDisk.carrier_inter_subset_iUnion_range_of_sphereSlicing Sl hy)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact ⟨(Sl.c i).range_subset_carrier hi,
        by obtain ⟨t, rfl⟩ := hi; exact Sl.mem i t⟩
  have hdisj_ball : ∀ i : Sl.ι, i ≠ i₀ →
      Metric.ball z ρ ∩ Set.range (Sl.c i).γ = ∅ := by
    intro i hi
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyb, hyi⟩
    have hy2 : y ∈ Metric.ball z ρ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        Work.BoxShrink.Core.sphereSet c σ s) :=
      ⟨hyb, (Sl.c i).range_subset_carrier hyi,
        by obtain ⟨t, rfl⟩ := hyi; exact Sl.mem i t⟩
    rw [hball] at hy2
    exact Set.disjoint_left.mp (Sl.disjoint hi) hyi hy2.2
  have hEqS : (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        Work.BoxShrink.Core.sphereSet c σ s) =
      (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        Set.range (Sl.c i₀).γ) := by
    rw [show (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          Work.BoxShrink.Core.sphereSet c σ s)
        = O ∩ (Metric.ball z ρ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          Work.BoxShrink.Core.sphereSet c σ s)) from by
          ext x; simp only [Set.mem_inter_iff]; tauto,
      hball,
      show O ∩ (Metric.ball z ρ ∩ Set.range (Sl.c i₀).γ)
          = (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            Set.range (Sl.c i₀).γ) from by
          ext x
          simp only [Set.mem_inter_iff]
          constructor
          · rintro ⟨hxO, hxb, hxr⟩
            exact ⟨⟨hxO, hxb⟩, (Sl.c i₀).range_subset_carrier hxr, hxr⟩
          · rintro ⟨⟨hxO, hxb⟩, -, hxr⟩
            exact ⟨hxO, hxb, hxr⟩]
  have htrace : (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) =
      (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        Set.range (Sl.c i₀).γ) := by
    calc (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
        = (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ (frontier
            (tiltedLevelRemoved s c σ u v h ℓ lam) ∩ (O ∩ Metric.ball z ρ)) := by
          ext x; simp only [Set.mem_inter_iff]; tauto
      _ = (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            (Work.BoxShrink.Core.sphereSet c σ s ∩ (O ∩ Metric.ball z ρ)) := by rw [hfr]
      _ = (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            Work.BoxShrink.Core.sphereSet c σ s) := by
          ext x; simp only [Set.mem_inter_iff]; tauto
      _ = (O ∩ Metric.ball z ρ) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            Set.range (Sl.c i₀).γ) := hEqS
  refine ⟨O ∩ Metric.ball z ρ, hO.inter Metric.isOpen_ball,
    ⟨hzO, Metric.mem_ball_self hρpos⟩, ?_⟩
  rw [htrace]
  have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean (Set.range (Sl.c i₀).γ) :=
    Work.EpsW.localEuclidean_range_of_periodic_injOn (Sl.c i₀).cont (Sl.c i₀).periodic
      (Sl.simple i₀)
  refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn ?_ ?_ hloc
  · intro x hx
    exact hx.2.2
  · show IsOpen ((Subtype.val ⁻¹' ((O ∩ Metric.ball z ρ) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Set.range (Sl.c i₀).γ))) :
        Set ↥(Set.range (Sl.c i₀).γ))
    have hVe : ((Subtype.val ⁻¹' ((O ∩ Metric.ball z ρ) ∩
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Set.range (Sl.c i₀).γ))) :
        Set ↥(Set.range (Sl.c i₀).γ)) =
        (Subtype.val ⁻¹' (O ∩ Metric.ball z ρ) : Set ↥(Set.range (Sl.c i₀).γ)) := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, (Sl.c i₀).range_subset_carrier x.2, x.2⟩
    rw [hVe]
    exact (hO.inter Metric.isOpen_ball).preimage continuous_subtype_val

/-- The trace at a point of the box sphere strictly above the level. -/
private theorem localModel_spherePoint_of_lt_level {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s) (hzl : lam < ℓ z) :
    ∃ O' : Set R3, IsOpen O' ∧ z ∈ O' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  refine localModel_of_eq_PBox hs hslice hz hzS
    (isOpen_lt continuous_const ℓ.continuous) (by simpa using hzl) ?_
  ext y
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved] at hyf
    exact ⟨hyf.1, hyO⟩
  · rintro ⟨hyP, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    refine ⟨hyP, ?_⟩
    intro hc
    have hc' : ℓ y < lam := hc.2
    exact absurd hyO (not_lt.mpr (le_of_lt hc'))

/-- The trace at a point of the box sphere strictly outside the slab. -/
private theorem localModel_spherePoint_outsideSlab {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hzout : h < |inner ℝ v z - (inner ℝ v c + u)|) :
    ∃ O' : Set R3, IsOpen O' ∧ z ∈ O' ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  refine localModel_of_eq_PBox hs hslice hz hzS
    (isOpen_lt continuous_const (continuous_abs.comp
      ((continuous_const.inner continuous_id).sub continuous_const)))
    (by simpa using hzout) ?_
  ext y
  constructor
  · rintro ⟨hyf, hyO⟩
    rw [tiltedLevelRemoved] at hyf
    exact ⟨hyf.1, hyO⟩
  · rintro ⟨hyP, hyO⟩
    refine ⟨?_, hyO⟩
    rw [tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff]
    refine ⟨hyP, ?_⟩
    intro hc
    have hyO' : h < |inner ℝ v y - (inner ℝ v c + u)| := hyO
    have hc' : |inner ℝ v y - (inner ℝ v c + u)| ≤ h := hc.1
    exact absurd hc' (not_le.mpr hyO')

/-! ## 5. The middle of the two relation-invariance lemmas -/

/-- The set-theoretic form of the corner `{boxNorm ≤ s ∧ k ≤ φ ∧ (boxNorm = s ∨ φ = k)}`. -/
private theorem max_corner_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (φ : R3 →L[ℝ] ℝ) (k : ℝ)
    (y : R3) :
    (max (Submission.boxNorm c σ y - s) (k - φ y) = 0) ↔
      Submission.boxNorm c σ y ≤ s ∧ k ≤ φ y ∧
        (Submission.boxNorm c σ y = s ∨ φ y = k) := by
  rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by rcases h3 with h | h <;> [left; right] <;> linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by rcases h3 with h | h <;> [left; right] <;> linarith⟩


/-! ## 6. The two junction local models -/

/-- The sweep height is the pull-back of the functional along `par`. -/
private theorem sweepHeight_eq_par (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) :
    Work.Drive.EpsForm.sweepHeight ψ ℓ = fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q) := by
  funext q
  simp only [Work.Drive.EpsForm.sweepHeight, Work.Smooth.Morse.pullback,
    Work.BoxShrink.Pinch.par_def]

/-- The `innerSL`-pull-back is the `inner`-pull-back. -/
private theorem innerSL_par_eq (ψ : Submission.Diffeo) (v : R3) :
    (fun q : ℝ × ℝ => (innerSL ℝ) v (Work.BoxShrink.Pinch.par ψ q))
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) := by
  funext q
  exact innerSL_apply_apply ℝ v _

/-- The (negated) sweep height of the flipped normal is regular where the face functional is. -/
private theorem fderiv_sweepHeight_neg_ne_zero {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    (h : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) :
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (-v))) p ≠ 0 := by
  have hfun : (fun q : ℝ × ℝ => -(inner ℝ v (Work.BoxShrink.Pinch.par ψ q)))
      = -(fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := rfl
  rw [sweepHeight_neg ψ v, hfun, fderiv_neg]
  simpa using h

/-- The transversality with the flipped face functional. -/
private theorem faceTrans_neg {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    {q : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : ∀ t : ℝ, q ≠ t • fderiv ℝ (fun q' : ℝ × ℝ => inner ℝ v
      (Work.BoxShrink.Pinch.par ψ q')) p) :
    ∀ t : ℝ, q ≠ t • fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (-v))) p := by
  have hfun : (fun q : ℝ × ℝ => -(inner ℝ v (Work.BoxShrink.Pinch.par ψ q)))
      = -(fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := rfl
  intro t ht
  rw [sweepHeight_neg ψ v, hfun, fderiv_neg] at ht
  refine h (-t) ?_
  rw [ht, smul_neg, ← neg_smul]

/-- **The trace at a wall ∩ box-sphere junction**: a point of the surface on the box sphere,
strictly inside the slab and at the level, where the level crosses the box sphere transversally.
The trace is the "V" of the wall inside the box and of the box-sphere trace above the wall. -/
private theorem localModel_wallSphere {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3} {i : Fin 3} {ε : ℝ}
    (hs : 0 < s) (hℓne : ℓ ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z = lam)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s)
    (hdata : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨p, hp, hF, hB, hind⟩ := hdata
  obtain ⟨δ, hδpos, hδ⟩ := hdir_of_htrans (v := v) (h := h) (u := u) hs hℓne hzS hzl hp hB hind
  obtain ⟨O₁, hO₁open, hzO₁, hident⟩ :=
    frontier_tiltedLevelRemoved_wallSphereJunction hs hℓne hzS hzslab hzl ⟨δ, hδpos, hδ⟩
  have hsweep : (fun q : ℝ × ℝ => ℓ (Work.BoxShrink.Pinch.par ψ q))
      = Work.Drive.EpsForm.sweepHeight ψ ℓ := (sweepHeight_eq_par ψ ℓ).symm
  obtain ⟨O₂, hO₂open, hzO₂, hloc⟩ :=
    Work.Drive.Mono.corner_locallyEuclidean_of_activeFace (ψ := ψ) (c := c) (σ := σ) (s := s)
      (φ := ℓ) (k := lam) (z := z) (i := i) (ε := ε) hs hε hz hact huniq hzl
      ⟨p, hp, by rwa [hsweep], hB, by
        intro t ht
        exact hind t (by rwa [hsweep] at ht)⟩
  have hC : {y : R3 | Submission.boxNorm c σ y ≤ s ∧ ℓ y ≥ lam ∧
      (Submission.boxNorm c σ y = s ∨ ℓ y = lam)}
      = {y : R3 | max (Submission.boxNorm c σ y - s) (lam - ℓ y) = 0} := by
    ext y
    simp only [Set.mem_setOf_eq]
    exact (max_corner_iff s c σ ℓ lam y).symm
  have h1 : O₁ ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)
      = O₁ ∩ {y : R3 | max (Submission.boxNorm c σ y - s) (lam - ℓ y) = 0} := by
    have h0 : O₁ ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) = O₁ ∩ {y : R3 |
        Submission.boxNorm c σ y ≤ s ∧ ℓ y ≥ lam ∧
          (Submission.boxNorm c σ y = s ∨ ℓ y = lam)} := by
      ext y
      exact ⟨fun hy => ⟨hy.1, (hident y hy.1).mp hy.2⟩,
        fun hy => ⟨hy.1, (hident y hy.1).mpr hy.2⟩⟩
    rwa [hC] at h0
  have heq : O₁ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam))
      = O₁ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        {y : R3 | max (Submission.boxNorm c σ y - s) (lam - ℓ y) = 0}) := by
    ext y
    constructor
    · rintro ⟨hy1, hy2, hy3⟩
      have hmem : y ∈ O₁ ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := ⟨hy1, hy3⟩
      rw [h1] at hmem
      exact ⟨hy1, hy2, hmem.2⟩
    · rintro ⟨hy1, hy2, hy3⟩
      have hmem : y ∈ O₁ ∩ {y : R3 |
          max (Submission.boxNorm c σ y - s) (lam - ℓ y) = 0} := ⟨hy1, hy3⟩
      rw [← h1] at hmem
      exact ⟨hy1, hy2, hmem.2⟩
  exact localModel_of_frontier_eq (P := (Work.Drive.EpsSphere.torusOf ψ).carrier)
    hO₁open hzO₁ heq ⟨O₂, hO₂open, hzO₂, hloc⟩


/-- The universal form of the regularity of the sweep height, from the existential one. -/
private theorem fderiv_sweepHeight_forall_of_exists {ψ : Submission.Diffeo} {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (h : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) :
    ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 := by
  obtain ⟨p₀, hp₀, h₀⟩ := h
  rw [sweepHeight_eq_par] at h₀
  intro p hp
  rw [sweepHeight_eq_par]
  rw [fderiv_pullback_eq_of_par_eq (p := p) (p' := p₀) ℓ (by rw [hp, hp₀])]
  exact h₀

/-! ## 7. The face-flip conversions and the lower-face reductions -/

/-- Membership in the closed tilted slab. -/
private theorem mem_tiltedSlabClosed_iff {s u : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {h : ℝ}
    {y : R3} :
    y ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔
      |inner ℝ v y - (inner ℝ v c + u)| ≤ h := by
  simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq]

/-- The face regularity in its universal form, from the existential hypothesis. -/
private theorem faceReg_forall_of_exists {ψ : Submission.Diffeo} {v : R3} {z : R3}
    (h : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) :
    ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) p ≠ 0 := by
  obtain ⟨p₀, hp₀, h₀⟩ := h
  intro p hp
  have h1 := fderiv_inner_par_ne_zero_of_exists hp₀ h₀ p hp
  rwa [Work.Drive.EpsForm.sweepHeight_innerSL]

/-- Differentiating the negative of a pull-back. -/
private theorem fderiv_inner_neg_ne_zero {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    (h : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (-v) (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
  have hfun : (fun q : ℝ × ℝ => inner ℝ (-v) (Work.BoxShrink.Pinch.par ψ q))
      = -(fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := by
    funext q
    rw [inner_neg_left]
    rfl
  rw [hfun, fderiv_neg]
  simpa using h

/-- The transversality for the negative of a pull-back. -/
private theorem fderiv_inner_neg_ne_smul {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    {θ : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      ≠ t • θ) :
    ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ (-v) (Work.BoxShrink.Pinch.par ψ q)) p
      ≠ t • θ := by
  have hfun : (fun q : ℝ × ℝ => inner ℝ (-v) (Work.BoxShrink.Pinch.par ψ q))
      = -(fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) := by
    funext q
    rw [inner_neg_left]
    rfl
  intro t ht
  rw [hfun, fderiv_neg] at ht
  refine h (-t) ?_
  calc fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p
      = -(-fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :=
        (neg_neg _).symm
    _ = -(t • θ) := by rw [ht]
    _ = (-t) • θ := (neg_smul t θ).symm

/-- The face regularity of the flipped normal (universal form). -/
private theorem faceReg_neg {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    (h : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) p ≠ 0) :
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (-v))) p ≠ 0 := by
  rw [Work.Drive.EpsForm.sweepHeight_innerSL] at h
  exact fderiv_sweepHeight_neg_ne_zero h

/-- The transversality of the flipped normal (universal form). -/
private theorem faceTrans_neg2 {ψ : Submission.Diffeo} {v : R3} {p : ℝ × ℝ}
    {q : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : ∀ t : ℝ, q ≠ t • fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) p) :
    ∀ t : ℝ, q ≠ t • fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (-v))) p := by
  rw [Work.Drive.EpsForm.sweepHeight_innerSL] at h
  exact faceTrans_neg h

/-- A local model for the flipped slab gives one for the slab. -/
private theorem localModel_of_neg {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hmodel : ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ (-u) (-v) h ℓ lam)))) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨O, hO, hzO, hloc⟩ := hmodel
  exact ⟨O, hO, hzO, by rwa [tiltedLevelRemoved_neg s c σ u v h ℓ lam] at hloc⟩

/-! ## 8. The assembly -/

/-- **The trace of a level of the tilted sweep is locally Euclidean at every point**, from the
stratified genericity of the junction data. -/
theorem trace_localModels_of_junctionGen {ψ : Submission.Diffeo} {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hfaceReg : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hT : Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : Work.Drive.Mono.JunctionGen ψ s c σ u v h ℓ exc lam0 lam1)
    (hlam : lam ∈ Set.Icc lam0 lam1) (hne : lam ∉ (exc : Set ℝ)) :
    ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  intro z hz
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hT
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := hz.1
  have hzfr : z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := hz.2
  have hface_or : ∀ w : R3, |inner ℝ v w - (inner ℝ v c + u)| = h →
      inner ℝ v w = inner ℝ v c + u + h ∨ inner ℝ v w = inner ℝ v c + u - h := by
    intro w hw
    rcases (abs_eq (le_of_lt hh)).mp hw with h2 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hb_le : Submission.boxNorm c σ z ≤ s :=
    boxNorm_le_of_mem_frontier_tiltedLevelRemoved hzfr
  rcases lt_or_ge (Submission.boxNorm c σ z) s with hlt | hge
  · -- ### the point is inside the box
    have hzP : z ∈ Submission.PBox s c σ := (Submission.mem_PBox_iff s c σ z).mpr hlt
    rcases lt_trichotomy |inner ℝ v z - (inner ℝ v c + u)| h with hslab | hslab | hslab
    · -- strictly inside the slab
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · exact absurd (frontier_subset_closure hzfr)
          (notMem_closure_tiltedLevelRemoved_of_slab_below hslab hzlam)
      · -- the interior of the wall
        refine Work.Drive.Mono.isLocallyEuclidean_trace_of_wallPoint hℓne hzc hzP hslab hzlam ?_
        intro p hp
        refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
        simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp]
        exact le_of_lt hslab
      · exact absurd hzfr (notMem_frontier_of_mem_interior
          (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
    · -- on a face of the slab
      rcases hface_or z hslab with hf | hf
      · -- upper face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- interior of a face
          exact Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint hv hh hzc hzP hf hzlam
            (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab))
        · -- wall ∩ face
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction hv hh hℓne hzc hzP
            hf hzlam ?_ ?_ ?_
          · intro p hp
            refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring, abs_of_pos hh]
          · exact faceReg_forall_of_exists (hfaceReg z hzc hzP hslab)
          · intro p hp t
            have h2 := hgen.2.1 lam hne p (by rwa [hp])
              (by rw [hp, hf]
                  rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring,
                    abs_of_pos hh])
              (by rw [hp]; exact hzlam) t
            rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ v]
            exact h2
        · exact absurd hzfr (notMem_frontier_of_mem_interior
            (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
      · -- lower face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- interior of a face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint (ψ := ψ) (s := s) (u := -u)
            (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            (by simpa using hv) hh hzc hzP ?_ hzlam ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · intro p hp
            exact faceReg_neg (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab) p hp)
        · -- wall ∩ face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction (ψ := ψ) (s := s)
            (u := -u) (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            (by simpa using hv) hh hℓne hzc hzP ?_ hzlam ?_ ?_ ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · intro p hp
            refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u - h - (inner ℝ v c + u) = -h from by ring, abs_neg,
              abs_of_pos hh]
          · intro p hp
            exact faceReg_neg (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab) p hp)
          · intro p hp t
            refine faceTrans_neg2 ?_ t
            intro t'
            have h2 := hgen.2.1 lam hne p (by rwa [hp])
              (by rw [hp, hf]
                  rw [show inner ℝ v c + u - h - (inner ℝ v c + u) = -h from by ring, abs_neg,
                    abs_of_pos hh])
              (by rw [hp]; exact hzlam) t'
            rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ v]
            exact h2
        · exact absurd hzfr (notMem_frontier_of_mem_interior
            (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
    · -- outside the slab
      exact absurd hzfr (notMem_frontier_of_mem_interior
        (mem_interior_tiltedLevelRemoved_of_slab_lt hzP hslab))
  · -- ### the point is on the box sphere
    have hbS : Submission.boxNorm c σ z = s := le_antisymm hb_le hge
    rcases lt_trichotomy |inner ℝ v z - (inner ℝ v c + u)| h with hslab | hslab | hslab
    · -- strictly inside the slab
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · exact absurd (frontier_subset_closure hzfr)
          (notMem_closure_tiltedLevelRemoved_of_slab_below hslab hzlam)
      · -- wall ∩ box sphere: the "V" of the wall and the box sphere
        obtain ⟨p, hp, hF, hB, hind⟩ := hJ.1 lam hlam hne z hzc hbS (le_of_lt hslab) hzlam
        obtain ⟨i, ε, hε, hact, huniq⟩ :=
          unique_activeFace_of_junctionGen hJ hlam hne hzc hbS hzlam
        exact localModel_wallSphere hs hℓne hε hzc hbS hslab hzlam hact huniq
          ⟨p, hp, hF, hB, hind⟩
      · -- above the wall: the trace is the box sphere
        exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- on a face of the slab
      rcases hface_or z hslab with hf | hf
      · -- upper face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := hJ.2.1 lam hlam hne z hzc hbS hslab hzlam
          exact Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction hs hv hh hzc hbS
            hf hzlam ⟨p, hp, hd1, hd2, hd3⟩
        · -- triple point: forbidden by the genericity of the levels of the face points
          exact absurd (by rw [← hzlam]; exact hJ.2.2.2 z hzc hbS hslab) hne
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
      · -- lower face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := hJ.2.1 lam hlam hne z hzc hbS hslab hzlam
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction (ψ := ψ) (s := s)
            (u := -u) (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            hs (by simpa using hv) hh hzc hbS ?_ hzlam ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · exact ⟨p, hp, fderiv_inner_neg_ne_zero hd1, hd2, fderiv_inner_neg_ne_smul hd3⟩
        · -- triple point
          exact absurd (by rw [← hzlam]; exact hJ.2.2.2 z hzc hbS hslab) hne
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- outside the slab: the trace is the box sphere
      exact localModel_spherePoint_outsideSlab hs hslice hzc hbS hslab

end

end Work.Drive.Mono
