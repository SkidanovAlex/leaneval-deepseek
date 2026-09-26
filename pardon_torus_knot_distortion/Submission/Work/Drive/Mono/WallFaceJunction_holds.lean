import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.EpsW.localArc_gluedPair
import Submission.Work.EpsW.exists_half_arc
import Submission.Work.Drive.Mono.LevelSetLocallyEuclidean_holds
import Submission.Work.EpsW.localModel_endpoint
import Submission.Work.Drive.Mono.ProdInvertible_holds

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

/-! ## The trace of the tilted sweep at a wall ∩ face junction

This module proves `Work.Drive.Mono.WallFaceJunction_holds`, the local model of the trace of a level
of the tilted sweep at a point where the level wall meets a face of the tilted slab.

Near such a point `z` the trace is the *corner* built from the half of the level wall inside the
closed slab and the half of the face curve behind the wall.  It is realised as the level set of the
maximum of the two level functions read in the parameter plane (`F = ℓ∘par - lam` and
`G = ⟪v,par·⟫ - (⟪v,c⟫+u+h)`) — the plane model of a transverse corner, locally an arc by
`Work.Smooth.OneManifold.isLocallyArc_max_of_isInvertible`, whose hypothesis is exactly the
invertibility of the pair of derivatives at `z` produced by `htrans`
(`Work.Drive.Mono.ProdInvertible_holds`) — and transported to the surface by
`Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param`.

The pointwise identification of the trace with the plane corner is the private lemma
`frontier_corner_aux` below: above the mid-plane of the slab, the frontier of the level's removed
set is the union of the top face below the level and of the wall inside the slab.
-/

/-- **The frontier of the removed set of a level, above the mid-plane of the slab.**
For a point `y` of the *open* box strictly above the mid-plane `⟪v,·⟫ = ⟪v,c⟫+u` of the tilted
slab, and with the wall functional `ℓ` not a multiple of `⟪v,·⟫` (which is what transversality at
`z` gives), the frontier of the level's removed set is exactly the union of the top face of the slab
below the level and of the wall inside the slab:

`y ∈ frontier (tiltedLevelRemoved …) ↔ (⟪v,y⟫ = ⟪v,c⟫+u+h ∧ ℓ y ≤ lam) ∨ (ℓ y = lam ∧ ⟪v,y⟫ < ⟪v,c⟫+u+h)`.

This is the pointwise form of the local model `Work.Drive.Mono.Trace_eq_planeNear_facePoint_holds`
on the face and of `Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds` in the interior of the
slab, together: the removed set is `f = PBox ∖ (slab ∩ {ℓ < lam})`, so for `y ∈ PBox` one has
`y ∈ closure f ↔ y ∉ interior (slab ∩ {ℓ<lam})` and `y ∈ interior f ↔ y ∉ closure (slab ∩ {ℓ<lam})`,
and the closure lies in the closed slab below the level. -/
private theorem frontier_corner_aux {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3}
    (hv : v ≠ 0) (hh : 0 < h) (hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v)
    (hy : y ∈ Submission.PBox s c σ)
    (habove : inner ℝ v c + u < inner ℝ v y) :
    y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
      (inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y ≤ lam) ∨
      (ℓ y = lam ∧ inner ℝ v y < inner ℝ v c + u + h) := by
  classical
  set a : ℝ := inner ℝ v c + u with hadef
  set C : Set R3 := Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {z : R3 | ℓ z < lam} with hCdef
  set f : Set R3 := Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam with hfdef
  have hf_eq : f = Submission.PBox s c σ \ C := by
    rw [hfdef, hCdef, Work.Drive.Mono.tiltedLevelRemoved, hadef]
  have hPopen : IsOpen (Submission.PBox s c σ) := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hLopen : IsOpen {z : R3 | ℓ z < lam} := isOpen_lt ℓ.continuous continuous_const
  have hCmem : ∀ z : R3, (z ∈ C ↔ |inner ℝ v z - a| ≤ h ∧ ℓ z < lam) := fun z => Iff.rfl
  have hvv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  have hnormpos : 0 < ‖v‖ ^ 2 := by positivity
  have hcontI : Continuous fun z : R3 => inner ℝ v z := continuous_const.inner continuous_id
  -- a direction tangent to the slab faces along which `ℓ` decreases
  have hex : ∃ w : R3, inner ℝ v w = 0 ∧ 0 < ℓ w := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ z : R3, inner ℝ v z = 0 → ℓ z = 0 := by
      intro z hz
      refine le_antisymm (hcon z hz) ?_
      have h := hcon (-z) (by rw [inner_neg_right, hz, neg_zero])
      rw [map_neg] at h
      linarith
    refine hanti (ℓ v / ‖v‖ ^ 2) ?_
    ext z
    have hperp : inner ℝ v (z - (inner ℝ v z / ‖v‖ ^ 2) • v) = 0 := by
      rw [inner_sub_right, inner_smul_right, hvv,
        div_mul_cancel₀ _ (ne_of_gt hnormpos), sub_self]
    calc ℓ z = ℓ ((inner ℝ v z / ‖v‖ ^ 2) • v + (z - (inner ℝ v z / ‖v‖ ^ 2) • v)) := by
          rw [show (inner ℝ v z / ‖v‖ ^ 2) • v + (z - (inner ℝ v z / ‖v‖ ^ 2) • v) = z
            from by abel]
      _ = ℓ ((inner ℝ v z / ‖v‖ ^ 2) • v) + 0 := by rw [map_add, hzero _ hperp, add_zero]
      _ = ((ℓ v / ‖v‖ ^ 2) • (innerSL ℝ) v) z := by
          rw [map_smul, smul_eq_mul]
          simp
          ring
  obtain ⟨w, hwv, hwℓ⟩ := hex
  -- moving along the face into the wall puts a point of `C` arbitrarily close to `y`
  have hmemC_move : |inner ℝ v y - a| ≤ h → ℓ y ≤ lam →
      ∀ ε : ℝ, 0 < ε → ∃ y' : R3, ‖y' - y‖ < ε ∧ y' ∈ C := by
    intro hle hℓle ε hε
    set t : ℝ := ε / (2 * (‖w‖ + 1)) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have htw : t * (‖w‖ + 1) = ε / 2 := by
      rw [htdef, div_mul_eq_mul_div]
      exact mul_div_mul_right ε 2 (by positivity)
    refine ⟨y - t • w, ?_, ?_⟩
    · have h1 : y - t • w - y = -(t • w) := by abel
      rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have hle2 : t * ‖w‖ ≤ t * (‖w‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) (le_of_lt htpos)
      rw [htw] at hle2
      linarith
    · rw [hCmem]
      refine ⟨?_, ?_⟩
      · have hval : inner ℝ v (y - t • w) - a = inner ℝ v y - a := by
          rw [inner_sub_right, inner_smul_right, hwv, mul_zero, sub_zero]
        rw [hval]; exact hle
      · have hval : ℓ (y - t • w) = ℓ y - t * ℓ w := by
          rw [map_sub, map_smul, smul_eq_mul]
        rw [hval]
        have : 0 < t * ℓ w := mul_pos htpos hwℓ
        linarith
  -- on the top face, `y` is a limit of points of `f` (the ray `y + t·v` leaves the slab)
  have hclosuref_ray : inner ℝ v y = a + h → y ∈ closure f := by
    intro hyface
    rw [mem_closure_iff]
    intro U hUo hyU
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp (hUo.inter hPopen) y ⟨hyU, hy⟩
    set t : ℝ := ε / (2 * (‖v‖ + 1)) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have htw : t * (‖v‖ + 1) = ε / 2 := by
      rw [htdef, div_mul_eq_mul_div]
      exact mul_div_mul_right ε 2 (by positivity)
    have hball : y + t • v ∈ U ∩ Submission.PBox s c σ := by
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : y + t • v - y = t • v := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have hle : t * ‖v‖ ≤ t * (‖v‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (le_of_lt htpos)
      rw [htw] at hle
      linarith
    refine ⟨y + t • v, hball.1, ?_⟩
    rw [hf_eq]
    refine ⟨hball.2, ?_⟩
    intro hmemC
    have h2 := (hCmem _).mp hmemC
    have hval : inner ℝ v (y + t • v) - a = h + t * ‖v‖ ^ 2 := by
      rw [inner_add_right, inner_smul_right, hvv, hyface]; ring
    have h3 : |inner ℝ v (y + t • v) - a| ≤ h := h2.1
    have h4 : h < |inner ℝ v (y + t • v) - a| := by
      rw [hval]
      have hpos : 0 < t * ‖v‖ ^ 2 := by positivity
      linarith [le_abs_self (h + t * ‖v‖ ^ 2)]
    linarith
  -- the closure of `C` lies in the closed slab, below the level
  have hclC : closure C ⊆ Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {z : R3 | ℓ z ≤ lam} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have h1 : closure C ⊆ closure (Work.Drive.EpsForm.tiltedSlabClosed a v h) :=
        closure_mono inter_subset_left
      rw [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed a v h).closure_eq] at h1
      exact h1 hz
    · have h1 : closure C ⊆ closure {z : R3 | ℓ z < lam} := closure_mono inter_subset_right
      exact closure_lt_subset_le ℓ.continuous continuous_const (h1 hz)
  -- strictness on both levels puts a point in the interior of `C`
  have hintC_of : ∀ z : R3, |inner ℝ v z - a| < h → ℓ z < lam → z ∈ interior C := by
    intro z h1 h2
    have hs : Work.Drive.EpsForm.tiltedSlab a v h ∩ {z : R3 | ℓ z < lam} ⊆ C := by
      rintro t ⟨ht1, ht2⟩
      exact ⟨Work.Drive.EpsForm.tiltedSlab_subset_tiltedSlabClosed a v h ht1, ht2⟩
    have hso : IsOpen (Work.Drive.EpsForm.tiltedSlab a v h ∩ {z : R3 | ℓ z < lam}) :=
      (isOpen_lt ((hcontI.sub continuous_const).abs) continuous_const).inter hLopen
    exact interior_maximal hs hso ⟨by rw [Work.Drive.EpsForm.tiltedSlab]; exact h1, h2⟩
  -- the two closure/interior identities for the removed set inside the open box
  have hnotintC_of_cl : y ∈ closure f → y ∉ interior C := by
    intro hcl hint
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior y hint
    rw [mem_closure_iff] at hcl
    obtain ⟨z, hzball, hzf⟩ := hcl (Metric.ball y ε) Metric.isOpen_ball
      (Metric.mem_ball_self hεpos)
    rw [hf_eq] at hzf
    exact hzf.2 (interior_subset (hεsub hzball))
  have hclC_of_notint : y ∉ interior f → y ∈ closure C := by
    intro hint
    by_contra hnotcl
    rw [mem_closure_iff] at hnotcl
    push_neg at hnotcl
    obtain ⟨U, hUo, hyU, hUdisj⟩ := hnotcl
    have hsub : U ∩ Submission.PBox s c σ ⊆ f := by
      rintro z ⟨hzU, hzP⟩
      refine ⟨hzP, ?_⟩
      intro hzC
      have hmem : z ∈ U ∩ C := ⟨hzU, hzC⟩
      rw [hUdisj] at hmem
      exact hmem
    exact hint (interior_maximal hsub (hUo.inter hPopen) ⟨hyU, hy⟩)
  have hnotintf_of : |inner ℝ v y - a| ≤ h → ℓ y ≤ lam → y ∉ interior f := by
    intro h1 h2 hyint
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior y hyint
    obtain ⟨y', hy'close, hy'C⟩ := hmemC_move h1 h2 ε hεpos
    have hy'f : y' ∈ f := interior_subset (hεsub (by rwa [Metric.mem_ball]))
    rw [hf_eq] at hy'f
    exact hy'f.2 hy'C
  rw [frontier, Set.mem_sdiff]
  constructor
  · rintro ⟨hcl, hint⟩
    have h1' : |inner ℝ v y - a| ≤ h := (hclC (hclC_of_notint hint)).1
    have h2 : ℓ y ≤ lam := (hclC (hclC_of_notint hint)).2
    have h1 : inner ℝ v y ≤ a + h := by linarith [(abs_le.mp h1').2]
    have h3 : ¬(inner ℝ v y - a < h ∧ ℓ y < lam) := fun hcon =>
      hnotintC_of_cl hcl (hintC_of y (abs_lt.mpr ⟨by linarith [hcon.1], hcon.1⟩) hcon.2)
    by_cases hface : inner ℝ v y = a + h
    · exact Or.inl ⟨hface, h2⟩
    · refine Or.inr ⟨le_antisymm h2 (le_of_not_gt ?_), lt_of_le_of_ne h1 hface⟩
      intro hℓlt
      have hx : inner ℝ v y - a < h := by
        rcases lt_trichotomy (inner ℝ v y - a) h with hlt | heq | hgt
        · exact hlt
        · exact absurd (by linarith : inner ℝ v y = a + h) hface
        · linarith [(abs_le.mp h1').2]
      exact h3 ⟨hx, hℓlt⟩
  · rintro (⟨hface, hℓ⟩ | ⟨hℓ, hlt⟩)
    · have hle : |inner ℝ v y - a| ≤ h := by
        rw [hface]
        have : a + h - a = h := by ring
        rw [this, abs_of_pos hh]
      exact ⟨hclosuref_ray hface, hnotintf_of hle hℓ⟩
    · have hyC : y ∉ C := by
        intro hmemC
        have h2 := (hCmem y).mp hmemC
        rw [hℓ] at h2
        exact absurd h2.2 (lt_irrefl lam)
      have hyf : y ∈ f := by rw [hf_eq]; exact ⟨hy, hyC⟩
      have hle : |inner ℝ v y - a| ≤ h := abs_le.mpr ⟨by linarith [habove], by linarith⟩
      exact ⟨subset_closure hyf, hnotintf_of hle (le_of_eq hℓ)⟩

/-- `max (r - lam) (s - a) = 0` if and only if `s = a` and `r ≤ lam`, or `r = lam` and `s < a`:
the corner `{ℓ = lam, ⟪v,·⟫ ≤ a}` ∪ `{⟪v,·⟫ = a, ℓ ≤ lam}` is the zero set of the maximum of the
two level functions. -/
private lemma max_sub_eq_zero_iff_aux {r s lam a : ℝ} :
    max (r - lam) (s - a) = 0 ↔ (s = a ∧ r ≤ lam) ∨ (r = lam ∧ s < a) := by
  rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · rcases lt_or_eq_of_le h2 with h2' | h2'
      · right; constructor <;> linarith
      · left; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩
    · exact ⟨by linarith, by linarith, Or.inl (by linarith)⟩

/-- **The local model of the trace at a wall ∩ face junction of the tilted sweep.**

Let `z` be a point of the surface `carrier` in the *open* box, on the upper slab face
(`⟪v,z⟫ = ⟪v,c⟫ + u + h`) and at the level `lam` (`ℓ z = lam`).  Assume that the surface crosses the
level wall regularly at `z` (`hregℓ`, clause (i) of `TiltedGenericity`), that it crosses the face
plane regularly at `z` (`hregG`, the transversality of the surface with the slab faces which the
stratified genericity of the data must provide), and that the two curves are transverse to each
other at `z` (`htrans`, clause (ii) of `TiltedGenericity`).  Then the trace of the level,
`carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)`, is locally Euclidean of dimension one
at `z`.

Near `z` the trace is the *corner* made of the half of the wall curve inside the closed slab and the
half of the face curve below the level:
`{ℓ = lam, |⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h} ∪ {|⟪v,·⟫ - (⟪v,c⟫+u)| = h, ℓ ≤ lam}`, and the two half-curves
meet only at `z` because `htrans` says the two curves are transverse there.  The two arcs are glued
by `Work.EpsW.localArc_gluedPair` (which is already proved), so the work is to produce the two arcs
(a half of the level set `{sweepHeight = lam}` and a half of the level set `{⟪v, par ψ ·⟫ = a + h}`)
and to identify the trace with their union on a neighbourhood of `z`. -/
theorem WallFaceJunction_holds {ψ : Submission.Diffeo} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {lam : ℝ} {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : v ≠ 0) (hh : 0 < h) (hℓne : ℓ ≠ 0)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzb : z ∈ Submission.PBox s c σ)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z = lam)
    (hregℓ : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (hregG : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (htrans : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z → ∀ t : ℝ,
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  -- the two level functions, read in the parameter plane
  set a : ℝ := inner ℝ v c + u + h with hadef
  set F : ℝ × ℝ → ℝ := fun q => Work.Drive.EpsForm.sweepHeight ψ ℓ q - lam with hFdef
  set G : ℝ × ℝ → ℝ := fun q => Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v) q - a with hGdef
  -- a parameter point above `z`
  obtain ⟨p₀, hp₀⟩ : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = z := by
    have h1 : z ∈ Set.range (Work.Smooth.Morse.param ψ) := by
      simpa [Work.Drive.EpsSphere.torusOf] using hz
    exact h1
  have hp₀' : Work.BoxShrink.Pinch.par ψ p₀ = z := by
    rw [Work.BoxShrink.Pinch.par_def]; exact hp₀
  -- the two level functions vanish at `p₀`
  have hFp : F p₀ = 0 := by
    show Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ - lam = 0
    have h1 : Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ = lam := by
      show ℓ (Work.Smooth.Morse.param ψ p₀) = lam
      rw [hp₀]; exact hzl
    rw [h1]; ring
  have hGp : G p₀ = 0 := by
    show Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v) p₀ - a = 0
    have h1 : Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v) p₀ = a := by
      rw [Work.Drive.EpsForm.sweepHeight_innerSL]
      show inner ℝ v (Work.BoxShrink.Pinch.par ψ p₀) = a
      rw [hp₀', hadef]
      exact hzface
    rw [h1]; ring
  have hFcd : ContDiffAt ℝ 1 F p₀ := by
    rw [hFdef]
    exact (((Work.Drive.EpsForm.sweepHeight_contDiff_two ψ ℓ).contDiffAt).sub
      contDiffAt_const).of_le (by norm_num)
  have hGcd : ContDiffAt ℝ 1 G p₀ := by
    rw [hGdef]
    exact (((Work.Drive.EpsForm.sweepHeight_contDiff_two ψ ((innerSL ℝ) v)).contDiffAt).sub
      contDiffAt_const).of_le (by norm_num)
  have hdF : fderiv ℝ F p₀ ≠ 0 := by
    rw [hFdef, fderiv_sub_const]
    exact hregℓ p₀ hp₀'
  have hdG : fderiv ℝ G p₀ ≠ 0 := by
    rw [hGdef, fderiv_sub_const, Work.Drive.EpsForm.sweepHeight_innerSL]
    exact hregG p₀ hp₀'
  -- `htrans` is the independence of the two derivatives
  have hind : ∀ t : ℝ, fderiv ℝ F p₀ ≠ t • fderiv ℝ G p₀ := by
    intro t
    rw [hFdef, hGdef, fderiv_sub_const, fderiv_sub_const, Work.Drive.EpsForm.sweepHeight_innerSL]
    exact htrans p₀ hp₀' t
  -- the plane model of the corner
  obtain ⟨V, hVopen, hp₀V, hVloc⟩ :=
    Work.Smooth.OneManifold.isLocallyArc_max_of_isInvertible hFcd hGcd hFp hGp
      (ProdInvertible_holds hdG hind)
  -- a neighbourhood of `z`: inside the box and strictly above the mid-plane of the slab
  have hnhds_above : {y : R3 | inner ℝ v c + u < inner ℝ v y} ∈ nhds z := by
    have hlt : inner ℝ v c + u < inner ℝ v z := by rw [hzface]; linarith [hh]
    exact (isOpen_lt continuous_const (continuous_const.inner continuous_id)).mem_nhds hlt
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hnhds_above
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    Metric.mem_nhds_iff.mp ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hzb)
  set δgeo : ℝ := min δ₁ δ₂ with hδgeodef
  have hδgeopos : 0 < δgeo := lt_min hδ₁pos hδ₂pos
  have hnhds_ball : {q : ℝ × ℝ | Work.Smooth.Morse.param ψ q ∈ Metric.ball z δgeo} ∈ nhds p₀ := by
    have hmem : Metric.ball z δgeo ∈ nhds (Work.Smooth.Morse.param ψ p₀) := by
      rw [hp₀]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδgeopos)
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt hmem
  obtain ⟨δ₄, hδ₄pos, hδ₄sub⟩ := Metric.mem_nhds_iff.mp hnhds_ball
  obtain ⟨δ₃, hδ₃pos, hδ₃sub⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hp₀V)
  obtain ⟨ε₀, hε₀pos, hε₀inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p₀
  set δ : ℝ := min (min δ₃ δ₄) ε₀ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₃pos hδ₄pos) hε₀pos
  have hδ3 : δ ≤ δ₃ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ4 : δ ≤ δ₄ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ0 : δ ≤ ε₀ := min_le_right _ _
  set B : Set (ℝ × ℝ) := Metric.ball p₀ δ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hp₀B : p₀ ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
  have hBV : B ⊆ V := by
    intro q hq
    have hq' : q ∈ Metric.ball p₀ δ := by rwa [hBdef] at hq
    exact hδ₃sub (Metric.ball_subset_ball hδ3 hq')
  have hBinj : Set.InjOn (Work.Smooth.Morse.param ψ) B := by
    intro x hx y hy hxy
    have hx' : x ∈ Metric.ball p₀ δ := by rwa [hBdef] at hx
    have hy' : y ∈ Metric.ball p₀ δ := by rwa [hBdef] at hy
    exact hε₀inj (Metric.ball_subset_ball hδ0 hx') (Metric.ball_subset_ball hδ0 hy') hxy
  have hBP : ∀ q ∈ B, Work.Smooth.Morse.param ψ q ∈ Submission.PBox s c σ := by
    intro q hq
    have hq' : q ∈ Metric.ball p₀ δ := by rwa [hBdef] at hq
    have h5 := hδ₄sub (Metric.ball_subset_ball hδ4 hq')
    exact hδ₂sub (Metric.ball_subset_ball (min_le_right _ _) h5)
  have hBabove : ∀ q ∈ B, inner ℝ v c + u < inner ℝ v (Work.Smooth.Morse.param ψ q) := by
    intro q hq
    have hq' : q ∈ Metric.ball p₀ δ := by rwa [hBdef] at hq
    have h5 := hδ₄sub (Metric.ball_subset_ball hδ4 hq')
    exact hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) h5)
  -- the shape of `F` and `G` on the surface
  have hF_eq : ∀ q : ℝ × ℝ, F q = ℓ (Work.Smooth.Morse.param ψ q) - lam := by
    intro q; rw [hFdef]; rfl
  have hG_eq : ∀ q : ℝ × ℝ,
      G q = inner ℝ v (Work.Smooth.Morse.param ψ q) - (inner ℝ v c + u + h) := by
    intro q
    rw [hGdef, Work.Drive.EpsForm.sweepHeight_innerSL]
    rfl
  -- `ℓ` is not a multiple of `⟪v,·⟫`, so the wall really crosses the slab face
  have hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v := by
    intro t ht
    have hdiff : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀ := by
      rw [← Work.Drive.EpsForm.sweepHeight_innerSL]
      exact ((Work.Drive.EpsForm.sweepHeight_contDiff_two ψ ((innerSL ℝ) v)).differentiable
        (by norm_num)).differentiableAt
    have hfun : Work.Drive.EpsForm.sweepHeight ψ ℓ =
        fun q : ℝ × ℝ => t * (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) q := by
      funext q
      show ℓ (Work.Smooth.Morse.param ψ q) =
        t * (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) q
      rw [Work.Drive.EpsForm.sweepHeight_innerSL]
      show ℓ (Work.Smooth.Morse.param ψ q) = t * inner ℝ v (Work.BoxShrink.Pinch.par ψ q)
      rw [ht]
      simp
    have h1 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀
        = t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀ := by
      rw [hfun, Work.Drive.EpsForm.sweepHeight_innerSL, fderiv_const_mul hdiff]
    exact htrans p₀ hp₀' t h1
  -- the pointwise identification of the trace with the plane corner
  have hpoint : ∀ q ∈ B, (max (F q) (G q) = 0 ↔
      Work.Smooth.Morse.param ψ q ∈
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
    intro q hqB
    have hfr : Work.Smooth.Morse.param ψ q ∈
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
        (inner ℝ v (Work.Smooth.Morse.param ψ q) = inner ℝ v c + u + h ∧
          ℓ (Work.Smooth.Morse.param ψ q) ≤ lam) ∨
        (ℓ (Work.Smooth.Morse.param ψ q) = lam ∧
          inner ℝ v (Work.Smooth.Morse.param ψ q) < inner ℝ v c + u + h) :=
      frontier_corner_aux hv hh hanti (hBP q hqB) (hBabove q hqB)
    rw [hfr, hF_eq q, hG_eq q]
    exact max_sub_eq_zero_iff_aux
  -- the plane model
  set P : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ | max (F q) (G q) = 0} with hPdef
  have hPB : P ⊆ B := by rw [hPdef]; exact inter_subset_left
  have hlocB : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ P) := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥((V ∩ {q : ℝ × ℝ | max (F q) (G q) = 0}) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hVloc hBopen
    refine Work.Smooth.OneManifold.isLocallyArc_of_eq ?_ h1
    ext q
    constructor
    · rintro ⟨⟨hqV, hqmax⟩, hqB⟩
      exact ⟨hqB, ⟨hqB, hqmax⟩⟩
    · rintro ⟨hqB, hqB', hqmax⟩
      exact ⟨⟨hBV hqB, hqmax⟩, hqB⟩
  set Z : Set R3 := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) with hZdef
  have hZc : Z ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := fun y hy => hy.1
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ P) = Work.Smooth.Morse.param ψ '' B' ∩ Z := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, ⟨hqB', hqP⟩, rfl⟩
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      refine ⟨Work.Smooth.Morse.param_mem ψ q, ?_⟩
      exact (hpoint q (hB'sub hqB')).mp hqP.2
    · rintro ⟨⟨q, hqB', rfl⟩, hyZ⟩
      exact ⟨q, ⟨hqB', ⟨hB'sub hqB', (hpoint q (hB'sub hqB')).mpr hyZ.2⟩⟩, rfl⟩
  have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.Smooth.Morse.param ψ '' B ∩ Z) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param hZc hBopen hPB hident hBinj hlocB
  -- the trace is the trace of an open set on the surface
  have hVopenC : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Smooth.Morse.param ψ '' B) :=
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen
  obtain ⟨W, hWopen, hWeq⟩ := Work.SliceArcs.exists_isOpen_inter_carrier hVopenC
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hzmem : z ∈ Work.Smooth.Morse.param ψ '' B ∩
        (Work.Drive.EpsSphere.torusOf ψ).carrier := ⟨⟨p₀, hp₀B, hp₀⟩, hz⟩
    rw [hWeq] at hzmem
    exact hzmem.1
  · have hsub : Work.Smooth.Morse.param ψ '' B ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
      Set.image_subset_range _ _
    have hWc : W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier =
        Work.Smooth.Morse.param ψ '' B := by
      rw [← hWeq, Set.inter_eq_left.mpr hsub]
    have hset : W ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) =
        Work.Smooth.Morse.param ψ '' B ∩ Z := by
      rw [hZdef]
      ext y
      constructor
      · rintro ⟨hyW, hyC, hyfr⟩
        exact ⟨hWc ▸ ⟨hyW, hyC⟩, hyC, hyfr⟩
      · rintro ⟨hyB, hyC, hyfr⟩
        exact ⟨(hWc.symm ▸ hyB).1, hyC, hyfr⟩
    exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq hset.symm hloc

end Work.Drive.Mono
