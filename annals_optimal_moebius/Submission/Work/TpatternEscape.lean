import Submission.Work.BandFoliationInstance
import Submission.Work.LargeDisplacement
import Submission.Work.FinalAssembly
import Submission.Work.NoVerticalKernel
import Submission.Commons.Geometry.Moebius.image_segment_affine
import Submission.Commons.Geometry.Moebius.tpattern_escape_of_disjoint_chords
import Submission.Work.EndpointMonotone

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Lemma G endgame: from the T-pattern to the far boundary point

This file closes the last gap in the chain `theorem_1_1`:

    theorem_1_1 ⟸ lemmaG_inequality ⟸ (this file)

Given the T-pattern of `FoliationInterface.lemmaT_tpattern` for the explicit
spliced foliation `spliceFoliation` (Prop main0, `bandFoliation_exists`), we
produce a boundary point at perpendicular distance `> 1` from a pre-bend
chord's line, and feed it to `witness_of_boundary_point`.

The mathematical content:
* **deck rigidity** (`f_eq_imp_bandRel`): two strip points with equal images
  are `bandRel`-equivalent (orbit reduction to the fundamental domain +
  injectivity of `f` there).  This is the only place where the *embedding*
  hypothesis is used;
* **height comparison** (`chord_pt_eq_of_bandRel`): two spliced leaves whose
  centreline heights differ by `δ ∈ (0, a/2]` can only have a common point
  when they share it as a common PREIMAGE point;
* the mirror trick (`imageDir` odd, `imageMid` periodic) reduces the T-pattern
  to `δ ≤ a/2`;
* case analysis: either the two preimage chords share an endpoint (WEDGE: the
  far endpoint of one bend is at distance `ℓ > 1` from the other bend's line,
  because the two displacements differ), or they do not, in which case the
  bites' image segments are disjoint and the escape lemma
  `Commons.Geometry.Moebius.tpattern_escape_of_disjoint_chords` applies.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

variable {a : ℝ} {f : ℝ² → ℝ³}

/-- **The explicit spliced foliation** (Prop main0) as a structure value (no
`Classical.choice`, so all the properties of `spliceChord` stay available
definitionally). -/
def spliceFoliation (hf : IsMoebiusEmbedding a f) (ha : 0 < a) :
    BandFoliation a f hf where
  chord := spliceChord hf ha
  centre := fun y => spliceChord_centre hf ha y
  deck := fun y => spliceChord_deck hf ha y
  cont_left := by
    show Continuous (fun y : ℝ => ((spliceChord hf ha y).A 1 : ℝ))
    simpa [spliceA1] using continuous_spliceA1 hf ha
  cont_right := by
    show Continuous (fun y : ℝ => ((spliceChord hf ha y).B 1 : ℝ))
    simpa [spliceB1] using continuous_spliceB1 hf ha
  preBend := fun y => spliceChord_preBend hf ha y

/-- The T-pattern for the explicit spliced foliation. -/
theorem tpattern_splice {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) :
    ∃ y : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < a ∧
      (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y) ⬝ᵥ
         WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ)) = 0) ∧
      (WithLp.ofLp (BandFoliation.imageMid (spliceFoliation hf ha) y -
          BandFoliation.imageMid (spliceFoliation hf ha) (y + δ)) ⬝ᵥ
         (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y) ⨯₃
           WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ))) = 0) :=
  lemmaT_tpattern hf ha (spliceFoliation hf ha)

/-! ## 1. Deck rigidity: equal images imply `bandRel` -/

/-- Arithmetic: for `a > 0` and any `y`, some integer translate of `y` by a
multiple of `a` lies in `[0, a)`. -/
lemma exists_int_zsmul_mem_Ico {a y : ℝ} (ha : 0 < a) :
    ∃ j : ℤ, y + j • a ∈ Set.Ico (0 : ℝ) a := by
  set n : ℤ := ⌊y / a⌋ with hn
  have h1 : (n : ℝ) ≤ y / a := Int.floor_le _
  have h2 : y / a < (n : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨-n, ?_⟩
  have hmul : y + (-n) • a = a * (y / a - n) := by
    rw [zsmul_eq_mul, mul_sub, mul_div_cancel₀ _ (ne_of_gt ha)]
    push_cast
    ring
  rw [Set.mem_Ico, hmul]
  have h3 : 0 ≤ y / a - n := by linarith
  have h4 : y / a - n < 1 := by linarith [h2]
  exact ⟨mul_nonneg ha.le h3, by nlinarith [h4, ha]⟩

/-- **Orbit reduction**: every point of the unit strip is `bandRel`-equivalent
to a point of the fundamental domain `[0,1] × [0,a)`. -/
lemma exists_fundamentalDomain_bandRel {a : ℝ} (ha : 0 < a) {x : ℝ²}
    (hx : x ∈ unitStrip) :
    ∃ c : ℝ², c ∈ fundamentalDomain a ∧ bandRel a x c := by
  have hx0 : x 0 ∈ Set.Icc (0 : ℝ) 1 := hx
  obtain ⟨j, hj⟩ := exists_int_zsmul_mem_Ico (a := a) ha (y := x 1)
  rw [Set.mem_Ico] at hj
  rcases Int.even_or_odd j with hj2 | hj2
  · obtain ⟨m, hm⟩ := hj2
    refine ⟨!₂[x 0, x 1 + j • a], ?_, Or.inl ⟨m, ?_, ?_⟩⟩
    · show (!₂[x 0, x 1 + j • a] : ℝ²) 0 ∈ Set.Icc (0 : ℝ) 1 ∧
        (!₂[x 0, x 1 + j • a] : ℝ²) 1 ∈ Set.Ico (0 : ℝ) a
      exact ⟨by simpa using hx0, by simpa using hj⟩
    · simp
    · have h1 : (!₂[x 0, x 1 + j • a] : ℝ²) 1 - x 1 = j • a := by simp
      rw [h1, hm]
      rw [show (2 : ℤ) * m = m + m by ring]
  · obtain ⟨m, hm⟩ := hj2
    refine ⟨!₂[1 - x 0, x 1 + j • a], ?_, Or.inr ⟨m, ?_, ?_⟩⟩
    · show (!₂[1 - x 0, x 1 + j • a] : ℝ²) 0 ∈ Set.Icc (0 : ℝ) 1 ∧
        (!₂[1 - x 0, x 1 + j • a] : ℝ²) 1 ∈ Set.Ico (0 : ℝ) a
      constructor
      · have h' : (!₂[1 - x 0, x 1 + j • a] : ℝ²) 0 = 1 - x 0 := by simp
        rw [h']
        rw [Set.mem_Icc] at hx0 ⊢
        constructor <;> linarith [hx0.1, hx0.2]
      · simpa using hj
    · have h' : (!₂[1 - x 0, x 1 + j • a] : ℝ²) 0 = 1 - x 0 := by simp
      rw [h']
      ring
    · have h1 : (!₂[1 - x 0, x 1 + j • a] : ℝ²) 1 - x 1 = j • a := by simp
      rw [h1, hm]

/-- **Deck rigidity**: two points of the unit strip with the same image under
`f` are related by the deck relation `bandRel a`. -/
theorem f_eq_imp_bandRel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {v w : ℝ²} (hv : v ∈ unitStrip) (hw : w ∈ unitStrip) (h : f v = f w) :
    bandRel a v w := by
  obtain ⟨c, hcFD, hvc⟩ := exists_fundamentalDomain_bandRel ha hv
  obtain ⟨d, hdFD, hwd⟩ := exists_fundamentalDomain_bandRel ha hw
  have hfc : f c = f v := (f_eq_of_bandRel hf hv hvc).symm
  have hfd : f d = f w := (f_eq_of_bandRel hf hw hwd).symm
  have hcd : c = d := hf.embedding hcFD hdFD (by rw [hfc, h, ← hfd])
  refine bandQuot_eq_iff.mp ?_
  rw [bandQuot_eq_iff.mpr hvc, bandQuot_eq_iff.mpr hwd, hcd]

/-! ## 2. Chord parametrization, the displacement bound, and the height comparison -/

section Height

open BandFoliation

variable {hf : IsMoebiusEmbedding a f}

/-- The point of the chord at centreline height `y` with parameter `s`. -/
def chordPt (F : BandFoliation a f hf) (y s : ℝ) : ℝ² := (1 - s) • A F y + s • B F y

/-- The `x₀`-coordinate of a chord point is its parameter. -/
lemma chordPt_coord0 (F : BandFoliation a f hf) (y s : ℝ) : (chordPt F y s) 0 = s := by
  have hA := A_left_coord F y
  have hB := B_right_coord F y
  simp [chordPt, hA, hB]

/-- The `x₁`-coordinate of a chord point: `y + (s − 1/2)·Δ`. -/
lemma chordPt_coord1 (F : BandFoliation a f hf) (y s : ℝ) :
    (chordPt F y s) 1 = y + (s - 1 / 2) * Δ F y := by
  have hsum : (A F y) 1 + (B F y) 1 = 2 * y := by
    have h := congrArg (fun z : ℝ² => z 1) (A_add_B_eq_centre F y)
    simpa using h
  have hcoord : (chordPt F y s) 1 = (1 - s) * (A F y) 1 + s * (B F y) 1 := by
    simp [chordPt]
  rw [hcoord]
  have hΔ : Δ F y = (B F y) 1 - (A F y) 1 := rfl
  rw [hΔ]
  linarith

/-- The `x₁`-coordinate of a chord point in terms of the endpoints. -/
lemma chordPt_coord1_mid (F : BandFoliation a f hf) (y s : ℝ) :
    (chordPt F y s) 1 = (1 - s) * (A F y) 1 + s * (B F y) 1 := by
  simp [chordPt]

/-- A chord point with parameter in `[0,1]` lies in the unit strip. -/
lemma chordPt_mem_unitStrip (F : BandFoliation a f hf) (y : ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : chordPt F y s ∈ unitStrip := by
  show (chordPt F y s) 0 ∈ Set.Icc (0 : ℝ) 1
  rw [chordPt_coord0]
  exact hs

/-- The displacement of a leaf is bounded by `(a²−1)/(2a) < a/2`. -/
lemma abs_delta_le (F : BandFoliation a f hf) (ha : 0 < a) (y : ℝ) :
    |Δ F y| ≤ (a ^ 2 - 1) / (2 * a) := by
  have h := abs_delta_le_div_of_chord hf ha ((F.chord y).A 1) ((F.chord y).B 1)
    (preBend_vec F y)
  simpa [BandFoliation.Δ, BendData.slope] using h

/-- The fraction `(a²−1)/(2a)` is below `a/2`. -/
lemma div_lt_half (ha : 0 < a) : (a ^ 2 - 1) / (2 * a) < a / 2 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_pos_of_ne_zero (ne_of_gt ha)]

/-- `|2m·a| < a` forces `m = 0`. -/
lemma int_eq_zero_of_abs_two_mul_zsmul_lt {a : ℝ} (ha : 0 < a) {m : ℤ}
    (h : |(2 * m) • a| < a) : m = 0 := by
  by_contra hm
  have h1 : (1 : ℝ) ≤ |((m : ℤ) : ℝ)| := by
    have h := Int.one_le_abs hm
    exact_mod_cast h
  have h2 : |(2 * m) • a| = 2 * |((m : ℤ) : ℝ)| * a := by
    rw [zsmul_eq_mul]
    have hcast : (((2 * m : ℤ)) : ℝ) = 2 * ((m : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2] at h
  nlinarith

/-- `a ≤ |(2m+1)·a|` for every integer `m`. -/
lemma le_abs_odd_zsmul {a : ℝ} (ha : 0 < a) (m : ℤ) : a ≤ |(2 * m + 1) • a| := by
  have h1 : |(2 * m + 1) • a| = |(((2 * m + 1 : ℤ)) : ℝ)| * a := by
    rw [zsmul_eq_mul, abs_mul, abs_of_pos ha]
  rw [h1]
  have h2 : (1 : ℝ) ≤ |(((2 * m + 1 : ℤ)) : ℝ)| := by
    have hne : (2 * m + 1 : ℤ) ≠ 0 := by omega
    have h := Int.one_le_abs hne
    exact_mod_cast h
  nlinarith

/-- **Height comparison**: for `0 < δ ≤ a/2`, a point of the leaf at centreline
height `y` and a point of the leaf at centreline height `y+δ` whose images
coincide are EQUAL as preimage points. -/
theorem chordPt_eq_of_bandRel (F : BandFoliation a f hf) (ha : 0 < a) {y δ s t : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ a / 2)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hrel : bandRel a (chordPt F y s) (chordPt F (y + δ) t)) :
    chordPt F y s = chordPt F (y + δ) t := by
  have hC : (a ^ 2 - 1) / (2 * a) < a / 2 := div_lt_half ha
  have hΔ1 : |Δ F y| ≤ (a ^ 2 - 1) / (2 * a) := abs_delta_le F ha y
  have hΔ2 : |Δ F (y + δ)| ≤ (a ^ 2 - 1) / (2 * a) := abs_delta_le F ha (y + δ)
  have ht' : |t - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hs' : |s - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hb2 : |(t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y|
      ≤ (a ^ 2 - 1) / (2 * a) := by
    have h3 : |(t - 1 / 2) * Δ F (y + δ)| ≤ (1 / 2) * ((a ^ 2 - 1) / (2 * a)) := by
      rw [abs_mul]
      exact mul_le_mul ht' hΔ2 (abs_nonneg _) (by norm_num)
    have h4 : |(s - 1 / 2) * Δ F y| ≤ (1 / 2) * ((a ^ 2 - 1) / (2 * a)) := by
      rw [abs_mul]
      exact mul_le_mul hs' hΔ1 (abs_nonneg _) (by norm_num)
    calc |(t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y|
        ≤ |(t - 1 / 2) * Δ F (y + δ)| + |(s - 1 / 2) * Δ F y| := abs_sub _ _
      _ ≤ (1 / 2) * ((a ^ 2 - 1) / (2 * a)) + (1 / 2) * ((a ^ 2 - 1) / (2 * a)) :=
          add_le_add h3 h4
      _ = (a ^ 2 - 1) / (2 * a) := by ring
  have hcoord : (chordPt F (y + δ) t) 1 - (chordPt F y s) 1
      = δ + ((t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y) := by
    rw [chordPt_coord1, chordPt_coord1]
    ring
  have hb : |(chordPt F (y + δ) t) 1 - (chordPt F y s) 1| < a := by
    rw [hcoord]
    have h5 : |δ + ((t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y)| ≤
        δ + |(t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y| := by
      have := abs_add_le δ ((t - 1 / 2) * Δ F (y + δ) - (s - 1 / 2) * Δ F y)
      rwa [abs_of_pos hδ0] at this
    linarith [hb2, hδ, hC]
  rcases hrel with ⟨m, hx0, hd⟩ | ⟨m, hsum, hd⟩
  · -- even clause: the parameters agree and the height shift is a multiple of `2a`
    have hs0 : (chordPt F y s) 0 = s := chordPt_coord0 F y s
    have ht0 : (chordPt F (y + δ) t) 0 = t := chordPt_coord0 F (y + δ) t
    have hst : s = t := by rw [hs0, ht0] at hx0; exact hx0
    have hm0 : m = 0 := int_eq_zero_of_abs_two_mul_zsmul_lt ha (by rw [← hd]; exact hb)
    have h1eq : (chordPt F y s) 1 = (chordPt F (y + δ) t) 1 := by
      have hz : (chordPt F (y + δ) t) 1 - (chordPt F y s) 1 = 0 := by
        rw [hd, hm0]
        simp
      linarith
    have h0eq : (chordPt F y s) 0 = (chordPt F (y + δ) t) 0 := hx0
    ext i <;> fin_cases i
    · simpa using h0eq
    · simpa using h1eq
  · -- odd clause: the height shift is an odd multiple of `a`, impossible
    have hs0 : (chordPt F y s) 0 = s := chordPt_coord0 F y s
    have ht0 : (chordPt F (y + δ) t) 0 = t := chordPt_coord0 F (y + δ) t
    have hge : a ≤ |(2 * m + 1) • a| := le_abs_odd_zsmul ha m
    rw [← hd] at hge
    linarith [hb]

end Height

/-! ## 3. The normalized T-pattern (`δ ≤ a/2`) -/

/-- The T-pattern can be normalized so that the two centreline heights differ by
at most `a/2` (using the deck symmetry of the leaf family: the image direction
is odd and the image midpoint is periodic). -/
theorem tpattern_small {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a) :
    ∃ y δ, 0 < δ ∧ δ ≤ a / 2 ∧
      (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y) ⬝ᵥ
         WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ)) = 0) ∧
      (WithLp.ofLp (BandFoliation.imageMid (spliceFoliation hf ha) y -
          BandFoliation.imageMid (spliceFoliation hf ha) (y + δ)) ⬝ᵥ
         (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y) ⨯₃
           WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ))) = 0) := by
  obtain ⟨y, δ, hδ0, hδa, hperp, hcop⟩ := tpattern_splice hf ha
  by_cases h : δ ≤ a / 2
  · exact ⟨y, δ, hδ0, h, hperp, hcop⟩
  · push_neg at h
    have hdir : BandFoliation.imageDir (spliceFoliation hf ha) ((y + δ) + (a - δ))
        = - BandFoliation.imageDir (spliceFoliation hf ha) y := by
      have harg : (y + δ) + (a - δ) = y + a := by ring
      rw [harg]
      exact BandFoliation.imageDir_odd (spliceFoliation hf ha) y
    have hmid : BandFoliation.imageMid (spliceFoliation hf ha) ((y + δ) + (a - δ))
        = BandFoliation.imageMid (spliceFoliation hf ha) y := by
      have harg : (y + δ) + (a - δ) = y + a := by ring
      rw [harg]
      exact BandFoliation.imageMid_period (spliceFoliation hf ha) y
    refine ⟨y + δ, a - δ, by linarith, by linarith, ?_, ?_⟩
    · rw [hdir, WithLp.ofLp_neg, dotProduct_neg, dotProduct_comm, hperp, neg_zero]
    · rw [hdir, hmid]
      have hD : BandFoliation.imageMid (spliceFoliation hf ha) (y + δ) -
            BandFoliation.imageMid (spliceFoliation hf ha) y
          = -(BandFoliation.imageMid (spliceFoliation hf ha) y -
              BandFoliation.imageMid (spliceFoliation hf ha) (y + δ)) := by abel
      rw [hD, WithLp.ofLp_neg, neg_dotProduct]
      have hcross : (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ)) ⨯₃
            WithLp.ofLp (-(BandFoliation.imageDir (spliceFoliation hf ha) y)))
          = WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y) ⨯₃
              WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ)) := by
        rw [WithLp.ofLp_neg,
          map_neg (crossProduct (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ))))
            (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y))]
        exact neg_cross (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) (y + δ)))
          (WithLp.ofLp (BandFoliation.imageDir (spliceFoliation hf ha) y))
      rw [hcross, hcop, neg_zero]

/-! ## 4. Wedge and disjointness lemmas -/

section Assembly

open BandFoliation

variable {hf : IsMoebiusEmbedding a f}

/-- **Wedge escape**: two image segments with perpendicular directions sharing
their first endpoint `X = P = P'`; then the perpendicular decomposition of the
other endpoint `Q'` of the second segment about the first segment's midpoint. -/
lemma wedge_escape {P Q P' Q' : ℝ³} {ℓ ℓ' : ℝ} {u u' : ℝ³}
    (hP : Q - P = ℓ • u) (hQ : Q' - P' = ℓ' • u')
    (hperp : inner ℝ u u' = 0) (hX : P = P') :
    Q' - (1 / 2 : ℝ) • (P + Q) = (-1 / 2 : ℝ) • (Q - P) + (Q' - P') ∧
      inner ℝ (Q' - P') (Q - P) = 0 := by
  have hperp' : inner ℝ (Q' - P') (Q - P) = 0 := by
    rw [hQ, hP, real_inner_smul_left, real_inner_smul_right, real_inner_comm, hperp]
    ring
  refine ⟨?_, hperp'⟩
  rw [← hX]
  module

/-- **Wedge escape, shared right endpoint** `X = Q = Q'`: the perpendicular
decomposition of the other endpoint `P'` of the second segment about the first
segment's midpoint. -/
lemma wedge_escape_right {P Q P' Q' : ℝ³} {ℓ ℓ' : ℝ} {u u' : ℝ³}
    (hP : Q - P = ℓ • u) (hQ : Q' - P' = ℓ' • u')
    (hperp : inner ℝ u u' = 0) (hX : Q = Q') :
    P' - (1 / 2 : ℝ) • (P + Q) = (1 / 2 : ℝ) • (Q - P) + (P' - Q') ∧
      inner ℝ (P' - Q') (Q - P) = 0 := by
  have hperp' : inner ℝ (P' - Q') (Q - P) = 0 := by
    have hneg : P' - Q' = -(Q' - P') := by abel
    rw [hneg, inner_neg_left, hQ, hP, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm, hperp]
    ring
  refine ⟨?_, hperp'⟩
  rw [← hX]
  module

end Assembly

/-! ## 5. Leaf lengths and the chord-meeting classification -/

section Leaf

open BandFoliation

variable {hf : IsMoebiusEmbedding a f}

/-- The image leaf vector in explicit `!₂` coordinates. -/
lemma leafVec_explicit (F : BandFoliation a f hf) (y : ℝ) :
    leafVec F y = f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1] := by
  have hB : f ((F.chord y).B) = f !₂[1, ((F.chord y).B) 1] :=
    congrArg f (rightEdge_eq_vec (F.chord y).right_coord)
  have hA : f ((F.chord y).A) = f !₂[0, ((F.chord y).A) 1] :=
    congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
  show f ((F.chord y).B) - f ((F.chord y).A) = _
  rw [hB, hA]

/-- The length of a leaf's image is `√(1 + Δ²)`. -/
lemma leafVec_norm (F : BandFoliation a f hf) (y : ℝ) :
    ‖leafVec F y‖ = Real.sqrt (1 + (Δ F y) ^ 2) := by
  have h1 : leafVec F y = f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1] :=
    leafVec_explicit F y
  have h2 : ‖f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1]‖ = ‖leafVec F y‖ := by
    rw [h1]
  have h3 : ‖f !₂[1, ((F.chord y).B) 1] - f !₂[0, ((F.chord y).A) 1]‖
      = ‖(!₂[1, ((F.chord y).B) 1] : ℝ²) - !₂[0, ((F.chord y).A) 1]‖ := preBend_vec F y
  rw [← h2, h3, preimage_chord_length, BandFoliation.Δ, BendData.slope]

/-- A leaf whose displacement `Δ` is nonzero has image length `> 1`. -/
lemma one_lt_leafVec_norm {F : BandFoliation a f hf} {y : ℝ} (h : Δ F y ≠ 0) :
    1 < ‖leafVec F y‖ := by
  rw [leafVec_norm F y]
  have h1 : (1 : ℝ) < 1 + (Δ F y) ^ 2 := by
    have := sq_pos_of_ne_zero h
    linarith
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (1 + (Δ F y) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1

/-- The perpendicularity of the T-pattern in `inner` form. -/
lemma inner_imageDir_zero {F : BandFoliation a f hf} {y δ : ℝ}
    (hperp : WithLp.ofLp (imageDir F y) ⬝ᵥ WithLp.ofLp (imageDir F (y + δ)) = 0) :
    inner ℝ (imageDir F y) (imageDir F (y + δ)) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa using hperp

/-- **Chord meeting classification**: if a point of the leaf at centreline height
`y` and a point of the leaf at centreline height `y + δ` coincide as preimage
points, then the two chords share an endpoint (monotone endpoint heights). -/
lemma chordPt_eq_imp_endpoint_eq (F : BandFoliation a f hf)
    (hmonoA : Monotone (fun y : ℝ => ((F.chord y).A) 1))
    (hmonoB : Monotone (fun y : ℝ => ((F.chord y).B) 1))
    {y δ s t : ℝ} (hδ0 : 0 < δ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : chordPt F y s = chordPt F (y + δ) t) :
    (F.chord y).A 1 = (F.chord (y + δ)).A 1 ∨
      (F.chord y).B 1 = (F.chord (y + δ)).B 1 := by
  have h0 : s = t := by
    have hc := congrArg (fun z : ℝ² => z 0) h
    rw [chordPt_coord0, chordPt_coord0] at hc
    exact hc
  have h1 : (1 - s) * (A F y) 1 + s * (B F y) 1
      = (1 - t) * (A F (y + δ)) 1 + t * (B F (y + δ)) 1 := by
    have hc := congrArg (fun z : ℝ² => z 1) h
    simpa only [chordPt_coord1_mid] using hc
  rw [h0] at h1
  set d : ℝ := (A F (y + δ)) 1 - (A F y) 1 with hd
  set e : ℝ := (B F (y + δ)) 1 - (B F y) 1 with he
  have hd0 : 0 ≤ d := by
    rw [hd]; exact sub_nonneg.mpr (hmonoA (by linarith))
  have he0 : 0 ≤ e := by
    rw [he]; exact sub_nonneg.mpr (hmonoB (by linarith))
  have hkey : (1 - s) * d + s * e = 0 := by
    rw [hd, he]
    nlinarith [h1]
  have h₁ : (1 - s) * d = 0 := by
    nlinarith [mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hd0, mul_nonneg hs.1 he0]
  have h₂ : s * e = 0 := by
    nlinarith [mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hd0, mul_nonneg hs.1 he0]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with hh | hh
  · left
    have hz : d = 0 := by nlinarith [h₁]
    rw [hd] at hz
    show (A F y) 1 = (A F (y + δ)) 1
    linarith
  · right
    rw [he] at hh
    show (B F y) 1 = (B F (y + δ)) 1
    linarith

/-- If `d = 0` then the two leaves share their left endpoint (the same STRIP
point). -/
lemma A_eq_of_left_eq (F : BandFoliation a f hf) (y δ : ℝ)
    (h : (F.chord y).A 1 = (F.chord (y + δ)).A 1) : A F y = A F (y + δ) := by
  have h0 : (A F y) 0 = (A F (y + δ)) 0 := by rw [A_left_coord, A_left_coord]
  have h1 : (A F y) 1 = (A F (y + δ)) 1 := h
  ext i <;> fin_cases i <;> simp_all

/-- If `e = 0` then the two leaves share their right endpoint. -/
lemma B_eq_of_right_eq (F : BandFoliation a f hf) (y δ : ℝ)
    (h : (F.chord y).B 1 = (F.chord (y + δ)).B 1) : B F y = B F (y + δ) := by
  have h0 : (B F y) 0 = (B F (y + δ)) 0 := by rw [B_right_coord, B_right_coord]
  have h1 : (B F y) 1 = (B F (y + δ)) 1 := h
  ext i <;> fin_cases i <;> simp_all

end Leaf

/-! ## 6. The escape from a T-pattern with disjoint bends -/

section Escape

open BandFoliation

variable {hf : IsMoebiusEmbedding a f}

/-- **The Lemma-G witness from a T-pattern whose bends are disjoint** (chords
version of the escape). -/
theorem witness_of_tpattern_disjoint {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (F : BandFoliation a f hf) {y δ : ℝ}
    (hdisj : ∀ v w : ℝ²,
      (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        v = (1 - s) • (F.chord y).A + s • (F.chord y).B) →
      (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        w = (1 - s) • (F.chord (y + δ)).A + s • (F.chord (y + δ)).B) →
      f v ≠ f w)
    (hδ0 : 0 < δ) (hδa : δ < a)
    (hperp : WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
        WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0)
    (hcop : WithLp.ofLp (BandFoliation.imageMid F y - BandFoliation.imageMid F (y + δ)) ⬝ᵥ
        (WithLp.ofLp (BandFoliation.imageDir F y) ⨯₃
          WithLp.ofLp (BandFoliation.imageDir F (y + δ))) = 0) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have hesc := Commons.Geometry.Moebius.tpattern_escape_of_disjoint_chords
    (toCommonsEmbedding hf) ha (toCommons hf F) hdisj hδ0 hδa hperp hcop
  rcases hesc with ⟨c, n, hdec, hp, hn⟩ | ⟨c, n, hdec, hp, hn⟩
    | ⟨c, n, hdec, hp, hn⟩ | ⟨c, n, hdec, hp, hn⟩
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
      (s := ((F.chord (y + δ)).A) 1 - a) (W := f ((F.chord (y + δ)).A))
      (c := c) (n := n) ?_ (decomp_vec F y hdec) (perp_vec F y hp) hn (preBend_vec F y)
    have hA2 : f ((F.chord (y + δ)).A) = f !₂[0, ((F.chord (y + δ)).A) 1] :=
      congrArg f (leftEdge_eq_vec (F.chord (y + δ)).left_coord)
    rw [hA2]
    exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord (y + δ)).A) 1)).symm
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
      (s := ((F.chord (y + δ)).B) 1) (W := f ((F.chord (y + δ)).B))
      (c := c) (n := n) ?_ (decomp_vec F y hdec) (perp_vec F y hp) hn (preBend_vec F y)
    exact congrArg f (rightEdge_eq_vec (F.chord (y + δ)).right_coord)
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
      (s := ((F.chord y).A) 1 - a) (W := f ((F.chord y).A))
      (c := c) (n := n) ?_ (decomp_vec F (y + δ) hdec) (perp_vec F (y + δ) hp) hn
      (preBend_vec F (y + δ))
    have hA1 : f ((F.chord y).A) = f !₂[0, ((F.chord y).A) 1] :=
      congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
    rw [hA1]
    exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord y).A) 1)).symm
  · refine witness_of_boundary_point hf ha
      (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
      (s := ((F.chord y).B) 1) (W := f ((F.chord y).B))
      (c := c) (n := n) ?_ (decomp_vec F (y + δ) hdec) (perp_vec F (y + δ) hp) hn
      (preBend_vec F (y + δ))
    exact congrArg f (rightEdge_eq_vec (F.chord y).right_coord)

end Escape

/-! ## 7. The main case analysis: wedge cases and the disjoint case -/

section Main

open BandFoliation

variable {hf : IsMoebiusEmbedding a f}

/-- **The Lemma-G witness from the normalized T-pattern**: wedge cases (the two
bends share an endpoint) and the disjoint case. -/
theorem witness_of_tpattern_small {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (F : BandFoliation a f hf)
    (hmonoA : Monotone (fun y : ℝ => ((F.chord y).A) 1))
    (hmonoB : Monotone (fun y : ℝ => ((F.chord y).B) 1))
    {y δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ a / 2) (hδa : δ < a)
    (hperp : WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
        WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0)
    (hcop : WithLp.ofLp (BandFoliation.imageMid F y - BandFoliation.imageMid F (y + δ)) ⬝ᵥ
        (WithLp.ofLp (BandFoliation.imageDir F y) ⨯₃
          WithLp.ofLp (BandFoliation.imageDir F (y + δ))) = 0) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  have hc1 : (F.chord y).A 1 + (F.chord y).B 1 = 2 * y := by
    have h := F.centre y
    simp only [BendData.centreHeight] at h
    linarith
  have hc2 : (F.chord (y + δ)).A 1 + (F.chord (y + δ)).B 1 = 2 * (y + δ) := by
    have h := F.centre (y + δ)
    simp only [BendData.centreHeight] at h
    linarith
  set d : ℝ := (F.chord (y + δ)).A 1 - (F.chord y).A 1 with hd
  set e : ℝ := (F.chord (y + δ)).B 1 - (F.chord y).B 1 with he
  have hsum : d + e = 2 * δ := by rw [hd, he]; linarith
  have hd0 : 0 ≤ d := by
    rw [hd]; exact sub_nonneg.mpr (hmonoA (by linarith))
  have he0 : 0 ≤ e := by
    rw [he]; exact sub_nonneg.mpr (hmonoB (by linarith))
  have hΔdiff : Δ F (y + δ) - Δ F y = e - d := by
    rw [BandFoliation.Δ, BandFoliation.Δ, BendData.slope, BendData.slope, he, hd]
    ring
  by_cases hdzero : d = 0
  · -- the two leaves share their LEFT endpoint
    have hAeq : A F y = A F (y + δ) := by
      refine A_eq_of_left_eq F y δ ?_
      rw [hd] at hdzero
      linarith
    have hΔne : Δ F (y + δ) ≠ Δ F y := by
      intro hcon
      have : e - d = 0 := by linarith [hΔdiff.symm.trans (by rw [hcon])]
      rw [hdzero] at this
      linarith [hsum, hδ0]
    have hfA : f (A F y) = f (A F (y + δ)) := congrArg f hAeq
    by_cases h₂ : Δ F (y + δ) = 0
    · -- far point: the right endpoint of the FIRST leaf (reference: the second)
      have hΔ1 : Δ F y ≠ 0 := by
        intro h1
        exact hΔne (by rw [h₂, h1])
      obtain ⟨hdec, hperp'⟩ := wedge_escape
        (P := f (A F (y + δ))) (Q := f (B F (y + δ)))
        (P' := f (A F y)) (Q' := f (B F y))
        (hP := leafVec_eq_norm_smul' F (y + δ)) (hQ := leafVec_eq_norm_smul' F y)
        (hperp := by rw [real_inner_comm]; exact inner_imageDir_zero hperp)
        (hX := hfA.symm)
      have hn : (1 : ℝ) < ‖f (B F y) - f (A F y)‖ := one_lt_leafVec_norm (F := F) hΔ1
      have hdec' : f (B F y) - (1 / 2 : ℝ) • (f (B F (y + δ)) + f (A F (y + δ)))
          = (-1 / 2 : ℝ) • (f (B F (y + δ)) - f (A F (y + δ)))
            + (f (B F y) - f (A F y)) := by
        rw [show f (B F (y + δ)) + f (A F (y + δ))
              = f (A F (y + δ)) + f (B F (y + δ)) from by rw [add_comm]]
        exact hdec
      refine witness_of_boundary_point hf ha
        (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
        (s := ((F.chord y).B) 1) (W := f (B F y))
        (c := (-1 / 2 : ℝ)) (n := f (B F y) - f (A F y)) ?_
        (decomp_vec F (y + δ) hdec') (perp_vec F (y + δ) hperp') hn (preBend_vec F (y + δ))
      exact congrArg f (rightEdge_eq_vec (F.chord y).right_coord)
    · -- far point: the right endpoint of the SECOND leaf (reference: the first)
      have hn : (1 : ℝ) < ‖f (B F (y + δ)) - f (A F (y + δ))‖ :=
        one_lt_leafVec_norm (F := F) h₂
      obtain ⟨hdec, hperp'⟩ := wedge_escape
        (P := f (A F y)) (Q := f (B F y))
        (P' := f (A F (y + δ))) (Q' := f (B F (y + δ)))
        (hP := leafVec_eq_norm_smul' F y) (hQ := leafVec_eq_norm_smul' F (y + δ))
        (hperp := inner_imageDir_zero hperp) (hX := hfA)
      have hdec' : f (B F (y + δ)) - (1 / 2 : ℝ) • (f (B F y) + f (A F y))
          = (-1 / 2 : ℝ) • (f (B F y) - f (A F y))
            + (f (B F (y + δ)) - f (A F (y + δ))) := by
        rw [show f (B F y) + f (A F y) = f (A F y) + f (B F y) from by rw [add_comm]]
        exact hdec
      refine witness_of_boundary_point hf ha
        (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
        (s := ((F.chord (y + δ)).B) 1) (W := f (B F (y + δ)))
        (c := (-1 / 2 : ℝ)) (n := f (B F (y + δ)) - f (A F (y + δ))) ?_
        (decomp_vec F y hdec') (perp_vec F y hperp') hn (preBend_vec F y)
      exact congrArg f (rightEdge_eq_vec (F.chord (y + δ)).right_coord)
  · by_cases hezero : e = 0
    · -- the two leaves share their RIGHT endpoint
      have hBeq : B F y = B F (y + δ) := by
        refine B_eq_of_right_eq F y δ ?_
        rw [he] at hezero
        linarith
      have hfB : f (B F y) = f (B F (y + δ)) := congrArg f hBeq
      have hΔne : Δ F (y + δ) ≠ Δ F y := by
        intro hcon
        have : e - d = 0 := by linarith [hΔdiff.symm.trans (by rw [hcon])]
        rw [hezero] at this
        linarith [hsum, hδ0]
      by_cases h₂ : Δ F (y + δ) = 0
      · -- far point: the left endpoint of the FIRST leaf (reference: the second)
        have hΔ1 : Δ F y ≠ 0 := by
          intro h1
          exact hΔne (by rw [h₂, h1])
        obtain ⟨hdec, hperp'⟩ := wedge_escape_right
          (P := f (A F (y + δ))) (Q := f (B F (y + δ)))
          (P' := f (A F y)) (Q' := f (B F y))
          (hP := leafVec_eq_norm_smul' F (y + δ)) (hQ := leafVec_eq_norm_smul' F y)
          (hperp := by rw [real_inner_comm]; exact inner_imageDir_zero hperp)
          (hX := hfB.symm)
        have hn : (1 : ℝ) < ‖f (A F y) - f (B F y)‖ := by
          have h : (1 : ℝ) < ‖f (B F y) - f (A F y)‖ := one_lt_leafVec_norm (F := F) hΔ1
          rwa [norm_sub_rev] at h
        have hdec' : f (A F y) - (1 / 2 : ℝ) • (f (B F (y + δ)) + f (A F (y + δ)))
            = (1 / 2 : ℝ) • (f (B F (y + δ)) - f (A F (y + δ)))
              + (f (A F y) - f (B F y)) := by
          rw [show f (B F (y + δ)) + f (A F (y + δ))
                = f (A F (y + δ)) + f (B F (y + δ)) from by rw [add_comm]]
          exact hdec
        refine witness_of_boundary_point hf ha
          (α := ((F.chord (y + δ)).A) 1) (β := ((F.chord (y + δ)).B) 1)
          (s := ((F.chord y).A) 1 - a) (W := f (A F y))
          (c := (1 / 2 : ℝ)) (n := f (A F y) - f (B F y)) ?_
          (decomp_vec F (y + δ) hdec') (perp_vec F (y + δ) hperp') hn (preBend_vec F (y + δ))
        have hA1 : f (A F y) = f !₂[0, ((F.chord y).A) 1] :=
          congrArg f (leftEdge_eq_vec (F.chord y).left_coord)
        rw [hA1]
        exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord y).A) 1)).symm
      · -- far point: the left endpoint of the SECOND leaf (reference: the first)
        have hn : (1 : ℝ) < ‖f (A F (y + δ)) - f (B F (y + δ))‖ := by
          have h : (1 : ℝ) < ‖f (B F (y + δ)) - f (A F (y + δ))‖ :=
            one_lt_leafVec_norm (F := F) h₂
          rwa [norm_sub_rev] at h
        obtain ⟨hdec, hperp'⟩ := wedge_escape_right
          (P := f (A F y)) (Q := f (B F y))
          (P' := f (A F (y + δ))) (Q' := f (B F (y + δ)))
          (hP := leafVec_eq_norm_smul' F y) (hQ := leafVec_eq_norm_smul' F (y + δ))
          (hperp := inner_imageDir_zero hperp) (hX := hfB)
        have hdec' : f (A F (y + δ)) - (1 / 2 : ℝ) • (f (B F y) + f (A F y))
            = (1 / 2 : ℝ) • (f (B F y) - f (A F y))
              + (f (A F (y + δ)) - f (B F (y + δ))) := by
          rw [show f (B F y) + f (A F y) = f (A F y) + f (B F y) from by rw [add_comm]]
          exact hdec
        refine witness_of_boundary_point hf ha
          (α := ((F.chord y).A) 1) (β := ((F.chord y).B) 1)
          (s := ((F.chord (y + δ)).A) 1 - a) (W := f (A F (y + δ)))
          (c := (1 / 2 : ℝ)) (n := f (A F (y + δ)) - f (B F (y + δ))) ?_
          (decomp_vec F y hdec') (perp_vec F y hperp') hn (preBend_vec F y)
        have hA2 : f (A F (y + δ)) = f !₂[0, ((F.chord (y + δ)).A) 1] :=
          congrArg f (leftEdge_eq_vec (F.chord (y + δ)).left_coord)
        rw [hA2]
        exact (f_leftEdge_eq_rightEdge_minus hf (((F.chord (y + δ)).A) 1)).symm
    · -- the two leaves do not meet: their image segments are disjoint
      have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdzero)
      have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm hezero)
      refine witness_of_tpattern_disjoint hf ha F ?_ hδ0 hδa hperp hcop
      intro v w hv hw heq
      obtain ⟨s, hs, rfl⟩ := hv
      obtain ⟨t, ht, rfl⟩ := hw
      have hvs : ((1 - s) • A F y + s • B F y) ∈ unitStrip :=
        chordPt_mem_unitStrip F y hs
      have hws : ((1 - t) • A F (y + δ) + t • B F (y + δ)) ∈ unitStrip :=
        chordPt_mem_unitStrip F (y + δ) ht
      have hrel : bandRel a ((1 - s) • A F y + s • B F y)
          ((1 - t) • A F (y + δ) + t • B F (y + δ)) :=
        f_eq_imp_bandRel hf ha hvs hws heq
      have heq' : chordPt F y s = chordPt F (y + δ) t :=
        chordPt_eq_of_bandRel F ha hδ0 hδ hs ht hrel
      rcases chordPt_eq_imp_endpoint_eq F hmonoA hmonoB hδ0 hs ht heq' with h | h
      · exfalso
        apply hdzero
        rw [hd]
        linarith
      · exfalso
        apply hezero
        rw [he]
        linarith

end Main

/-! ## 8. Lemma G -/

/-- **Lemma G (Schwartz, "The optimal paper Moebius band", §2.3).**  For an
embedded paper Moebius band of aspect ratio `a` there is a real `t` with
`2a > max(δ(t), ν(t))` — the length inequality obtained from the T-pattern and
the cut-open trapezoid.

The proof assembles: the explicit spliced bend foliation (Prop main0), the
T-pattern (`lemmaT_tpattern`), the normalization `δ ≤ a/2` (deck symmetry), the
deck rigidity of `f` (embedding + orbit reduction) and the height comparison of
the leaves (`δ ≤ a/2`), followed by the wedge/disjointness case analysis. -/
theorem lemmaG_inequality {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) :
    ∃ t : ℝ, 2 * a > max (aspectDelta t) (aspectNu t) := by
  obtain ⟨y, δ, hδ0, hδ, hperp, hcop⟩ := tpattern_small hf ha
  have hmono : Monotone (fun y : ℝ => (((spliceFoliation hf ha).chord y).A) 1) ∧
      Monotone (fun y : ℝ => (((spliceFoliation hf ha).chord y).B) 1) :=
    Commons.Geometry.Moebius.spliceChord_endpoint_monotone hf ha
  refine witness_of_tpattern_small hf ha (spliceFoliation hf ha) hmono.1 hmono.2 hδ0 hδ ?_
    hperp hcop
  linarith

end Submission
