/-
# `Work.SeedExist.Sides.image_wakeSide`

The **wake sides** `S_j = wakeSide hN z₁ j` of the root portrait are permuted by the map
`Tantibar c z = z̄² + c`: for `j ≤ 3` one has

  `Tantibar c '' S_j = S_{j+1}`.

This is step W3 of `NOTES_LEAD_mandelbar_seed.md` §3.3 in the form in which the seed's
`wake` field consumes it.

## The argument

Let `P_j = (W_j, y_j)` be the pair of rays bounding the wake arc `W_j` (`wakeLo j`, `wakeHi j`),
landing at the `j`-th point `y_j = (T_c)^[j] z₁` of the parabolic cycle; the angle data is the
one of `Work.EL.wakeLo`/`Work.EL.wakeHi`, and `S_j = pairSide P_j` because the angles of the
raw α-pair `alphaPairRaw c z₁ j` and of `P_j` differ by integral translations
(`curve_alphaPairRaw`).

The map `T_c` carries the curve of `P_j` into the curve of `P_{j+1}` (`image_curve_wakePair`)
because `T` sends the wake arc `W_j` onto `W_{j+1}` (`T_wakeLo_wakeHi`).  Hence
`Work.ELPull.side_image_eq` applies: it suffices that

* `S_j` is disjoint from the preimage of the curve of `P_{j+1}` (`disjoint_preimage_wakePair`,
  which uses the antipodal pair: the preimage of a ray of the pair `P_{j+1}` is the
  corresponding ray of `P_j` together with the antipodal ray, and both antipodal rays lie in
  the *other* side of `P_j`), and
* the reference point of `S_j` is mapped into the side of `P_{j+1}` through `W_{j+1}`
  (`T` carries the middle of `W_j` into `W_{j+1}`, `InArc_T_mid_wake`).
-/
import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Antipodal
import Submission.Work.SeedExist.Pairs
import Submission.Work.ELPull.side_image_eq
import Submission.Work.ELPull.pb1
import Submission.Work.ELTop.pairSides_decomposition

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## 0. Elementary bridges -/

/-- The dynamical rays are `1`-periodic in the angle (in the `Work.EL` vocabulary). -/
theorem paramRay_fract_EL {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (Int.fract θ) = Work.EL.paramRay hN θ := by
  conv_lhs => rw [Int.fract]
  rw [show θ - (⌊θ⌋ : ℝ) = θ + (-⌊θ⌋ : ℤ) by push_cast; ring]
  exact Work.ELTop.paramRay_add_int_aux hN θ (-⌊θ⌋)

/-- The image of a dynamical ray under `Tantibar c` lies in the ray of the doubled angle. -/
theorem image_paramRay_EL {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) (θ : ℝ) :
    Tantibar c '' Work.EL.paramRay hN θ ⊆ Work.EL.paramRay hN (Work.EL.T θ) := by
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ Work.EL.paramRay hN θ := hz
  rw [show Work.EL.paramRay hN θ
        = Set.range (fun t : {t : ℝ // 1 < t} => Work.EL.rayPt hN θ t.1)
      from Work.Top.NakaneData.paramRay_eq_range hN θ] at hz'
  obtain ⟨t, rfl⟩ := hz'
  rw [show Work.EL.paramRay hN (Work.EL.T θ)
        = Set.range (fun s : {s : ℝ // 1 < s} => Work.EL.rayPt hN (Work.EL.T θ) s.1)
      from Work.Top.NakaneData.paramRay_eq_range hN (Work.EL.T θ)]
  exact ⟨⟨t.1 ^ 2, by nlinarith [t.2]⟩, Work.ELPull.rayPt_Tantibar hN hφ t.2⟩

/-- **The preimages of a ray of angle `θ` when `T β ≡ θ`.**  If the angle `β` is doubled onto
`θ`, then the preimage of the ray `R(θ)` is contained in `R(β) ∪ R(β + 1/2)`. -/
theorem preimage_paramRay_subset {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    {β θ : ℝ} (h : Work.EL.T β = Int.fract θ) :
    Tantibar c ⁻¹' Work.EL.paramRay hN θ ⊆
      Work.EL.paramRay hN β ∪ Work.EL.paramRay hN (β + 1/2) := by
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  intro x hx
  have hT : Int.fract (-2*β) = Int.fract θ := by simpa [Work.EL.T] using h
  obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hT
  have hhalf : -θ/2 = β + (m:ℝ)/2 := by
    have hm' : (m:ℝ) = -2*β - θ := hm.symm
    rw [hm']; ring
  have h1 : x ∈ Work.EL.paramRay hN (Int.fract (-θ/2)) ∪
      Work.EL.paramRay hN (Int.fract (-θ/2 + 1/2)) :=
    Work.ELPull.preimage_paramRay hN hφ θ hx
  rw [Set.mem_union] at h1 ⊢
  rcases Int.even_or_odd m with hev | hod
  · obtain ⟨q, hq⟩ := hev
    have hmq : (m:ℝ) = 2*(q:ℝ) := by rw [hq]; push_cast; ring
    have hA : Int.fract (-θ/2) = Int.fract β := by
      rw [hhalf, hmq, show β + 2*(q:ℝ)/2 = β + (q:ℝ) by ring, Int.fract_add_intCast]
    have hB : Int.fract (-θ/2 + 1/2) = Int.fract (β + 1/2) := by
      rw [hhalf, hmq, show β + 2*(q:ℝ)/2 + 1/2 = (β + 1/2) + (q:ℝ) by ring,
        Int.fract_add_intCast]
    rw [hA, hB] at h1
    rcases h1 with h | h
    · left; rwa [paramRay_fract_EL hN β] at h
    · right; rwa [paramRay_fract_EL hN (β + 1/2)] at h
  · obtain ⟨q, hq⟩ := hod
    have hmq : (m:ℝ) = 2*(q:ℝ) + 1 := by rw [hq]; push_cast; ring
    have hA : Int.fract (-θ/2) = Int.fract (β + 1/2) := by
      rw [hhalf, hmq, show β + (2*(q:ℝ) + 1)/2 = (β + 1/2) + (q:ℝ) by ring,
        Int.fract_add_intCast]
    have hB : Int.fract (-θ/2 + 1/2) = Int.fract β := by
      rw [hhalf, hmq, show β + (2*(q:ℝ) + 1)/2 + 1/2 = β + ((q + 1 : ℤ) : ℝ)
        by push_cast; ring, Int.fract_add_intCast]
    show x ∈ Work.EL.paramRay hN β ∨ x ∈ Work.EL.paramRay hN (β + 1/2)
    rw [hA, hB] at h1
    rcases h1 with h | h
    · right; rwa [paramRay_fract_EL hN (β + 1/2)] at h
    · left; rwa [paramRay_fract_EL hN β] at h

/-- The fiber of `Tantibar c` over a point: two preimages, opposite to each other. -/
theorem eq_or_eq_neg_of_tantibar_eq {c : ℂ} {z w : ℂ} (h : Tantibar c z = Tantibar c w) :
    z = w ∨ z = -w := by
  have h2 : (starRingEnd ℂ z) ^ 2 = (starRingEnd ℂ w) ^ 2 := by
    have h' := h
    simp only [Tantibar] at h'
    exact add_right_cancel h'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h' | h'
  · left; simpa using congrArg (starRingEnd ℂ) h'
  · right; simpa using congrArg (starRingEnd ℂ) h'

/-- The complementary arc length: `arcLen b a = 1 - arcLen a b` when the two angles are not
congruent modulo `ℤ`. -/
theorem arcLen_swap {a b : ℝ} (h : Work.EL.arcLen a b ≠ 0) :
    Work.EL.arcLen b a = 1 - Work.EL.arcLen a b := by
  rw [Work.EL.arcLen, Work.EL.arcLen, show a - b = -(b - a) by ring, Int.fract_neg h]

/-! ## 1. The wake arcs -/

/-- **The angle doubling carries the wake arc `W_j` onto `W_{j+1}`**: it sends the lower end of
`W_j` to the upper end of `W_{j+1}` and the upper end to the lower end (both modulo `1`). -/
theorem T_wakeLo_wakeHi {j : ℕ} (hj : j ≤ 3) :
    Work.EL.T (Work.EL.wakeLo j) = Int.fract (Work.EL.wakeHi (j + 1)) ∧
      Work.EL.T (Work.EL.wakeHi j) = Int.fract (Work.EL.wakeLo (j + 1)) := by
  interval_cases j <;> norm_num [Work.EL.T, Work.EL.wakeLo, Work.EL.wakeHi, Int.fract]

/-- **The middle of `W_j` is mapped into `W_{j+1}`.** -/
theorem InArc_T_mid_wake {j : ℕ} (hj : j ≤ 3) :
    Work.EL.InArc
      (Work.EL.T (Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2))
      (Work.EL.wakeLo (j + 1)) (Work.EL.wakeHi (j + 1)) := by
  interval_cases j <;>
    norm_num [Work.EL.T, Work.EL.InArc, Work.EL.arcLen, Work.EL.wakeLo, Work.EL.wakeHi,
      Int.fract]

/-- The order of the ends of the wake arcs: `wakeLo j < wakeHi j < wakeLo j + 1`. -/
theorem wakeLo_lt_wakeHi (j : ℕ) (hj : j ≤ 4) :
    Work.EL.wakeLo j < Work.EL.wakeHi j ∧ Work.EL.wakeHi j < Work.EL.wakeLo j + 1 := by
  have h := Work.SeedExist.wakeHi_eq j hj
  have hpos : 0 < Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) :=
    Work.SeedExist.arcLen_wake_pos j (by omega)
  have hlt : Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) < 1 := Int.fract_lt_one _
  constructor
  · rw [h]; linarith
  · rw [h]; linarith

/-- The length of the wake arc `W_j` is nonzero, for `j ≤ 4`. -/
theorem arcLen_wakeLo_wakeHi_ne_zero (j : ℕ) (hj : j ≤ 4) :
    Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) ≠ 0 :=
  ne_of_gt (Work.SeedExist.arcLen_wake_pos j (by omega))

/-- **The antipodal angles lie in the complementary (long) arc**: for `a`, `b` with
`arcLen a b ∈ (0, 1/2)`, both `b + 1/2` and `a + 1/2` lie in the arc from `b` to `a + 1`. -/
theorem InArc_half_of_arcLen {a b : ℝ} (hne : Work.EL.arcLen a b ≠ 0)
    (hlen : Work.EL.arcLen a b < 1/2) :
    Work.EL.InArc (b + 1 / 2) b (a + 1) ∧ Work.EL.InArc (a + 1 / 2) b (a + 1) := by
  have hswap : Work.EL.arcLen b a = 1 - Work.EL.arcLen a b := arcLen_swap hne
  have hb : Work.EL.arcLen b (a + 1) = Work.EL.arcLen b a := by
    rw [Work.EL.arcLen, Work.EL.arcLen,
      show a + 1 - b = (a - b) + ((1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
  have h1 : Int.fract (b + 1 / 2 - b) = 1 / 2 := by
    rw [show b + 1 / 2 - b = (1 / 2 : ℝ) by ring]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have h2 : Int.fract (a + 1 / 2 - b) = 1 / 2 - Work.EL.arcLen a b := by
    rw [Work.EL.arcLen, Int.fract_eq_iff]
    have hf0 : 0 ≤ Int.fract (b - a) := Int.fract_nonneg _
    have hld : Int.fract (b - a) < 1 / 2 := hlen
    refine ⟨by linarith, by linarith, ⟨-⌊b - a⌋, ?_⟩⟩
    have hf : (⌊b - a⌋ : ℝ) = (b - a) - Int.fract (b - a) := by rw [Int.fract]; ring
    push_cast
    rw [hf]; ring
  constructor
  · rw [Work.EL.InArc, h1, hb, hswap]; constructor <;> linarith
  · rw [Work.EL.InArc, h2, hb, hswap]; constructor <;> linarith

/-! ## 2. The wake pair and the wake side -/

/-- The pair of rays bounding the wake arc `W_j`, landing at the `j`-th point of the parabolic
cycle. -/
def wakePair {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    Work.EL.CoPair hN where
  toRawPair := ⟨Work.EL.wakeLo j, Work.EL.wakeHi j, (Tantibar c)^[j] z₁⟩
  lands_a := (Work.SeedExist.landsN_wake hN h1 h2 j hj).1
  lands_b := (Work.SeedExist.landsN_wake hN h1 h2 j hj).2

@[simp] theorem wakePair_a {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    (wakePair hN h1 h2 j hj).a = Work.EL.wakeLo j := rfl

@[simp] theorem wakePair_b {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    (wakePair hN h1 h2 j hj).b = Work.EL.wakeHi j := rfl

@[simp] theorem wakePair_y {c : ℂ} {z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    (wakePair hN h1 h2 j hj).y = (Tantibar c)^[j] z₁ := rfl

/-- The curve of the raw α-pair `alphaPairRaw c z₁ j` is the curve of the pair of the wake arc
`W_j`: the angles of the two pairs differ by integral translations. -/
theorem curve_alphaPairRaw {c z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (j : ℕ) (hj : j ≤ 4) :
    Work.EL.RawPair.curve hN (Work.EL.alphaPairRaw c z₁ j) =
      Work.EL.RawPair.curve hN ⟨Work.EL.wakeLo j, Work.EL.wakeHi j, (Tantibar c)^[j] z₁⟩ := by
  interval_cases j
  · ext z
    simp only [Work.EL.RawPair.curve, Work.EL.alphaPairRaw, Set.mem_union, Set.mem_singleton_iff]
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
      Int.fract, Function.iterate_succ_apply', Function.iterate_zero, min_eq_left]
  · ext z
    simp only [Work.EL.RawPair.curve, Work.EL.alphaPairRaw, Set.mem_union, Set.mem_singleton_iff]
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
      Int.fract, Function.iterate_succ_apply', Function.iterate_zero, min_eq_left, min_eq_right]
  · ext z
    simp only [Work.EL.RawPair.curve, Work.EL.alphaPairRaw, Set.mem_union, Set.mem_singleton_iff]
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
      Int.fract, Function.iterate_succ_apply', Function.iterate_zero, min_eq_left, min_eq_right]
  · ext z
    simp only [Work.EL.RawPair.curve, Work.EL.alphaPairRaw, Set.mem_union, Set.mem_singleton_iff]
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
      Int.fract, Function.iterate_succ_apply', Function.iterate_zero, min_eq_left, min_eq_right]
    have h3 : (1124 : ℝ) / 1023 = 101 / 1023 + 1 := by norm_num
    rw [h3, Work.ELTop.paramRay_add_one hN (101 / 1023)]
    tauto
  · ext z
    simp only [Work.EL.RawPair.curve, Work.EL.alphaPairRaw, Set.mem_union, Set.mem_singleton_iff]
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.alpha1, Work.EL.alpha2, Work.EL.T,
      Int.fract, Function.iterate_succ_apply', Function.iterate_zero, min_eq_left, min_eq_right]
    have h3 : (1349 : ℝ) / 1023 = 326 / 1023 + 1 := by norm_num
    rw [h3, Work.ELTop.paramRay_add_one hN (326 / 1023)]
    tauto

/-- The curve of the wake pair is the curve of the raw α-pair. -/
theorem curve_wakePair {c z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    Work.EL.RawPair.curve hN (Work.EL.alphaPairRaw c z₁ j) =
      Work.EL.RawPair.curve hN (wakePair hN h1 h2 j hj).toRawPair := by
  rw [curve_alphaPairRaw hN j hj]
  rfl

/-- **The wake side `S_j` is the side of the wake pair `P_j`**: `wakeSide hN z₁ j = pairSide P_j`. -/
theorem wakeSide_eq_pairSide {c z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 4) :
    Work.SeedExist.wakeSide hN z₁ j = Work.EL.pairSide (wakePair hN h1 h2 j hj) := by
  have hL : Work.SeedExist.wakeSide hN z₁ j
      = Work.EL.RawPair.sideThrough hN (Work.EL.alphaPairRaw c z₁ j)
          (Work.EL.wakeLo j) (Work.EL.wakeHi j) := rfl
  have hR : Work.EL.pairSide (wakePair hN h1 h2 j hj)
      = Work.EL.RawPair.sideThrough hN (wakePair hN h1 h2 j hj).toRawPair
          (Work.EL.wakeLo j) (Work.EL.wakeHi j) := rfl
  rw [hL, hR]
  simp only [Work.EL.RawPair.sideThrough]
  rw [curve_wakePair hN h1 h2 j hj]

/-! ## 3. The image of the wake curve -/

/-- **`Tantibar c` maps the curve of `P_j` into the curve of `P_{j+1}`**, for `j ≤ 3`. -/
theorem image_curve_wakePair {c z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 3) :
    Tantibar c '' Work.EL.RawPair.curve hN (wakePair hN h1 h2 j (by omega)).toRawPair ⊆
      Work.EL.RawPair.curve hN (wakePair hN h1 h2 (j + 1) (by omega)).toRawPair := by
  obtain ⟨hTlo, hThi⟩ := T_wakeLo_wakeHi hj
  rw [show (wakePair hN h1 h2 j (by omega)).toRawPair
      = ⟨Work.EL.wakeLo j, Work.EL.wakeHi j, (Tantibar c)^[j] z₁⟩ from rfl]
  rw [show (wakePair hN h1 h2 (j + 1) (by omega)).toRawPair
      = ⟨Work.EL.wakeLo (j + 1), Work.EL.wakeHi (j + 1), (Tantibar c)^[j + 1] z₁⟩ from rfl]
  rintro w ⟨z, hz, rfl⟩
  simp only [Work.EL.RawPair.curve, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
  rcases hz with (hz | hz) | hz
  · -- `z` on the ray of `wakeLo j`: the image lies on the ray of `wakeHi (j+1)`
    refine Or.inr ?_
    have h := image_paramRay_EL hN (Work.EL.wakeLo j) ⟨z, hz, rfl⟩
    rw [hTlo] at h
    rwa [paramRay_fract_EL hN (Work.EL.wakeHi (j + 1))] at h
  · -- the landing point
    rw [hz]
    refine Or.inl (Or.inr ?_)
    exact (Function.iterate_succ_apply' (Tantibar c) j z₁).symm
  · -- `z` on the ray of `wakeHi j`: the image lies on the ray of `wakeLo (j+1)`
    refine Or.inl (Or.inl ?_)
    have h := image_paramRay_EL hN (Work.EL.wakeHi j) ⟨z, hz, rfl⟩
    rw [hThi] at h
    rwa [paramRay_fract_EL hN (Work.EL.wakeLo (j + 1))] at h

/-! ## 4. The antipodal landing point lies in the other side -/

/-- **The antipode of the landing point of a pair lies in the near (long) side.**  If the far arc
of the pair `P` is short (`arcLen P.a P.b < 1/2`) and `P.y ≠ 0`, then `-P.y` is on the near side:
it is the landing point of the antipodal ray `R(P.b + 1/2)`, whose angle lies in the long arc. -/
theorem neg_landing_mem_pairSideNear {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (P : Work.EL.CoPair hN) (ha : P.a < P.b) (hb : P.b < P.a + 1)
    (hne : Work.EL.arcLen P.a P.b ≠ 0) (hlen : Work.EL.arcLen P.a P.b < 1/2)
    (hy : P.y ≠ 0) : -P.y ∈ Work.EL.pairSideNear P := by
  have hland : Work.EL.LandsN hN (P.b + 1/2) (-P.y) :=
    Work.SeedExist.landsN_add_half hN P.lands_b
  have hsub : Work.EL.paramRay hN (P.b + 1/2) ⊆ Work.EL.pairSideNear P :=
    Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN P ha hb
      (InArc_half_of_arcLen hne hlen).1
  have hcl : -P.y ∈ closure (Work.EL.pairSideNear P) :=
    mem_closure_of_tendsto hland (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hsub (Work.EL.rayPt_mem_paramRay hN ht))
  have hyK : P.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN P.lands_b
  have hnegK : -P.y ∈ Work.EL.K c := (mem_K_neg_iff).mpr hyK
  have hnotcurve : -P.y ∉ Work.EL.pairCurve P := by
    intro hmem
    have h1 := Work.ELTop.pairCurve_inter_K_subset hN P ⟨hmem, hnegK⟩
    rw [Set.mem_singleton_iff] at h1
    exact hy (by linear_combination (-1/2) * h1)
  have hint : -P.y ∈ interior (Work.EL.pairSideNear P) := by
    by_contra h
    have hfr : -P.y ∈ frontier (Work.EL.pairSideNear P) := by
      rw [← closure_sdiff_interior]
      exact ⟨hcl, h⟩
    rw [Work.ELTop.frontier_pairSideNear hN P ha hb] at hfr
    exact hnotcurve hfr
  exact interior_subset hint

/-! ## 5. The side misses the preimage of the next curve -/

/-- **`S_j` is disjoint from the preimage of the curve of `P_{j+1}`.**  Indeed the preimage of
each ray of `P_{j+1}` is the corresponding ray of `P_j` together with the antipodal ray, and both
antipodal rays lie in the near side of `P_j` (`InArc_half_of_arcLen`); the preimage of the
landing point is the pair `{P_j.y, -P_j.y}`, the second point being on the near side as well
(`neg_landing_mem_pairSideNear`). -/
theorem disjoint_preimage_wakePair {c z₁ : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) (j : ℕ) (hj : j ≤ 3)
    (hzj : (Tantibar c)^[j] z₁ ≠ 0) :
    Disjoint (Work.EL.pairSide (wakePair hN h1 h2 j (by omega)))
      (Tantibar c ⁻¹' Work.EL.pairCurve (wakePair hN h1 h2 (j + 1) (by omega))) := by
  obtain ⟨hTlo, hThi⟩ := T_wakeLo_wakeHi hj
  have hj4 : j ≤ 4 := by omega
  have harcne : Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) ≠ 0 :=
    arcLen_wakeLo_wakeHi_ne_zero j hj4
  have harclt : Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) < 1/2 :=
    Work.SeedExist.arcLen_wake_lt_half j hj
  obtain ⟨hord1, hord2⟩ := wakeLo_lt_wakeHi j hj4
  obtain ⟨hin1, hin2⟩ := InArc_half_of_arcLen harcne harclt
  have ha : (wakePair hN h1 h2 j hj4).a < (wakePair hN h1 h2 j hj4).b := by
    simpa using hord1
  have hb : (wakePair hN h1 h2 j hj4).b < (wakePair hN h1 h2 j hj4).a + 1 := by
    simpa using hord2
  have hdisj : Disjoint (Work.EL.pairSide (wakePair hN h1 h2 j hj4))
      (Work.EL.pairSideNear (wakePair hN h1 h2 j hj4)) :=
    Work.ELTop.pairSide_disjoint hN hJ _ ha hb
  have hnear1 : Work.EL.paramRay hN (Work.EL.wakeHi j + 1/2) ⊆
      Work.EL.pairSideNear (wakePair hN h1 h2 j hj4) := by
    refine Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN _ ha hb ?_
    simpa using hin1
  have hnear2 : Work.EL.paramRay hN (Work.EL.wakeLo j + 1/2) ⊆
      Work.EL.pairSideNear (wakePair hN h1 h2 j hj4) := by
    refine Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN _ ha hb ?_
    simpa using hin2
  have hnegy : -(wakePair hN h1 h2 j hj4).y ∈
      Work.EL.pairSideNear (wakePair hN h1 h2 j hj4) := by
    refine neg_landing_mem_pairSideNear hN _ ha hb harcne harclt ?_
    simpa using hzj
  have hsub : Work.EL.pairSide (wakePair hN h1 h2 j hj4) ⊆
      (Work.EL.pairCurve (wakePair hN h1 h2 j hj4))ᶜ :=
    connectedComponentIn_subset _ _
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxc : x ∉ Work.EL.pairCurve (wakePair hN h1 h2 j hj4) := hsub hx
  have hx'' : Tantibar c x ∈ Work.EL.pairCurve (wakePair hN h1 h2 (j + 1) (by omega)) := hx'
  rw [Work.EL.mem_pairCurve_iff] at hx''
  rw [wakePair_a, wakePair_b, wakePair_y] at hx''
  rcases hx'' with hA | hB | hC
  · rcases preimage_paramRay_subset hN hThi hA with h | h
    · exact hxc ((Work.EL.mem_pairCurve_iff _ x).mpr (Or.inr (Or.inr h)))
    · exact Set.disjoint_left.mp hdisj hx (hnear1 h)
  · have heq : Tantibar c x = Tantibar c (wakePair hN h1 h2 j hj4).y := by
      rw [hB, wakePair_y]
      exact Function.iterate_succ_apply' (Tantibar c) j z₁
    rcases eq_or_eq_neg_of_tantibar_eq heq with h | h
    · exact hxc ((Work.EL.mem_pairCurve_iff _ x).mpr (Or.inr (Or.inl h)))
    · rw [h] at hx
      exact Set.disjoint_left.mp hdisj hx hnegy
  · rcases preimage_paramRay_subset hN hTlo hC with h | h
    · exact hxc ((Work.EL.mem_pairCurve_iff _ x).mpr (Or.inl h))
    · exact Set.disjoint_left.mp hdisj hx (hnear2 h)

/-! ## 6. The main theorem -/

theorem image_wakeSide {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hzn : ∀ i : ℕ, i ≤ 4 → (LeanEval.ComplexAnalysis.Tantibar c)^[i] z₁ ≠ 0)
    (j : ℕ) (hj : j ≤ 3) :
    LeanEval.ComplexAnalysis.Tantibar c '' Work.SeedExist.wakeSide hN z₁ j =
      Work.SeedExist.wakeSide hN z₁ (j + 1) := by
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have hj4 : j ≤ 4 := by omega
  have hj4' : j + 1 ≤ 4 := by omega
  have hzj : (Tantibar c)^[j] z₁ ≠ 0 := hzn j hj4
  -- the two pairs, in the `Work.ELPull` vocabulary used by `side_image_eq`
  let G : Work.ELPull.CoPair hN :=
    ⟨Work.EL.wakeLo j, Work.EL.wakeHi j, (Tantibar c)^[j] z₁,
      (landsN_wake hN h1 h2 j hj4).1, (landsN_wake hN h1 h2 j hj4).2⟩
  let Q : Work.ELPull.CoPair hN :=
    ⟨Work.EL.wakeLo (j + 1), Work.EL.wakeHi (j + 1), (Tantibar c)^[j + 1] z₁,
      (landsN_wake hN h1 h2 (j + 1) hj4').1, (landsN_wake hN h1 h2 (j + 1) hj4').2⟩
  have htop : Work.ELPull.PB1Top hN := Work.ELPull.pb1Top_of_jordanForm hN hJ
  -- the middle of the wake arc lies in the wake arc
  have hmid : Work.EL.InArc
      (Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2)
      (Work.EL.wakeLo j) (Work.EL.wakeHi j) := by
    have hpos := Work.SeedExist.arcLen_wake_pos j (by omega)
    have hlt := Work.SeedExist.arcLen_wake_lt_half j hj
    rw [Work.EL.InArc]
    have h1 : Int.fract (Work.EL.wakeLo j
          + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2 - Work.EL.wakeLo j)
        = Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2 := by
      rw [show Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2
            - Work.EL.wakeLo j = Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2
          by ring]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [h1]
    exact ⟨by linarith, by linarith⟩
  -- (i) the curve of `G` is mapped into the curve of `Q`
  have himg : Tantibar c '' Work.ELPull.pairCurve hN G ⊆ Work.ELPull.pairCurve hN Q :=
    image_curve_wakePair hN h1 h2 j hj
  -- (ii) the side misses the preimage of the curve of `Q`
  have hmiss : Disjoint (Work.ELPull.pairSide hN G)
      (Tantibar c ⁻¹' Work.ELPull.pairCurve hN Q) :=
    disjoint_preimage_wakePair hN hJ h1 h2 j hj hzj
  -- (iii) the reference point of the side is mapped into the side of `Q` through `W_{j+1}`
  have hpt : ∃ x ∈ Work.ELPull.pairSide hN G,
      Tantibar c x ∈ Work.ELPull.arcSide hN Q (Work.EL.wakeLo (j + 1))
        (Work.EL.wakeHi (j + 1)) := by
    refine ⟨Work.EL.rayPt hN
      (Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2) 2, ?_, ?_⟩
    · exact Work.ELPull.arcSide_angle hN G G.a G.b _
        (Or.inl ⟨rfl, rfl⟩) hmid (Work.EL.rayPt_mem_paramRay hN (by norm_num))
    · have hx : Tantibar c (Work.EL.rayPt hN
          (Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2) 2)
          = Work.EL.rayPt hN (Work.EL.T (Work.EL.wakeLo j
              + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) / 2)) (2 ^ 2) :=
        (Work.ELPull.rayPt_Tantibar hN hφ (by norm_num : (1 : ℝ) < 2)).symm
      rw [hx]
      exact Work.ELPull.arcSide_angle hN Q (Work.EL.wakeLo (j + 1)) (Work.EL.wakeHi (j + 1)) _
        (Or.inl ⟨rfl, rfl⟩) (InArc_T_mid_wake hj) (Work.EL.rayPt_mem_paramRay hN (by norm_num))
  have hside := Work.ELPull.side_image_eq hN htop G Q
    (Work.EL.wakeLo (j + 1)) (Work.EL.wakeHi (j + 1)) himg hmiss hpt
  rw [wakeSide_eq_pairSide hN h1 h2 j hj4, wakeSide_eq_pairSide hN h1 h2 (j + 1) hj4']
  exact hside

end Work.SeedExist.Sides
