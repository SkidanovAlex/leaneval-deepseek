/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — `L4`: the side of a pair is read off the angle, locally at a ray point

`NOTES_LEAD_mandelbar_rn0.md` §2, `L4` (with the corrected margin of
`Submission/Work/SeedSimple2/COP/NOTES_COP.md` §2: the constant `η` of the design note is too
weak, because it does not bound `1 - μ` and `1 - μ'`).

The lemma is purely angular.  At a point `p` of one of the two rays of a co-landing pair `P`,
the map `F c = (T_c)^{10}` multiplies the external angle by `1024` (mod `1`).  If `z` is close
enough to `p` in the plane, then its external angle `φ` is close to the angle `e ∈ {P.a, P.b}`
of the ray through `p`, and the sign of the angular offset `σ = φ - e` is preserved by the
factor `1024 > 0`.  Reading the two sides of the pair off the angle
(`Work.SeedSimple2.COP.mem_pairSide_iff_InArc`) and comparing the four cases of the sign of `σ`
and of the choice of the ray, one finds

* `z ∈ Work.EL.pairSide P ↔ F c z ∈ Work.EL.pairSide P'` (far goes to far, near goes to near);

and moreover `F c z` avoids the curve of `P'` altogether, because its angle
`Int.fract (1024 * φ)` is never congruent to `P'.a` or `P'.b` modulo `1` and `F c z ∉ K c`.

The arithmetic core is isolated in `angle_correspondence_a` / `angle_correspondence_b`; the
uniform final step is `local_angle_concl`.
-/
import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.extAngle_close_at
import Submission.Work.SeedSimple2.COP.mem_pairSide_iff_InArc
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.SeedSimple2.COP

/-! ## Two elementary facts about `Int.fract` -/

/-- `Int.fract` commutes with the subtraction of a real number *after* having been applied:
`fract (fract y - a) = fract (y - a)`, because `fract y - y` is an integer. -/
theorem fract_fract_sub {y a : ℝ} : Int.fract (Int.fract y - a) = Int.fract (y - a) := by
  have h : Int.fract y - a = (y - a) - (⌊y⌋ : ℤ) := by
    have hh := Int.fract_add_floor y
    linarith
  rw [h, Int.fract_sub_intCast]

/-- The fractional part of a real number in `(-1, 0)`: `fract x = x + 1`. -/
theorem fract_eq_add_one {x : ℝ} (h1 : -1 < x) (h2 : x < 0) : Int.fract x = x + 1 := by
  have hx : x = (x + 1) - (1 : ℤ) := by push_cast; ring
  conv_lhs => rw [hx]
  rw [Int.fract_sub_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

/-- Two angles of `(0,1)` which are distinct are not congruent modulo `1`: the cyclic arc
between them is nondegenerate. -/
theorem arcLen_ne_zero_of_mem_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hb : b ∈ Set.Ioo (0:ℝ) 1) (h : a ≠ b) : Work.EL.arcLen a b ≠ 0 := by
  intro h0
  have hf : Int.fract (b - a) = 0 := h0
  obtain ⟨k, hk⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp hf)
  have hk' : (k : ℝ) = b - a := hk
  have h2 : -(1:ℝ) < (k:ℝ) ∧ (k:ℝ) < 1 := by
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hk']
  have h3 : (-1 : ℤ) < k := by exact_mod_cast h2.1
  have h4 : k < (1 : ℤ) := by exact_mod_cast h2.2
  have h5 : k = 0 := by omega
  rw [h5] at hk'
  push_cast at hk'
  exact h (by linarith)

/-! ## Two facts about the rays of `F` -/

/-- Two parameter rays through a common point have angles which are congruent modulo `1`. -/
theorem exists_eq_add_int_of_mem_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ θ' : ℝ}
    {z : ℂ} (hz : z ∈ Work.EL.paramRay hN θ) (hz' : z ∈ Work.EL.paramRay hN θ') :
    ∃ k : ℤ, θ = θ' + k := by
  by_contra h
  push Not at h
  exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN h) hz' hz

/-- **`F` maps rays to rays**: the image of the ray of angle `θ` is contained in the ray of the
angle `Int.fract (1024 * θ)`.  (`F c = (T_c)^{10}` acts on the Böttcher angle by
`θ ↦ -2θ mod 1`, so on the tenth iterate by `θ ↦ 1024 θ mod 1`.) -/
theorem F_mem_paramRay_fract {c : ℂ} (d : Work.EL.RootParabolic c) {θ : ℝ} {z : ℂ}
    (hz : z ∈ Work.EL.paramRay d.hN θ) :
    Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract (1024 * θ)) := by
  have hz' : z ∈ Work.Top.NakaneData.paramRay d.hN θ := hz
  rw [Work.Top.NakaneData.paramRay_eq_range] at hz'
  obtain ⟨⟨t, ht⟩, htz⟩ := hz'
  have htz' : Work.EL.rayPt d.hN θ t = z := htz
  obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int θ 10
  have hm' : Work.EL.T^[10] θ = (1024 : ℝ) * θ + (m : ℝ) := by
    have h : ((-2 : ℝ) ^ 10) = 1024 := by norm_num
    rw [h] at hm
    exact hm
  have hfl : (1024 : ℝ) * θ = Int.fract (1024 * θ) + (⌊(1024:ℝ) * θ⌋ : ℤ) := by
    have h := Int.fract_add_floor ((1024:ℝ) * θ)
    linarith
  have htarget : Work.EL.rayPt d.hN (Int.fract (1024 * θ)) (t ^ 1024) = Work.EL.F c z := by
    rw [← htz', Work.ELRig.rayPt_iterate d.hN d.bottcher ht, hm']
    rw [show (1024:ℝ) * θ + (m:ℝ)
        = Int.fract (1024 * θ) + ((⌊(1024:ℝ) * θ⌋ + m : ℤ) : ℝ) by push_cast; linarith,
      Work.ELTop.rayPt_add_int]
  exact htarget ▸ Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ ht (by norm_num))

/-! ## The angular core: the four cases -/

/-- **The angular core of `L4`, first ray.**  If `φ = a + σ` with `σ ≠ 0`, `|σ| < η`, and `η`
small compared with the two arc lengths (`η ≤ μ/2`, `η ≤ (1-μ)/2`, `η ≤ μ'/2048`,
`η ≤ (1-μ')/2048`, where `μ = arcLen a b` and `μ' = arcLen a' b'` are the arcs of the pairs and
`a' ≡ 1024 a`, `b' ≡ 1024 b` are the images of their angles), then

* the arc membership of `φ` in `(a,b)` is equivalent to that of `Int.fract (1024 φ)` in
  `(a',b')` (both are true when `σ > 0`, both false when `σ < 0`);
* `φ` is congruent to neither `a` nor `b` modulo `1`, and `Int.fract (1024 φ)` to neither `a'`
  nor `b'` modulo `1`.

This is the `σ > 0` half of the four-case table of `COP/NOTES_COP.md` §2 when `p` lies on the
ray `R(P.a)`, and its mirror image for `σ < 0`. -/
theorem angle_correspondence_a {a b a' b' φ σ η : ℝ}
    (hφ : φ = a + σ)
    (ha' : ∃ k : ℤ, a' = 1024 * a + k) (hb' : ∃ k : ℤ, b' = 1024 * b + k)
    (hσ0 : σ ≠ 0) (hσ1 : |σ| < η)
    (hμ0 : 0 < Work.EL.arcLen a b) (hμ1 : Work.EL.arcLen a b < 1)
    (hμ'0 : 0 < Work.EL.arcLen a' b') (hμ'1 : Work.EL.arcLen a' b' < 1)
    (hημ : η ≤ Work.EL.arcLen a b / 2) (hη1μ : η ≤ (1 - Work.EL.arcLen a b) / 2)
    (hημ' : η ≤ Work.EL.arcLen a' b' / 2048) (hη1μ' : η ≤ (1 - Work.EL.arcLen a' b') / 2048) :
    (Work.EL.InArc φ a b ↔ Work.EL.InArc (Int.fract (1024 * φ)) a' b') ∧
    (∀ k : ℤ, φ ≠ a + k) ∧ (∀ k : ℤ, φ ≠ b + k) ∧
    (∀ k : ℤ, Int.fract (1024 * φ) ≠ a' + k) ∧
    (∀ k : ℤ, Int.fract (1024 * φ) ≠ b' + k) := by
  have hσgt : -η < σ := (abs_lt.mp hσ1).1
  have hσlt : σ < η := (abs_lt.mp hσ1).2
  rcases lt_or_gt_of_ne hσ0 with hσneg | hσpos
  · -- `σ < 0`: both arcs are `false`
    have hσneg1 : -1 < σ := by linarith [hσgt, hημ, hμ0]
    have h1024neg : -1 < 1024 * σ := by linarith [hσgt, hημ', hμ'0, hμ'1]
    have hρ : Int.fract (φ - a) = σ + 1 := by
      rw [hφ, show a + σ - a = σ by ring]
      exact fract_eq_add_one hσneg1 hσneg
    have hρ' : Int.fract (1024 * φ - a') = 1024 * σ + 1 := by
      obtain ⟨k, hk⟩ := ha'
      rw [hφ, hk, show 1024 * (a + σ) - (1024 * a + (k : ℝ)) = 1024 * σ - (k : ℝ) by ring,
        Int.fract_sub_intCast]
      exact fract_eq_add_one h1024neg (by linarith)
    have hρbig : Work.EL.arcLen a b < σ + 1 := by linarith [hσgt, hη1μ, hμ1]
    have hρ'big : Work.EL.arcLen a' b' < 1024 * σ + 1 := by linarith [hσgt, hη1μ', hμ'1]
    have hn1 : ¬ Work.EL.InArc φ a b := by
      rw [Work.EL.InArc, hρ]
      intro h
      linarith [h.2, hρbig]
    have hn2 : ¬ Work.EL.InArc (Int.fract (1024 * φ)) a' b' := by
      rw [Work.EL.InArc, fract_fract_sub, hρ']
      intro h
      linarith [h.2, hρ'big]
    refine ⟨⟨fun h => absurd h hn1, fun h => absurd h hn2⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hσneg1] : (0:ℝ) < σ + 1))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (φ - a) = Work.EL.arcLen a b := by
        rw [hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
        rfl
      rw [hρ] at h0
      exact absurd h0 (ne_of_gt hρbig)
    · intro k hk
      apply (ne_of_gt (by linarith : (0:ℝ) < 1024 * σ + 1))
      rw [← hρ', ← fract_fract_sub, hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (1024 * φ - a') = Work.EL.arcLen a' b' := by
        rw [← fract_fract_sub, hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
          Int.fract_add_intCast]
        rfl
      rw [hρ'] at h0
      exact absurd h0 (ne_of_gt hρ'big)
  · -- `σ > 0`: both arcs are `true`
    have hσ1lt : σ < 1 := by linarith [hσlt, hημ, hμ0]
    have h1024lt : 1024 * σ < 1 := by linarith [hσlt, hημ', hμ'0, hμ'1]
    have hρ : Int.fract (φ - a) = σ := by
      rw [hφ, show a + σ - a = σ by ring,
        Int.fract_eq_self.mpr ⟨le_of_lt hσpos, hσ1lt⟩]
    have hρ' : Int.fract (1024 * φ - a') = 1024 * σ := by
      obtain ⟨k, hk⟩ := ha'
      rw [hφ, hk, show 1024 * (a + σ) - (1024 * a + (k : ℝ)) = 1024 * σ - (k : ℝ) by ring,
        Int.fract_sub_intCast, Int.fract_eq_self.mpr ⟨by linarith, h1024lt⟩]
    have hρsmall : σ < Work.EL.arcLen a b := by linarith [hσlt, hημ, hμ0]
    have hρ'small : 1024 * σ < Work.EL.arcLen a' b' := by linarith [hσlt, hημ', hμ'0]
    have h1 : Work.EL.InArc φ a b := by
      refine ⟨?_, ?_⟩
      · rw [hρ]; exact hσpos
      · rw [hρ]; exact hρsmall
    have h2 : Work.EL.InArc (Int.fract (1024 * φ)) a' b' := by
      refine ⟨?_, ?_⟩
      · rw [fract_fract_sub, hρ']; linarith
      · rw [fract_fract_sub, hρ']; exact hρ'small
    refine ⟨⟨fun _ => h2, fun _ => h1⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply hσ0
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (φ - a) = Work.EL.arcLen a b := by
        rw [hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
        rfl
      rw [hρ] at h0
      exact absurd h0 (ne_of_lt hρsmall)
    · intro k hk
      apply (ne_of_gt (by linarith : (0:ℝ) < 1024 * σ))
      rw [← hρ', ← fract_fract_sub, hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      have h0 : Int.fract (1024 * φ - a') = Work.EL.arcLen a' b' := by
        rw [← fract_fract_sub, hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
          Int.fract_add_intCast]
        rfl
      rw [hρ'] at h0
      exact absurd h0 (ne_of_lt hρ'small)

/-- **The angular core of `L4`, second ray.**  The same statement as
`angle_correspondence_a`, for `φ = b + σ`, i.e. for a point `p` on the ray `R(P.b)`: now
`σ > 0` gives the *near* arc and `σ < 0` the *far* arc (see the table of
`COP/NOTES_COP.md` §2), and both sides of the equivalence always agree. -/
theorem angle_correspondence_b {a b a' b' φ σ η : ℝ}
    (hφ : φ = b + σ)
    (ha' : ∃ k : ℤ, a' = 1024 * a + k) (hb' : ∃ k : ℤ, b' = 1024 * b + k)
    (hσ0 : σ ≠ 0) (hσ1 : |σ| < η)
    (hμ0 : 0 < Work.EL.arcLen a b) (hμ1 : Work.EL.arcLen a b < 1)
    (hμ'0 : 0 < Work.EL.arcLen a' b') (hμ'1 : Work.EL.arcLen a' b' < 1)
    (hημ : η ≤ Work.EL.arcLen a b / 2) (hη1μ : η ≤ (1 - Work.EL.arcLen a b) / 2)
    (hημ' : η ≤ Work.EL.arcLen a' b' / 2048) (hη1μ' : η ≤ (1 - Work.EL.arcLen a' b') / 2048) :
    (Work.EL.InArc φ a b ↔ Work.EL.InArc (Int.fract (1024 * φ)) a' b') ∧
    (∀ k : ℤ, φ ≠ a + k) ∧ (∀ k : ℤ, φ ≠ b + k) ∧
    (∀ k : ℤ, Int.fract (1024 * φ) ≠ a' + k) ∧
    (∀ k : ℤ, Int.fract (1024 * φ) ≠ b' + k) := by
  have hσgt : -η < σ := (abs_lt.mp hσ1).1
  have hσlt : σ < η := (abs_lt.mp hσ1).2
  have hfl : b - a = Work.EL.arcLen a b + ((⌊b - a⌋ : ℤ) : ℝ) := by
    have h := Int.floor_add_fract (b - a)
    rw [Work.EL.arcLen]
    linarith
  have hρ : Int.fract (φ - a) = Work.EL.arcLen a b + σ := by
    conv_lhs => rw [hφ]
    rw [show b + σ - a = (b - a) + σ by ring, hfl]
    rw [show Work.EL.arcLen a b + ((⌊b - a⌋ : ℤ) : ℝ) + σ
        = (Work.EL.arcLen a b + σ) + ((⌊b - a⌋ : ℤ) : ℝ) by ring, Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ0, hσgt, hημ]
      · linarith [hμ0, h]
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ1, h]
      · linarith [hμ1, hσlt, hη1μ]
  have hρ' : Int.fract (1024 * φ - a') = Work.EL.arcLen a' b' + 1024 * σ := by
    obtain ⟨k₁, hk₁⟩ := ha'
    obtain ⟨k₂, hk₂⟩ := hb'
    have h4 : 1024 * (b - a)
        = Work.EL.arcLen a' b' + ((⌊b' - a'⌋ : ℝ) - ((k₂ - k₁ : ℤ) : ℝ)) := by
      have h := Int.floor_add_fract (b' - a')
      have hf : Int.fract (b' - a') = Work.EL.arcLen a' b' := rfl
      have hb : b' - a' = 1024 * (b - a) + ((k₂ - k₁ : ℤ) : ℝ) := by
        rw [hk₁, hk₂]; push_cast; ring
      linarith
    conv_lhs => rw [hφ, hk₁]
    rw [show 1024 * (b + σ) - (1024 * a + (k₁ : ℝ))
          = 1024 * (b - a) + 1024 * σ - (k₁ : ℝ) by ring, h4]
    rw [show Work.EL.arcLen a' b' + ((⌊b' - a'⌋ : ℝ) - ((k₂ - k₁ : ℤ) : ℝ)) + 1024 * σ
          - (k₁ : ℝ)
          = (Work.EL.arcLen a' b' + 1024 * σ)
            + ((⌊b' - a'⌋ - (k₂ - k₁) - k₁ : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ'0, hσgt, hημ']
      · linarith [hμ'0, h]
    · rcases lt_or_gt_of_ne hσ0 with h | h
      · linarith [hμ'1, h]
      · linarith [hμ'1, hσlt, hη1μ']
  rcases lt_or_gt_of_ne hσ0 with hσneg | hσpos
  · -- `σ < 0`: both arcs are `true`
    have h1 : Work.EL.InArc φ a b := by
      refine ⟨?_, ?_⟩
      · rw [hρ]; linarith [hσgt, hημ, hμ0]
      · rw [hρ]; linarith [hσneg]
    have h2 : Work.EL.InArc (Int.fract (1024 * φ)) a' b' := by
      refine ⟨?_, ?_⟩
      · rw [fract_fract_sub, hρ']; linarith [hσgt, hημ', hμ'0]
      · rw [fract_fract_sub, hρ']; linarith [hσneg]
    refine ⟨⟨fun _ => h2, fun _ => h1⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hμ0, hσgt, hημ] :
        (0:ℝ) < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      apply (ne_of_lt (by linarith [hσneg] :
        (Work.EL.arcLen a b + σ) < Work.EL.arcLen a b))
      rw [← hρ, hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
      rfl
    · intro k hk
      apply (ne_of_gt (by linarith [hμ'0, hσgt, hημ'] :
        (0:ℝ) < Work.EL.arcLen a' b' + 1024 * σ))
      rw [← hρ', ← fract_fract_sub, hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      apply (ne_of_lt (by linarith [hσneg] :
        (Work.EL.arcLen a' b' + 1024 * σ) < Work.EL.arcLen a' b'))
      rw [← hρ', ← fract_fract_sub, hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
        Int.fract_add_intCast]
      rfl
  · -- `σ > 0`: both arcs are `false`
    have hn1 : ¬ Work.EL.InArc φ a b := by
      rw [Work.EL.InArc, hρ]
      intro h
      linarith [h.2]
    have hn2 : ¬ Work.EL.InArc (Int.fract (1024 * φ)) a' b' := by
      rw [Work.EL.InArc, fract_fract_sub, hρ']
      intro h
      linarith [h.2]
    refine ⟨⟨fun h => absurd h hn1, fun h => absurd h hn2⟩, ?_, ?_, ?_, ?_⟩
    · intro k hk
      apply (ne_of_gt (by linarith [hμ0, hσpos] : (0:ℝ) < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show a + (k : ℝ) - a = (k : ℝ) by ring, Int.fract_intCast]
    · intro k hk
      apply (ne_of_gt (by linarith [hσpos] :
        Work.EL.arcLen a b < Work.EL.arcLen a b + σ))
      rw [← hρ, hk, show b + (k : ℝ) - a = (b - a) + (k : ℝ) by ring, Int.fract_add_intCast]
      rfl
    · intro k hk
      apply (ne_of_gt (by linarith [hμ'0, hσpos] : (0:ℝ) < Work.EL.arcLen a' b' + 1024 * σ))
      rw [← hρ', ← fract_fract_sub, hk, show a' + (k : ℝ) - a' = (k : ℝ) by ring,
        Int.fract_intCast]
    · intro k hk
      apply (ne_of_gt (by linarith [hσpos] :
        Work.EL.arcLen a' b' < Work.EL.arcLen a' b' + 1024 * σ))
      rw [← hρ', ← fract_fract_sub, hk, show b' + (k : ℝ) - a' = (b' - a') + (k : ℝ) by ring,
        Int.fract_add_intCast]
      rfl

/-! ## The uniform final step -/

/-- **The conclusion of `L4` from the local angle data**: if `z` lies on the ray of angle `φ`,
`F c z` on the ray of angle `Int.fract (1024 φ)`, if the arc memberships of these two angles
correspond and neither is congruent to an endpoint modulo `1`, then the sides correspond and no
point of the curve of `P'` is created.  The last point is where `F c z ∉ K c` (it is a point of a
ray) and `P'.y ∈ K c` are used. -/
theorem local_angle_concl {c : ℂ} (d : Work.EL.RootParabolic c) {P P' : Work.EL.CoPair d.hN}
    (hS : Work.EL.PairSides d.hN P) (hS' : Work.EL.PairSides d.hN P')
    (hab : ∀ k : ℤ, P.b ≠ P.a + k) (hab' : ∀ k : ℤ, P'.b ≠ P'.a + k)
    {φ : ℝ} (hφa : ∀ k : ℤ, φ ≠ P.a + k) (hφb : ∀ k : ℤ, φ ≠ P.b + k)
    (hFa : ∀ k : ℤ, Int.fract (1024 * φ) ≠ P'.a + k)
    (hFb : ∀ k : ℤ, Int.fract (1024 * φ) ≠ P'.b + k)
    (heq : Work.EL.InArc φ P.a P.b ↔ Work.EL.InArc (Int.fract (1024 * φ)) P'.a P'.b)
    {z : ℂ} (hz : z ∈ Work.EL.paramRay d.hN φ)
    (hFz : Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract (1024 * φ))) :
    Work.EL.F c z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P') := by
  have hPK : P'.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN P'.lands_a
  have hFzK : Work.EL.F c z ∉ Work.EL.K c := Work.EL.paramRay_subset_compl d.hN _ hFz
  refine ⟨?_, ?_⟩
  · rw [Work.EL.mem_pairCurve_iff]
    push Not
    refine ⟨?_, ?_, ?_⟩
    · intro h
      obtain ⟨k, hk⟩ := exists_eq_add_int_of_mem_paramRay d.hN hFz h
      exact hFa k hk
    · intro h
      exact hFzK (h ▸ hPK)
    · intro h
      obtain ⟨k, hk⟩ := exists_eq_add_int_of_mem_paramRay d.hN hFz h
      exact hFb k hk
  · exact (mem_pairSide_iff_InArc d.hN P hS hab hφa hφb hz).trans
      (heq.trans (mem_pairSide_iff_InArc d.hN P' hS' hab' hFa hFb hFz).symm)

/-! ## `L4` -/

/-- **`L4`: the side of a pair is read off the angle, locally at a ray point** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L4`; the corrected margin and the full four-case table are in `Submission/Work/SeedSimple2/COP/NOTES_COP.md` §2 — **read that file before starting: the constant `η` in the design note is too weak**).

At a ray point `p` of `R(P.a) ∪ R(P.b)` there is a ball on which `F` maps the far side (resp. the near side) of `P` to the far side (resp. the near side) of `P'`, **and** creates no point of the curve `P'`.

Proof design.  Put `μ := Work.EL.arcLen P.a P.b`, `μ' := Work.EL.arcLen P'.a P'.b`; both lie in `(0,1)` (`μ ≠ 0` because `P.a ≠ P.b` with both in `(0,1)`; `μ' ≠ 0` is `hnd'`; `< 1` is `Work.EL.arcLen_lt_one`).  Take `η > 0` with
`η ≤ min (min μ (1 - μ)) (min (μ' / 1024) ((1 - μ') / 1024)) / 2`.
Unfold `p ∈ Work.EL.paramRay d.hN P.a ∪ Work.EL.paramRay d.hN P.b` as `p = Work.EL.rayPt d.hN e t₀` with `e ∈ {P.a, P.b}`, `t₀ > 1` (`Work.Top.NakaneData.paramRay_eq_range`), and let `δ > 0` be given by `Work.SeedSimple2.COP.extAngle_close_at d he0 he1 hη ht₀` (for `e ∈ (0,1)` use `hPa`/`hPb`).  For `z ∈ Metric.ball p δ` with `z ∉ Work.EL.pairCurve P` put `φ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z` and `σ := φ - e`;  then `|σ| < η`, `z ∈ Work.EL.paramRay d.hN φ` (`Work.Top.mem_paramRay_extAngle`) hence `z = Work.EL.rayPt d.hN φ r` for some `r > 1`, and `Work.EL.F c z = Work.EL.rayPt d.hN ((Work.EL.T^[10]) φ) (r^1024)`, i.e. `Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract (1024 * φ))` (`Work.ELRig.rayPt_iterate`, `Work.ELRig.T_iterate_eq_add_int`, `Work.ELTop.paramRay_add_int`).  The four cases of `NOTES_COP.md` §2 then show
`Work.EL.InArc φ P.a P.b ↔ Work.EL.InArc (Int.fract (1024 * φ)) P'.a P'.b`,
using `Int.fract (Int.fract (1024 * φ) - P'.a) = Int.fract (1024 * σ)` (from `ha'`) and `Work.EL.arcLen P'.a P'.b = Int.fract (1024 * (P.b - P.a))` (from `hb'`).  `Work.EL.F c z ∉ Work.EL.pairCurve P'` holds because `Int.fract (1024 * φ)` is not congruent to `P'.a` or `P'.b` modulo `1` (four cases again) while `Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract (1024 * φ))` and `Work.EL.F c z ∉ Work.EL.K c ∋ d.z₁`.  Finally convert both sides with `Work.SeedSimple2.COP.mem_pairSide_iff_InArc` (`hS`, `hS'`, `hab`, and the non-congruences). -/
theorem local_angle {c : ℂ} (d : Work.EL.RootParabolic c)
    (P P' : Work.EL.CoPair d.hN) (hS : Work.EL.PairSides d.hN P)
    (hS' : Work.EL.PairSides d.hN P')
    (hPa : P.a ∈ Set.Ioo (0:ℝ) 1) (hPb : P.b ∈ Set.Ioo (0:ℝ) 1) (hab : P.a ≠ P.b)
    (ha' : ∃ k : ℤ, P'.a = 1024 * P.a + k) (hb' : ∃ k : ℤ, P'.b = 1024 * P.b + k)
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0)
    {p : ℂ} (hp : p ∈ Work.EL.paramRay d.hN P.a ∪ Work.EL.paramRay d.hN P.b) :
    ∃ δ > 0, ∀ z ∈ Metric.ball p δ, z ∉ Work.EL.pairCurve P →
      Work.EL.F c z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P') := by
  -- the two arc lengths lie in `(0,1)`
  have hμ0 : 0 < Work.EL.arcLen P.a P.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _) (Ne.symm (arcLen_ne_zero_of_mem_Ioo hPa hPb hab))
  have hμ1 : Work.EL.arcLen P.a P.b < 1 := Work.EL.arcLen_lt_one _ _
  have hμ'0 : 0 < Work.EL.arcLen P'.a P'.b :=
    lt_of_le_of_ne (Work.EL.arcLen_nonneg _ _) (Ne.symm hnd')
  have hμ'1 : Work.EL.arcLen P'.a P'.b < 1 := Work.EL.arcLen_lt_one _ _
  -- the margin
  set M : ℝ := min (min (Work.EL.arcLen P.a P.b) (1 - Work.EL.arcLen P.a P.b))
    (min (Work.EL.arcLen P'.a P'.b / 1024) ((1 - Work.EL.arcLen P'.a P'.b) / 1024)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min (lt_min hμ0 (by linarith)) (lt_min (by linarith) (by linarith))
  set η : ℝ := M / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hM1 : M ≤ Work.EL.arcLen P.a P.b := le_trans (min_le_left _ _) (min_le_left _ _)
  have hM2 : M ≤ 1 - Work.EL.arcLen P.a P.b := le_trans (min_le_left _ _) (min_le_right _ _)
  have hM3 : M ≤ Work.EL.arcLen P'.a P'.b / 1024 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hM4 : M ≤ (1 - Work.EL.arcLen P'.a P'.b) / 1024 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hημ : η ≤ Work.EL.arcLen P.a P.b / 2 := by rw [hη]; linarith
  have hη1μ : η ≤ (1 - Work.EL.arcLen P.a P.b) / 2 := by rw [hη]; linarith
  have hημ' : η ≤ Work.EL.arcLen P'.a P'.b / 2048 := by rw [hη]; linarith
  have hη1μ' : η ≤ (1 - Work.EL.arcLen P'.a P'.b) / 2048 := by rw [hη]; linarith
  -- the two angles of the pair `P` are not congruent, and neither are those of `P'`
  have hab_int : ∀ k : ℤ, P.b ≠ P.a + k := by
    intro k hk
    exact hμ0.ne' (by
      rw [Work.EL.arcLen, hk, show P.a + (k : ℝ) - P.a = (k : ℝ) by ring, Int.fract_intCast])
  have hab'_int : ∀ k : ℤ, P'.b ≠ P'.a + k := by
    intro k hk
    exact hnd' (by
      rw [Work.EL.arcLen, hk, show P'.a + (k : ℝ) - P'.a = (k : ℝ) by ring, Int.fract_intCast])
  rcases hp with hp | hp
  · -- `p` lies on the ray of `P.a`
    have hp' : p ∈ Work.Top.NakaneData.paramRay d.hN P.a := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt d.hN P.a t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ := extAngle_close_at d hPa.1 hPa.2 hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt d.hN P.a t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, hzang⟩ := hδ z hzn
    set φ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hφdef
    set σ : ℝ := φ - P.a with hσdef
    have hσabs : |σ| < η := by
      rw [hσdef, hφdef]
      simpa using hzang
    have hφray : z ∈ Work.EL.paramRay d.hN φ := by
      rw [hφdef]
      exact Work.Top.mem_paramRay_extAngle d.hN hzK
    have hφeq : φ = P.a + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφa : φ = P.a := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inl (hφa ▸ hφray))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_a hφeq ha' hb' hσne hσabs hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    exact local_angle_concl d hS hS' hab_int hab'_int hna hnb hFa hFb heq hφray
      (F_mem_paramRay_fract d hφray)
  · -- `p` lies on the ray of `P.b`
    have hp' : p ∈ Work.Top.NakaneData.paramRay d.hN P.b := hp
    rw [Work.Top.NakaneData.paramRay_eq_range] at hp'
    obtain ⟨⟨t₀, ht₀⟩, hpt₀⟩ := hp'
    have hpt₀' : Work.EL.rayPt d.hN P.b t₀ = p := hpt₀
    obtain ⟨δ, hδpos, hδ⟩ := extAngle_close_at d hPb.1 hPb.2 hηpos ht₀
    refine ⟨δ, hδpos, fun z hz hzc => ?_⟩
    have hzn : ‖z - Work.EL.rayPt d.hN P.b t₀‖ < δ := by
      have h1 : dist z p < δ := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at h1
      rwa [← hpt₀'] at h1
    obtain ⟨hzK, hzang⟩ := hδ z hzn
    set φ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hφdef
    set σ : ℝ := φ - P.b with hσdef
    have hσabs : |σ| < η := by
      rw [hσdef, hφdef]
      simpa using hzang
    have hφray : z ∈ Work.EL.paramRay d.hN φ := by
      rw [hφdef]
      exact Work.Top.mem_paramRay_extAngle d.hN hzK
    have hφeq : φ = P.b + σ := by rw [hσdef]; ring
    have hσne : σ ≠ 0 := by
      intro h0
      have hφb : φ = P.b := by rw [hφeq, h0]; ring
      exact hzc (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inr (hφb ▸ hφray)))
    obtain ⟨heq, hna, hnb, hFa, hFb⟩ :=
      angle_correspondence_b hφeq ha' hb' hσne hσabs hμ0 hμ1 hμ'0 hμ'1 hημ hη1μ hημ' hη1μ'
    exact local_angle_concl d hS hS' hab_int hab'_int hna hnb hFa hFb heq hφray
      (F_mem_paramRay_fract d hφray)

end Work.SeedSimple2.COP

end
