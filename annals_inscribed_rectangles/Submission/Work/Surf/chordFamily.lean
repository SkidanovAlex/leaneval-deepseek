import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.Surf.Model

/-!
# The straightening family of a chord, and the `(SURF)` difference map

The proof of the mod-2 intersection form of `ℝP²` (`Submission/Work/Drive/SURF_PLAN.md`, the file
`Submission/Work/Surf/chord_parity.lean`) deforms a chord `a : ℝ → ℝ²` to the *diameter* through its
own endpoints.  Because the diameter `s ↦ cos (π s) • a 0` has the same endpoints `a 0`, `-a 0` as the
chord, the convex combination

`chordHom a a 0 τ s = (1 - τ) • a s + τ • (cos (π s) • a 0)`

is again a chord for every `τ ∈ [0,1]`, with *fixed endpoints*: `chordHom a a 0 τ 0 = a 0` and
`chordHom a a 0 τ 1 = -a 0`.  This is the family used in the proof: its `τ = 0` member is the chord
`a`, its `τ = 1` member is the diameter through `a 0`, and — crucially — the two faces `s = 0`, `s = 1`
of the family are *constant*, so the corresponding faces of the cube carry no zeros of the difference
map below.

`chordDiff a b` is the difference map of the family against a second chord `b`, on the cube `[0,1]³`
with coordinates `(τ, s, t)`; it is the map to which `Submission.Drive.ParityProp` (proved as
`Work.Drive.boxParity`) is applied, and whose two `τ`-faces are the intersections of `a` resp. of the
diameter through `a 0` with `b`.
-/

namespace Work.Surf

open Submission.Drive
open scoped Topology

noncomputable section

/-- The straight-line homotopy from the curve `a` to the diameter `s ↦ cos (π s) • z` through the
origin: `chordHom a z τ s = (1 - τ) • a s + τ • (cos (π s) • z)`. -/
def chordHom (a : ℝ → EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 2)) (τ s : ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 - τ) • a s + τ • (Real.cos (Real.pi * s) • z)

@[simp] lemma chordHom_zero (a : ℝ → EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 2))
    (s : ℝ) : chordHom a z 0 s = a s := by
  simp [chordHom]

@[simp] lemma chordHom_one (a : ℝ → EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 2))
    (s : ℝ) : chordHom a z 1 s = Real.cos (Real.pi * s) • z := by
  simp [chordHom]

lemma chordHom_at_zero (a : ℝ → EuclideanSpace ℝ (Fin 2)) (τ : ℝ) :
    chordHom a (a 0) τ 0 = a 0 := by
  simp only [chordHom, mul_zero, Real.cos_zero, one_smul]
  rw [← add_smul, sub_add_cancel, one_smul]

lemma chordHom_at_one (a : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : Work.Drive.IsChord a) (τ : ℝ) :
    chordHom a (a 0) τ 1 = -a 0 := by
  have h1 : a 1 = -a 0 := by simpa using ha.periodic 0
  have h2 : Real.cos (Real.pi * 1) = -1 := by simp
  simp only [chordHom, h1, h2]
  rw [neg_one_smul, smul_neg, smul_neg, ← neg_add, ← add_smul, sub_add_cancel, one_smul]

/-- The difference map of the straightening family of the chord `a` (towards the diameter through
`a 0`) against the chord `b`, on the cube `[0,1]³` with coordinates `(τ, s, t)`:
`chordDiff a b (τ, s, t) = chordHom a (a 0) τ s - b t`. -/
def chordDiff (a b : ℝ → EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.Amb 2 → Work.Drive.Tgt 2 :=
  fun x => chordHom a (a 0) (x 0) (x 1) - b (x 2)

@[simp] lemma chordDiff_apply (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (x : Work.Drive.Amb 2) :
    chordDiff a b x = (1 - x 0) • a (x 1) + (x 0) • (Real.cos (Real.pi * x 1) • a 0) - b (x 2) :=
  rfl

lemma chordDiff_eq (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (x : Work.Drive.Amb 2) :
    chordDiff a b x = chordHom a (a 0) (x 0) (x 1) - b (x 2) := rfl

/-- Every member of the family lies in the closed unit disk. -/
lemma norm_chordHom_le {a : ℝ → EuclideanSpace ℝ (Fin 2)} {z : EuclideanSpace ℝ (Fin 2)}
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hz : ‖z‖ ≤ 1) (ha : ‖a s‖ ≤ 1) :
    ‖chordHom a z τ s‖ ≤ 1 := by
  rw [chordHom]
  have h1 : ‖(1 - τ) • a s‖ ≤ 1 - τ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2] : (0 : ℝ) ≤ 1 - τ)]
    calc (1 - τ) * ‖a s‖ ≤ (1 - τ) * 1 :=
          mul_le_mul_of_nonneg_left ha (by linarith [hτ.2] : (0 : ℝ) ≤ 1 - τ)
      _ = 1 - τ := by ring
  have h2 : ‖τ • (Real.cos (Real.pi * s) • z)‖ ≤ τ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    have hc : |Real.cos (Real.pi * s)| ≤ 1 := Real.abs_cos_le_one _
    have hmul : |Real.cos (Real.pi * s)| * ‖z‖ ≤ 1 := by
      calc |Real.cos (Real.pi * s)| * ‖z‖ ≤ 1 * 1 :=
            mul_le_mul hc hz (norm_nonneg _) zero_le_one
        _ = 1 := by ring
    calc τ * (|Real.cos (Real.pi * s)| * ‖z‖) ≤ τ * 1 :=
          mul_le_mul_of_nonneg_left hmul hτ.1
      _ = τ := by ring
  calc ‖(1 - τ) • a s + τ • (Real.cos (Real.pi * s) • z)‖
      ≤ ‖(1 - τ) • a s‖ + ‖τ • (Real.cos (Real.pi * s) • z)‖ := norm_add_le _ _
    _ ≤ (1 - τ) + τ := add_le_add h1 h2
    _ = 1 := by ring

/-- **The two `s`-faces of the cube carry no zeros**: on them the family is constant (`= a 0` or
`= -a 0 = a 1`), and `hint` forbids an intersection of the chords there. -/
lemma chordDiff_ne_zero_of_sface (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1)
    {x : Work.Drive.Amb 2} (hx : x ∈ Submission.Drive.unitBox 2)
    (h1 : x 1 = 0 ∨ x 1 = 1) : chordDiff a b x ≠ 0 := by
  intro h0
  have hx1 : x 1 ∈ Set.Icc (0 : ℝ) 1 := hx 1
  have hx2 : x 2 ∈ Set.Icc (0 : ℝ) 1 := hx 2
  have heq : a (x 1) = b (x 2) := by
    have h := h0
    rw [chordDiff_eq] at h
    have hch : chordHom a (a 0) (x 0) (x 1) = a (x 1) := by
      rcases h1 with h1 | h1
      · rw [h1]; exact chordHom_at_zero a (x 0)
      · rw [h1, chordHom_at_one a ha]
        have hp : a 1 = -a 0 := by simpa using ha.periodic 0
        rw [← hp]
    rw [hch] at h
    exact sub_eq_zero.mp h
  have hmem := (hint (x 1) (x 2) hx1 hx2 heq).1
  rcases h1 with h1 | h1
  · rw [h1] at hmem
    exact absurd hmem.1 (by norm_num)
  · rw [h1] at hmem
    exact absurd hmem.2 (by norm_num)

/-- A point of the unit circle which is a convex combination with strictly positive weights of two
points of the closed unit disk coincides with both of them. -/
lemma eq_of_combo_norm_eq_one {u v w : EuclideanSpace ℝ (Fin 2)} {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hw : (1 - τ) • u + τ • v = w) (hwn : ‖w‖ = 1) : u = v := by
  have hτ0' : (0 : ℝ) < 1 - τ := by linarith
  have hu1 : ‖u‖ = 1 := by
    have hle : ‖(1 - τ) • u‖ ≤ 1 - τ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0']
      calc (1 - τ) * ‖u‖ ≤ (1 - τ) * 1 := mul_le_mul_of_nonneg_left hu hτ0'.le
        _ = 1 - τ := by ring
    have hge : 1 - τ ≤ ‖(1 - τ) • u‖ := by
      have hsub : (1 - τ) • u = w - τ • v := by
        rw [← hw]; module
      rw [hsub]
      calc ‖w - τ • v‖ ≥ |‖w‖ - ‖τ • v‖| := abs_norm_sub_norm_le w (τ • v)
        _ ≥ ‖w‖ - ‖τ • v‖ := le_abs_self _
        _ = 1 - τ * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, hwn]
        _ ≥ 1 - τ := by
            have : τ * ‖v‖ ≤ τ * 1 := mul_le_mul_of_nonneg_left hv hτ0.le
            linarith
    have heq : ‖(1 - τ) • u‖ = 1 - τ := le_antisymm hle hge
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0'] at heq
    have hne : (1 - τ) ≠ 0 := ne_of_gt hτ0'
    have : ‖u‖ * (1 - τ) = 1 * (1 - τ) := by linarith
    exact mul_right_cancel₀ hne this
  have hv1 : ‖v‖ = 1 := by
    have hle : ‖τ • v‖ ≤ τ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
      calc τ * ‖v‖ ≤ τ * 1 := mul_le_mul_of_nonneg_left hv hτ0.le
        _ = τ := by ring
    have hge : τ ≤ ‖τ • v‖ := by
      have hsub : τ • v = w - (1 - τ) • u := by
        rw [← hw]; module
      rw [hsub]
      calc ‖w - (1 - τ) • u‖ ≥ |‖w‖ - ‖(1 - τ) • u‖| := abs_norm_sub_norm_le w ((1 - τ) • u)
        _ ≥ ‖w‖ - ‖(1 - τ) • u‖ := le_abs_self _
        _ = 1 - (1 - τ) * ‖u‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0', hwn]
        _ ≥ 1 - (1 - τ) := by
            have : (1 - τ) * ‖u‖ ≤ (1 - τ) * 1 := mul_le_mul_of_nonneg_left hu hτ0'.le
            linarith
        _ = τ := by ring
    have heq : ‖τ • v‖ = τ := le_antisymm hle hge
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0] at heq
    have hne : τ ≠ 0 := ne_of_gt hτ0
    have : ‖v‖ * τ = 1 * τ := by linarith
    exact mul_right_cancel₀ hne this
  have htri : ‖(1 - τ) • u + τ • v‖ = ‖(1 - τ) • u‖ + ‖τ • v‖ := by
    rw [hw, hwn, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hτ0', abs_of_pos hτ0, hu1, hv1]
    ring
  have hsr := norm_add_eq_iff_real.mp htri
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, hv1, mul_one,
    norm_smul, Real.norm_eq_abs, abs_of_pos hτ0', hu1, mul_one] at hsr
  rw [smul_smul, smul_smul, mul_comm (1 - τ) τ] at hsr
  have hc : τ * (1 - τ) ≠ 0 := by positivity
  have h2 := congrArg (fun z => (τ * (1 - τ))⁻¹ • z) hsr
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h2

/-- **The two `t`-faces of the cube carry no zeros.**  There the family member is a convex combination
of the point `a (x 1)` of the disk and the point `cos (π (x 1)) • a 0` of the disk, and a zero would put
it on the unit circle; the extreme-point property of the disk then forces both to be the common value,
which is `b (x 2) ∈ ∂D̄`, and `hint` forbids that. -/
lemma chordDiff_ne_zero_of_tface (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1)
    {x : Work.Drive.Amb 2} (hx : x ∈ Submission.Drive.unitBox 2)
    (h2 : x 2 = 0 ∨ x 2 = 1) : chordDiff a b x ≠ 0 := by
  intro h0
  have hx0 : x 0 ∈ Set.Icc (0 : ℝ) 1 := hx 0
  have hx1 : x 1 ∈ Set.Icc (0 : ℝ) 1 := hx 1
  have hx2 : x 2 ∈ Set.Icc (0 : ℝ) 1 := hx 2
  have hch : chordHom a (a 0) (x 0) (x 1) = b (x 2) := by
    have h := h0
    rw [chordDiff_eq] at h
    exact sub_eq_zero.mp h
  have hb2 : ‖b (x 2)‖ = 1 := by
    rcases h2 with h2 | h2
    · rw [h2]; exact hb.start
    · rw [h2]; exact hb.end
  have ha1 : ‖a (x 1)‖ ≤ 1 := ha.mem_disk (x 1) hx1
  have ha0 : ‖a 0‖ = 1 := ha.start
  have hv1 : ‖Real.cos (Real.pi * x 1) • a 0‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, ha0, mul_one]
    exact Real.abs_cos_le_one _
  have ha1' : a 1 = -a 0 := by simpa using ha.periodic 0
  have heq : a (x 1) = b (x 2) := by
    rcases eq_or_lt_of_le hx0.1 with hz | hz
    · rw [← hz, chordHom_zero] at hch
      exact hch
    · rcases eq_or_lt_of_le hx0.2 with ho | ho
      · -- the case `x 0 = 1`: the zero is on the diameter, hence `cos (π x 1) = ± 1`
        rw [ho, chordHom_one] at hch
        have hnorm : |Real.cos (Real.pi * x 1)| = 1 := by
          have := congrArg Norm.norm hch
          rw [norm_smul, Real.norm_eq_abs, ha0, mul_one, hb2] at this
          exact this
        have hx1' : x 1 = 0 ∨ x 1 = 1 := by
          by_contra hcon
          rw [not_or] at hcon
          have hpi0 : 0 < Real.pi * x 1 := by
            have := lt_of_le_of_ne hx1.1 (Ne.symm hcon.1)
            nlinarith [Real.pi_pos]
          have hpipi : Real.pi * x 1 < Real.pi := by
            have := lt_of_le_of_ne hx1.2 hcon.2
            nlinarith [Real.pi_pos]
          have hlt := Real.strictAntiOn_cos
            (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_refl _, Real.pi_pos.le⟩)
            (show Real.pi * x 1 ∈ Set.Icc 0 Real.pi from ⟨hpi0.le, hpipi.le⟩) hpi0
          have hlt2 := Real.strictAntiOn_cos
            (show Real.pi * x 1 ∈ Set.Icc 0 Real.pi from ⟨hpi0.le, hpipi.le⟩)
            (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le, le_refl _⟩) hpipi
          rw [Real.cos_zero] at hlt
          rw [Real.cos_pi] at hlt2
          have habs : |Real.cos (Real.pi * x 1)| < 1 := abs_lt.mpr ⟨hlt2, hlt⟩
          linarith
        rcases hx1' with h1 | h1
        · rw [h1, mul_zero, Real.cos_zero, one_smul] at hch
          rw [h1]; exact hch
        · rw [h1, mul_one, Real.cos_pi, neg_one_smul, ← ha1'] at hch
          rw [h1]; exact hch
      · -- the interior case `0 < x 0 < 1`: the extreme-point argument
        have hw : (1 - x 0) • a (x 1) + (x 0) • (Real.cos (Real.pi * x 1) • a 0) = b (x 2) := hch
        have hcombo := eq_of_combo_norm_eq_one hz ho ha1 hv1 hw hb2
        rw [hcombo] at hw
        have hch2 : Real.cos (Real.pi * x 1) • a 0 = b (x 2) := by
          simpa only [← add_smul, sub_add_cancel, one_smul] using hw
        exact hcombo.trans hch2
  have hmem := (hint (x 1) (x 2) hx1 hx2 heq).2
  rcases h2 with h2 | h2
  · rw [h2] at hmem
    exact absurd hmem.1 (by norm_num)
  · rw [h2] at hmem
    exact absurd hmem.2 (by norm_num)

/-- The derivative of a member of the family. -/
lemma deriv_chordHom {a : ℝ → EuclideanSpace ℝ (Fin 2)} {z : EuclideanSpace ℝ (Fin 2)}
    (ha : ContDiff ℝ 1 a) (τ s : ℝ) :
    deriv (fun u : ℝ => chordHom a z τ u) s =
      (1 - τ) • deriv a s - τ • ((Real.pi * Real.sin (Real.pi * s)) • z) := by
  have hd : HasDerivAt a (deriv a s) s :=
    ((ha.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (Real.pi * u))
      (-Real.pi * Real.sin (Real.pi * s)) s := by
    have h1 : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi s := by
      simpa using (hasDerivAt_id s).const_mul Real.pi
    have h2 := (Real.hasDerivAt_cos (Real.pi * s)).comp s h1
    have h3 : (-Real.sin (Real.pi * s)) * Real.pi = -Real.pi * Real.sin (Real.pi * s) := by ring
    simpa only [Function.comp_def, h3] using h2
  have h : HasDerivAt (fun u : ℝ => chordHom a z τ u)
      ((1 - τ) • deriv a s + τ • ((-Real.pi * Real.sin (Real.pi * s)) • z)) s := by
    have hthis := (hd.const_smul (1 - τ)).add ((hcos.smul_const z).const_smul τ)
    refine hthis.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext u
    rfl
  rw [h.deriv,
    show (-Real.pi * Real.sin (Real.pi * s)) = -(Real.pi * Real.sin (Real.pi * s)) by ring,
    neg_smul, smul_neg]
  abel

end

end Work.Surf
