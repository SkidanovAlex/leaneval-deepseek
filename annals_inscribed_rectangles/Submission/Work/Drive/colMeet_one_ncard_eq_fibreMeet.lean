import Mathlib
import Submission.Work.Drive.collapseT4defs
import Submission.Work.Drive.diskCut_inner_avoid
import Submission.Work.Drive.dirParam_radParam
import Submission.Work.Drive.polarParam_unique
import Submission.Work.Drive.sqDisk_foldBox_existsUnique

/-!
# T4 of the radial-collapse transport: the fibre sum at `s = 1`

`Work.Drive.colMeet β Q V W 1` is the collapsed meet set at the collapsed end `s = 1` of the radial
collapse (`Submission/Work/Drive/collapseTransport.lean`): the triples `(u, y, z)` of parameters of
the square, the two sweeps, such that

> `colPlane β Q 1 u = V y`  and  `diskPlane Q u = W z`.

`Work.Drive.fibreMeet Q V W` is the fibre-sum form of the same count: the quadruples `(t, σ, y, z)`
with `t` a direction in `[0,1)`, `σ` a signed radius in `[0,1]` and

> `coreLoop Q t = V y`  and  `diamLoop Q t σ = W z`.

The two sets are in bijection, and this is the parabolic identity of the transport
(`Submission/Work/Drive/collapseT4defs.lean`): the box point `u` corresponds to the disk point
`ζ u = sqDisk (foldBox u)`, whose polar coordinates are `(dirParam (ζ u), radParam (ζ u))`
(`Work.Drive.dirParam_radParam`, `Work.Drive.polarParam_unique`); the collar hypothesis
`hβδ : β = √· on [δ², ∞)` makes the collapsed plane at `s = 1` the *normalised* plane there
(`Work.Drive.colMap_one_of_collar`), and the seam hypothesis `hQseam : Q (-z) = Q z` on the circle
identifies the normalised point `±exp (π i t)` with `exp (π i t)`, i.e. `colPlane β Q 1 u` with
`coreLoop Q t`.  The inner part of the disk (of radius `≤ δ`) contributes to neither side: there the
cut `diskCut Q W` avoids the corresponding disk points (`hδcut`), so the condition
`diskPlane Q u = W z` (resp. `diamLoop Q t σ = W z`) is unsatisfiable.  Consequently the bijection is

> `(u, y, z) ↦ (dirParam (ζ u), radParam (ζ u), y, z)`,

with inverse `(t, σ, y, z) ↦ (ζ⁻¹ ((1 - 2σ) exp (π i t)), y, z)`.
-/

namespace Work.Drive

noncomputable section

/-! ## 1. The polar coordinate of a disk point -/

/-- The disk point `(1 - 2σ) · exp (π i t)` attached to the polar pair `(t, σ)`: the point of the
diameter through `exp (π i t)` with signed radius `1 - 2σ`.  `Work.Drive.diamLoop Q t σ` is `Q` of
it. -/
def polPt (t σ : ℝ) : ℂ := (1 - 2 * σ) * Complex.exp (Real.pi * (t : ℂ) * Complex.I)

/-- The diameter loop is `Q` applied to the polar point. -/
lemma diamLoop_eq (Q : ℂ → CappingSpace) (t σ : ℝ) : diamLoop Q t σ = Q (polPt t σ) := rfl

/-- The two ways of writing the polar point (the real-coefficient form of
`Work.Drive.dirParam_radParam`). -/
lemma polPt_ofReal (t σ : ℝ) :
    ((1 - 2 * σ : ℝ) : ℂ) * Complex.exp (Real.pi * (t : ℂ) * Complex.I) = polPt t σ := by
  rw [polPt]; congr 1; apply Complex.ext <;> simp

/-- `polPt` of the polar data of a point of the closed disk is the point itself. -/
lemma polPt_dirParam_radParam (z : ℂ) (hz : ‖z‖ ≤ 1) :
    polPt (dirParam z) (radParam z) = z := by
  rw [← polPt_ofReal]
  exact (dirParam_radParam z hz).2.2

lemma norm_exp_pi_mul_I (t : ℝ) :
    ‖Complex.exp (Real.pi * (t : ℂ) * Complex.I)‖ = 1 := by
  simp only [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

lemma norm_polPt (t σ : ℝ) : ‖polPt t σ‖ = |1 - 2 * σ| := by
  have h : polPt t σ = ((1 - 2 * σ : ℝ) : ℂ) * Complex.exp (Real.pi * (t : ℂ) * Complex.I) :=
    (polPt_ofReal t σ).symm
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_pi_mul_I, mul_one]

lemma norm_cplxOfInv (z : ℂ) : ‖cplxOfInv z‖ = ‖z‖ := by
  have h := norm_cplxOf (cplxOfInv z)
  rw [cplxOf_cplxOfInv] at h
  exact h.symm

lemma norm_ofReal_mul_exp_pi_mul_I (c t : ℝ) :
    ‖((c : ℂ) * Complex.exp (Real.pi * (t : ℂ) * Complex.I))‖ = |c| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_pi_mul_I, mul_one]

lemma inv_mul_self_eq_sign {c : ℝ} (hc : c ≠ 0) : |c|⁻¹ * c = 1 ∨ |c|⁻¹ * c = -1 := by
  rcases lt_trichotomy c 0 with h | h | h
  · right
    rw [abs_of_neg h]; field_simp
  · exact absurd h hc
  · left
    rw [abs_of_pos h]; field_simp

/-! ## 2. The inner part of the disk misses the cut -/

/-- **A disk point that lies on the sweep `W` (over the parameter cube) is outside the collar.**  If
`‖w‖ ≤ 1` and `Q w = W z` with `z` in the parameter cube, then `δ < ‖w‖`: otherwise the point `w`
(read in the parameter plane through `Work.Drive.cplxOfInv`) would be a point of the cut
`Work.Drive.diskCut Q W`, which `hδcut` forbids. -/
lemma norm_gt_delta_of_Q_mem {Q : ℂ → CappingSpace} {W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {δ : ℝ} (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ → x ∉ diskCut Q W)
    {w : ℂ} (hw : ‖w‖ ≤ 1) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.Drive.unitBox 2) (hQw : Q w = W z) : δ < ‖w‖ := by
  by_contra hle
  have hle : ‖w‖ ≤ δ := not_lt.mp hle
  have hx := hδcut (cplxOfInv w) (by rw [norm_cplxOf, norm_cplxOfInv]; exact hle)
  apply hx
  refine ⟨?_, ?_⟩
  · rw [norm_cplxOf, norm_cplxOfInv]; exact hw
  · exact ⟨z, hz, by rw [cplxOf_cplxOfInv]; exact hQw.symm⟩

/-! ## 3. The normalised point of a disk point is the core point -/

/-- **The collapse at `s = 1`, read at a disk point, is the core loop at its direction.**  For a point
`w ≠ 0` of the closed disk the normalised point `‖w‖⁻¹ • w` is `± exp (π i (dirParam w))`, and the
seam hypothesis of the chart identifies `Q (-z)` with `Q z` on the circle. -/
lemma Q_inv_smul_eq_coreLoop {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 0) :
    Q (((‖w‖)⁻¹ : ℝ) • w) = coreLoop Q (dirParam w) := by
  set E : ℂ := Complex.exp (Real.pi * (((dirParam w : ℝ)) : ℂ) * Complex.I) with hE
  set c : ℝ := 1 - 2 * radParam w with hc
  obtain ⟨ht, hσ, hweq⟩ := dirParam_radParam w hw
  have hcE : (c : ℂ) * E = w := by rw [hc, hE]; exact hweq
  have hcne : c ≠ 0 := by
    intro h0
    apply hne
    rw [← hcE, h0]; simp
  have hnorm : ‖w‖ = |c| := by
    rw [← hcE]; exact norm_ofReal_mul_exp_pi_mul_I c (dirParam w)
  have hsmul : ((‖w‖)⁻¹ : ℝ) • w = (↑((‖w‖)⁻¹ * c) : ℂ) * E := by
    rw [Complex.real_smul, ← hcE, ← mul_assoc, ← Complex.ofReal_mul]
  have hs := inv_mul_self_eq_sign hcne
  rw [← hnorm] at hs
  rcases hs with hs | hs
  · rw [hsmul, hs, Complex.ofReal_one, one_mul]; rfl
  · rw [hsmul, hs, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul]
    exact hQseam E (norm_exp_pi_mul_I (dirParam w))

/-! ## 4. The square parameter of a point of the closed disk -/

/-- **The square parameter of a point of the closed disk**: the unique `y` of the unit square with
`sqDisk (foldBox y) = w` (`Work.Drive.sqDisk_foldBox_existsUnique`), and `0` outside the disk. -/
def diskPreimage (w : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  if h : ‖w‖ ≤ 1 then Classical.choose (sqDisk_foldBox_existsUnique w h) else 0

lemma diskPreimage_mem (w : ℂ) (hw : ‖w‖ ≤ 1) :
    diskPreimage w ∈ Submission.Drive.unitBox 1 := by
  have h := Classical.choose_spec (sqDisk_foldBox_existsUnique w hw)
  simpa [diskPreimage, dif_pos hw] using h.1.1

lemma sqDisk_foldBox_diskPreimage (w : ℂ) (hw : ‖w‖ ≤ 1) :
    sqDisk (foldBox (diskPreimage w)) = w := by
  have h := Classical.choose_spec (sqDisk_foldBox_existsUnique w hw)
  simpa [diskPreimage, dif_pos hw] using h.1.2

lemma eq_diskPreimage {w : ℂ} {y : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ ≤ 1)
    (hy : y ∈ Submission.Drive.unitBox 1) (h : sqDisk (foldBox y) = w) :
    y = diskPreimage w := by
  have huniq := (Classical.choose_spec (sqDisk_foldBox_existsUnique w hw)).2
  rw [diskPreimage, dif_pos hw]
  exact huniq y ⟨hy, h⟩

/-! ## 5. The bijection between the collapsed meet at `s = 1` and the fibre meet -/

/-- **The reparametrisation of the collapsed meet set at `s = 1`**: a triple `(u, y, z)` of the
collapsed meet is sent to the quadruple `(dirParam (ζ u), radParam (ζ u), y, z)` of the fibre
meet. -/
def colFibreMap
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ℝ × ℝ × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (dirParam (sqDisk (foldBox p.1)), radParam (sqDisk (foldBox p.1)), p.2.1, p.2.2)

/-- **The reparametrisation lands in the fibre meet.** -/
lemma colFibreMap_mem {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace} {δ : ℝ} (hδ : 0 ≤ δ)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ → x ∉ diskCut Q W)
    {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ colMeet β Q V W 1) : colFibreMap p ∈ fibreMeet Q V W := by
  simp only [colMeet, Set.mem_ofPred_eq] at hp
  obtain ⟨hu, hy, hz, hcol, hdisk⟩ := hp
  have hw1 : ‖sqDisk (foldBox p.1)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
  have hQw : Q (sqDisk (foldBox p.1)) = W p.2.2 := hdisk
  have hout := norm_gt_delta_of_Q_mem hδcut hw1 hz hQw
  have hne : sqDisk (foldBox p.1) ≠ 0 := by
    intro h0; rw [h0] at hout; simp at hout; linarith
  obtain ⟨ht, hσ, -⟩ := dirParam_radParam (sqDisk (foldBox p.1)) hw1
  have hcore : coreLoop Q (dirParam (sqDisk (foldBox p.1))) = V p.2.1 := by
    rw [← Q_inv_smul_eq_coreLoop hQseam hw1 hne,
      ← colMap_one_of_collar hδ hβδ _ (le_of_lt hout)]
    exact hcol
  have hdiam : diamLoop Q (dirParam (sqDisk (foldBox p.1)))
      (radParam (sqDisk (foldBox p.1))) = W p.2.2 := by
    rw [diamLoop_eq, polPt_dirParam_radParam _ hw1]
    exact hQw
  simp only [fibreMeet, Set.mem_ofPred_eq, colFibreMap]
  exact ⟨ht, hσ, hy, hz, hcore, hdiam⟩

/-- **The reparametrisation is onto the fibre meet.** -/
lemma fibreMeet_range {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace} {δ : ℝ} (hδ : 0 ≤ δ)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δ → x ∉ diskCut Q W)
    {q : ℝ × ℝ × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hq : q ∈ fibreMeet Q V W) :
    ∃ p, p ∈ colMeet β Q V W 1 ∧ colFibreMap p = q := by
  simp only [fibreMeet, Set.mem_ofPred_eq] at hq
  obtain ⟨ht, hσ, hy, hz, hcore, hdiam⟩ := hq
  have hw1 : ‖polPt q.1 q.2.1‖ ≤ 1 := by
    rw [norm_polPt, abs_le]; constructor <;> linarith [hσ.1, hσ.2]
  have hQw : Q (polPt q.1 q.2.1) = W q.2.2.2 := hdiam
  have hout := norm_gt_delta_of_Q_mem hδcut hw1 hz hQw
  have hne : polPt q.1 q.2.1 ≠ 0 := by
    intro h0; rw [h0] at hout; simp at hout; linarith
  have hpol := polarParam_unique hne ht hσ (polPt_ofReal q.1 q.2.1)
  have hdpre := sqDisk_foldBox_diskPreimage (polPt q.1 q.2.1) hw1
  refine ⟨(diskPreimage (polPt q.1 q.2.1), q.2.2.1, q.2.2.2), ?_, ?_⟩
  · simp only [colMeet, Set.mem_ofPred_eq]
    refine ⟨diskPreimage_mem _ hw1, hy, hz, ?_, ?_⟩
    · have h1 : colPlane β Q 1 (diskPreimage (polPt q.1 q.2.1))
          = Q (((‖polPt q.1 q.2.1‖)⁻¹ : ℝ) • polPt q.1 q.2.1) := by
        show Q (colMap β 1 (sqDisk (foldBox (diskPreimage (polPt q.1 q.2.1))))) = _
        rw [hdpre, colMap_one_of_collar hδ hβδ _ (le_of_lt hout)]
      rw [h1, Q_inv_smul_eq_coreLoop hQseam hw1 hne, ← hpol.1]
      exact hcore
    · show Q (sqDisk (foldBox (diskPreimage (polPt q.1 q.2.1)))) = W q.2.2.2
      rw [hdpre]
      exact hQw
  · simp only [colFibreMap, hdpre, ← hpol.1, ← hpol.2]

/-- **The reparametrisation is injective on the collapsed meet set.** -/
lemma colFibreMap_injOn {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {p p' : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ colMeet β Q V W 1) (hp' : p' ∈ colMeet β Q V W 1)
    (h : colFibreMap p = colFibreMap p') : p = p' := by
  simp only [colMeet, Set.mem_ofPred_eq] at hp hp'
  obtain ⟨hu, hy, hz, hcol, hdisk⟩ := hp
  obtain ⟨hu', hy', hz', hcol', hdisk'⟩ := hp'
  simp only [colFibreMap, Prod.mk.injEq] at h
  obtain ⟨ht, hσ, hyy, hzz⟩ := h
  have hw1 : ‖sqDisk (foldBox p.1)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
  have hw1' : ‖sqDisk (foldBox p'.1)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
  have hpw : sqDisk (foldBox p'.1) = sqDisk (foldBox p.1) := by
    rw [← polPt_dirParam_radParam (sqDisk (foldBox p'.1)) hw1',
      ← polPt_dirParam_radParam (sqDisk (foldBox p.1)) hw1, ← ht, ← hσ]
  have h1 : p'.1 = p.1 :=
    (eq_diskPreimage hw1 hu' hpw).trans (eq_diskPreimage hw1 hu rfl).symm
  exact Prod.ext h1.symm (Prod.ext hyy hzz)

/-- **T4 of the radial-collapse transport: the fibre sum at `s = 1`.**  With a collar radius `δ`
small enough that the disk of radius `δ` misses the cut of `Q` by `W` (`hδcut`), the collapsed meet
count at `s = 1` is the fibre meet count: a box point `u` corresponds to the polar pair of
`ζ u = sqDisk (foldBox u)`, at which the collapsed plane is the core loop, and the plane itself is
the diameter. -/
theorem colMeet_one_ncard_eq_fibreMeet (β : ℝ → ℝ) (Q : ℂ → Work.Drive.CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hβδ : ∀ t : ℝ, δ ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖Work.Drive.cplxOf x‖ ≤ δ → x ∉ Work.Drive.diskCut Q W) :
    (Work.Drive.colMeet β Q V W 1).ncard = (Work.Drive.fibreMeet Q V W).ncard :=
  Set.ncard_congr (fun p _ => colFibreMap p)
    (fun p hp => colFibreMap_mem hδ hQseam hβδ hδcut hp)
    (fun p p' hp hp' h => colFibreMap_injOn hp hp' h)
    (fun q hq => by
      obtain ⟨p, hp, hpq⟩ := fibreMeet_range hδ hQseam hβδ hδcut hq
      exact ⟨p, hp, hpq⟩)

end

end Work.Drive
