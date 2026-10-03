import Mathlib
import Submission.Work.Pert.pert2v2.waist_cover_pinned_im_seg_low
import Submission.Work.Pert.pert2v2.gate_coord_end_asymptotic
import Submission.Work.Pert.Phi_dev_le_on_gate
import Submission.Work.Pert.pert2v2.fatou_proper_im
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_fwd_re
import Submission.Work.Pert.pert2v2.GatePreimageReBound.walk_bwd_re
import Submission.Work.Pert.pert2v2.GatePreimageReBound.exists_mul_exp_neg_le

/-!
# `Work.Pert.pert2v2.GatePreimageReBound.gate_preimage_re_bound`

**The `Re`-confinement of the gate preimage.**  For a Fatou coordinate `Φ` of the lifted
near-translation `F = liftF u σ α` on the lower gate `Qm Ξ α` (near-translation, exponentially
close to `z + 1` high up, `FatouStatement` available), and given the cover hypothesis that every
point of the unit vertical window at height `y ≥ Y` has a gate preimage in the waist of height
`≥ (3y + Ξ)/4`, the chosen gate preimage

`ς = invOn Φ (Qm Ξ α) w`,  `0 ≤ w.re < 1`,  `w.im ≥ Yc`,  `w ∈ Φ '' Qm Ξ α`

has `|ς.re| ≤ B` for constants `B, Yc` depending only on the data.

## The argument

`FatouEnds` (a field of `FatouStatement`, instantiated by
`Work.Pert.pert2v2.gate_coord_end_asymptotic_Qm`) gives a constant `c` with
`Φ z = z + c + o(1)` on vertical windows `|z.re - x| ≤ 2` as `z.im → ∞` — with **one and the same**
`c` for every window `x`.  The only missing ingredient is that this asymptotic is *uniform in the
real part*; this is what the two walks supply:

* if `ς.re ≤ -1`, walk **forward** (`walk_fwd_re`) until the real part reaches `[0,1]`;
* if `ς.re ≥ 1`, walk **backward** (`walk_bwd_re`, using the preimage step `backStep_exists`) until
  the real part reaches `[-1,0]`;
* otherwise `ς` itself already lies in `[-1,1]`.

The walk moves the real part by `≈ 1` per step and shifts `Φ` by the corresponding integer, and
since the *actual* displacement error of a step is the defect `F z - z - 1` — exponentially small
above height `Ydec` — the accumulated displacement error is summable: the walked-to point `z'`
satisfies `z' ∈ Qm Ξ α`, `|z'.re| ≤ 2`, `z'.im ≥ ς.im - 1`, and
`‖(Φ z' - z') - (Φ ς - ς)‖ ≤ 1`.  Because `ς.im ≥ (3 w.im + Ξ)/4`, choosing `Yc` large makes the
thresholds of the walks, of the end asymptotics, and of the decay all hold.  Then

`|Re ς| ≤ |Re w| + |Re(Φ ς - ς - c)| + |Re c| ≤ 1 + 2 + ‖c‖`.

The header hypotheses `hΞ`, `hQAdm`, `hNT`, `hΦ`, `hdec` are exactly those of
`gate_coord_end_asymptotic_Qm`; `hcover` is the design's "pinned cover"
(`Work.Pert.pert2v2.waist_cover_pinned_im_seg_low` produces it at the call site).
-/

namespace Work.Pert.pert2v2.GatePreimageReBound

/-- **Assembly of the `Re`-bound from the two walks.**  This is the mathematical content of
`gate_preimage_re_bound`, with the two walk lemmas of `Pert/pert2v2/GatePreimageReBound/` taken as
hypotheses.  The walk statements are exactly those of `walk_fwd_re` / `walk_bwd_re`. -/
theorem gate_preimage_re_bound_assemble {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdec : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)))
    (hcover : ∃ Y : ℝ, Ξ < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      (3 * y₀ + Ξ) / 4 ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im)
    (hwalkF : ∃ K : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → z.re ≤ -1 → K ≤ z.im →
      ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ ∃ N : ℕ,
        Φ z' = Φ z + (N : ℂ) ∧ z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧ z.im - 1 ≤ z'.im ∧
        ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1)
    (hwalkB : ∃ K : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → 1 ≤ z.re → K ≤ z.im →
      ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ ∃ N : ℕ,
        Φ z' = Φ z - (N : ℂ) ∧ z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧ z.im - 1 ≤ z'.im ∧
        ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1) :
    ∃ B Yc : ℝ, 0 < B ∧ ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re < 1 →
      w ∈ Φ '' (Work.Pert.Qm Ξ α) →
      |(Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).re| ≤ B := by
  -- the upper-end asymptotics of `Φ`, with a single constant `c` for all `Re`-windows
  obtain ⟨c, hc⟩ := Work.Pert.pert2v2.gate_coord_end_asymptotic_Qm hF hΞ hQAdm hNT hΦ hdec
  obtain ⟨Ye, hYe⟩ := hc 0 1 one_pos
  have hYe' : ∀ z ∈ Work.Pert.Qm Ξ α, Ye < z.im → |z.re| ≤ 2 →
      ‖Φ z - z - c‖ < 1 := by
    intro z hz h1 h2
    exact hYe z hz h1 (by simpa using h2)
  -- the cover threshold and the two walk thresholds
  obtain ⟨Yc0, _hYc0Ξ, hcov⟩ := hcover
  obtain ⟨Kf, hKf⟩ := hwalkF
  obtain ⟨Kb, hKb⟩ := hwalkB
  have hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α) := hΦ.2.1
  -- the comparison constant
  set M₀ : ℝ := max Kf (max Kb (Ye + 1)) with hM₀
  have hKfM : Kf ≤ M₀ := by
    rw [hM₀]; exact le_max_left Kf (max Kb (Ye + 1))
  have hKbM : Kb ≤ M₀ := by
    rw [hM₀]
    exact le_trans (le_max_left Kb (Ye + 1)) (le_max_right Kf (max Kb (Ye + 1)))
  have hYeM : Ye + 1 ≤ M₀ := by
    rw [hM₀]
    exact le_trans (le_max_right Kb (Ye + 1)) (le_max_right Kf (max Kb (Ye + 1)))
  refine ⟨‖c‖ + 3, max Yc0 (max (((4 : ℝ) / 3) * M₀ + 1) 1), by positivity, ?_⟩
  intro w hwy hw0 hw1 hwmem
  -- the height thresholds
  have hYc0le : Yc0 ≤ w.im := le_trans (le_max_left _ _) hwy
  have h3 : ((4 : ℝ) / 3) * M₀ + 1 ≤ w.im :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hwy
  -- the chosen gate preimage
  set z : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hzdef
  have hzQ : z ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hwmem
  have hzΦ : Φ z = w := Work.Pert.invOn_spec hwmem
  -- the cover forces the preimage to be high up (it is the *same* point, by injectivity)
  have hcovw := hcov w.im hYc0le w.re ⟨hw0, hw1⟩
  have hz_im : (3 * w.im + Ξ) / 4 ≤ z.im := by
    have h := hcovw.2
    rw [Complex.re_add_im w] at h
    simpa [hzdef] using h
  have hY0 : M₀ ≤ z.im := by linarith [hz_im, hΞ, h3, hYeM]
  -- the walk to a bounded `Re`-window
  have hex : ∃ z' : ℂ, z' ∈ Work.Pert.Qm Ξ α ∧ z'.re ∈ Set.Icc (-2 : ℝ) 2 ∧
      z.im - 1 ≤ z'.im ∧ ‖(Φ z' - z') - (Φ z - z)‖ ≤ 1 := by
    by_cases hF1 : z.re ≤ -1
    · obtain ⟨z', h1, N, -, h2, h3, h4⟩ := hKf z hzQ hF1 (le_trans hKfM hY0)
      exact ⟨z', h1, h2, h3, h4⟩
    · by_cases hB1 : 1 ≤ z.re
      · obtain ⟨z', h1, N, -, h2, h3, h4⟩ := hKb z hzQ hB1 (le_trans hKbM hY0)
        exact ⟨z', h1, h2, h3, h4⟩
      · push_neg at hF1 hB1
        exact ⟨z, hzQ, ⟨by linarith, by linarith⟩, by linarith, by simp⟩
  obtain ⟨z', hz'Q, hz're, hz'im, hErr⟩ := hex
  have hz're2 : |z'.re| ≤ 2 := by
    rw [Set.mem_Icc] at hz're
    exact abs_le.mpr ⟨hz're.1, hz're.2⟩
  have hz'Ye : Ye < z'.im := lt_of_lt_of_le (by linarith [hYeM, hY0]) hz'im
  have hEnd := hYe' z' hz'Q hz'Ye hz're2
  -- the constant `c` transfers from `z'` to `z`
  have hErr' : ‖Φ z - z - (Φ z' - z')‖ ≤ 1 := by
    rw [norm_sub_rev]; exact hErr
  have hid : Φ z - z - c = (Φ z - z - (Φ z' - z')) + (Φ z' - z' - c) := by ring
  have hmain : ‖Φ z - z - c‖ ≤ 2 := by
    rw [hid]
    refine le_trans (norm_add_le _ _) ?_
    linarith [hErr', hEnd]
  have hrec : |(Φ z - z - c).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hmain
  -- conclusion
  have hzre : z.re = w.re - (Φ z - z - c).re - c.re := by
    have h1 : z.re = w.re - (Φ z - z).re := by
      rw [← hzΦ]; simp only [Complex.sub_re]; ring
    have h2 : (Φ z - z).re = (Φ z - z - c).re + c.re := by
      simp only [Complex.sub_re]; ring
    linarith
  calc |z.re| = |w.re - (Φ z - z - c).re - c.re| := by rw [hzre]
    _ ≤ w.re + 2 + ‖c‖ := by
        have hsplit : w.re - (Φ z - z - c).re - c.re
            = w.re + (-((Φ z - z - c).re)) + (-c.re) := by ring
        have h1 : |w.re - (Φ z - z - c).re - c.re|
            ≤ w.re + |(Φ z - z - c).re| + |c.re| := by
          rw [hsplit]
          refine le_trans (abs_add_three _ _ _) ?_
          rw [abs_neg, abs_neg, abs_of_nonneg hw0]
        linarith [h1, hrec, Complex.abs_re_le_norm c]
    _ ≤ ‖c‖ + 3 := by linarith [hw1]

/-- **The `Re`-confinement of the gate preimage** (the requested lemma). -/
theorem gate_preimage_re_bound {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdec : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)))
    (hcover : ∃ Y : ℝ, Ξ < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) ∧
      (3 * y₀ + Ξ) / 4 ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im) :
    ∃ B Yc : ℝ, 0 < B ∧ ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re < 1 →
      w ∈ Φ '' (Work.Pert.Qm Ξ α) →
      |(Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).re| ≤ B := by
  obtain ⟨M, κ, Yd, hM, hκ, hdec'⟩ := hdec
  exact gate_preimage_re_bound_assemble hF hΞ hQAdm hNT hΦ ⟨M, κ, Yd, hM, hκ, hdec'⟩ hcover
    (walk_fwd_re hNT.1 hΦ.2.2 hdec' hM hκ)
    (walk_bwd_re hNT.1 hΦ.2.2 hdec' hM hκ)

end Work.Pert.pert2v2.GatePreimageReBound
