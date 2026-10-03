import Mathlib
import Submission.Work.Pert.pert2v2.GatePreimageReBound.gate_preimage_re_bound
import Submission.Work.Pert.pert2v2.gate_coord_end_asymptotic

namespace Work.Pert.pert2v2

/-- **Uniformity of the upper-end asymptotic over a bounded real window.**  If `Φ z = z + c + o(1)`
on `Q` in every window `|z.re - x| ≤ 2` (`x` fixed, height threshold depending on `x`), then the
same holds with one single height threshold for all points of `Q` with `|z.re| ≤ B`.

The proof covers `[-B, B]` by the finitely many windows centred at `x_j = -B + 2j`
(`j < ⌈B⌉₊ + 2`): a point with `|Re z| ≤ B` has `Re z ∈ [-B, B]`, so the index
`j = ⌈(Re z + B)/2⌉₊` satisfies `j < ⌈B⌉₊ + 2` and `|Re z - x_j| ≤ 2`; taking the maximum of the
finitely many thresholds `Y'(x_j)` gives the uniform one. -/
theorem exists_threshold_re_bounded {Q : Set ℂ} {Φ : ℂ → ℂ} {c : ℂ} {B : ℝ}
    (hc : ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Q, Y' < z.im → |z.re - x| ≤ 2 →
      ‖Φ z - z - c‖ < ε) :
    ∃ Ye : ℝ, ∀ z ∈ Q, Ye < z.im → |z.re| ≤ B → ‖Φ z - z - c‖ < 1 := by
  classical
  set m : ℕ := Nat.ceil B + 2 with hmdef
  have hmne : (Finset.range m).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by rw [hmdef]; omega)⟩
  refine ⟨(Finset.range m).sup' hmne
    (fun j : ℕ => Classical.choose (hc (-B + 2 * (j : ℝ)) 1 one_pos)), ?_⟩
  intro z hz hYe hzre
  -- the index of the window containing `Re z`
  set j : ℕ := Nat.ceil ((z.re + B) / 2) with hjdef
  have hjeq : ((j : ℕ) : ℝ) = ((Nat.ceil ((z.re + B) / 2) : ℕ) : ℝ) := by rw [hjdef]
  have hzlow : -B ≤ z.re := (abs_le.mp hzre).1
  have hzup : z.re ≤ B := (abs_le.mp hzre).2
  have hhalf : (0 : ℝ) ≤ (z.re + B) / 2 := by linarith
  have hj_ub : (j : ℝ) < B + 1 := by
    have h1 : ((Nat.ceil ((z.re + B) / 2) : ℕ) : ℝ) < (z.re + B) / 2 + 1 :=
      Nat.ceil_lt_add_one hhalf
    have h2 : (z.re + B) / 2 + 1 ≤ B + 1 := by linarith
    rw [hjeq]; linarith
  have hj_mem : j ∈ Finset.range m := by
    rw [Finset.mem_range, hmdef]
    have h3 : B + 1 ≤ ((Nat.ceil B : ℕ) : ℝ) + 2 := by
      have := Nat.le_ceil B
      linarith
    have h4 : (j : ℝ) < ((Nat.ceil B : ℕ) : ℝ) + 2 := lt_of_lt_of_le hj_ub h3
    exact_mod_cast h4
  have hj_win : |z.re - (-B + 2 * (j : ℝ))| ≤ 2 := by
    have h1 : (z.re + B) / 2 ≤ (j : ℝ) := by
      rw [hjeq]; exact Nat.le_ceil _
    have h2 : (j : ℝ) < (z.re + B) / 2 + 1 := by
      rw [hjeq]; exact Nat.ceil_lt_add_one hhalf
    have h3 : z.re + B ≤ 2 * (j : ℝ) := by linarith
    have h4 : 2 * (j : ℝ) < z.re + B + 2 := by linarith
    have h5 : |2 * (j : ℝ) - (z.re + B)| < 2 := by
      rw [abs_lt]; constructor <;> linarith
    have he : z.re - (-B + 2 * (j : ℝ)) = -(2 * (j : ℝ) - (z.re + B)) := by ring
    rw [he, abs_neg]
    exact le_of_lt h5
  have hle : Classical.choose (hc (-B + 2 * (j : ℝ)) 1 one_pos) ≤
      (Finset.range m).sup' hmne
        (fun j : ℕ => Classical.choose (hc (-B + 2 * (j : ℝ)) 1 one_pos)) :=
    Finset.le_sup' (fun j : ℕ => Classical.choose (hc (-B + 2 * (j : ℝ)) 1 one_pos))
      hj_mem
  have hspec := Classical.choose_spec (hc (-B + 2 * (j : ℝ)) 1 one_pos)
  exact hspec z hz (lt_of_le_of_lt hle hYe) hj_win

/-- The height localisation of the gate preimage: the preimage under a gate coordinate
`Φ` of a point of the window `[0,1) × [Y,∞)` has imaginary part `≥ w.im - C`, for a constant `C`
that does not depend on the height.

This is the `Im`-companion of `Work.Pert.pert2v2.GatePreimageReBound.gate_preimage_re_bound`
(same hypotheses, same proof template: the forward/backward walk steps of
`GatePreimageReBound/walk_fwd_re.lean`, `walk_bwd_re.lean`, whose conclusion `z.im - 1 ≤ z'.im`
is already the imaginary-part ingredient, together with `gate_coord_end_asymptotic_Qm`).

**Proof actually formalised here** (the walk is not needed in this direction).  Let
`ς = invOn Φ (Qm Ξ α) w`, so `Φ ς = w`.  The companion `Re`-bound
`gate_preimage_re_bound` (already on disk, sorry-free) gives `|ς.re| ≤ B`; hence ς lies in the fixed
real window `|Re| ≤ B`, and the uniformisation `exists_threshold_re_bounded` of the upper-end
asymptotic `Φ z = z + c + o(1)` (one single height threshold for the whole window, obtained from
`gate_coord_end_asymptotic_Qm`) gives `‖Φ ς - ς - c‖ < 1` as soon as `ς.im` exceeds that threshold.
The cover `hcover` supplies exactly the height: `ς.im ≥ (3 w.im + Ξ)/4`, which is large for large
`w.im`.  Then `|w.im - ς.im - c.im| ≤ ‖Φ ς - ς - c‖ < 1`, i.e. `w.im < ς.im + c.im + 1`, and
`C = max 0 (c.im + 1)` does the job. -/
theorem gate_preimage_im_bound {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
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
    ∃ C Yc : ℝ, 0 ≤ C ∧ ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re < 1 →
      w ∈ Φ '' (Work.Pert.Qm Ξ α) →
      w.im - C ≤ (Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w).im := by
  -- the `Re`-companion: the gate preimage has bounded real part
  obtain ⟨B, YcB, _hBpos, hReB⟩ :=
    Work.Pert.pert2v2.GatePreimageReBound.gate_preimage_re_bound hF hΞ hQAdm hNT hΦ hdec hcover
  -- the upper-end asymptotics of `Φ`, uniformised over the real window `|Re| ≤ B`
  obtain ⟨c, hc⟩ := Work.Pert.pert2v2.gate_coord_end_asymptotic_Qm hF hΞ hQAdm hNT hΦ hdec
  obtain ⟨Ye, hYe⟩ :=
    exists_threshold_re_bounded (Q := Work.Pert.Qm Ξ α) (Φ := Φ) (c := c) (B := B) hc
  -- the cover threshold
  obtain ⟨Ycov, _hYcovΞ, hcov⟩ := hcover
  refine ⟨max 0 (c.im + 1),
    max YcB (max Ycov (max ((4 * (Ye + 1) - Ξ) / 3) 0)), le_max_left 0 _, ?_⟩
  intro w hwy hw0 hw1 hwmem
  have hsplit := hwy
  simp only [max_le_iff] at hsplit
  have hYcB : YcB ≤ w.im := hsplit.1
  have hYcov : Ycov ≤ w.im := hsplit.2.1
  have hYem : (4 * (Ye + 1) - Ξ) / 3 ≤ w.im := hsplit.2.2.1
  -- the chosen gate preimage
  set z : ℂ := Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w with hzdef
  have hzQ : z ∈ Work.Pert.Qm Ξ α := Work.Pert.invOn_mem hwmem
  have hzΦ : Φ z = w := Work.Pert.invOn_spec hwmem
  -- its real part is bounded (the `Re`-companion), its height is large (the cover)
  have hzre : |z.re| ≤ B := hReB w hYcB hw0 hw1 hwmem
  have hcovw := hcov w.im hYcov w.re ⟨hw0, hw1⟩
  have hz_im : (3 * w.im + Ξ) / 4 ≤ z.im := by
    have h := hcovw.2
    rw [Complex.re_add_im w] at h
    simpa [hzdef] using h
  have hYlt : Ye < z.im := by linarith
  -- the asymptotic at the preimage itself
  have hAsym : ‖Φ z - z - c‖ < 1 := hYe z hzQ hYlt hzre
  have hfin : w.im - (c.im + 1) < z.im := by
    have h := Complex.abs_im_le_norm (Φ z - z - c)
    have h2 : |(Φ z - z - c).im| < 1 := lt_of_le_of_lt h hAsym
    have him : (Φ z - z - c).im = w.im - z.im - c.im := by
      simp only [Complex.sub_im, hzΦ]
    rw [him] at h2
    have h3 := (abs_lt.mp h2).2
    linarith
  calc w.im - max 0 (c.im + 1) ≤ w.im - (c.im + 1) := by
        linarith [le_max_right (0 : ℝ) (c.im + 1)]
    _ ≤ z.im := le_of_lt hfin

end Work.Pert.pert2v2
