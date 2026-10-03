import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou

/-!
# PERT · `Work.Pert.gate_walk_legal`: a walk of prescribed length inside the lower gate

`Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))` is the lower gate of §4.2, i.e. the intersection of
the cone with vertex `a = Ξ - 1/α` opening to the left and the cone with vertex `b = -Ξ` opening
to the right:

`z ∈ Qm Ξ α ↔ marg₁ z > 0 ∧ marg₂ z > 0`,  `marg₁ w = Re (w - a) + |Im (w - a)|`,
`marg₂ w = |Im (w - b)| - Re (w - b) = |Im w| - Re w - Ξ`.

If `F = liftF u σ α` is a near-translation by `1` on `Qm Ξ α` with error `‖F w - (w+1)‖ ≤ 1/32`,
then, writing `ε w = F w - w - 1` (`‖ε w‖ ≤ 1/32`),

* `marg₁ (F w) ≥ marg₁ w + 1 - 2‖ε w‖ ≥ marg₁ w + 30/32`: the real part gains `1 - ‖ε‖` and the
  modulus of the imaginary part loses at most `‖ε‖`, so the `b₁`-condition can only improve;
* `marg₂ (F w) ≥ marg₂ w - 1 - 2‖ε w‖ ≥ marg₂ w - 17/16`: the real part gains at most `1 + ‖ε‖`
  and the modulus of the imaginary part loses at most `‖ε‖`.

Hence the walk `z, F z, F² z, …` stays in the gate as long as its room to the *upper* boundary
`marg₂` stays positive, and `marg₂ (F^j z) ≥ marg₂ z - (17/16) j ≥ (17/16)(m - j) + 1 > 0` for
`j ≤ m` as soon as `marg₂ z ≥ (17/16) m + 1`.  This is the hypothesis `hroom` of the statement
(note `|z.im| - Ξ - z.re = marg₂ z`).
-/

namespace Work.Pert

set_option linter.unusedSimpArgs false

open MandelDim Complex Set Metric

noncomputable section

/-- The `b₁`-margin of `w` at the vertex `a`: `Re (w - a) + |Im (w - a)|`; its positivity is the
`b₁`-condition of `Qreg`. -/
private def marg1 (a w : ℂ) : ℝ := (w - a).re + |(w - a).im|

/-- The `b₂`-margin of `w` at the vertex `b`: `|Im (w - b)| - Re (w - b)`; its positivity is the
`b₂`-condition of `Qreg`. -/
private def marg2 (b w : ℂ) : ℝ := |(w - b).im| - (w - b).re

/-- One step of a near-translation increases the `b₁`-margin by at least `30/32`. -/
private lemma marg1_step {F : ℂ → ℂ} {w a : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) : marg1 a w + 30 / 32 ≤ marg1 a (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hre : (F w - a).re = (w - a).re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F w - a).im = (w - a).im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : (w - a).re + 1 - ‖ε‖ ≤ (F w - a).re := by
    rw [hre]
    have := (abs_le.mp (Complex.abs_re_le_norm ε)).1
    linarith
  have h2 : |(w - a).im| - ‖ε‖ ≤ |(F w - a).im| := by
    rw [him]
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub (w - a).im (-ε.im)
    rw [abs_neg] at h4
    have h5 : (w - a).im - -ε.im = (w - a).im + ε.im := by ring
    rw [h5] at h4
    linarith
  simp only [marg1]
  linarith

/-- One step of a near-translation decreases the `b₂`-margin by at most `17/16`. -/
private lemma marg2_step {F : ℂ → ℂ} {w b : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) : marg2 b w - 17 / 16 ≤ marg2 b (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hre : (F w - b).re = (w - b).re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F w - b).im = (w - b).im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : ε.re ≤ ‖ε‖ := (abs_le.mp (Complex.abs_re_le_norm ε)).2
  have h2 : |(w - b).im| - ‖ε‖ ≤ |(F w - b).im| := by
    rw [him]
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub (w - b).im (-ε.im)
    rw [abs_neg] at h4
    have h5 : (w - b).im - -ε.im = (w - b).im + ε.im := by ring
    rw [h5] at h4
    linarith
  simp only [marg2]
  linarith

/-- Membership in the lower gate is exactly positivity of the two cone margins. -/
private lemma mem_Qm_iff_margins (Ξ : ℝ) (α z : ℂ) :
    z ∈ Qm Ξ α ↔ 0 < marg1 ((Ξ : ℂ) - 1 / α) z ∧ 0 < marg2 (-(Ξ : ℂ)) z := by
  have hunfold : z ∈ Qm Ξ α ↔
      (-|(z - ((Ξ : ℂ) - 1 / α)).im| < (z - ((Ξ : ℂ) - 1 / α)).re ∧
        (z - (-(Ξ : ℂ))).re < |(z - (-(Ξ : ℂ))).im|) := by
    simp only [Qm, MandelDim.Qreg, Set.mem_ofPred_eq, Option.mem_some_iff]
    constructor
    · intro h; exact ⟨h.1 _ rfl, h.2 _ rfl⟩
    · intro h; exact ⟨fun b hb => by rw [← hb]; exact h.1,
        fun b hb => by rw [← hb]; exact h.2⟩
  rw [hunfold]
  simp only [marg1, marg2]
  constructor
  · intro h; exact ⟨by linarith, by linarith⟩
  · intro h; exact ⟨by linarith, by linarith⟩

/-- The `b₂`-margin at the vertex `-Ξ` is the room `|Im w| - Re w - Ξ` used in the hypothesis. -/
private lemma marg2_neg_eq {Ξ : ℝ} (w : ℂ) : marg2 (-(Ξ : ℂ)) w = |w.im| - w.re - Ξ := by
  simp only [marg2, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- **A walk of prescribed length inside the lower gate.** -/
theorem gate_walk_legal {Ξ : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hΞ : 0 < Ξ)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hroom : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ |z.im| - Ξ - z.re) :
    ∀ j ≤ m, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α := by
  have _ := hΞ
  set F : ℂ → ℂ := liftF u σ α with hF
  have hstep : ∀ w ∈ Qm Ξ α, ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ) := fun w hw => by
    rw [hF]; exact hNT w hw
  have hz' : 0 < marg1 ((Ξ : ℂ) - 1 / α) z ∧ 0 < marg2 (-(Ξ : ℂ)) z :=
    (mem_Qm_iff_margins Ξ α z).mp hz
  have hroom' : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ marg2 (-(Ξ : ℂ)) z := by
    rw [marg2_neg_eq]; linarith
  -- the invariant: membership, positivity of `marg₁`, and the room to the upper boundary
  have key : ∀ j : ℕ, j ≤ m →
      F^[j] z ∈ Qm Ξ α ∧ 0 < marg1 ((Ξ : ℂ) - 1 / α) (F^[j] z) ∧
        (17 / 16 : ℝ) * (m : ℝ) + 1 ≤
          marg2 (-(Ξ : ℂ)) (F^[j] z) + (17 / 16 : ℝ) * (j : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨hz, hz'.1, by simpa using hroom'⟩
    | succ j ih =>
      intro hj
      have hjm : j ≤ m := by omega
      obtain ⟨hmem, hm1, hm2⟩ := ih hjm
      have hε : ‖F (F^[j] z) - (F^[j] z + 1)‖ ≤ (1 / 32 : ℝ) := hstep _ hmem
      have h1 : marg1 ((Ξ : ℂ) - 1 / α) (F^[j] z) + 30 / 32 ≤
          marg1 ((Ξ : ℂ) - 1 / α) (F (F^[j] z)) := marg1_step hε
      have h2 : marg2 (-(Ξ : ℂ)) (F^[j] z) - 17 / 16 ≤ marg2 (-(Ξ : ℂ)) (F (F^[j] z)) :=
        marg2_step hε
      -- the point stays in the gate: `marg₂` is still `≥ 1 > 0`
      have hjle : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ m)
      have hpos : 0 < marg2 (-(Ξ : ℂ)) (F (F^[j] z)) := by
        have h3 : (17 / 16 : ℝ) * ((j : ℝ) + 1) ≤ (17 / 16 : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hjle (by norm_num)
        linarith
      have hmem' : F (F^[j] z) ∈ Qm Ξ α :=
        (mem_Qm_iff_margins Ξ α _).mpr ⟨by linarith, hpos⟩
      rw [Function.iterate_succ_apply']
      exact ⟨hmem', by linarith, by push_cast; linarith⟩
  intro j hj
  have h := (key j hj).1
  rwa [hF] at h

end

end Work.Pert
