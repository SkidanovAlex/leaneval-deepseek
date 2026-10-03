import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.pert2v2.EfChain
import Submission.Work.Pert.pert2v2.equiv_transport
import Submission.Work.Pert.tools
import Submission.Work.Repel.end_bound_piExp

/-!
# `Work.Pert.pert2v2.HsegRow` — the (A.4.4) segment estimate from the pinned gate coordinates

`pert2v2.end_const_le_seg` (the paper's (A.4.4)) needs one segment estimate: for the segment
`{x + i y₀}` at a height `y₀ > d.η₀` and the floor-based extended horn map
`Ef = EfFloor Φm Φp (Qm Ξ' α)`,

  `hseg : ∀ x : ℝ, ‖Ef (x + i y₀) - d.E (x + i y₀)‖ < δ / 2`.

This file reduces `hseg` to the design's **pinned** data, with no near-zero asymptotics of `d.Φ`
and no shadowing statement:

* the cover at the segment (`waist_cover_seg_zero`-type) supplies, for every `x ∈ [0,1)`, a gate
  point `ς ∈ Qm Ξ' α` with `Φm ς = x + i y₀`; since `Re (x + i y₀) = x ∈ [0,1)`, the canonical
  representative is `Φm ς` itself, so `Ef (Φm ς) = Φp ς` (`EfChain.EfFloor_level_of_re_mem`);
* the crux's **pin** `‖Φp ζ - d.Φ (τ₀ ζ)‖ < εp` on a compact `Kp` is evaluated at
  `ζ = Xc d (x + i y₀)` — *not* at `ς` — where it reads `‖Φp (Xc d w) - d.E w‖ < εp`
  (because `τ₀ (Xc d w) = d.φ w`), and at `ς` where it is transferred to `Xc d w` by the
  gate Lipschitz bound (`gate_fatou_lipschitz`) and the modulus of injectivity
  (`FatouModulus3.norm_sub_le_mul_of_fatou`);
* the integer shifts of `Ef` (`EfChain.EfFloor_add_int_of_per`) and of `d.E`
  (`E_add_int_band`) transport the estimate from `[0,1)` to all of `ℝ`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- `τ₀` undoes the datum's curve: `τ₀ (Xc d u) = d.φ u` (local copy, to avoid importing the
module `pert2v2.XcV2_deriv_bound`, whose import closure contains an unrelated `sorry`). -/
theorem tau0_Xc' {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (u : ℂ) :
    MandelDim.tau0 (Work.Pert.Xc d u) = d.φ u := by
  simp only [Work.Pert.Xc, Work.Pert.tau0_tau0]

/-- **The `ℤ`-shift of `d.E` on a band.**  For `y₀ > d.η₀`, `d.E (u + k) = d.E u + k` on the band
`{y₀ ≤ |Im·|}`.  This is `Work.Repel.E_add_one` transported along the integer walk
(`pert2v2.E_add_int` at the `T`-invariant band). -/
theorem E_add_int_band {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {y₀ : ℝ}
    (hy₀ : d.η₀ < y₀) :
    ∀ (k : ℤ) (u : ℂ), y₀ ≤ |u.im| → d.E (u + (k : ℂ)) = d.E u + (k : ℂ) := by
  have hS : MandelDim.IsTInvariant {u : ℂ | y₀ ≤ |u.im|} := by
    intro u
    simp [Complex.add_im]
  refine E_add_int hS (fun w hw _ => ?_)
  exact Work.Repel.E_add_one d (lt_of_lt_of_le hy₀ hw)

/-- **The residual at the gate point, from the pin and the Lipschitz transfer.**  If the pin holds
at `Xc d w` and at `ς`, if `Φp` is `C`-Lipschitz on the pair `(ς, Xc d w)`, and if the modulus of
injectivity of `Φm` gives `‖ς - Xc d w‖ ≤ Cmod * (2 εp)`, then `‖Φp ς - d.E w‖ < δ`. -/
theorem gate_residual_of_pin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Φp : ℂ → ℂ} {Kp : Set ℂ} {w ς : ℂ} {εp C Cmod δ : ℝ}
    (hC : 0 ≤ C)
    (hpin : ∀ ζ ∈ Kp, ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖ < εp)
    (hXcKp : Work.Pert.Xc d w ∈ Kp) (hςKp : ς ∈ Kp)
    (hLip : ‖Φp ς - Φp (Work.Pert.Xc d w)‖ ≤ C * ‖ς - Work.Pert.Xc d w‖)
    (hclose : ‖ς - Work.Pert.Xc d w‖ ≤ Cmod * (2 * εp))
    (hδ : εp + C * (Cmod * (2 * εp)) < δ) :
    ‖Φp ς - d.E w‖ < δ := by
  have h1 : ‖Φp (Work.Pert.Xc d w) - d.E w‖ < εp := by
    have h := hpin _ hXcKp
    rw [tau0_Xc' d w] at h
    exact h
  have h2 : C * ‖ς - Work.Pert.Xc d w‖ ≤ C * (Cmod * (2 * εp)) :=
    mul_le_mul_of_nonneg_left hclose hC
  calc ‖Φp ς - d.E w‖
      ≤ ‖Φp ς - Φp (Work.Pert.Xc d w)‖ + ‖Φp (Work.Pert.Xc d w) - d.E w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < C * (Cmod * (2 * εp)) + εp := by linarith
    _ = εp + C * (Cmod * (2 * εp)) := by ring
    _ < δ := hδ

/-- **`hseg` from the level-`0` cover and the residual at the gate points.**  If
`Ef (Φm ς) = Φp ς` at every gate point `ς` whose `Φm`-value has real part in `[0,1)`, and if the
gate points of the segment satisfy the residual, then `hseg` holds for *all* `x : ℝ` — the integer
shifts of `Ef` and of `d.E` cancel. -/
theorem hseg_of_level0_cover {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ef Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y₀ δ : ℝ}
    (hEf_int : ∀ (k : ℤ) (u : ℂ), y₀ ≤ u.im → Ef (u + (k : ℂ)) = Ef u + (k : ℂ))
    (hEint : ∀ (k : ℤ) (u : ℂ), y₀ ≤ |u.im| → d.E (u + (k : ℂ)) = d.E u + (k : ℂ))
    (hcover : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∃ ς ∈ Q, Φm ς = (x : ℂ) + (y₀ : ℂ) * Complex.I)
    (hlvl : ∀ ς ∈ Q, 0 ≤ (Φm ς).re → (Φm ς).re < 1 → Ef (Φm ς) = Φp ς)
    (hres : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ ς ∈ Q, Φm ς = (x : ℂ) + (y₀ : ℂ) * Complex.I →
      ‖Φp ς - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2) :
    ∀ x : ℝ, ‖Ef ((x : ℂ) + (y₀ : ℂ) * Complex.I)
      - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2 := by
  intro x
  set x' : ℝ := x - (⌊x⌋ : ℤ) with hx'
  have hx'0 : 0 ≤ x' := by rw [hx']; exact Int.fract_nonneg x
  have hx'1 : x' < 1 := by rw [hx']; exact Int.fract_lt_one x
  have hxs : (x : ℂ) = (x' : ℂ) + (((⌊x⌋ : ℤ)) : ℂ) := by rw [hx']; push_cast; ring
  obtain ⟨ς, hςQ, hςΦ⟩ := hcover x' ⟨hx'0, hx'1⟩
  have hre : (Φm ς).re = x' := by rw [hςΦ]; simp
  have hlvl' : Ef (Φm ς) = Φp ς := hlvl ς hςQ (by rw [hre]; exact hx'0) (by rw [hre]; exact hx'1)
  have hres' := hres x' ⟨hx'0, hx'1⟩ ς hςQ hςΦ
  have hEfx : Ef ((x : ℂ) + (y₀ : ℂ) * Complex.I)
      = Ef ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ) := by
    have him : y₀ ≤ ((x' : ℂ) + (y₀ : ℂ) * Complex.I).im := by simp
    have harg : (x : ℂ) + (y₀ : ℂ) * Complex.I
        = ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ) := by rw [hxs]; ring
    rw [harg, hEf_int (⌊x⌋) ((x' : ℂ) + (y₀ : ℂ) * Complex.I) him]
  have hEx : d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)
      = d.E ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ) := by
    have him : y₀ ≤ |((x' : ℂ) + (y₀ : ℂ) * Complex.I).im| := by
      have h : ((x' : ℂ) + (y₀ : ℂ) * Complex.I).im = y₀ := by simp
      rw [h]; exact le_abs_self y₀
    have harg : (x : ℂ) + (y₀ : ℂ) * Complex.I
        = ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ) := by rw [hxs]; ring
    rw [harg, hEint (⌊x⌋) ((x' : ℂ) + (y₀ : ℂ) * Complex.I) him]
  rw [hEfx, hEx]
  have hge : ‖(Ef ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ))
        - (d.E ((x' : ℂ) + (y₀ : ℂ) * Complex.I) + (((⌊x⌋ : ℤ)) : ℂ))‖
      = ‖Ef ((x' : ℂ) + (y₀ : ℂ) * Complex.I)
        - d.E ((x' : ℂ) + (y₀ : ℂ) * Complex.I)‖ := by
    congr 1
    ring
  rw [hge]
  have h1 : Ef ((x' : ℂ) + (y₀ : ℂ) * Complex.I) = Φp ς := by
    rw [← hςΦ]; exact hlvl'
  rw [h1]
  exact hres'

/-- **`herb1` and `hlvl` from one legal walk step.**  With the canonical representative
`r := w - ⌊Re w⌋` of `w` a gate value (`hrep`) and its witness `ς := invOn Φm Q r` walking one step
inside the gate (`hstep`), the level-`1` translate of the representative is again a gate value
(`herb1`, the missing hypothesis of `EfFloor_sub_id_differentiableOn`) and `Φp` shifts by `1` there
(`hlvl`).  The walk step `F ς ∈ Q ∩ Qp` is produced by `pert2v2.fwdStep` (`Qm`) and the one-step
instance of `pert2v2.walk_Qp_waist` (`Qp`). -/
theorem herb1_hlvl_of_step {Φm Φp F : ℂ → ℂ} {Q Qp : Set ℂ} {y : ℝ}
    (hinj : Set.InjOn Φm Q)
    (hab : ∀ z ∈ Q, F z ∈ Q → Φm (F z) = Φm z + 1)
    (hstep : ∀ w : ℂ, y ≤ w.im → F (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) ∈ Q)
    (habP : ∀ z ∈ Qp, F z ∈ Qp → Φp (F z) = Φp z + 1)
    (hςP : ∀ w : ℂ, y ≤ w.im → Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ)) ∈ Qp)
    (hstepP : ∀ w : ℂ, y ≤ w.im → F (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) ∈ Qp)
    (hrep : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Q) :
    (∀ w : ℂ, y ≤ w.im → (w - (((⌊w.re⌋ : ℤ)) : ℂ)) + 1 ∈ Φm '' Q) ∧
      (∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1 ∈ Φm '' Q →
        Φp (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1))
          = Φp (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) + 1) := by
  constructor
  · intro w hw
    have hmem := hrep w hw
    set ς := Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ)) with hς
    have hςQ : ς ∈ Q := Work.Pert.invOn_mem hmem
    have hςΦ : Φm ς = w - (((⌊w.re⌋ : ℤ)) : ℂ) := Work.Pert.invOn_spec hmem
    refine ⟨F ς, hstep w hw, ?_⟩
    rw [hab ς hςQ (hstep w hw), hςΦ]
  · intro w hw _
    have hmem := hrep w hw
    set ς := Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ)) with hς
    have hςQ : ς ∈ Q := Work.Pert.invOn_mem hmem
    have hςΦ : Φm ς = w - (((⌊w.re⌋ : ℤ)) : ℂ) := Work.Pert.invOn_spec hmem
    have hFQ : F ς ∈ Q := hstep w hw
    have hmem2 : (w - (((⌊w.re⌋ : ℤ)) : ℂ)) + 1 ∈ Φm '' Q :=
      ⟨F ς, hFQ, by rw [hab ς hςQ hFQ, hςΦ]⟩
    have hinv2 : Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1) = F ς :=
      Work.Pert.invOn_eq hinj hmem2 hFQ (by rw [hab ς hςQ hFQ, hςΦ])
    rw [hinv2, hς, habP ς (hςP w hw) (hstepP w hw)]

end

end Work.Pert.pert2v2
