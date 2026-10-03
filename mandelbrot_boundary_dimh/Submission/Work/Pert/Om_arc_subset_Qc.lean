import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.OmArc.geom_Om
import Submission.Work.Pert.OmArc.geom_arc
import Submission.Work.Pert.OmArc.inv_bound
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

open MandelDim Complex Set Metric

set_option linter.unusedVariables false

noncomputable section

/-!
# PERT · `Work.Pert.Om_arc_subset_Qc`

The two discs `Om η` and the circular arc `{η e^{iθ} | θ ∈ [π/2, 3π/2]}` through `-η` both lie in
the *safe core* `Qc η ξ₁ α = {ζ ∈ Qm ξ₁ α | closedBall ζ (η/100) ⊆ Qm ξ₁ α}` of the gate, under the
arithmetic side conditions of the PERT area (`2ξ₁ < η`, `|Im α| < Re α`, `2πη‖α‖ ≤ 1/64`).

Recall `Qm ξ₁ α ↔ ξ₁ - Re(1/α) - |Im z + Im(1/α)| < Re z < |Im z| - ξ₁` (`Qm_mem_iff`), so it
suffices to prove, uniformly over a point `ζ` and all `v` in its `η/100`-ball,

* **(B-cone, upper)** `Re v - |Im v| < -ξ₁`, which follows from `Re v - |Im v| ≤
  (Re ζ - |Im ζ|) + 2(η/100)` and the geometric bound `Re ζ - |Im ζ| ≤ -η + (13√2/40)η` for
  `ζ ∈ Om η` resp. `≤ -η` for `ζ` on the arc, together with `13√2/40 + 1/50 < 1/2` and `2ξ₁ < η`;
* **(A-cone, lower)** `ξ₁ - Re(1/α) < Re v + |Im v + Im(1/α)|`, which follows from
  `Re v + |Im v + c| ≥ Re(1/α) + |c| - (|Re v| + |Im v|) ≥ 64πη - √2‖v‖ ≥ 64πη - 2η > ξ₁`,
  where the first inequality is `|c| - |Im v| ≤ |Im v + c|` and the last uses
  `Re(1/α) + |Im(1/α)| ≥ 64πη` (`inv_bound`) and `64π - 2 > 1/2`.

The `η/100`-ball never gets closer to the apexes than the centre does by more than `2(η/100)`, which
is why `Qc` (rather than `Qm`) is the right region.

Note on the hypotheses: the route below uses only `0 < η`, `2ξ₁ < η`, `|Im α| < Re α` and
`2πη‖α‖ ≤ 1/64` — the side conditions `100 ≤ η`, `0 < ξ₁` and `η/2 + 2ξ₁ < Re(1/α)` of the fixed
statement are *not* needed (the numerical margins are enormous: `64π - 2 ≈ 199` against `ξ₁ < η/2`,
and `13√2/40 + 1/50 ≈ 0.4796 < 1/2`).  They are kept because the statement is the requester's.
-/

/-- The arithmetic core of the upper (B-cone) estimate: `13√2/40 + 1/50 < 1/2`, i.e.
`√2 < 96/65`; equivalently `13√2/40 < 12/25`, leaving a margin of `1/2 - 12/25 - 1/50 = 0`. -/
private lemma thirteen_sqrt_two_div_forty_add : 13 * Real.sqrt 2 / 40 + 1 / 50 < (1 / 2 : ℝ) := by
  have h : Real.sqrt 2 < 96 / 65 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  nlinarith [h]

/-- `√2 ≤ 400/267`, the constant needed to turn `‖v‖ ≤ (53/40 + 1/100)η` into `√2‖v‖ ≤ 2η`. -/
private lemma sqrt_two_le_400_div_267 : Real.sqrt 2 ≤ 400 / 267 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- Points of `Om η` are within `53η/40 = η + 13η/40` of the origin (`η > 0`). -/
private lemma norm_le_of_mem_Om {η : ℝ} (hη : 0 < η) {ζ : ℂ} (h : ζ ∈ Om η) :
    ‖ζ‖ ≤ 53 * η / 40 := by
  rw [Om, Set.mem_union] at h
  have hc : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul]
    simp [abs_of_pos hη]
  rcases h with h | h
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    calc ‖ζ‖ = ‖(ζ - Complex.I * (η : ℂ)) + Complex.I * (η : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - Complex.I * (η : ℂ)‖ + ‖Complex.I * (η : ℂ)‖ := norm_add_le _ _
      _ ≤ 13 * η / 40 + η := by rw [hc]; linarith
      _ = 53 * η / 40 := by ring
  · rw [Metric.mem_closedBall, dist_eq_norm] at h
    have hc' : ‖-(Complex.I * (η : ℂ))‖ = η := by rw [norm_neg, hc]
    calc ‖ζ‖ = ‖(ζ - -(Complex.I * (η : ℂ))) + -(Complex.I * (η : ℂ))‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - -(Complex.I * (η : ℂ))‖ + ‖-(Complex.I * (η : ℂ))‖ := norm_add_le _ _
      _ ≤ 13 * η / 40 + η := by rw [hc']; linarith
      _ = 53 * η / 40 := by ring

/-- **The gate geometry.**  A point `ζ` with `‖ζ‖ ≤ 53η/40` whose cone quantity satisfies
`Re ζ - |Im ζ| ≤ -η + (13√2/40)η` (which holds on `Om η` and on the arc `η e^{i[π/2,3π/2]}`)
belongs to the safe core `Qc η ξ₁ α`, provided `2ξ₁ < η`, `η > 0`, `|Im α| < Re α` and
`2πη‖α‖ ≤ 1/64`. -/
private lemma mem_Qc_of_geom {ξ₁ η : ℝ} {α : ℂ} (hη : 0 < η) (h2ξ : 2 * ξ₁ < η)
    (hF1 : |α.im| < α.re) (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    {ζ : ℂ} (hn : ‖ζ‖ ≤ 53 * η / 40)
    (hc : ζ.re - |ζ.im| ≤ -η + 13 * Real.sqrt 2 / 40 * η) :
    ζ ∈ Qc η ξ₁ α := by
  have hS : 64 * Real.pi * η ≤ (1 / α).re + |(1 / α).im| := OmArc.inv_bound hη hF1 hαη
  have hpi : (1 / 2 : ℝ) < 64 * Real.pi - 2 := by
    have h3 := Real.pi_gt_three
    nlinarith [h3]
  have hxi : ξ₁ < 64 * Real.pi * η - 2 * η := by nlinarith [h2ξ, hη, hpi]
  have hball : ∀ v : ℂ, dist v ζ ≤ η / 100 → v ∈ Qm ξ₁ α := by
    intro v hv
    rw [dist_eq_norm] at hv
    have hvn : ‖v‖ ≤ 53 * η / 40 + η / 100 := by
      calc ‖v‖ = ‖(v - ζ) + ζ‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ ≤ η / 100 + 53 * η / 40 := add_le_add hv hn
        _ = 53 * η / 40 + η / 100 := by ring
    have hvm : Real.sqrt 2 * ‖v‖ ≤ 2 * η := by
      have h2 : Real.sqrt 2 * ‖v‖ ≤ (400 / 267) * (53 * η / 40 + η / 100) :=
        mul_le_mul sqrt_two_le_400_div_267 hvn (norm_nonneg _) (by norm_num)
      have h3 : (400 / 267 : ℝ) * (53 * η / 40 + η / 100) = 2 * η := by ring
      linarith
    rw [Qm_mem_iff]
    constructor
    · -- A-cone (lower) condition: `ξ₁ - Re(1/α) - |Im v + Im(1/α)| < Re v`
      set c : ℝ := (1 / α).im with hcdef
      have h1 : |c| - |v.im| ≤ |v.im + c| := by
        have h := abs_add_le (v.im + c) (-(v.im))
        have h2 : v.im + c + -(v.im) = c := by ring
        rw [h2, abs_neg] at h
        linarith
      have h2 : -|v.re| ≤ v.re := neg_abs_le v.re
      have h3 : |v.re| + |v.im| ≤ Real.sqrt 2 * ‖v‖ := sqrt2_norm v
      have : ξ₁ < (1 / α).re + |v.im + c| + v.re := by
        nlinarith [hS, h1, h2, h3, hvm, hxi]
      linarith
    · -- B-cone (upper) condition: `Re v < |Im v| - ξ₁`
      have hv1 : v.re ≤ ζ.re + η / 100 := by
        have h := Complex.abs_re_le_norm (v - ζ)
        have hre : (v - ζ).re = v.re - ζ.re := by simp
        rw [hre] at h
        have h' := (abs_le.mp h).2
        linarith
      have hv2 : |ζ.im| - η / 100 ≤ |v.im| := by
        have h := abs_sub_abs_le_abs_sub ζ.im v.im
        have him : (v - ζ).im = v.im - ζ.im := by simp
        have hb : |ζ.im - v.im| ≤ ‖v - ζ‖ := by
          rw [abs_sub_comm, ← him]; exact Complex.abs_im_le_norm (v - ζ)
        linarith
      have hlt : (ζ.re - |ζ.im|) + 2 * (η / 100) < -ξ₁ := by
        have ha := thirteen_sqrt_two_div_forty_add
        nlinarith [hc, ha, h2ξ, hη]
      linarith
  rw [Qc, Set.mem_ofPred_eq]
  exact ⟨hball ζ (by rw [dist_self]; linarith), fun v hv => hball v hv⟩

/-- The region `Om η` and the circular arc `{η e^{iθ} | θ ∈ [π/2, 3π/2]}` (which passes through
`-η`) both lie in the safe core `Qc η ξ₁ α` of the gate.

Route: in the coordinate description `w ∈ Qm ξ₁ α ↔ ξ₁ - (1/α).re - |w.im + (1/α).im| < w.re < |w.im| - ξ₁` (`Work.Pert.Gates.Qp_mem_iff` + `Tt_mem_Qm_iff`), the only nontrivial requirement is the lower bound at `w = -η`, where one needs `(1/α).re + |(1/α).im| > η + ξ₁ + η/100`.  Now `(1/α).re + |(1/α).im| = (α.re + |α.im|)/‖α‖² ≥ 1/(α.re + |α.im|) ≥ 1/(2α.re) ≥ 1/(2‖α‖) ≥ 64πη`, using `hF1`, `hαη`; and `64πη > η + ξ₁ + η/100` for `η ≥ 100`, `2ξ₁ < η`.  The upper condition `max (w.re - |w.im|) ≤ 13η/40·√2 + η/100 = 0.4697η < η - ξ₁` follows from `2ξ₁ < η`. -/
theorem Om_arc_subset_Qc {ξ₁ η : ℝ} {α : ℂ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hξ₁ : 0 < ξ₁) (h2ξ : 2 * ξ₁ < η)
    (hRe : η / 2 + 2 * ξ₁ < (1 / α).re)
    (hF1 : |α.im| < α.re)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64) :
    (∀ ζ ∈ Work.Pert.Om η, ζ ∈ Work.Pert.Qc η ξ₁ α) ∧
    (∀ θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2),
      η * Complex.exp (θ * Complex.I) ∈ Work.Pert.Qc η ξ₁ α) := by
  constructor
  · intro ζ hζ
    exact mem_Qc_of_geom hη h2ξ hF1 hαη (norm_le_of_mem_Om hη hζ) (OmArc.geom_Om hζ)
  · intro θ hθ
    have hnorm : ‖(η : ℂ) * Complex.exp (θ * Complex.I)‖ = η := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [abs_of_pos hη]
    have hcone : ((η : ℂ) * Complex.exp (θ * Complex.I)).re -
        |((η : ℂ) * Complex.exp (θ * Complex.I)).im| ≤ -η + 13 * Real.sqrt 2 / 40 * η := by
      have h := OmArc.geom_arc hη hθ
      have h3 : (0 : ℝ) ≤ 13 * Real.sqrt 2 / 40 * η := by
        have := Real.sqrt_nonneg 2
        positivity
      linarith
    exact mem_Qc_of_geom hη h2ξ hF1 hαη (by rw [hnorm]; linarith) hcone

end

end Work.Pert
