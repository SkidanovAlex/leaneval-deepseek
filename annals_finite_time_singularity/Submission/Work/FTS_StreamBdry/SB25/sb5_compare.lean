import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.Sb5CmpAux
import Submission.Work.FTS_StreamBdry.SB25.Sb5CmpCore
import Submission.Work.FTS_StreamBdry.SB25.bslOp_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.sb5_compare` — leaf E4c of the SB2/SB5 plan

The comparison half of the FIX-SB5 barrier: for `Q` of class `C²` on the open quadrant `Qd`,
`bslOp α Q = 0` above the line `z = L`, `|Q| ≤ Mb·sin 2θ` on the half-strip `z ≥ L` and
`|Q| ≤ ε·sin 2θ` beyond some radius (uniformly in `θ`),

`|Q z θ| ≤ Mb · sin 2θ · (L/z)^k`  for `L ≤ z`, `θ ∈ (0, π/2)`.

The proof is a Phragmén--Lindelöf comparison for the ground-state operator
`Lgs α u = bslOp α (s2·u)/s2` (`bslOp_split`).  Writing `u = Q/sin 2θ` and fixing a point
`(z₁,θ₁)`, the barrier `w = (Mb + ρ + δφ θ)(z/L)^{-k} + σ` (with `φ ≥ 0` blowing up at both
ends and `𝓐φ` bounded below, from `SB5Barrier`) is a strict supersolution of `Lgs`
(`Lgs_barrier`), dominates `u` on the boundary of a bounded rectangle and is `C²` on it
(`Sb5CmpAux`); hence `u - w ≤ 0` there by the maximum principle `Lgs_le_zero_of_max`.  Letting
`δ → 0`, then `ρ, σ → 0`, gives `u z₁ θ₁ ≤ Mb (L/z₁)^k`; the same argument for `-u` gives the
absolute value, and a final division by `sin 2θ` the claim for `Q`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem sb5_compare (α k L Mb : ℝ) (Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.Sb5Compare α k L Mb Q := by
  intro hα hL hαk hαk5 hBar hQc2 hbsl hbd hdec
  intro z₁ θ₁ hz₁ hθ₁
  by_cases hMb : Mb < 0
  · exfalso
    have h1 := hbd z₁ θ₁ hz₁ hθ₁
    have h2 : 0 < Work.Construction.s2 θ₁ := sb5c_s2_pos_of_Ioo hθ₁
    have h3 : Mb * Work.Construction.s2 θ₁ < 0 := mul_neg_of_neg_of_pos hMb h2
    linarith [abs_nonneg (Q z₁ θ₁)]
  · have hMb0 : 0 ≤ Mb := not_lt.mp hMb
    obtain ⟨φ, Cφ, hφ2, hφ0, hφtop0, hφtopπ, hφA⟩ := hBar
    have hφe0 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε → B ≤ φ θ := by
      intro B
      have h : ∀ᶠ θ in 𝓝[>] (0 : ℝ), B ≤ φ θ := hφtop0.eventually (eventually_ge_atTop B)
      rw [eventually_nhdsWithin_iff] at h
      have hmem : {x : ℝ | x ∈ Set.Ioi 0 → B ≤ φ x} ∈ 𝓝 (0 : ℝ) := h
      rw [Metric.mem_nhds_iff] at hmem
      obtain ⟨ε, hεpos, hε⟩ := hmem
      refine ⟨ε, hεpos, fun θ hθ0 hθε => ?_⟩
      have hmem : θ ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_lt]
        exact ⟨by linarith, hθε⟩
      exact hε hmem hθ0
    have hφeπ : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ θ : ℝ, Real.pi / 2 - ε < θ → θ < Real.pi / 2 → B ≤ φ θ := by
      intro B
      have h : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), B ≤ φ θ := hφtopπ.eventually (eventually_ge_atTop B)
      rw [eventually_nhdsWithin_iff] at h
      have hmem : {x : ℝ | x ∈ Set.Iio (Real.pi / 2) → B ≤ φ x} ∈ 𝓝 (Real.pi / 2) := h
      rw [Metric.mem_nhds_iff] at hmem
      obtain ⟨ε, hεpos, hε⟩ := hmem
      refine ⟨ε, hεpos, fun θ hθ0 hθ1 => ?_⟩
      have hmem : θ ∈ Metric.ball (Real.pi / 2) ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith⟩
      exact hε hmem hθ1
    have huC2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ))
        Work.Construction.Qd := by
      have hs : ContDiff ℝ 2 (fun t : ℝ => Work.Construction.s2 t) := by
        change ContDiff ℝ 2 (fun t : ℝ => Real.sin (2 * t))
        fun_prop
      have h2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
          Work.Construction.Qd := hs.comp_contDiffOn contDiffOn_snd
      have h3 : ∀ p ∈ Work.Construction.Qd, Work.Construction.s2 p.2 ≠ 0 := by
        intro p hp
        rw [Work.Construction.Qd] at hp
        exact ne_of_gt (sb5c_s2_pos_of_Ioo hp.2)
      have h4 := hQc2.div h2 h3
      have h5 : Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ)
          = Function.uncurry Q / (fun p : ℝ × ℝ => Work.Construction.s2 p.2) := by
        funext p; rfl
      rw [h5]
      exact h4
    have huLgs : ∀ z θ, L < z → θ ∈ Ioo 0 (Real.pi / 2) →
        Lgs α (fun z θ => Q z θ / Work.Construction.s2 θ) z θ = 0 := by
      intro z θ hz hθ
      have hzpos : 0 < z := lt_trans hL hz
      have hQd : (z, θ) ∈ Work.Construction.Qd := by
        rw [Work.Construction.Qd]; exact Set.mem_prod.mpr ⟨hzpos, hθ⟩
      have hsplit := bslOp_split α Q hQd (hQc2.contDiffAt (sb5c_Qd_mem_nhds hQd))
      have hz0 : Work.Elliptic.bslOp α Q z θ = 0 := hbsl z θ hz hθ
      have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (sb5c_s2_pos_of_Ioo hθ)
      have key : Work.Construction.s2 θ *
          Lgs α (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ = 0 := by
        rw [← hsplit, hz0]
      exact (mul_eq_zero.mp key).resolve_left hs2
    have huMb : ∀ z θ, L ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => Q z θ / Work.Construction.s2 θ) z θ| ≤ Mb := by
      intro z θ hz hθ
      have hs2 : 0 < Work.Construction.s2 θ := sb5c_s2_pos_of_Ioo hθ
      have h := hbd z θ hz hθ
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact h
    have huDec : ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => Q z θ / Work.Construction.s2 θ) z θ| ≤ ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := hdec ε hε
      refine ⟨R, fun z θ hz hθ => ?_⟩
      have hs2 : 0 < Work.Construction.s2 θ := sb5c_s2_pos_of_Ioo hθ
      have h := hR z θ hz hθ
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact h
    have huP : (fun z θ => Q z θ / Work.Construction.s2 θ) z₁ θ₁ ≤ Mb * (L / z₁) ^ k := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h := sb5c_core_le α k L Mb φ Cφ (fun z θ => Q z θ / Work.Construction.s2 θ)
        hα hαk hαk5 hL hMb0 hφ2 hφ0 hφe0 hφeπ hφA huC2 huLgs huMb huDec hz₁ hθ₁
        (ε / 4) (ε / 4) (by linarith) (by linarith)
      simp only [] at h ⊢
      linarith
    have hnuC2 : ContDiffOn ℝ 2
        (Function.uncurry (fun z θ => -(Q z θ / Work.Construction.s2 θ)))
        Work.Construction.Qd := by
      have h5 : (Function.uncurry (fun z θ => -(Q z θ / Work.Construction.s2 θ)))
          = -(Function.uncurry (fun z θ => Q z θ / Work.Construction.s2 θ)) := by
        funext p; rfl
      rw [h5]
      exact huC2.neg
    have hnuLgs : ∀ z θ, L < z → θ ∈ Ioo 0 (Real.pi / 2) →
        Lgs α (fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ = 0 := by
      intro z θ hz hθ
      have h := congrFun (congrFun
        (sb5c_Lgs_neg α (fun z θ => Q z θ / Work.Construction.s2 θ)) z) θ
      rw [h, huLgs z θ hz hθ]
      ring
    have hnuMb : ∀ z θ, L ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ| ≤ Mb := by
      intro z θ hz hθ
      simpa using huMb z θ hz hθ
    have hnuDec : ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) →
        |(fun z θ => -(Q z θ / Work.Construction.s2 θ)) z θ| ≤ ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := huDec ε hε
      refine ⟨R, fun z θ hz hθ => ?_⟩
      simpa using hR z θ hz hθ
    have huN : -(Q z₁ θ₁ / Work.Construction.s2 θ₁) ≤ Mb * (L / z₁) ^ k := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h := sb5c_core_le α k L Mb φ Cφ (fun z θ => -(Q z θ / Work.Construction.s2 θ))
        hα hαk hαk5 hL hMb0 hφ2 hφ0 hφe0 hφeπ hφA hnuC2 hnuLgs hnuMb hnuDec hz₁ hθ₁
        (ε / 4) (ε / 4) (by linarith) (by linarith)
      try simp only [] at h
      linarith
    have hs2 : 0 < Work.Construction.s2 θ₁ := sb5c_s2_pos_of_Ioo hθ₁
    have habs : |Q z₁ θ₁ / Work.Construction.s2 θ₁| ≤ Mb * (L / z₁) ^ k :=
      abs_le.mpr ⟨by linarith, huP⟩
    calc |Q z₁ θ₁| = |Q z₁ θ₁ / Work.Construction.s2 θ₁| * Work.Construction.s2 θ₁ := by
          rw [abs_div, abs_of_pos hs2, div_mul_cancel₀ _ (ne_of_gt hs2)]
      _ ≤ Mb * (L / z₁) ^ k * Work.Construction.s2 θ₁ :=
          mul_le_mul_of_nonneg_right habs (le_of_lt hs2)
      _ = Mb * Work.Construction.s2 θ₁ * (L / z₁) ^ k := by ring


end Work.FTS_StreamBdry.SB25
