import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

set_option autoImplicit false

/-! ## Pointwise bounds on the star coefficients `ℛ, 𝒰, 𝒱` at `Φ̃_* = Φ_* - Θ_*(α)`

The package `StarPkgo2` records, among other things, the `𝒲^{4,∞}`-bounds of the two weighted
coefficients `((z+1)/z)·ℛ(Φ̃_*)` and `𝒱(Φ̃_*)`.  The pointwise consequence of the `𝒲^{4,∞}`-norm
(`Work.Spaces.WlInf_z_bound`) turns those into the pointwise bounds `Rop_PhiTs_abs_le_max` and
`Vop_PhiTs_abs_le_max`; note that they hold for **every** value of `α` (in particular no
positivity of `α` is required: the weight `(z+1)/z` is `≥ 1` for `z > 0`, and a negative bound
only makes the statement stronger).

The third operator `𝒰` is *not* bounded in the package, but it is not independent of the other
two: the pointwise identity (valid on `cos θ ≠ 0`)

  `ℛ(Ψ) - 𝒱(Ψ) = tan θ·(3Ψ + α z ∂_zΨ) = - tan θ·𝒰(Ψ)`

(`Work.FTS.Nonlinear.Pieces.Rl1.Rop_sub_Vop_eq_tan`) shows that on the angular region
`θ ≥ c > 0`, on which `tan θ` is bounded *below* by `tan c > 0`, the uniform bound on `𝒰` is
that of `ℛ` and `𝒱` multiplied by the finite constant `cot c`.  This is the content of
`Uop_PhiTs_abs_le_mul`; it is the reason the statement is true up to the axis `θ = π/2`
(as `θ → π/2` the factor `cot θ` *decreases* to `0`, while the corresponding factor for the
field `𝒰/sin(2θ)` of the package would blow up). -/

/-- Pointwise bound on `ℛ(Φ̃_*)` from the `𝒲^{4,∞}`-field `StarPkgo2.RW`: the weight `(z+1)/z`
is `≥ 1` for `z > 0`. -/
theorem Rop_PhiTs_abs_le_max {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ max (Cs * α) 0 := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hmem : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := hstar.RW.1
  have hb : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ Cs * α := hstar.RW.2
  have h0 := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (Nat.zero_le 4) z θ hzI hθ
  have h1 : |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ Cs * α := by
    refine le_trans ?_ hb
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h0
  have hge1 : (1 : ℝ) ≤ (z + 1) / z := by
    rw [le_div_iff₀ hz]
    linarith
  have hpos : 0 < (z + 1) / z := lt_of_lt_of_le zero_lt_one hge1
  calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      = 1 * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := (one_mul _).symm
    _ ≤ ((z + 1) / z) * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| :=
        mul_le_mul_of_nonneg_right hge1 (abs_nonneg _)
    _ = |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
        rw [abs_mul, abs_of_pos hpos]
    _ ≤ max (Cs * α) 0 := le_trans h1 (le_max_left _ _)

/-- Pointwise bound on `𝒱(Φ̃_*)` from the `𝒲^{4,∞}`-field `StarPkgo2.VW`. -/
theorem Vop_PhiTs_abs_le_max {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ max (Cs * α) 0 := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hmem : Work.Spaces.WlInfMem α 4
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) := hstar.VW.1
  have hb : Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ≤ Cs * α := hstar.VW.2
  have h1 := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (Nat.zero_le 4) z θ hzI hθ
  have h1' : |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    refine le_trans ?_ hb
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h1
  exact le_trans h1' (le_max_left _ _)

/-- Pointwise bound on `𝒰(Φ̃_*)` on the angular region `c ≤ θ < π/2`, `c > 0`, from the bounds
on `ℛ` and `𝒱` and the identity `tan θ·𝒰 = 𝒱 - ℛ`.  The constant is `2·cot c·max (Cs α) 0`,
which is finite precisely because `θ ≥ c > 0`. -/
theorem Uop_PhiTs_abs_le_mul {α Cs c : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z) (hc : 0 < c)
    (hcθ : c ≤ θ) (hθ : θ < Real.pi / 2) :
    |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 * |Real.cos c / Real.sin c| := by
  have hθpos : 0 < θ := lt_of_lt_of_le hc hcθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθpos, le_of_lt hθ⟩
  have hclt : c < Real.pi / 2 := lt_of_le_of_lt hcθ hθ
  have hR := Rop_PhiTs_abs_le_max hstar hz hθI
  have hV := Vop_PhiTs_abs_le_max hstar hz hθI
  -- the pointwise identity `tan θ·𝒰 = -(ℛ - 𝒱)`
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩)
  have htanU : Real.tan θ * Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = -(Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) := by
    have h := Work.FTS.Nonlinear.Pieces.Rl1.Rop_sub_Vop_eq_tan α
      (Work.FTS.VocabO2.PhiTs α Φs) (z := z) hcosθ
    have h2 : 3 * Work.FTS.VocabO2.PhiTs α Φs z θ
        + α * z * Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
        = -(Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := by
      simp only [Work.Construction.Uop]
      ring
    rw [h2] at h
    rw [h]
    ring
  have htan_le : Real.tan c ≤ Real.tan θ := by
    rcases lt_or_eq_of_le hcθ with hlt | heq
    · exact le_of_lt (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hc.le hθ hlt)
    · rw [heq]
  have htanθpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθpos hθ
  have htri : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ 2 * max (Cs * α) 0 := by
    have hab : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
      have h := abs_add_le (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        (-(Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith [hR, hV]
  have hTU : Real.tan c * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 := by
    have h2 : Real.tan θ * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
      have h := congrArg (fun x : ℝ => |x|) htanU
      rw [abs_mul, abs_neg, abs_of_pos htanθpos] at h
      exact h
    calc Real.tan c * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ Real.tan θ * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| :=
          mul_le_mul_of_nonneg_right htan_le (abs_nonneg _)
      _ = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := h2
      _ ≤ 2 * max (Cs * α) 0 := htri
  have htanpos : 0 < Real.tan c := Real.tan_pos_of_pos_of_lt_pi_div_two hc hclt
  have hU1 : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 / Real.tan c := by
    rw [le_div_iff₀ htanpos]
    have h := hTU
    rw [mul_comm (Real.tan c)] at h
    exact h
  have hsinpos : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi hc (by linarith [hclt, Real.pi_pos])
  have hcospos : 0 < Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hclt⟩
  have hU2 : 2 * max (Cs * α) 0 / Real.tan c
      = 2 * max (Cs * α) 0 * |Real.cos c / Real.sin c| := by
    rw [Real.tan_eq_sin_div_cos, abs_of_pos (div_pos hcospos hsinpos),
      div_eq_mul_inv (2 * max (Cs * α) 0) (Real.sin c / Real.cos c),
      inv_div (Real.sin c) (Real.cos c)]
  exact hU1.trans (le_of_eq hU2)

theorem star_blocks_bnd {α Cs c : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ C := by
  change ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        + |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C
  refine ⟨(2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 :=
      mul_nonneg (by positivity) (le_max_right _ _)
    linarith
  · intro z θ hz hcθ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt (lt_of_lt_of_le hc hcθ), le_of_lt hθ⟩
    have hR := Rop_PhiTs_abs_le_max hstar hz hθI
    have hV := Vop_PhiTs_abs_le_max hstar hz hθI
    have hU := Uop_PhiTs_abs_le_mul hstar hz hc hcθ hθ
    calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 := by
          nlinarith [hR, hV, hU]
      _ ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 + 1 := by linarith

end Work.FTS.StrongEps.blocks
