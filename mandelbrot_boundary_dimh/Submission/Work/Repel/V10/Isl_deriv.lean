import Mathlib
import Submission.Work.Repel.V10.chain_v9_isl
import Submission.Work.Repel.V10.chain_v9_walk
import Submission.Work.Repel.chain_v9_geom
import Submission.Work.Repel.V10.SrcC_isConnected
import Submission.Work.Repel.V10.SrcC_sub_Dflat
import Submission.Work.Repel.V10.uOf_differentiableOn
import Submission.Work.Repel.exists_piExp_eq_of_ball
import Submission.Work.Repel.exists_local_inv
import Submission.Work.L62.chain
import Submission.Work.Repel.walk_of_sub
import Submission.Work.Repel.V10.lift_deriv
import Submission.Work.Repel.V10.wOf_deriv
import Submission.Work.Repel.norm_deriv_phi_eq
import Submission.Work.Repel.deriv_iterate_shift_le
import Submission.Work.Repel.V10.fN_lift_eq
import Submission.Work.Repel.V10.deriv_relation

/-!
# `Work.Repel.Isl_deriv` : the derivative bound on the islands of the §6 cells

This is the `hderiv` field of `Work.Repel.ReturnData` for the §6 assembly
(`Work.Repel.chain_v9_final`): on the island `V.Isl j k n` of a cell, the derivative of the cell
iterate `f^[N]` is bounded by the constant `10⁶ · Cb · (C₁'+1) · η² · η₁` of the ledger
(`NOTES_chain_returns_v9_design.md`, row 15/17).

## Route

The source region `SrcC j k n` is the image of the fibre `fib j k = W j + k` under the explicit
lift `lift j k n` (`SrcC_eq_image_lift`), and on that (open) fibre the cell iterate is

  `f^[N] (φ₀ (lift u)) = φ₀ (wOf (ĥ^[j] u - k))`   (`Work.Repel.fN_lift_eq`),

with `ĥ = R - β`.  Differentiating this identity on the open set `fib j k`
(`Work.Repel.deriv_relation`) gives, at `u`,

  `(f^[N])'(w₀) · φ₀'(w₀) · (lift)'(u) = φ₀'(w₁) · (wOf)'(u') · (ĥ^[j])'(u)`,

where `w₀ = lift j k n u`, `w₁ = wOf u'`, `u' = ĥ^[j] u - k`.  Taking norms and inserting

* `‖(lift)'(u)‖ = ‖φ₁'(u)‖ / (2π ‖φ₁ u‖)` (`Work.Repel.lift_deriv`),
* `‖(wOf)'(u')‖ = ‖φ₁'(u')‖ / (‖s‖ · 2π ‖π w₁‖)` (`Work.Repel.wOf_deriv`),
* `‖φ'(w)‖ = ‖(τ₀ ∘ φ)'(w)‖ · ‖φ w‖²` and `1/2 < ‖(τ₀ ∘ φ)'‖ < 2`
  (`Work.Repel.norm_deriv_phi_eq`, `PertData.φ_star_deriv`),
* `40/(51η) ≤ ‖φ₀ w‖`, `40/(51η₁) ≤ ‖φ₁ u‖ ≤ 40/(29η₁)` (`chain_v9_geom`),
* `‖φ₀'(w₁)‖ · ‖φ₁'(u')‖ / (‖s‖ 2π ‖π w₁‖) ≤ Cb` (`PertData`'s `hCbbd`),
* `‖(ĥ^[j])'(u)‖ < C₁'` on the shifted fibre (`Work.Repel.deriv_iterate_shift_le`),

yields `‖(f^[N])'‖ ≤ 120 · Cb · C₁' · η² η₁` on the island, which is `≤ 10⁶ Cb (C₁'+1) η² η₁`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- `(4η²)·((1/2)(40/(51η))²) = 3200/2601`. -/
private lemma key_four (η : ℝ) (hη : 0 < η) :
    (4 * η ^ 2) * ((1 / 2) * (40 / (51 * η)) ^ 2) = 3200 / 2601 := by
  field_simp
  ring

/-- `30η₁·((1/2)(40/(51η₁))²/(2π·40/(29η₁))) = 8700/(2601π)`. -/
private lemma key_thirty (η₁ : ℝ) (hη₁ : 0 < η₁) :
    30 * η₁ * ((1 / 2) * (40 / (51 * η₁)) ^ 2 / (2 * Real.pi * (40 / (29 * η₁))))
      = 8700 / (2601 * Real.pi) := by
  field_simp
  ring

namespace V10

variable (V : V10)

/-- The source region of a cell lies in `Dsm η`. -/
theorem SrcC_sub_Dsm {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) : V.SrcC j k n ⊆ Dsm V.η :=
  fun _ hw => Dflat_subset_Dsm V.η (SrcC_sub_Dflat V hSm hn hw)

/-- On the source region, `4η² ‖(φ₀)'(w)‖ ≥ 1`. -/
theorem one_le_four_eta_sq_mul_deriv_phi₀ {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) {w : ℂ} (hw : w ∈ V.SrcC j k n) :
    1 ≤ 4 * V.η ^ 2 * ‖deriv V.P₀.φ w‖ := by
  have hηpos : 0 < V.η := V.hηpos
  have hdsm : w ∈ Dsm V.η := SrcC_sub_Dsm V hSm hn hw
  have hder : (1 : ℝ) / 2 < ‖deriv (fun u => tau0 (V.P₀.φ u)) w‖ :=
    (V.P₀.φ_star_deriv w (Or.inl hdsm)).1
  have hnor : 40 / (51 * V.η) ≤ ‖V.P₀.φ w‖ :=
    (phi_norm_bounds V.P₀ V.hηpos (Or.inl hdsm)).1
  have hrel : ‖deriv V.P₀.φ w‖
      = ‖deriv (fun u => tau0 (V.P₀.φ u)) w‖ * ‖V.P₀.φ w‖ ^ 2 :=
    norm_deriv_phi_eq V.P₀ V.hηpos (Or.inl hdsm)
  have h0 : (0 : ℝ) ≤ 40 / (51 * V.η) := by positivity
  have hsq : (40 / (51 * V.η)) ^ 2 ≤ ‖V.P₀.φ w‖ ^ 2 :=
    pow_le_pow_left₀ h0 hnor 2
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hb : (1 / 2) * (40 / (51 * V.η)) ^ 2 ≤ ‖deriv V.P₀.φ w‖ := by
    rw [hrel]
    exact le_trans (mul_le_mul_of_nonneg_left hsq hhalf)
      (mul_le_mul_of_nonneg_right hder.le (sq_nonneg _))
  have hkey := key_four V.η hηpos
  have hstep : 1 ≤ (4 * V.η ^ 2) * ((1 / 2) * (40 / (51 * V.η)) ^ 2) := by
    rw [hkey]; norm_num
  have := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 4 * V.η ^ 2 by positivity)
  linarith [hstep, this]

/-- On a fibre, `30η₁ ‖(lift)'(u)‖ ≥ 1`. -/
theorem one_le_thirty_eta₁_mul_deriv_lift {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u : ℂ} (hu : u ∈ V.fib j k) :
    1 ≤ 30 * V.η₁ * ‖deriv (V.lift j k n) u‖ := by
  have hη₁pos : 0 < V.η₁ := V.hη₁pos
  have huSm : u ∈ V.Sm1 := hSm hu
  have hder : (1 : ℝ) / 2 < ‖deriv (fun u => tau0 (V.P₁.φ u)) u‖ :=
    (V.P₁.φ_star_deriv u (Sm1_sub_Dsm_union V huSm)).1
  have hlo : 40 / (51 * V.η₁) ≤ ‖V.P₁.φ u‖ := (phi_bounds_of_mem_Sm1 V huSm).1
  have hhi : ‖V.P₁.φ u‖ ≤ 40 / (29 * V.η₁) := (phi_bounds_of_mem_Sm1 V huSm).2
  have hrel : ‖deriv V.P₁.φ u‖
      = ‖deriv (fun u => tau0 (V.P₁.φ u)) u‖ * ‖V.P₁.φ u‖ ^ 2 :=
    norm_deriv_phi_eq V.P₁ V.hη₁pos (Sm1_sub_Dsm_union V huSm)
  have h0 : (0 : ℝ) ≤ 40 / (51 * V.η₁) := by positivity
  have hsq : (40 / (51 * V.η₁)) ^ 2 ≤ ‖V.P₁.φ u‖ ^ 2 :=
    pow_le_pow_left₀ h0 hlo 2
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hnum : (1 / 2) * (40 / (51 * V.η₁)) ^ 2 ≤ ‖deriv V.P₁.φ u‖ := by
    rw [hrel]
    exact le_trans (mul_le_mul_of_nonneg_left hsq hhalf)
      (mul_le_mul_of_nonneg_right hder.le (sq_nonneg _))
  have hden : 2 * Real.pi * ‖V.P₁.φ u‖ ≤ 2 * Real.pi * (40 / (29 * V.η₁)) :=
    mul_le_mul_of_nonneg_left hhi (by positivity)
  have hlift := lift_deriv V (n := n) hSm hu
  have hc' : (0 : ℝ) ≤ ‖deriv V.P₁.φ u‖ := norm_nonneg _
  have hd' : 0 < 2 * Real.pi * ‖V.P₁.φ u‖ := by
    have h1 : (0 : ℝ) < 40 / (51 * V.η₁) := by positivity
    have h2 : (0 : ℝ) < ‖V.P₁.φ u‖ := lt_of_lt_of_le h1 hlo
    positivity
  have hquot : (1 / 2) * (40 / (51 * V.η₁)) ^ 2 / (2 * Real.pi * (40 / (29 * V.η₁)))
      ≤ ‖deriv (V.lift j k n) u‖ := by
    rw [hlift]
    exact div_le_div₀ hc' hnum hd' hden
  have hkey := key_thirty V.η₁ hη₁pos
  have hpi : (1 : ℝ) ≤ 8700 / (2601 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d4]
  have := mul_le_mul_of_nonneg_left hquot (show (0 : ℝ) ≤ 30 * V.η₁ by positivity)
  linarith [hkey, hpi, this]

/-- The target factor: `‖(φ₀)'(w₁)‖ · ‖(wOf)'(u')‖ ≤ Cb`. -/
theorem target_bound {u' : ℂ} (hu' : u' ∈ V.W 0) :
    ‖deriv V.P₀.φ (V.wOf u')‖ * ‖deriv V.wOf u'‖ ≤ V.Cb := by
  obtain ⟨hbal, hpi⟩ := V.wOf_spec hu'
  have hb := V.hCbbd u' hu' (V.wOf u') hbal hpi
  rw [Work.Repel.norm_deriv_piExp] at hb
  have hd := wOf_deriv V hu'
  have hD : 0 < ‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖ := by
    have h1 : (0 : ℝ) < ‖V.s‖ := norm_pos_iff.mpr V.hs
    have h2 : (0 : ℝ) < ‖MandelDim.piExp (V.wOf u')‖ :=
      norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have h3 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  rw [hd]
  have hkey : ‖deriv V.P₀.φ (V.wOf u')‖
        * (‖deriv V.P₁.φ u'‖ / (‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖))
      = (‖deriv V.P₀.φ (V.wOf u')‖ * ‖deriv V.P₁.φ u'‖)
        / (‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖) := by ring
  rw [hkey, div_le_iff₀ hD]
  ring_nf at hb ⊢
  exact hb

end V10

/-- Final arithmetic of `Isl_deriv`. -/
private lemma Isl_deriv_arith {A b c d1 d2 d3 η η₁ Cb C₁' : ℝ}
    (hη : 0 < η) (hη₁ : 0 < η₁) (hCb : 0 < Cb) (hC₁' : 0 < C₁')
    (hE : A * (b * c) = (d1 * d2) * d3)
    (hb : 1 ≤ 4 * η ^ 2 * b) (hc : 1 ≤ 30 * η₁ * c)
    (hd : d1 * d2 ≤ Cb) (he : d3 ≤ C₁') (hd3 : 0 ≤ d3) :
    A ≤ 10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁ := by
  have hb0 : 0 < b := by nlinarith [hη, hb]
  have hc0 : 0 < c := by nlinarith [hη₁, hc]
  have hbc0 : 0 < b * c := mul_pos hb0 hc0
  have h1 : 1 ≤ (4 * η ^ 2 * b) * (30 * η₁ * c) := by
    have h1a : (0 : ℝ) ≤ 1 := by norm_num
    have hb' : (0 : ℝ) ≤ 4 * η ^ 2 * b := by nlinarith [hη, hb]
    have := mul_le_mul hb hc h1a hb'
    linarith [this]
  have h120 : 0 < 120 * η ^ 2 * η₁ := by positivity
  have hbc_ge : 1 / (120 * η ^ 2 * η₁) ≤ b * c := by
    rw [div_le_iff₀ h120]
    nlinarith [h1]
  have h2 : (d1 * d2) * d3 ≤ Cb * C₁' := mul_le_mul hd he hd3 (le_of_lt hCb)
  have h3 : A * (b * c) ≤ Cb * C₁' := by rw [hE]; exact h2
  have h4 : A ≤ Cb * C₁' / (b * c) := by
    rw [le_div_iff₀ hbc0]
    exact h3
  have hA : (0 : ℝ) < 1 / (120 * η ^ 2 * η₁) := by positivity
  have hinv : (b * c)⁻¹ ≤ 120 * η ^ 2 * η₁ := by
    have h := one_div_le_one_div_of_le hA hbc_ge
    simpa [one_div] using h
  have h5 : Cb * C₁' / (b * c) ≤ Cb * C₁' * (120 * η ^ 2 * η₁) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have h7 : 120 * η ^ 2 * η₁ * Cb * C₁' ≤ 10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁ := by
    have hthin : 120 * C₁' ≤ 10 ^ 6 * (C₁' + 1) := by nlinarith [hC₁']
    have := mul_le_mul_of_nonneg_right hthin (by positivity : (0 : ℝ) ≤ Cb * η ^ 2 * η₁)
    nlinarith [this]
  have := le_trans h4 h5
  linarith [this, h7]

theorem Isl_deriv (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    ∀ z ∈ V.Isl j k n,
      ‖deriv (V.f ^[N]) z‖ ≤ 10 ^ 6 * V.Cb * (V.C₁' + 1) * V.η ^ 2 * V.η₁ := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨hwSrc, -⟩ := hw
  -- write the source point as the explicit lift of a point of the fibre
  have hS : w ∈ V.lift j k n '' V.fib j k := by
    rw [← V.SrcC_eq_image_lift (k := k) hSm]
    exact hwSrc
  obtain ⟨u, hu, hulift⟩ := hS
  have hSrcLift : V.lift j k n u ∈ V.SrcC j k n := by rw [hulift]; exact hwSrc
  have hRawLift : V.lift j k n u ∈ V.Raw j k := hSrcLift.1
  have huOf : V.uOf (V.s * MandelDim.piExp (V.lift j k n u)) = u := by
    rw [V.lift_piExp (n := n) hSm hu, ← mul_div_assoc, mul_div_cancel_left₀ _ V.hs]
    exact V.uOf_unique (hSm hu) rfl
  have hmem : ((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ) ∈ V.W 0 := by
    have h := V.wOfCell_target_mem_Raw hj hSm hRawLift
    rwa [huOf] at h
  rw [← hulift]
  -- the derivative relation, and its norm form
  have hE := deriv_relation V hj hSm hn hN hu
  have hEnorm := congrArg (fun t : ℂ => ‖t‖) hE
  simp only [norm_mul] at hEnorm
  have hE' : ‖deriv (V.f ^[N]) (V.P₀.φ (V.lift j k n u))‖
        * (‖deriv V.P₀.φ (V.lift j k n u)‖ * ‖deriv (V.lift j k n) u‖)
      = (‖deriv V.P₀.φ (V.wOf (((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ)))‖
          * ‖deriv V.wOf (((fun x : ℂ => V.R x - V.β)^[j] u) - ((k : ℤ) : ℂ))‖)
        * ‖deriv ((fun x : ℂ => V.R x - V.β)^[j]) u‖ := by
    linarith [hEnorm]
  refine Isl_deriv_arith V.hηpos V.hη₁pos V.hCbpos V.hC₁'pos hE'
    (V.one_le_four_eta_sq_mul_deriv_phi₀ hSm hn hSrcLift)
    (V.one_le_thirty_eta₁_mul_deriv_lift hSm hu)
    (V.target_bound hmem)
    (le_of_lt (deriv_iterate_shift_le V.hIsChain V.hReq hu))
    (norm_nonneg _)

end

end Work.Repel
