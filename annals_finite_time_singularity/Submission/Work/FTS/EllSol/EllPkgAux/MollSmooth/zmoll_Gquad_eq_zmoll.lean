/-
# `Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll`

The double mollification `zmoll` only probes the datum `G` near the closed quadrant
`[0,π/2]` in the angular variable: the angular kernel `sKer ε` has support of radius `ε ≤ 1/2`,
and the doubly-odd extension `Qext` reflects values at `-s` (for `s < 0`) or at `π - s`
(for `s > π/2`) back into `(0, π/2)`.  Consequently, replacing `G` by its *quadrant cutoff*
`Gquad G` (which is `G` inside `(0,π/2)` and `0` outside) leaves `zmoll` unchanged, *provided*
`G` vanishes on the two boundary lines `θ = 0` and `θ = π/2` — those two lines are the only
places where `Gquad G` differs from `G` on the range that is actually probed.

The proof is pointwise in the outer (`t`- or `z`-) variable and reduces to the single
statement that `Qext (Gquad G) = Qext G` on the window `(-π/2, π)`, which is where all the
`s`-arguments of the angular convolution live when `θ ∈ (-1, π/2+1)` and `ε ≤ 1/2`.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about `Gquad` and `Qext` -/

/-- `Gquad G` agrees with `G` on the *open* quadrant. -/
lemma Gquad_eq_self_of_mem {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.EllPkgAux.Gquad G z θ = G z θ := by
  rw [Work.FTS.EllSol.EllPkgAux.Gquad, if_pos h]

/-- `Gquad G` agrees with `G` on the *closed* quadrant when `G` vanishes on the two boundary
lines (at `θ = 0` both `G` and `Gquad G` are `0`, and likewise at `θ = π/2`). -/
lemma Gquad_eq_self_of_mem_Icc (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) {z s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.EllPkgAux.Gquad G z s = G z s := by
  rcases lt_or_eq_of_le hs.1 with h | h
  · rcases lt_or_eq_of_le hs.2 with h2 | h2
    · exact Gquad_eq_self_of_mem ⟨h, h2⟩
    · rw [h2, hπ z, Work.FTS.EllSol.EllPkgAux.Gquad]
      norm_num [Set.mem_Ioo]
  · rw [← h, h0 z, Work.FTS.EllSol.EllPkgAux.Gquad]
    norm_num [Set.mem_Ioo]

/-- `Qext u z s = u z s` on the closed quadrant. -/
lemma Qext_of_mem_Icc (u : ℝ → ℝ → ℝ) (z s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = u z s := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_pos (Set.mem_Icc.mp hs)]

/-- `Qext` reflects a negative argument `s` to `-u z (-s)`. -/
lemma Qext_of_neg (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = -u z (-s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (by rintro ⟨h1, _⟩; linarith), if_pos hs]

/-- `Qext` reflects an argument `s > π/2` to `-u z (π - s)`. -/
lemma Qext_of_pihalf_lt (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = -u z (Real.pi - s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (by rintro ⟨_, h2⟩; linarith),
    if_neg (by intro h; linarith [Real.pi_pos])]

/-! ## Insensitivity of `Qext`, and hence of the angular mollification, to the cutoff -/

/-- On the window `(-π/2, π)` — the range of angular arguments that the mollification actually
probes — cutting `G` off outside the open quadrant does not change the doubly-odd extension
`Qext`, provided `G` vanishes on the two boundary lines. -/
lemma Qext_Gquad_eq_Qext (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (w s : ℝ)
    (hs : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi) :
    Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) w s
      = Work.FTS.EllSol.PkgK5.K5c.Qext G w s := by
  by_cases h1 : 0 ≤ s ∧ s ≤ Real.pi / 2
  · rw [Qext_of_mem_Icc _ w s (Set.mem_Icc.mpr h1),
      Qext_of_mem_Icc _ w s (Set.mem_Icc.mpr h1),
      Gquad_eq_self_of_mem_Icc G h0 hπ (Set.mem_Icc.mpr h1)]
  · rcases lt_or_ge s 0 with hneg | hge
    · rw [Qext_of_neg _ w s hneg, Qext_of_neg _ w s hneg,
        Gquad_eq_self_of_mem (G := G) (z := w)
          (show -s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨by linarith, by linarith [hs.1]⟩)]
    · have hsgt : Real.pi / 2 < s := lt_of_not_ge (fun hle => h1 ⟨hge, hle⟩)
      rw [Qext_of_pihalf_lt _ w s hsgt, Qext_of_pihalf_lt _ w s hsgt,
        Gquad_eq_self_of_mem (G := G) (z := w)
          (show Real.pi - s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from
            ⟨by linarith [hs.2], by linarith⟩)]

/-- The angular mollification is insensitive to the quadrant cutoff (for the validity window
`0 < ε ≤ 1/2` of the mollification and the strip `-1 < θ < π/2 + 1` on which it is used). -/
lemma thMoll_Gquad_eq (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (ε w θ : ℝ) (hεpos : 0 < ε) (hε : ε ≤ 1 / 2)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllSol.PkgK5.K5c.thMoll (Work.FTS.EllSol.EllPkgAux.Gquad G) ε w θ
      = Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ := by
  rw [Work.FTS.EllSol.PkgK5.K5c.thMoll, Work.FTS.EllSol.PkgK5.K5c.thMoll]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
        * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) w s
      = Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
        * Work.FTS.EllSol.PkgK5.K5c.Qext G w s
  by_cases h : |θ - s| < ε
  · have hmem : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi := by
      rw [abs_lt] at h
      constructor <;> linarith [Real.pi_gt_three, h.1, h.2, hθ.1, hθ.2, hε]
    rw [Qext_Gquad_eq_Qext G h0 hπ w s hmem]
  · have hzero : Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) = 0 :=
      Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hεpos (not_lt.mp h)
    rw [hzero, zero_mul, zero_mul]

/-- The double mollification is insensitive to the quadrant cutoff: no `z`-, `δ`- or
integrability hypothesis is needed, because the identity is pointwise in the outer (`t`)
variable. -/
theorem zmoll_Gquad_eq_zmoll (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (δ ε : ℝ) (hεpos : 0 < ε) (hε : ε ≤ 1 / 2)
    (z θ : ℝ) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ := by
  rw [Work.FTS.EllSol.PkgK5.K5c.zmoll, Work.FTS.EllSol.PkgK5.K5c.zmoll]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll (Work.FTS.EllSol.EllPkgAux.Gquad G) ε (Real.exp t) θ
      = Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll G ε (Real.exp t) θ
  rw [thMoll_Gquad_eq G h0 hπ ε (Real.exp t) θ hεpos hε hθ]

end Work.FTS.EllSol.EllPkgAux.MollSmooth
