import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# pureGamFamSix — critical-weight slot (B): the slice bound
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The slice bound -/






end Work.FTS.StrongPersist.N6Trans.SixRoute
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.starUop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.starUop`

The pointwise regularity of the coefficient `𝒰(Φ̃_*)/sin 2θ` of the self-similar vorticity
equation, in the form consumed by the regularity-export (`RXT`) cone: from the star package
`Work.FTS.VocabO2.StarPkgo2 α Cs Φs` (which contains the `𝒲^{4,∞}`-bound on the *weighted* field
`((z+1)/z)·𝒰(Φ̃_*)/sin 2θ`, the field `StarPkgo2.UszW`) one gets, for every `j + i ≤ 2`,

  `|D_z^j D_θ^i (𝒰(Φ̃_*)/sin 2θ)| ≤ C · max Cs 1 · α · min z 1`

on the open quadrant `(0,∞) × (0,π/2)`.

The `min z 1` factor (the vanishing at `z = 0⁺`) comes from writing

  `𝒰(Φ̃_*)/sin 2θ = A(z) · (((z+1)/z)·𝒰(Φ̃_*)/sin 2θ)`,   `A(z) = z/(1+z)`:

the mixed derivatives of the *unweighted* factor `A` are `≤ min z 1` in modulus (`A`,
`z/(1+z)²`, `z(1-z)/(1+z)³`, and `0` as soon as a `θ`-derivative is applied —
`Work.FTS_RegExport.RXT.starUopAux.Afun_mixed_le`), while the mixed derivatives of the weighted
field are uniformly bounded by its `𝒲^{4,∞}`-membership
(`Work.FTS.OpenPkg.mixed_le_WlInf_200`).  The Leibniz expansion on the open quadrant is
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` (`starUopAux.mixed_Afun_mul_le_aux` below is the
packaged two-factor bound, proved here to keep this file's cone `sorry`-free), and
`Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen` (locality of `mixed` on the open quadrant) is used
to replace `A·((z+1)/z·𝒰/sin 2θ)` by `𝒰/sin 2θ`: the two agree on the open quadrant.
-/

namespace Work.FTS_RegExport.RXT

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-- **The Leibniz bound for the `min z 1` factor `A(z) = z/(1+z)`.**  For `h` smooth on the open
quadrant and of class `𝒲^{4,∞}`, every mixed derivative `D_z^j D_θ^i (A·h)` with `j + i ≤ 2` is
bounded by `10^5 · |h|_𝒲 · min z 1` there.

`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed` expands `D_z^j D_θ^i (A·h)` into
`∑_{a ≤ i} ∑_{b ≤ j} C(i,a)C(j,b)·(D_z^b D_θ^a A)·(D_z^{j-b}D_θ^{i-a} h)`; each of the at most
`9` terms has a binomial factor `≤ 16`, an `A`-factor `≤ min z 1` (`Afun_mixed_le`) and an
`h`-factor `≤ 200 |h|_𝒲` (`Work.FTS.OpenPkg.mixed_le_WlInf_200`). -/
private theorem mixed_Afun_mul_le_aux : ∃ C : ℝ, 0 ≤ C ∧ ∀ {α : ℝ} {h : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen h →
    Work.Spaces.WlInfMem α 4 h →
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ : ℝ => z / (1 + z) * h z θ) z θ|
        ≤ C * Work.Spaces.WlInf α 4 h * min z 1 := by
  refine ⟨100000, by norm_num, ?_⟩
  intro α h hα hα1 hsmh hmem j i hji z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.FTS.OpenPkg.wlInf_nonneg_of_mem hmem
  have hm : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hWm : 0 ≤ Work.Spaces.WlInf α 4 h * min z 1 := mul_nonneg hW hm
  -- smoothness of the multiplier `A(z) = z/(1+z)` on the open quadrant
  have hsmA : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => z / (1 + z)) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 / (1 + p.1))
      Work.FTS.EllipticEst.Q0
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
        Work.FTS.EllipticEst.Q0 := contDiff_fst.contDiffOn.of_le le_top
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => 1 + p.1)
        Work.FTS.EllipticEst.Q0 := (contDiff_const.add contDiff_fst).contDiffOn.of_le le_top
    exact h1.div h2 (fun p hp => by
      have hp1 : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      linarith)
  -- the Leibniz expansion on the open quadrant
  have hleib := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i
    (fun z θ : ℝ => z / (1 + z)) h hsmA hsmh z θ hz hθ0 hθ1
  rw [hleib]
  -- the per-term bound, with `16 = 4 · 4` for the two binomials
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      |((i.choose a : ℝ) * (j.choose b : ℝ)) *
        (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
         Work.Spaces.mixed (j - b) (i - a) h z θ)|
        ≤ 16 * (200 * Work.Spaces.WlInf α 4 h * min z 1) := by
    intro a ha b hb
    have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hX : |Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ| ≤ min z 1 :=
      Work.FTS_RegExport.RXT.starUopAux.Afun_mixed_le b a (by omega) z θ hz hθ0 hθ1
    have hY : |Work.Spaces.mixed (j - b) (i - a) h z θ|
        ≤ 200 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hsmh hmem (by omega) hz hθ
    have hci : (i.choose a : ℝ) ≤ 4 := by
      have h1 : i.choose a ≤ 2 ^ i := Nat.choose_le_two_pow i a
      have h2 : 2 ^ i ≤ 4 := by
        calc 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega : i ≤ 2)
          _ = 4 := by norm_num
      exact_mod_cast le_trans h1 h2
    have hcj : (j.choose b : ℝ) ≤ 4 := by
      have h1 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
      have h2 : 2 ^ j ≤ 4 := by
        calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega : j ≤ 2)
          _ = 4 := by norm_num
      exact_mod_cast le_trans h1 h2
    have hcoef : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 16 := by
      have h1 : (0 : ℝ) ≤ (i.choose a : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
      nlinarith [hci, hcj, h1, h2]
    have hcoef0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
    simp only [abs_mul, abs_of_nonneg hcoef0]
    calc (i.choose a : ℝ) * (j.choose b : ℝ) *
          (|Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ| *
          |Work.Spaces.mixed (j - b) (i - a) h z θ|)
        ≤ 16 * (min z 1 * (200 * Work.Spaces.WlInf α 4 h)) :=
          mul_le_mul hcoef (mul_le_mul hX hY (abs_nonneg _) hm)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 16 * (200 * Work.Spaces.WlInf α 4 h * min z 1) := by ring
  have hK0 : (0 : ℝ) ≤ 16 * (200 * Work.Spaces.WlInf α 4 h * min z 1) := by
    have h1 : (0 : ℝ) ≤ 200 * Work.Spaces.WlInf α 4 h := by linarith
    exact mul_nonneg (by norm_num) (mul_nonneg h1 hm)
  -- the two nested sum bounds
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
        |((i.choose a : ℝ) * (j.choose b : ℝ)) *
          (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
           Work.Spaces.mixed (j - b) (i - a) h z θ)|)
        ≤ 3 * (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1)) := by
    intro a ha
    refine le_trans (Finset.sum_le_card_nsmul (Finset.range (j + 1)) _
      (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1)) (fun b hb => hterm a ha b hb)) ?_
    rw [Finset.card_range, nsmul_eq_mul]
    have hj : ((j + 1 : ℕ) : ℝ) ≤ 3 := by
      have h : j + 1 ≤ 3 := by omega
      exact_mod_cast h
    nlinarith [hK0]
  have houter : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        |((i.choose a : ℝ) * (j.choose b : ℝ)) *
          (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
           Work.Spaces.mixed (j - b) (i - a) h z θ)|)
        ≤ 9 * (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1)) := by
    refine le_trans (Finset.sum_le_sum hinner) ?_
    refine le_trans (Finset.sum_le_card_nsmul (Finset.range (i + 1)) _
      (3 * (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1))) (fun a _ => le_rfl)) ?_
    rw [Finset.card_range, nsmul_eq_mul]
    have hi : ((i + 1 : ℕ) : ℝ) ≤ 3 := by
      have h : i + 1 ≤ 3 := by omega
      exact_mod_cast h
    have h3K : (0 : ℝ) ≤ 3 * (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1)) := by
      linarith [hK0]
    nlinarith [hi, h3K]
  calc |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ)) *
            (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
             Work.Spaces.mixed (j - b) (i - a) h z θ)|
      ≤ ∑ a ∈ Finset.range (i + 1), |∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ)) *
            (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
             Work.Spaces.mixed (j - b) (i - a) h z θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ)) *
            (Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ *
             Work.Spaces.mixed (j - b) (i - a) h z θ)| :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 9 * (16 * (200 * Work.Spaces.WlInf α 4 h * min z 1)) := houter
    _ ≤ 100000 * Work.Spaces.WlInf α 4 h * min z 1 := by nlinarith [hWm]

theorem starUop {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)) z θ|
        ≤ C * (max Cs 1 * α) * min z 1 := by
  obtain ⟨C0, hC0nn, hC0⟩ := mixed_Afun_mul_le_aux
  refine ⟨C0, hC0nn, ?_⟩
  intro j i hji z θ hz hθ0 hθ1
  -- smoothness of `Φ̃_*`
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hS.smooth).1
  -- the weighted field `H = ((z+1)/z)·𝒰(Φ̃_*)/sin 2θ` and its `𝒲^{4,∞}`-data
  have hsmH : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ))) :=
    (Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α
      (Work.FTS.Nonlin.PhiTs α Φs) hsmΨ).2.2.2.2.1
  have hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ))) :=
    hS.UszW.1
  have hWle : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)))
      ≤ max Cs 1 * α :=
    le_trans hS.UszW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  -- the pointwise identity `𝒰/sin 2θ = A·H` on the open quadrant
  have hEqOn : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)))
      (Function.uncurry (fun z θ : ℝ => z / (1 + z) * ((z + 1) / z *
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)))))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hz', -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h1 : (p.1 : ℝ) ≠ 0 := ne_of_gt hz'
    have h2 : (1 + p.1 : ℝ) ≠ 0 := by linarith
    have hcoef : p.1 / (1 + p.1) * ((p.1 + 1) / p.1) = 1 := by
      rw [div_mul_div_comm, show (p.1 : ℝ) * (p.1 + 1) = (1 + p.1) * p.1 from by ring]
      exact div_self (mul_ne_zero h2 h1)
    have hgoal : ∀ a : ℝ, a = p.1 / (1 + p.1) * ((p.1 + 1) / p.1 * a) := by
      intro a
      rw [← mul_assoc]
      simp [hcoef]
    simp only [Function.uncurry]
    exact hgoal _
  -- transfer along the open-quadrant agreement, then apply the Leibniz bound
  rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩) j i]
  refine le_trans (hC0 hα hα1 hsmH hmem j i hji z θ hz hθ0 hθ1) ?_
  have hmin : 0 ≤ min z 1 := le_min hz.le zero_le_one
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWle hC0nn) hmin

end Work.FTS_RegExport.RXT
end
