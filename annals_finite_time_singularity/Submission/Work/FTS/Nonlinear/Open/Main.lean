/-
# The honest (open-quadrant) row bundle of node N4 — `n4Rows2`

This is the *honest* form of the section-8 per-piece table, in the vocabulary the lead froze on
2026-10-04/06 (`Submission/Work/FTS/VocabO.lean`, `VocabO2.lean`, `OpenPkg/Defs.lean`,
`STARPKG_T2_LEAD.md`):

* the `IP`-level contract is `Work.FTS.OpenPkg.N4Extra'` (every clause carries the `ℋ⁴`-honesty
  `HkMem α 4` of its first argument), and the norm interface is `N4Norm'`;
* the elliptic packages are the open-quadrant `EllPkgGo` (N1) and `VocabO2.StarPkgo2` (N3);
* row 16 is at the **relaxed** rate `|IP (N3gg) g| ≤ K·X³` — `√α·X³` is *not* reachable
  (`STARPKG_T2_LEAD.md` section 1.6: `CoefTh 1 V(PhiTg) ~ α^-0.5X` is sharp), and
  `X³ ≤ α^-1.5X³` keeps the term inside `Pbd`'s budget;
* rows 10, 11, 14, 15, 18, 19 are stated over `StarPkgo2`: the frozen `StarPkgo` prices the star
  coefficients only by open-quadrant `D`-sups, which are blind to the behaviour at `z = 0` and to
  the angular decay, and those six rows are *false* with the frozen fields
  (`STARPKG_T2_LEAD.md` section 1.1 and the refutations listed there).

The five conjuncts are exactly the ingredients a `pairing_bound_open2`-style assembly consumes:
the three row groups, the three exact splits, and the `ℋ⁴`-honesty table.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Open.Row1
import Submission.Work.FTS.Nonlinear.Open.Row2
import Submission.Work.FTS.Nonlinear.Open.Row3
import Submission.Work.FTS.Nonlinear.Open.Row4
import Submission.Work.FTS.Nonlinear.Open.Row5
import Submission.Work.FTS.Nonlinear.Open.Row6
import Submission.Work.FTS.Nonlinear.Open.Row7
import Submission.Work.FTS.Nonlinear.Open.Row8
import Submission.Work.FTS.Nonlinear.Open.Row9
import Submission.Work.FTS.Nonlinear.Open.Row10
import Submission.Work.FTS.Nonlinear.Open.Row11
import Submission.Work.FTS.Nonlinear.Open.Row12
import Submission.Work.FTS.Nonlinear.Open.Row13
import Submission.Work.FTS.Nonlinear.Open.Row14
import Submission.Work.FTS.Nonlinear.Open.Row15
import Submission.Work.FTS.Nonlinear.Open.Row16
import Submission.Work.FTS.Nonlinear.Open.Row17
import Submission.Work.FTS.Nonlinear.Open.Row18
import Submission.Work.FTS.Nonlinear.Open.Row19
import Submission.Work.FTS.Nonlinear.Open.Row20
import Submission.Work.FTS.Nonlinear.Open.Row21
import Submission.Work.FTS.Nonlinear.Open.Row22
import Submission.Work.FTS.Nonlinear.Open.Row23
import Submission.Work.FTS.Nonlinear.Open.Row24
import Submission.Work.FTS.Nonlinear.Open.Row25
import Submission.Work.FTS.Nonlinear.Open.Row26
import Submission.Work.FTS.Nonlinear.Open.Rak
import Submission.Work.FTS.Nonlinear.Open.Rl0
import Submission.Work.FTS.Nonlinear.Open.Rl1
import Submission.Work.FTS.Nonlinear.Open.Rl2
import Submission.Work.FTS.Nonlinear.Open.Splits
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The context of this chapter: the flat form of `Work.FTS.VocabO2.Ctx2`. -/
def CtxO (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop :=
  0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ Work.FTS.Nonlin.GalClass α g ∧
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs ∧ Work.FTS.VocabO.EllPkgGo α Ce g Φg

/-- **The honest row bundle of node N4** (design 3.4--3.5, the paper's section 8 table). -/
theorem n4Rows2 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K₁ K₂ K₃ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ 0 < K₃ ∧
      (∀ {α : ℝ} {g Φs Φg : Fn}, CtxO α₂ Ci Ct Ce Cs α g Φs Φg →
        Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg) ∧
      (∀ {α : ℝ} {g Φs Φg : Fn}, CtxO α₂ Ci Ct Ce Cs α g Φs Φg →
        Work.FTS.VocabO2.NRows2 IP α K₂ g Φs Φg) ∧
      (∀ {α : ℝ} {g Φs Φg : Fn}, CtxO α₂ Ci Ct Ce Cs α g Φs Φg →
        Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg) ∧
      (∀ {α : ℝ} {g Φs Φg : Fn}, CtxO α₂ Ci Ct Ce Cs α g Φs Φg →
        Work.FTS.NonlinRows.SplitsData α g Φs Φg) ∧
      (∀ {α : ℝ} {g Φs Φg : Fn}, CtxO α₂ Ci Ct Ce Cs α g Φs Φg →
        Work.FTS.OpenPkg.PiecesHk α g Φs Φg) := by
  obtain ⟨K1, hK1, h1⟩ := Row1 IP hN hE
  obtain ⟨K2, hK2, h2⟩ := Row2 IP hN hE
  obtain ⟨K3, hK3, h3⟩ := Row3 IP hN hE
  obtain ⟨K4, hK4, h4⟩ := Row4 IP hN hE
  obtain ⟨K5, hK5, h5⟩ := Row5 IP hN hE
  obtain ⟨K6, hK6, h6⟩ := Row6 IP hN hE
  obtain ⟨K7, hK7, h7⟩ := Row7 IP hN hE
  obtain ⟨K8, hK8, h8⟩ := Row8 IP hN hE
  obtain ⟨K9, hK9, h9⟩ := Row9 IP hN hE
  obtain ⟨K10, hK10, h10⟩ := Row10 IP hN hE
  obtain ⟨K11, hK11, h11⟩ := Row11 IP hN hE
  obtain ⟨K12, hK12, h12⟩ := Row12 IP hN hE
  obtain ⟨K13, hK13, h13⟩ := Row13 IP hN hE
  obtain ⟨K14, hK14, h14⟩ := Row14 IP hN hE
  obtain ⟨K15, hK15, h15⟩ := Row15 IP hN hE
  obtain ⟨K16, hK16, h16⟩ := Row16 IP hN hE
  obtain ⟨K17, hK17, h17⟩ := Row17 IP hN hE
  obtain ⟨K18, hK18, h18⟩ := Row18 IP hN hE
  obtain ⟨K19, hK19, h19⟩ := Row19 IP hN hE
  obtain ⟨K20, hK20, h20⟩ := Row20 IP hN hE
  obtain ⟨K21, hK21, h21⟩ := Row21 IP hN hE
  obtain ⟨K22, hK22, h22⟩ := Row22 IP hN hE
  obtain ⟨K23, hK23, h23⟩ := Row23 IP hN hE
  obtain ⟨K24, hK24, h24⟩ := Row24 IP hN hE
  obtain ⟨K25, hK25, h25⟩ := Row25 IP hN hE
  obtain ⟨K26, hK26, h26⟩ := Row26 IP hN hE
  obtain ⟨Krak, hKrak, hrak⟩ := Rak IP hN hE
  obtain ⟨Krl0, hKrl0, hrl0⟩ := Rl0 IP hN hE
  obtain ⟨Krl1, hKrl1, hrl1⟩ := Rl1 IP hN hE
  obtain ⟨Krl2, hKrl2, hrl2⟩ := Rl2 IP hN hE
  set K₁ : ℝ := 1 + (K1 + K2 + K3 + K4 + K5 + K6 + K7) with hK₁def
  set K₂ : ℝ := 1 + (K8 + K9 + K10 + K11 + K12 + K13 + K14 + K15 + K16 + K17 + K18 + K19 + K20 + K21 + K22 + K23 + K24 + K25 + K26) with hK₂def
  set K₃ : ℝ := 1 + (Krak + Krl0 + Krl1 + Krl2) with hK₃def
  have hK₁pos : 0 < K₁ := by rw [hK₁def]; linarith [hK1, hK2, hK3, hK4, hK5, hK6, hK7]
  have hK₂pos : 0 < K₂ := by rw [hK₂def]; linarith [hK8, hK9, hK10, hK11, hK12, hK13, hK14, hK15, hK16, hK17, hK18, hK19, hK20, hK21, hK22, hK23, hK24, hK25, hK26]
  have hK₃pos : 0 < K₃ := by rw [hK₃def]; linarith [hKrak, hKrl0, hKrl1, hKrl2]
  refine ⟨K₁, K₂, K₃, hK₁pos, hK₂pos, hK₃pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hg, hs, hell⟩ := hctx
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsq : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hr12 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h32 : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα.le _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (h1 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (pow_nonneg hα.le 2))
    · exact le_trans (h2 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 2)))
    · exact le_trans (h3 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg hsq hX0))
    · exact le_trans (h4 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 3)))
    · exact le_trans (h5 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg hsq hX0))
    · exact le_trans (h6 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg hr12 (pow_nonneg hX0 3)))
    · exact le_trans (h7 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₁def]; linarith) (mul_nonneg hsq (pow_nonneg hX0 2)))
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hg, hs, hell⟩ := hctx
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsq : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hr12 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h32 : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα.le _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (h8 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hr12 (pow_nonneg hX0 2)))
    · exact le_trans (h9 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hsq hX0))
    · exact le_trans (h10 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hsq hX0))
    · exact le_trans (h11 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hα.le 2))
    · exact le_trans (h12 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hr12 (pow_nonneg hX0 3)))
    · exact le_trans (h13 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg h32 hX0))
    · exact le_trans (h14 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hsq (pow_nonneg hX0 2)))
    · exact le_trans (h15 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hα.le 2))
    · exact le_trans (h16 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hX0 3))
    · exact le_trans (h17 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg h32 hX0))
    · exact le_trans (h18 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg h32 (pow_nonneg hX0 2)))
    · exact le_trans (h19 hα hα1 hαα₂ hg hs hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hα.le 3))
    · exact le_trans (h20 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hr12 (pow_nonneg hX0 3)))
    · exact le_trans (h21 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg h32 hX0))
    · exact le_trans (h22 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hsq (pow_nonneg hX0 2)))
    · exact le_trans (h23 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hα.le 3))
    · exact le_trans (h24 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hX0 2))
    · exact le_trans (h25 hα hα1 hαα₂ hg hs.toStarPkgo hell).2.2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (mul_nonneg hsq hX0))
    · exact le_trans (h26 hα hα1 hαα₂ hg hs.toStarPkgo hell).2
        (mul_le_mul_of_nonneg_right (by rw [hK₂def]; linarith) (pow_nonneg hα.le 2))
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hg, hs, hell⟩ := hctx
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsq : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hbr : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      add_nonneg (add_nonneg (pow_nonneg hα.le 2) (mul_nonneg hsq hX0))
        (mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 2))
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans (hrak hα hα1 hαα₂ hg hs.toStarPkgo hell).2 (by rw [hK₃def]; linarith)
    · exact le_trans (hrl0 hα hα1 hαα₂ hg hs.toStarPkgo hell)
        (mul_le_mul_of_nonneg_right (by rw [hK₃def]; linarith) hbr)
    · exact le_trans (hrl1 hα hα1 hαα₂ hg hs.toStarPkgo hell)
        (mul_le_mul_of_nonneg_right (by rw [hK₃def]; linarith) hbr)
    · exact le_trans (hrl2 hα hα1 hαα₂ hg hs.toStarPkgo hell)
        (mul_le_mul_of_nonneg_right (by rw [hK₃def]; linarith) hX0)

  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hg, hs, hell⟩ := hctx
    exact Splits IP hN hE hα hα1 hαα₂ hg hs hell
  · intro α g Φs Φg hctx
    obtain ⟨hα, hα1, hαα₂, hg, hs, hell⟩ := hctx
    exact PiecesHkOpen IP hN hE hα hα1 hαα₂ hg hs hell

end Work.FTS.Nonlinear.Open
