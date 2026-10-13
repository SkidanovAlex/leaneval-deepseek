/-
# `PiecesHkOpen` — the `ℋ⁴`-honesty table of the §8 chunks, in the honest vocabulary

`Work.FTS.OpenPkg.PiecesHk` is the 31-conjunct table the primed `IP`-interface
(`N4Extra'`) consumes: the `HkMem α 4` honesty of the 27 pieces, of `AK`, of the two
blocks `N₀`, `N` of `gRHS`, and of `D_z g`.

* the 27 pieces: the `HkMem` conjunct of the corresponding row lemma of this chapter
  (`Open/Row1` … `Open/Row26`);
* `AK`: `Rak`;
* the two blocks: build `Work.FTS.OpenPkg.Good` (i.e. `C⁴` on the open quadrant *and*
  honest) for every summand — the `C⁴` half is `OpenPkg/Pieces4.lean` from `FourFactors`,
  the honesty half is the row — add them with `Good.add`, and transfer along the exact split
  (`Open/Splits`) by `Good.of_eqOn_Qd`;
* `D_z g`: `CoercivityFix.QuadPorts.HkMem_Dz_quad` from `GalClass` (`RegQ α 6 g`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.VocabO2
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
import Submission.Work.FTS.Nonlinear.Open.Splits

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
set_option linter.unusedVariables false

/-- The `ℋ⁴`-honesty table `PiecesHk` of the §8 chunks, from the rows of this chapter. -/
theorem PiecesHkOpen (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.OpenPkg.PiecesHk α g Φs Φg := by
  intro α g Φs Φg hα hα1 hαα₂ hg hs hell
  have hsp : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
  have hFF : Work.FTS.OpenPkg.FourFactors α g Φs Φg :=
    Work.FTS.OpenPkg.fourFactors_of_gal hα hα1 hg hs.toStarPkgo hell
  have hsq : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hg.reg.2.1
  obtain ⟨hspl0, hspl, _hNs⟩ := Splits IP hN hE hα hα1 hαα₂ hg hs hell
  -- ## the honesty of the 27 pieces
  have hp1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) := by
    obtain ⟨_, _, hh⟩ := Row1 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) := by
    obtain ⟨_, _, hh⟩ := Row2 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) := by
    obtain ⟨_, _, hh⟩ := Row3 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) := by
    obtain ⟨_, _, hh⟩ := Row4 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) := by
    obtain ⟨_, _, hh⟩ := Row5 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) := by
    obtain ⟨_, _, hh⟩ := Row6 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp7 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) := by
    obtain ⟨_, _, hh⟩ := Row7 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp8 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1gg α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row8 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp9 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1gs α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row9 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp10 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1sg α Φs g) := by
    obtain ⟨_, _, hh⟩ := Row10 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp11 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) := by
    obtain ⟨_, _, hh⟩ := Row11 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp12 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gg α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row12 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp13 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gs α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row13 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp14 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2sg α Φs g) := by
    obtain ⟨_, _, hh⟩ := Row14 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp15 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2ss α Φs) := by
    obtain ⟨_, _, hh⟩ := Row15 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp16 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3gg α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row16 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp17 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3gs α g Φg) := by
    obtain ⟨_, _, hh⟩ := Row17 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp18 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3sg α Φs g) := by
    obtain ⟨_, _, hh⟩ := Row18 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp19 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3ss α Φs) := by
    obtain ⟨_, _, hh⟩ := Row19 IP hN hE
    exact (hh hα hα1 hαα₂ hg hs hell).1
  have hp20 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gg α g) := by
    obtain ⟨_, _, hh⟩ := Row20 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp21 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gs α g) := by
    obtain ⟨_, _, hh⟩ := Row21 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp22 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4sg α g) := by
    obtain ⟨_, _, hh⟩ := Row22 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp23 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4ss α) := by
    obtain ⟨_, _, hh⟩ := Row23 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp24 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gg g) := by
    obtain ⟨_, _, hh⟩ := Row24 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp25 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gs α g) := by
    obtain ⟨_, _, hh⟩ := Row25 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hp26 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5sg α g) := by
    obtain ⟨_, _, hh⟩ := Row25 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).2.1
  have hp27 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5ss α) := by
    obtain ⟨_, _, hh⟩ := Row26 IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1

  -- ## `Good` for each piece (C^4 from `FourFactors`, honesty from the rows)
  have hg1 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N0fix α) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N0fix hFF, hp1⟩
  have hg2 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N03g α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N03g hFF, hp2⟩
  have hg3 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N04aF α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N04aF hFF, hp3⟩
  have hg4 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N04bF α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N04bF hFF, hp4⟩
  have hg5 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N05aF α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N05aF hFF, hp5⟩
  have hg6 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N05bF α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N05bF hFF, hp6⟩
  have hg7 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N06F α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N06F hFF, hp7⟩
  have hg8 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1gg α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N1gg hFF, hp8⟩
  have hg9 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1gs α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N1gs hFF, hp9⟩
  have hg10 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1sg α Φs g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N1sg hFF, hp10⟩
  have hg11 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N1ss α Φs) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N1ss hFF, hp11⟩
  have hg12 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2gg α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N2gg hFF, hp12⟩
  have hg13 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2gs α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N2gs hFF, hp13⟩
  have hg14 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2sg α Φs g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N2sg hFF, hp14⟩
  have hg15 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N2ss α Φs) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N2ss hFF, hp15⟩
  have hg16 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3gg α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N3gg hFF, hp16⟩
  have hg17 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3gs α g Φg) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N3gs hFF, hp17⟩
  have hg18 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3sg α Φs g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N3sg hFF, hp18⟩
  have hg19 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N3ss α Φs) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N3ss hFF, hp19⟩
  have hg20 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4gg α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N4gg hFF, hp20⟩
  have hg21 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4gs α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N4gs hFF, hp21⟩
  have hg22 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4sg α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N4sg hFF, hp22⟩
  have hg23 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N4ss α) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N4ss hFF, hp23⟩
  have hg24 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5gg g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N5gg hFF, hp24⟩
  have hg25 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5gs α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N5gs hFF, hp25⟩
  have hg26 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5sg α g) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N5sg hFF, hp26⟩
  have hg27 : Work.FTS.OpenPkg.Good α (Work.FTS.Nonlin.N5ss α) :=
    ⟨Work.FTS.OpenPkg.contDiffOn_four_N5ss hFF, hp27⟩

  -- ## the `N₀` block
  have hgs0 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ) + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
        + Work.FTS.Nonlin.N05bF α g z θ) + Work.FTS.Nonlin.N06F α g z θ) :=
    ((((hg2.add hg3).add hg4).add hg5).add hg6).add hg7
  have hgN0 : Work.FTS.OpenPkg.Good α
      (fun z θ => Work.FTS.Nonlin.N0fix α z θ + (((((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ) + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
        + Work.FTS.Nonlin.N05bF α g z θ) + Work.FTS.Nonlin.N06F α g z θ)) :=
    hg1.add hgs0
  have hpN0 : Work.Spaces.HkMem α 4
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g) :=
    (hgN0.of_eqOn_Qd (fun z θ hq => (hspl0 z θ hq).symm)).2

  -- ## the `N` block
  have hgs1 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ) + Work.FTS.Nonlin.N1sg α Φs g z θ) + Work.FTS.Nonlin.N1ss α Φs z θ) :=
    ((hg8.add hg9).add hg10).add hg11
  have hgs2 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ) + Work.FTS.Nonlin.N2sg α Φs g z θ) + Work.FTS.Nonlin.N2ss α Φs z θ) :=
    ((hg12.add hg13).add hg14).add hg15
  have hgs3 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ) + Work.FTS.Nonlin.N3sg α Φs g z θ) + Work.FTS.Nonlin.N3ss α Φs z θ) :=
    ((hg16.add hg17).add hg18).add hg19
  have hgs4 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ) + Work.FTS.Nonlin.N4sg α g z θ) + Work.FTS.Nonlin.N4ss α z θ) :=
    ((hg20.add hg21).add hg22).add hg23
  have hgs5 : Work.FTS.OpenPkg.Good α
      (fun z θ => ((Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ) + Work.FTS.Nonlin.N5sg α g z θ) + Work.FTS.Nonlin.N5ss α z θ) :=
    ((hg24.add hg25).add hg26).add hg27
  have hgN : Work.FTS.OpenPkg.Good α
      (fun z θ => ((((Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ) + Work.FTS.Nonlin.N1sg α Φs g z θ) + Work.FTS.Nonlin.N1ss α Φs z θ) + (((Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ) + Work.FTS.Nonlin.N2sg α Φs g z θ) + Work.FTS.Nonlin.N2ss α Φs z θ) + (((Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ) + Work.FTS.Nonlin.N3sg α Φs g z θ) + Work.FTS.Nonlin.N3ss α Φs z θ) + (((Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ) + Work.FTS.Nonlin.N4sg α g z θ) + Work.FTS.Nonlin.N4ss α z θ) + (((Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ) + Work.FTS.Nonlin.N5sg α g z θ) + Work.FTS.Nonlin.N5ss α z θ))) :=
    ((((hgs1.add hgs2).add hgs3).add hgs4).add hgs5)
  have hpN : Work.Spaces.HkMem α 4
      (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) :=
    (hgN.of_eqOn_Qd (fun z θ hq => (hspl z θ hq).symm)).2

  -- ## `AK` and `D_z g`
  have hpAK : Work.Spaces.HkMem α 4 (Work.Construction.AK α) := by
    obtain ⟨_, _, hh⟩ := Rak IP hN hE
    exact (hh hα hα1 hαα₂ hg hsp hell).1
  have hpDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hsq
      (Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsq hmem6)

  exact ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hpAK, hpN0, hpN, hpDz⟩

end Work.FTS.Nonlinear.Open
