import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELNest.bAng_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.ELAssembly.z1_near_Q_of`

The parabolic point `z₁` lies in the **near side** of every level-`n` pair of the nest at `z₁`
(the field `z1_near_Q` of `Work.ELAssembly.CertGeometry`), the only hypothesis on the pair being
that it does *not* land at `z₁`.

The proof is purely angular.  The level-`n` pair `Qp n` has angles `(βₙ', βₙ + 1)` with

* `βₙ ∈ (0, α₁)` and `βₙ' ∈ (α₂, β₀']` (`Work.ELNest.bAng_range`),

so its **near arc** — the counterclockwise arc from `βₙ + 1` to `βₙ' + 1` — contains the
integer translate `α₁ + 1` of the first root angle.  Hence

* the whole ray `R(α₁ + 1) = R(α₁)` lies in `pairSideNear (Qp n)`
  (`Work.ELTop.paramRay_subset_pairSideNear`), so `z₁`, being the landing point of `R(α₁)`,
  lies in the closure of `pairSideNear (Qp n)`;
* `z₁` is not on the pair curve `pairCurve (Qp n)`: it is not the landing point (`hne`) and it lies
  in the filled Julia set `K c` (`Work.ELTop.landsN_mem_K`), while the two rays avoid `K c`.

Since `pairSideNear (Qp n)` is open with frontier the pair curve (`pairSides_decomposition`),
membership in the closure and not in the frontier gives membership.
-/

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

/-- **`z₁` lies in the near side of the level-`n` pair** of the nest at `z₁`.  The pair's near arc
contains the root angle `α₁`, and the pair does not land at `z₁`. -/
theorem z1_near_Q_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) (hJ : Work.Top.JordanForm) (n : ℕ) (hne : (N.Qp n).y ≠ d.z₁) : d.z₁ ∈ Work.EL.pairSideNear (N.Qp n) := by
  -- the angle range of the two level-`n` angles, in the `Work.EL` normalisation of the constants
  have hrange := Work.ELNest.bAng_range n
  have hα1 : Work.ELNest.alpha1 = Work.EL.alpha1 := rfl
  have hα2 : Work.ELNest.alpha2 = Work.EL.alpha2 := rfl
  rw [hα1, hα2] at hrange
  have hb1 : Work.ELNest.bAng' n < 1 := by
    have h : Work.ELNest.beta0' < 1 := by norm_num [Work.ELNest.beta0']
    linarith [hrange.2.2, h]
  have ha1 : Work.EL.alpha1 < Work.EL.alpha2 := by
    rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
  have h12 : Work.ELNest.bAng n < Work.ELNest.bAng' n :=
    lt_trans hrange.1.2 (lt_trans ha1 hrange.2.1)
  -- `α₁ + 1` lies in the near arc `(βₙ + 1, βₙ' + 1)`
  have hd1 : 0 < Work.EL.alpha1 - Work.ELNest.bAng n := by linarith [hrange.1.2]
  have hd2 : Work.EL.alpha1 - Work.ELNest.bAng n < 1 := by
    have h : Work.EL.alpha1 < 1 := by norm_num [Work.EL.alpha1]
    linarith [hrange.1.1, h]
  have hf1 : Int.fract (Work.EL.alpha1 - Work.ELNest.bAng n) = Work.EL.alpha1 - Work.ELNest.bAng n :=
    Int.fract_eq_self.mpr ⟨le_of_lt hd1, hd2⟩
  have hd3 : 0 < Work.ELNest.bAng' n - Work.ELNest.bAng n := by linarith [h12]
  have hd4 : Work.ELNest.bAng' n - Work.ELNest.bAng n < 1 := by linarith [hb1, hrange.1.1]
  have hf2 : Int.fract (Work.ELNest.bAng' n - Work.ELNest.bAng n)
      = Work.ELNest.bAng' n - Work.ELNest.bAng n :=
    Int.fract_eq_self.mpr ⟨le_of_lt hd3, hd4⟩
  have hA : Work.EL.InArc (Work.EL.alpha1 + 1) (N.Qp n).b ((N.Qp n).a + 1) := by
    rw [N.Qpb n, N.Qpa n]
    unfold Work.EL.InArc Work.EL.arcLen
    rw [show Work.EL.alpha1 + 1 - (Work.ELNest.bAng n + 1) = Work.EL.alpha1 - Work.ELNest.bAng n by ring,
        show Work.ELNest.bAng' n + 1 - (Work.ELNest.bAng n + 1) = Work.ELNest.bAng' n - Work.ELNest.bAng n by ring,
        hf1, hf2]
    exact ⟨hd1, by linarith [ha1, hrange.2.1]⟩
  -- the whole ray of angle `α₁ + 1` lies in the near side
  have hray : Work.EL.paramRay d.hN (Work.EL.alpha1 + 1) ⊆ Work.EL.pairSideNear (N.Qp n) :=
    Work.ELTop.paramRay_subset_pairSideNear d.hN hJ (N.Qp n) hA
  have hland : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  -- `z₁` lies in the closure of the near side
  have hz1_cl : d.z₁ ∈ closure (Work.EL.paramRay d.hN (Work.EL.alpha1 + 1)) := by
    rw [Work.ELTop.paramRay_add_one d.hN Work.EL.alpha1]
    exact mem_closure_of_tendsto hland (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_mem_paramRay d.hN ht)
  -- `z₁` does not lie on the pair curve
  have hz1K : d.z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN hland
  have hz1_notcurve : d.z₁ ∉ Work.EL.pairCurve (N.Qp n) := by
    intro hc
    rw [Work.EL.mem_pairCurve_iff] at hc
    rcases hc with hpa | hy | hpb
    · exact Work.EL.paramRay_subset_compl d.hN (N.Qp n).a hpa hz1K
    · exact hne hy.symm
    · exact Work.EL.paramRay_subset_compl d.hN (N.Qp n).b hpb hz1K
  -- the pair is non-degenerate, so its near side has the pair curve as frontier
  have hnd : Work.EL.arcLen (N.Qp n).a (N.Qp n).b ≠ 0 := by
    rw [N.Qpa n, N.Qpb n]
    unfold Work.EL.arcLen
    have hpos : 0 < Work.ELNest.bAng n + 1 - Work.ELNest.bAng' n := by linarith [hb1, hrange.1.1]
    have hlt1 : Work.ELNest.bAng n + 1 - Work.ELNest.bAng' n < 1 := by linarith [h12]
    rw [Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt1⟩]
    exact ne_of_gt hpos
  obtain ⟨-, -, -, hfrN⟩ := Work.ELTop.pairSides_decomposition d.hN hJ (N.Qp n) hnd
  have hSopen : IsOpen (Work.EL.pairSideNear (N.Qp n)) :=
    (Work.ELTop.isOpen_pairSide d.hN (N.Qp n)).2
  have hz1_clS : d.z₁ ∈ closure (Work.EL.pairSideNear (N.Qp n)) := closure_mono hray hz1_cl
  have hnotfr : d.z₁ ∉ frontier (Work.EL.pairSideNear (N.Qp n)) := by
    rw [hfrN]; exact hz1_notcurve
  rw [hSopen.frontier_eq] at hnotfr
  by_contra hmem
  exact hnotfr ⟨hz1_clS, hmem⟩

end Work.ELAssembly
