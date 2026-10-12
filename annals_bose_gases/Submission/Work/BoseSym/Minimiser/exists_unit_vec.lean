import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseSym.Basic.exists_graphPoint_close
import Submission.Work.BoseSym.Bridge.pos_l2Sq_graphPoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Minimiser — a unit vector in the energy space

The energy space `Hsub N L` is the closure, in the ambient space
`Amb N = L²(Conf N) × ∏_j L²(Conf N)`, of the graph `F ↦ (F, ∇F)` of the smooth
test functions supported in the open box `openBox N L = (0,L)^{3N}`.

For `L > 0` the open box is nonempty, so there is a nonzero test function `F`
(`exists_testSub_ne_zero`: a smooth bump function supported in a small cube
around the centre of the box, normalised to `1` there).  Its graph point is a
nonzero vector of `Hsub N L`; more precisely, by `pos_l2Sq_graphPoint`, its
function part has strictly positive squared `L²` norm.  Rescaling the graph
point by the inverse of that norm then produces a vector of `Hsub N L` of
squared `L²` norm exactly `1`.

This is the nonemptiness of the unit sphere of the energy space, which the
minimiser arguments (`exists_minimiser`, `symMinimiser_exists`) require.
-/

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- For `0 < L` the open box `(0,L)^{3N}` is nonempty, and a smooth bump
function supported in it is a nonzero element of the test module `testSub N L`. -/
lemma exists_testSub_ne_zero {N : ℕ} {L : ℝ} (hL : 0 < L) :
    ∃ F : testSub N L, (F : Conf N → ℝ) ≠ 0 := by
  let c : Conf N := fun _ : Fin N => WithLp.toLp 2 (fun _ : Fin 3 => L / 2)
  have hc : c ∈ Submission.BoseGases.openBox N L := by
    intro i k
    dsimp [c, Submission.BoseGases.openBox]
    exact ⟨by linarith, by linarith⟩
  have hnhds : Submission.BoseGases.openBox N L ∈ 𝓝 c :=
    (Submission.BoseGases.openBox_isOpen (N := N) L).mem_nhds hc
  obtain ⟨f, hts, _hcs, hcd, _hrange, hfval⟩ :=
    exists_contDiff_tsupport_subset (E := Conf N) (s := Submission.BoseGases.openBox N L)
      (x := c) (n := ⊤) hnhds
  refine ⟨⟨f, hcd, hts⟩, ?_⟩
  intro hf0
  have h0 : f c = 0 := congrFun hf0 c
  rw [hfval] at h0
  exact one_ne_zero h0

/-- Scaling of `l2Sq` in the ambient space. -/
lemma l2Sq_smul_amb {N : ℕ} (a : ℝ) (q : Amb N) :
    l2Sq (a • q) = a ^ 2 * l2Sq q := by
  simp only [l2Sq, show (a • q).1 = a • q.1 from rfl, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

theorem exists_unit_vec (N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∃ p : Work.BoseSym.Hsub N L, Work.BoseSym.l2Sq (p : Work.BoseSym.Amb N) = 1 := by
  obtain ⟨F, hF⟩ := exists_testSub_ne_zero (N := N) (L := L) hL
  have hpos : 0 < l2Sq (graphPoint N L F) :=
    Work.BoseSym.Bridge.pos_l2Sq_graphPoint F hF
  have hmem : graphPoint N L F ∈ Hsub N L :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, rfl⟩)
  refine ⟨⟨(Real.sqrt (l2Sq (graphPoint N L F)))⁻¹ • graphPoint N L F,
      Submodule.smul_mem _ _ hmem⟩, ?_⟩
  rw [l2Sq_smul_amb, inv_pow, Real.sq_sqrt hpos.le]
  exact inv_mul_cancel₀ hpos.ne'

end

end Work.BoseSym.Minimiser
