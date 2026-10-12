import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Basic.exists_graphPoint_close
import Submission.Work.BoseSym.Bridge.ae_eq_zero_off_of_setIntegral_eq_zero
import Submission.Work.BoseSym.Bridge.continuous_setIntegral_Lp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — elements of the energy space vanish a.e. outside the box

The energy space `Hsub N L` is, by definition, the closure in the ambient space
`Amb N = L²(Conf N) × ∏_j L²(Conf N)` of the (linear span of the) graph points
`F ↦ (F, ∇F)` of smooth test functions `F` supported in the open box
`openBox N L ⊆ box N L` (see `Hsub_eq_closure`).

Hence the function part of every element of `Hsub N L` vanishes almost
everywhere outside the closed box `box N L`.  The proof has three steps, all
carried out for the concrete measure `volC N = volume` and the measurable set
`S = box N L`:

* the set `K` of ambient elements whose function part has vanishing integral
  over every measurable subset of `Sᶜ` of finite measure is closed — it is an
  intersection of sets of the form `{q | ∫_A q.1 = 0}`, each the preimage of
  `{0}` under the continuous linear functional `q ↦ ∫_A q.1`
  (`continuous_setIntegral_Lp`);
* the graph point of a test function lies in `K`, because that function
  vanishes identically off `openBox N L ⊆ box N L`;
* a closed set containing the range of `graphPoint` contains its closure, and
  the conclusion converts the integral information into an a.e. statement
  (`ae_eq_zero_off_of_setIntegral_eq_zero`).
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

/-! ## The proof -/

/-- A smooth test function supported in the open box vanishes outside the
closed box (the support of `F` is contained in `tsupport F ⊆ openBox N L`). -/
lemma testSub_apply_eq_zero_of_notMem_box {N : ℕ} {L : ℝ} (F : testSub N L) {x : Conf N}
    (hx : x ∉ BoseGases.box N L) : (F : Conf N → ℝ) x = 0 := by
  by_contra hne
  have hx_supp : x ∈ Function.support (F : Conf N → ℝ) := Function.mem_support.mpr hne
  exact hx (openBox_subset_box (F.2.2 (subset_tsupport (F : Conf N → ℝ) hx_supp)))

theorem ae_eq_zero_off_box {N : ℕ} {L : ℝ} (p : Work.BoseSym.Hsub N L) :
    ∀ᵐ x ∂(Work.BoseSym.volC N), x ∉ BoseGases.box N L →
      ((p : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x = 0 := by
  set S : Set (Conf N) := BoseGases.box N L with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact box_measurable N L
  -- the "good" set of ambient elements
  let K : Set (Amb N) := {q : Amb N | ∀ A : Set (Conf N), MeasurableSet A →
      volC N A < ⊤ → A ⊆ Sᶜ →
      ∫ x in A, ((q : Amb N).1 : Conf N → ℝ) x ∂(volC N) = 0}
  -- `K` is closed
  have hKclosed : IsClosed K := by
    have hKeq : K = ⋂₀ {T : Set (Amb N) | ∃ A : Set (Conf N), MeasurableSet A ∧
        volC N A < ⊤ ∧ A ⊆ Sᶜ ∧
        T = {q : Amb N | ∫ x in A, ((q : Amb N).1 : Conf N → ℝ) x ∂(volC N) = 0}} := by
      ext q
      constructor
      · intro hq
        rw [Set.mem_sInter]
        rintro T ⟨A, hA, hμA, hAsub, rfl⟩
        exact hq A hA hμA hAsub
      · intro hq A hA hμA hAsub
        rw [Set.mem_sInter] at hq
        exact hq _ ⟨A, hA, hμA, hAsub, rfl⟩
    rw [hKeq]
    refine isClosed_sInter ?_
    rintro T ⟨A, hA, hμA, -, rfl⟩
    exact isClosed_eq
      ((continuous_setIntegral_Lp (μ := volC N) (s := A) hA hμA.ne).comp continuous_fst)
      continuous_const
  -- the graph points of test functions belong to `K`
  have hrange : Set.range (graphPoint N L) ⊆ K := by
    rintro q ⟨F, rfl⟩ A _hA _hμA hAsub
    simp only [graphPoint]
    set hmem : MemLp (F : Conf N → ℝ) 2 (volC N) :=
      memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [MemLp.coeFn_toLp hmem] with x hx hxA
    rw [hx]
    exact testSub_apply_eq_zero_of_notMem_box F (fun hbox => hAsub hxA hbox)
  -- hence the whole energy space is contained in `K`
  have hpK : (p : Amb N) ∈ K := by
    refine closure_minimal hrange hKclosed ?_
    rw [← Work.BoseSym.Basic.Hsub_eq_closure N L]
    exact p.2
  -- convert the integral information on `Sᶜ` into an a.e. statement
  have hmain : ∀ᵐ x ∂(volC N), x ∉ S →
      ((p : Amb N).1 : Conf N → ℝ) x = 0 :=
    ae_eq_zero_off_of_setIntegral_eq_zero (μ := volC N) hSmeas
      (f := ((p : Amb N).1 : Conf N → ℝ))
      (fun s _hs hμs => integrableOn_Lp_of_measure_ne_top ((p : Amb N).1)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμs.ne)
      (fun A hA hμA hAsub => hpK A hA hμA hAsub)
  simpa only [hS] using hmain

end Work.BoseSym.Bridge
