import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart
import Submission.Work.WilE7.Auxiliary.rangePiEqTopOfRank
import Submission.Work.WilE7.Auxiliary.fibreFDeriv
import Submission.Work.WilE7.Auxiliary.fibreGradMemSpan2
import Submission.Work.WilE7.Auxiliary.fibreRowspanRankLe
import Submission.Work.WilE7.Auxiliary.fibreKerLe
import Submission.Work.WilE7.Auxiliary.constantOnLevelSet
import Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe
import Submission.Work.WilE7.Auxiliary.criticalLevelSetLocallyConst2
-- `Work.WilE7.Auxiliary.critMinorsVanishKer2` (the re-homed request) is being proved
-- independently in `Auxiliary/critMinorsVanishKer2.lean`; in the meantime this import takes the
-- lemma from its buildable copy `Auxiliary/critMinorsVanishKer.lean`, which declares the same
-- statement (under its originally requested name `Work.WilE7.Aux.critMinorsVanishKer`).
-- See `Submission/Work/WilE7/Aux/NOTES_critMinorsVanishKer.md`.
import Submission.Work.WilE7.Auxiliary.critMinorsVanishKer
import Submission.Work.WilE7.Auxiliary.fibreCritCond
import Submission.Work.WilE7.Auxiliary.fibreComponentLocallyLevelSet
import Submission.Work.WilE7.Auxiliary.fibreLevelSetEq

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter
open scoped Topology
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7

variable {p q : ℕ}

/-- The fibre map of a stratum over a base point. -/
def fibreMap (S : Stratum p q) (x : Fin p → ℝ) : (Fin q → ℝ) → (Fin S.j → ℝ) :=
  fun y a => eaEval S.X.c (S.h a) (Fin.append x y)

/-- The fibre map is analytic. -/
lemma analyticAt_fibreMap (S : Stratum p q) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    AnalyticAt ℝ (fibreMap S x) y := by
  unfold fibreMap
  refine AnalyticAt.pi (fun a => ?_)
  have happ : AnalyticAt ℝ (fun y' : Fin q → ℝ => Fin.append x y') y := by
    have h1 : (fun y' : Fin q → ℝ => Fin.append x y')
        = (Work.WilE9.Ift.appendCLM p q) ∘ (fun y' : Fin q → ℝ => (x, y')) := by
      funext y'
      simp [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]
    rw [h1]
    exact ((Work.WilE9.Ift.appendCLM p q).analyticAt (x, y)).comp
      ((analyticAt_const (v := x)).prod analyticAt_id)
  exact (Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) (Fin.append x y)).comp happ

/-- The range of the derivative of the fibre map of a `Good` stratum at a point of its set. -/
lemma range_fderiv_fibreMap (S : Stratum p q) (hGood : S.Good) (x : Fin p → ℝ) (y : Fin q → ℝ)
    (hy : Fin.append x y ∈ S.X.set) :
    (fderiv ℝ (fibreMap S x) y).range = ⊤ := by
  have hfirst : projFirst p q (Fin.append x y) = x := by
    funext i; simp [projFirst, Fin.append_left]
  have hsecond : projSnd p q (Fin.append x y) = y := by
    funext i; simp [projSnd, Fin.append_right]
  have h1 := Work.WilE7.Aux.fibreFDeriv S.X.c S.h (Fin.append x y)
  rw [hfirst, hsecond] at h1
  have h1' : fderiv ℝ (fibreMap S x) y
      = ContinuousLinearMap.pi (fun a : Fin S.j => (∑ l : Fin q,
          eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y) •
            (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) := h1
  rw [h1']
  exact Work.WilE7.Aux.rangePiEqTopOfRank
    (fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) (Fin.append x y))
    (Work.WilE5.Stratum.good_rank hGood hy)

/-- The fibre level set of `S'` is contained in the fibre level set of `S` near the base point. -/
lemma eventually_fibreMap_S'_eq_zero_imp (S S' : Stratum p q) (hGood' : S'.Good)
    (hGood : S.Good) (l : Fin q) (hsub : S'.X.set ⊆ (critSet S l).set) {z : Fin (p + q) → ℝ}
    (hzX' : z ∈ S'.X.set) :
    ∀ᶠ y in nhds (projSnd p q z),
      (∀ b, eaEval S'.X.c (S'.h b) (Fin.append (projFirst p q z) y) = 0) →
      (∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y) = 0) := by
  have hcont : Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
      (nhds (projSnd p q z)) (nhds z) := by
    have hfd : ContinuousAt (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
        (projSnd p q z) :=
      (Work.WilE7.Aux.hasFDerivAt_append_const p q (projFirst p q z) (projSnd p q z)).continuousAt
    have hfd2 : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z) = z :=
      append_projFirst_projSnd z
    change Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (nhds (projSnd p q z))
      (nhds ((fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z))) at hfd
    rwa [hfd2] at hfd
  have hev := hcont.eventually ((hGood' z hzX').2.2)
  have hbf : ∀ y : Fin q → ℝ,
      projFirst p q (Fin.append (projFirst p q z) y) = projFirst p q z := by
    intro y; funext i; simp [projFirst, Fin.append_left]
  filter_upwards [hev] with y hy
  intro hh
  have hmem : Fin.append (projFirst p q z) y ∈ S'.X.set := hy (hbf y) hh
  exact fun a => Work.WilE5.Stratum.good_eqs hGood (critSet_subset S l (hsub hmem)) a

theorem stratum_j_lt_of_subset_crit {p q : ℕ} (S S' : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hGood' : S'.Good) (l : Fin q) (hj : S.j < q) (hsub : S'.X.set ⊆ (Work.WilE7.critSet S l).set) (hwit : ∃ z ∈ S'.X.set, ∃ w ∈ WilkiesDesign.E.fiber (p := p) (q := q) S.X.set (WilkiesDesign.E.projFirst p q z), w ∈ connectedComponentIn (WilkiesDesign.E.fiber (p := p) (q := q) S.X.set (WilkiesDesign.E.projFirst p q z)) (WilkiesDesign.E.projSnd p q z) ∧ w l ≠ z (Work.WilE7.fibDir p q l)) : S.j < S'.j := by
  obtain ⟨z, hzX', w, hwf, hwc, hwl⟩ := hwit
  have hzS : z ∈ S.X.set := critSet_subset S l (hsub hzX')
  have hzS0 : ∀ a, eaEval S.X.c (S.h a) z = 0 := fun a => Work.WilE5.Stratum.good_eqs hGood hzS a
  have hzS'0 : ∀ b, eaEval S'.X.c (S'.h b) z = 0 :=
    fun b => Work.WilE5.Stratum.good_eqs hGood' hzX' b
  have hrankS := Work.WilE5.Stratum.good_rank hGood hzS
  have hrankS' := Work.WilE5.Stratum.good_rank hGood' hzX'
  -- the "fibre" statements
  have hvanFib := eventually_fibreMap_S'_eq_zero_imp S S' hGood' hGood l hsub hzX'
  -- (A) the row span inclusion
  have hrow : ∀ a : Fin S.j, ∃ lam : Fin S'.j → ℝ, ∀ l : Fin q,
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a)) z
    = ∑ b, lam b * eaEval S'.X.c (eaD S'.X.c (Work.WilE5.yDir p l) (S'.h b)) z := by
    intro a
    exact Work.WilE7.Auxiliary.fibreGradMemSpan2 S.X.c S'.X.c S.h S'.h a z hzS'0 hrankS'
      (hvanFib.mono (fun y hy h0 => hy h0 a))
  -- (B) the rank inequality
  have hle : S.j ≤ S'.j :=
    Work.WilE7.Aux.fibreRowspanRankLe S.X.c S'.X.c S.h S'.h z hrankS hrankS' hrow
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    -- (C) the two fibre level sets coincide near the fibre base point
    have hkerFib : ∀ v : Fin q → ℝ,
        (∀ b, ∑ l', eaEval S'.X.c (eaD S'.X.c (Work.WilE5.yDir p l') (S'.h b)) z * v l' = 0) →
        (∀ a, ∑ l', eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l') (S.h a)) z * v l' = 0) :=
      fun v hv => Work.WilE7.Aux.fibreKerLe S.X.c S'.X.c S.h S'.h z hrow v hv
    have hsurjS : (fderiv ℝ (fibreMap S (projFirst p q z)) (projSnd p q z)).range = ⊤ :=
      range_fderiv_fibreMap S hGood (projFirst p q z) (projSnd p q z)
        (by rw [append_projFirst_projSnd]; exact hzS)
    have hlev := Work.WilE7.Auxiliary.fibreLevelSetEq S.X.c S'.X.c S.h S'.h l z heq hzS'0
      hrankS hrankS' hkerFib hvanFib
    -- (D) the criticality data
    have hminFib : ∀ᶠ y in nhds (projSnd p q z),
        (∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y) = 0) →
        ∀ σ : Fin (S.j + 1) → Fin q,
          eaEval S.X.c (critMinor S.X.c S.h l σ) (Fin.append (projFirst p q z) y) = 0 := by
      have hcont : Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
          (nhds (projSnd p q z)) (nhds z) := by
        have hfd : ContinuousAt (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
            (projSnd p q z) :=
          (Work.WilE7.Aux.hasFDerivAt_append_const p q (projFirst p q z)
            (projSnd p q z)).continuousAt
        have hfd2 : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z) = z :=
          append_projFirst_projSnd z
        change Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (nhds (projSnd p q z))
          (nhds ((fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z))) at hfd
        rwa [hfd2] at hfd
      have hev := hcont.eventually ((hGood' z hzX').2.2)
      have hbf : ∀ y : Fin q → ℝ,
          projFirst p q (Fin.append (projFirst p q z) y) = projFirst p q z := by
        intro y; funext i; simp [projFirst, Fin.append_left]
      filter_upwards [hlev, hev] with y hlev_y hy
      intro hgy
      have hgy'_forall : ∀ b, eaEval S'.X.c (S'.h b) (Fin.append (projFirst p q z) y) = 0 :=
        (hlev_y).mpr hgy
      have hmem : Fin.append (projFirst p q z) y ∈ S'.X.set := hy (hbf y) hgy'_forall
      have hcs : Fin.append (projFirst p q z) y ∈ (critSet S l).set := hsub hmem
      rw [critSet_set] at hcs
      exact fun σ => hcs.2 σ
    have hrankFib : ∀ᶠ y in nhds (projSnd p q z),
        (∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y) = 0) →
        (Matrix.of fun (a : Fin S.j) (l' : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l') (S.h a))
            (Fin.append (projFirst p q z) y)).rank = S.j := by
      have hcont : Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
          (nhds (projSnd p q z)) (nhds z) := by
        have hfd : ContinuousAt (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y)
            (projSnd p q z) :=
          (Work.WilE7.Aux.hasFDerivAt_append_const p q (projFirst p q z)
            (projSnd p q z)).continuousAt
        have hfd2 : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z) = z :=
          append_projFirst_projSnd z
        change Tendsto (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (nhds (projSnd p q z))
          (nhds ((fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) (projSnd p q z))) at hfd
        rwa [hfd2] at hfd
      have hev := hcont.eventually ((hGood z hzS).2.2)
      have hbf : ∀ y : Fin q → ℝ,
          projFirst p q (Fin.append (projFirst p q z) y) = projFirst p q z := by
        intro y; funext i; simp [projFirst, Fin.append_left]
      filter_upwards [hev] with y hy
      intro hgy
      have hmem : Fin.append (projFirst p q z) y ∈ S.X.set := hy (hbf y) hgy
      exact Work.WilE5.Stratum.good_rank hGood hmem
    have hcritData : ∀ᶠ y in nhds (projSnd p q z),
        (∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y) = 0) →
        (∀ v : Fin q → ℝ,
          (∀ a, ∑ l', eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l') (S.h a))
            (Fin.append (projFirst p q z) y) * v l' = 0) → v l = 0) := by
      filter_upwards [hminFib, hrankFib] with y hmin_y hrank_y
      intro hgy v hv
      exact Work.WilE7.Aux.critMinorsVanishKer S.X.c S.h l (Fin.append (projFirst p q z) y)
        (hrank_y hgy) (fun σ => hmin_y hgy σ) v hv
    have hcritCond :=
      Work.WilE7.Auxiliary.fibreCritCond S.X.c S'.X.c S.h S'.h l z hrankFib hcritData
    -- (E) `y_l` is locally constant on the fibre level set near the fibre base point
    have hF_an : ∀ y : Fin q → ℝ, AnalyticAt ℝ (fun y' : Fin q → ℝ => y' l) y :=
      fun y => (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).analyticAt y
    have hlocConst : ∀ᶠ y in nhds (projSnd p q z),
        fibreMap S (projFirst p q z) y = 0 → y l = (projSnd p q z) l := by
      refine Work.WilE7.Auxiliary.criticalLevelSetLocallyConst2 (fibreMap S (projFirst p q z))
        (fun y : Fin q → ℝ => y l) (projSnd p q z)
        (fun y => analyticAt_fibreMap S (projFirst p q z) y) hF_an hsurjS ?_
      filter_upwards [hcritCond] with y hy
      intro hgy v hv
      have hgy' : ∀ a, eaEval S.X.c (S.h a) (Fin.append (projFirst p q z) y) = 0 :=
        fun a => by simpa [fibreMap] using funext_iff.mp hgy a
      unfold fibreMap at hv
      exact hy hgy' v hv
    -- (F) the connected component is locally the level set
    have hCpre : IsPreconnected
        (connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z)) :=
      isPreconnected_connectedComponentIn
    have hy0C : (projSnd p q z) ∈
        connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z) := by
      refine mem_connectedComponentIn ?_
      show Fin.append (projFirst p q z) (projSnd p q z) ∈ S.X.set
      rw [append_projFirst_projSnd]
      exact hzS
    have hloc := Work.WilE7.Auxiliary.fibreComponentLocallyLevelSet S hGood z hzS
    have hrankC : ∀ y ∈ connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z),
        (fderiv ℝ (fibreMap S (projFirst p q z)) y).range = ⊤ := by
      intro y hy
      exact range_fderiv_fibreMap S hGood (projFirst p q z) y
        (connectedComponentIn_subset (fiber S.X.set (projFirst p q z)) (projSnd p q z) hy)
    -- (G) conclude that `y_l` is constant on the component
    have hconst := Work.WilE7.Aux.constantOnLevelSet (fibreMap S (projFirst p q z))
      (fun y : Fin q → ℝ => y l)
      (connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z)) (projSnd p q z)
      (fun y => analyticAt_fibreMap S (projFirst p q z) y) hF_an
      hy0C hCpre hloc hrankC hlocConst
    have hw := hconst w hwc
    exact hwl hw

end Work.WilE7
