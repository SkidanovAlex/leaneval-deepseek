/-
  WilE7 — `DimDrop` from analytic curve selection (route "CS-slice", Claude design 2026-10-11).
  Design: `sources/wilkiesE7/wilkies_e7_frontier.md`.  The nodes N1–N9b of that design are proved
  in the sibling modules of `Submission/Work/WilE7/FrontierCS/` and imported here; this file holds
  the assembly plus the wiring of the delivered C4a curve selection.

  Idea.  Assume `n ≥ N - j =: d`; restrict `γ` to `ℝ^d`.  Straighten: `Φ (t,e) = γ t + B e`.
  For each 0/1 matrix `Λ` (finitely many) use slice coordinates `ψ_Λ (τ,e) = Φ (τ + Λ e, e)`.
  `A_Λ` = points of the slice chart over `W` where the slice Jacobian `∂_e (G ∘ ψ_Λ)` is invertible.
  (1) every point `(τ,0)`, `τ` small, is in `closure A_Λ` for some `Λ` (grid lemma);
  (2) finite-union Baire: one `Λ` works on an open set `V` of `τ`s;
  (3) `fst '' (A_Λ ∩ {‖e‖ < 1/(k+1)})` is open (IFT) and dense in `V`; Baire gives `τ₀`;
  (4) `g e := G (ψ_Λ (τ₀, e))` has nondegenerate zeros `e_k ≠ 0`, `e_k → 0`;
  (5) curve selection on `{Σ gᵢ² = 0, (det Dg)² > 0}` + isolation of nondegenerate zeros: False.
  The rank-drop hypothesis of `DimDrop` is never used.
-/
import Mathlib
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilE7.FrontierDropFromDimDrop
import Submission.Work.WilE7.E7_fiber_cut_proved
import Submission.Work.WilC4aRW.Main
import Submission.Work.WilC4aAL.SpecAlias
import Submission.Work.WilC4aP.Main
import Submission.Work.WilC4aTS.TS
import Submission.Work.WilC4aCS.CurveSelStep
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.eventually_ne_of_range_top
import Submission.Work.WilE7.FrontierCS.jacDet_ne_zero_iff
import Submission.Work.WilE7.FrontierCS.analyticOnNhd_jacDet
import Submission.Work.WilE7.FrontierCS.nondegZeros_not_accum
import Submission.Work.WilE7.FrontierCS.multiAffine_eq_zero
import Submission.Work.WilE7.FrontierCS.exists_real_det_ne_zero
import Submission.Work.WilE7.FrontierCS.exists_grid_det_ne_zero
import Submission.Work.WilE7.FrontierCS.exists_complement
import Submission.Work.WilE7.FrontierCS.mem_closure_preimage
import Submission.Work.WilE7.FrontierCS.exists_open_subset_of_finite_closed_cover
import Submission.Work.WilE7.FrontierCS.exists_mem_iInter_of_dense_in_open
import Submission.Work.WilE7.FrontierCS.isOpen_fst_image_sliceSet
import Submission.Work.WilE7.FrontierCS.grid_cover
import Submission.Work.WilE7.FrontierCS.slice_reduction
import Submission.Work.WilE7.FrontierCS.restrict_chart
import Submission.Work.WilE7.FrontierCS.le_of_range_top

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.FrontierCS
open WilkiesDesign.CG.C4a

/-- **N9. `DimDrop` from curve selection** (proved from N1, N8, N9a, N9b, all imported). -/
theorem dimDrop_of_curveSel (hCS : ∀ n, CurveSel n) : Work.WilE7.DimDrop := by
  intro N j n G hG W hWZ hWopen hWrk γ hγ hγinj hγW hγrk
  by_cases hj : j = 0
  · -- `j = 0`: the codomain is the zero space, so `range = ⊤` always and `hγrk` is absurd.
    subst hj
    have htop : (fderiv ℝ G (γ 0)).range = ⊤ :=
      Submodule.eq_top_iff'.mpr fun x => by
        rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    exact absurd hγrk.self_of_nhds (fun hcon => hcon htop)
  · have hj' : 0 < j := Nat.pos_of_ne_zero hj
    by_contra hlt
    rw [not_lt] at hlt
    -- `W` is nonempty, hence `j ≤ N`
    obtain ⟨s, hs⟩ := hγW.exists
    have hWne : W.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, closure_empty] at hs
      exact hs.1
    obtain ⟨w, hw⟩ := hWne
    have hjN : j ≤ N := le_of_range_top _ (hWrk w hw)
    obtain ⟨γ', hγ', hγ'inj, hγ'W⟩ :=
      restrict_chart (d := N - j) hlt hγ hγinj (P := fun z => z ∈ closure W \ W) hγW
    obtain ⟨g, hg, hacc⟩ :=
      slice_reduction (d := N - j) (by omega) hj' hG hWZ hWopen hWrk hγ' hγ'inj hγ'W
    exact nondegZeros_not_accum (hCS j) hg hacc

/-- **The delivered C4a curve selection in every dimension** (sorry-free closure term), so that no
hypothesis is added to `DimDrop`.  This is the `FINAL-WIRE` line of the design document. -/
theorem curveSel_all : ∀ n, CurveSel n := fun n =>
  Nat.rec CurveSel_zero
    (fun n ih => C4a_CS_step_proved C4a_RW_proved
      (C4a_arcLift_proved C4a_puiseux_proved) Work.WilC4aTS.C4a_TS1_proved n ih) n

/-- **`DimDrop` unconditionally**, from the delivered curve selection. -/
theorem dimDrop_proved : Work.WilE7.DimDrop :=
  dimDrop_of_curveSel curveSel_all

/-- **The E7 target from curve selection** (`hCS` is wired from the delivered C4a holes). -/
theorem E7_fiber_cut_proved_of_curveSel (hCS : ∀ n, CurveSel n)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set :=
  Work.WilE7.E7_fiber_cut_proved_of_dimDrop (dimDrop_of_curveSel hCS) hE2 hE5 hE6

end Work.WilE7.FrontierCS
