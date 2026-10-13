/-
  Area E7: the **assembly of the frontier dimension drop from a single, general,
  classical analytic-geometry input.**

  The gap (`Submission/Work/WilE7/NOTES_S15_frontier_general.md`) is the classical dimension drop
  of real analytic sets: for an analytic `G : ℝ^N → ℝ^j` and `W` open in the level set `{G = 0}`
  with `rank dG = j` on `W`, the *rank-drop part* of the frontier `closure W \ W` has dimension
  `< N - j`.  This file isolates that statement as `Work.WilE7.DimDrop` and derives, from it
  alone,

    `Work.WilE7.frontierDrop_of_dimDrop : DimDrop → FrontierDrop`

  i.e. the whole frontier input of BV's Lemma 8 (both the rank-drop case *and* the `S'.j = 1`
  case of `frontier_codim_one`, which it subsumes).

  The reduction uses only already-proved results of the workspace:
  * `Work.WilE7.fibre_analytic_chart` (the analytic chart of the fibre of a `Good` stratum);
  * `Work.WilE7.frontier_nondrop_proved` (the case in which the fibre Jacobian has full rank
    somewhere on `S'.X.set`);
  * `Work.WilE7.Aux.fibreFDeriv`, `Work.WilE7.Aux.rangePiEqTopOfRank`,
    `Work.WilE7.analyticAt_fibreMap`, `Work.WilE7.range_fderiv_fibreMap`,
    `Work.WilE7.eventually_mem_fiber_of_good` for the analyticity/rank bookkeeping.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.stratum_j_lt_of_subset_crit
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.fibre_analytic_chart
import Submission.Work.WilE7.frontier_nondrop_proved
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.exists_critSet_witness_of_closed_fiber

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped Topology
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## The single input: the dimension drop for analytic level sets -/

/-- **The classical dimension drop for real analytic level sets** (Łojasiewicz), in curve form.

`G : ℝ^N → ℝ^j` is analytic, `W` is open in the level set `{G = 0}` and the differential of `G` is
surjective on `W` (so `W` is an `(N-j)`-manifold near each of its points).  If an analytic chart
`γ : ℝ^n → ℝ^N` with injective differential at `0` maps into the *rank-deficient part of the
closure of `W` minus `W`* (i.e. `γ s ∈ closure W \ W` and `rank dG(γ s) < j`), then `n < N - j`.

This is the statement `Work.AnalyticFrontier.analytic_frontier_dim_drop`; it is TRUE (the
non-analytic analogue fails: `{(t, sin (1/t)) : t > 0} ∪ ({0} × [-1,1])`), and its proof is the
classical local theory of germs of real analytic sets. -/
def DimDrop : Prop :=
  ∀ {N j n : ℕ} {G : (Fin N → ℝ) → (Fin j → ℝ)}, AnalyticOnNhd ℝ G Set.univ →
    ∀ {W : Set (Fin N → ℝ)}, (∀ w ∈ W, G w = 0) →
    (∀ w ∈ W, ∃ U ∈ nhds w, ∀ z ∈ U, G z = 0 → z ∈ W) →
    (∀ w ∈ W, (fderiv ℝ G w).range = ⊤) →
    ∀ {γ : (Fin n → ℝ) → (Fin N → ℝ)}, AnalyticOnNhd ℝ γ Set.univ →
    Function.Injective (fderiv ℝ γ (0 : Fin n → ℝ)) →
    (∀ᶠ s in nhds (0 : Fin n → ℝ), γ s ∈ closure W \ W) →
    (∀ᶠ s in nhds (0 : Fin n → ℝ), (fderiv ℝ G (γ s)).range ≠ ⊤) →
    n < N - j

/-! ## Linear algebra: full range implies full row rank -/

/-- The converse of `Work.WilE7.Aux.rangePiEqTopOfRank`: if the matrix-vector map of `M` is
surjective then `M` has full row rank. -/
theorem matrix_rank_eq_of_pi_range_top {m q : ℕ} (M : Fin m → Fin q → ℝ)
    (h : (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))).range
      = ⊤) :
    (Matrix.of M).rank = m := by
  let f : (Fin q → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ)))
  have hcoe : (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = (Matrix.of M).mulVecLin := by
    ext v a
    simp [f, ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVec, dotProduct]
  have hfr : (f : (Fin q → ℝ) →ₗ[ℝ] (Fin m → ℝ)).range = ⊤ := h
  have htop : (Matrix.of M).mulVecLin.range = ⊤ := (hcoe ▸ hfr : _)
  rw [Matrix.rank, htop]
  simp

/-! ## The other three geometric inputs of BV's Lemma 8

These are the same statements as `Work.WilE7.closureProj_proved`, `Work.WilE7.critDrop_proved` and
`Work.WilE7.critWitness_proved` of `Submission/Work/WilE7/FiberCutInputsProved.lean`; they are
re-derived here from their own (sorry-free) modules so that this file, and the target, do not
depend on `Work.WilE7.frontier_codim_one` (which is on the critical path only through the older
`frontierDrop_of_rankDrop` assembly). -/

/-- `π_n(fiberClosure Y) = π_n(Y)`. -/
theorem closureProj_proved' : ClosureProj :=
  fun n m Y => projFirst_fiberClosure Y

/-- The critical-side dimension drop. -/
theorem critDrop_proved' : CritDrop :=
  fun p q S S' hGood hGood' l hj hsub hwit =>
    stratum_j_lt_of_subset_crit S S' hGood hGood' l hj hsub hwit

/-- Critical points with a witness over closed fibres. -/
theorem critWitness_proved' : CritWitness :=
  fun p q S hGood hj x hclosed hne =>
    exists_critSet_witness_of_closed_fiber S hGood hj x hclosed hne

/-! ## The frontier dimension drop from the analytic input -/

/-- **The frontier dimension drop from the single analytic input `DimDrop`.**

`S`, `S'` are `Good` strata of `ℝ^{p+q}` and `S'.X.set` lies in the fibrewise frontier of
`S.X.set`.  Then `S.j < S'.j`.

The proof splits on whether the fibre Jacobian of `S` has full rank somewhere on `S'.X.set`:

* if it does, `Work.WilE7.frontier_nondrop_proved` applies;
* otherwise the Jacobian is rank-deficient on all of `S'.X.set`, and the analytic chart of the
  `S'`-fibre (`Work.WilE7.fibre_analytic_chart`, of dimension `q - S'.j`) maps into the
  rank-deficient part of `closure W \ W`; `DimDrop` then gives `q - S'.j < q - S.j`, i.e.
  `S.j < S'.j`.  (This covers the case `S'.j = 1`, hence subsumes `frontier_codim_one`.) -/
theorem frontierDrop_of_dimDrop (hDim : DimDrop) : FrontierDrop := by
  intro p q S S' hGood hGood' hsub hne
  by_cases hnd : ∃ z ∈ S'.X.set, (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank = S.j
  · obtain ⟨z, hz, hrank⟩ := hnd
    exact frontier_nondrop_proved S S' hGood hGood' hsub z hz hrank
  · have hdrop : ∀ z ∈ S'.X.set, (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank < S.j := by
      intro z hz
      have hle : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank ≤ S.j :=
        Matrix.rank_le_height _
      exact lt_of_le_of_ne hle (fun h => hnd ⟨z, hz, h⟩)
    obtain ⟨z0, hz0⟩ := hne
    set x : Fin p → ℝ := projFirst p q z0 with hx
    obtain ⟨γ, hγ0, hγan, hγinj, hγmem⟩ := fibre_analytic_chart S' hGood' z0 hz0
    -- the analyticity of the fibre map of `S` over the base `x`
    have hGan : AnalyticOnNhd ℝ (fibreMap S x) Set.univ :=
      fun y _ => analyticAt_fibreMap S x y
    have hWZ : ∀ w ∈ fiber S.X.set x, fibreMap S x w = 0 := by
      intro w hw
      funext a
      exact Work.WilE5.Stratum.good_eqs hGood hw a
    have hWopen : ∀ w ∈ fiber S.X.set x, ∃ U ∈ nhds w,
        ∀ z ∈ U, fibreMap S x z = 0 → z ∈ fiber S.X.set x := by
      intro w hw
      have hev := eventually_mem_fiber_of_good S hGood x w hw
      rw [Filter.eventually_iff_exists_mem] at hev
      obtain ⟨U, hU, hUsub⟩ := hev
      refine ⟨U, hU, fun z hz hz0 => hUsub z hz (fun a => ?_)⟩
      have := congr_fun hz0 a
      simpa [fibreMap] using this
    have hrkW : ∀ w ∈ fiber S.X.set x, (fderiv ℝ (fibreMap S x) w).range = ⊤ :=
      fun w hw => range_fderiv_fibreMap S hGood x w hw
    -- the chart maps into the rank-deficient part of the frontier of the fibre
    set x' : Fin p → ℝ := projFirst p q z0 with hx'
    have hxeq : x' = x := rfl
    have hγcl : ∀ᶠ s in nhds (0 : Fin (q - S'.j) → ℝ),
        γ s ∈ closure (fiber S.X.set x) \ fiber S.X.set x := by
      filter_upwards [hγmem] with s hs
      have hs' : Fin.append x (γ s) ∈ S'.X.set := by
        rw [← hxeq]; exact hs
      obtain ⟨h1, h2⟩ := hsub hs'
      have h1' : projSnd p q (Fin.append x (γ s)) ∈
          closure (fiber S.X.set (projFirst p q (Fin.append x (γ s)))) := h1
      refine ⟨?_, ?_⟩
      · have hpf : projFirst p q (Fin.append x (γ s)) = x := by
          funext i; simp [projFirst, Fin.append_left]
        have hps : projSnd p q (Fin.append x (γ s)) = γ s := by
          funext i; simp [projSnd, Fin.append_right]
        rw [hpf, hps] at h1'
        exact h1'
      · intro hcon
        exact h2 hcon
    have hγrk : ∀ᶠ s in nhds (0 : Fin (q - S'.j) → ℝ),
        (fderiv ℝ (fibreMap S x) (γ s)).range ≠ ⊤ := by
      filter_upwards [hγmem] with s hs
      have hs' : Fin.append x (γ s) ∈ S'.X.set := by
        rw [← hxeq]; exact hs
      have hlt := hdrop _ hs'
      intro htop
      -- identify the derivative with the matrix-vector map
      have hpf : projFirst p q (Fin.append x (γ s)) = x := by
        funext i; simp [projFirst, Fin.append_left]
      have hps : projSnd p q (Fin.append x (γ s)) = γ s := by
        funext i; simp [projSnd, Fin.append_right]
      have hident' : fderiv ℝ (fibreMap S x) (γ s)
          = ContinuousLinearMap.pi (fun a : Fin S.j => (∑ l : Fin q,
              eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a))
                (Fin.append x (γ s)) •
              (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) := by
        have h := Work.WilE7.Aux.fibreFDeriv S.X.c S.h (Fin.append x (γ s))
        rw [hpf, hps] at h
        exact h
      rw [hident'] at htop
      have hrankj : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir p l) (S.h a))
            (Fin.append x (γ s))).rank = S.j :=
        matrix_rank_eq_of_pi_range_top _ htop
      have hsame : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
          eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a))
            (Fin.append x (γ s))).rank = S.j := hrankj
      omega
    have hlt : q - S'.j < q - S.j :=
      hDim hGan hWZ hWopen hrkW (fun s _ => hγan s) hγinj hγcl hγrk
    omega

end Work.WilE7
