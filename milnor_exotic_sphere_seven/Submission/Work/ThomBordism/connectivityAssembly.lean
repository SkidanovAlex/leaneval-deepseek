import Mathlib
import Submission.Work.ThomBordism.Grassmann.thomSpacePieces
import Submission.Work.ThomBordism.Grassmann.finsetCoveredConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `(k-1)`-connectivity of the Thom space of the tautological bundle, in AREA THOM

`Work.ThomBordism.Grassmann.thomSpaceConnectedAssembly` (`Submission/Work/ThomBordism/Grassmann/`,
area GRASSMANN) is the area's assembly of the `(k-1)`-connectivity of `Th(γ_k)` from the connectivity
of the chart pieces `chartPiece k m S = far 1 ∪ π⁻¹ (baseSet S)` — the finite-cover Mayer–Vietoris
theorem `finsetCoveredConnected` applied to the open cover of `Th(γ_k)` by the chart pieces.  In that
file the piece connectivity is a `sorry` (`chartPieceConnected`), so
`thomSpaceConnectedAssembly` is *not yet* available to this area's endgame
(`Work.ThomBordism.thomRational_of_grassmannConnectivity` consumes
`hconn : ∀ k ≥ 11, Grassmann.ThomSpaceConnected k m`).

This file builds the **assembly** on the AREA THOM side, parameterised by the piece connectivity as a
single named hypothesis, so that the area's endgame can be fed from a proof of the piece connectivity
that lives here — independently of GRASSMANN's file, which is blocked on a route
(`ChartPieceCompressFarCrux`, `chartPieceCompressFar`) whose intermediate statement
`pieceHomotopyCubed` (`Z ≃ Cubed ↥W k`) is **FALSE** (see
`Submission/Work/ThomBordism/Grassmann/pieceOverChartConnectivity.lean`'s header: for `k = 1, m = 1`
and an open arc `W` one has `Z ≅ S² ∖ (closed disc) ≅ ℝ²` while `Cubed ↥W 1 ≃ S¹`).

The statement of the hypothesis is exactly `Work.ThomBordism.Grassmann.pieceOverChartConnectivity`
(`Submission/Work/ThomBordism/Grassmann/pieceOverChartConnectivity.lean`, the correct statement, with
a `sorry` there): the piece over an arbitrary **open** subset of a chart cell is `(k-1)`-connected.

## Main declarations

* `Work.ThomBordism.thomPiece` — the piece `far 1 ∪ π⁻¹ W`;
* `Work.ThomBordism.chartPieceConnected_of_pieces` — the graph-cover form of the piece connectivity
  (`⋂ S ∈ σ, chartPiece S` is highly connected) from the open-subset form;
* `Work.ThomBordism.thomSpaceConnected_of_pieces` — **the target**: `Grassmann.ThomSpaceConnected k m`
  from the open-subset form of the piece connectivity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.Grassmann

/-- **The piece over an open subset of a chart cell**: `far 1 ∪ π⁻¹ W ⊆ Th(γ_k)`. -/
def thomPiece (k m : ℕ) (W : Set (OG k m)) : Set (Torsion.TP k m) :=
  Torsion.far k m 1 ∪ OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' W)

/-- The point at infinity belongs to every piece. -/
theorem infty_mem_pieceSet (k m : ℕ) (W : Set (OG k m)) :
    (OnePoint.infty : Torsion.TP k m) ∈ thomPiece k m W :=
  Or.inl (Torsion.infty_mem_far k m 1)

/-- **The piece connectivity, as a single named hypothesis** (the statement of
`Work.ThomBordism.Grassmann.pieceOverChartConnectivity`): for `W ⊆ Th(γ_k)` the piece over an open
`W ⊆ baseSet S₀` is `(k-1)`-connected. -/
def PieceOverChartConnected : Prop :=
  ∀ (k m : ℕ) (S₀ : ChartIdx k m) (W : Set (OG k m)), IsOpen W →
    W ⊆ (tautologicalBundle k m).baseSet S₀ →
    ∀ j : ℕ, j < k → ∀ x : ↥(thomPiece k m W),
      Subsingleton (HomotopyGroup (Fin j) ↥(thomPiece k m W) x)

/-- **The graph-cover form of the piece connectivity** (piece connectivity ⟹ `chartPieceConnected`):
for every nonempty finite family `σ` of charts, the intersection `⋂ S ∈ σ, chartPiece k m S =
far 1 ∪ π⁻¹ (⋂ S ∈ σ, baseSet S)` has vanishing `π_j` in the range `j < k`.

This is `Work.ThomBordism.Grassmann.chartPieceConnected` with the range `j < k` (which is what the
Mayer–Vietoris assembly consumes), from the open-subset form. -/
theorem chartPieceConnected_of_pieces (h : PieceOverChartConnected) (k m : ℕ)
    (σ : Finset (ChartIdx k m)) (hσ : σ.Nonempty) :
    ∀ j : ℕ, j < k → ∀ x : ↥(⋂ S ∈ σ, chartPiece k m S),
      Subsingleton (HomotopyGroup (Fin j) ↥(⋂ S ∈ σ, chartPiece k m S) x) := by
  classical
  obtain ⟨S₀, hS₀⟩ := hσ
  have hWopen : IsOpen (⋂ S ∈ σ, baseSet S) :=
    isOpen_biInter_finset (fun S _ => isOpen_baseSet S)
  have hWsub : (⋂ S ∈ σ, baseSet S) ⊆ baseSet S₀ :=
    fun x hx => Set.mem_iInter₂.mp hx S₀ hS₀
  intro j hj x
  refine subsingleton_of_set_eq
    (show (⋂ S ∈ σ, chartPiece k m S) = thomPiece k m (⋂ S ∈ σ, baseSet S) from
      iInter_chartPiece k m σ) ?_ x
  intro y
  exact h k m S₀ (⋂ S ∈ σ, baseSet S) hWopen hWsub j hj y

/-- The canonical homeomorphism `↥(univ : Set X) ≃ₜ X`. -/
def univHomeo (X : Type*) [TopologicalSpace X] : ↥(Set.univ : Set X) ≃ₜ X where
  toFun x := x.1
  invFun x := ⟨x, trivial⟩
  left_inv x := by ext; rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- **The connectivity of the Thom space of the tautological oriented bundle**, assembled from the
piece connectivity by the finite-cover Mayer–Vietoris theorem — the AREA THOM version of
`Work.ThomBordism.Grassmann.thomSpaceConnectedAssembly`, with the piece connectivity as a named
hypothesis. -/
theorem thomSpaceConnected_of_pieces (h : PieceOverChartConnected) (k m : ℕ) :
    ThomSpaceConnected k m := by
  classical
  intro i hi
  have hcov := iUnion_chartPiece k m
  have hne : ∀ σ : Finset (ChartIdx k m), σ.Nonempty → σ ⊆ Finset.univ →
      (⋂ S ∈ σ, chartPiece k m S).Nonempty :=
    fun σ _ _ => ⟨OnePoint.infty, Set.mem_iInter₂.mpr (fun S _ => infty_mem_chartPiece k m S)⟩
  have hcon : ∀ σ : Finset (ChartIdx k m), σ.Nonempty → σ ⊆ Finset.univ →
      ∀ j < k + 1 - σ.card, ∀ x : ↥(⋂ S ∈ σ, chartPiece k m S),
        Subsingleton (HomotopyGroup (Fin j) ↥(⋂ S ∈ σ, chartPiece k m S) x) := by
    intro σ hσ _ j hj x
    have h1 : 1 ≤ σ.card := Finset.card_pos.mpr hσ
    exact chartPieceConnected_of_pieces h k m σ hσ j (by omega) x
  have hmain := finsetCoveredConnected (fun S : ChartIdx k m => chartPiece k m S)
    (fun S => isOpen_chartPiece k m S) Finset.univ Finset.univ_nonempty (k + 1) (by omega) hne hcon
  have hfin : ∀ j < k + 1 - 1, ∀ x : ↥(⋃ S ∈ (Finset.univ : Finset (ChartIdx k m)),
      chartPiece k m S), Subsingleton (HomotopyGroup (Fin j) _ x) := hmain
  rw [show k + 1 - 1 = k from by omega] at hfin
  have hbase : ((univHomeo (TautologicalThomSpace k m)).symm.trans
      (Homeomorph.setCongr hcov).symm) (thomBasepoint k m)
        = (⟨thomBasepoint k m, by rw [hcov]; trivial⟩ :
            ↥(⋃ S ∈ (Finset.univ : Finset (ChartIdx k m)), chartPiece k m S)) :=
    Subtype.ext rfl
  exact subsingleton_homotopyGroup_of_homeomorph _ hbase i
    (hfin i hi ⟨thomBasepoint k m, by rw [hcov]; trivial⟩)

end

end Work.ThomBordism
