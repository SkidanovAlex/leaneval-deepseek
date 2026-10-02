import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.finsetCoveredConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The open chart pieces of the Thom space of the tautological bundle

**Target** (`Work.ThomBordism.Grassmann.thomSpaceConnectedAssembly`): for all `k m : ℕ`,
`ThomSpaceConnected k m`, i.e. every `π_i(Th γ, ∞)` with `i < k` is trivial, where `γ` is the
tautological oriented rank-`k` bundle over `G̃r_k(ℝ^{k+m})` and `Th γ = OnePoint (TotalSpace γ)` its
Thom space (the metric-free model of `Model.lean`).

## The route

**The cover.**  For a chart `S : ChartIdx k m` put

`chartPiece k m S := far 1 ∪ π⁻¹ (baseSet S) ⊆ Th γ`,

where `far 1 = {fibN > 1} ∪ {∞}` is the "far" neighbourhood of `∞` (`Torsion.far`, from
`Torsion/ModelGeom.lean`) and `fibN` is the continuous fibrewise-norm-like function of
`Torsion.exists_fibreNormLike` (the norm `‖evalVec p‖` of the vector of the plane, with
`{fibN ≤ 1}` compact).  Each `chartPiece k m S` is **open** (its complement is
`{fibN ≤ 1} ∩ π⁻¹(G ∖ baseSet S)`, a closed subset of the compact `{fibN ≤ 1}`, hence compact),
the finitely many pieces **cover** `Th γ` (the chart cells `baseSet S` cover the Grassmannian), and
every finite intersection is **nonempty** (it contains `∞`).  Moreover

`⋂ S ∈ σ, chartPiece k m S = far 1 ∪ π⁻¹ (⋂ S ∈ σ, baseSet S)`,

so the finite intersections are again "chart pieces", over the intersection of the chart cells.

**The assembly.**  The finite-cover Mayer–Vietoris theorem for homotopy groups
(`Work.ThomBordism.Grassmann.finsetCoveredConnected`, proved) applied to this cover with parameter
`k+1` gives `π_j(Th γ) = 0` for `j < k` as soon as every finite intersection `⋂ S ∈ σ` is
`(k+1-|σ|)`-connected, i.e. as soon as

  `(★)  π_j (⋂ S ∈ σ, chartPiece k m S) = 0`  for  `j + |σ| ≤ k`  and every nonempty `σ`.

**The pieces `(★)`.**  For `σ` fix a chart `S₀ ∈ σ`, so `U := ⋂ S ∈ σ, baseSet S ⊆ baseSet S₀` and
the bundle is trivialised over `U` by the chart `S₀`.  Then `⋂ S ∈ σ, chartPiece k m S` is the
one-point compactification-like space `far 1 ∪ π⁻¹(U)`, the "Thom space of the trivial rank-`k`
bundle over `U`": it is homotopy equivalent to the `k`-fold (reduced) suspension
`Σ^k (U_+) = U_+ ∧ S^k`, i.e. to the cube model `(U × I^k)/(U × ∂I^k)`.  A `k`-fold suspension of a
nonempty space is `(k-1)`-connected (`Cubed`/`CubedS` connectivity), which is more than enough for
`(★)` (since `|σ| ≥ 1`).

The two ingredients of the pieces `(★)` are therefore

* the trivial-bundle model `Q_σ ≃ (U × I^k)/(U × ∂I^k)` — geometric, "collar/radial" work in the
  trivialised chart; and
* the connectivity of the `k`-fold suspension `(W × I^k)/(W × ∂I^k)` of a nonempty space `W` —
  pure homotopy theory (an induction on `k` using the two-hemisphere cover and
  `twoSetConnected`).

This file contains the cover, its API, and the assembly `(★) ⟹ target`; the two ingredients are
isolated below as `chartPieceConnected` (the pieces) and the suspension lemma it is built from.

## Main declarations

* `chartPiece`, `chartPiece_iInter`, `isOpen_chartPiece`, `iUnion_chartPiece`,
  `infty_mem_chartPiece`, `some_mem_chartPiece`.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- There is at least one chart of `G̃r_k(ℝ^{k+m})`. -/
instance instNonemptyChartIdx (k m : ℕ) : Nonempty (ChartIdx k m) :=
  ⟨⟨(Finset.univ : Finset (Fin k)).map (Fin.castLEEmb (Nat.le_add_right k m)), by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩⟩

/-! ## The open chart pieces of the Thom space -/

/-- **The open chart piece of `Th γ` over the chart cell `baseSet S`**: the point at infinity, the
whole "far" region `{fibN > 1}`, and the part of the total space lying over `baseSet S`. -/
def chartPiece (k m : ℕ) (S : ChartIdx k m) : Set (TautologicalThomSpace k m) :=
  Torsion.far k m 1 ∪ (OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' baseSet S))

/-- The point at infinity lies in every chart piece. -/
theorem infty_mem_chartPiece (k m : ℕ) (S : ChartIdx k m) :
    OnePoint.infty ∈ chartPiece k m S :=
  Or.inl (Torsion.infty_mem_far k m 1)

/-- A point of the total space whose projection lies in `baseSet S` lies in the chart piece. -/
theorem some_mem_chartPiece (k m : ℕ) (S : ChartIdx k m) {p : (tautologicalBundle k m).TotalSpace}
    (hp : p.proj ∈ baseSet S) : (OnePoint.some p : TautologicalThomSpace k m) ∈ chartPiece k m S :=
  Or.inr ⟨p, hp, rfl⟩

/-- **The chart pieces are open.**  The complement of `chartPiece k m S` is
`{fibN ≤ 1} ∩ π⁻¹ (G ∖ baseSet S)`, a closed subset of the compact `{fibN ≤ 1}`. -/
theorem isOpen_chartPiece (k m : ℕ) (S : ChartIdx k m) : IsOpen (chartPiece k m S) := by
  have hfar : IsOpen (Torsion.far k m 1) := Torsion.isOpen_far_one k m
  have himg : IsOpen (OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹' baseSet S)) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _
      ((Work.TangentClasses.RealBundle.continuous_proj _).isOpen_preimage _ (isOpen_baseSet S))
  exact hfar.union himg

/-- **The finite intersections of the chart pieces.** -/
theorem iInter_chartPiece (k m : ℕ) (σ : Finset (ChartIdx k m)) :
    (⋂ S ∈ σ, chartPiece k m S)
      = Torsion.far k m 1 ∪ (OnePoint.some '' ((tautologicalBundle k m).proj ⁻¹'
          (⋂ S ∈ σ, baseSet S))) := by
  ext y
  constructor
  · intro hy
    by_cases h : y ∈ Torsion.far k m 1
    · exact Or.inl h
    · refine Or.inr ?_
      have hy' : ∀ S ∈ σ, y ∈ chartPiece k m S := Set.mem_iInter₂.mp hy
      have hE : ∃ p : (tautologicalBundle k m).TotalSpace, OnePoint.some p = y := by
        rcases y with _ | p
        · exact absurd (Torsion.infty_mem_far k m 1) h
        · exact ⟨p, rfl⟩
      obtain ⟨p, rfl⟩ := hE
      refine ⟨p, ?_, rfl⟩
      rw [Set.mem_preimage, Set.mem_iInter₂]
      intro S hS
      rcases hy' S hS with h1 | ⟨q, hq, hqy⟩
      · exact absurd h1 h
      · exact (Option.some.inj hqy) ▸ hq
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Set.mem_iInter₂.mpr (fun S _ => Or.inl h)
    · refine Set.mem_iInter₂.mpr (fun S hS => Or.inr ⟨p, ?_, rfl⟩)
      exact Set.mem_iInter₂.mp hp S hS

/-- The chart pieces indexed by all charts cover the Thom space. -/
theorem iUnion_chartPiece (k m : ℕ) :
    (⋃ S ∈ (Finset.univ : Finset (ChartIdx k m)), chartPiece k m S) = Set.univ := by
  refine Set.eq_univ_of_forall (fun y => ?_)
  rcases y with _ | p
  · exact Set.mem_iUnion₂.mpr ⟨Classical.arbitrary _, Finset.mem_univ _, Or.inl (Torsion.infty_mem_far k m 1)⟩
  · exact Set.mem_iUnion₂.mpr
      ⟨chartCover p.proj, Finset.mem_univ _, Or.inr ⟨p, mem_baseSet_chartCover p.proj, rfl⟩⟩

end

end Work.ThomBordism.Grassmann
