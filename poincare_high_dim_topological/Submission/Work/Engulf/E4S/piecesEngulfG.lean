import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4P.PiecesEngulfG

open Set Metric PL

namespace Work.Engulf.E4S

/-- **`E4c`, the piece loop** (Newman §§13–14), moving-map form: the design is
`Submission/Work/NOTES_LEAD_poincare_E4c.md` §A.3, the compiled interface
`Submission/Work/lead_engulf/E4cIface.lean.txt`.  It supersedes the fixed-map
`Work.Engulf.E4Aux.piecesEngulf` (which is FALSE).

Setting: the `E4a` normalisation `ND`, the new field-shaped fact `Core11`, `H7`, `Amb`, `SCh`,
`hB : B n p q`, a `Γ₁`-subcomplex `G` all of whose faces have `≤ p+1` vertices, a map `g`
continuous on `Γ₁.space` and **frozen on `L ∪ coreSet`** (Newman (13.3)), a compactly supported `h`
with `X ∪ g '' G ⊆ h '' V`, the prism data of the shelled simplex and a closed `(q-2)`-dominated
`J ⊆ F` whose region lies in the `9/16` cube, and a budget `β > 0`.

Conclusion: `g'`, `h'` with `g'` continuous on `Γ₁.space`, `g' = g` on `L ∪ coreSet`,
`dist (g' x) (g x) < β` on `Γ₁.space`, `CSupp h' univ`, `X ∪ g' '' G ⊆ h' '' V`, and the region over
`J` engulfed.

Proof recipe (§A.3, do not deviate): `Work.Engulf.E4alt.exists_pieces` with `J₀ := J` and small `δ`
gives pieces `s₁…s_R`, each of card `≤ q`, lying in `cl(11/16)` chart coordinates, affinely
independent (`Work.Engulf.E4Aux.prism_cover` / `Work.Engulf.Auxi.exists_indep_cover`), covering the
region over `J`.  Then a loop `k = 0…R` with state `(Γc, gc, hc)`: `Γ₁ ⊆ Γc` with the far pieces
added so far (`Work.Engulf.Auxi.exists_far_piece`); `gc = g` on `L ∪ coreSet`; `gc = ψ ∘ A_j` on
piece `j`; `dist (gc, g) < k·β/(R+1)` on `Γ₁.space`; `X ∪ gc '' (G ∪ P_{<k}) ⊆ hc '' V`.  Step `k`:
add `s_k` as a far piece, set `gc := ψ ∘ A_k` on it, and call `hB` with `H := G ∪ P_{≤k}`,
`Lc := L ∪ coreSet ∪ P_{≤k}` and `ε := β/(R+1)`; one single
`Work.Engulf.Auxi.tame_extend` call with `L₀ := L`, `L₁ := ∅`, `S := coreSet ∪ (far pieces)`,
`ρ := 11/16`, whose `hψ` comes from `SCh` + `ND.wit` + `ψ ∘ affine` and whose `hSim` is `Core11`;
`OvCtl` with `C := (G ∩ Lc) ∪ P_{<k} ∪ (P_k ∩ gc⁻¹ (X ∪ gc '' ((G ∩ Lc) ∪ P_{<k})))`; and
`BadCard q` from `Work.Engulf.Auxi.face_subset_of_subset_union` (faces of `G ∪ P_{<k}` map into
`hc '' V`, `P_k` has card `≤ q`).  The call returns `g'', h''` with
`X ∪ g'' '' (G ∪ P_{≤k}) ⊆ h'' '' (hc '' V)` and `g'' = gc` on `Lc`; set `hc := h'' ∘ hc`.  At the
end restrict `g'` to `Γ₁.space`; the region over `J` lies in `⋃ ψ '' simp s_k = ⋃ gc '' P_k`, and the
accumulated distance is `< β`.  The templates for the loop are
`Submission/Work/Engulf/E1B/step.lean` + `Submission/Work/Engulf/E1B/group.lean`.

If a proved instance of exactly this statement becomes available while you work (for example
`Work.Engulf.E4P.piecesEngulfG`, area E4P), applying it is a complete answer for this lemma. -/
theorem piecesEngulfG {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M}
    {Γ : PL.Cx N} {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)}
    {ψ : PL.CubeChart n M} {ε : ℝ} (T : Work.Engulf.ToolsAllM M n)
    (hB : Work.Engulf.BM M n p q)
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (A : Work.Engulf.Amb n p M V) (SCh : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hq : q + 1 ≤ p + 1)
    {G : Set (PL.E N)} (hGsub : Work.Engulf.IsSubSp ND.Γ₁ G)
    (hGdim : ∀ s ∈ ND.Γ₁.faces, PL.simp s ⊆ G → s.card ≤ p + 1)
    {g : PL.E N → M} (hgc : ContinuousOn g ND.Γ₁.space)
    (hgfrz : Set.EqOn g ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ))
    {h : M ≃ₜ M} (hsupp : PL.CSupp h (Set.univ : Set M)) (heng : X ∪ g '' G ⊆ h '' V)
    {Φ : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q} {F : Set (PL.E q)} {γ₀ γ₁ : PL.E q → ℝ}
    (hFc : IsCompact F) (hFconv : Convex ℝ F) (hγ₀c : Continuous γ₀) (hγ₁c : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z)
    {J : Set (PL.E q)} (hJF : J ⊆ F) (hJd : PL.DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
    (hsmall : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      Φ.symm ((0 : PL.E (n - q - 1)), z, t) ∈ PL.openCube (n := n) (9 / 16 : ℝ))
    {β : ℝ} (hβ : 0 < β) :
    ∃ (g' : PL.E N → M) (h' : M ≃ₜ M), ContinuousOn g' ND.Γ₁.space ∧
      Set.EqOn g' g (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ∧
      (∀ x ∈ ND.Γ₁.space, dist (g' x) (g x) < β) ∧
      PL.CSupp h' (Set.univ : Set M) ∧ X ∪ g' '' G ⊆ h' '' V ∧
      ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        ψ.toFun (Φ.symm ((0 : PL.E (n - q - 1)), z, t)) ∈ h' '' V := by
  -- redirect: area E4P owns the proof of the piece loop `E4c` (Newman §§13–14); this file only
  -- re-states it under the name used by `Work.Engulf.E4S.StepG`.
  exact Work.Engulf.E4P.piecesEngulfG (β := β) T hB ND hc11 H7 A SCh hq hGsub hGdim hgc hgfrz
    hsupp heng hFc hFconv hγ₀c hγ₁c hle hJF hJd hJc hsmall hβ
end Work.Engulf.E4S
