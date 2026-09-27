import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2

/-!
# `Work.Engulf.Alt.Defs3` — the Newman `E4c`/`E4d` interface (moving map)

`Submission/Work/NOTES_LEAD_poincare_E4c.md` §A: the `E4c` piece loop cannot keep the map fixed at
`g₁` (a `B n p q` call only controls its *returned* map on its frozen set).  Newman's (13.3) instead
lets the loop carry a **moving** map `g` which agrees with `g₁` on `L ∪ Core`, where `Core` is the
union of the *core* faces of `Γ₁` (the faces whose `f`-image lies in the closed `5/8`-cube) — those
are exactly the faces carrying a `wit`-witness, hence `ψ`-affine.

* `coreSet Γ₁ f ψ` — the core faces;
* `AltInnerG … g h` — Newman's (13.2)–(13.4);
* `Core11 ND` — the one strengthening of `E4a` the frozen core needs: a point of `Γ₁.space` whose
  `f`-image is in the `5/8`-cube has `g₁`-image in the `11/16`-cube.  (This makes `g '' Core`
  sit inside `ψ '' closedCube (11/16)`, which is the `hSim` hypothesis of `Auxi.tame_extend`.)
* `CarrierS ND` — the carrier property of `SubdivTools` for *arbitrary* subcomplexes of `Γ`.
-/

open Set Metric PL

namespace Work.Engulf.Alt

universe u

variable {n p q : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {N : ℕ} {Γ : PL.Cx N}
  {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M} {ε : ℝ}

/-- The union of the **core** faces of `Γ₁`: those whose `f`-image lies in the closed `5/8`-cube.
They are exactly the faces for which `NormData.wit` provides a `ψ`-affine witness, and the moving map
of the `E4c` loop is frozen on `L ∪ coreSet`. -/
def coreSet (Γ₁ : PL.Cx N) (f : PL.E N → M) (ψ : PL.CubeChart n M) : Set (PL.E N) :=
  ⋃ s ∈ Γ₁.faces, ⋃ (_ : f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)), PL.simp s

/-- **Newman's (13.2)–(13.4)** for the `E4c` piece loop: a moving map `g` which agrees with `g₁` on
`L ∪ Cr` (`Cr = coreSet`), stays within `i * β` of `g₁`, and whose image of the engulfed `q`-skeleton
of the first `i` shelled simplices is carried into `h '' V` by the moving homeomorphism `h`. -/
structure AltInnerG (V X : Set M) (K L Cr : Set (E N)) (Γ₁ : PL.Cx N) (g₁ : E N → M)
    (ord : List (Finset (E N))) (β : ℝ) (i : ℕ) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le : i ≤ ord.length
  supp : CSupp h univ
  cont : ContinuousOn g Γ₁.space
  frz : EqOn g g₁ (L ∪ Cr)
  near : ∀ x ∈ Γ₁.space, dist (g x) (g₁ x) ≤ i * β
  eng : X ∪ g '' (K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length),
          ⋃ w ∈ ord[j], simp (ord[j].erase w)) ⊆ h '' V

/-- The `E4a` fact that a point of `Γ₁.space` whose `f`-image lies in the `5/8`-cube has `g₁`-image
in the `11/16`-cube (it is the strengthened form of the bound `A '' simp s ⊆ openCube 1` of
`NormData.wit`; needed so that `Auxi.tame_extend` can absorb the frozen core with `ρ := 11/16`). -/
def Core11 (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε) : Prop :=
  ∀ x ∈ ND.Γ₁.space, f x ∈ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) →
    ND.g₁ x ∈ ψ.toFun '' PL.closedCube (11 / 16 : ℝ)

/-- The carrier property of the subdivision for *arbitrary* subcomplexes of `Γ`: a face of `Γ₁`
inside `S` lies in a face of `Γ` inside `S`.  (The `NormData.carrier` field is the case `S = L`.) -/
def CarrierS (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε) : Prop :=
  ∀ S : Set (PL.E N), IsSubSp Γ S → ∀ s ∈ ND.Γ₁.faces, PL.simp s ⊆ S →
    ∃ t ∈ Γ.faces, PL.simp s ⊆ PL.simp t ∧ PL.simp t ⊆ S

end Work.Engulf.Alt
