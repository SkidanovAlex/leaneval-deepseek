import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Geo.Radial.ChartImage

/-!
# `Work.Engulf.Alt.Defs2` — the output of the `E4a` normalisation

`NormData` bundles everything `E4b`–`E4e` need from the normalisation step of Newman's Lemma 7
Case 1 (see `Submission/Work/Engulf/E4alt/NOTES_E4alt.md`, §2): a fine subdivision `Γ₁` of `Γ`, a
"frozen" map `g₁` close to `f` and equal to `f` on `L`, the frozen region `Rc`, a vertex value map
`vv` on the ambient space, and the affine-witness/general-position facts about it.

Two interface points fixed in the light of `Submission/Work/Engulf/E4alt/NOTES_step_interface.md`:

* `Fzv_hull` replaces the earlier vertex-level `Fzv_core`: the frozen vertices of a *core* face
  must span a set **inside `L`**, not merely lie in it.  This is exactly `SdFullForm` (`Tools.full`)
  applied to `Γ₁`, so it must be proved at a level `r ≥ 1` of `sdIter` (use `Tools.plApproxAt`,
  which lets the level be chosen, rather than `Tools.plApprox`).  It is what makes the frozen vertex
  values affinely independent (`Work.Engulf.E4alt.hndOfFzvHull`) and what makes the `hcol`
  side condition of `gp_pairs_pairwise` follow from `L7Hyp.clean`.
* `pair` no longer asks for the frozen-independence of `σ₂`: `Work.PL.Generic.gp_pairs_pairwise`
  does not need it, and for the collision faces `σ₂ = λ ⊆ K` of `E4b` it is not implied by the
  hypotheses (f is only known to be injective on `L ∩ (K ∪ simp Δ)` through `L7Hyp.clean`).

`AltInner` is the invariant of the shelling loop: as in `E4Aux/NOTES_loop.md` §2 the loop keeps the
map `g := g₁` **fixed** and only moves the homeomorphism `h`, so the invariant carries `h` alone.
-/

open Set Metric PL

namespace Work.Engulf.Alt

universe u

variable {n p q : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-- The result of the `E4a` normalisation.  The radii of `NOTES_E4alt.md` §1 are hard-wired:
`ρ1 = 5/8` (core), `9/16` (the region where the analysis happens), `1/2` (the simplex). -/
structure NormData (n p q N : ℕ) (M : Type*) [MetricSpace M]
    (V X : Set M) (Γ : Cx N) (K L : Set (E N)) (f : E N → M)
    (τ₀ τ₁ : Finset (E N)) (ψ : CubeChart n M) (ε : ℝ) : Type _ where
  /-- the budget of the whole normalisation -/
  η : ℝ
  hη0 : 0 < η
  hη16 : η ≤ 1 / 16
  hηε : η < ε
  /-- the fine subdivision -/
  Γ₁ : Cx N
  hΓ₁ : Γ₁.faces.Finite
  sub : Subdivides Γ₁ Γ
  /-- `Γ₁` refines `Γ` in the *subcomplex* sense: the space of every subcomplex of `Γ` is a
  subcomplex of `Γ₁`.  `Subdivides` alone does not give this (it only says that the faces of `Γ₁`
  lie in faces of `Γ`), yet `step` needs it: a collision partner `y ∈ K` of the bad-set analysis
  must lie in a *face of `Γ₁`* whose simplex is inside `K`, so that that face carries the affine
  witness `NormData.wit` and `L7Hyp.clean` applies to it.  It is `SubdivTools.subsp` applied twice
  along `Γ₁ = S.sdIter r Γ₀`, `Γ₀ = S.sdIter r₀ Γ`. -/
  subsp : ∀ S : Set (E N), IsSubSp Γ S → IsSubSp Γ₁ S
  /-- **carrier**: a face of `Γ₁` whose simplex lies in the subcomplex `L` is contained in a face of
  `Γ` whose simplex lies in `L` (this is `Tools.carrier` applied twice, along `Γ₁ = S.sdIter r Γ₀`
  and `Γ₀ = S.sdIter r₀ Γ`; it is *not* a consequence of `Subdivides Γ₁ Γ`).  `step` needs it to
  obtain `Tame n p X Γ₁ L g₁` from `H7.cfg.tame` and `SmoothChart p X Γ L f ψ`: the local
  `ψ'`-affinity of `f = g₁` on a coarse `L`-face restricts to every fine face inside it, and that is
  the `Cfg.tame` hypothesis of the `B n p q` calls of `E4c`. -/
  carrier : ∀ s ∈ Γ₁.faces, PL.simp s ⊆ L → ∃ t ∈ Γ.faces, PL.simp s ⊆ PL.simp t ∧ PL.simp t ⊆ L
  /-- the shelling of `simp (τ₀ ∪ τ₁)` by the fine `(q+2)`-faces (`SubdivTools.shell`) -/
  ord : List (Finset (E N))
  ord_mem : ∀ t ∈ ord, t ∈ Γ₁.faces
  ord_card : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card
  ord_sub : ∀ t ∈ ord, simp t ⊆ simp (τ₀ ∪ τ₁)
  ord_cov : simp (τ₀ ∪ τ₁) ⊆ ⋃ t ∈ ord, simp t
  ord_split : ∀ i (hi : i < ord.length), ∃ fl : Finset (E N),
      fl.Nonempty ∧ fl ⊂ ord[i] ∧
      simp (ord[i]) ∩ (floorOf τ₀ τ₁ ∪ ⋃ j ∈ Finset.range i,
          ⋃ (hj : j < ord.length), simp (ord[j])) = ⋃ w ∈ fl, simp (ord[i].erase w)
  /-- the frozen map -/
  g₁ : E N → M
  g₁cont : ContinuousOn g₁ Γ₁.space
  g₁frz : EqOn g₁ f L
  g₁near : ∀ x ∈ Γ₁.space, dist (g₁ x) (f x) < η
  /-- `g₁` already engulfs `K` (the base case `i = 0` of the loop) -/
  g₁_eng : X ∪ g₁ '' K ⊆ V
  /-- the vertex set of `Γ₁` -/
  Vt : Finset (E N)
  Vt_mem : ∀ v, v ∈ Vt ↔ ∃ s ∈ Γ₁.faces, v ∈ s
  /-- the frozen region: the union of the faces whose `g₁`-image meets the core cube -/
  Rc : Set (E N)
  Rc_sub : IsSubSp Γ₁ Rc
  Rc_mem : ∀ x ∈ Γ₁.space, g₁ x ∈ ψ.toFun '' closedCube (5 / 8 : ℝ) → x ∈ Rc
  Rc_face : ∀ s ∈ Γ₁.faces, (∃ x ∈ simp s, g₁ x ∈ ψ.toFun '' closedCube (5 / 8 : ℝ)) →
    simp s ⊆ Rc
  /-- faces whose `f`-image lies in the half cube are frozen -/
  halfcube_frz : ∀ s ∈ Γ₁.faces, f '' simp s ⊆ ψ.toFun '' openCube (1 / 2 : ℝ) →
    simp s ⊆ L ∪ Rc
  /-- the vertex values of the perturbed chart map -/
  vv : E N → E n
  /-- affine witnesses on the faces whose `f`-image lies in the core cube -/
  wit : ∀ s ∈ Γ₁.faces, f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) →
    ∃ A : E N →ᵃ[ℝ] E n, EqOn g₁ (fun x => ψ.toFun (A x)) (simp s) ∧
      ∀ x ∈ simp s, A x ∈ openCube 1 ∧ ∀ v ∈ s, A v = vv v
  /-- mesh fineness: every face either has its `f`-image in the core cube or its `g₁`-image misses
  the `9/16`-cube (a consequence of a fine enough subdivision, see `NOTES_E4alt.md` §2.4) -/
  mesh : ∀ s ∈ Γ₁.faces, f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) ∨
    ∀ x ∈ simp s, g₁ x ∉ ψ.toFun '' closedCube (9 / 16 : ℝ)
  /-- **the shelled simplices sit in the `17/32` cube**: the perturbed vertex values of the
  vertices of `simp (τ₀ ∪ τ₁)` are within `ε_pl + ε_gp ≤ 1/32` of `chartInv ψ (f v)`, which lies in
  `openCube (1/2)` (`hch`).  `openCube (17/32)` is convex, so the *witness* `A` of a face inside
  `simp (τ₀ ∪ τ₁)` (`wit`) takes the face into `openCube (17/32)` as well.  `step` needs this to
  choose the push's support `W` inside `openCube (9/16)` (since `17/32 < 9/16`), which is what puts
  the support strictly inside the `9/16`-cube where the bad-set analysis is available. -/
  shell17 : ∀ v ∈ Vt, v ∈ PL.simp (τ₀ ∪ τ₁) → vv v ∈ openCube (17 / 32 : ℝ)
  /-- the vertices not moved by the perturbation (`Gp`'s `fz`) -/
  Fzv : Finset (E N)
  Fzv_sub : Fzv ⊆ Vt
  /-- **the convex hull of the frozen vertices of a core face lies in `L`** (the strengthened form
  of the old vertex-level `Fzv_core`; it is `SdFullForm` applied to `Γ₁`, so it must be proved at a
  level `r ≥ 1` of `sdIter`).  `Work.Engulf.E4alt.hndOfFzvHull` derives the affine independence of
  `vv` on `σ ∩ Fzv` from this. -/
  Fzv_hull : ∀ s ∈ Γ₁.faces, f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) →
    PL.simp (s ∩ Fzv) ⊆ L
  /-- the affine maps with vertex values `vv` on a vertex set of `Γ₁` are injective on the simplex
  (general position: `affineIndependent_of_gp`) -/
  indep : ∀ (σ : Finset (E N)) (A : E N →ᵃ[ℝ] E n), σ.card ≤ n + 1 → (∀ v ∈ σ, v ∈ Vt) →
      (∀ v ∈ σ, A v = vv v) →
      AffineIndependent ℝ (fun v : ↥(σ ∩ Fzv) => vv v) →
      Set.InjOn A (simp σ)
  /-- the pairwise general position bound (`gp_pairs_pairwise`); only the `hcol` side condition is
  left to the consumer (`L7Hyp.clean` supplies it) -/
  pair : ∀ (σ₁ σ₂ : Finset (E N)) (A₁ A₂ : E N →ᵃ[ℝ] E n),
      σ₁.card ≤ n + 1 → σ₂.card ≤ n + 1 → (∀ v ∈ σ₁, v ∈ Vt) → (∀ v ∈ σ₂, v ∈ Vt) →
      (∀ v ∈ σ₁, A₁ v = vv v) → (∀ v ∈ σ₂, A₂ v = vv v) →
      (∀ z ∈ A₁ '' simp (σ₁ ∩ Fzv) ∩ A₂ '' simp (σ₂ ∩ Fzv),
        (∃ v ∈ σ₁ ∩ σ₂, v ∉ Fzv) → z ∈ A₁ '' simp (σ₁ ∩ σ₂ ∩ Fzv)) →
      ∃ D : Set (E n), PL.DomDim D ((σ₁.card : ℤ) + (σ₂.card : ℤ) - 2 - (n : ℤ)) ∧
        A₁ '' simp σ₁ ∩ A₂ '' simp σ₂ ⊆
          A₁ '' simp (σ₁ ∩ σ₂) ∪ (A₁ '' simp (σ₁ ∩ Fzv) ∩ A₂ '' simp (σ₂ ∩ Fzv)) ∪ D
  /-- the `X`-cover: the `DomDim p` simplices covering the `X`-points of the unit cube.  It is
  `SmoothChart.1` (`DomIn p ψ X`, i.e. `∃ P, PL.DomDim P p ∧ ∀ y ∈ closedCube 1, ψ y ∈ X → y ∈ P`)
  unwound into its cover.  The vertex bound `Xcov_card` is what collapses the `DomDim` index of
  `fixed` to `q - 2` (`q + 2 + (p+1) - 2 - n ≤ q - 2`), so it must **not** be dropped: do not
  take `Xcov` to be a triangulation of the whole cube. -/
  Xcov : Finset (Finset (E n))
  Xcov_card : ∀ S ∈ Xcov, S.card ≤ p + 1
  Xcov_cov : ∀ y ∈ closedCube (1 : ℝ), ψ.toFun y ∈ X → y ∈ ⋃ S ∈ Xcov, simp S
  /-- the "fixed" general position bound (`gp_pairs_fixed`) -/
  fixed : ∀ (σ S : Finset (E N)) (A : E N →ᵃ[ℝ] E n) (T : Finset (E n)),
      σ.card ≤ n + 1 → (∀ v ∈ σ, v ∈ Vt) → (∀ v ∈ σ, A v = vv v) →
      AffineIndependent ℝ (fun v : ↥(σ ∩ Fzv) => vv v) → T ∈ Xcov →
      ∃ D : Set (E n), PL.DomDim D ((σ.card : ℤ) + (T.card : ℤ) - 2 - (n : ℤ)) ∧
        A '' simp σ ∩ simp T ⊆ A '' simp (σ ∩ Fzv) ∪ D

/-- Invariant of the shelling loop of `E4e`: after `i` steps the homeomorphism `h` has captured
the `g₁`-images of `K` and of the `q`-skeleton `⋃_{j<i} ∂ ord[j]` of the first `i` members of the
shelling order.  The map of the conclusion is *not* part of the loop: the loop keeps `g := g₁`
fixed (`E4Aux/NOTES_loop.md` §2), which is what makes the `9/16`-cube bookkeeping harmless. -/
structure AltInner (V X : Set M) (K : Set (E N)) (g₁ : E N → M)
    (ord : List (Finset (E N))) (i : ℕ) (h : M ≃ₜ M) : Prop where
  le : i ≤ ord.length
  supp : CSupp h univ
  eng : X ∪ g₁ '' (K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length),
          ⋃ w ∈ ord[j], simp (ord[j].erase w)) ⊆ h '' V

end Work.Engulf.Alt
