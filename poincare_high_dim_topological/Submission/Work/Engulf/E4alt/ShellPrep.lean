import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.hndOfFzvHull

/-!
# `Work.Engulf.E4alt.ShellPrep` — the geometry of one shelled simplex

Everything `Work.Engulf.E4alt.step` needs about a single member `ND.ord[i]` of the shelling order,
read off `NormData` and `L7Hyp`:

* its `f`-image lies in the chart's half cube (`hch` + `ord_sub`), hence in the core `5/8` cube;
* it lies in `L ∪ Rc` (`halfcube_frz`);
* it carries a `ψ`-affine witness with vertex values `vv`, values in the open unit cube (`wit`);
* the frozen vertex values on it are affinely independent (`hndOfFzvHull` + `Fzv_hull`);
* the witness is injective on the simplex (`indep` + the previous point);
* every vertex of it lies in `Vt`, and it has at most `n + 1` vertices.
-/

open Set Metric PL

namespace Work.Engulf.Alt

universe u

variable {n p q : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {N : ℕ} {Γ : PL.Cx N}
  {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M} {ε : ℝ}

/-- The `i`-th shelled simplex has its `f`-image in the chart's half cube. -/
theorem shell_halfcube (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ) :=
  (Set.image_mono (ND.ord_sub _ (List.getElem_mem hi))).trans hch

/-- The `i`-th shelled simplex is a core face: its `f`-image lies in the closed `5/8` cube. -/
theorem shell_core (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) :=
  (shell_halfcube ND hch hi).trans
    (Set.image_mono ((openCube_mono (show (1 : ℝ) / 2 ≤ 5 / 8 by norm_num)).trans
      (openCube_subset_closedCube (5 / 8 : ℝ))))

/-- The `i`-th shelled simplex lies in the frozen region `L ∪ Rc`. -/
theorem shell_LRc (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    PL.simp (ND.ord[i]) ⊆ L ∪ ND.Rc :=
  ND.halfcube_frz _ (ND.ord_mem _ (List.getElem_mem hi)) (shell_halfcube ND hch hi)

/-- The `ψ`-affine witness of `g₁` on the `i`-th shelled simplex, with the vertex values `vv`. -/
theorem shell_wit (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      (∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A x)) ∧
      (∀ x ∈ PL.simp (ND.ord[i]), A x ∈ openCube 1) ∧
      (∀ v ∈ ND.ord[i], A v = ND.vv v) := by
  obtain ⟨A, h1, h2⟩ := ND.wit _ (ND.ord_mem _ (List.getElem_mem hi)) (shell_core ND hch hi)
  exact ⟨A, fun x hx => h1 hx, fun x hx => (h2 x hx).1,
    fun v hv => (h2 v (subset_simp hv)).2 v hv⟩

/-- Every vertex of the `i`-th shelled simplex lies in `Vt`. -/
theorem shell_Vt (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    {i : ℕ} (hi : i < ND.ord.length) : ∀ v ∈ ND.ord[i], v ∈ ND.Vt :=
  fun v hv => (ND.Vt_mem v).mpr ⟨ND.ord[i], ND.ord_mem _ (List.getElem_mem hi), hv⟩

/-- The `i`-th shelled simplex has at most `n + 1` vertices. -/
theorem shell_card (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (A : Work.Engulf.Amb n p M V) (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (hq : q + 1 ≤ p + 1) {i : ℕ} (hi : i < ND.ord.length) :
    (ND.ord[i]).card ≤ n + 1 := by
  rw [ND.ord_card _ (List.getElem_mem hi), H7.card]
  have h1 : q + 1 ≤ p + 1 := hq
  have h2 : q ≤ p := H7.hq
  have h4 : p + 3 ≤ n := A.hp
  omega

/-- The frozen vertex values on the `i`-th shelled simplex are affinely independent. -/
theorem shell_hnd (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) :
    AffineIndependent ℝ (fun v : ↥(ND.ord[i] ∩ ND.Fzv) => ND.vv v) :=
  Work.Engulf.E4alt.hndOfFzvHull ND H7
    (fun s hs hc => ND.Fzv_hull s hs hc)
    (ND.ord_mem _ (List.getElem_mem hi)) (ND.ord_sub _ (List.getElem_mem hi))
    (shell_core ND hch hi)

/-- The witness of `g₁` on the `i`-th shelled simplex is injective on its simplex. -/
theorem shell_injOn (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (A0 : Work.Engulf.Amb n p M V) (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (hq : q + 1 ≤ p + 1)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {i : ℕ} (hi : i < ND.ord.length) (A : PL.E N →ᵃ[ℝ] PL.E n)
    (hA : ∀ v ∈ ND.ord[i], A v = ND.vv v) :
    Set.InjOn A (PL.simp (ND.ord[i])) :=
  ND.indep _ A (shell_card ND A0 H7 hq hi) (shell_Vt ND hi) hA (shell_hnd ND H7 hch hi)

end Work.Engulf.Alt
