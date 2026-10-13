/-
  CoreStep: `Work.CoreStep.semiPf_inter_exists`.

  Two restricted semi-Pfaffian sets `X`, `Y` in `ℝ^k` of format `≤ F` have a common
  representative `Z` of the point set `X.set ∩ Y.set` with format `≤ 2 * F` and degree
  bounded by `2 * (1 + F) * (1 + (X.deg + Y.deg))^2`.

  The construction is the "conjunction of two DNFs over the concatenated chain" of
  `Submission.Work.WilE7.SemiPfInter`: `Work.WilE7.interSet X Y` has point set `X.set ∩ Y.set`
  (`Work.WilE7.interSet_set`).

  The degree estimate has the same shape as the one for the product (`Work.WilE7.prodDeg`):
  a conjunction of two branches has degree at most the sum of the two degrees, so the degree of
  the conjunction of the two DNFs is at most
  `(number of branches of one) * (degree of the other) + (number of branches of the other) *
  (degree of one)`, and the branch count is controlled by the degree once a *trivial* branch
  (no equations, no inequalities) is collapsed to a single one, which is what
  `Work.WilE7.redBasics` does.  Indeed, a list of `m` trivial branches has degree `0` but length
  `m`, so without that collapse no bound in terms of `X.deg`, `Y.deg` alone can hold.
-/
import Mathlib
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.sumProduct

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

namespace SemiPfInterAux

/-! ## The normalised representative of a semi-Pfaffian set -/

/-- The normalised representative of a semi-Pfaffian set: the DNF list is replaced by
`Work.WilE7.redBasics`, which collapses a trivial branch to a single one (and hence bounds the
number of branches by `max 1 X.deg`).  The point set and the format are unchanged. -/
def normSemiPf {k : ℕ} (X : SemiPf k) : SemiPf k := ⟨X.r, X.c, Work.WilE7.redBasics X⟩

@[simp] theorem normSemiPf_r {k : ℕ} (X : SemiPf k) : (normSemiPf X).r = X.r := rfl

@[simp] theorem normSemiPf_c {k : ℕ} (X : SemiPf k) : (normSemiPf X).c = X.c := rfl

@[simp] theorem normSemiPf_basics {k : ℕ} (X : SemiPf k) :
    (normSemiPf X).basics = Work.WilE7.redBasics X := rfl

/-- Normalising the DNF list does not change the point set. -/
theorem normSemiPf_set {k : ℕ} (X : SemiPf k) : (normSemiPf X).set = X.set := by
  have h := Work.WilE7.exists_holds_redBasics X
  ext z
  simp only [SemiPf.set, normSemiPf_basics, normSemiPf_c, Set.mem_ofPred_eq]
  exact ⟨fun hh => ⟨hh.1, (h z).mp hh.2⟩, fun hh => ⟨hh.1, (h z).mpr hh.2⟩⟩

/-! ## The degree of a conjunction of two branches -/

/-- `atomDeg` does not increase under the variable renaming `Work.WilE7.EAPoly.inl`. -/
theorem atomDeg_inl_le {k r₁ r₂ : ℕ} (Q : EAPoly k r₁) :
    atomDeg (Work.WilE7.EAPoly.inl (r₂ := r₂) Q) ≤ atomDeg Q :=
  Nat.add_le_add_right
    (MvPolynomial.totalDegree_rename_le (Sum.map id (Fin.castAdd r₂)) Q) 1

/-- `atomDeg` does not increase under the variable renaming `Work.WilE7.EAPoly.inr`. -/
theorem atomDeg_inr_le {k r₁ r₂ : ℕ} (Q : EAPoly k r₂) :
    atomDeg (Work.WilE7.EAPoly.inr (r₁ := r₁) Q) ≤ atomDeg Q :=
  Nat.add_le_add_right
    (MvPolynomial.totalDegree_rename_le (Sum.map id (Fin.natAdd r₁)) Q) 1

/-- Conjoining two branches does not raise the degree: `Work.WilE7.interBasic` only renames the
variables of the two sides and concatenates the two lists of atoms. -/
theorem deg_interBasic_le {k r r' : ℕ} (B : Basic k r) (B' : Basic k r') :
    (Work.WilE7.interBasic B B').deg ≤ B.deg + B'.deg := by
  have h1 : ((B.eqs.map (Work.WilE7.EAPoly.inl (r₂ := r'))).map atomDeg).sum
      ≤ (B.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B.eqs _ _
      (fun Q _ => atomDeg_inl_le (r₂ := r') Q)
  have h2 : ((B.pos.map (Work.WilE7.EAPoly.inl (r₂ := r'))).map atomDeg).sum
      ≤ (B.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B.pos _ _
      (fun Q _ => atomDeg_inl_le (r₂ := r') Q)
  have h3 : ((B'.eqs.map (Work.WilE7.EAPoly.inr (r₁ := r))).map atomDeg).sum
      ≤ (B'.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B'.eqs _ _
      (fun Q _ => atomDeg_inr_le (r₁ := r) Q)
  have h4 : ((B'.pos.map (Work.WilE7.EAPoly.inr (r₁ := r))).map atomDeg).sum
      ≤ (B'.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B'.pos _ _
      (fun Q _ => atomDeg_inr_le (r₁ := r) Q)
  simp only [Basic.deg, Work.WilE7.interBasic, List.map_append, List.sum_append]
  linarith

end SemiPfInterAux

/-! ## The intersection -/

theorem semiPf_inter_exists (F k : ℕ) (X Y : WilkiesDesign.E.SemiPf k)
    (hX : X.fmt ≤ F) (hY : Y.fmt ≤ F) :
    ∃ Z : WilkiesDesign.E.SemiPf k,
      Z.set = X.set ∩ Y.set ∧ Z.fmt ≤ 2 * F ∧
      Z.deg ≤ 2 * (1 + F) * (1 + (X.deg + Y.deg)) ^ 2 := by
  refine ⟨Work.WilE7.interSet (SemiPfInterAux.normSemiPf X) (SemiPfInterAux.normSemiPf Y),
    ?_, ?_, ?_⟩
  · -- point set
    rw [Work.WilE7.interSet_set]
    exact congrArg₂ Set.inter (SemiPfInterAux.normSemiPf_set X)
      (SemiPfInterAux.normSemiPf_set Y)
  · -- format
    have hXr : k + X.r ≤ F := hX
    have hYr : k + Y.r ≤ F := hY
    show k + ((SemiPfInterAux.normSemiPf X).r + (SemiPfInterAux.normSemiPf Y).r) ≤ 2 * F
    rw [SemiPfInterAux.normSemiPf_r, SemiPfInterAux.normSemiPf_r]
    omega
  · -- degree
    have hsum : (Work.WilE7.interSet (SemiPfInterAux.normSemiPf X)
        (SemiPfInterAux.normSemiPf Y)).deg
        ≤ (((Work.WilE7.redBasics X).product (Work.WilE7.redBasics Y)).map
            (fun p : Basic k X.r × Basic k Y.r => p.1.deg + p.2.deg)).sum := by
      show (List.map (fun b : Basic k (X.r + Y.r) => b.deg)
          (List.map (fun b => Work.WilE7.interBasic b.1 b.2)
            ((Work.WilE7.redBasics X).product (Work.WilE7.redBasics Y)))).sum
        ≤ (List.map (fun p : Basic k X.r × Basic k Y.r => p.1.deg + p.2.deg)
            ((Work.WilE7.redBasics X).product (Work.WilE7.redBasics Y))).sum
      rw [List.map_map]
      refine Work.WilE7.sum_map_le_of_pointwise _ _ _ ?_
      rintro ⟨B, B'⟩ -
      exact SemiPfInterAux.deg_interBasic_le B B'
    rw [Work.WilE7.sumProduct] at hsum
    refine le_trans hsum (le_trans (Work.WilE7.deg_bound_arith X.deg Y.deg
      (Work.WilE7.redBasics X).length (Work.WilE7.redBasics Y).length
      ((Work.WilE7.redBasics X).map Basic.deg).sum ((Work.WilE7.redBasics Y).map Basic.deg).sum
      (Work.WilE7.redBasics_length_le X) (Work.WilE7.redBasics_length_le Y)
      (Work.WilE7.redBasics_deg_le X) (Work.WilE7.redBasics_deg_le Y)) ?_)
    have h2 : 2 ≤ 2 * (1 + F) := by omega
    exact Nat.mul_le_mul_right _ h2

end Work.CoreStep
