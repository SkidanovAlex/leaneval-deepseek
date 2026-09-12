import Mathlib
import Submission.Work.Lattice.GraysonLattice
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one

/-!
# P1-general (a): boundedness of the rank data for isometry images of the integer lattice

The per-rank Grayson data of a lattice `Λ` (`rankData Λ j = sInf { log covol W | W ≤ Λ,
dim(span W) = j }`) is bounded below — the sub-step that turns `polygon_le_covol`
(which carries an explicit `BddBelow (rankDataSet Λ j)` hypothesis) into a hypothesis-free
lemma for the §3-route lattices `Λ = g(ℤᵈ)`, `g` a linear isometry of `ℝᵈ` (exactly the
lattices produced by the session-91 rotation reduction of item F).

Reduction (family-span form, which is all the realiser/HN subgroups are): a rank-`j`
subgroup is the `ℤ`-span of a `ℝ`-independent family `u : Fin j → ℝᵈ` of lattice points,
and `latticeCovol(span(range u)) = ‖ιMulti u‖` (`latticeCovol_span`).  For
`Λ = g(ℤᵈ)` every such family satisfies `g⁻¹∘u` is an integer family, so — by isometry
invariance of the wedge norm (`norm_iMulti_comp_isometry`) and the **integer-wedge lower
bound** (`Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one`: an `ℝ`-independent
integer-coordinate family has wedge norm `≥ 1`) — every rank-`j` data value is `≥ 0`.

This module records the integer-lattice vocabulary (`stdIntLattice d` = the `ℤ`-span of
the standard coordinate vectors — definitionally the challenge `intPoints`), the
coordinate-integrality of its members, and the two boundedness theorems over family spans
(plain and isometry-preimage form).  All declarations are Mathlib + Submission.GraysonLattice
+ Commons (L74, `norm_iMulti_comp_isometry`) only.
-/

noncomputable section

open Set Module Real
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.GraysonLattice

open Submission.GraysonData

/-- The standard coordinate unit vector `e_t` of `ℝᵈ`. -/
def stdVec (d : ℕ) (t : Fin d) : E d := EuclideanSpace.basisFun (Fin d) ℝ t

/-- The standard integer lattice `ℤᵈ ≤ ℝᵈ` (the `ℤ`-span of the coordinate vectors). -/
def stdIntLattice (d : ℕ) : Submodule ℤ (E d) :=
  Submodule.span ℤ (Set.range (fun t : Fin d => stdVec d t))

/-- Orthonormal expansion: for an orthonormal family `b`, the inner product of `b t` with
the combination `Σᵢ aᵢ • bᵢ` is the coefficient `a t`. -/
lemma inner_basis_sum {d : ℕ} {b : Fin d → E d} (hb : Orthonormal ℝ b) (t : Fin d)
    (a : Fin d → ℝ) :
    ⟪b t, ∑ i : Fin d, a i • b i⟫ = a t := by
  classical
  have hortho : ∀ i : Fin d, ⟪b t, b i⟫ = if i = t then 1 else 0 := by
    intro i
    by_cases hit : i = t
    · subst i
      have hsq : ⟪b t, b t⟫ = 1 := by
        calc
          ⟪b t, b t⟫ = ‖b t‖ ^ 2 := real_inner_self_eq_norm_sq (b t)
          _ = 1 := by rw [hb.1 t]; norm_num
      rw [if_pos rfl]
      exact hsq
    · have hz : ⟪b t, b i⟫ = 0 := hb.2 (by exact fun h => hit h.symm)
      simp [hit, hz]
  calc
    ⟪b t, ∑ i : Fin d, a i • b i⟫ = ∑ i : Fin d, a i • ⟪b t, b i⟫ := by
          change (innerSL ℝ (b t)) (∑ i : Fin d, a i • b i) =
            ∑ i : Fin d, a i • (innerSL ℝ (b t)) (b i)
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_smul]
    _ = a t := by
          rw [Finset.sum_eq_single t]
          · rw [hortho t]
            simp
          · intro i hi hit
            rw [hortho i, if_neg hit]
            simp
          · intro ht
            exact (ht (Finset.mem_univ t)).elim

/-- The coordinates of a member of the integer lattice are integers:
`x t = ⟪stdVec t, x⟫` is the coefficient of the `ℤ`-combination of `x`. -/
lemma coord_mem_stdIntLattice {d : ℕ} {x : E d} (hx : x ∈ stdIntLattice d) (t : Fin d) :
    ∃ z : ℤ, x t = z := by
  classical
  dsimp [stdIntLattice, stdVec] at hx
  rw [Submodule.mem_span_range_iff_exists_fun (α := Fin d) (R := ℤ)
    (v := fun i : Fin d => EuclideanSpace.basisFun (Fin d) ℝ i)] at hx
  rcases hx with ⟨c, hc⟩
  have hb : Orthonormal ℝ (fun i : Fin d => EuclideanSpace.basisFun (Fin d) ℝ i) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal
  have hsum : (∑ i : Fin d, (c i : ℝ) • EuclideanSpace.basisFun (Fin d) ℝ i) = x := by
    calc
      (∑ i : Fin d, (c i : ℝ) • EuclideanSpace.basisFun (Fin d) ℝ i)
          = ∑ i : Fin d, c i • EuclideanSpace.basisFun (Fin d) ℝ i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Int.cast_smul_eq_zsmul ℝ (c i) (EuclideanSpace.basisFun (Fin d) ℝ i)
      _ = x := hc
  refine ⟨c t, ?_⟩
  calc
    x t = ⟪EuclideanSpace.basisFun (Fin d) ℝ t, x⟫ :=
          (EuclideanSpace.basisFun_inner (Fin d) ℝ x t).symm
    _ = ⟪EuclideanSpace.basisFun (Fin d) ℝ t,
          ∑ i : Fin d, (c i : ℝ) • EuclideanSpace.basisFun (Fin d) ℝ i⟫ := by rw [hsum]
    _ = (c t : ℝ) := inner_basis_sum hb t (fun i : Fin d => (c i : ℝ))

/-- An `ℝ`-independent family of integer-coordinate vectors of `ℝᵈ` (`j ≥ 1`) has wedge
norm `≥ 1`. -/
lemma intCoords_ιMulti_norm_ge_one {d j : ℕ} (hj1 : 1 ≤ j) (u : Fin j → E d)
    (huz : ∀ r : Fin j, ∀ t : Fin d, ∃ z : ℤ, u r t = z)
    (hli : LinearIndependent ℝ u) :
    (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ j u‖ := by
  exact Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one (d := d) (j := j) hj1 u huz hli

/-- The covolume of the `ℤ`-span of an integer-coordinate `ℝ`-independent family is `≥ 1`. -/
lemma intCoords_span_covol_ge_one {d j : ℕ} (hj1 : 1 ≤ j) (u : Fin j → E d)
    (huz : ∀ r : Fin j, ∀ t : Fin d, ∃ z : ℤ, u r t = z)
    (hli : LinearIndependent ℝ u) :
    (1 : ℝ) ≤ latticeCovol (Submodule.span ℤ (Set.range u)) := by
  classical
  rw [latticeCovol_span (d := d) (r := j) hj1 u hli]
  exact intCoords_ιMulti_norm_ge_one hj1 u huz hli

/-- Post-composition of a `ℝ`-independent family by an injective linear map is again
`ℝ`-independent. -/
lemma linearIndependent_comp_injective {d j : ℕ} (f : E d →ₗ[ℝ] E d)
    (hf : Function.Injective f) (u : Fin j → E d) (hli : LinearIndependent ℝ u) :
    LinearIndependent ℝ (fun r : Fin j => f (u r)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : (∑ r : Fin j, c r • u r) = 0 := by
    have hpre : f (∑ r : Fin j, c r • u r) = 0 := by
      calc
        f (∑ r : Fin j, c r • u r) = ∑ r : Fin j, c r • f (u r) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro r hr
              rw [map_smul]
        _ = 0 := by simpa using hc
    exact hf (by simpa using hpre)
  exact (Fintype.linearIndependent_iff.mp hli) c hc0

/-- **Isometry-image boundedness (family-span form)**: if `g⁻¹(u r)` is an integer point of
`ℝᵈ` for every `r` (i.e. `u r` belongs to the isometry image `g(ℤᵈ)`), then the covolume of
the `ℤ`-span of the `ℝ`-independent family `u` is `≥ 1` — the elementwise bound
`0 ≤ log covol` behind `BddBelow (rankDataSet Λ j)` for the §3-route lattices. -/
theorem span_covol_ge_one_of_isometry_intPreimage {d j : ℕ} (hj1 : 1 ≤ j)
    (g : E d ≃ₗᵢ[ℝ] E d) (u : Fin j → E d)
    (hpre : ∀ r : Fin j, g.symm (u r) ∈ stdIntLattice d)
    (hli : LinearIndependent ℝ u) :
    (1 : ℝ) ≤ latticeCovol (Submodule.span ℤ (Set.range u)) := by
  classical
  have hliPre : LinearIndependent ℝ (fun r : Fin j => g.symm (u r)) := by
    exact linearIndependent_comp_injective (g.symm : E d →ₗ[ℝ] E d)
      (LinearEquiv.injective (g.symm : E d ≃ₗ[ℝ] E d)) u hli
  have huzPre : ∀ r : Fin j, ∀ t : Fin d, ∃ z : ℤ, (g.symm (u r)) t = z := by
    intro r t
    exact coord_mem_stdIntLattice (hpre r) t
  rw [latticeCovol_span (d := d) (r := j) hj1 u hli]
  calc
    ‖exteriorPower.ιMulti ℝ j u‖
        = ‖exteriorPower.ιMulti ℝ j (fun r : Fin j => g.symm (u r))‖ := by
            exact (Commons.Analysis.InnerProductSpace.norm_iMulti_comp_isometry (E := E d)
              g.symm u).symm
    _ ≥ (1 : ℝ) := intCoords_ιMulti_norm_ge_one hj1 (fun r : Fin j => g.symm (u r))
            huzPre hliPre


/-- **Log form**: for an isometry-image integer preimage family, `0 ≤ log covol(span u)`
(so the family-span rank data are bounded below by `0`). -/
theorem logCovol_nonneg_of_isometry_intPreimage {d j : ℕ} (hj1 : 1 ≤ j)
    (g : E d ≃ₗᵢ[ℝ] E d) (u : Fin j → E d)
    (hpre : ∀ r : Fin j, g.symm (u r) ∈ stdIntLattice d)
    (hli : LinearIndependent ℝ u) :
    (0 : ℝ) ≤ Real.log (latticeCovol (Submodule.span ℤ (Set.range u))) := by
  have hge : (1 : ℝ) ≤ latticeCovol (Submodule.span ℤ (Set.range u)) :=
    span_covol_ge_one_of_isometry_intPreimage hj1 g u hpre hli
  have hpos : 0 < latticeCovol (Submodule.span ℤ (Set.range u)) := lt_of_lt_of_le zero_lt_one hge
  calc
    (0 : ℝ) = Real.log 1 := by simp
    _ ≤ Real.log (latticeCovol (Submodule.span ℤ (Set.range u))) := Real.log_le_log (by norm_num) hge

end Submission.GraysonLattice

end
