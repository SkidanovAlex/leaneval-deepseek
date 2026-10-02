import Mathlib
import Submission.Work.Whitney.RankTwo.Faces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The explicit chain and its boundary

`Z = Σ_{k<6} S_k` is the cone over the inscribed hexagon and `c = Σ_{k<6} arc k` its boundary
cycle.  The radial faces telescope (`δ 1 S_k = δ 2 S_{k+1}`), which uses the closure
`rad 6 = rad 0` of the hexagon.
-/

namespace Work.Whitney.RankTwo

open Work.Thom
open CategoryTheory AlgebraicTopology
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- `ℤ` as a module, spelled once. -/
abbrev zR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The chain `Z = Σ_{k<6} S_k`, the cone over the inscribed hexagon. -/
def Z (y : Y) : ((ssX Y).chainComplex zR).X 2 :=
  ∑ k ∈ Finset.range 6, ((ssX Y).ιChainComplex (R := zR) (secSimp Y y k)).hom 1

/-- The chain `c = Σ_{k<6} arc k`, the boundary cycle. -/
def c (y : Y) : ((ssX Y).chainComplex zR).X 1 :=
  ∑ k ∈ Finset.range 6, ((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1

/-! ## The radial segments at angle `2π` and `0` agree -/

theorem u2_two_pi : u2 (2 * Real.pi) = u2 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;>
    simp [u2, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]

/-- The fibre point on the ray at angle `θ` at radius `r` is the inverse image of `r • u2 θ`. -/
theorem fibCone_ray (r θ : ℝ) : fibCone (r * θ) r = (tcmSumLin 1 1).symm (r • u2 θ) := by
  rcases eq_or_ne r 0 with h | h
  · subst h; simp [fibCone]
  · rw [fibCone, mul_div_cancel_left₀ θ h]

theorem radC_apply (y : Y) (k : ℕ) (q : stdSimplex ℝ (Fin 2)) :
    radC Y y k q = (y, (tcmSumLin 1 1).symm (q 1 • u2 (ang k))) := by
  simp only [radC, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.mul_apply, coord_apply, fibConeCM_apply,
    fibConeP]
  rw [fibCone_ray]

theorem radC_six_eq (y : Y) : radC Y y 6 = radC Y y 0 := by
  apply ContinuousMap.ext
  intro q
  rw [radC_apply, radC_apply, ang_six, ang_zero, u2_two_pi]

theorem radSimp_six_eq (y : Y) : radSimp Y y 6 = radSimp Y y 0 := by
  apply (sEquiv Y 1).injective
  rw [sEquiv_radSimp, sEquiv_radSimp, radC_six_eq]

/-! ## The boundary of a single sector -/

theorem d_secSimp (y : Y) (k : ℕ) :
    (((ssX Y).chainComplex zR).d 2 1) ((((ssX Y).ιChainComplex (R := zR)
      (secSimp Y y k)).hom (1 : zR))) =
      ((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1
        - ((ssX Y).ιChainComplex (R := zR) (radSimp Y y (k + 1))).hom 1
        + ((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1 := by
  show ((ssX Y).chainComplex zR).d (1+1) 1 (((ssX Y).ιChainComplex (R := zR)
      (secSimp Y y k)).hom (1 : zR))
      = ((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1
        - ((ssX Y).ιChainComplex (R := zR) (radSimp Y y (k + 1))).hom 1
        + ((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1
  have h := congrArg (fun (g : zR ⟶ ((ssX Y).chainComplex zR).X 1) => g.hom (1 : zR))
    (SSet.ιChainComplex_d (ssX Y) zR (secSimp Y y k))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  rw [Fin.sum_univ_three]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply]
  norm_num
  rw [show (((ssX Y).δ (0 : Fin 3)) (secSimp Y y k)) = arcSimp Y y k from ssX_δ_zero_secSimp Y y k]
  rw [show (((ssX Y).δ (1 : Fin 3)) (secSimp Y y k)) = radSimp Y y (k + 1) from
    ssX_δ_one_secSimp Y y k]
  rw [show (((ssX Y).δ (2 : Fin 3)) (secSimp Y y k)) = radSimp Y y k from ssX_δ_two_secSimp Y y k]
  rw [sub_eq_add_neg]

/-! ## The telescoping of the radial faces -/

theorem sum_range_succ_eq {M : Type} [AddCommGroup M] (f : ℕ → M) (n : ℕ) (h : f n = f 0) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.range n, f k := by
  have h1 : (∑ k ∈ Finset.range (n + 1), f k) = (∑ k ∈ Finset.range n, f (k + 1)) + f 0 :=
    Finset.sum_range_succ' f n
  have h2 : (∑ k ∈ Finset.range (n + 1), f k) = (∑ k ∈ Finset.range n, f k) + f n :=
    Finset.sum_range_succ f n
  rw [h2, h] at h1
  exact (add_right_cancel h1).symm

/-- **The boundary of the cone over the hexagon is the cycle of arcs.** -/
theorem d_Z (y : Y) : (((ssX Y).chainComplex zR).d 2 1) (Z Y y) = c Y y := by
  rw [Z, c]
  rw [map_sum]
  have hsec : ∀ k ∈ Finset.range 6,
      (((ssX Y).chainComplex zR).d 2 1)
        (((ssX Y).ιChainComplex (R := zR) (secSimp Y y k)).hom 1)
        = ((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1
          - ((ssX Y).ιChainComplex (R := zR) (radSimp Y y (k + 1))).hom 1
          + ((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1 :=
    fun k _ => d_secSimp Y y k
  rw [Finset.sum_congr rfl hsec]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have htel : (∑ k ∈ Finset.range 6, ((ssX Y).ιChainComplex (R := zR)
      (radSimp Y y (k + 1))).hom 1)
      = ∑ k ∈ Finset.range 6, ((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1 :=
    sum_range_succ_eq (fun k => ((ssX Y).ιChainComplex (R := zR) (radSimp Y y k)).hom 1) 6
      (by rw [radSimp_six_eq])
  rw [htel]
  abel

end

end Work.Whitney.RankTwo
