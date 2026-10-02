import Mathlib
import Submission.Work.Kunneth.Assembly.theta

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The "collapse" map `thetaOdd` is bijective (odd degrees)

The odd-degree companion of `Work.Kunneth.Asm.theta_bijective`
(`Submission/Work/Kunneth/Assembly/theta.lean`), for the family map
`(x_i)_{i<m, i≤k} ↦ Σ_i kSingle_{τ i} (x_i ⊗ ζ^i)` in *odd* total degree `2k+1`, with the
bidegrees `τ i = (2k+1-2i, 2i)`.
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The bidegree of the `i`-th summand of `Work.Kunneth.Asm.thetaOdd`: `(2k+1-2i, 2i)`. -/
def tauOdd (m : ℕ) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) : Work.Kunneth.tpIdx (2 * k + 1) :=
  ⟨(2 * k + 1 - 2 * (i : ℕ), 2 * (i : ℕ)), by have := i.2; omega⟩

theorem tauOdd_injective (m k : ℕ) : Function.Injective (tauOdd m k) := by
  intro i j hij
  have h1 : 2 * (i : ℕ) = 2 * (j : ℕ) := congrArg (fun pq => pq.1.2) hij
  have h2 : (i : ℕ) = (j : ℕ) := by omega
  exact Subtype.ext (Fin.ext h2)

/-- The value of the `i`-th summand of `thetaOdd` at its own bidegree `τ i`. -/
theorem thetaTermOdd_tau (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    (thetaTermOdd m B k i x) (tauOdd m k i) = x ⊗ₜ[ℤ]
      Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ) := by
  rw [thetaTermOdd]
  show kSingle (ssB B) (ssB (Qb m)) (2 * k + 1) (tauOdd m k i)
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ))
      (tauOdd m k i) = _
  exact kSingle_self _ _ _ _ _

/-- The value of the `j`-th summand of `thetaOdd` at a different bidegree vanishes. -/
theorem thetaTermOdd_ne (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (j : {i : Fin m // (i : ℕ) ≤ k}) (rs : Work.Kunneth.tpIdx (2 * k + 1))
    (h : rs ≠ tauOdd m k j) (x : Coh ℤ (2 * k + 1 - 2 * (j : ℕ)) B) :
    (thetaTermOdd m B k j x) rs = 0 := by
  rw [thetaTermOdd]
  show kSingle (ssB B) (ssB (Qb m)) (2 * k + 1) (tauOdd m k j)
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (j : ℕ)) rs = _
  exact kSingle_of_ne _ _ _ h _

/-- The value of `thetaOdd` at the index `τ i`. -/
theorem thetaOdd_tau (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B)
    (i : {i : Fin m // (i : ℕ) ≤ k}) :
    (thetaOdd m B k xf) (tauOdd m k i)
      = xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ) := by
  rw [thetaOdd, Finset.sum_apply]
  have h : ∀ j : {i : Fin m // (i : ℕ) ≤ k},
      (thetaTermOdd m B k j (xf j)) (tauOdd m k i)
        = if j = i then xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
            (Work.LerayHirsch.trivCore m) (i : ℕ) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [thetaTermOdd_tau, if_pos rfl]
    · rw [thetaTermOdd_ne m B k j (tauOdd m k i)
        (fun hh => hj (tauOdd_injective m k hh.symm)) (xf j), if_neg hj]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]

/-- An index of `tpIdx (2k+1)` is of the form `τ i` exactly when its second coordinate is even and
`< 2m`. -/
theorem mem_range_tauOdd {m k : ℕ} (rs : Work.Kunneth.tpIdx (2 * k + 1)) :
    (∃ i : {i : Fin m // (i : ℕ) ≤ k}, tauOdd m k i = rs) ↔ Even rs.1.2 ∧ rs.1.2 < 2 * m := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), by simp only [tauOdd]; omega⟩, by have := i.2; simp only [tauOdd]; omega⟩
  · rintro ⟨⟨i, hi⟩, hlt⟩
    have hilt : i < m := by omega
    have hile : i ≤ k := by have := rs.2; omega
    refine ⟨⟨⟨i, hilt⟩, hile⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show 2 * k + 1 - 2 * i = rs.1.1
      have := rs.2
      omega
    · show 2 * i = rs.1.2
      omega

theorem thetaOdd_bijective (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (hvan : ∀ q : ℕ, ¬ (Even q ∧ q < 2 * m) → Subsingleton (Coh ℤ q (Qb m)))
    (hgen : ∀ i : ℕ, i < m → ∃ f : Coh ℤ (2 * i) (Qb m) ≃ₗ[ℤ] ℤ,
      f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) i) = 1) :
    Function.Bijective (thetaOdd m B k) := by
  classical
  let f : (i : {i : Fin m // (i : ℕ) ≤ k}) → (Coh ℤ (2 * (i : ℕ)) (Qb m) ≃ₗ[ℤ] ℤ) :=
    fun i => Classical.choose (hgen (i : ℕ) i.1.2)
  have hf : ∀ i, f i (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = 1 :=
    fun i => Classical.choose_spec (hgen (i : ℕ) i.1.2)
  let comp : (i : {i : Fin m // (i : ℕ) ≤ k}) →
      (Work.Kunneth.cohomSummand (ssB B) (ssB (Qb m)) (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
        ≃ₗ[ℤ] Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :=
    fun i => (TensorProduct.congr (LinearEquiv.refl ℤ ↥((Work.Cohomology.cochainC ℤ (ssB B)).homology
      (2 * k + 1 - 2 * (i : ℕ)))) (f i)).trans (TensorProduct.rid ℤ _)
  have hcomp_tmul : ∀ (i : {i : Fin m // (i : ℕ) ≤ k})
      (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B),
      comp i (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = x :=
    fun i x => tensorCongr_rid_tmul (M := Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B)
      (H := Coh ℤ (2 * (i : ℕ)) (Qb m)) (f i) _ (hf i) x
  have hcomp_symm : ∀ (i : {i : Fin m // (i : ℕ) ≤ k})
      (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B),
      (comp i).symm x = x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
        (Work.LerayHirsch.trivCore m) (i : ℕ) :=
    fun i x => tensorCongr_rid_symm_tmul (M := Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B)
      (H := Coh ℤ (2 * (i : ℕ)) (Qb m)) (f i) _ (hf i) x
  let Λ : ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k + 1)) →
      ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :=
    fun y i => comp i (y (tauOdd m k i))
  have h1 : ∀ xf, Λ (thetaOdd m B k xf) = xf := by
    intro xf
    funext i
    show comp i ((thetaOdd m B k xf) (tauOdd m k i)) = xf i
    rw [thetaOdd_tau]
    exact hcomp_tmul i (xf i)
  have h2 : ∀ y, thetaOdd m B k (Λ y) = y := by
    intro y
    funext rs
    by_cases hrs : ∃ i : {i : Fin m // (i : ℕ) ≤ k}, tauOdd m k i = rs
    · obtain ⟨i, rfl⟩ := hrs
      rw [thetaOdd_tau]
      show comp i (y (tauOdd m k i)) ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
        (Work.LerayHirsch.trivCore m) (i : ℕ) = y (tauOdd m k i)
      rw [← hcomp_symm i (comp i (y (tauOdd m k i)))]
      exact LinearEquiv.symm_apply_apply (comp i) _
    · have hnot : ¬ (Even rs.1.2 ∧ rs.1.2 < 2 * m) := fun h => hrs ((mem_range_tauOdd rs).mpr h)
      have hzero : (thetaOdd m B k (Λ y)) rs = 0 := by
        rw [thetaOdd, Finset.sum_apply]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        exact thetaTermOdd_ne m B k i rs (fun h => hrs ⟨i, h.symm⟩) (Λ y i)
      rw [hzero]
      have hsub : Subsingleton (Coh ℤ rs.1.2 (Qb m)) := hvan rs.1.2 hnot
      have hzero2 : ∀ a : Work.Kunneth.cohomSummand (ssB B) (ssB (Qb m)) rs.1.1 rs.1.2,
          a = 0 := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rfl
        | tmul m n => rw [@Subsingleton.elim _ hsub n 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact (hzero2 (y rs)).symm
  exact ⟨fun x y hxy => by
      have h := congrArg Λ hxy
      rwa [h1 x, h1 y] at h,
    fun y => ⟨Λ y, h2 y⟩⟩

end

end Work.Kunneth.Asm
