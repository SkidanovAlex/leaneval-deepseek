import Mathlib
import Submission.Work.Kunneth.Assembly.Defs

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
# The "collapse" map `theta` is bijective (even degrees)

`Work.Kunneth.Asm.theta m B k` is the family map
`(x_i)_{i<m, i≤k} ↦ Σ_i kSingle_{τ i} (x_i ⊗ ζ^i)` into the Künneth target, at the bidegrees
`τ i = (2(k-i), 2i)`.

Assuming that `H^q(ℂP^{m-1})` vanishes for `q` odd or `q ≥ 2m` (`hvan`) and that `ζ^i` is a
`ℤ`-basis of `H^{2i}(ℂP^{m-1})` for `i < m` (`hgen`), the map `theta` is a bijection: its inverse is
the extension to all elements of the target of the "extract the `i`-th coefficient"
`y ↦ φ_i (y ⟨τ i⟩)`, where `φ_i : H^{2(k-i)}(B) ⊗ H^{2i}(ℂP^{m-1}) ≅ H^{2(k-i)}(B)` is the inverse
of `x ↦ x ⊗ ζ^i`.
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The bidegree of the `i`-th summand of `Work.Kunneth.Asm.theta`: `(2(k-i), 2i)`. -/
def tau (m : ℕ) (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) : Work.Kunneth.tpIdx (2 * k) :=
  ⟨(2 * (k - (i : ℕ)), 2 * (i : ℕ)), by have := i.2; omega⟩

theorem tau_injective (m k : ℕ) : Function.Injective (tau m k) := by
  intro i j hij
  have h1 : 2 * (k - (i : ℕ)) = 2 * (k - (j : ℕ)) := congrArg (fun pq => pq.1.1) hij
  have h2 : (i : ℕ) = (j : ℕ) := by omega
  exact Subtype.ext (Fin.ext h2)

/-- The component isomorphism `H^{2(k-i)}(B) ⊗ H^{2i}(ℂP^{m-1}) ≅ H^{2(k-i)}(B)`: the inverse of
`x ↦ x ⊗ ζ^i`, given a linear equivalence `H^{2i}(ℂP^{m-1}) ≅ ℤ` sending `ζ^i` to `1`. -/
noncomputable def thetaComp (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (f : Coh ℤ (2 * (i : ℕ)) (Qb m) ≃ₗ[ℤ] ℤ)
    (hf : f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = 1) :
    Work.Kunneth.cohomSummand (ssB B) (ssB (Qb m)) (2 * (k - (i : ℕ))) (2 * (i : ℕ))
      ≃ₗ[ℤ] Coh ℤ (2 * (k - (i : ℕ))) B :=
  (TensorProduct.congr
      (LinearEquiv.refl ℤ ↥((Work.Cohomology.cochainC ℤ (ssB B)).homology (2 * (k - (i : ℕ)))))
      f).trans (TensorProduct.rid ℤ _)

theorem tensorCongr_rid_tmul {M H : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup H]
    [Module ℤ H] (f : H ≃ₗ[ℤ] ℤ) (ζ : H) (hf : f ζ = 1) (x : M) :
    ((TensorProduct.congr (LinearEquiv.refl ℤ M) f).trans (TensorProduct.rid ℤ M))
        (x ⊗ₜ[ℤ] ζ) = x := by
  rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, hf]
  simp

theorem thetaComp_tmul (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (f : Coh ℤ (2 * (i : ℕ)) (Qb m) ≃ₗ[ℤ] ℤ)
    (hf : f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = 1)
    (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    thetaComp m B k i f hf
        (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = x :=
  tensorCongr_rid_tmul (M := Coh ℤ (2 * (k - (i : ℕ))) B)
    (H := Coh ℤ (2 * (i : ℕ)) (Qb m)) f _ hf x

/-- The inverse of `thetaComp`: `x ↦ x ⊗ ζ`. -/
theorem tensorCongr_rid_symm_tmul {M H : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup H]
    [Module ℤ H] (f : H ≃ₗ[ℤ] ℤ) (ζ : H) (hf : f ζ = 1) (x : M) :
    ((TensorProduct.congr (LinearEquiv.refl ℤ M) f).trans (TensorProduct.rid ℤ M)).symm x
      = x ⊗ₜ[ℤ] ζ := by
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply,
    TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    show f.symm 1 = ζ from (f.symm_apply_eq).mpr hf.symm]

theorem thetaComp_symm_tmul (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (f : Coh ℤ (2 * (i : ℕ)) (Qb m) ≃ₗ[ℤ] ℤ)
    (hf : f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = 1)
    (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    (thetaComp m B k i f hf).symm x
      = x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ) :=
  tensorCongr_rid_symm_tmul (M := Coh ℤ (2 * (k - (i : ℕ))) B)
    (H := Coh ℤ (2 * (i : ℕ)) (Qb m)) f _ hf x

/-- The value of the `i`-th summand of `theta` at its own bidegree `τ i`. -/
theorem thetaTerm_tau (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    (thetaTerm m B k i x) (tau m k i) = x ⊗ₜ[ℤ]
      Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ) := by
  rw [thetaTerm]
  show kSingle (ssB B) (ssB (Qb m)) (2 * k) (tau m k i)
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) (tau m k i) = _
  exact kSingle_self _ _ _ _ _

/-- The value of the `j`-th summand of `theta` at a different bidegree vanishes. -/
theorem thetaTerm_ne (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (j : {i : Fin m // (i : ℕ) ≤ k}) (rs : Work.Kunneth.tpIdx (2 * k))
    (h : rs ≠ tau m k j) (x : Coh ℤ (2 * (k - (j : ℕ))) B) :
    (thetaTerm m B k j x) rs = 0 := by
  rw [thetaTerm]
  show kSingle (ssB B) (ssB (Qb m)) (2 * k) (tau m k j)
    (x ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (j : ℕ)) rs = _
  exact kSingle_of_ne _ _ _ h _

/-- The value of `theta` at the index `τ i`: the `i`-th block of `theta xf` is `xf i ⊗ ζ^i`. -/
theorem theta_tau (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B)
    (i : {i : Fin m // (i : ℕ) ≤ k}) :
    (theta m B k xf) (tau m k i)
      = xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ) := by
  rw [theta, Finset.sum_apply]
  have h : ∀ j : {i : Fin m // (i : ℕ) ≤ k},
      (thetaTerm m B k j (xf j)) (tau m k i)
        = if j = i then xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
            (Work.LerayHirsch.trivCore m) (i : ℕ) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [thetaTerm_tau, if_pos rfl]
    · rw [thetaTerm_ne m B k j (tau m k i) (fun hh => hj (tau_injective m k hh.symm)) (xf j),
        if_neg hj]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]

/-- An index of `tpIdx (2k)` is of the form `τ i` exactly when its second coordinate is even and
`< 2m`. -/
theorem mem_range_tau {m k : ℕ} (rs : Work.Kunneth.tpIdx (2 * k)) :
    (∃ i : {i : Fin m // (i : ℕ) ≤ k}, tau m k i = rs) ↔ Even rs.1.2 ∧ rs.1.2 < 2 * m := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), by simp only [tau]; omega⟩, by have := i.2; simp only [tau]; omega⟩
  · rintro ⟨⟨i, hi⟩, hlt⟩
    have hilt : i < m := by omega
    have hile : i ≤ k := by have := rs.2; omega
    refine ⟨⟨⟨i, hilt⟩, hile⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show 2 * (k - i) = rs.1.1
      have := rs.2
      omega
    · show 2 * i = rs.1.2
      omega

theorem theta_bijective (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (hvan : ∀ q : ℕ, ¬ (Even q ∧ q < 2 * m) →
      Subsingleton (Coh ℤ q (Qb m)))
    (hgen : ∀ i : ℕ, i < m → ∃ f : Coh ℤ (2 * i) (Qb m) ≃ₗ[ℤ] ℤ,
      f (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) i) = 1) :
    Function.Bijective (theta m B k) := by
  classical
  let f : (i : {i : Fin m // (i : ℕ) ≤ k}) → (Coh ℤ (2 * (i : ℕ)) (Qb m) ≃ₗ[ℤ] ℤ) :=
    fun i => Classical.choose (hgen (i : ℕ) i.1.2)
  have hf : ∀ i, f i (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)) = 1 :=
    fun i => Classical.choose_spec (hgen (i : ℕ) i.1.2)
  let Λ : ↥(Work.Kunneth.kunnethTarget (ssB B) (ssB (Qb m)) (2 * k)) →
      ((i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :=
    fun y i => thetaComp m B k i (f i) (hf i) (y (tau m k i))
  have h1 : ∀ xf, Λ (theta m B k xf) = xf := by
    intro xf
    funext i
    show thetaComp m B k i (f i) (hf i) ((theta m B k xf) (tau m k i)) = xf i
    rw [theta_tau]
    exact thetaComp_tmul m B k i (f i) (hf i) (xf i)
  have h2 : ∀ y, theta m B k (Λ y) = y := by
    intro y
    funext rs
    by_cases hrs : ∃ i : {i : Fin m // (i : ℕ) ≤ k}, tau m k i = rs
    · obtain ⟨i, rfl⟩ := hrs
      rw [theta_tau]
      show thetaComp m B k i (f i) (hf i) (y (tau m k i))
          ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore m) (i : ℕ)
        = y (tau m k i)
      rw [← thetaComp_symm_tmul m B k i (f i) (hf i)
        (thetaComp m B k i (f i) (hf i) (y (tau m k i)))]
      exact LinearEquiv.symm_apply_apply (thetaComp m B k i (f i) (hf i)) _
    · have hnot : ¬ (Even rs.1.2 ∧ rs.1.2 < 2 * m) := fun h => hrs ((mem_range_tau rs).mpr h)
      have hzero : (theta m B k (Λ y)) rs = 0 := by
        rw [theta, Finset.sum_apply]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        exact thetaTerm_ne m B k i rs (fun h => hrs ⟨i, h.symm⟩) (Λ y i)
      rw [hzero]
      have hsub : Subsingleton (Coh ℤ rs.1.2 (Qb m)) := hvan rs.1.2 hnot
      have hzero2 : ∀ a : Work.Kunneth.cohomSummand (ssB B) (ssB (Qb m)) rs.1.1 rs.1.2, a = 0 := by
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
