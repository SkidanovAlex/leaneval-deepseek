import Mathlib
import Submission.Work.Cohomology.sphereHomologyTop

/-!
# Vanishing of the singular homology of spheres off the top degree

This file proves `H_k(Sⁿ; ℤ) = 0` for `k ≠ 0, n` (`n ≥ 1`), the "non-top" companion of
`Work.Cohomology.sphereHomologyTop` (`Hₙ(Sⁿ) ≅ ℤ`).  The proof is the same Mayer–Vietoris
induction: the sphere `S^(m+1)` is covered by the two contractible caps `capA m`, `capB m`, whose
intersection `band m` is homotopy equivalent to `Sᵐ`.  Hence

`H_k(S^(m+1)) ≅ H_(k-1)(band m) ≅ H_(k-1)(Sᵐ)`  for `k ≥ 2`,

which lowers both `m` and `k`; the base cases are `k = 1` (`H₁` of a cover by contractible sets
with connected intersection) and `m = 0` (`S⁰` is a finite discrete, hence totally disconnected,
space).  The final statement `sphereVanishing` is phrased for the standard sphere
`Metric.sphere (0 : ℝ^(n+1)) 1`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## Auxiliary: `Sⁿ` is path connected for `n ≥ 1` -/

/-- `sphSet n ⊆ ℝ^n` is path connected for `n ≥ 2`. -/
theorem pathConnected_sphSet (n : ℕ) (hn : 2 ≤ n) : PathConnectedSpace ↥(sphSet n) := by
  have hsphere : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    refine isPathConnected_sphere ?_ 0 (by norm_num)
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin n)) = (n : Cardinal) from by
      have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv
      rw [h2]; exact rank_fin_fun n]
    norm_num; omega
  haveI : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsphere
  rw [pathConnectedSpace_iff_univ]
  exact ((Homeomorph.setCongr (sphereSet_eq n)).isPathConnected_preimage (s := Set.univ)).mp
    (isPathConnected_univ :
      IsPathConnected (Set.univ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-! ## The base case `S⁰` -/

/-- **`H_k(S⁰) = 0` for `k ≠ 0`.**  `S⁰` is a finite discrete space, hence totally disconnected,
and Mathlib computes the positive-degree singular homology of a totally disconnected space. -/
theorem sphereVanishing_zero (k : ℕ) (hk : k ≠ 0) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (sphTop 1)).homology k) := by
  haveI : DiscreteTopology ↥(sphSet 1) := discreteTopology_sphSet_one
  haveI : TotallyDisconnectedSpace ↥(sphSet 1) := inferInstance
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) k (ModuleCat.of ℤ ℤ) (sphTop 1) hk

/-! ## The main vanishing theorem for `Sⁿ ⊆ ℝ^(n+1)` -/

theorem sphereVanishing_aux (n : ℕ) : 1 ≤ n → ∀ k, k ≠ 0 → k ≠ n →
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (sphTop (n+1))).homology k) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn k hk hnk
    rcases k with _ | _ | k
    · -- `k = 0`
      exact absurd rfl hk
    · -- `k = 1`: `1 ≠ n`, so `n ≥ 2`
      have hn2 : 2 ≤ n := by omega
      haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
      haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
      obtain ⟨e1⟩ := mvδX_zero_iso (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
        (capA_union_capB n)
      have hker : LinearMap.ker (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (mvLeft (capA n) (capB n)) 0))
          = LinearMap.ker (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
              (TopCat.of ↥((capA n) ∩ (capB n))) (ModuleCat.of ℤ ℤ))) :=
        ker_mvLeft_zero_eq_ker_eps (capA n) (capB n)
      have e2 : kerMod (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (mvLeft (capA n) (capB n)) 0))
          ≅ kerMod (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
              (TopCat.of ↥((capA n) ∩ (capB n))) (ModuleCat.of ℤ ℤ))) :=
        LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hker)
      obtain ⟨e3⟩ := ker_eps_homotopyEquiv (bandHomotopyEquiv n (by omega)).some
      haveI : PathConnectedSpace ↥(sphSet n) := pathConnected_sphSet n hn2
      have hkerzero : CategoryTheory.Limits.IsZero (kerMod (ModuleCat.Hom.hom
          (TopCat.singularHomology₀ε (TopCat.of ↥(sphSet n)) (ModuleCat.of ℤ ℤ)))) := by
        haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥(sphSet n))
            (ModuleCat.of ℤ ℤ)) := inferInstance
        rw [ModuleCat.isZero_iff_subsingleton]
        show Subsingleton ↥(LinearMap.ker (ModuleCat.Hom.hom
          (TopCat.singularHomology₀ε (TopCat.of ↥(sphSet n)) (ModuleCat.of ℤ ℤ))))
        rw [LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance)]
        infer_instance
      exact IsZero.of_iso hkerzero (e1 ≪≫ e2 ≪≫ e3)
    · -- `k = k + 2 ≥ 2`
      rcases eq_or_lt_of_le hn with hn1 | hn2
      · -- `n = 1`
        subst hn1
        haveI hA : ContractibleSpace ↥(capA 1) := contractibleSpace_capA 1
        haveI hB : ContractibleSpace ↥(capB 1) := contractibleSpace_capB 1
        haveI hiso : IsIso (mvδX (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
            (capA_union_capB 1) (k+1)) :=
          mvδX_isIso (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
            (capA_union_capB 1) (k+1) (by omega)
        obtain ⟨e2⟩ := homologyIso_of_homotopyEquiv (bandHomotopyEquiv 1 le_rfl).some (k+1)
        exact IsZero.of_iso
          (IsZero.of_iso (sphereVanishing_zero (k+1) (by omega)) e2)
          (asIso (mvδX (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
            (capA_union_capB 1) (k+1)))
      · -- `n ≥ 2`
        haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
        haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
        haveI hiso : IsIso (mvδX (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
            (capA_union_capB n) (k+1)) :=
          mvδX_isIso (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
            (capA_union_capB n) (k+1) (by omega)
        obtain ⟨e2⟩ := homologyIso_of_homotopyEquiv (bandHomotopyEquiv n (by omega)).some (k+1)
        have hIH := ih (n-1) (by omega) (by omega) (k+1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hIH
        exact IsZero.of_iso (IsZero.of_iso hIH e2)
          (asIso (mvδX (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
            (capA_union_capB n) (k+1)))

/-- **`H_k(Sⁿ; ℤ) = 0` for `k ≠ 0, n`** (`n ≥ 1`), for the standard sphere
`Sⁿ = Metric.sphere (0 : ℝ^(n+1)) 1`. -/
theorem sphereVanishing (n k : ℕ) (hn : 1 ≤ n) (h0 : k ≠ 0) (hnk : k ≠ n) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology k) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq (n+1))).toHomotopyEquiv k
  exact IsZero.of_iso (sphereVanishing_aux n hn k h0 hnk) e

end

end Work.Cohomology
