import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.LhCalc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The restriction of a Leray–Hirsch combination to a fibre

Helper lemmas and the target `Work.Gen.CohMap_fibreIncl_lhMap`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- **The pullback along a constant map of a positive-degree class vanishes.**  A constant map
`X → B` factors through the one-point space `PUnit`, whose positive-degree singular cohomology
vanishes (`Work.Cohomology.punit`). -/
theorem CohMap_const_eq_zero {X : Type} [TopologicalSpace X] (b : B)
    {d : ℕ} (hd : 1 ≤ d) (z : Coh ℤ d B) :
    (ModuleCat.Hom.hom (Work.Thom.CohMap (ContinuousMap.const X b) ℤ d)) z = 0 := by
  haveI hsub : Subsingleton (Coh ℤ d PUnit) := by
    have hz : CategoryTheory.Limits.IsZero (Coh ℤ d PUnit) := by
      rw [show d = (d - 1) + 1 from by omega]
      exact Work.Cohomology.punit ℤ (d - 1)
    exact ModuleCat.isZero_iff_subsingleton.mp hz
  have hcomp : (ContinuousMap.const PUnit b : C(PUnit, B)).comp
      (ContinuousMap.const X PUnit.unit) = ContinuousMap.const X b :=
    ContinuousMap.ext (fun _ => rfl)
  rw [← hcomp, ← Work.Thom.CohMap_comp_apply (ContinuousMap.const X PUnit.unit)
    (ContinuousMap.const PUnit b) ℤ d z]
  rw [Subsingleton.elim
    ((ModuleCat.Hom.hom (Work.Thom.CohMap (ContinuousMap.const PUnit b) ℤ d)) z) 0]
  exact map_zero _

/-- **The pullback along the constant map to a fibre of a positive-degree class vanishes.** -/
theorem CohMap_constFibre_eq_zero {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    {d : ℕ} (hd : 1 ≤ d) (z : Coh ℤ d B) :
    (ModuleCat.Hom.hom (Work.Thom.CohMap (constFibre Z b) ℤ d)) z = 0 := by
  have hconst : constFibre Z b
      = ContinuousMap.const (Work.LerayHirsch.ProjFibre Z b) b := rfl
  rw [hconst]
  exact CohMap_const_eq_zero (X := Work.LerayHirsch.ProjFibre Z b) b hd z

/-- **The pullback of a summand of the Leray–Hirsch decomposition to a fibre.** -/
theorem lhTerm_comap_fibreIncl {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B)
    (h : 2 * ((k - (i : ℕ)) + (i : ℕ)) = 2 * k) :
    (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * k)))
        (cohTransport h (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap Z)
            ℤ (2 * (k - (i : ℕ))))) x)
          (Work.LerayHirsch.zetaPow Z (i : ℕ))))
      = cohTransport h (Work.Whitney.cupChern (k - (i : ℕ)) (i : ℕ)
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (constFibre Z b) ℤ (2 * (k - (i : ℕ))))) x)
          ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b)
            ℤ (2 * (i : ℕ)))) (Work.LerayHirsch.zetaPow Z (i : ℕ)))) := by
  rw [Work.Whitney.cohTransport_CohMap, Work.Whitney.cupChern_CohMap]
  have hmap : (Work.LerayHirsch.projMap Z).comp (Work.LerayHirsch.fibreIncl Z b)
      = constFibre Z b :=
    ContinuousMap.ext (fun y => Work.LerayHirsch.projMap_fibreIncl Z b y)
  have h1 : (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b)
        ℤ (2 * (k - (i : ℕ)))))
      ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * (k - (i : ℕ))))) x)
      = (ModuleCat.Hom.hom (Work.Thom.CohMap (constFibre Z b) ℤ (2 * (k - (i : ℕ))))) x := by
    rw [Work.Thom.CohMap_comp_apply (Work.LerayHirsch.fibreIncl Z b)
      (Work.LerayHirsch.projMap Z) ℤ (2 * (k - (i : ℕ))) x, hmap]
  rw [h1]

end

noncomputable section

open Work.TangentClasses Work.Thom in
/-- **The restriction of a Leray–Hirsch combination to a fibre.**  Let `ψ = Σ_j π^*(ψ_j) ζ^j` be
the Leray–Hirsch expansion of a class of `H^{2(n-1)}(P(Z))`, `Z` of rank `n+1`.  Restricted to the
fibre of `π : P(Z) → B` over `b`, only the top summand `j = n-1` (whose coefficient has degree `0`)
survives; its coefficient is pulled back along the constant map `constFibre Z b` and its `ζ^{n-1}` is
the fibre's hyperplane class, which is the pullback of `ζ^{n-1}(P(ε^{n+1}))` along the canonical
identification `fibreIdent Z b = projUniv ∘ projClassFibre` of the fibre with `P(ε^{n+1})`
(`Work.LerayHirsch.CohMap_fibreIncl_zetaPow`). -/
theorem CohMap_fibreIncl_lhMap {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (hn : 1 ≤ n) (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (ψf : (j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) → Work.Thom.Coh ℤ (2 * ((n - 1) - (j : ℕ))) B)
    (b : B) :
    (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * (n - 1))))
        (Work.LerayHirsch.lhMap Z (n - 1) ψf)
      = Work.Thom.cohTransport (by omega : 2 * (0 + (n - 1)) = 2 * (n - 1))
          (Work.Whitney.cupChern 0 (n - 1)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.constFibre Z b) ℤ 0))
              (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
                (ψf Work.Gen.topCoeffIdx)))
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.fibreIdent Z b) ℤ (2 * (n - 1))))
              (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (n - 1)))) := by
  classical
  let F : Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjSpace Z) →ₗ[ℤ]
      Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjFibre Z b) :=
    ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * (n - 1)))
  let T : ({j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) →
      Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjFibre Z b) :=
    fun j => Work.Thom.cohTransport
      (by omega : 2 * (((n - 1) - (j : ℕ)) + (j : ℕ)) = 2 * (n - 1))
      (Work.Whitney.cupChern ((n - 1) - (j : ℕ)) (j : ℕ)
        ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.constFibre Z b)
          ℤ (2 * ((n - 1) - (j : ℕ))))) (ψf j))
        ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * (j : ℕ))))
          (Work.LerayHirsch.zetaPow Z (j : ℕ))))
  have hstep1 : (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b)
        ℤ (2 * (n - 1))))
        (Work.LerayHirsch.lhMap Z (n - 1) ψf)
      = ∑ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1},
          F (Work.LerayHirsch.lhTerm Z (n - 1) j (ψf j)) := by
    rw [Work.LerayHirsch.lhMap_apply, map_sum]
  have hterm : ∀ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1},
      F (Work.LerayHirsch.lhTerm Z (n - 1) j (ψf j)) = T j := by
    intro j
    dsimp only [F, T]
    rw [Work.LerayHirsch.lhTerm_def]
    exact lhTerm_comap_fibreIncl Z b (n - 1) j (ψf j) _
  have hzero : ∀ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1},
      j ≠ Work.Gen.topCoeffIdx (n := n) → T j = 0 := by
    intro j hj
    have hval : (j : ℕ) ≠ n - 1 := by
      intro h
      refine hj (Subtype.ext (Fin.ext ?_))
      simpa [Work.Gen.topCoeffIdx_val] using h
    have hpos : 1 ≤ 2 * ((n - 1) - (j : ℕ)) := by
      have h1 : 1 ≤ (n - 1) - (j : ℕ) := by omega
      omega
    dsimp only [T]
    rw [CohMap_constFibre_eq_zero Z b hpos (ψf j), Work.LerayHirsch.cupChern_zero_left,
      Work.Thom.cohTransport_zero]
  have hsingle : ∀ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1},
      T j = if j = Work.Gen.topCoeffIdx (n := n) then T Work.Gen.topCoeffIdx else 0 := by
    intro j
    by_cases hj : j = Work.Gen.topCoeffIdx (n := n)
    · rw [if_pos hj, hj]
    · rw [if_neg hj, hzero j hj]
  have htop_eq : T (Work.Gen.topCoeffIdx (n := n))
      = Work.Thom.cohTransport (by omega : 2 * (0 + (n - 1)) = 2 * (n - 1))
          (Work.Whitney.cupChern 0 (n - 1)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.constFibre Z b) ℤ 0))
              (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
                (ψf Work.Gen.topCoeffIdx)))
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.fibreIdent Z b) ℤ (2 * (n - 1))))
              (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (n - 1)))) := by
    have hz : (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.fibreIdent Z b) ℤ (2 * (n - 1))))
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (n - 1))
        = (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b)
            ℤ (2 * (n - 1)))) (Work.LerayHirsch.zetaPow Z (n - 1)) := by
      rw [Work.Gen.fibreIdent, ← Work.LerayHirsch.CohMap_fibreIncl_zetaPow Z b (n - 1)]
    dsimp only [T]
    rw [Work.Whitney.cohTransport_CohMap (Work.Gen.topCoeffIdx_degree (n := n))
      (Work.Gen.constFibre Z b) (ψf Work.Gen.topCoeffIdx)]
    rw [Work.Gen.cupChern_cast_left (h := Work.Gen.topCoeffIdx_degree (n := n))]
    rw [hz]
    rw [Work.Whitney.cohTransport_trans]
  calc (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl Z b) ℤ (2 * (n - 1))))
        (Work.LerayHirsch.lhMap Z (n - 1) ψf)
      = ∑ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1},
          F (Work.LerayHirsch.lhTerm Z (n - 1) j (ψf j)) := hstep1
    _ = ∑ j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}, T j :=
          Finset.sum_congr rfl (fun j _ => hterm j)
    _ = T (Work.Gen.topCoeffIdx (n := n)) := by
          rw [Finset.sum_congr rfl (fun j _ => hsingle j), Finset.sum_ite_eq',
            if_pos (Finset.mem_univ _)]
    _ = Work.Thom.cohTransport (by omega : 2 * (0 + (n - 1)) = 2 * (n - 1))
          (Work.Whitney.cupChern 0 (n - 1)
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.constFibre Z b) ℤ 0))
              (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
                (ψf Work.Gen.topCoeffIdx)))
            ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.Gen.fibreIdent Z b) ℤ (2 * (n - 1))))
              (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (n - 1)))) :=
          htop_eq

end

end Work.Gen
