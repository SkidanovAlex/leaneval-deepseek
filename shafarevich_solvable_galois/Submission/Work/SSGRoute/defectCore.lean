import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The defect `1`-cocycle of the `p = 2` graded step

For `x` in the free `G`-operator group `F(n) = FreeGroup (Fin n × G)` and an involution `δ ∈ G`
acting on the basis by `(i, g) ↦ (i, δ * g)`, the **defect** is `defect δ x = (δ • x) * x`: the
deviation of `x` from being anti-fixed under the induced involution.

For `x ∈ F(n)^{(j,1)}` with `(δ • x) * x ∈ F(n)^{(j+1,1)}` (i.e. `x` anti-fixed modulo
`F(n)^{(j+1,1)}`) the class of the defect in `F(n)^{(j+1,1)}/F(n)^{(j+2,1)}` is `δ`-fixed
(`defect_smul`) and independent of the choice of representative modulo the `(1+δ)`-images
(`defect_mul_mem`).  On the "doubles" `A * (δ • A)` the defect is the *coboundary*
`(1 + δ)(A * A)` modulo `F(n)^{(j+2,1)}` (`defect_double_mul_defect_sq_mem`), so that multiplying
by the explicit element `A * A ∈ F(n)^{(j+1,1)}` kills the first obstruction
(`defect_double_mul_sq_mem`).  This is the concrete form of the vanishing of the obstruction class
in `H¹(⟨δ⟩, F(n)^{(j+1,1)}/F(n)^{(j+2,1)})`; it is the base case of the "half of the monomial"
witness construction of the `p = 2` graded step.
-/

open scoped commutatorElement

namespace Work.SSGRoute

open Work.CohomologicalShrinking

section Defect

variable {G : Type*} [Group G] {n : ℕ}

/-- **The defect** `(δ • x) * x` of an element of the free operator group: its deviation from being
anti-fixed under the involution induced by `δ`.  For `x ∈ F(n)^{(j,1)}` it measures the obstruction
class in `H¹(⟨δ⟩, F(n)^{(j,1)}/F(n)^{(j+1,1)})`. -/
noncomputable def defect (δ : G) (x : Work.Shrinking.freeOperatorGroup G n) :
    Work.Shrinking.freeOperatorGroup G n := (δ • x) * x

/-- The action of `G` written as a monoid homomorphism (it is the action by definition). -/
theorem freeOperatorActionHom_apply (δ : G) (y : Work.Shrinking.freeOperatorGroup G n) :
    Work.Shrinking.freeOperatorActionHom (G := G) n δ y = δ • y := rfl

/-- The `p`-central terms are preserved by the action of `G`. -/
theorem smul_mem_pSeries (δ : G) (hδ : δ * δ = 1) {j : ℕ}
    {x : Work.Shrinking.freeOperatorGroup G n}
    (hx : x ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j) :
    δ • x ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  have hmap := Work.Shrinking.map_pCentralSeries_surjective
    (P := Work.Shrinking.freeOperatorGroup G n) (Q := Work.Shrinking.freeOperatorGroup G n) 2
    (Work.Shrinking.freeOperatorActionHom (G := G) n δ).toMonoidHom
    (Work.Shrinking.freeOperatorActionHom (G := G) n δ).surjective (j - 1)
  have h1 : δ • x ∈ (Work.Shrinking.pCentralSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (j - 1)).map
      (Work.Shrinking.freeOperatorActionHom (G := G) n δ).toMonoidHom :=
    ⟨x, hx, rfl⟩
  rw [hmap] at h1
  exact h1

/-- The square of an element of `F(n)^{(j,1)}` lies in `F(n)^{(j+1,1)}`. -/
theorem sq_mem_pSeries_succ (A : Work.Shrinking.freeOperatorGroup G n) {j : ℕ}
    (hA : A ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j) :
    A * A ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp
  · have h1 : A ^ 2 ∈ Work.Shrinking.powSubgroup 2
        (Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j - 1)) :=
      Subgroup.subset_closure ⟨A, hA, rfl⟩
    have h2 : Work.Shrinking.powSubgroup 2
        (Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j - 1))
        ≤ Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
      rw [show j = (j - 1) + 1 from by omega, Work.Shrinking.pCentralSeries_succ]
      exact le_sup_left
    change A * A ∈ Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j
    simpa [pow_two] using h2 h1

/-- A square of an element of `F(n)^{(j+1,1)}` lies in `F(n)^{(j+2,1)}`. -/
theorem sq_mem_pSeries_succ' {j : ℕ} {v : Work.Shrinking.freeOperatorGroup G n}
    (hv : v ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)) :
    v * v ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) :=
  sq_mem_pSeries_succ v hv

/-- Conjugation preserves the `p`-central terms from level `j + 2` on. -/
theorem conj_mem_pSeries (j : ℕ) {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2))
    (g : Work.Shrinking.freeOperatorGroup G n) :
    g * z * g⁻¹ ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
  have hmem : ⁅z⁻¹, g⁆ ∈ ⁅pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2), ⊤⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hz) (Subgroup.mem_top g)
  have h1 := (commutator_pSeries_le 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2)) hmem
  have h2 : pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 3)
      ≤ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) :=
    pSeries_antitone 2 _ (by omega)
  have h3 : z * ⁅z⁻¹, g⁆ ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) :=
    (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2)).mul_mem hz (h2 h1)
  rwa [show g * z * g⁻¹ = z * ⁅z⁻¹, g⁆ from by rw [commutatorElement_def]; group]

/-- The action of `δ` on the defect is the defect times the commutator `⁅x, δ • x⁆`. -/
theorem defect_smul (δ : G) (hδ : δ * δ = 1)
    (x : Work.Shrinking.freeOperatorGroup G n) :
    δ • defect δ x = ⁅x, δ • x⁆ * defect δ x := by
  have h : δ • (δ • x) = x := by rw [← mul_smul, hδ, one_smul]
  have hm : δ • defect δ x = (δ • (δ • x)) * (δ • x) := by
    rw [defect]
    exact map_mul (Work.Shrinking.freeOperatorActionHom (G := G) n δ) (δ • x) x
  rw [hm, h, defect, commutatorElement_def]
  group

/-- **The defect of a "double" is the coboundary `(1 + δ)(A * A)`.**  For `A ∈ F(n)^{(j,1)}` the
defect of `A * (δ • A)` differs from `defect (A * A) = (δ • (A * A)) * (A * A)` by an element of
`F(n)^{(j+2,1)}`.  Hence on the doubles the obstruction class in
`H¹(⟨δ⟩, F(n)^{(j+1,1)}/F(n)^{(j+2,1)})` is a coboundary, with correcting element `A * A`. -/
theorem defect_double_mul_defect_sq_mem (δ : G) (hδ : δ * δ = 1) {j : ℕ}
    (A : Work.Shrinking.freeOperatorGroup G n)
    (hA : A ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j) :
    defect δ (A * (δ • A)) * (defect δ (A * A))⁻¹
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
  have h2 := sq_mem_pSeries_succ A hA
  have hcomm : ⁅A * A, δ • A⁆
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) :=
    (commutator_pSeries_le 2 _ (j + 1))
      (Subgroup.commutator_mem_commutator h2 (Subgroup.mem_top _))
  have h1 : δ • (δ • A) = A := by rw [← mul_smul, hδ, one_smul]
  have hm : δ • (A * (δ • A)) = (δ • A) * A := by
    have h := map_mul (Work.Shrinking.freeOperatorActionHom (G := G) n δ) A (δ • A)
    simp only [freeOperatorActionHom_apply] at h
    rw [h, h1]
  have hm2 : δ • (A * A) = (δ • A) * (δ • A) := by
    have h := map_mul (Work.Shrinking.freeOperatorActionHom (G := G) n δ) A A
    simpa only [freeOperatorActionHom_apply] using h
  have hkey : defect δ (A * (δ • A)) * (defect δ (A * A))⁻¹
      = (δ • A) * ⁅A * A, δ • A⁆ * (δ • A)⁻¹ := by
    simp only [defect, hm, hm2, commutatorElement_def]
    group
  rw [hkey]
  exact conj_mem_pSeries j (by simpa using hcomm) (δ • A)

/-- **Multiplicativity of the defect modulo `F(n)^{(j+2,1)}`.**  For any `x` and any
`u ∈ F(n)^{(j+1,1)}` the defect of the product is the product of the defects modulo
`F(n)^{(j+2,1)}`. -/
theorem defect_mul_mem (δ : G) (hδ : δ * δ = 1) {j : ℕ}
    {u : Work.Shrinking.freeOperatorGroup G n}
    (hu : u ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1))
    (x : Work.Shrinking.freeOperatorGroup G n) :
    defect δ (x * u) * (defect δ x * defect δ u)⁻¹
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
  have hdu : defect δ u ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) :=
    (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)).mul_mem
      (smul_mem_pSeries δ hδ hu) hu
  have hbu : (defect δ u) * u⁻¹ ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) :=
    (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)).mul_mem hdu
      (Subgroup.inv_mem _ hu)
  have hmem : ⁅x⁻¹, (defect δ u) * u⁻¹⁆
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
    have h1 : ⁅x⁻¹, (defect δ u) * u⁻¹⁆ ∈
        ⁅⊤, pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hbu
    rw [Subgroup.commutator_comm] at h1
    exact (commutator_pSeries_le 2 _ (j + 1)) h1
  have hkey : defect δ (x * u) * (defect δ x * defect δ u)⁻¹
      = defect δ x * ⁅x⁻¹, (defect δ u) * u⁻¹⁆ * (defect δ x)⁻¹ := by
    have hm : δ • (x * u) = (δ • x) * (δ • u) := by
      have h := map_mul (Work.Shrinking.freeOperatorActionHom (G := G) n δ) x u
      simpa only [freeOperatorActionHom_apply] using h
    simp only [defect, hm, commutatorElement_def]
    group
  rw [hkey]
  exact conj_mem_pSeries j hmem (defect δ x)

/-- **The first correction for a double.**  Multiplying `A * (δ • A)` by the explicit element
`A * A ∈ F(n)^{(j+1,1)}` kills the first obstruction: the defect of
`A * (δ • A) * (A * A)` lies in `F(n)^{(j+2,1)}`. -/
theorem defect_double_mul_sq_mem (δ : G) (hδ : δ * δ = 1) {j : ℕ}
    (A : Work.Shrinking.freeOperatorGroup G n)
    (hA : A ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) j) :
    defect δ (A * (δ • A) * (A * A))
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
  have h2 := sq_mem_pSeries_succ A hA
  have hdu : defect δ (A * A) ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) :=
    (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)).mul_mem
      (smul_mem_pSeries δ hδ h2) h2
  have hdouble := defect_double_mul_defect_sq_mem δ hδ A hA
  -- the product of the two defects is again in `P_{j+2}`
  have hsq : defect δ (A * A) * defect δ (A * A)
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
    exact sq_mem_pSeries_succ (defect δ (A * A)) hdu
  have hx2 : defect δ (A * (δ • A)) * defect δ (A * A)
      ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) := by
    have h1 : defect δ (A * (δ • A)) * (defect δ (A * A))⁻¹
        * (defect δ (A * A) * defect δ (A * A))
        ∈ pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2) :=
      (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2)).mul_mem hdouble hsq
    rwa [show defect δ (A * (δ • A)) * (defect δ (A * A))⁻¹
        * (defect δ (A * A) * defect δ (A * A))
        = defect δ (A * (δ • A)) * defect δ (A * A) from by group] at h1
  have hmul := defect_mul_mem δ hδ h2 (A * (δ • A))
  have h := (pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 2)).mul_mem hmul hx2
  rwa [show defect δ (A * (δ • A) * (A * A)) * (defect δ (A * (δ • A))
        * defect δ (A * A))⁻¹ * (defect δ (A * (δ • A)) * defect δ (A * A))
      = defect δ (A * (δ • A) * (A * A)) from by group] at h

end Defect

end Work.SSGRoute
