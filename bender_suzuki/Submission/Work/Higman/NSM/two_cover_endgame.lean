/-
# The two-cover endgame of the `C₄` exclusion

This module proves `Work.Higman.NSM.two_cover_endgame`: in the *two-cover configuration* of
Higman's Theorem 1 (a Suzuki 2-group `P` with `A` satisfying the `C₄`-data — `A` `ξ`-invariant
abelian normal, `Ω₁(P) ≤ A`, `[P,P] = A`, all squares in `A`, `A⁴ = 1`, `A² = Ω₁(P)`,
`|A| = |Ω₁(P)|²`, `C_P(A) = A` — and two `ξ`-invariant normal subgroups `C, E > A` with
`C ⊓ E = A`, `C ⊔ E = ⊤`, `[C,C] = [E,E] = A²`, `C² = E² = A²`, `[C,A] = [E,A] = A²`) there is a
contradiction.

The mathematical content is the classical *two-cover endgame* of the `C₄` case.  The commutator
pairings `B : C/A × E/A → A/A²` and `Φ : A/A² × C/A → A²` are `ξ`-equivariant and perfect, and
the group identities `⟦⟦c,e⟧,c⟧ = ⟦c,e⟧²`, `⟦⟦c,e⟧,e⟧ = ⟦c,e⟧²`, `⟦⟦c,e⟧,c'⟧ = ⟦⟦c',e⟧,c⟧`
(valid because `c²`, `e²` lie in the central subgroup `A² = Ω₁(P)`) turn into the *diagonal* and
*Jacobi* relations for `Φ` and `B`.  Together with the Frobenius (eigenvalue) bookkeeping of the
Singer identifications of the irreducible `𝔽₂⟨ξ⟩`-modules `C/A`, `E/A`, `A/A²`, `A²` this is
impossible (the algebraic endgame is `Work.Higman.RedAux.two_cover_algebraic_core`).
-/

import Mathlib
import Submission.Work.Higman.H8.c4_resonance_false
import Submission.Work.Higman.omega1_iso_field
import Submission.Work.Higman.resonance_of_equivariant_biadditive
import Submission.Work.Higman.Q3.two_pow_add_eq_pow
import Submission.Work.Higman.Q3.crux_class_three_jacobi
import Submission.Work.Higman.RedAux.two_cover_algebraic_core
import Submission.Work.Higman.reducible_aux
import Submission.Work.Commutator.two_cover_false

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.NSM

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- If `x ^ 2` commutes with `y` then `x` conjugates the commutator `⟦x,y⟧` to its inverse;
equivalently `⟦x, ⟦x,y⟧⟧ = (⟦x,y⟧ ^ 2)⁻¹`. -/
theorem commutatorElement_diag_aux {G : Type} [Group G] (x y : G)
    (h : x ^ 2 * y = y * x ^ 2) :
    ⁅x, ⁅x, y⁆⁆ = (⁅x, y⁆ ^ 2)⁻¹ := by
  have h1 : ⁅x ^ 2, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
  have h2 := Work.Higman.commutatorElement_sq x y
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

/-- If `x ^ 2` commutes with `y` then `⟦⟦x,y⟧, x⟧ = ⟦x,y⟧ ^ 2`. -/
theorem commutatorElement_diag {G : Type} [Group G] (x y : G)
    (h : x ^ 2 * y = y * x ^ 2) :
    ⁅⁅x, y⁆, x⁆ = ⁅x, y⁆ ^ 2 := by
  have h1 := commutatorElement_diag_aux x y h
  calc ⁅⁅x, y⁆, x⁆ = ⁅x, ⁅x, y⁆⁆⁻¹ := (commutatorElement_inv x ⁅x, y⁆).symm
    _ = ((⁅x, y⁆ ^ 2)⁻¹)⁻¹ := by rw [h1]
    _ = ⁅x, y⁆ ^ 2 := inv_inv _

/-- For `t` in a normal abelian subgroup, `⟦t⁻¹, y⟧ = ⟦t, y⟧⁻¹`. -/
theorem commutatorElement_inv_left_mem {G : Type} [Group G] {A : Subgroup G}
    (hAn : A.Normal) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {t y : G} (ht : t ∈ A) : ⁅t⁻¹, y⁆ = ⁅t, y⁆⁻¹ := by
  have h := Work.Higman.commutatorElement_mul_of_abel_normal hAn hAab (A.inv_mem ht) ht
    (C := ⊤) (Subgroup.mem_top y)
  rw [inv_mul_cancel] at h
  have h1 : ⁅(1 : G), y⁆ = 1 := by rw [commutatorElement_def]; group
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **The group-theoretic facts of the two-cover configuration.** -/
theorem two_cover_group_facts (h : Work.Higman.IsSuzuki2Grp P)
    {A C E : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hEn : E.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAC : A ≤ C) (hAE : A ≤ E) (hCA : A ≠ C) (hEA : A ≠ E)
    (hCcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hEcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) (hEd : ⁅E, E⁆ = Work.Higman.powSub A 2)
    (hCpow2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hEpow2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) (hEAd : ⁅E, A⁆ = Work.Higman.powSub A 2)
    (hCE : C ⊓ E = A) (hCEsup : C ⊔ E = ⊤) :
    (∀ c ∈ C, c ^ 2 ∈ Work.Higman.powSub A 2) ∧
    (∀ e ∈ E, e ^ 2 ∈ Work.Higman.powSub A 2) ∧
    (∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ * e⁻¹ ∈ A) ∧
    (∀ c ∈ C, ∀ e ∈ E,
      (c * e * c⁻¹ * e⁻¹) * c * (c * e * c⁻¹ * e⁻¹)⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹) ^ 2) ∧
    (∀ c ∈ C, ∀ e ∈ E,
      (c * e * c⁻¹ * e⁻¹) * e * (c * e * c⁻¹ * e⁻¹)⁻¹ * e⁻¹ = (c * e * c⁻¹ * e⁻¹) ^ 2) ∧
    (∀ c ∈ C, ∀ c' ∈ C, ∀ e ∈ E,
      (c * e * c⁻¹ * e⁻¹) * c' * (c * e * c⁻¹ * e⁻¹)⁻¹ * c'⁻¹ =
        (c' * e * c'⁻¹ * e⁻¹) * c * (c' * e * c'⁻¹ * e⁻¹)⁻¹ * c⁻¹) ∧
    (∃ c ∈ C, ∃ e ∈ E, c * e * c⁻¹ * e⁻¹ ∉ Work.Higman.powSub A 2) := by
  haveI hAn : A.Normal := hA.normal
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- `A ^ (2) = Ω₁(P)` is central
  have hA2central : ∀ a ∈ Work.Higman.powSub A 2, a ∈ Subgroup.center P := by
    intro a ha
    rw [htop] at ha
    exact h.omega1_le_center ha
  -- `A ≠ A ^ (2)`
  have hAne2 : A ≠ Work.Higman.powSub A 2 := by
    intro heq
    have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.omega1 P) := by rw [heq, htop]
    have h3 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
    have h4 : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
      rw [← hcard, h1]
    nlinarith [h3, h4]
  -- every commutator `⟦c,e⟧` lies in `A = C ⊓ E`
  have hcomm_mem : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ * e⁻¹ ∈ A := by
    intro c hc e he
    rw [← hCE, Subgroup.mem_inf]
    exact ⟨by simpa only [mul_assoc] using C.mul_mem hc (hCn.conj_mem c⁻¹ (C.inv_mem hc) e),
      E.mul_mem (hEn.conj_mem e he c) (E.inv_mem he)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [← hCpow2]
    exact Work.Higman.pow_mem_powSub hc
  · intro e he
    rw [← hEpow2]
    exact Work.Higman.pow_mem_powSub he
  · intro c hc e he
    exact hcomm_mem c hc e he
  · intro c hc e he
    have hc2 : c ^ 2 ∈ Work.Higman.powSub A 2 := by
      rw [← hCpow2]; exact Work.Higman.pow_mem_powSub hc
    have hce2 : c ^ 2 * e = e * c ^ 2 :=
      (Subgroup.mem_center_iff.mp (hA2central _ hc2) e).symm
    have hd := commutatorElement_diag c e hce2
    simpa only [commutatorElement_def] using hd
  · intro c hc e he
    have he2 : e ^ 2 ∈ Work.Higman.powSub A 2 := by
      rw [← hEpow2]; exact Work.Higman.pow_mem_powSub he
    have hec2 : e ^ 2 * c = c * e ^ 2 :=
      (Subgroup.mem_center_iff.mp (hA2central _ he2) c).symm
    have htA : ⁅c, e⁆ ∈ A := by
      have := hcomm_mem c hc e he
      simpa only [commutatorElement_def] using this
    have hte : ⁅⁅c, e⁆, e⁆ = ⁅c, e⁆ ^ 2 := by
      have h1 : ⁅⁅c, e⁆⁻¹, e⁆ = (⁅c, e⁆ ^ 2)⁻¹ := by
        have h2 := commutatorElement_diag e c hec2
        rw [← commutatorElement_inv c e] at h2
        rwa [show (⁅c, e⁆⁻¹) ^ 2 = (⁅c, e⁆ ^ 2)⁻¹ by
          rw [pow_two, pow_two, mul_inv_rev]] at h2
      have h3 : (⁅⁅c, e⁆, e⁆)⁻¹ = (⁅c, e⁆ ^ 2)⁻¹ := by
        rw [← commutatorElement_inv_left_mem hAn hAab htA]
        exact h1
      exact inv_injective h3
    simpa only [commutatorElement_def] using hte
  · intro c hc c' hc' e he
    have ht1 : ⁅c, e⁆ ∈ A := by
      have := hcomm_mem c hc e he; simpa only [commutatorElement_def] using this
    have ht2 : ⁅c', e⁆ ∈ A := by
      have := hcomm_mem c' hc' e he; simpa only [commutatorElement_def] using this
    have hzc : ⁅c', c⁆ ∈ Subgroup.center P :=
      hA2central _ (by rw [← hCd]; exact Subgroup.commutator_mem_commutator hc' hc)
    have h3 : ⁅⁅c', c⁆, e⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hzc e).symm
    have hJ : ⁅⁅c, e⁆, c'⁆ * ⁅⁅e, c'⁆, c⁆ * ⁅⁅c', c⁆, e⁆ = 1 := by
      simpa only [commutatorElement_def] using
        Work.Higman.Q3.crux_class_three_jacobi h hA hGs hsq htop c e c'
    rw [h3, mul_one] at hJ
    have h4 : ⁅⁅e, c'⁆, c⁆ = (⁅⁅c', e⁆, c⁆)⁻¹ := by
      rw [← commutatorElement_inv c' e]
      exact commutatorElement_inv_left_mem hAn hAab ht2
    rw [h4] at hJ
    have h5 : ⁅⁅c, e⁆, c'⁆ = ⁅⁅c', e⁆, c⁆ := mul_inv_eq_one.mp hJ
    simpa only [commutatorElement_def] using h5
  · by_contra hcon
    push_neg at hcon
    have hCEd : ⁅C, E⁆ ≤ Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_le]
      intro c hc e he
      have := hcon c hc e he
      simpa only [commutatorElement_def] using this
    haveI hCN : C.Normal := hCn
    haveI hEN : E.Normal := hEn
    have hkey : ⁅C ⊔ E, C ⊔ E⁆ ≤ Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_sup_right C E (C ⊔ E)]
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_sup_left C C E]
        exact sup_le (le_of_eq hCd) hCEd
      · rw [Subgroup.commutator_sup_left E C E]
        refine sup_le ?_ (le_of_eq hEd)
        rw [Subgroup.commutator_le]
        intro e he c hc
        rw [← commutatorElement_inv c e]
        exact Subgroup.inv_mem _ (by
          have := hcon c hc e he
          simpa only [commutatorElement_def] using this)
    have hA_le : A ≤ Work.Higman.powSub A 2 := by
      have h1 : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.powSub A 2 := by
        rw [← hCEsup]
        exact hkey
      rwa [hGs] at h1
    exact hAne2 (le_antisymm hA_le (Work.Higman.powSub_le (by norm_num)))

theorem two_cover_endgame {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C E : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hEn : E.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAC : A ≤ C) (hAE : A ≤ E) (hCA : A ≠ C) (hEA : A ≠ E)
    (hCcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hEcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) (hEd : ⁅E, E⁆ = Work.Higman.powSub A 2)
    (hCpow2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hEpow2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) (hEAd : ⁅E, A⁆ = Work.Higman.powSub A 2)
    (hCE : C ⊓ E = A) (hCEsup : C ⊔ E = ⊤) :
    False :=
  Work.Commutator.two_cover_false h hA
    (Work.Higman.maximal_of_c4_data h hA hsq hA4 htop hcard)
    hNA hGs hsq hA4 htop hcard hcent hCn hEn hCinv hEinv hAC hAE hCA hEA
    hCcover hEcover hCd hEd hCpow2 hEpow2 hCAd hEAd hCE hCEsup

end Work.Higman.NSM
