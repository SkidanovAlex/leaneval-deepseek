import Mathlib
import Submission.Work.Higman.higman9_case_deriv_le_sq
import Submission.Work.Higman.no_cent_elt_outside_maximal
import Submission.Work.Higman.H8.alt_pairing_false
import Submission.Work.Higman.no_square_derived
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.H8.c4_hard_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

open scoped commutatorElement

/-- In the situation of `c4_exclusion_sq` the Frattini subgroup `Φ(D) = D² ⊔ [D,D]` of the
covering `D` lies in `A` and contains `A²`, and is `ξ`-invariant; by the dichotomy for
`ξ`-invariant subgroups of `A` it is therefore `A²` or `A`. -/
theorem phi_dichotomy {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2) :
    Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ = Work.Higman.powSub A 2 ∨
      Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ = A := by
  have hA2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  have hPhile : Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ ≤ A := by
    refine sup_le ?_ ?_
    · rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    · rw [hDd]; exact hA2le
  have hA2lePhi : Work.Higman.powSub A 2 ≤ Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ := by
    rw [← hDd]; exact le_sup_right
  have hPhiinv : (Work.Higman.powSub D 2 ⊔ ⁅D, D⁆).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ := by
    rw [Subgroup.map_sup, Work.Higman.map_powSub (h.xi : MulAut P) hDinv 2,
      Subgroup.map_commutator, hDinv]
  exact Work.Higman.xi_invariant_eq_powSub_two_or_self h hA hPhile hA2lePhi hPhiinv

/-- **Higman 1963, Lemma 8, the case `C' = A²` of the `C₄` setting.**

Here `P` is a Suzuki 2-group, `A ≤ D` are normal `ξ`-invariant subgroups with `A` abelian and
maximal among the `ξ`-invariant abelian normal subgroups, `[P,P] = A`, every square of `P` in `A`,
`Ω₁(P) ≤ A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, `D > A` with `[D,D] = A²` and `D/A` a
minimal `ξ`-section above `A` (i.e. `hcover`).  Then contradiction.

The proof splits on `Φ(D) = D² ⊔ [D,D] ∈ {A², A}` (`phi_dichotomy`):

* `Φ(D) = A`: Higman's Lemma 7 (`Work.Higman.higman9_case_deriv_le_sq`) makes `D` abelian, against
  the maximality of `A`;
* `Φ(D) = A²` and `D` centralising `A`: Higman's fourth-power/Gorenstein–Thompson argument
  (`Work.Higman.H8.alt_pairing_false`);
* `Φ(D) = A²` and `D` not centralising `A`: the "hard core" `Work.Higman.H8.c4_hard_core`, where
  the centre analysis `Z(D) ∈ {A², A}` and the class-three eigenvalue argument (Higman's Lemma 6)
  are performed. -/
theorem c4_exclusion_sq {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D) :
    False := by
  classical
  have hA2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h2 := h.omega1_card_ge_four
    omega
  have hexp : ∀ a ∈ A, a ^ 4 = 1 := by
    intro a ha
    have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub ha
    rw [hA4] at hmem
    simpa using hmem
  rcases phi_dichotomy h hA hDinv hsq hDd with hPhi | hPhi
  · -- `Φ(D) = A²`
    by_cases hZ : ∀ e ∈ D, ∀ a ∈ A, e * a = a * e
    · -- `D` centralises `A`: Gorenstein--Thompson
      refine H8.alt_pairing_false h hA hDn hDinv hAD hADne hcover hZ ?_ hDd htop.symm hA2ne hexp
      exact (hPhi ▸ le_sup_left).trans hA2le
    · -- the hard case
      exact c4_hard_core h hA hmax hGs hsq hNA hA4 htop hcard hDn hDinv hAD hADne hDd hcover
        hPhi hZ
  · -- `Φ(D) = A`: Higman's Lemma 7 makes `D` abelian
    have hCd : ⁅D, D⁆ ≤ Work.Higman.powSub A 2 := hDd ▸ le_rfl
    have hDab :=
      Work.Higman.higman9_case_deriv_le_sq h hA hDn hDinv hAD hADne.symm hcover hPhi hCd
    exact hADne (hmax D ⟨hDn, hDinv, hDab⟩ hAD)

end Work.Higman.H8
