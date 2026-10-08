import Mathlib
import Submission.Work.Higman.xi_pow_triv_omega1_iff
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for `Work.Higman.H8.c4_sq_a2`

This file contains the pieces of the `C₄`-exclusion (`Work.Higman.H8.c4_sq_a2`) that are proved
independently of the still-open final case.  It is import-safe for delegated lemmas: the file
with the `sorry` (`H8/c4_sq_a2.lean`) imports *this* file, not the other way round.
-/

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- In the `C₄` setting `A ≠ ⊥` (from `|A| = |Ω₁(P)|² ≥ 4`). -/
theorem c4_A_ne_bot (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) : A ≠ ⊥ := by
  intro hb
  have h1 : Nat.card ↥A = 1 := by rw [hb, Subgroup.card_bot]
  have h4 := h.omega1_card_ge_four
  rw [h1] at hcard
  nlinarith [hcard, h4]

/-- **First step towards the counting.**  In the `C₄` setting with `C_P(A) = A` and
`[A,D] = A²`, the power `ξ ^ (|Ω₁(P)| - 1)` acts trivially on `D/A`: for `x ∈ D`,
`ξ^(q-1) x · x⁻¹ ∈ A` where `q = |Ω₁(P)|`.

Route: `Work.Higman.xi_pow_triv_omega1_iff` shows that `ξ^(q-1)` fixes `Ω₁(P) = A²` pointwise;
since `[D,A] ⊆ [D,D] = A² = Ω₁(P)` is central, `η := ξ^(q-1)` satisfies `[ηx, ηa] = η[x,a] = [x,a]`
for `x ∈ D`, `a ∈ A` (using `ηa · a⁻¹ ∈ A²`, i.e. triviality of `η` on `A/A²` via the
`ξ`-equivariant squaring isomorphism `A/A² ≅ A²`), so `ηx · x⁻¹` centralises `A`, and
`C_P(A) = A` gives `ηx · x⁻¹ ∈ A`.  The collapse `⁅ηx·x⁻¹, y⁆ = 1` is
`Work.Higman.HS.commutator_pow_mul_inv_eq_one`. -/
theorem c4_sq_a2_xi_pow_sub_one_triv (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hDA : ⁅A, D⁆ = Work.Higman.powSub A 2) :
    ∀ x ∈ D, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A := by
  intro x hx
  have hηΩ : ∀ w ∈ Work.Higman.omega1 P,
      (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) w = w :=
    (xi_pow_triv_omega1_iff h _).mpr (dvd_refl _)
  have hca : ∀ y ∈ A, ((h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹) * y
      = y * ((h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹) := by
    intro y hy
    have h1 : ⁅(h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹, y⁆ = 1 :=
      HS.commutator_pow_mul_inv_eq_one h hA.abelian hA.map_eq htop hDA hηΩ hx hy
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hmem : ((h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹)
      ∈ Subgroup.centralizer (A : Set P) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy => (hca y hy).symm)
  rwa [hcent] at hmem

end Work.Higman.H8
