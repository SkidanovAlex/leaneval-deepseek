/-
Copyright (c) 2024. All rights reserved.

# The `C₄`-endgame: the commutator pairing `b : P/A × C/A → A/A²`

Helper for `Work.Higman.RedAux.c4_endgame`.

Setting: `A ⊴ P` is a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group with
`⁅⊤,⊤⁆ = A`, every square of `P` in `A`, `A² = Ω₁(P)` (whence `A² ≠ ⊥`), and `C ⊴ P` is
`ξ`-invariant with `A ≤ C`.

Write `Z := A² = Ω₁(P)` (`Z` is central and elementary in `P`).  The commutator

    b(x, c) := ⁅x,c⁆ · Z  ∈  A/Z                       (x ∈ P, c ∈ C)

descends to a well-defined map `P/A × C/A → A/A²`.  This file proves:

* `c4_endgame_comm_A_top_eq` : `⁅A,⊤⁆ = A²`  (so `[A,P] ⊆ A²`), the form of Higman's
  unipotence needed for well-definedness in the *first* variable;
* `c4_powSub_two_mem_center` : `A² ≤ Z(P)`;
* `c4_b_wd1`, `c4_b_wd2`     : independence of the representatives (modulo `A`), stated on
  representatives as `⁅x·a,c⁆ · ⁅x,c⁆⁻¹ ∈ A²` and `⁅x,c·a⁆ · ⁅x,c⁆⁻¹ ∈ A²` for `a ∈ A`;
* `c4_b_add1`, `c4_b_add2`   : biadditivity modulo `A²`, with corrections `⁅x,⁅y,c⁆⁆·⁅⁅y,c⁆,⁅x,c⁆⁆`
  and `⁅c,⁅x,d⁆⁆` respectively;
* `c4_b_xi`                  : `ξ`-equivariance, `⁅ξx, ξc⁆ = ξ⁅x,c⁆`.

(Note for whoever continues: in the second variable the correction is `⁅x,a⁆` itself, **not**
`c·⁅x,a⁆·c⁻¹` — one must use that `⁅x,a⁆ ∈ A²` is central, since `A` does not commute with `C`,
only `[A,C] = A²`.  Likewise in the first variable the correction is the conjugate `x·⁅a,c⁆·x⁻¹`,
which equals `⁅a,c⁆` only by centrality of `A²`.)

Next paving stones (not in this file yet): biadditivity modulo `A²` (both variables), then the
two kernel computations — left kernel `C/A` under `hPhi`, right kernel `0` via `hcover` and
`⁅⊤,C⁆ = A` — which together with `Work.Higman.RedAux.finrank_le_of_forall_injective`
(`c4_spread.lean`) give `dim(P/C) ≤ n`, i.e. `|P| = q⁴`.
-/

import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.RedAux.c4_phi_equiv
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.H8.Clean.Nsd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped commutatorElement

namespace Work.Higman.RedAux

variable {P : Type} [Group P] [Finite P]

/-- **`⁅A,⊤⁆ = A²` in the `C₄` setting.**  Higman's unipotence gives `⁅A,⊤⁆ ≤ A² = Ω₁(P)`;
the case `⁅A,⊤⁆ = ⊥` (i.e. `A` central) is impossible, and `Ω₁(P)` is `ξ`-irreducible. -/
theorem c4_endgame_comm_A_top_eq (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 := by
  have hle : ⁅A, (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub A 2 :=
    Work.Higman.H8.Clean.nsd_comm_le h hA.map_eq hA.abelian hGs
  have hne : ⁅A, (⊤ : Subgroup P)⁆ ≠ ⊥ :=
    Work.Higman.H8.Clean.nsd_comm_eq_bot_false h hA.abelian hNA hGs hsq htop
  have hdich :=
    Work.Higman.H8.Clean.nsd_comm_eq_bot_or_omega1 h hA.map_eq hA.abelian hGs htop
  rcases hdich with hbot | htop'
  · exact absurd hbot hne
  · rw [htop', htop]

/-- In the `C₄` setting `A² = Ω₁(P)` is central in `P`. -/
theorem c4_powSub_two_mem_center (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Work.Higman.powSub A 2 ≤ Subgroup.center P := by
  rw [htop]; exact h.omega1_le_center

/-- **Well definedness of `b` in the first variable.**  For `a ∈ A`,
`⁅x·a, c⁆ ≡ ⁅x, c⁆  (mod A²)`. -/
theorem c4_b_wd1 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {a x c : P} (ha : a ∈ A) :
    ⁅x * a, c⁆ * ⁅x, c⁆⁻¹ ∈ Work.Higman.powSub A 2 := by
  -- `⁅a,c⁆ ∈ A²` by unipotence
  have hac : ⁅a, c⁆ ∈ Work.Higman.powSub A 2 := by
    have h1 : ⁅c, a⁆ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.commutator_mem_powSub_two h hA c a ha
    have h2 : ⁅a, c⁆ = ⁅c, a⁆⁻¹ := by rw [commutatorElement_def, commutatorElement_def]; group
    rw [h2]; exact Subgroup.inv_mem _ h1
  -- `x * ⁅a,c⁆ * x⁻¹ = ⁅a,c⁆` since `A² ≤ Z(P)`
  have hconj : x * ⁅a, c⁆ * x⁻¹ ∈ Work.Higman.powSub A 2 := by
    have hZ := c4_powSub_two_mem_center h htop hac
    have hc := Subgroup.mem_center_iff.mp hZ x
    have hxc : x * ⁅a, c⁆ * x⁻¹ = ⁅a, c⁆ := by rw [hc]; group
    rw [hxc]; exact hac
  have hgoal : ⁅x * a, c⁆ * ⁅x, c⁆⁻¹ = x * ⁅a, c⁆ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hgoal]
  exact hconj

/-- **Well definedness of `b` in the second variable.**  For `a ∈ A`,
`⁅x, c·a⁆ ≡ ⁅x, c⁆  (mod A²)`. -/
theorem c4_b_wd2 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {a x c : P} (ha : a ∈ A) :
    ⁅x, c * a⁆ * ⁅x, c⁆⁻¹ ∈ Work.Higman.powSub A 2 := by
  have hxa : ⁅x, a⁆ ∈ Work.Higman.powSub A 2 :=
    Work.Higman.commutator_mem_powSub_two h hA x a ha
  have hconj : c * ⁅x, a⁆ * c⁻¹ ∈ Work.Higman.powSub A 2 := by
    have hZ := c4_powSub_two_mem_center h htop hxa
    have hc := Subgroup.mem_center_iff.mp hZ c
    have hxc : c * ⁅x, a⁆ * c⁻¹ = ⁅x, a⁆ := by rw [hc]; group
    rw [hxc]; exact hxa
  have hcen : ⁅x, a⁆ ∈ Subgroup.center P := c4_powSub_two_mem_center h htop hxa
  have hgoal : ⁅x, c * a⁆ * ⁅x, c⁆⁻¹ = ⁅x, a⁆ := by
    have h1 : ⁅x, c * a⁆ = ⁅x, c⁆ * (c * ⁅x, a⁆ * c⁻¹) := by
      have h := commutatorElement_mul_right_eq_mul_conj x c a
      simp only [commutatorElement_def] at h ⊢
      rw [h]
      group
    have h2 : c * ⁅x, a⁆ * c⁻¹ = ⁅x, a⁆ := by
      rw [Subgroup.mem_center_iff.mp hcen c]; group
    rw [h1, h2]
    rw [Subgroup.mem_center_iff.mp hcen ⁅x, c⁆]
    group
  rw [hgoal]
  exact hxa

/-- **Biadditivity of `b` in the first variable** (modulo `A²`):
`⁅x·y, c⁆ ≡ ⁅x,c⁆ · ⁅y,c⁆`.  The correction, read off the commutator identity
`⁅x·y,c⁆ = (x·⁅y,c⁆·x⁻¹)·⁅x,c⁆`, is `⁅x,⁅y,c⁆⁆ · ⁅⁅y,c⁆,⁅x,c⁆⁆`, both factors lying in `A²`
(second arguments in `A`, using unipotence). -/
theorem c4_b_add1 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (x y c : P) :
    ⁅x * y, c⁆ * (⁅x, c⁆ * ⁅y, c⁆)⁻¹ ∈ Work.Higman.powSub A 2 := by
  have hyc : ⁅y, c⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top c)
    rwa [hGs] at h1
  -- `⁅x, ⁅y,c⁆⁆ ∈ A²` (unipotence, second argument in `A`)
  have hxz : ⁅x, ⁅y, c⁆⁆ ∈ Work.Higman.powSub A 2 :=
    Work.Higman.commutator_mem_powSub_two h hA x ⁅y, c⁆ hyc
  -- `⁅⁅y,c⁆, ⁅x,c⁆⁆ ∈ A²`
  have hzy : ⁅⁅y, c⁆, ⁅x, c⁆⁆ ∈ Work.Higman.powSub A 2 := by
    have h1 : ⁅⁅x, c⁆, ⁅y, c⁆⁆ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.commutator_mem_powSub_two h hA ⁅x, c⁆ ⁅y, c⁆ hyc
    have h2 : ⁅⁅y, c⁆, ⁅x, c⁆⁆ = ⁅⁅x, c⁆, ⁅y, c⁆⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h2]; exact Subgroup.inv_mem _ h1
  -- the whole difference is that product (a group identity)
  have hgoal : ⁅x * y, c⁆ * (⁅x, c⁆ * ⁅y, c⁆)⁻¹ = ⁅x, ⁅y, c⁆⁆ * ⁅⁅y, c⁆, ⁅x, c⁆⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hgoal]
  exact Subgroup.mul_mem _ hxz hzy

/-- **Biadditivity of `b` in the second variable** (modulo `A²`):
`⁅x, c·d⁆ ≡ ⁅x,c⁆ · ⁅x,d⁆`.  The correction, read off
`⁅x,c·d⁆ = ⁅x,c⁆·(c·⁅x,d⁆·c⁻¹)`, is `⁅c,⁅x,d⁆⁆ ∈ A²` (second argument `⁅x,d⁆ ∈ A`), which is
central because `A² = Ω₁(P) ≤ Z(P)`. -/
theorem c4_b_add2 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (x c d : P) :
    ⁅x, c * d⁆ * (⁅x, c⁆ * ⁅x, d⁆)⁻¹ ∈ Work.Higman.powSub A 2 := by
  have hxd : ⁅x, d⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top d)
    rwa [hGs] at h1
  have hcw : ⁅c, ⁅x, d⁆⁆ ∈ Work.Higman.powSub A 2 :=
    Work.Higman.commutator_mem_powSub_two h hA c ⁅x, d⁆ hxd
  -- the difference is the conjugate of that correction (a group identity)
  have hbase : ⁅x, c * d⁆ * (⁅x, c⁆ * ⁅x, d⁆)⁻¹
      = ⁅x, c⁆ * ⁅c, ⁅x, d⁆⁆ * ⁅x, c⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  -- conjugation fixes it, since `A² ≤ Z(P)`
  have hconj : ⁅x, c⁆ * ⁅c, ⁅x, d⁆⁆ * ⁅x, c⁆⁻¹ = ⁅c, ⁅x, d⁆⁆ := by
    have hZ := c4_powSub_two_mem_center h htop hcw
    have hc := Subgroup.mem_center_iff.mp hZ ⁅x, c⁆
    rw [hc]; group
  rw [hbase, hconj]
  exact hcw

/-- **The flipped form of biadditivity in the second variable**, i.e. the membership that
`QuotientGroup.eq.mpr` in the `map_mul'` step of the packaging actually asks for:
`⁅x,c·d⁆⁻¹ · (⁅x,c⁆ · ⁅x,d⁆) ∈ A²`, as opposed to `c4_b_add2`'s
`⁅x,c·d⁆ · (⁅x,c⁆·⁅x,d⁆)⁻¹ ∈ A²`.  The two forms differ by an inverse; the passage uses that
`A` is abelian, so that `u⁻¹ v = v u⁻¹`. -/
theorem c4_b_add2_rev (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (x c d : P) :
    ⁅x, c * d⁆⁻¹ * (⁅x, c⁆ * ⁅x, d⁆) ∈ Work.Higman.powSub A 2 := by
  have hu : ⁅x, c * d⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top (c * d))
    rwa [hGs] at h1
  have hv : ⁅x, c⁆ * ⁅x, d⁆ ∈ A := by
    refine A.mul_mem ?_ ?_
    · have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top c)
      rwa [hGs] at h1
    · have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top d)
      rwa [hGs] at h1
  have h2 := c4_b_add2 h hA hGs htop x c d
  have hinv : (⁅x, c * d⁆ * (⁅x, c⁆ * ⁅x, d⁆)⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 :=
    Subgroup.inv_mem _ h2
  have heq : ⁅x, c * d⁆⁻¹ * (⁅x, c⁆ * ⁅x, d⁆)
      = (⁅x, c * d⁆ * (⁅x, c⁆ * ⁅x, d⁆)⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hA.abelian _ (A.inv_mem hu) _ hv
  rw [heq]
  exact hinv

/-- The commutator `⁅x,c⁆` as an element of `A` (uses only `⁅⊤,⊤⁆ = A`). -/
theorem c4_commA_mem {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A) (x c : P) :
    x * c * x⁻¹ * c⁻¹ ∈ A := by
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top c)
  rwa [hGs] at h1

/-- `⁅x,c⁆` packaged as an element of `A`. -/
def c4_commA {A : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A) (x c : P) : ↥A :=
  ⟨x * c * x⁻¹ * c⁻¹, c4_commA_mem hGs x c⟩

@[simp] theorem c4_commA_coe {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A) (x c : P) :
    ((c4_commA hGs x c : ↥A) : P) = ⁅x, c⁆ := rfl

/-- **The quotient-level packaging, second variable.**  For fixed `x ∈ P` the map
`c̄ ↦ ⁅x,c⁆ · A²` is a well-defined homomorphism `C/A →* A/A²`:
multiplicativity is the flipped additivity `c4_b_add2_rev`, and the kernel contains `A` by the
unipotence `c4_b_wd2`. -/
theorem c4_b_hom_second (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    [hN2 : (A.subgroupOf C).Normal]
    [hN1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal]
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) (x : P) :
    ∃ Φ : (↥C ⧸ (A.subgroupOf C)) →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)),
      ∀ c : ↥C, Φ (QuotientGroup.mk c) = QuotientGroup.mk (c4_commA hGs x (c : P)) := by
  let f : ↥C →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) :=
    { toFun := fun c => QuotientGroup.mk (c4_commA hGs x (c : P))
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        have h1 : c4_commA hGs x ((1 : ↥C) : P) = 1 := by
          apply Subtype.ext
          simp [c4_commA]
        rw [h1]
        exact Subgroup.one_mem _
      map_mul' := fun c d => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, c4_commA_coe]
        exact c4_b_add2_rev h hA hGs htop x (c : P) (d : P) }
  have hle : A.subgroupOf C ≤ MonoidHom.ker f := by
    intro c hc
    show QuotientGroup.mk (c4_commA hGs x (c : P)) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [c4_commA, commutatorElement_def] using
      Work.Higman.commutator_mem_powSub_two h hA x c (Subgroup.mem_subgroupOf.mp hc)
  exact ⟨QuotientGroup.lift (A.subgroupOf C) f hle,
    fun c => QuotientGroup.lift_mk (N := A.subgroupOf C) (φ := f) hle c⟩

/-- **The flipped form of biadditivity in the first variable** — the exact analogue of
`c4_b_add2_rev` and the membership that the `map_mul'` step of the first-variable packaging asks
for: `⁅x·y,c⁆⁻¹ · (⁅x,c⁆ · ⁅y,c⁆) ∈ A²`, as opposed to `c4_b_add1`'s product with `(…)⁻¹`.
Same passage: take the inverse and commute using abelianness of `A`. -/
theorem c4_b_add1_rev (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (x y c : P) :
    ⁅x * y, c⁆⁻¹ * (⁅x, c⁆ * ⁅y, c⁆) ∈ Work.Higman.powSub A 2 := by
  have hu : ⁅x * y, c⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top (x * y))
      (Subgroup.mem_top c)
    rwa [hGs] at h1
  have hv : ⁅x, c⁆ * ⁅y, c⁆ ∈ A := by
    refine A.mul_mem ?_ ?_
    · have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top c)
      rwa [hGs] at h1
    · have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top c)
      rwa [hGs] at h1
  have h2 := c4_b_add1 h hA hGs x y c
  have hinv : (⁅x * y, c⁆ * (⁅x, c⁆ * ⁅y, c⁆)⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 :=
    Subgroup.inv_mem _ h2
  have heq : ⁅x * y, c⁆⁻¹ * (⁅x, c⁆ * ⁅y, c⁆)
      = (⁅x * y, c⁆ * (⁅x, c⁆ * ⁅y, c⁆)⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hA.abelian _ (A.inv_mem hu) _ hv
  rw [heq]
  exact hinv

/-- **The quotient-level packaging, first variable, fixed second argument.**  Mirror of
`c4_b_hom_second`: for fixed `c ∈ P` the map `x̄ ↦ ⁅x,c⁆ · A²` is a well-defined homomorphism
`P/A →* A/A²`.  Multiplicativity is the mirror flip `c4_b_add1_rev`; the kernel contains `A` by
unipotence in the first argument (`⁅a,c⁆ = ⁅c,a⁆⁻¹ ∈ A²` for `a ∈ A`). -/
theorem c4_b_hom_first_single (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) [hN0 : A.Normal]
    [hN1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal]
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) (c : P) :
    ∃ Φ : (P ⧸ A) →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)),
      ∀ x : P, Φ (QuotientGroup.mk x) = QuotientGroup.mk (c4_commA hGs x c) := by
  let f : P →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)) :=
    { toFun := fun x => QuotientGroup.mk (c4_commA hGs x c)
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        have h1 : c4_commA hGs (1 : P) c = 1 := by
          apply Subtype.ext
          simp [c4_commA]
        rw [h1]
        exact Subgroup.one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, c4_commA_coe]
        exact c4_b_add1_rev h hA hGs x y c }
  have hker : A ≤ MonoidHom.ker f := by
    intro a ha
    show QuotientGroup.mk (c4_commA hGs a c) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, c4_commA_coe]
    have h2 : ⁅c, a⁆ ∈ Work.Higman.powSub A 2 :=
      Work.Higman.commutator_mem_powSub_two h hA c a ha
    have h3 : ⁅a, c⁆ = ⁅c, a⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h3]
    exact Subgroup.inv_mem _ h2
  have hform : ∀ x : P, QuotientGroup.lift A f hker (QuotientGroup.mk x) = f x :=
    fun x => QuotientGroup.lift_mk (N := A) (φ := f) hker x
  exact ⟨QuotientGroup.lift A f hker, fun x => hform x⟩

/-- **Flipped orientation of `c4_b_wd1`**, i.e. the membership `QuotientGroup.eq.mpr` asks for when
the well-definedness of `x̄ ↦ b(x̄,c)` is checked at the quotient level.  Same passage as the
additivity flips: take the inverse, then commute using abelianness of `A`. -/
theorem c4_b_wd1_rev (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {a x c : P} (ha : a ∈ A) :
    ⁅x * a, c⁆⁻¹ * ⁅x, c⁆ ∈ Work.Higman.powSub A 2 := by
  have hu : ⁅x * a, c⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top (x * a))
      (Subgroup.mem_top c)
    rwa [hGs] at h1
  have hv : ⁅x, c⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top c)
    rwa [hGs] at h1
  have h2 := c4_b_wd1 h hA htop (x := x) (c := c) ha
  have hinv : (⁅x * a, c⁆ * ⁅x, c⁆⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 := Subgroup.inv_mem _ h2
  have heq : ⁅x * a, c⁆⁻¹ * ⁅x, c⁆ = (⁅x * a, c⁆ * ⁅x, c⁆⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hA.abelian _ (A.inv_mem hu) _ hv
  rw [heq]
  exact hinv

/-- **Flipped orientation of `c4_b_wd2`** (the mirror of `c4_b_wd1_rev`). -/
theorem c4_b_wd2_rev (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {a x c : P} (ha : a ∈ A) :
    ⁅x, c * a⁆⁻¹ * ⁅x, c⁆ ∈ Work.Higman.powSub A 2 := by
  have hu : ⁅x, c * a⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top (c * a))
    rwa [hGs] at h1
  have hv : ⁅x, c⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top c)
    rwa [hGs] at h1
  have h2 := c4_b_wd2 h hA htop (x := x) (c := c) ha
  have hinv : (⁅x, c * a⁆ * ⁅x, c⁆⁻¹)⁻¹ ∈ Work.Higman.powSub A 2 := Subgroup.inv_mem _ h2
  have heq : ⁅x, c * a⁆⁻¹ * ⁅x, c⁆ = (⁅x, c * a⁆ * ⁅x, c⁆⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact hA.abelian _ (A.inv_mem hu) _ hv
  rw [heq]
  exact hinv

/-- **The curried pairing `b : P → C/A → A/A²`** (function level: a raw function with additivity
equations, the form the resonance tool consumes; no nested `MonoidHom` type).  Each `b x` is the
homomorphism of `c4_b_hom_second` (`Classical.choose`); multiplicativity in the first variable is
checked on the generators `mk c`, where it is the flip `c4_b_add1_rev`. -/
theorem c4_b_bimap (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) [hN2 : (A.subgroupOf C).Normal]
    [hN1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal]
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    ∃ b : P → (↥C ⧸ (A.subgroupOf C)) → (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)),
      (∀ x c, b x (QuotientGroup.mk c) = QuotientGroup.mk (c4_commA hGs x c)) ∧
      (∀ x c c', b x (c * c') = b x c * b x c') ∧
      (∀ x y c, b (x * y) c = b x c * b y c) := by
  classical
  haveI hI2 : (A.subgroupOf C).Normal := hN2
  haveI hI1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal := hN1
  have hex : ∀ x : P,
      ∃ Φ : (↥C ⧸ (A.subgroupOf C)) →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A)),
        ∀ c : ↥C, Φ (QuotientGroup.mk c) = QuotientGroup.mk (c4_commA hGs x c) :=
    fun x => c4_b_hom_second h hA hGs htop x
  let Ψ : P → ((↥C ⧸ (A.subgroupOf C)) →* (↥A ⧸ ((Work.Higman.powSub A 2).subgroupOf A))) :=
    fun x => Classical.choose (hex x)
  have hΨ : ∀ (x : P) (c : ↥C),
      Ψ x (QuotientGroup.mk c) = QuotientGroup.mk (c4_commA hGs x c) :=
    fun x c => Classical.choose_spec (hex x) c
  have hmulx : ∀ x y : P, ∀ c : ↥C ⧸ (A.subgroupOf C), Ψ (x * y) c = Ψ x c * Ψ y c := by
    intro x y c
    induction c using QuotientGroup.induction_on with
    | _ c0 =>
      rw [hΨ (x * y) c0, hΨ x c0, hΨ y c0, ← QuotientGroup.mk_mul]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c4_commA_coe]
      exact c4_b_add1_rev h hA hGs x y c0
  exact ⟨fun x (c : ↥C ⧸ (A.subgroupOf C)) => Ψ x c, fun x c => hΨ x c,
    fun x c c' => map_mul (Ψ x) c c', fun x y c => hmulx x y c⟩

/-- **The left kernel of `b(·, c̄)` is `C/A`.**  Under the subgroup form `hphi` (every `x ∉ C`
has `⁅⟨x⟩,C⁆ ⊄ A`) the elementwise condition `∀ c ∈ C, ⁅x,c⁆ ∈ A` forces `x ∈ C`.  Immediate from
the equivalence `c4_phi_equiv`; recorded because it is the left-kernel statement used together
with the pairing `c4_b_bimap`. -/
theorem c4_kernel_left {P : Type} [Group P] {A C : Subgroup P} (hA : A.Normal)
    (hphi : ∀ x : P, x ∉ C → ¬ (⁅Subgroup.zpowers x, C⁆ ≤ A))
    {x : P} (hxc : ∀ c : P, c ∈ C → x * c * x⁻¹ * c⁻¹ ∈ A) : x ∈ C := by
  by_contra hx
  exact hphi x hx ((Work.Higman.RedAux.c4_phi_equiv hA).mpr hxc)

/-- **`ξ`-equivariance** of the raw pairing, `⁅ξx, ξc⁆ = ξ⁅x, c⁆`. -/
theorem c4_b_xi (h : Work.Higman.IsSuzuki2Grp P) (x c : P) :
    ⁅(h.xi : MulAut P) x, (h.xi : MulAut P) c⁆ = (h.xi : MulAut P) ⁅x, c⁆ := by
  simp only [commutatorElement_def, map_mul, map_inv]

end Work.Higman.RedAux
