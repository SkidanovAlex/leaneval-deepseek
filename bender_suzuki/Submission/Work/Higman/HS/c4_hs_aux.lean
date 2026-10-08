/-
Copyright (c) 2024. All rights reserved.

# The `C₄` exclusion of the derived subgroup (`Work.Higman.HS.c4_exclusion_hs`)

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96: a Suzuki 2-group has no
`ξ`-invariant abelian normal subgroup `A` with `[P,P] = A`, `A² = Ω₁(P)`, `A⁴ = 1` and
`|A| = |Ω₁(P)|²`.

The reduction is complete and unconditional (see `NOTES_c4_hs.md` for the exact remaining work
and for a full proof of the `m = n` step, i.e. of `|C/A| = |Ω₁(P)|` for a cover with `C' = A`):

* `[A,P]` is `ξ`-invariant `≤ A`, hence `⊥`, `A²` or `A` (`xi_inv_sub_dichotomy`);
* `[A,P] = ⊥` is impossible (`comm_bot_false`), `[A,P] = A` is impossible (`comm_self_false`);
* for `[A,P] = A²` one takes a minimal cover `C` of `A` (`exists_minimal_cover`), splits
  `[C,C] ∈ {⊥, A², A}` and invokes the three case lemmas `abelian_cover_false`,
  `cover_deriv_sq_false`, `cover_deriv_self_false`.
-/

import Mathlib
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.HS.core_mul
import Submission.Work.Higman.H8.card_pow_of_irreducible
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.xi_pow_triv_omega1_iff
import Submission.Work.Higman.nsd_transfer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.HS

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary structural facts -/

/-- `[P,P] = A` makes `A` normal. -/
theorem normal_of_commutator_top_eq {A : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) :
    A.Normal := by
  rw [← hGs]
  exact Subgroup.commutator_normal ⊤ ⊤

/-- `⁅A,⊤⁆ ≤ A` for a normal `A`. -/
theorem commutator_A_top_le {A : Subgroup P} (hAn : A.Normal) : ⁅A, ⊤⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b _
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := by simpa using hAn.conj_mem a⁻¹ (A.inv_mem ha) b
  have h2 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def, mul_assoc]
  rw [h2]
  exact A.mul_mem ha h1

/-- `⁅A,⊤⁆` is `ξ`-invariant whenever `A` is. -/
theorem map_xi_commutator_A_top (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A) :
    Subgroup.map (h.xi : MulAut P).toMonoidHom (⁅A, ⊤⁆ : Subgroup P) = ⁅A, ⊤⁆ := by
  rw [Subgroup.map_commutator, hAxi,
    Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]

/-- **The dichotomy for `ξ`-invariant subgroups of `A`.**  In the configuration of the `C₄`
exclusion (`A` abelian, `ξ`-invariant, `A² = Ω₁(P)`, `A⁴ = ⊥`), every `ξ`-invariant subgroup of
`A` is `⊥`, `A²` or `A`. -/
theorem xi_inv_sub_dichotomy (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    {B : Subgroup P} (hBA : B ≤ A) (hBin : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = Work.Higman.powSub A 2 ∨ B = A := by
  obtain ⟨e, -, -, -, hsub⟩ := Work.Higman.homogeneous_structure h hab hinv
  obtain ⟨i, hi⟩ := hsub B hBA hBin
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · refine Or.inr (Or.inr ?_)
    rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]
  · rcases Nat.lt_or_ge i 2 with hlt | hge
    · refine Or.inr (Or.inl ?_)
      have hi1 : i = 1 := by omega
      rw [hi, hi1]
      norm_num
    · refine Or.inl ?_
      rw [hi]
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega⟩
      exact le_bot_iff.mp (hA4 ▸ Work.Higman.powSub_le_of_dvd hab hdvd)

/-- **`Ω₁(P)` is `ξ`-irreducible.**  A non-trivial `ξ`-invariant subgroup of `Ω₁(P)` is all of
`Ω₁(P)`: `ξ` is transitive on the involutions, and every element of `Ω₁(P)` is an involution. -/
theorem eq_omega1_of_ne_bot_of_map_eq (h : Work.Higman.IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ Work.Higman.omega1 P)
    (hSinv : Subgroup.map (h.xi : MulAut P).toMonoidHom S = S) (hne : S ≠ ⊥) :
    S = Work.Higman.omega1 P := by
  refine le_antisymm hS ?_
  obtain ⟨z, hzS, hz1⟩ : ∃ z ∈ S, z ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hne (le_bot_iff.mp (fun x hx => by simpa using hc x hx))
  have hz2 : z ^ 2 = 1 := h.mem_omega1.mp (hS hzS)
  have hzord : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hz2) with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h2
  have hstep : ∀ v ∈ S, h.xi v ∈ S := by
    intro v hv
    have h1 : h.xi v ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom S :=
      Subgroup.mem_map_of_mem _ hv
    rwa [hSinv] at h1
  have hpow : ∀ k : ℕ, ∀ v ∈ S, (h.xi ^ k) v ∈ S := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih => intro v hv; rw [pow_succ, MulAut.mul_apply]; exact ih (h.xi v) (hstep v hv)
  intro w hw
  have hw2 : w ^ 2 = 1 := h.mem_omega1.mp hw
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hw2) with h1 | h2
  · rw [orderOf_eq_one_iff.mp h1]
    exact S.one_mem
  · obtain ⟨k, hk⟩ := h.trans z w hzord h2
    rw [← hk]
    exact hpow k z hzS

/-- **A power of `ξ` that fixes one involution fixes `Ω₁(P)` pointwise.**  The `⟨ξ⟩`-orbit of an
involution `z` is all of `Ω₁(P) ∖ {1}` (`IsSuzuki2Grp.trans`), and the powers of `ξ` commute with
each other. -/
theorem xi_pow_fixes_omega1 (h : Work.Higman.IsSuzuki2Grp P) {k : ℕ} {z : P}
    (hz : orderOf z = 2) (hfix : (h.xi ^ k) z = z) :
    ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w := by
  intro w hw
  have hw2 : w ^ 2 = 1 := h.mem_omega1.mp hw
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hw2) with h1 | h2
  · rw [orderOf_eq_one_iff.mp h1]
    simp
  · obtain ⟨j, hj⟩ := h.trans z w hz h2
    have hcomm : (h.xi ^ k) ((h.xi ^ j) z) = (h.xi ^ j) ((h.xi ^ k) z) := by
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, add_comm, pow_add]
    rw [← hj, hcomm, hfix]

/-! ## The `L₃`-triviality input: `ξ ^ (|Ω₁(P)| - 1)` fixes `Ω₁(P)` pointwise -/

/-- `ξ ^ (|Ω₁(P)| - 1)` fixes `Ω₁(P)` pointwise (`Work.Higman.xi_pow_triv_omega1_iff`, which is
axiom-clean).  This is the `L₃`-triviality input of the `m = n` step, and also shows that
`η := ξ ^ (|Ω₁(P)| - 1)` acts trivially on `A/A²` whenever `A² = Ω₁(P)`. -/
theorem xi_pow_card_sub_one_fixes_omega1 (h : Work.Higman.IsSuzuki2Grp P) :
    ∀ w ∈ Work.Higman.omega1 P,
      (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) w = w :=
  (Work.Higman.xi_pow_triv_omega1_iff h (Nat.card ↥(Work.Higman.omega1 P) - 1)).mpr dvd_rfl

/-- Conversely, a power of `ξ` acting trivially on `Ω₁(P)` is a multiple of `|Ω₁(P)| - 1`. -/
theorem card_omega1_sub_one_dvd_of_xi_pow_triv (h : Work.Higman.IsSuzuki2Grp P) {k : ℕ}
    (hk : ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w) :
    (Nat.card ↥(Work.Higman.omega1 P) - 1) ∣ k :=
  (Work.Higman.xi_pow_triv_omega1_iff h k).mp hk

/-! ## The commutator collapse (Higman, Lemma 6, first step) -/

/-- Powers of an automorphism preserving a subgroup preserve it. -/
theorem mem_of_pow_map_eq {H : Subgroup P} {φ : MulAut P}
    (hφ : H.map (φ : MulAut P).toMonoidHom = H) (k : ℕ) {x : P} (hx : x ∈ H) :
    (φ ^ k) x ∈ H := by
  revert x
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply]
      exact ih (by rw [← hφ]; exact Subgroup.mem_map_of_mem _ hx)

/-- If `η = ξ ^ k` fixes `Ω₁(P)` pointwise and `A² = Ω₁(P)`, then `η` moves every element of `A`
by an element of `A²`. -/
theorem pow_mul_inv_mem_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) {k : ℕ}
    (hηΩ : ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w) {y : P} (hy : y ∈ A) :
    (h.xi ^ k) y * y⁻¹ ∈ Work.Higman.powSub A 2 := by
  have hyA : (h.xi ^ k) y ∈ A := mem_of_pow_map_eq (φ := h.xi) hAxi k hy
  have hcomm : Commute ((h.xi ^ k) y) y⁻¹ :=
    hAab ((h.xi ^ k) y) hyA y⁻¹ (A.inv_mem hy)
  rw [htop, h.mem_omega1]
  rw [Commute.mul_pow hcomm 2]
  rw [inv_pow, ← map_pow]
  have hy2 : (y : P) ^ 2 ∈ Work.Higman.omega1 P := by
    rw [← htop]; exact Work.Higman.pow_mem_powSub hy
  rw [hηΩ _ hy2, mul_inv_cancel]

/-- **Higman's commutator collapse (Lemma 6, first step).**  Let `A ≤ C` with `A` abelian
`ξ`-invariant, `A² = Ω₁(P)`, `[A,C] = A²`, and let `η = ξ ^ k` fix `Ω₁(P)` pointwise.  Then
`(η x)·x⁻¹` centralises `A` for every `x ∈ C`.

Proof.  `η y = y · u` with `u = y⁻¹(η y) ∈ A² ⊆ Z(P)`, so `[η x, η y] = [η x, y]`; and
`[η x, η y] = η [x, y] = [x, y]` because `[x, y] ∈ [C,A] = A² = Ω₁(P)` is fixed by `η`.  Writing
`δ := (η x)·x⁻¹`, so that `δ * x = η x`, the identity `[a*b, c] = a * [b, c] * a⁻¹ * [a, c]`
turns `[δ*x, y] = [x, y]` into `δ * [x, y] * δ⁻¹ * [δ, y] = [x, y]`, and `[x,y]` is central, so
`[δ, y] = 1`. -/
theorem commutator_pow_mul_inv_eq_one (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCA2 : ⁅A, C⁆ = Work.Higman.powSub A 2) {k : ℕ}
    (hηΩ : ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w) {x : P} (hx : x ∈ C) {y : P}
    (hy : y ∈ A) : ⁅(h.xi ^ k) x * x⁻¹, y⁆ = 1 := by
  have hyA : (h.xi ^ k) y ∈ A := mem_of_pow_map_eq (φ := h.xi) hAxi k hy
  have hu0 : (h.xi ^ k) y * y⁻¹ ∈ Work.Higman.powSub A 2 :=
    pow_mul_inv_mem_powSub_two h hAab hAxi htop hηΩ hy
  have hu : y⁻¹ * (h.xi ^ k) y ∈ Work.Higman.powSub A 2 := by
    rw [← hAab ((h.xi ^ k) y) hyA y⁻¹ (A.inv_mem hy)]
    exact hu0
  have huz : y⁻¹ * (h.xi ^ k) y ∈ Subgroup.center P := h.omega1_le_center (by rw [← htop]; exact hu)
  have hxy : ⁅x, y⁆ ∈ Work.Higman.powSub A 2 := by
    have h1 : ⁅x, y⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hx hy
    rwa [Subgroup.commutator_comm, hCA2] at h1
  have hxyz : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center (by rw [← htop]; exact hxy)
  have hfix : (h.xi ^ k) ⁅x, y⁆ = ⁅x, y⁆ := hηΩ ⁅x, y⁆ (by rw [← htop]; exact hxy)
  have key : ⁅(h.xi ^ k) x, (h.xi ^ k) y⁆ = ⁅x, y⁆ := by
    have h1 : ⁅(h.xi ^ k) x, (h.xi ^ k) y⁆ = (h.xi ^ k) ⁅x, y⁆ :=
      (map_commutatorElement (f := (h.xi ^ k : MulAut P).toMonoidHom) x y).symm
    rw [h1, hfix]
  have h2 : ⁅(h.xi ^ k) x, y⁆ = ⁅x, y⁆ := by
    have h1 : ⁅(h.xi ^ k) x, (h.xi ^ k) y⁆ = ⁅(h.xi ^ k) x, y⁆ := by
      have huy : (h.xi ^ k) y = y * (y⁻¹ * (h.xi ^ k) y) := by group
      rw [huy, commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp huz ((h.xi ^ k) x))]
      group
    rw [← h1, key]
  have hdx : ((h.xi ^ k) x * x⁻¹) * x = (h.xi ^ k) x := by group
  have h4 : ((h.xi ^ k) x * x⁻¹) * ⁅x, y⁆ * ((h.xi ^ k) x * x⁻¹)⁻¹
      * ⁅(h.xi ^ k) x * x⁻¹, y⁆ = ⁅x, y⁆ := by
    rw [← commutatorElement_mul_left_eq_conj_mul ((h.xi ^ k) x * x⁻¹) x y, hdx, h2]
  have hconj : ((h.xi ^ k) x * x⁻¹) * ⁅x, y⁆ * ((h.xi ^ k) x * x⁻¹)⁻¹ = ⁅x, y⁆ := by
    rw [(Subgroup.mem_center_iff.mp hxyz) ((h.xi ^ k) x * x⁻¹)]
    group
  rw [hconj] at h4
  exact mul_left_cancel (a := ⁅x, y⁆) (by simpa using h4)

/-! ## Higman's first step: `ξ ^ (|Ω₁| - 1)` acts trivially on `C/A` -/

/-- **Higman's Lemma 6, first step.**  Setting of Higman's Lemma 8 with `⁅C,C⁆ = A` and
`⁅A,C⁆ = A² = Ω₁(P)`: the power `ξ ^ (|Ω₁(P)| - 1)` acts trivially on `C/A`, i.e.
`(ξ^(|Ω₁|-1) x)·x⁻¹ ∈ A` for every `x ∈ C`.

Proof.  Let `E ≤ P` be generated by `A` and the elements `(η x)·x⁻¹` (`η := ξ^(|Ω₁|-1)`,
`x ∈ C`).  Then `E` is normal (`E/A ≤ C/A` and `C/A` is abelian because `C' = A`) and
`ξ`-invariant, and `A ≤ E ≤ C`, so `hcover` gives `E = A` or `E = C`.  If `E = C` then, since
every `(η x)·x⁻¹` centralises `A` (Higman's commutator collapse), `[C,A]` is generated by
conjugates of `1`, so `[C,A] = 1`, contradicting `[A,C] = A² ≠ 1`.  Hence `E = A`, which is the
claim. -/
theorem xi_pow_card_sub_one_triv_quot (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAn : A.Normal) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCA2 : ⁅A, C⁆ = Work.Higman.powSub A 2) (hCd : ⁅C, C⁆ = A) :
    ∀ x ∈ C, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A := by
  intro x0 hx0
  haveI := hAn
  set k : ℕ := Nat.card ↥(Work.Higman.omega1 P) - 1 with hk
  have hηΩ : ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w := by
    intro w hw; rw [hk]; exact xi_pow_card_sub_one_fixes_omega1 h w hw
  set G : Set P := (A : Set P) ∪ {e | ∃ y ∈ C, e = (h.xi ^ k) y * y⁻¹} with hG
  set E : Subgroup P := Subgroup.closure G with hE
  have hAE : A ≤ E := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have hEC : E ≤ C := by
    rw [hE, Subgroup.closure_le]
    rintro d (hd | ⟨y, hy, rfl⟩)
    · exact hAC hd
    · exact C.mul_mem (mem_of_pow_map_eq (φ := h.xi) hCinv k hy) (C.inv_mem hy)
  -- `ξ` sends each generator to a generator
  have hξC : ∀ y ∈ C, h.xi y ∈ C := by
    intro y hy
    have h1 : h.xi y ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom C := Subgroup.mem_map_of_mem _ hy
    rwa [hCinv] at h1
  have hgen : ∀ y ∈ C, h.xi ((h.xi ^ k) y * y⁻¹) = (h.xi ^ k) (h.xi y) * (h.xi y)⁻¹ := by
    intro y _
    have h1 : h.xi ((h.xi ^ k) y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ']
    have h2 : (h.xi ^ k) (h.xi y) = (h.xi ^ (k + 1)) y := by
      rw [← MulAut.mul_apply, ← pow_succ]
    simp only [map_mul, map_inv]
    rw [h1, h2]
  -- `ξ ^ (-1)` also sends generators to generators
  have hgen' : ∀ y ∈ C, (h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹)
      = (h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹ := by
    intro y hy
    have h1 : h.xi ((h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹)
        = (h.xi : MulAut P) ((h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹)) := by
      rw [hgen ((h.xi : MulAut P).symm y) (symm_mem_of_map_eq (h.xi : MulAut P) hCinv hy),
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h2 : (h.xi : MulAut P) ((h.xi : MulAut P).symm ((h.xi ^ k) y * y⁻¹))
        = (h.xi ^ k) y * y⁻¹ := MulEquiv.apply_symm_apply _ _
    exact h.xi.injective (by rw [h1, h2])
  -- `E` is `ξ`-invariant
  have hEin : Subgroup.map (h.xi : MulAut P).toMonoidHom E = E := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, hE, Subgroup.closure_le]
      rintro d (hd | ⟨y, hy, rfl⟩)
      · have h1 : h.xi d ∈ Subgroup.map (h.xi : MulAut P).toMonoidHom A := Subgroup.mem_map_of_mem _ hd
        rw [hAxi] at h1
        exact hAE h1
      · exact Subgroup.subset_closure (Or.inr ⟨h.xi y, hξC y hy, hgen y hy⟩)
    · rw [hE, Subgroup.closure_le]
      rintro d (hd | ⟨y, hy, rfl⟩)
      · refine Subgroup.mem_map.mpr ⟨(h.xi : MulAut P).symm d,
          hAE (symm_mem_of_map_eq (h.xi : MulAut P) hAxi hd), ?_⟩
        exact MulEquiv.apply_symm_apply h.xi d
      · have hy' : (h.xi : MulAut P).symm y ∈ C := symm_mem_of_map_eq (h.xi : MulAut P) hCinv hy
        refine Subgroup.mem_map.mpr ⟨(h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹,
          Subgroup.subset_closure (Or.inr ⟨(h.xi : MulAut P).symm y, hy', rfl⟩), ?_⟩
        show (h.xi : MulAut P) ((h.xi ^ k) ((h.xi : MulAut P).symm y) * ((h.xi : MulAut P).symm y)⁻¹)
          = (h.xi ^ k) y * y⁻¹
        rw [hgen ((h.xi : MulAut P).symm y) hy']
        simp
  -- `E` is normal: `E/A ≤ C/A`, `C/A` abelian since `C' = A`
  have hEn : E.Normal := by
    refine Subgroup.Normal.mk ?_
    intro d hd g
    have hcomm : g * d * g⁻¹ * d⁻¹ ∈ A := by
      have h1 : ⁅g, d⁆ ∈ ⁅(⊤ : Subgroup P), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top d)
      rw [hGs] at h1
      rwa [commutatorElement_def] at h1
    have h2 : g * d * g⁻¹ = (g * d * g⁻¹ * d⁻¹) * d := by group
    rw [h2]
    exact E.mul_mem (hAE hcomm) hd
  rcases hcover E hEn hEin hAE hEC with hEA | hEC'
  · -- `E = A`: the generator `(η x0)·x0⁻¹` lies in `A`
    have hmem : (h.xi ^ k) x0 * x0⁻¹ ∈ E := Subgroup.subset_closure (Or.inr ⟨x0, hx0, rfl⟩)
    rw [hEA] at hmem
    rw [hk] at hmem
    exact hmem
  · -- `E = C`: then `[C,A] = 1`, against `[A,C] = A²`
    exfalso
    have hCA1 : ⁅C, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcollapse : ∀ y ∈ C, ⁅(h.xi ^ k) y * y⁻¹, a⁆ = 1 :=
        fun y hy => commutator_pow_mul_inv_eq_one h hAab hAxi htop hCA2 hηΩ hy ha
      have hker : ∀ z ∈ E, ⁅z, a⁆ = 1 := by
        intro z hz
        rw [hE] at hz
        exact Subgroup.closure_induction
          (k := G) (p := fun (z : P) (_ : z ∈ Subgroup.closure G) => ⁅z, a⁆ = 1)
          (fun x hx => by
            rcases hx with hxA | ⟨y, hy, rfl⟩
            · rw [commutatorElement_eq_one_iff_mul_comm]
              exact (hAab a ha x hxA).symm
            · exact hcollapse y hy)
          (by simp)
          (fun x y hx hy ihx ihy => by
            rw [commutatorElement_mul_left_eq_conj_mul, ihx, ihy]
            group)
          (fun x hx ihx => by
            rw [commutatorElement_inv_left, show ⁅a, x⁆ = ⁅x, a⁆⁻¹ from (commutatorElement_inv x a).symm, ihx,
              inv_one]
            group)
          hz
      have h1 : ⁅c, a⁆ = 1 := hker c (hEC' ▸ hc)
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have h2 : Work.Higman.powSub A 2 = ⊥ := by
      rw [← hCA2, Subgroup.commutator_comm]; exact hCA1
    have h3 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, h2, Subgroup.card_bot]
    have h4 := h.omega1_card_ge_four
    omega
/-! ## Well-definedness of the commutator-square pairing on `C/A` -/

/-- Squaring is injective on the `2 ^ n`-th powers: if `x² = y²` then `x^(2^n) = y^(2^n)`
(for `n ≥ 1`). -/
theorem pow_two_pow_eq_of_sq_eq {P : Type} [Group P] {x y : P} {n : ℕ} (hn : 1 ≤ n)
    (h : x ^ 2 = y ^ 2) : x ^ 2 ^ n = y ^ 2 ^ n := by
  have h1 : ∀ z : P, z ^ 2 ^ n = (z ^ 2) ^ 2 ^ (n - 1) := by
    intro z
    rw [← pow_mul, show 2 * 2 ^ (n - 1) = 2 ^ n from by rw [← pow_succ']; congr 1; omega]
  rw [h1 x, h1 y, h]

/-- **Well-definedness of `⁅u⁻¹, v⁆²` on cosets of `A`.**  If `u' ≡ u` and `v' ≡ v` modulo `A`
(in the form `u'⁻¹ * u ∈ A`, `v'⁻¹ * v ∈ A`) then `⁅u⁻¹, v⁆² = ⁅u'⁻¹, v'⁆²`.

This is the well-definedness input for `MSA.L8.BV` (`(uA, vA) ↦ ⁅u⁻¹,v⁆ ^ 2^(e-1)` on
representatives): moving the `A`-component from the left of an argument to the right uses the
normality of `A`. -/
theorem comm_sq_eq_of_mul_mem (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hAn : A.Normal)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {u u' v v' : P} (hu : u'⁻¹ * u ∈ A) (hv : v'⁻¹ * v ∈ A) :
    ⁅u⁻¹, v⁆ ^ 2 = ⁅u'⁻¹, v'⁆ ^ 2 := by
  have hueq : u = u' * (u'⁻¹ * u) := by group
  have hveq : v = v' * (v'⁻¹ * v) := by group
  have ha' : u' * (u'⁻¹ * u)⁻¹ * u'⁻¹ ∈ A := hAn.conj_mem (u'⁻¹ * u)⁻¹ (A.inv_mem hu) u'
  have h2 : (u' * (u'⁻¹ * u))⁻¹ = u'⁻¹ * (u' * (u'⁻¹ * u)⁻¹ * u'⁻¹) := by group
  rw [hueq, hveq, h2]
  exact Work.Higman.comm_sq_congr h hAxi hAab hGs htop u'⁻¹ v' ha' hv

/-- The `2 ^ n`-th power version of `comm_sq_eq_of_mul_mem`: this is the form in which
`MSA.L8.BV` (whose exponent is `2 ^ (e - 1)`) is well defined on representatives. -/
theorem comm_pow_two_pow_eq_of_mul_mem (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAn : A.Normal) (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {n : ℕ} (hn : 1 ≤ n) {u u' v v' : P} (hu : u'⁻¹ * u ∈ A) (hv : v'⁻¹ * v ∈ A) :
    ⁅u⁻¹, v⁆ ^ 2 ^ n = ⁅u'⁻¹, v'⁆ ^ 2 ^ n :=
  pow_two_pow_eq_of_sq_eq hn (comm_sq_eq_of_mul_mem h hAn hAxi hAab hGs htop hu hv)

/-- **`ξ`-equivariance of the commutator pairing `BV`.**  In the situation of Higman's Lemma 8
with `e = 2` (so that the exponent `2 ^ (e - 1)` of `BV` is `2`), the pairing
`BV (x, y) = ⁅repC x⁻¹, repC y⁆ ^ 2` commutes with the `ξ`-actions on `C/A` and on `Ω₁(P)`.

Well-definedness (`comm_pow_two_pow_eq_of_mul_mem`) compares the two choices of representatives:
`repC (ξQuot x)` versus `ξ (repC x)`, which represent the same coset by
`QuotientGroup.congr_mk` and `MSA.L8.repC_spec`; the `ξ`-side is `map_pow`,
`map_commutatorElement` and `map_inv`. -/
theorem BV_xiQuot {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2)
    (x y : ↥C ⧸ (A.subgroupOf C)) :
    MSA.L8.BV S (MSA.L8.xiQuot h S.hA.map_eq S.hCinv x)
        (MSA.L8.xiQuot h S.hA.map_eq S.hCinv y)
      = MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h) (MSA.L8.BV S x y) := by
  have htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
    rw [← S.htopA, he]
    norm_num
  apply Subtype.ext
  rw [MSA.L8.BV_apply, MSA.L8.xiSubAut_apply, MSA.L8.BV_apply, he]
  norm_num
  -- goal: `⁅(repC x')⁻¹, repC y'⁆ ^ 2 = ⁅(ξ (repC x))⁻¹, ξ (repC y)⁆ ^ 2`
  set ux : ↥C := MSA.L8.xiSubAut h S.hCinv (MSA.L8.repC x) with hux
  set uy : ↥C := MSA.L8.xiSubAut h S.hCinv (MSA.L8.repC y) with huy
  have hx' : QuotientGroup.mk ux = MSA.L8.xiQuot h S.hA.map_eq S.hCinv x := by
    have h1 : MSA.L8.xiQuot h S.hA.map_eq S.hCinv (QuotientGroup.mk (MSA.L8.repC x))
        = QuotientGroup.mk ux := by
      rw [hux]
      exact (QuotientGroup.congr_mk (A.subgroupOf C) (A.subgroupOf C) (MSA.L8.xiSubAut h S.hCinv)
        (MSA.L8.map_xi_subgroupOf h S.hA.map_eq S.hCinv) (MSA.L8.repC x)).symm
    rw [MSA.L8.repC_spec x] at h1
    exact h1.symm
  have hy' : QuotientGroup.mk uy = MSA.L8.xiQuot h S.hA.map_eq S.hCinv y := by
    have h1 : MSA.L8.xiQuot h S.hA.map_eq S.hCinv (QuotientGroup.mk (MSA.L8.repC y))
        = QuotientGroup.mk uy := by
      rw [huy]
      exact (QuotientGroup.congr_mk (A.subgroupOf C) (A.subgroupOf C) (MSA.L8.xiSubAut h S.hCinv)
        (MSA.L8.map_xi_subgroupOf h S.hA.map_eq S.hCinv) (MSA.L8.repC y)).symm
    rw [MSA.L8.repC_spec y] at h1
    exact h1.symm
  have hu := MSA.L8.repC_mul_inv_mem (A := A) (C := C) hx'
  have hv := MSA.L8.repC_mul_inv_mem (A := A) (C := C) hy'
  have hmap : (h.xi (((MSA.L8.repC x : ↥C) : P)) : P) = ((ux : ↥C) : P) :=
    MSA.L8.xiSubAut_apply h S.hCinv (MSA.L8.repC x)
  have hmap' : (h.xi (((MSA.L8.repC y : ↥C) : P)) : P) = ((uy : ↥C) : P) :=
    MSA.L8.xiSubAut_apply h S.hCinv (MSA.L8.repC y)
  rw [hmap, hmap', hux, huy] at *
  exact (comm_pow_two_pow_eq_of_mul_mem h hAn S.hA.map_eq S.hA.abelian hGs htop
    (n := 1) le_rfl hu hv).symm

/-- The iterated form of `BV_xiQuot`: `BV` intertwines the `k`-th powers of the two `ξ`-actions. -/
theorem BV_xiQuot_pow {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2) (k : ℕ)
    (x y : ↥C ⧸ (A.subgroupOf C)) :
    MSA.L8.BV S (((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ k) x)
        (((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ k) y)
      = ((MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h)) ^ k) (MSA.L8.BV S x y) := by
  revert x y
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      have hxl : ((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ (k + 1)) x
          = ((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ k)
              (MSA.L8.xiQuot h S.hA.map_eq S.hCinv x) := by
        rw [pow_succ]; rfl
      have hyl : ((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ (k + 1)) y
          = ((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ k)
              (MSA.L8.xiQuot h S.hA.map_eq S.hCinv y) := by
        rw [pow_succ]; rfl
      have hzl : ((MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h)) ^ (k + 1))
            (MSA.L8.BV S x y)
          = ((MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h)) ^ k)
              (MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h) (MSA.L8.BV S x y)) := by
        rw [pow_succ]; rfl
      rw [hxl, hyl, hzl, ih, BV_xiQuot S hGs he]

/-! ## `A²` is central in `C`: the inputs for `im(BV) ≠ 1` -/

/-- In the situation of Higman's Lemma 8 with `e = 2` (so `A` has exponent `4`), `A ^ 4 = ⊥`. -/
theorem powSub_four_eq_bot {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (he : S.e = 2) : Work.Higman.powSub A 4 = ⊥ := by
  rw [eq_bot_iff, Work.Higman.powSub, Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  show x ^ 4 = 1
  rw [show (4 : ℕ) = 2 ^ S.e from by rw [he]; norm_num]
  exact S.he1 x hx

/-- **`A²` is central in `C`**: with `e = 2`, `⁅A,C⁆ = A²` and `⁅A²,C⁆ = A⁴ = ⊥`
(`Work.Higman.commutator_powSub_A_C`). -/
theorem powSub_two_central {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (he : S.e = 2) : ⁅Work.Higman.powSub A 2, C⁆ = ⊥ := by
  have h := Work.Higman.commutator_powSub_A_C h S.hA S.hCn S.hC2 S.hCd 1
  have h4 : ⁅Work.Higman.powSub A 2, C⁆ = Work.Higman.powSub A 4 := by
    simpa using h
  rw [h4, powSub_four_eq_bot S he]

/-- Consequently conjugation by `C` fixes `A²` pointwise. -/
theorem conj_powSub_two {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (he : S.e = 2) {a : P} (ha : a ∈ Work.Higman.powSub A 2) {c : P}
    (hc : c ∈ C) : c * a * c⁻¹ = a := by
  have h1 : ⁅a, c⁆ = 1 := by
    have h2 : ⁅a, c⁆ ∈ ⁅Work.Higman.powSub A 2, C⁆ :=
      Subgroup.commutator_mem_commutator ha hc
    rw [powSub_two_central S he] at h2
    simpa using h2
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [h1]
    _ = a := by group

/-- **`BV` does not vanish** (given `A ≠ A²`).  Since `⁅C,C⁆ = A ⊋ A²` there is a commutator
`⁅c,d⁆ ∉ A²`; then `BV (cA) (dA) = ⁅c⁻¹,d⁆² ≠ 1`: indeed `⁅c⁻¹,d⁆² = 1` would put `⁅c⁻¹,d⁆` in
`Ω₁ = A²`, and `⁅c⁻¹,d⁆ = c⁻¹ * ⁅c,d⁆⁻¹ * c` (`commutatorElement_inv_left`) together with the
fact that conjugation by `C` fixes `A²` pointwise (`conj_powSub_two`) would then force
`⁅c,d⁆ ∈ A²`, a contradiction. -/
theorem BV_ne_one {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : MSA.L8.D h A C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2)
    (hA2ne : A ≠ Work.Higman.powSub A 2) :
    ∃ x y : ↥C ⧸ (A.subgroupOf C), MSA.L8.BV S x y ≠ 1 := by
  have htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
    rw [← S.htopA, he]; norm_num
  obtain ⟨c, hc, d, hd, hcd⟩ : ∃ c ∈ C, ∃ d ∈ C, ⁅c, d⁆ ∉ Work.Higman.powSub A 2 := by
    by_contra hcon
    push_neg at hcon
    refine hA2ne (le_antisymm ?_ (Work.Higman.powSub_le (by norm_num)))
    conv_lhs => rw [← S.hCd]
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact hcon x hx y hy
  let xc : ↥C := ⟨c, hc⟩
  let xd : ↥C := ⟨d, hd⟩
  have hrepx : (((MSA.L8.repC (QuotientGroup.mk xc))⁻¹ * xc : ↥C) : P) ∈ A :=
    MSA.L8.repC_mul_inv_mem (A := A) (C := C) (x := QuotientGroup.mk xc) (u := xc) rfl
  have hrepy : (((MSA.L8.repC (QuotientGroup.mk xd))⁻¹ * xd : ↥C) : P) ∈ A :=
    MSA.L8.repC_mul_inv_mem (A := A) (C := C) (x := QuotientGroup.mk xd) (u := xd) rfl
  refine ⟨QuotientGroup.mk xc, QuotientGroup.mk xd, ?_⟩
  intro hzero
  have hval : ((MSA.L8.BV S (QuotientGroup.mk xc) (QuotientGroup.mk xd) : ↥(Work.Higman.omega1 P)) : P)
      = ⁅c⁻¹, d⁆ ^ 2 := by
    rw [MSA.L8.BV_apply, show (2 : ℕ) ^ (S.e - 1) = 2 from by rw [he]; norm_num]
    exact (comm_sq_eq_of_mul_mem h hAn S.hA.map_eq S.hA.abelian hGs htop hrepx hrepy).symm
  have hsq : ⁅c⁻¹, d⁆ ^ 2 = 1 := by
    have h1 : ((MSA.L8.BV S (QuotientGroup.mk xc) (QuotientGroup.mk xd) : ↥(Work.Higman.omega1 P)) : P) = 1 := by
      rw [hzero]; rfl
    rw [hval] at h1
    exact h1
  have hmem : ⁅c⁻¹, d⁆ ∈ Work.Higman.powSub A 2 := by
    rw [htop]
    exact h.mem_omega1.mpr hsq
  have hconj : ⁅c⁻¹, d⁆ = c⁻¹ * ⁅c, d⁆⁻¹ * c := by
    rw [commutatorElement_inv_left, commutatorElement_inv]
  have h1 : c * ⁅c⁻¹, d⁆ * c⁻¹ = ⁅c⁻¹, d⁆ := conj_powSub_two S he hmem hc
  have h2 : ⁅c, d⁆⁻¹ ∈ Work.Higman.powSub A 2 := by
    have h3 : c * ⁅c⁻¹, d⁆ * c⁻¹ = ⁅c, d⁆⁻¹ := by
      rw [hconj]; group
    rw [← h3, h1]
    exact hmem
  exact hcd (by simpa using (Work.Higman.powSub A 2).inv_mem h2)

/-- **`ξ^k = 1` on `C/A` forces `ξ^k = 1` on `Ω₁(P)`.**  The subgroup `F` of fixed points of
`ξZ^k` inside `↥(Ω₁ P)` contains every `BV`-value (`BV_xiQuot_pow` plus the hypothesis), hence the
subgroup generated by those values; `F` is a `ξ`-invariant subgroup of `Ω₁` (`ξZ` commutes with
`ξZ^k`) and it is non-trivial by `BV_ne_one`; `Ω₁` being `ξ`-irreducible
(`eq_omega1_of_ne_bot_of_map_eq`) then gives `F = ⊤`. -/
theorem xiZ_pow_fixes_of_xiQuot_pow_fixes {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : MSA.L8.D h A C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2)
    (hA2ne : A ≠ Work.Higman.powSub A 2) {k : ℕ}
    (hk : ∀ x : ↥C ⧸ (A.subgroupOf C),
      ((MSA.L8.xiQuot h S.hA.map_eq S.hCinv) ^ k) x = x) :
    ∀ w ∈ Work.Higman.omega1 P, (h.xi ^ k) w = w := by
  -- work inside `↥(Ω₁ P)`
  set ξZ : MulAut ↥(Work.Higman.omega1 P) := MSA.L8.xiSubAut h (Work.Higman.map_xi_omega1 h)
    with hξZ
  let F : Subgroup ↥(Work.Higman.omega1 P) :=
    { carrier := {v | (ξZ ^ k) v = v}
      mul_mem' := by
        intro a b ha hb
        show (ξZ ^ k) (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by show (ξZ ^ k) 1 = 1; exact map_one _
      inv_mem' := by
        intro a ha
        show (ξZ ^ k) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  -- every `BV`-value is fixed by `ξZ ^ k`
  have hmem : ∀ x y : ↥C ⧸ (A.subgroupOf C), MSA.L8.BV S x y ∈ F := by
    intro x y
    show (ξZ ^ k) (MSA.L8.BV S x y) = MSA.L8.BV S x y
    rw [hξZ, ← BV_xiQuot_pow S hGs he k x y, hk x, hk y]
  -- `F` is `ξ`-invariant
  have hFinv : Subgroup.map ξZ F = F := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro v hv
      show (ξZ ^ k) (ξZ v) = ξZ v
      have h1 : (ξZ ^ k) (ξZ v) = ξZ ((ξZ ^ k) v) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
      rw [h1, hv]
    · intro v hv
      refine Subgroup.mem_map.mpr ⟨ξZ.symm v, ?_, by simp⟩
      have h4 : ξZ ((ξZ ^ k) (ξZ.symm v)) = (ξZ ^ k) v := by
        rw [← MulAut.mul_apply, ← pow_succ', pow_succ, MulAut.mul_apply,
          MulEquiv.apply_symm_apply]
      have h3 : (ξZ ^ k) (ξZ.symm v) = ξZ.symm ((ξZ ^ k) v) := by
        apply ξZ.injective
        rw [MulEquiv.apply_symm_apply]
        exact h4
      show (ξZ ^ k) (ξZ.symm v) = ξZ.symm v
      rw [h3, hv]
  -- the image of `F` in `P` is a non-trivial `ξ`-invariant subgroup of `Ω₁`
  have hle : F.map (Subgroup.subtype (Work.Higman.omega1 P)) ≤ Work.Higman.omega1 P := by
    rintro v ⟨w, -, rfl⟩
    exact w.2
  have hne : F.map (Subgroup.subtype (Work.Higman.omega1 P)) ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := BV_ne_one S hGs he hA2ne
    intro hbot
    have h1 : ((MSA.L8.BV S x y : ↥(Work.Higman.omega1 P)) : P)
        ∈ F.map (Subgroup.subtype (Work.Higman.omega1 P)) :=
      Subgroup.mem_map_of_mem _ (hmem x y)
    rw [hbot] at h1
    exact hxy (by simpa using h1)
  have hinv : Subgroup.map (h.xi : MulAut P).toMonoidHom
        (F.map (Subgroup.subtype (Work.Higman.omega1 P)))
      = F.map (Subgroup.subtype (Work.Higman.omega1 P)) := by
    rw [Subgroup.map_map]
    have hcomp : (h.xi : MulAut P).toMonoidHom.comp (Subgroup.subtype (Work.Higman.omega1 P))
        = (Subgroup.subtype (Work.Higman.omega1 P)).comp (ξZ : MulAut ↥(Work.Higman.omega1 P)).toMonoidHom := by
      ext v
      show h.xi ((v : ↥(Work.Higman.omega1 P)) : P) = ((ξZ v : ↥(Work.Higman.omega1 P)) : P)
      rw [hξZ]
      exact MSA.L8.xiSubAut_apply h (Work.Higman.map_xi_omega1 h) v
    rw [hcomp, ← Subgroup.map_map,
      show Subgroup.map (MulEquiv.toMonoidHom ξZ) F = F from hFinv]
  intro w hw
  have hEq := eq_omega1_of_ne_bot_of_map_eq h
    (S := F.map (Subgroup.subtype (Work.Higman.omega1 P))) hle hinv hne
  have hw' : w ∈ F.map (Subgroup.subtype (Work.Higman.omega1 P)) := by
    rw [hEq]; exact hw
  obtain ⟨v, hv, hvw⟩ := hw'
  have hvfix : (ξZ ^ k) v = v := hv
  have h1 := congrArg (fun t : ↥(Work.Higman.omega1 P) => (t : P)) hvfix
  rw [MSA.L8.xiSubAut_pow_apply h (Work.Higman.map_xi_omega1 h) k v] at h1
  rw [← hvw]
  exact h1

/-! ## The induced automorphism of `C/A` -/

/-- The `k`-th power of `MSA.L8.xiQuot` sends `QuotientGroup.mk x` to `QuotientGroup.mk (ξ^k x)`. -/
theorem xiQuot_pow_mk {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (k : ℕ) (x : ↥C) :
    ((Work.Higman.MSA.L8.xiQuot h hAxi hCinv) ^ k) (QuotientGroup.mk x)
      = QuotientGroup.mk ((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x) := by
  revert x
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ, pow_succ]
      show (Work.Higman.MSA.L8.xiQuot h hAxi hCinv ^ k)
          (Work.Higman.MSA.L8.xiQuot h hAxi hCinv (QuotientGroup.mk x)) = _
      rw [show Work.Higman.MSA.L8.xiQuot h hAxi hCinv (QuotientGroup.mk x)
          = QuotientGroup.mk (Work.Higman.MSA.L8.xiSubAut h hCinv x) from
        QuotientGroup.congr_mk _ _ _ _ _]
      rw [ih]
      rfl

/-- **The order of the induced automorphism of `C/A` divides `k`, provided `ξ^k` acts trivially on
`C/A`.**  In particular (`k = |Ω₁(P)| - 1`, `xi_pow_card_sub_one_triv_quot`) the order of the
induced automorphism divides `|Ω₁(P)| - 1`: the easy half of the `m = n` count. -/
theorem orderOf_xiQuot_dvd {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) {k : ℕ}
    (hk : ∀ x ∈ C, (h.xi ^ k) x * x⁻¹ ∈ A) :
    orderOf (Work.Higman.MSA.L8.xiQuot h hAxi hCinv) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one]
  ext y
  induction y using QuotientGroup.induction_on with
  | _ x =>
      rw [xiQuot_pow_mk hAxi hCinv k x]
      have hmem : (h.xi ^ k) (x : P) * (x : P)⁻¹ ∈ A := hk (x : P) x.2
      have hmem' : (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P) * (x : P)⁻¹ ∈ A := by
        rw [Work.Higman.MSA.L8.xiSubAut_pow_apply]
        exact hmem
      have hx1 : (x : P)⁻¹ * (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P) ∈ A := by
        have h2 := hAn.conj_mem ((((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P) * (x : P)⁻¹)
          hmem' (x : P)⁻¹
        have h3 : (x : P)⁻¹ * ((((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P) * (x : P)⁻¹)
            * (x : P)⁻¹⁻¹ = (x : P)⁻¹ * (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P) := by
          group
        rwa [h3] at h2
      have h1 : (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P)⁻¹ * (x : P) ∈ A := by
        rw [show (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P)⁻¹ * (x : P)
            = ((x : P)⁻¹ * (((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x : ↥C) : P))⁻¹ from by group]
        exact A.inv_mem hx1
      have h1' : ((Work.Higman.MSA.L8.xiSubAut h hCinv ^ k) x)⁻¹ * x ∈ A.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        simpa using h1
      exact QuotientGroup.eq.mpr h1'

/-- **The order of the induced automorphism of `C/A` divides `|Ω₁(P)| - 1`.**  In the setting of
Higman's Lemma 8 with `⁅C,C⁆ = A`, `⁅A,C⁆ = A² = Ω₁(P)`: the first step
(`xi_pow_card_sub_one_triv_quot`) says that `ξ^(|Ω₁|-1)` acts trivially on `C/A`.  Together with
the reverse divisibility this gives `|C/A| = |Ω₁(P)|` (`H8.card_pow_of_irreducible`). -/
theorem orderOf_xiQuot_dvd_card_sub_one (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    [hAn : A.Normal] (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCA2 : ⁅A, C⁆ = Work.Higman.powSub A 2) (hCd : ⁅C, C⁆ = A) :
    orderOf (Work.Higman.MSA.L8.xiQuot h hAxi hCinv) ∣ Nat.card ↥(Work.Higman.omega1 P) - 1 :=
  orderOf_xiQuot_dvd hAxi hCinv
    (xi_pow_card_sub_one_triv_quot h hAn hAab hAxi hCn hCinv hGs hAC hCA hcover htop hCA2 hCd)

/-! ## The first two cases of `[A,P] ∈ {⊥, A², A}` -/

/-- **Case `⁅A,P⁆ = ⊥`.**  Then `A` is central, `P` has class two, every commutator is an
involution, and `A = [P,P] ≤ Ω₁ = A²`, contradicting `|A| = |Ω₁|²` with `|Ω₁| ≥ 4`. -/
theorem comm_bot_false (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (h3 : (⁅A, (⊤ : Subgroup P)⁆ : Subgroup P) = ⊥) : False := by
  -- `A` is central
  have hAZ : A ≤ Subgroup.center P := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro b
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup P) := by
      rw [← h3]
      exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b)
    have h2 : ⁅a, b⁆ = 1 := Subgroup.mem_bot.mp h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  -- `P` has class two: `[[P,P],[P,P]]`-free enough for `[x,y]² = [x²,y]`
  have hZ : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) ≤ Subgroup.center P := by
    rw [hGs]; exact hAZ
  have hsq1 : ∀ x y : P, ⁅x, y⁆ ^ 2 = 1 := by
    intro x y
    rw [Work.Higman.commutator_sq_eq hZ x y]
    have hx : x ^ 2 ∈ Subgroup.center P := hAZ (hsq x)
    have hc : y * x ^ 2 = x ^ 2 * y := (Subgroup.mem_center_iff.mp hx y)
    rw [commutatorElement_def, ← hc]
    group
  -- hence every commutator is an involution and `A ≤ Ω₁ = A²`
  have hAle : A ≤ Work.Higman.omega1 P := by
    rw [← hGs, Subgroup.commutator_le]
    intro x _ y _
    exact h.mem_omega1.mpr (hsq1 x y)
  have hAeq : A = Work.Higman.powSub A 2 := by
    rw [htop]
    exact le_antisymm hAle hNA
  have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.omega1 P) := by rw [hAeq, htop]
  have h1 : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    rw [← hc] at hcard
    rw [← hc]
    exact hcard
  have h2 := h.omega1_card_ge_four
  have h3' : 1 < Nat.card ↥(Work.Higman.omega1 P) := by omega
  nlinarith [h1, h2, h3']

/-- **Case `⁅A,P⁆ = A`.**  Then `A ≤ γ_n(P)` for every `n`, while `P` is nilpotent, so `A = ⊥`,
contradicting `Ω₁ ≤ A` with `|Ω₁| ≥ 4`. -/
theorem comm_self_false (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hNA : Work.Higman.omega1 P ≤ A) (h3 : (⁅A, (⊤ : Subgroup P)⁆ : Subgroup P) = A) : False := by
  have hNil : Group.IsNilpotent P := h.isPGroup.isNilpotent
  have hle : ∀ n : ℕ, A ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup P) n := by
    intro n
    induction n with
    | zero => rw [Subgroup.lowerCentralSeries_zero]; exact le_top
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        calc A = (⁅A, (⊤ : Subgroup P)⁆ : Subgroup P) := h3.symm
          _ ≤ (⁅Subgroup.lowerCentralSeries (⊤ : Subgroup P) n, (⊤ : Subgroup P)⁆ : Subgroup P) :=
              Subgroup.commutator_mono ih le_rfl
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hNil
  have hbot : A ≤ (⊥ : Subgroup P) := by
    have := hle n
    rwa [hn] at this
  have hcard1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
    have h1 : Work.Higman.omega1 P ≤ (⊥ : Subgroup P) := hNA.trans hbot
    rw [le_bot_iff.mp h1, Subgroup.card_bot]
  have h4 := h.omega1_card_ge_four
  omega

/-! ## A minimal `ξ`-invariant normal cover of `A` -/

/-- There is a `ξ`-invariant normal subgroup `C` minimal among those strictly containing `A`. -/
theorem exists_minimal_cover (h : IsSuzuki2Grp P) {A : Subgroup P} (hAne : A ≠ ⊤) :
    ∃ C : Subgroup P, C.Normal ∧ C.map (h.xi : MulAut P).toMonoidHom = C ∧ A ≤ C ∧ C ≠ A ∧
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) := by
  classical
  set S : Set (Subgroup P) :=
    {D | D.Normal ∧ D.map (h.xi : MulAut P).toMonoidHom = D ∧ A < D} with hS
  have hSne : S.Nonempty :=
    ⟨⊤, Subgroup.normal_top, by
      rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective], lt_of_le_of_ne le_top hAne⟩
  have hSfin : S.Finite := Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨C, hCs, hCmin⟩ := hSfin.exists_minimal hSne
  obtain ⟨hCn, hCinv, hAClt⟩ := hCs
  refine ⟨C, hCn, hCinv, le_of_lt hAClt, ne_of_gt hAClt, ?_⟩
  intro D hDn hDinv hAD hDC
  rcases eq_or_ne D A with hDA | hDA
  · exact Or.inl hDA
  · exact Or.inr (le_antisymm hDC (hCmin ⟨hDn, hDinv, lt_of_le_of_ne hAD (Ne.symm hDA)⟩ hDC))


/-- **Reverse divisibility**: `|Ω₁(P)| - 1` divides the order of the induced automorphism of
`C/A`.  Immediate from `xiZ_pow_fixes_of_xiQuot_pow_fixes` at `k = orderOf ξQuot` together with
`card_omega1_sub_one_dvd_of_xi_pow_triv`. -/
theorem card_sub_one_dvd_orderOf_xiQuot {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : MSA.L8.D h A C) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2)
    (hA2ne : A ≠ Work.Higman.powSub A 2) :
    (Nat.card ↥(Work.Higman.omega1 P) - 1)
      ∣ orderOf (MSA.L8.xiQuot h S.hA.map_eq S.hCinv) :=
  card_omega1_sub_one_dvd_of_xi_pow_triv h
    (xiZ_pow_fixes_of_xiQuot_pow_fixes S hGs he hA2ne (k := _) (by
      intro x; rw [pow_orderOf_eq_one]; rfl))

/-- **The order of the induced automorphism of `C/A` is `|Ω₁(P)| - 1`** — the `m = n` order
equality, combining the two divisibilities. -/
theorem orderOf_xiQuot_eq {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P}
    [hAn : A.Normal] (S : MSA.L8.D h A C) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) (he : S.e = 2) (hA2ne : A ≠ Work.Higman.powSub A 2)
    (hCn : C.Normal := S.hCn) (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCA2 : ⁅A, C⁆ = Work.Higman.powSub A 2) (hCd : ⁅C, C⁆ = A) :
    orderOf (MSA.L8.xiQuot h S.hA.map_eq S.hCinv)
      = Nat.card ↥(Work.Higman.omega1 P) - 1 :=
  Nat.dvd_antisymm
    (orderOf_xiQuot_dvd_card_sub_one h hAab S.hA.map_eq S.hCn S.hCinv hGs hAC hCA hcover
      (by rw [← S.htopA, he]; norm_num) hCA2 hCd)
    (card_sub_one_dvd_orderOf_xiQuot S hGs he hA2ne)

end Work.Higman.HS
