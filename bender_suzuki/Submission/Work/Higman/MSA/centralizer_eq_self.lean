import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.H8.alt_pairing_false
import Submission.Work.Higman.commutator_sq_eq_one_of_sq_mem_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.MSA

open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Elementary tools used by the proof of `centralizer_eq_self`

The three lemmas `xi_inv_sub_dichotomy'`, `dComm_dichotomy'` and `no_abelian_covering'` are
private copies of results that live in `Submission.Work.Higman.no_square_of_maximal`; that
module is (at the time of writing) not buildable because of an unfinished file below it in the
import graph, so the copies are made here to keep this module self-contained.  They are proved
by exactly the same (short) arguments. -/

/-- If `A` is invariant under an automorphism `ξ` of `P`, then so is the centralizer of `A`. -/
theorem centralizer_map_xi_eq {P : Type} [Group P] {A : Subgroup P} (ξ : MulAut P)
    (hAinv : A.map (ξ : MulAut P).toMonoidHom = A) :
    (Subgroup.centralizer (A : Set P)).map (ξ : MulAut P).toMonoidHom =
      Subgroup.centralizer (A : Set P) := by
  have mem_iff : ∀ g : P, (∀ a ∈ A, a * g = g * a) ↔
      g ∈ Subgroup.centralizer (A : Set P) := fun g => Subgroup.mem_centralizer_iff
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    refine (mem_iff (ξ x)).mpr ?_
    intro a ha
    have hx' := (mem_iff x).mp hx
    have h1 := hx' ((ξ : MulAut P).symm a)
      (Work.Higman.symm_mem_of_map_eq ξ hAinv ha)
    calc a * ξ x = ξ ((ξ : MulAut P).symm a) * ξ x := by simp
      _ = ξ ((ξ : MulAut P).symm a * x) := by simp
      _ = ξ (x * (ξ : MulAut P).symm a) := by rw [h1]
      _ = ξ x * a := by simp
  · intro y hy
    refine ⟨(ξ : MulAut P).symm y, ?_, by simp⟩
    refine (mem_iff ((ξ : MulAut P).symm y)).mpr ?_
    intro a ha
    have hy' := (mem_iff y).mp hy
    have h2 : ξ a ∈ A := by
      have h3 := Subgroup.mem_map_of_mem (ξ : MulAut P).toMonoidHom ha
      rwa [hAinv] at h3
    have h1 := hy' (ξ a) h2
    have h4 : a * (ξ : MulAut P).symm y = (ξ : MulAut P).symm y * a := by
      have := congrArg (ξ : MulAut P).symm h1
      simpa using this
    exact h4

/-- If `B` is a subgroup of a group `P` containing all squares of the elements of a subgroup
`D` and centralising `D`, then every commutator of two elements of `D` has order dividing two. -/
theorem commutator_sq_one_of_central_squares {P : Type} [Group P] {D B : Subgroup P}
    (hsq : ∀ x ∈ D, x ^ 2 ∈ B) (hcomm : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) :
    ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ^ 2 = 1 := by
  intro x hx y hy
  have hsq_center : ∀ u : ↥D, u ^ 2 ∈ Subgroup.center ↥D := by
    intro u
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hcomm (w : P) w.2 ((u : P) ^ 2) (hsq (u : P) u.2)
  have hcs := Work.Higman.commutator_sq_eq_one_of_sq_mem_center (P := ↥D) hsq_center
    ⟨x, hx⟩ ⟨y, hy⟩
  have key : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
    have := congrArg (fun t : ↥D => (t : P)) hcs
    simpa using this
  rw [commutatorElement_def]
  exact key

/-- In the maximal setting (`A² = Ω₁(P)`, `A⁴ = ⊥`) every `ξ`-invariant subgroup `B ≤ A` is
`⊥`, `A²` or `A`. -/
theorem xi_inv_sub_dichotomy' {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (htop : powSub A 2 = omega1 P) (hA4 : powSub A 4 = ⊥)
    {B : Subgroup P} (hBA : B ≤ A) (hBin : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = powSub A 2 ∨ B = A := by
  obtain ⟨e, -, -, -, hsub⟩ := homogeneous_structure h hA.abelian hA.map_eq
  obtain ⟨i, hi⟩ := hsub B hBA hBin
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · refine Or.inr (Or.inr ?_)
    rw [hi, h0, pow_zero, powSub_one_eq]
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
      exact le_bot_iff.mp (hA4 ▸ powSub_le_of_dvd hA.abelian hdvd)

/-- The derived subgroup of a `ξ`-invariant subgroup is `ξ`-invariant. -/
theorem map_commutator_self' {P : Type} [Group P] (ξ : MulAut P) {D : Subgroup P}
    (hDinv : D.map (ξ : MulAut P).toMonoidHom = D) :
    (⁅D, D⁆).map (ξ : MulAut P).toMonoidHom = ⁅D, D⁆ := by
  rw [Subgroup.map_commutator, hDinv]

/-- `D' ≤ A` whenever `[P,P] = A` and `D ≤ P`. -/
theorem commutator_le_of_eq_top' {P : Type} [Group P] {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) {D : Subgroup P} : ⁅D, D⁆ ≤ A := by
  rw [← hGs]
  exact Subgroup.commutator_mono le_top le_top

/-- For a `ξ`-invariant `D ≤ P` the derived subgroup `D'` is `⊥`, `A²` or `A`. -/
theorem dComm_dichotomy' {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A D : Subgroup P} (hA : IsXiAbelNormal h A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hA4 : powSub A 4 = ⊥)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    ⁅D, D⁆ = ⊥ ∨ ⁅D, D⁆ = powSub A 2 ∨ ⁅D, D⁆ = A :=
  xi_inv_sub_dichotomy' h hA htop hA4 (commutator_le_of_eq_top' hGs)
    (map_commutator_self' h.xi hDinv)

/-- An abelian `ξ`-invariant normal subgroup strictly containing `A` contradicts maximality. -/
theorem no_abelian_covering' {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A D : Subgroup P} (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D) (hab : ⁅D, D⁆ = ⊥) : False := by
  refine (ne_of_lt hAD).symm (hmax D ⟨hDn, hDinv, ?_⟩ (le_of_lt hAD))
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
    rw [← hab]
    exact Subgroup.commutator_mem_commutator hx hy
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

/-- The centralizer of `A` is `A` in the non-central case.  DO NOT prove this by appealing to
(e.g.) `Work.Higman.no_square_of_maximal` (same hypotheses, but its proof contains a `sorry`):
the goal must be reached without `sorryAx`.  Route: `D` minimal with `A < D ≤ C_P(A)`
(`MSA.exists_minimal_covering` with `M := C_P(A)`); `A ≤ Z(D)`, so `D` is of class two with
`D' ≤ [P,P] = A` ξ-invariant, whence `D' ∈ {⊥, A², A}` (`xi_inv_sub_dichotomy`).  `D' = ⊥`
contradicts `hmax` (`no_abelian_covering`), `D' = A²` contradicts `xi_alt_pairing_false`
(with `C := D`), and `D' = A` gives `D' ≤ Ω₁(P) = A² < A` because `⁅x,y⁆² = ⁅x²,y⁆ = 1`
for `x, y ∈ D` (`x² ∈ A ≤ Z(D)`), a contradiction. -/
theorem centralizer_eq_self {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAZ : ¬ A ≤ Subgroup.center P) :
    Subgroup.centralizer (A : Set P) = A := by
  classical
  haveI hAn : A.Normal := hA.normal
  set M : Subgroup P := Subgroup.centralizer (A : Set P) with hM
  have hAM : A ≤ M := by
    intro a ha
    rw [hM, Subgroup.mem_centralizer_iff]
    intro x hx
    exact hA.abelian x hx a ha
  by_cases hMA : M ≤ A
  · exact le_antisymm hMA hAM
  · -- `A < M`: take `D` minimal with `A < D ≤ M = C_P(A)`
    have hAne : A ≠ M := fun hEq => hMA (le_of_eq hEq.symm)
    have hAMlt : A < M := lt_of_le_of_ne hAM hAne
    have hMne : M ≠ A := ne_of_gt hAMlt
    have hMn : M.Normal := by rw [hM]; infer_instance
    have hMinv : M.map (h.xi : MulAut P).toMonoidHom = M := by
      rw [hM]; exact centralizer_map_xi_eq h.xi hA.map_eq
    obtain ⟨D, hDn, hDinv, hAD, hDM, hDA, hcover⟩ :=
      MSA.exists_minimal_covering h (A := A) (M := M) hMn hMinv hAM hMne
    have hADlt : A < D := lt_of_le_of_ne hAD hDA.symm
    -- every element of `D` commutes with every element of `A`
    have hDcomm : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := by
      intro d hd a ha
      have hdM : d ∈ Subgroup.centralizer (A : Set P) := hDM hd
      rw [Subgroup.mem_centralizer_iff] at hdM
      exact (hdM a ha).symm
    rcases dComm_dichotomy' h hA hGs htop hA4 hDinv with hD' | hD' | hD'
    · -- `D' = ⊥`: `D` is an abelian covering of `A`, contradicting maximality
      exact (no_abelian_covering' h hA hmax hDn hDinv hADlt hD').elim
    · -- `D' = A²`: the alternating pairing of `xi_alt_pairing_false`
      have hD2leA : powSub D 2 ≤ A := by
        rw [powSub, Subgroup.closure_le]
        rintro y ⟨x, hx, rfl⟩
        exact hsq x
      have hA2ne : powSub A 2 ≠ ⊥ := by
        intro hb
        have hc : Nat.card ↥(powSub A 2) = 1 := by rw [hb, Subgroup.card_bot]
        rw [htop] at hc
        have h4 := h.omega1_card_ge_four
        omega
      have hexp : ∀ a ∈ A, a ^ 4 = 1 := by
        intro a ha
        have hmem : a ^ 4 ∈ powSub A 4 := pow_mem_powSub ha
        rw [hA4] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact (H8.alt_pairing_false h hA hDn hDinv hAD hDA hcover hDcomm hD2leA hD'
        htop.symm hA2ne hexp).elim
    · -- `D' = A`: then `A ≤ Ω₁(P) = A² < A`, contradicting `|A| = |Ω₁(P)|²`
      have hcs : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ^ 2 = 1 :=
        commutator_sq_one_of_central_squares (B := A) (fun x _ => hsq x) hDcomm
      have hD'le : ⁅D, D⁆ ≤ omega1 P := by
        rw [Subgroup.commutator_le]
        intro x hx y hy
        exact h.mem_omega1.mpr (hcs x hx y hy)
      have hAle : A ≤ powSub A 2 := by
        rw [← htop] at hD'le
        rwa [hD'] at hD'le
      have hAeq : A = powSub A 2 := le_antisymm hAle (powSub_le (by norm_num))
      have hAne2 : A ≠ powSub A 2 := by
        intro heq
        have hc : Nat.card ↥A = Nat.card ↥(powSub A 2) :=
          congrArg (fun X : Subgroup P => Nat.card ↥X) heq
        rw [htop] at hc
        have hq : Nat.card ↥(Work.Higman.omega1 P) =
            (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
          rw [← hcard, ← hc]
        have h4 := h.omega1_card_ge_four
        have hcc : Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥(Work.Higman.omega1 P)
            = Nat.card ↥(Work.Higman.omega1 P) := by
          rw [← pow_two]
          exact hq.symm
        have hlt : Nat.card ↥(Work.Higman.omega1 P) <
            Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥(Work.Higman.omega1 P) := by
          have h1 := Nat.mul_lt_mul_of_pos_left (show 1 < Nat.card ↥(Work.Higman.omega1 P)
            by omega) (show 0 < Nat.card ↥(Work.Higman.omega1 P) by omega)
          simpa using h1
        exact absurd hcc (ne_of_gt hlt)
      exact (hAne2 hAeq).elim

end Work.Higman.MSA
