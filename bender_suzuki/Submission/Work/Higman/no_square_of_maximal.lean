import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.commutator_le_omega1
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.higman9_case_deriv_le_sq
import Submission.Work.Higman.H8.c4_exclusion
import Submission.Work.Higman.H8.c4_exclusion_sq
import Submission.Work.Higman.H8.alt_pairing_false

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Structural lemmas in the maximal setting -/

/-- In the maximal setting (`A² = Ω₁(P)`, `A⁴ = 1`) every `ξ`-invariant subgroup `B ≤ A` is
`⊥`, `A²` or `A`.  (Higman's Lemma 1: the `ξ`-invariant subgroups of `A` are the power subgroups
`A ^ (2 ^ i)`; here only `i = 0`, `i = 1` and `i ≥ 2` occur, and the last gives `⊥` because
`A ^ 4 = ⊥`.) -/
theorem xi_inv_sub_dichotomy (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A)
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

/-- In a group of class two, `⁅x, y ^ 2⁆ = ⁅x, y⁆ ^ 2`. -/
theorem class_two_sq_sq {G : Type} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y : G) :
    ⁅x, y ^ 2⁆ = ⁅x, y⁆ ^ 2 := by
  have hcomm : y * ⁅x, y⁆ = ⁅x, y⁆ * y := commutator_central_comm hZ x y y
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := Work.Higman.mul_mul_inv_eq_commutator_mul x y
  have h2 : x * y ^ 2 * x⁻¹ = (x * y * x⁻¹) ^ 2 := by
    rw [pow_two, pow_two]; group
  have h4 : (⁅x, y⁆ * y) ^ 2 * (y ^ 2)⁻¹ = ⁅x, y⁆ ^ 2 := by
    rw [pow_two, pow_two]
    rw [show (⁅x, y⁆ * y) * (⁅x, y⁆ * y) = ⁅x, y⁆ * (y * ⁅x, y⁆) * y by group, hcomm]
    rw [pow_two]
    group
  rw [commutatorElement_def, h2, h1, h4]

/-- If two elementary abelian `2`-groups carrying `ξ`-actions transitive on the non-identity
elements are joined by a `ξ`-equivariant isomorphism `e`, then every `ξ`-equivariant alternating
biadditive map `c : W → W → V` is trivial (transport along `e` and apply Gorenstein–Thompson,
`equivariant_bihom_trivial`). -/
theorem no_alt_form_of_iso {W V : Type} [CommGroup W] [CommGroup V] [Finite W] [Finite V]
    (hW2 : ∀ a : W, a * a = 1)
    (ξW : MulAut W) (hWtr : ∀ a b : W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b)
    (ξV : MulAut V)
    (e : W ≃* V) (he : ∀ a : W, e (ξW a) = ξV (e a))
    (c : W → W → V)
    (hmul : ∀ a b d : W, c (a * b) d = c a d * c b d)
    (hmul' : ∀ a b d : W, c a (b * d) = c a b * c a d)
    (halt : ∀ a : W, c a a = 1)
    (heq : ∀ a b : W, ξV (c a b) = c (ξW a) (ξW b)) :
    ∀ a b : W, c a b = 1 := by
  have hesym : ∀ v : V, ξW (e.symm v) = e.symm (ξV v) := by
    intro v
    apply e.injective
    rw [he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have key : ∀ a b : W, e.symm (c a b) = 1 :=
    equivariant_bihom_trivial hW2 ξW hWtr (fun a b => e.symm (c a b))
      (by intro a b d; rw [hmul a b d, map_mul])
      (by intro a b d; rw [hmul' a b d, map_mul])
      (by intro a; rw [halt a, map_one])
      (by intro a b; rw [hesym (c a b), heq a b])
  intro a b
  have h := congrArg e (key a b)
  rwa [MulEquiv.apply_symm_apply, map_one] at h

/-! ## Entering Case 2: the centre meets `A` in `A²` -/

/-- The centre of a Suzuki 2-group is `ξ`-invariant. -/
theorem map_xi_center_eq (h : IsSuzuki2Grp P) :
    (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom = Subgroup.center P := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨z, hz, rfl⟩
    exact aut_mem_center (h.xi : MulAut P) hz
  · intro x hx
    exact ⟨(h.xi : MulAut P).symm x, aut_mem_center ((h.xi : MulAut P).symm) hx, by simp⟩

/-- In the non-central case `Z(P) ⊓ A = A² = Ω₁(P)`: the intersection is a `ξ`-invariant
subgroup of `A` containing `A²`, hence `A²` or `A` by `xi_inv_sub_dichotomy`, and it is not `A`
because `A ⊄ Z(P)`. -/
theorem inf_center_eq_powSub_two (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hNA : omega1 P ≤ A)
    (htop : powSub A 2 = omega1 P) (hA4 : powSub A 4 = ⊥)
    (hAZ : ¬ A ≤ Subgroup.center P) :
    A ⊓ Subgroup.center P = powSub A 2 := by
  have hBin : (A ⊓ Subgroup.center P).map (h.xi : MulAut P).toMonoidHom
      = A ⊓ Subgroup.center P := by
    rw [Subgroup.map_inf A (Subgroup.center P) (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective, hA.map_eq, map_xi_center_eq h]
  have hle : powSub A 2 ≤ A ⊓ Subgroup.center P := by
    rw [htop]
    exact le_inf hNA h.omega1_le_center
  rcases xi_inv_sub_dichotomy h hA htop hA4 inf_le_left hBin with hbot | h2 | htop'
  · rw [hbot] at hle
    have hc : Nat.card ↥(omega1 P) = 1 := by
      rw [← htop, le_bot_iff.mp hle, Subgroup.card_bot]
    have := h.omega1_card_ge_four
    omega
  · exact h2
  · exact absurd (htop' ▸ inf_le_right) hAZ

/-! ## A minimal `ξ`-invariant normal subgroup strictly above `A` -/

/-- There is a `ξ`-invariant normal subgroup `D` minimal among those strictly containing `A`. -/
theorem exists_minimal_covering_of_lt (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAne : A ≠ ⊤) :
    ∃ D : Subgroup P, D.Normal ∧ D.map (h.xi : MulAut P).toMonoidHom = D ∧ A < D ∧
      ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
        A < E → E ≤ D → E = D := by
  classical
  set S : Set (Subgroup P) :=
    {D | D.Normal ∧ D.map (h.xi : MulAut P).toMonoidHom = D ∧ A < D} with hS
  have hSne : S.Nonempty :=
    ⟨⊤, Subgroup.normal_top, by simp, lt_of_le_of_ne le_top hAne⟩
  have hSfin : S.Finite := Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨D, hDs, hDmin⟩ := hSfin.exists_minimal hSne
  obtain ⟨hDn, hDinv, hAD⟩ := hDs
  exact ⟨D, hDn, hDinv, hAD, fun E hEn hEinv hAE hED =>
    le_antisymm hED (@hDmin E ⟨hEn, hEinv, hAE⟩ hED)⟩

/-! ## Two elementary facts about the derived subgroup -/

/-- In any group, the derived subgroup is contained in the subgroup generated by the squares:
`⁅x⁻¹,y⁆ = x⁻² (xy)² y⁻²`. -/
theorem commutator_le_powSub_two {G : Type} [Group G] (D : Subgroup G) :
    ⁅D, D⁆ ≤ powSub D 2 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have key : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹ := by
    rw [commutatorElement_def, pow_two (a := x), pow_two (a := x⁻¹ * y), pow_two (a := y)]
    group
  rw [key]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact pow_mem_powSub hx
  · exact pow_mem_powSub (D.mul_mem (D.inv_mem hx) hy)
  · exact Subgroup.inv_mem _ (pow_mem_powSub hy)

/-- The derived subgroup of a `ξ`-invariant subgroup is `ξ`-invariant. -/
theorem map_commutator_self (h : IsSuzuki2Grp P) {D : Subgroup P}
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    (⁅D, D⁆).map (h.xi : MulAut P).toMonoidHom = ⁅D, D⁆ := by
  rw [Subgroup.map_commutator, hDinv]

/-- `D' ≤ A` whenever `[P,P] = A` and `D ≤ P`. -/
theorem commutator_le_of_eq_top {A : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    {D : Subgroup P} :
    ⁅D, D⁆ ≤ A := by
  rw [← hGs]
  exact Subgroup.commutator_mono le_top le_top

/-- If `D' = A` (and `D ≤ P`, `[P,P] = A`, every square of `P` in `A`) then `D² = A`:
`D' ≤ D²` by `commutator_le_powSub_two`, and `D² ≤ A` because squares of `P` lie in `A`. -/
theorem powSub_two_eq_of_comm_eq (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hcd : ⁅D, D⁆ = A) : powSub D 2 = A := by
  refine le_antisymm ?_ ?_
  · rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  · rw [← hcd]
    exact commutator_le_powSub_two D


/-! ## The dichotomy for the derived subgroup of a covering, and two impossible shapes -/

/-- For a `ξ`-invariant normal `D ⊴ P` the derived subgroup `D'` is `⊥`, `A²` or `A`. -/
theorem dComm_dichotomy (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : powSub A 2 = omega1 P) (hA4 : powSub A 4 = ⊥)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    ⁅D, D⁆ = ⊥ ∨ ⁅D, D⁆ = powSub A 2 ∨ ⁅D, D⁆ = A :=
  xi_inv_sub_dichotomy h hA htop hA4 (commutator_le_of_eq_top hGs)
    (map_commutator_self h hDinv)

/-- An abelian `ξ`-invariant normal subgroup strictly containing `A` contradicts maximality. -/
theorem no_abelian_covering (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D) (hab : ⁅D, D⁆ = ⊥) : False := by
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
      rw [← hab]
      exact Subgroup.commutator_mem_commutator hx hy
    have h1 : ⁅x, y⁆ = 1 := Subgroup.mem_bot.mp hmem
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = (⁅x, y⁆ * y) * x := by rw [Work.Higman.mul_mul_inv_eq_commutator_mul]
      _ = y * x := by rw [h1, one_mul]
  exact (ne_of_lt hAD) (hmax D ⟨hDn, hDinv, hDab⟩ (le_of_lt hAD)).symm

/-- If `D' = A²` (with `D` `ξ`-invariant, squares of `P` in `A`), then `Φ(D) = D² ⊔ D'` is
`A²` or `A`: it is a `ξ`-invariant subgroup of `A` containing `A²`. -/
theorem phi_eq_powSub_two_or_self (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hDd : ⁅D, D⁆ = powSub A 2) :
    powSub D 2 ⊔ ⁅D, D⁆ = powSub A 2 ∨ powSub D 2 ⊔ ⁅D, D⁆ = A := by
  have hA2le : powSub A 2 ≤ A := powSub_le (by norm_num)
  have hPhile : powSub D 2 ⊔ ⁅D, D⁆ ≤ A := by
    refine sup_le ?_ ?_
    · rw [powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    · rw [hDd]; exact hA2le
  have hA2lePhi : powSub A 2 ≤ powSub D 2 ⊔ ⁅D, D⁆ := by
    rw [← hDd]; exact le_sup_right
  have hPhiinv : (powSub D 2 ⊔ ⁅D, D⁆).map (h.xi : MulAut P).toMonoidHom
      = powSub D 2 ⊔ ⁅D, D⁆ := by
    rw [Subgroup.map_sup, map_powSub (h.xi : MulAut P) hDinv 2, Subgroup.map_commutator, hDinv]
  exact xi_invariant_eq_powSub_two_or_self h hA hPhile hA2lePhi hPhiinv

/-! ## The main theorem -/

/-- **Higman 1963, Lemma 8, in the maximal setting.**  Let `A` be a *maximal* `ξ`-invariant
abelian normal subgroup of a Suzuki 2-group `P`, with `Ω₁(P) ≤ A`, `[P,P] = A`, every square of
`P` in `A`, `powSub A 4 = ⊥`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`.  Then we reach a contradiction:
`A = [P,P]` would be a homocyclic group of exponent `4` of order `|Ω₁(P)|²`, which is impossible
(Higman's Lemma 8: if `C' = A` for a normal `ξ`-subgroup `C` covering `A`, then `exp A ≤ 2`). -/
theorem no_square_of_maximal {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    False := by
  -- `Φ(P) ≤ A`: the commutator subgroup is `A` and every square lies in `A`.
  have hAn : A.Normal := hA.normal
  -- ## Case 1: `A` is central.
  by_cases hAZ : A ≤ Subgroup.center P
  · have hZle : Subgroup.center P ≤ A := center_le_of_maximal h hA hmax
    have hZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by rw [hGs]; exact hAZ
    -- in class two, `⁅x,y⁆² = ⁅x²,y⁆ = 1` because `x² ∈ A` is central
    have hsq1 : ∀ x y : P, ⁅x, y⁆ ^ 2 = 1 := by
      intro x y
      rw [commutator_sq_eq hZ x y]
      have hx : x ^ 2 * y = y * x ^ 2 := ((Subgroup.mem_center_iff.mp (hAZ (hsq x))) y).symm
      rw [commutatorElement_def, hx]
      group
    have hAle : A ≤ omega1 P := by
      rw [← hGs, Subgroup.commutator_le]
      intro x _ y _
      exact h.mem_omega1.mpr (hsq1 x y)
    have hAeq : A = omega1 P := le_antisymm hAle hNA
    have hcard' : Nat.card ↥A = (Nat.card ↥A) ^ 2 := by
      have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [hAeq]
      rw [← h1] at hcard
      exact hcard
    have hge : 4 ≤ Nat.card ↥A := by rw [hAeq]; exact h.omega1_card_ge_four
    have hlt : Nat.card ↥A < (Nat.card ↥A) ^ 2 := by
      have h1 : 1 < Nat.card ↥A := by omega
      calc Nat.card ↥A = Nat.card ↥A * 1 := (mul_one _).symm
        _ < Nat.card ↥A * Nat.card ↥A := Nat.mul_lt_mul_of_pos_left h1 (by omega)
        _ = (Nat.card ↥A) ^ 2 := (pow_two _).symm
    omega
  -- ## Case 2: `A` is not central.
  · -- `Z(P) ⊓ A = A²` (it is a `ξ`-invariant subgroup of `A` containing `A² = Ω₁(P)`, and it is
    -- not `A`), hence `Z(P) = Z(P) ⊓ A = A² = Ω₁(P)` because `Z(P) ≤ A` by maximality.
    have hZle : Subgroup.center P ≤ A := center_le_of_maximal h hA hmax
    have hZeq : Subgroup.center P = Work.Higman.powSub A 2 := by
      have h1 := inf_center_eq_powSub_two h hA hNA htop hA4 hAZ
      rwa [inf_eq_right.mpr hZle] at h1
    -- `A ≠ ⊤`, because `P` is not abelian while `A` is.
    have hAproper : A ≠ ⊤ := by
      intro htop'
      obtain ⟨x, y, hxy⟩ := h.noncomm
      exact hxy (hA.abelian x (by rw [htop']; trivial) y (by rw [htop']; trivial))
    -- `A² ≠ ⊥` (it is `Ω₁(P)`, of order at least `4`) and `A ≠ A²` (`|A| = |Ω₁(P)|²`).
    have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
      intro hb
      have hc : Nat.card ↥(Work.Higman.powSub A 2) = 1 := by rw [hb, Subgroup.card_bot]
      rw [htop] at hc
      have h4 := h.omega1_card_ge_four
      omega
    have hAne2 : A ≠ Work.Higman.powSub A 2 := by
      intro heq
      have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
        congrArg (fun X : Subgroup P => Nat.card ↥X) heq
      rw [htop] at hc
      have hq : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
        rw [← hcard, ← hc]
      have h4 := h.omega1_card_ge_four
      have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
      nlinarith
    -- A `ξ`-invariant normal subgroup `D > A`, minimal with these properties; then every
    -- `ξ`-invariant normal `E` with `A ≤ E ≤ D` is `A` or `D`.
    obtain ⟨D, hDn, hDinv, hADlt, hDmin⟩ := exists_minimal_covering_of_lt h hAproper
    have hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
        A ≤ E → E ≤ D → E = A ∨ E = D := by
      intro E hEn hEinv hAE hED
      rcases eq_or_ne E A with hEA | hEA
      · exact Or.inl hEA
      · exact Or.inr (hDmin E hEn hEinv (lt_of_le_of_ne hAE (Ne.symm hEA)) hED)
    have hAD : A ≤ D := le_of_lt hADlt
    have hADne : D ≠ A := ne_of_gt hADlt
    -- `A` has exponent `4`.
    have hexp : ∀ a ∈ A, a ^ 4 = 1 := by
      intro a ha
      have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub ha
      rw [hA4] at hmem
      simpa using hmem
    -- `D'` is a `ξ`-invariant subgroup of `A`, hence `⊥`, `A²` or `A`.
    rcases dComm_dichotomy h hA hGs htop hA4 hDinv with hD' | hD' | hD'
    · -- `D' = ⊥`: an abelian covering of `A`, contradicting maximality.
      exact no_abelian_covering h hA hmax hDn hDinv hADlt hD'
    · -- `D' = A²`: Higman's Lemma 8 in the case `C' = A²` (Higman's Lemma 7 in the
      -- `Φ(D) = A` sub-case, and the `L₁ × L₂ → L₃` analysis of Higman's §4 in the
      -- `Φ(D) = A²` sub-case).
      exact H8.c4_exclusion_sq h hA hmax hGs hsq hNA hA4 htop hcard hDn hDinv hAD hADne hD' hcover
    · -- `D' = A`: Higman's Lemma 8 in the case `C' = A` (Higman's Lemma 6 / Gorenstein–Thompson
      -- for the layers `L₁ = D/A`, `L₃ = Ω₁(P) = A²`).
      exact H8.c4_exclusion h hA hGs hsq hDn hDinv hAD hADne hD' hcover htop hA2ne hAne2

end Work.Higman
