import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.lemma9_maximal_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-!
# Higman 1963, Lemma 9 (existence form)

A Suzuki 2-group `P` (a finite non-abelian `2`-group with more than one involution admitting a
cyclic group of automorphisms `⟨ξ⟩` permuting its involutions transitively) has a `ξ`-invariant
abelian normal subgroup `A`, maximal among the `ξ`-invariant abelian normal subgroups, which
contains `Ω₁(P)`, the commutator subgroup `[P,P]` and the squares of all elements of `P`, and
which has exponent at most `4`.

This is Higman's Lemma 9 (*Suzuki 2-groups*, Illinois J. Math. **7** (1963), p. 87).  The two
halves of the argument are carried out here as `higman9_exp_four_new` and the call to
`Work.Higman.frattini_le_of_maximal`:

* **First half: `exp A | 4`.**  Take `A` maximal `ξ`-invariant abelian normal and a normal
  `ξ`-invariant `C > A` minimal with these properties (`MSA.exists_minimal_covering`).  Then `C/A`
  is a minimal `ξ`-section, `Φ(C) = C²⁅C,C⁆ ≤ A` (`MSA.phi_le_of_minimal_covering`) while
  `A² = Φ(A) ≤ Φ(C)`, so `Φ(C) ∈ {A², A}` (`xi_invariant_eq_powSub_two_or_self`).  In the first
  case Higman's **Lemma 3** (`higman_lemma3_general`) gives the bound; in the second case `⁅C,C⁆`,
  being `ξ`-invariant and contained in `A`, is a power subgroup `A ^ (2 ^ j)`
  (`homogeneous_structure`): for `j ≥ 1` Higman's **Lemma 7** (`higman_lemma7_general`) makes `C`
  abelian, contradicting maximality of `A`, and for `j = 0` Higman's **Lemma 8** in its weak form
  (`higman_lemma8_weak`, only the exponent bound `4` is needed) applies.
* **Second half: `Φ(P) ≤ A`.**  The endgame of Higman's §5, in the form proved as
  `frattini_le_of_maximal`: from `A⁴ = ⊥` one shows that `Φ(P) ≰ A` would produce a minimal cover
  `A < C ≤ A·Φ(P)` with `[C,A] = 1` and `Φ(C) ∈ {A², A}`, both sub-cases being contradictory.

The mathematical content of the three case lemmas and of the endgame is formalised in
`Submission/Work/Higman/lemma9_maximal_abelian.lean` (which also packages the two halves into
`Work.Higman.lemma9_maximal_abelian`, the unpacked form of the present statement).  All the
declarations used here are axiom-clean: `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.
-/

/-- **Higman 1963, Lemma 9, first half.**  A maximal `ξ`-invariant abelian normal subgroup `A` of
a Suzuki 2-group `P` has exponent at most `4`. -/
theorem higman9_exp_four_new {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  classical
  -- `A` is proper, since `P` is not abelian.
  have hAne : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hA.abelian x (htop ▸ Subgroup.mem_top x) y (htop ▸ Subgroup.mem_top y))
  -- a normal `ξ`-invariant subgroup `C > A`, minimal with these properties.
  obtain ⟨C, hCn, hCinv, hAC, -, hCA, hcover⟩ :=
    MSA.exists_minimal_covering h (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hAne.symm
  -- the Frattini subgroup of the cover lies in `A`
  have hPhi_le : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ ≤ A :=
    MSA.phi_le_of_minimal_covering h hA.normal hA.map_eq hCn hCinv hAC (Ne.symm hCA) hcover
  -- `A ^ (2) = Φ(A) ≤ Φ(C)`
  have hA2le : Work.Higman.powSub A 2 ≤ Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ :=
    (Work.Higman.powSub_mono (n := 2) hAC).trans le_sup_left
  -- `Φ(C)` is `ξ`-invariant
  have hPhi_inv : (Work.Higman.powSub C 2 ⊔ ⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ := by
    rw [Subgroup.map_sup, Work.Higman.map_powSub (h.xi : MulAut P) hCinv 2,
      Subgroup.map_commutator, hCinv]
  rcases Work.Higman.xi_invariant_eq_powSub_two_or_self h hA hPhi_le hA2le hPhi_inv with
    hPhi | hPhi
  · -- `Φ(C) = A²`: Higman's Lemma 3
    exact higman_lemma3_general h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi
  · -- `Φ(C) = A`
    have hC2 : Work.Higman.powSub C 2 ≤ A := le_sup_left.trans (le_of_eq hPhi)
    have hCd_le : ⁅C, C⁆ ≤ A := le_sup_right.trans (le_of_eq hPhi)
    have hCd_inv : (⁅C, C⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨e, -, -, -, hsub⟩ := Work.Higman.homogeneous_structure h hA.abelian hA.map_eq
    obtain ⟨j, hj⟩ := hsub ⁅C, C⁆ hCd_le hCd_inv
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- `C' = A`: Higman's Lemma 8, weak form (`exp A | 4`)
      have hCd_eq : ⁅C, C⁆ = A := by
        rw [hj, h0, pow_zero, Work.Higman.powSub_one_eq]
      have h4 : Work.Higman.powSub A 4 = ⊥ :=
        higman_lemma8_weak h hA hCn hCinv hAC (Ne.symm hCA) hcover hC2 hCd_eq
      intro a ha
      have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub (n := 4) ha
      rw [h4] at hmem
      simpa using hmem
    · -- `C' ≤ A²`: Higman's Lemma 7 makes `C` abelian, contradicting maximality of `A`
      have hCd2 : ⁅C, C⁆ ≤ Work.Higman.powSub A 2 := by
        rw [hj]
        exact Work.Higman.powSub_le_of_dvd hA.abelian (Nat.pow_dvd_pow 2 hpos)
      have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        higman_lemma7_general h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi hCd2
      exact absurd (hmax C ⟨hCn, hCinv, hcomm⟩ hAC) hCA

/-- **Higman 1963, Lemma 9 (existence form).**  A Suzuki 2-group has a `ξ`-invariant abelian
normal subgroup `A`, maximal among the `ξ`-invariant abelian normal subgroups, which contains
`Ω₁(P)`, the commutator subgroup `[P,P]` and the squares of all elements of `P`, and which has
exponent at most `4`. -/
theorem higman9_exists_new {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ A : Subgroup P, Work.Higman.IsXiAbelNormal h A ∧
      (∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A) ∧
      Work.Higman.omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A ∧
      (∀ x : P, x ^ 2 ∈ A) ∧ (∀ a ∈ A, a ^ 4 = 1) := by
  classical
  obtain ⟨A, hA, hmax⟩ := Work.Higman.exists_maximal_isXiAbelNormal h
  -- first half: `exp A | 4`
  have hexp : ∀ a ∈ A, a ^ 4 = 1 := higman9_exp_four_new h hA hmax
  have hA4 : Work.Higman.powSub A 4 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := (Work.Higman.mem_powSub_iff hA.abelian).mp hy
    exact hexp x hxA
  -- second half: `Φ(P) = P²⁅P,P⁆ ≤ A`
  have hPhi : Work.Higman.powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
    frattini_le_of_maximal h hA hmax hA4
  exact ⟨A, hA, hmax, Work.Higman.omega1_le_of_maximal h hA hmax,
    le_trans le_sup_right hPhi,
    fun x => le_trans le_sup_left hPhi
      (Work.Higman.pow_mem_powSub (Subgroup.mem_top x)),
    hexp⟩

end Work.Higman
