import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.abelian_case
import Submission.Work.HallHigman.GLCore.restrict_or_quotient_of_coreHyp
import Submission.Work.HallHigman.GLCore.nonabelian_case
import Submission.Work.HallHigman.GLCore.isPGroup_of_min

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.HallHigman.GLCore

open scoped commutatorElement

universe u v

/-! ## Restriction of the core hypotheses to a subgroup -/

/-- The core hypotheses descend to any subgroup `R ≤ Q` which does not commute with `X`. -/
lemma glCore_coreHyp_of_le {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : CoreHyp p Q X) {R : Subgroup (Module.End K V)ˣ} (hRQ : R ≤ Q)
    (hinv : ∀ a ∈ R, X * a * X⁻¹ ∈ R) (hnc : ∃ a ∈ R, a * X ≠ X * a) : CoreHyp p R X where
  finite := by
    haveI := h.finite
    refine Finite.of_injective (fun r : R => (⟨(r : (Module.End K V)ˣ), hRQ r.2⟩ : Q)) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : Q => (z : (Module.End K V)ˣ)) hab)
  odd := h.odd.of_dvd_nat (Subgroup.card_dvd_of_le hRQ)
  cop := fun hd => h.cop (hd.trans (Subgroup.card_dvd_of_le hRQ))
  pow := h.pow
  norm := hinv
  noncomm := hnc

/-- A proper subgroup of a finite subgroup has strictly smaller cardinality. -/
lemma glCore_card_lt_card_of_lt {H : Type*} [Group H] {R S : Subgroup H} [Finite S] (h : R < S) :
    Nat.card R < Nat.card S := by
  have hle : R ≤ S := h.le
  have hinj : Function.Injective (fun y : R => (⟨(y : H), hle y.2⟩ : S)) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : S => (z : H)) hab)
  haveI : Finite R := Finite.of_injective _ hinj
  have hne : R ≠ S := ne_of_lt h
  have hex : ∃ x : H, x ∈ S ∧ x ∉ R := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hle fun y hy => hc y hy)
  obtain ⟨x, hxS, hxR⟩ := hex
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Fintype S := Fintype.ofFinite S
  have hnsurj : ¬ Function.Surjective (fun y : R => (⟨(y : H), hle y.2⟩ : S)) := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨x, hxS⟩
    have h2 : (y : H) = x := congrArg (fun z : S => (z : H)) hy
    exact hxR (by rw [← h2]; exact y.2)
  simpa [Nat.card_eq_fintype_card] using Fintype.card_lt_of_injective_not_surjective _ hinj hnsurj

/-! ## The double induction -/

/-- Auxiliary form of the GL-core statement: strong induction on `finrank K V`, inside which a
strong induction on `Nat.card Q`. -/
theorem glCore_aux (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ),
      Module.finrank K V = n → Work.HallHigman.CoreHyp p Q X →
        ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro V _ _ _ Q X hdim h
  have key : ∀ m : ℕ, ∀ (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ),
      Nat.card Q = m → Work.HallHigman.CoreHyp p Q X →
        ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 := by
    intro m
    refine Nat.strong_induction_on m (fun m ih2 => ?_)
    intro Q X hcard h
    haveI := h.finite
    intro hfail
    by_cases hred : ∃ U : Submodule K V, U ≠ ⊥ ∧ U ≠ ⊤ ∧
        (∀ a ∈ Q, ∀ v ∈ U, (a : Module.End K V) v ∈ U) ∧
        (∀ v ∈ U, (X : Module.End K V) v ∈ U)
    · -- reducible: L14 gives a counterexample of smaller dimension
      obtain ⟨U, hU0, hU1, hQU, hXU⟩ := hred
      rcases restrict_or_quotient_of_coreHyp h hQU hXU hU0 hU1 hfail with
        ⟨Q', X', hcore, hf⟩ | ⟨Q'', X'', hcore, hf⟩
      · exact ih (Module.finrank K U) (by rw [← hdim]; exact Submodule.finrank_lt hU1)
          U Q' X' rfl hcore hf
      · have hlt : Module.finrank K (V ⧸ U) < n := by
          rw [← hdim]
          have h1 : Module.finrank K (V ⧸ U) + Module.finrank K U = Module.finrank K V :=
            Submodule.finrank_quotient_add_finrank U
          have h2 : 0 < Module.finrank K U := by
            haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU0
            exact Module.finrank_pos
          omega
        exact ih (Module.finrank K (V ⧸ U)) hlt (V ⧸ U) Q'' X'' rfl hcore hf
    · -- irreducible
      haveI hnt : Nontrivial V := by
        by_contra hcon
        rw [not_nontrivial_iff_subsingleton] at hcon
        haveI := hcon
        obtain ⟨a, _, hane⟩ := h.noncomm
        exact hane (Subsingleton.elim _ _)
      have hirr : Work.HallHigman.IsIrreducibleFor
          ((fun a : (Module.End K V)ˣ => (a : Module.End K V)) '' (Q ∪ {X})) := by
        refine ⟨inferInstance, ?_⟩
        intro U hU
        by_contra hc
        push Not at hc
        exact hred ⟨U, hc.1, hc.2,
          (fun a ha v hv => by
            have hmem : (a : Module.End K V) ∈ ((fun a : (Module.End K V)ˣ =>
                (a : Module.End K V)) '' (Q ∪ {X})) := ⟨a, Or.inl ha, rfl⟩
            exact hU _ hmem hv),
          (fun v hv => by
            have hmem : (X : Module.End K V) ∈ ((fun a : (Module.End K V)ˣ =>
                (a : Module.End K V)) '' (Q ∪ {X})) := ⟨X, Or.inr rfl, rfl⟩
            exact hU _ hmem hv)⟩
      -- minimality: every proper `X`-invariant subgroup of `Q` is centralized by `X`
      have hmin : ∀ R : Subgroup (Module.End K V)ˣ, R < Q →
          (∀ a ∈ R, X * a * X⁻¹ ∈ R) → ∀ a ∈ R, a * X = X * a := by
        intro R hRQ hinv
        by_contra hc
        push Not at hc
        obtain ⟨a, haR, hane⟩ := hc
        have hR : CoreHyp p R X := glCore_coreHyp_of_le h hRQ.le hinv ⟨a, haR, hane⟩
        have hlt : Nat.card R < m := by
          rw [← hcard]
          exact glCore_card_lt_card_of_lt hRQ
        exact (ih2 (Nat.card R) hlt R X rfl hR) hfail
      by_cases hab : IsMulCommutative Q
      · exact (abelian_case h hab hirr) hfail
      · obtain ⟨q, hq, hQq⟩ := isPGroup_of_min X h.pow h.norm h.cop hmin h.noncomm
        exact (nonabelian_case h hab hirr hq hQq hmin) hfail
  exact key (Nat.card Q) Q X rfl h

/-- **L16 of the GL-core design** (the double induction, Step 3 of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): the GL-core statement over an algebraically closed field. -/
lemma glCore_algClosed {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V]
    [Module K V] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) [FiniteDimensional K V]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.HallHigman.CoreHyp p Q X) :
    ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 :=
  glCore_aux K p hp2 (Module.finrank K V) V Q X rfl h

end Work.HallHigman.GLCore
