/-
Area A11 (p-stability) of the Feit--Thompson drive: the quadratic GL-core over an algebraically
closed field, by the same double induction (on `dim V`, then on `|𝒬|`) as the odd-order GL-core
of area A10 (`Work.HallHigman.GLCore.glCore_algClosed`).
-/
import Mathlib
import Submission.Work.PStable.Quad.Defs
import Submission.Work.PStable.Quad.abelian_case_quad
import Submission.Work.PStable.Quad.nonabelian_case_quad
import Submission.Work.PStable.Quad.restrict_or_quotient_of_quadCore
import Submission.Work.HallHigman.GLCore.isPGroup_of_min
import Submission.Work.HallHigman.GLCore.glCore_algClosed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PStable.Quad

universe u v

/-- The double induction of the quadratic GL-core. -/
theorem glCore_quad_aux (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ),
      Module.finrank K V = n → QuadCore p Q X → ((X : Module.End K V) - 1) ^ 2 ≠ 0 := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro V _ _ _ Q X hdim h
  have key : ∀ m : ℕ, ∀ (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ),
      Nat.card Q = m → QuadCore p Q X → ((X : Module.End K V) - 1) ^ 2 ≠ 0 := by
    intro m
    refine Nat.strong_induction_on m (fun m ih2 => ?_)
    intro Q X hcard h
    haveI := h.finite
    intro hfail
    by_cases hred : ∃ U : Submodule K V, U ≠ ⊥ ∧ U ≠ ⊤ ∧
        (∀ a ∈ Q, ∀ v ∈ U, (a : Module.End K V) v ∈ U) ∧
        (∀ v ∈ U, (X : Module.End K V) v ∈ U)
    · -- reducible: a counterexample of smaller dimension is inherited
      obtain ⟨U, hU0, hU1, hQU, hXU⟩ := hred
      rcases restrict_or_quotient_of_quadCore h hQU hXU hU0 hU1 hfail with
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
      -- minimality
      have hmin : ∀ R : Subgroup (Module.End K V)ˣ, R < Q →
          (∀ a ∈ R, X * a * X⁻¹ ∈ R) → ∀ a ∈ R, a * X = X * a := by
        intro R hRQ hinv
        by_contra hc
        push Not at hc
        obtain ⟨a, haR, hane⟩ := hc
        -- the core hypothesis descends to `R`
        have hR : QuadCore p R X := by
          refine ⟨?_, ?_, ?_, ?_, ⟨a, haR, hane⟩, ?_⟩
          · haveI := h.finite
            exact Finite.of_injective
              (fun r : R => (⟨(r : (Module.End K V)ˣ), hRQ.le r.2⟩ : Q)) (by
                intro x y hxy
                exact Subtype.ext (congrArg (fun z : Q => (z : (Module.End K V)ˣ)) hxy))
          · exact fun hd => h.cop (hd.trans (Subgroup.card_dvd_of_le hRQ.le))
          · exact h.pow
          · exact hinv
          · rcases h.two with h5 | h2
            · exact Or.inl h5
            · exact Or.inr (two_of_subgroup_le hRQ.le h2)
        have hlt : Nat.card R < m := by
          rw [← hcard]
          exact Work.HallHigman.GLCore.glCore_card_lt_card_of_lt hRQ
        exact (ih2 (Nat.card R) hlt R X rfl hR) hfail
      by_cases hab : IsMulCommutative Q
      · exact (abelian_case_quad hp2 h hab hirr) hfail
      · obtain ⟨q, hq, hQq⟩ :=
          Work.HallHigman.GLCore.isPGroup_of_min X h.pow h.norm h.cop hmin h.noncomm
        exact (nonabelian_case_quad hp2 h hab hirr hq hQq hmin) hfail
  exact key (Nat.card Q) Q X rfl h

/-- The quadratic GL-core over an algebraically closed field of characteristic `p ≠ 2`. -/
theorem glCore_quad_algClosed {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V]
    [Module K V] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) [FiniteDimensional K V]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ} (h : QuadCore p Q X) :
    ((X : Module.End K V) - 1) ^ 2 ≠ 0 :=
  glCore_quad_aux K p hp2 (Module.finrank K V) V Q X rfl h

end Work.PStable.Quad
