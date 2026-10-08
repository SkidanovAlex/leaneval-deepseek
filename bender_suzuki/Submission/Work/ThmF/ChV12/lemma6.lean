import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L6faith
import Submission.Work.ThmF.ChV12.L6setup
import Submission.Work.ThmF.ChV12.W_semireg
import Submission.Work.ThmF.ChV12.W_card_dvd
import Submission.Work.ThmF.ChV12.W_isCyclic
import Submission.Work.ThmF.ChV12.gl2_isCyclic_of_odd_no_eigen

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma6` — Peterfalvi II, Ch. V §2, Lemma 6 (p. 246)

Suppose `st` has order `3` and `Q` is a Suzuki 2-group of order `q³`, `q = |Q0sub H|`.
Then `W = C_V(K)` is cyclic and `|W|` divides `q + 1`.

The proof is assembled from four independent pieces (each proved in its own module):

* `Work.ThmF.ChV12.W_semireg` — `W` acts fixed-point-freely on `Q ∖ Q0sub H`;
* `Work.ThmF.ChV12.W_card_dvd` — hence `|W| ∣ q + 1` (fibres of the squaring map `Q → Q0sub H`);
* `Work.ThmF.ChV12.gl2_isCyclic_of_odd_no_eigen` — an odd-order subgroup of `GL₂` with no
  eigenvalue in the base field is cyclic ([H] II §8, quoted by the source);
* `Work.ThmF.ChV12.W_isCyclic` — `W` is cyclic: the semiregularity makes `Q` of type `B`
  (Higman), so `Q/Z(Q)` is a two-dimensional `𝔽_q`-space on which `W` acts without eigenvalue,
  and the `GL₂` lemma applies.

When `W = ⊥` the claim is trivial.
-/

set_option autoImplicit false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs

theorem lemma6 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q) (hcard : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3) : IsCyclic ↥(Work.ThmF.W H t) ∧ Nat.card ↥(Work.ThmF.W H t) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 := by
  classical
  by_cases hW : Work.ThmF.W H t = ⊥
  · rw [hW]
    exact ⟨inferInstance, by simp⟩
  · have hsemi : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
        x ∈ Work.ThmF.Q0sub H :=
      W_semireg hC4 hHig h hSuz hcard
    have hdvd : Nat.card ↥(Work.ThmF.W H t) ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 :=
      W_card_dvd hC4 hHig h hSuz hcard hsemi
    have hgl2 : ∀ {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
        [FiniteDimensional F V], Module.finrank F V = 2 → (A : Subgroup (V ≃ₗ[F] V)) →
        Odd (Nat.card ↥A) →
        (∀ a ∈ A, a ≠ 1 → ∀ (c : F) (v : V), v ≠ 0 → (a : V ≃ₗ[F] V) v ≠ c • v) →
        IsCyclic ↥A :=
      fun h2 A hodd hno => gl2_isCyclic_of_odd_no_eigen h2 A hodd hno
    exact ⟨W_isCyclic hC4 hHig h hSuz hcard hsemi hdvd hgl2, hdvd⟩

end Work.ThmF.ChV12
