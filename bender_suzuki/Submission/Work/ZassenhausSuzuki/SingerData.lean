import Mathlib
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Lemma5Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer-cycle data of Suzuki 1962 §8

In Suzuki's proof of Theorem 1, `X = G₀ = ⟨Q₀, K, τ⟩ = ⟨Q0sub H, Kset H t, t⟩` is isomorphic to
`LF(2,q)` and contains a **cyclic** subgroup `V` of order `q + 1` whose normaliser (in `G₀`) is
dihedral of order `2(q+1)`.  This module records the *interface* used by the two hard steps of
the crux `Work.ZassenhausSuzuki.QSZ_abelian_of_order_three`:

* `SingerCycle.Data` — the bundle of facts about `V` inside `X5 H t` that the model side
  (`SingerModelCycle.singer_cycle_model` + the transport) produces;
* the two consumers of this bundle, `Work.ZassenhausSuzuki.strongly_real_conj_structure`
  (Suzuki's Proposition 13 + the element structure of `LF(2,q)`) and
  `Work.ZassenhausSuzuki.singer_selfcentralizing` (Suzuki §8, pp. 117–118), are stated in
  separate modules against this interface.

`q` is written `Nat.card ↥(Work.ThmF.Q0sub H)` throughout, and `q + 1 = Nat.card ↥V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

namespace SingerCycle

/-- The Singer-cycle data inside `X5 H t` (Suzuki's `G₀ ≅ LF(2,q)`): a cyclic subgroup `V` of
order `q + 1` (`q = |Q0sub H|`), self-centralising in `X5 H t`, with normaliser in `X5 H t` of
order `2(q+1)`, inverted by an involution of `X5 H t`, and consisting of strongly real elements.

These are exactly the clauses that `SingerModelCycle.singer_cycle_model` provides in
`PSL2Model n` and that `singer_cycle_transport_full` then transports to `↥(X5 H t)`; the
inclusion `V ≤ X5 H t` and the ambient-group form of the statements are recorded here. -/
structure Data (G : Type) [Group G] (H : Subgroup G) (t : G) where
  /-- The Singer cycle `V`. -/
  V : Subgroup G
  /-- `V` lies in `X5 H t = ⟨Q₀, K, t⟩`. -/
  le_X5 : (V : Set G) ⊆ Work.ThmF.Lemma5.X5 H t
  /-- `V` is cyclic. -/
  cyclic : IsCyclic ↥V
  /-- `|V| = q + 1`, `q = |Q0sub H|`. -/
  card_V : Nat.card ↥V = Nat.card ↥(Work.ThmF.Q0sub H) + 1
  /-- `C_{X5}(V) = V`. -/
  centralizer_in_X5 : ∀ x : G, x ∈ Work.ThmF.Lemma5.X5 H t →
    (∀ v ∈ V, x * v = v * x) → x ∈ V
  /-- `|N_{X5}(V)| = 2(q+1)` (`N_X5(V)` is dihedral). -/
  normalizer_in_X5 : Nat.card ↥(Subgroup.normalizer (V : Set G) ⊓ Work.ThmF.Lemma5.X5 H t) =
    2 * (Nat.card ↥(Work.ThmF.Q0sub H) + 1)
  /-- An involution of `X5 H t` inverting `V`. -/
  inverting : ∃ τ : G, τ ∈ Work.ThmF.Lemma5.X5 H t ∧ τ * τ = 1 ∧
    ∀ v ∈ V, τ * v * τ = v⁻¹
  /-- Every element of `V` is strongly real (a product of two involutions). -/
  stronglyReal : ∀ v ∈ V, ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = v

namespace Data

variable {G : Type} [Group G] {H : Subgroup G} {t : G} (S : Data G H t)

/-- `V ≤ X5 H t`. -/
theorem V_le_X5 : S.V ≤ Work.ThmF.Lemma5.X5 H t := S.le_X5

/-- `V` is nontrivial: `|V| = q + 1` and `q ≥ 1`. -/
theorem one_lt_card_V (hq : 1 ≤ Nat.card ↥(Work.ThmF.Q0sub H)) : 1 < Nat.card ↥S.V := by
  rw [S.card_V]; omega

/-- The inverting involution, in the form `τ v τ⁻¹ = v⁻¹`. -/
theorem inverting' : ∃ τ : G, τ ∈ Work.ThmF.Lemma5.X5 H t ∧ τ * τ = 1 ∧
    ∀ v ∈ S.V, τ * v * τ⁻¹ = v⁻¹ := by
  obtain ⟨τ, hτX5, hτ2, hτinv⟩ := S.inverting
  exact ⟨τ, hτX5, hτ2, fun v hv => by rw [inv_eq_of_mul_eq_one_right hτ2]; exact hτinv v hv⟩

end Data

end SingerCycle

end Work.ZassenhausSuzuki
