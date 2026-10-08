import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A normal subgroup of exponent `p` and order `≥ p ^ 2` inside a `p`-group contains a
normal elementary abelian subgroup of order `p ^ 2`

`Work.PGroup.exists_elementaryAbelian_card_prime_sq_of_exponent_pp`: let `X` be a finite
`p`-group, `V ⊴ X` a normal subgroup with `v ^ p = 1` for all `v ∈ V`, and `|V| ≥ p ^ 2`.
Then `X` has a **normal** subgroup `W ≤ V` which is elementary abelian of order `p ^ 2`.

The proof is a "central series" argument.  Since `X` is a finite `p`-group it is nilpotent, so
its upper central series `Z 0 = ⊥ ≤ Z 1 ≤ … ≤ Z m = ⊤` reaches the top.  Let `i` be the least
index with `p ^ 2 ≤ |V ∩ Z (i+1)|`; put `A = V ∩ Z i` and `B = V ∩ Z (i+1)`.  Then
`|A| < p ^ 2` (so, `A` being a `p`-group, `|A| ∣ p ^ 2`) while `|B| ≥ p ^ 2` (so, `B` being a
`p`-group, `p ^ 2 ∣ |B|`).  Sylow's first theorem therefore produces `A ≤ K ≤ B` with
`|K| = p ^ 2`.  Finally `K` is normal in `X`: for `n ∈ B` and `x ∈ X` the commutator
`⁅n, x⁆` lies in `Z i` (because `n ∈ Z (i+1)`) and in `V` (because `V ⊴ X`), hence in `A ≤ K`,
so that `x * n * x⁻¹ = ⁅n, x⁆⁻¹ * n ∈ K`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup

theorem exists_elementaryAbelian_card_prime_sq_of_exponent_pp {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hX : IsPGroup p X) {V : Subgroup X} (hVnorm : V.Normal)
    (hexp : ∀ v : V, v ^ p = 1) (hcard : p ^ 2 ≤ Nat.card V) :
    ∃ W : Subgroup X, W ≤ V ∧ W.Normal ∧ Work.PGroup.IsElementaryAbelian p W ∧
      Nat.card W = p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : V.Normal := hVnorm
  -- `X` is nilpotent, so its upper central series reaches the whole group
  haveI : Group.IsNilpotent X := hX.isNilpotent
  obtain ⟨m, hm⟩ := Group.IsNilpotent.nilpotent X
  let Z : ℕ → Subgroup X := Subgroup.upperCentralSeries X
  have hZmono : Monotone Z := Subgroup.upperCentralSeries_mono X
  have hZ0 : Z 0 = ⊥ := Subgroup.upperCentralSeries_zero X
  have hmZ : Z m = ⊤ := hm
  -- a level whose `V`-part already has cardinality at least `p ^ 2`
  have hex : ∃ n : ℕ, p ^ 2 ≤ Nat.card ↥(V ⊓ Z (n + 1)) := by
    refine ⟨m, ?_⟩
    have htop : Z (m + 1) = ⊤ :=
      le_antisymm le_top (hmZ ▸ hZmono (Nat.le_succ m))
    rw [htop, inf_top_eq]
    exact hcard
  -- the least such level
  obtain ⟨i, hi, hprev⟩ : ∃ i : ℕ, (p ^ 2 ≤ Nat.card ↥(V ⊓ Z (i + 1))) ∧
      (∀ j < i, ¬ (p ^ 2 ≤ Nat.card ↥(V ⊓ Z (j + 1)))) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hAlt : Nat.card ↥(V ⊓ Z i) < p ^ 2 := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, hZ0, inf_bot_eq, Subgroup.card_bot]
      exact one_lt_pow₀ hp.one_lt (by norm_num)
    · have h := hprev (i - 1) (by omega)
      rw [Nat.sub_add_cancel hpos] at h
      exact not_le.mp h
  have hABle : (V ⊓ Z i) ≤ (V ⊓ Z (i + 1)) :=
    le_inf inf_le_left (le_trans inf_le_right (hZmono (Nat.le_succ i)))
  -- both levels are `p`-groups
  obtain ⟨kA, hkA⟩ : ∃ k, Nat.card ↥(V ⊓ Z i) = p ^ k :=
    IsPGroup.exists_card_eq (hX.to_subgroup (V ⊓ Z i))
  obtain ⟨kB, hkB⟩ : ∃ k, Nat.card ↥(V ⊓ Z (i + 1)) = p ^ k :=
    IsPGroup.exists_card_eq (hX.to_subgroup (V ⊓ Z (i + 1)))
  have hlt : p ^ kA < p ^ 2 := by rw [← hkA]; exact hAlt
  have hle : p ^ 2 ≤ p ^ kB := by rw [← hkB]; exact hi
  have hdvdA : Nat.card ↥(V ⊓ Z i) ∣ p ^ 2 := by
    rw [hkA]
    exact pow_dvd_pow p (le_of_lt ((Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt))
  have hdvdB : p ^ 2 ∣ Nat.card ↥(V ⊓ Z (i + 1)) := by
    rw [hkB]
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp hle)
  -- Sylow: a subgroup of order `p ^ 2` sandwiched between the two levels
  obtain ⟨K, hKcard, hAK, hKB⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (n := 2) hp hdvdA hdvdB hABle
  have hKV : K ≤ V := le_trans hKB inf_le_left
  -- `K` is normal in `X`
  have hKnorm : K.Normal := by
    refine Subgroup.Normal.mk (fun n hn x => ?_)
    have hnB : n ∈ V ⊓ Z (i + 1) := hKB hn
    obtain ⟨hnV, hnZ⟩ := Subgroup.mem_inf.mp hnB
    have h1 : ⁅n, x⁆ ∈ Z i := (Subgroup.mem_upperCentralSeries_succ_iff).mp hnZ x
    have h2 : ⁅n, x⁆ ∈ V :=
      commutator_le_left V ⊤ (commutator_mem_commutator hnV (Subgroup.mem_top x))
    have ha : ⁅n, x⁆⁻¹ ∈ V ⊓ Z i :=
      Subgroup.mem_inf.mpr ⟨V.inv_mem h2, (Z i).inv_mem h1⟩
    have heq : x * n * x⁻¹ = ⁅n, x⁆⁻¹ * n := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact K.mul_mem (hAK ha) hn
  refine ⟨K, hKV, hKnorm, ?_, hKcard⟩
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hKcard, fun k => ?_⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val (hexp ⟨(k : X), hKV k.2⟩)

end Work.PGroup
