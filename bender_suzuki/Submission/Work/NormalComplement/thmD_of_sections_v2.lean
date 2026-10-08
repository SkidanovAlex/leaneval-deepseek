import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.thmD_of_sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Theorem D** assembled from the *faithful* decomposition of Ch. III §2–§5.

Same construction as `Work.NormalComplement.thmD_of_sections` (import it for the helper lemmas
`exists_involution_not_mem` and the minimality set-up, and for the derivation of `IsD1` from
`hS2`, `hTrans`, `hPab`, `hStrat`), with the final step replaced by the case split on `IsD2`:

1. `t ∉ H` an involution, `D := twoPoint H t`, `W` minimal in `S = {W' | W' ≤ H, H ≤ N_G(W'),
   W' ⊔ D = H}`.
2. If `W ⊓ D = ⊥` then `Q := W` is the desired normal complement.
3. Otherwise `E := W ⊓ D ≠ ⊥` is odd hence solvable, and the prime-by-prime argument gives
   `IsD1 H t W` (for every prime `q | [E:E']`, `hS2` gives `q`-control, contradicting minimality of
   `W` via `hTrans` and `hStrat`, or the Sylow datum).
4. `by_cases h : IsD2 H t W`: if `h` holds, `hS45` (with the minimality witness of `W`) gives
   `False`, hence the goal; otherwise `hS3` gives `HasNormalComplementIn D H`, i.e. the
   conclusion of `ThmDProp` with `H` and `D` (note `D = twoPoint H t` here, so the existentially
   quantified `t` of `ThmDProp` is the one built in step 1). -/
theorem thmD_of_sections_v2 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hTrans : Work.NormalComplement.TransferProp) (hStrat : Work.NormalComplement.StrategyProp)
    (hPab : Work.NormalComplement.PrimesOfAbelianizationProp)
    (hX : Work.NormalComplement.AppXProp) (hS2 : Work.NormalComplement.Section2Prop) (hS3 : Work.NormalComplement.Section3Prop)
    (hS45 : Work.NormalComplement.Section45Prop) : Submission.Blueprint.ThmDProp := by
  classical
  intro G _ _ hSit H hH
  -- Step 1: an involution `t ∉ H`.
  obtain ⟨t, ht2, htH⟩ := exists_involution_not_mem G hH
  -- Step 2: `D = twoPoint H t` has odd order.
  have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
  -- The family of admissible subgroups, and a minimal member.
  let S : Set (Subgroup G) :=
    {W | W ≤ H ∧ H ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ twoPoint H t = H}
  have hSH : H ∈ S := ⟨le_rfl, Subgroup.le_normalizer, by rw [sup_eq_left]; exact inf_le_left⟩
  have hex : ∃ k : ℕ, ∃ W : Subgroup G, W ∈ S ∧ Nat.card W = k := ⟨_, H, hSH, rfl⟩
  obtain ⟨W, hWS, hWval⟩ : ∃ W : Subgroup G, W ∈ S ∧ Nat.card W = Nat.find hex :=
    Nat.find_spec hex
  have hWmin : ∀ W' ∈ S, Nat.card W ≤ Nat.card W' := by
    intro W' hW'
    rw [hWval]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  -- The minimality witness in the form consumed by `Section45Prop`.
  have hWminIn : IsMinimalIn H (twoPoint H t) W :=
    ⟨hWS.1, hWS.2.1, hWS.2.2, fun W' h1 h2 h3 => hWmin W' ⟨h1, h2, h3⟩⟩
  by_cases hWD : W ⊓ twoPoint H t = ⊥
  · -- Step 3a: `Q := W` is the desired normal complement.
    exact ⟨t, ht2, htH, W, hWS.1, hWS.2.1, hWD, hWS.2.2⟩
  · -- Step 3b: `E = W ⊓ D ≠ ⊥`; the prime-by-prime argument gives `IsD1 H t W`.
    let E : Subgroup G := W ⊓ twoPoint H t
    have hEne : E ≠ ⊥ := hWD
    have hEodd : Odd (Nat.card ↥E) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le (show E ≤ twoPoint H t from inf_le_right))
    have hEsol : Group.IsSolvable ↥E := hFT ↥E hEodd
    have hElt : ⁅E, E⁆ < E := commutator_lt_of_isSolvable hEne hEsol
    have hIsD1 : IsD1 H t W := by
      intro p hp hpdvd
      haveI : Fact p.Prime := ⟨hp⟩
      have hpcard : p ∣ Nat.card ↥(W ⊓ twoPoint H t) :=
        dvd_trans hpdvd
          (Subgroup.relIndex_dvd_card ⁅W ⊓ twoPoint H t, W ⊓ twoPoint H t⁆
            (W ⊓ twoPoint H t))
      rcases hS2 G hSit H hH t ht2 htH W hWS.1 hWS.2.1 hWS.2.2 (hX G hSit H hH t ht2 htH) p hp hpcard with hA | hB
      · exfalso
        obtain ⟨y, hyE, hyE', hyord⟩ := hPab G E hEne hEsol p hp hpdvd
        have hy1 : y ≠ 1 := by
          rintro rfl
          exact hyE' (Subgroup.one_mem _)
        have hyW : y ∈ W := hA.1 hyE
        have hyres : y ∉ Work.Grun.pResidual p W := hTrans G hA hyE hy1 hyord hyE' hpdvd
        obtain ⟨W₁, hlt, hW₁H, hHn₁, hW₁D⟩ :=
          hStrat G hA.1 inf_le_right hA.2.1 hWS.1 hWS.2.1 hWS.2.2 hyW hyres
        exact (not_lt.mpr (hWmin W₁ ⟨hW₁H, hHn₁, hW₁D⟩)) (Subgroup.card_lt_of_lt hlt)
      · exact hB
    -- Step 4: case split on `IsD2`.
    by_cases hD2 : IsD2 H t W
    · -- (D2) is contradictory by §4–§5, with the minimality witness of `W`.
      exact (hS45 G hSit H hH t ht2 htH W hWminIn hWD hIsD1 hD2).elim
    · -- `¬ IsD2`: §3 gives the normal complement of `D = twoPoint H t` in `H`.
      obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := hS3 G hSit H hH t ht2 htH W hWS.1 hWS.2.1 hWS.2.2 hIsD1 hD2
      exact ⟨t, ht2, htH, Q, hQ1, hQ2, hQ3, hQ4⟩

end Work.NormalComplement
