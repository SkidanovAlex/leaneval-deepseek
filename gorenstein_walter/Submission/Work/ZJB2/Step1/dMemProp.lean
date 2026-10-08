import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB.ZJApi.ZJ_ne_bot

/-!
# ZJB2, step (I), leaf I.5: `D ∈ 𝓗`

This file proves `Work.ZJB.DMemProp p G`, the leaf **I.5** of step (I) of Glauberman's
Theorem 5.1(a) (Glauberman 1968, p. 1118).  In the notation of
`Submission/Work/ZJB/Step1/Defs.lean`,

* `D = Dsub S S₁ = N_G(J(S)) ∩ S₁` is the intersection of `S₁` with the normalizer of
  Thompson's subgroup `J(S)`,
* `InScrH p S D a H` is membership of `H` in the set `𝓗` of p. 1118.

The statement is: for a "bad" Sylow subgroup `S₁` (in the sense of `MaxBad`) with
`Z(S₁) ≤ D` and an element `a ∈ N_G(D) ∩ S₁`, together with a Sylow `p`-subgroup `T₁` of
`N_G(D)` containing `D` and satisfying `|D| < |N_G(J(S)) ∩ T₁|`, the subgroup `D` itself is a
member of `𝓗` (with the witnesses `T₁`, `g = a`, `S₂ = S₁`).

The proof is a matter of checking the three clauses of `InScrH`:

* `D ≠ 1` because `Z(S) ≤ D` (as `Z(S) ≤ Z(J(S)) ≤ N_G(J(S))` and `Z(S) ≤ S₁`) and `Z(S) ≠ 1`
  for `S ≠ 1` (`Work.ZJB.ZJApi.centralizer_inf_ne_bot_of_isPGroup`);
* the witnesses `T = T₁` and `g = a` work: `Z(S) ≤ D ≤ T₁`, and `Z(S)^a ≤ T₁` because
  `a ∈ N_G(D)` normalises `D ⊇ Z(S)`;
* `S₂ = S₁` works because `Z(S₁) ≤ D` is a hypothesis and `D ≤ S₁` by construction.
-/

namespace Work.ZJB2.Step1

open Subgroup
open Work.ZJB

/-- `Z(P) ≤ N_G(J(P))`: `Z(P)` centralises `P ⊇ J(P)`, hence normalises `J(P)`. -/
theorem ZS_le_normalizer_thompsonJ {G : Type*} [Group G] (P : Subgroup G) :
    ZS P ≤ Subgroup.normalizer (Work.GW2.thompsonJ P : Set G) := by
  rw [ZS]
  exact (inf_le_left.trans (Subgroup.centralizer_le (Work.GW2.thompsonJ_le P))).trans
    (Subgroup.centralizer_le_normalizer (Work.GW2.thompsonJ P : Set G))

/-- **I.5.** `D = N_G(J(S)) ∩ S₁` is a member of `𝓗`. -/
theorem dMemProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.DMemProp p G := by
  intro S S₁ hS hbad hZ a ha T₁ hT₁ hDT hcard
  -- `Z(S) ≤ S₁` is part of badness, and `Z(S) ≤ N_G(J(S))` always.
  have hZS_S1 : ZS (S : Subgroup G) ≤ S₁ := hbad.1
  have hZnJ : ZS (S : Subgroup G) ≤
      Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) :=
    ZS_le_normalizer_thompsonJ (S : Subgroup G)
  have hZD : ZS (S : Subgroup G) ≤ Dsub S S₁ := le_inf hZnJ hZS_S1
  -- `D ≠ 1` because `1 ≠ Z(S) ≤ D`.
  have hZne : ZS (S : Subgroup G) ≠ ⊥ :=
    Work.ZJB.ZJApi.centralizer_inf_ne_bot_of_isPGroup (p := p) S.isPGroup' hS
  have hDne : Dsub S S₁ ≠ ⊥ := by
    intro hbot
    exact hZne (le_bot_iff.mp (hbot ▸ hZD))
  -- `a ∈ N_G(D)` normalises `D ⊇ Z(S)`, hence `Z(S)^a ≤ T₁`.
  have haN : a ∈ Subgroup.normalizer (Dsub S S₁ : Set G) := ha.1
  have haNinva : a⁻¹ ∈ Subgroup.normalizer (Dsub S S₁ : Set G) :=
    (Subgroup.normalizer (Dsub S S₁ : Set G)).inv_mem haN
  have hmapD : pconj (Dsub S S₁) a = Dsub S S₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haNinva
  have hpconj : pconj (ZS (S : Subgroup G)) a ≤ T₁ := by
    have h1 : pconj (ZS (S : Subgroup G)) a ≤ pconj (Dsub S S₁) a := pconj_mono hZD a
    rw [hmapD] at h1
    exact h1.trans hDT
  -- Assemble the three clauses of `InScrH p S (Dsub S S₁) a (Dsub S S₁)`.
  refine ⟨hDne, ?_, ⟨S₁, hZ, inf_le_right⟩⟩
  exact ⟨T₁, a, haN, hT₁, hZD.trans hDT, rfl, hpconj, hcard⟩

end Work.ZJB2.Step1
