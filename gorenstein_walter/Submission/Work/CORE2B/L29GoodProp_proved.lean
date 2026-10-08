import Mathlib
import Submission.Work.CORE2B.L29Parts
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L29_tower
import Submission.Work.CORE2B.L29_case_i_good

namespace Work.CORE2B

open Subgroup

/-- **Faithfulness against `t`.**  If the Klein four-group `V` acts faithfully on `A` and
`t ∈ V#`, then `t ∉ C_G(A)`: `t ∈ C_G(A)` means `A ≤ C_G(t)`, contradicting `Faithful V A` at
`v = t ≠ 1`.  (Subgroup of `L29_case_i_good.lean`, kept here so that the leaf below needs only
`import`.) -/
theorem not_mem_centralizer_of_faithful {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (V A : Subgroup G) (htV : B.t ∈ V)
    (hFaith : C15.Faithful V A) : B.t ∉ Subgroup.centralizer (A : Set G) := by
  intro hmem
  have ht1 : B.t ≠ 1 := by
    intro h
    have hord := B.t_order
    rw [h, orderOf_one] at hord
    norm_num at hord
  refine hFaith B.t htV ht1 ?_
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hmem a ha

-- Leaf P2 of the lead's design pass 15 (Lemma 2.9): the printed last sentence, with `u = t`.
-- Route, with `X := [⟨s⟩, C_A(t)]`:
-- 1. `X ≤ C_A(t) ≤ H` (`s` normalizes `C_A(t)` since `s ∈ V ≤ N(A)` and `st = ts`), `X` is odd;
--    `H = U·S` (`T.split`, `S` dihedral as it contains the four-group `V`), so `H/U` is a 2-group
--    and the odd `X` lies in `U`; `⁅⟨s⟩, X⁆ = X` by `T.c11i`; so the `hyp` hypothesis gives
--    `t ∈ O₂(N_G(X))`.
-- 2. `t` normalizes `A` and `X` (it centralizes `X`), hence normalizes `N_A(X)`; for `y ∈ N_A(X)`,
--    `[y,t] ∈ N_A(X) ⊓ O₂(N_G(X)) = ⊥` (odd ∩ 2-group), so `N_G(X) ⊓ A ≤ C(t)`.
-- 3. `Work.CORE2B.L29_tower` (proved, in `CORE2B/L29_tower`) gives `A ≤ C(t)`, contradicting
--    faithfulness at `t ≠ 1`.
/-- **Leaf P2 of the lead's design pass 15 (Bender 1981, Lemma 2.9, p. 222).**  The printed last
sentence with `u = t`: a faithful four-group `V ∋ t` with a witness `s ∈ V` such that
`[⟨s⟩, C_A(t)] ≠ ⊥` is impossible.

Steps 1–3 of the route above are formalised in `L29_case_i_good.lean` as
`L29_case_i_good_general`, the same statement with `hAcen : t ∉ C_G(A)` in place of
`Faithful V A`; the only bridge needed is that faithfulness of `V` on `A` at the involution
`t ∈ V#` is exactly `t ∉ C_G(A)` (`not_mem_centralizer_of_faithful`). -/
theorem L29GoodProp_proved : Work.CORE2B.C15.L29GoodProp := by
  intro T G _ _ hFT hctx B V A hVS htV hfour hhyp hAnil hAodd hVNA hFaith s hsV hgood
  exact L29_case_i_good_general T hctx B V A hVS htV hfour hhyp hAnil hAodd hVNA
    (not_mem_centralizer_of_faithful B V A htV hFaith) s hsV hgood

end Work.CORE2B
