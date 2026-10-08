import Mathlib
import Submission.Work.CORE2B.L29Parts
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.L29PairProp_proved
import Submission.Work.CORE2B.L29GoodProp_proved
import Submission.Work.CORE2B.L29TransportProp_proved
import Submission.Work.CORE2B.L29FaithfulProp_proved
import Submission.Work.CORE2B.L29_contra_proved
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27su_utils

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false

-- The assembly of Bender 1981, Lemma 2.9 (the lead's design pass 15)
-- (`_design_gw/Core15L29.lean`, `L29_contra_h27_of_parts`), from the four proved leaves:
-- `Work.CORE2B.L29PairProp_proved` (P1), `L29GoodProp_proved` (P2),
-- `L29TransportProp_proved` (P3), `L29FaithfulProp_proved` (P4).
-- Route: P4 gives `A := F_{2'}(N)` nilpotent, odd, `V`-normalized, with `V` acting faithfully on
-- `A` (`Faithful`); P1 (with `T.c11iii` and `IsFourGroup V` from `L29CallSite.hyp`) gives
-- `u, v ∈ V` nontrivial with `[⟨v⟩, A ⊓ C_A(u)] ≠ 1`; `T.fus` (its `N_G(V)`-transitivity clause)
-- gives `g ∈ N_G(V)` with `g * u * g⁻¹ = B.t`; P3 transports the pair to `(t, g*v*g⁻¹)` for
-- `A^g = Work.GW2.conjSub g A`; P2 (instantiated at `A^g` and `s := g*v*g⁻¹`, with the hypothesis
-- `hyp := hcs.hyp.hyp`) gives `False`.
theorem L29_contra_h27_final : Work.CORE2B.L29_contra_h27 := by
  intro T h22 h26 h27 G hG hFin hFT hctx B V N hcs h1 h2
  -- ## P4: `A := F_{2'}(N)` is nilpotent of odd order, `V`-normalized, with `V` faithful on it.
  obtain ⟨hAnil, hAodd, hVNA, hFaith⟩ :=
    L29FaithfulProp_proved T h22 h26 h27 G hFT hctx B V N hcs h1 h2
  -- ## P1: Bender 1.1(iii) produces a non-trivial witness pair `u, v ∈ V#`.
  obtain ⟨u, huV, v, hvV, hu1, hv1, hcom⟩ :=
    L29PairProp_proved T.c11iii G (Work.GW2.fittingPiIn {2}ᶜ N) V
      hAodd hVNA hcs.hyp.four hFaith
  -- ## `T.fus` (`N_G(V)`-transitivity on `V#`, with `S` dihedral by `BenderCtx.sylow`):
  --    some `g ∈ N_G(V)` carries `u` to `t`.
  obtain ⟨n, hn2, hdih⟩ := L27su_S_dihedral hctx B
  have hno2 : ∀ M : Subgroup G, M.Normal → M.index ≠ 2 := no_index_two_normal hctx
  obtain ⟨g, hgV, hgut⟩ :=
    (T.fus G B.S n hn2 hdih hno2).2 V hcs.hyp.four u huV B.t hcs.hyp.t_mem hu1 (t_ne_one B)
  -- ## P3: transport the pair `(u, v)` to `(t, g v g⁻¹)` for `A^g = conjSub g A`.
  obtain ⟨hAnil', hAodd', hVNA', hFaith', hgvgV, hcom'⟩ :=
    L29TransportProp_proved G (Work.GW2.fittingPiIn {2}ᶜ N) V u v g B.t
      hAnil hAodd hVNA hFaith huV hvV hgV hgut hcom
  -- ## P2: the printed last sentence with `u = t`, at `A^g` and `s := g * v * g⁻¹`.
  exact L29GoodProp_proved T G hFT hctx B V (Work.GW2.conjSub g (Work.GW2.fittingPiIn {2}ᶜ N))
    hcs.hyp.V_le_S hcs.hyp.t_mem hcs.hyp.four hcs.hyp.hyp hAnil' hAodd' hVNA' hFaith'
    (g * v * g⁻¹) hgvgV hcom'

end Work.CORE2B
