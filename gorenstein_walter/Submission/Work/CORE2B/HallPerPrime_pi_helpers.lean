import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.HallPerPrime_Xodd
import Submission.Work.CORE2B.HallPerPrime_tSylow
import Submission.Work.CORE2B.L27Hyp_of_L28MHyp
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.L27_solvable_base
-- RETIRED STUB (on disk for reference only; NOT on the delivered path): the declaration this
-- module was created for is retired because its conclusion is exactly the exclusion supplied by Theorem 2.10, so it is vacuous without the theorem it was meant to help prove.
-- Its corrected form, the reason, and the counterexample configuration are recorded in the
-- `RETIRED` block below and in `Submission/Work/CORE2B/NOTES_FALSE_HallPerPrime_pi_not.md`.
-- Nothing in the delivered closure of `Work.CORE2B.Proved` / `L27su_assembly` /
-- `L29_lemma_assembly` / `Thm210_assembly` imports this module.

/-!
# CORE2B — helpers around the per-prime step of Theorem 2.10

* `pCoreIn_le_fittingIn_U` — `O_p(U) ≤ F(U)` for the odd `p`-cores of `U = O(H)`;
* `fittingIn_U_le_fittingIn_Hhat` — `F(U) ≤ F(Ĥ)` (`U = O(Ĥ) ◁ Ĥ`, Theorem 2.6);
* `HallPerPrime_pi_not_negation` — the negation of the retired per-prime statement, i.e. exactly the
  `M`-configuration that Theorem 2.10 must exclude.

These declarations used to live in `Submission/Work/CORE2B/HallPerPrime_pi_not.lean`, which is kept on
disk as a retired stub (its target `HallPerPrime_pi_not` was the per-prime form of Lemma 2.7's first
assertion and is vacuous without Theorem 2.10 itself; design pass 18
`Submission/Work/CORE2B/Core18HallPerPrime{,Case2}.lean` replaced it).  They were moved here so that
the retired stub is imported by nothing on the delivered path.

Consumers: `Submission/Work/CORE2B/HallPerPrime_case2.lean`,
`Submission/Work/CORE2B/L27v12_selfcent.lean`,
`Submission/Work/CORE2B/L27v12_oddpart_mem_fittingU.lean`.
-/

namespace Work.CORE2B

open scoped commutatorElement

open Subgroup

/-!
# The `π'`-case of Bender's per-prime step, and a consequence of its hypotheses

The requested lemma `Work.CORE2B.HallPerPrime_pi_not` formalises Bender (1981), p. 222, the
sentence

> "In particular, `[t, M]` is not a `π'`-group when `N_G(X) ≤ M < G`."

with `X = C_{O_p(U)}(s) = O_p(U) ∩ C_G(s)`, `π = π(F(Ĥ))` and `M` a coatom containing `N_G(X)`
and `S`, not contained in `Ĥ`.

The helper theorem `HallPerPrime_pi_not_negation` below is proved (sorry-free) and records a
*rival consequence of the very same hypotheses*: the hypotheses of the requested lemma already
force

  `⁅M, zpowers B.t⁆ ≤ fittingPiIn B.piᶜ M`,

i.e. the *negation* of the requested conclusion.  Indeed:

* `hnot2 : ¬ Case2 B` forces `B.t ∉ layerIn M`: otherwise case (2) of Theorem 2.10 holds with
  the coatom `M` and the witness `X ≠ ⊥`, `X ≤ F(U)`, `N_G(X) ≤ M`;
* hence `Lemma27Prop` (`h27`) applies to `M`: its relation `Ĥ ⇝ M` is witnessed by `X`, which
  lies in `F(U) ≤ F(Ĥ)` (Theorem 2.6 gives `U = O(Ĥ) ◁ Ĥ`), and `N_G(X) ≤ M` by hypothesis;
  the remaining hypotheses of Lemma 2.7 are supplied by `S ≤ M` and `¬ M ≤ Ĥ`
  (`L27Hyp_of_L28MHyp`).

So the requested conclusion contradicts a consequence of the requested hypotheses; see the
reasoning recorded for the request.
-/

/-- `O_p(U) ≤ F(U)` inside the ambient group. -/
theorem pCoreIn_le_fittingIn_U {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCoreIn p B.U ≤ Work.GW2.fittingIn B.U := by
  rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
  exact Subgroup.map_mono (pCore_le_fitting_local (G := ↥B.U) p)

/-- `F(U) ≤ F(Ĥ)`, since `U = O(Ĥ) ◁ Ĥ` by Theorem 2.6. -/
theorem fittingIn_U_le_fittingIn_Hhat (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat := by
  have hUeq : B.U = Work.GW2.oddCoreIn B.Hhat := (h26 G hFT hCtx B).1.symm
  have hUle : B.U ≤ B.Hhat := hUeq.le.trans (Subgroup.map_subtype_le _)
  have hUnorm : (B.U.subgroupOf B.Hhat).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mpr ?_
    rw [hUeq, Work.GW2.oddCoreIn]
    exact le_normalizer_map_subtype_local B.Hhat (Work.GW2.oddCore ↥B.Hhat)
      (Subgroup.normalCore_normal _)
  exact fittingIn_le_fittingIn_of_normal_local hUle hUnorm

/-- **A rival consequence of the hypotheses of `HallPerPrime_pi_not`**: they already force the
negation of its conclusion.  See the module docstring for the two-line mathematical reason. -/
theorem HallPerPrime_pi_not_negation (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) (hp : Nat.Prime p)
    (hXne : Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) ≠ ⊥)
    (hXlt : ¬ Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G)) :
    ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer
        ((Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) ≤ M →
      (B.S : Subgroup G) ≤ M → ¬ M ≤ B.Hhat →
      ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M := by
  intro M hM hNM hSM hMhat
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set X : Subgroup G := Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) with hXdef
  -- `X ≤ F(U) ≤ F(Ĥ)`
  have hXFU : X ≤ Work.GW2.fittingIn B.U :=
    inf_le_left.trans (pCoreIn_le_fittingIn_U B)
  have hXFH : X ≤ Work.GW2.fittingIn B.Hhat :=
    hXFU.trans (fittingIn_U_le_fittingIn_Hhat h26 G hFT hCtx B)
  -- the Bender relation `Ĥ ⇝ M`, witnessed by `X`
  have hBRel : Work.GW2.BRel B.Hhat M := ⟨X, hXFH, le_trans inf_le_left hNM⟩
  -- `t ∉ E(M)`, since otherwise case (2) of Theorem 2.10 holds
  have htE : B.t ∉ Work.GW2.layerIn M := fun ht =>
    hnot2 ⟨M, hM, ht, X, hXne, hXFU, hNM⟩
  have hL28 : L28MHyp B M := ⟨hM.ne_top, hBRel, hMhat, hSM⟩
  have hD : L27Hyp B M := L27Hyp_of_L28MHyp hCtx B M hL28 htE
  exact (h27 G hFT hCtx B M hD.M_ne_top hD.rel hD.not_le hD.t_mem hD.t_not_layer
    hD.sylow_nc hD.size).1


end Work.CORE2B
