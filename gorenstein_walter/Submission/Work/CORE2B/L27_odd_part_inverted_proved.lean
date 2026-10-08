import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_api
import Submission.Work.BMAX.InvolutionInverts

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# CORE2B — Lemma 2.7, step 3, second half: `t` inverts `F_{π'}(M)`

Bender 1981, Lemma 2.7, p. 221: under `L27Hyp B M` the involution `t` inverts every element of
`F_{π'}(M) = O_{π'}(F(M))` (realized inside `G` as `Work.GW2.fittingPiIn B.piᶜ M`, with
`π = π(F(Ĥ))`).

The argument:

* `F_{π'}(M)` is the image in `M` of `O_{π'}(F(M))`, which is *characteristic* in the normal
  subgroup `F(M) ◁ ↥M`; hence it is normal in `↥M` and therefore normalized by `t ∈ M`
  (`fittingPi_normal`, `mem_normalizer_fittingPiIn` below).
* `F_{π'}(M) ∩ Ĥ = ⊥` is Lemma 2.3(ii) (`h23`), and the fixed points of `t` in `G` lie in
  `C_G(t) = H ≤ Ĥ`; hence the action of the involution `t` on `F_{π'}(M)` is fixed-point-free.
* An involution acting fixed-point-freely on a finite group inverts it — this is the classical
  Burnside argument, already available as `Work.BMAX.InvolutionInverts`.
-/

/-- `F_π(K) = O_π(F(K))` is normal in `↥K`: it is the image of the characteristic subgroup
`O_π(F(K))` of the normal subgroup `F(K) ◁ ↥K`. -/
theorem fittingPi_normal {G : Type} [Group G] [Finite G] (π : Set ℕ) (K : Subgroup G) :
    (Work.GW2.fittingPi π K).Normal := by
  haveI hFK : (Work.GW2.fitting K).Normal := by
    rw [fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.normal K
  haveI hchar : (Work.GW2.piCore π ↥(Work.GW2.fitting K)).Characteristic := by
    rw [piCore_eq_oPiCore π]
    exact inferInstance
  exact ConjAct.normal_of_characteristic_of_normal

/-- `F_π(K) = O_π(F(K))` is a characteristic part of `K`; `t ∈ K` acts on it by conjugation. -/
theorem mem_normalizer_fittingPiIn {G : Type} [Group G] [Finite G] (π : Set ℕ) (M : Subgroup G)
    {t : G} (ht : t ∈ M) :
    t ∈ Subgroup.normalizer ((Work.GW2.fittingPiIn π M : Subgroup G) : Set G) := by
  have hnorm : (Work.GW2.fittingPi π M).Normal := fittingPi_normal π M
  have hle : M ≤ Subgroup.normalizer
      (((Work.GW2.fittingPi π M).map M.subtype : Subgroup G) : Set G) :=
    le_normalizer_map_subtype M (Work.GW2.fittingPi π M) hnorm
  have hgoal : t ∈ Subgroup.normalizer
      (((Work.GW2.fittingPi π M).map M.subtype : Subgroup G) : Set G) := hle ht
  simpa only [Work.GW2.fittingPiIn] using hgoal

-- Prove the leaf `Work.CORE2B.L27_odd_part_inverted` (Bender 1981, Lemma 2.7, p. 221, step 3,
-- second half): under `L27Hyp B M`, `t` inverts every element of `F_{π'}(M) = fittingPiIn B.piᶜ M`,
-- where `B.pi = π(F(Ĥ))`.
-- Route: `F_{π'}(M) ∩ Ĥ = 1` (Lemma 2.3(ii), available as `h23`), and `Ĥ = C(t)` at least on
-- `F_{π'}(M)`: `t` normalizes `F_{π'}(M)` (characteristic in `M ∋ t`) and acts fixed-point-freely on
-- it, so (being an involution acting on a nilpotent `π'`-group) it inverts it.
-- NOTE: the statement was corrected from `{2}ᶜ` to `B.piᶜ` after the page-image audit of Bender
-- p. 221: Lemma 2.3(ii) and Lemma 2.7 both use the same `π = π(F(Ĥ))`, not `2`.
-- See `Submission/Work/CORE2B/NOTES_CORE2B.md` §3.
theorem L27_odd_part_inverted_proved : Work.CORE2B.L27_odd_part_inverted := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  -- Lemma 2.3(ii): the `π'`-part of `F(M)` meets `Ĥ` trivially.
  have hFixBot : Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat = ⊥ :=
    (h23 G hFT hCtx B M hD.M_ne_top hD.rel).2.1
  -- `t` is an involution.
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  -- `t ∈ M` normalizes the characteristic subgroup `F_{π'}(M)`.
  have htN : B.t ∈ Subgroup.normalizer
      ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) :=
    mem_normalizer_fittingPiIn (π := B.piᶜ) (M := M) hD.t_mem
  refine Work.BMAX.InvolutionInverts (Work.GW2.fittingPiIn B.piᶜ M) B.t ht2 htN ?_
  -- Fixed points of `t` in `F_{π'}(M)`: `C_G(t) = H ≤ Ĥ`, and `F_{π'}(M) ∩ Ĥ = 1`.
  intro x hx hfix
  have hxH : x ∈ B.Hhat := by
    refine B.H_le_Hhat ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h' : B.t * x = x * B.t := by
      have h2 := congrArg (· * B.t) hfix
      simpa [mul_assoc] using h2
    exact h'
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hFixBot]
    exact ⟨hx, hxH⟩
  exact Subgroup.mem_bot.mp hxbot

end Work.CORE2B
