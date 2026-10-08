import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_step1_leaf
import Submission.Work.CORE2B.layer_eq_bot_of_normal_contains_t
import Submission.Work.CORE2B.L27_fittingPi_sup_compl
import Submission.Work.CORE2B.L27_fittingPi_compl_of_odd
import Submission.Work.CORE2B.L27_crux_commutator_2prime
import Submission.Work.CORE2B.L27_O2_centralized_by_t
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.L27cf_centralizes_odd_pi_part
import Submission.Work.CORE2B.L27_pi_subgroup_in_fittingPi
import Submission.Work.CORE2B.L27_fittingPiIn_le_iSup_singleton
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.L27odd_helpers
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.L27su_hnot
import Submission.Work.CORE2B.L27su_two_core_le_pCoreIn_Hhat
import Submission.Work.CORE2B.L27su_eq_bot_of_le_pCoreIn_Hhat
import Submission.Work.CORE2B.L27su_pCore_le_centralizer_U

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Bender 1981, Lemma 2.7, the step `F_{π'}(M) ≠ 1`

This file proves the `F_{π'}(M) ≠ 1` step of Bender's Lemma 2.7 by assembling the pieces that
the sibling modules of area `CORE2B` provide:

* `t` centralizes `F_π(M)` (`L27su_pi_part_centralized` below, from `F_2(M) ≤ O₂(M) ≤ C(t)` and
  Bender's "`t` centralizes the odd part of `F_π(M)`", `L27cf_centralizes_odd_pi_part`);
* `t` inverts `F_{π'}(M)` (`inverts_fittingPiIn_pi_compl_local`);
* `E(M) = 1`, hence `C_M(F(M)) ≤ F(M)`, so that `[M,t] ≤ F(M)`
  (`layer_eq_bot_of_normal_contains_t` applied to Bender's step 1, `L27_step1_leaf`, plus
  `centralizer_fittingIn_inf_le_fitting`);
* `[M,t] ≠ 1` because `M ⊄ Ĥ ⊇ C(t)`;
* `F_2(M) = O₂(M) = 1` (`L27su_two_core_eq_bot_of_fstar` below: `F*(Ĥ) ≤ M` gives `F(U) ≤ M`,
  whence Bender's `[O₂(M),U] = 1` (1.1(iv) with `K = U`, `K₀ = F(U)`), and Theorem 2.6's
  `O₂(Ĥ) = S ⊓ C(U)` plus the coatom argument finish), which makes every generator `[m,t]` —
  an involution, since `t` inverts it and centralizes `F_π(M)` under the assumption
  `F_{π'}(M) = 1` — lie in `F_2(M)`; hence `[M,t] ≤ F_2(M) = 1`, a contradiction.
-/

/-- `t` centralizes `F_π(M)` (Bender 1981, Lemma 2.7: "`t` centralizes `F_π(M)`"), where
`π = π(F(Ĥ))`.

`F_π(M) ≤ ⨆_{q ∈ π} F_q(M)` because `F(M)` is nilpotent, and each `F_q(M)` is centralized by `t`:
for `q = 2` this is the 2-centrality of `t` (`t` centralizes `O₂(M) ≥ F_2(M)`), for odd `q ∈ π`
it is Bender's "`t` centralizes the odd part of `F_π(M)`". -/
theorem L27su_pi_part_centralized {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G) := by
  -- the odd part of `π`
  have hodd : Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ≤
      Subgroup.centralizer ({B.t} : Set G) :=
    L27cf_centralizes_odd_pi_part G hFT hCtx B M hD h23 h26
  -- `F_{2}(M) ≤ O₂(M) ≤ C(t)`
  have htwo : Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ Subgroup.centralizer ({B.t} : Set G) := by
    have h1 : Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ Work.GW2.pCoreIn 2 M := by
      rw [Work.GW2.fittingPiIn, Work.GW2.pCoreIn]
      exact Subgroup.map_mono (L27c_fittingPi_two_le_pCore_two (M := ↥M))
    exact h1.trans (L27_O2_centralized_by_t T h23 h26 G hFT hCtx B M hD)
  -- assemble over the primes of `π`
  refine (L27_fittingPiIn_le_iSup_singleton B.pi M).trans ?_
  refine iSup_le fun q => iSup_le fun hq => ?_
  by_cases hq2 : q = 2
  · subst hq2
    exact htwo
  · refine (fittingPiIn_mono' (K := M) ?_).trans hodd
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hq, by simpa using hq2⟩

/-! ## The step `O₂(M) = 1` -/

/-- **Bender 1981, Lemma 2.7: `O₂(M) = 1`.**  From `O₂(M) ≤ C_G(t)` and `F*(Ĥ) ≤ M` (hence
`F(U) ≤ M`): Bender's `[O₂(M),U] = 1` (1.1(iv) with `K = U`, `K₀ = F(U)`), Theorem 2.6's
`O₂(Ĥ) = S ⊓ C(U)`, and the coatom argument. -/
theorem L27su_two_core_eq_bot_of_fstar {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hnot : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat))
    (hC : Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G))
    (hFstar : Work.GW2.fstarIn B.Hhat ≤ M) :
    Work.GW2.pCoreIn 2 M = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `U ◁ Ĥ` (Theorem 2.6), hence `F(U) ≤ F(Ĥ) ≤ F*(Ĥ) ≤ M`
  have hUle : B.U ≤ B.Hhat :=
    (Subgroup.map_subtype_le (H := B.H) (Work.GW2.oddCore ↥B.H)).trans B.H_le_Hhat
  have hUeq : B.U = Work.GW2.oddCoreIn B.Hhat := (h26 G hFT hCtx B).1.symm
  have hUnorm : (B.U.subgroupOf B.Hhat).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mpr ?_
    rw [hUeq, Work.GW2.oddCoreIn]
    exact le_normalizer_map_subtype_local B.Hhat (Work.GW2.oddCore ↥B.Hhat)
      (Subgroup.normalCore_normal _)
  have hFUle : Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat :=
    fittingIn_le_fittingIn_of_normal_local hUle hUnorm
  have hFU : Work.GW2.fittingIn B.U ≤ M :=
    hFUle.trans ((Subgroup.map_mono
      (le_sup_left : Work.GW2.fitting ↥B.Hhat ≤ Work.GW2.fstar ↥B.Hhat)).trans hFstar)
  -- Bender's `[O₂(M), U] = 1`
  have hCU : Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer (B.U : Set G) :=
    L27su_pCore_le_centralizer_U T G hFT hCtx B M hC hFU
  -- Theorem 2.6: `O₂(M) ≤ O₂(Ĥ) = S ⊓ C(U)`, and the coatom argument
  have hle : Work.GW2.pCoreIn 2 M ≤ Work.GW2.pCoreIn 2 B.Hhat :=
    L27su_two_core_le_pCoreIn_Hhat T h26 G hFT hCtx B (Work.GW2.pCoreIn 2 M)
      (isPGroup_pCoreIn_two M) hCU hC
  exact L27su_eq_bot_of_le_pCoreIn_Hhat T h22 h26 G hFT hCtx B M hD hle

/-! ## The main reduction and the target -/

/-- **Bender 1981, Lemma 2.7, the step `F_{π'}(M) ≠ 1`**, reduced to the two inputs
"`F*(Ĥ)` is not a `p`-group" and "`O₂(M) = 1`". -/
theorem L27su_fittingPiIn_compl_ne_bot_aux :
    ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop)
      (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        (¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)) →
        Work.GW2.pCoreIn 2 M = ⊥ →
        Work.GW2.fittingPiIn B.piᶜ M ≠ ⊥ := by
  intro T h22 h23 h26 G _ _ hFT hCtx B M hD hnot hO2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- (1) `t` centralizes `F_π(M)`
  have hpiC : Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    L27su_pi_part_centralized T h22 h23 h26 hFT hCtx B M hD
  -- (2) `E(M) = 1`, hence `C_M(F(M)) ≤ F(M)`
  have hlayer : Work.GW2.layerIn M = ⊥ :=
    layer_eq_bot_of_normal_contains_t L27_step1_leaf T h23 h26 G hFT hCtx B M hD
  have hcentFit := centralizer_fittingIn_inf_le_fitting T hFT hCtx B M hD hlayer
  -- (3) `F(M) = F_π(M) · F_{π'}(M)`
  have hjoin : Work.GW2.fittingPiIn B.pi M ⊔ Work.GW2.fittingPiIn B.piᶜ M = Work.GW2.fittingIn M :=
    L27_fittingPi_sup_compl G B.pi
      (fun q hq => (Nat.mem_primeFactors.mp hq).1) M
  -- (4) `t` inverts `F_{π'}(M)`
  have hinv : Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M) :=
    inverts_fittingPiIn_pi_compl_local h23 hFT hCtx B M hD
  -- (5) `[M,t] ≤ C(F(M))`
  have hker : ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) :=
    centralizes_fittingIn_of_parts B M hpiC hjoin hinv
  -- (6) `[M,t] ≤ M`
  have hKM : ⁅M, Subgroup.zpowers B.t⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm y hy
    have hyM : y ∈ M := (Subgroup.zpowers_le.mpr hD.t_mem) hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)) (M.inv_mem hyM)
  -- (7) `[M,t] ≤ F(M)`
  have hKF : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingIn M :=
    (le_inf hker hKM).trans hcentFit
  -- (8) `[M,t] ≠ 1`
  have hKne : ⁅M, Subgroup.zpowers B.t⁆ ≠ ⊥ := by
    intro hbot
    have hle : M ≤ Subgroup.centralizer (Subgroup.zpowers B.t) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hMle : M ≤ Subgroup.centralizer ({B.t} : Set G) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp (hle hm) B.t (Subgroup.mem_zpowers B.t)
    exact hD.not_le (hMle.trans B.H_le_Hhat)
  -- (9) `t`'s powers are `1` and `t`
  have hpow : ∀ y ∈ Subgroup.zpowers B.t, y = 1 ∨ y = B.t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by
          rw [hx, hy]
          have h := pow_orderOf_eq_one B.t
          rw [B.t_order] at h
          simpa [pow_two] using h)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by
          rw [hx]
          have h := pow_orderOf_eq_one B.t
          rw [B.t_order] at h
          exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h))
  -- (10) `F_2(M) ≤ O₂(M) = 1`
  have hF2bot : Work.GW2.fittingPiIn ({2} : Set ℕ) M ≤ ⊥ := by
    rw [← hO2, Work.GW2.fittingPiIn, Work.GW2.pCoreIn]
    exact Subgroup.map_mono (L27c_fittingPi_two_le_pCore_two (M := ↥M))
  -- (11) suppose `F_{π'}(M) = 1`; then `F(M) = F_π(M)`
  by_contra hbot
  have hFM : Work.GW2.fittingIn M = Work.GW2.fittingPiIn B.pi M := by
    rw [← hjoin, hbot, sup_bot_eq]
  -- every generator `⁅m,t⁆` is an involution, hence lies in `F_2(M)`
  have hgen : ∀ m ∈ M, ⁅m, B.t⁆ ∈ Work.GW2.fittingPiIn ({2} : Set ℕ) M := by
    intro m hm
    have hxF : ⁅m, B.t⁆ ∈ Work.GW2.fittingIn M :=
      hKF (Subgroup.commutator_mem_commutator hm (Subgroup.mem_zpowers B.t))
    have hxpi : ⁅m, B.t⁆ ∈ Work.GW2.fittingPiIn B.pi M := hFM ▸ hxF
    have hcomm : B.t * ⁅m, B.t⁆ = ⁅m, B.t⁆ * B.t :=
      Subgroup.mem_centralizer_iff.mp (hpiC hxpi) B.t (Set.mem_singleton_iff.mpr rfl)
    have hinv := L27odd_t_inv B m
    have hxx : ⁅m, B.t⁆⁻¹ = ⁅m, B.t⁆ := by
      rw [← hinv]
      calc B.t * ⁅m, B.t⁆ * B.t⁻¹ = (B.t * ⁅m, B.t⁆) * B.t⁻¹ := by rw [mul_assoc]
        _ = (⁅m, B.t⁆ * B.t) * B.t⁻¹ := by rw [hcomm]
        _ = ⁅m, B.t⁆ * (B.t * B.t⁻¹) := by rw [mul_assoc]
        _ = ⁅m, B.t⁆ := by rw [mul_inv_cancel, mul_one]
    have hx2 : ⁅m, B.t⁆ * ⁅m, B.t⁆ = 1 := by
      simpa [hxx] using inv_mul_cancel ⁅m, B.t⁆
    have hord : orderOf ⁅m, B.t⁆ ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hx2
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅m, B.t⁆) := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h1
      · exact IsPGroup.of_card (p := 2) (G := ↥(Subgroup.zpowers ⁅m, B.t⁆)) (n := 0)
          (by rw [Nat.card_zpowers, h1]; rfl)
      · exact IsPGroup.of_card (p := 2) (G := ↥(Subgroup.zpowers ⁅m, B.t⁆)) (n := 1)
          (by rw [Nat.card_zpowers, h1]; rfl)
    have hpi : Subgroup.IsPiSubgroup ({2} : Set ℕ) (Subgroup.zpowers ⁅m, B.t⁆) :=
      Subgroup.isPiSubgroup_of_isPGroup_of_mem hpg (by simp)
    exact L27_pi_subgroup_in_fittingPi M (Subgroup.zpowers ⁅m, B.t⁆) ({2} : Set ℕ)
      (Subgroup.zpowers_le.mpr hxF) hpi (Subgroup.mem_zpowers ⁅m, B.t⁆)
  have hle2 : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn ({2} : Set ℕ) M := by
    rw [Subgroup.commutator_le]
    intro m hm y hy
    rcases hpow y hy with rfl | rfl
    · rw [commutatorElement_one_right]
      exact Subgroup.one_mem _
    · exact hgen m hm
  exact hKne (le_bot_iff.mp (hle2.trans hF2bot))

/-! ## The target declaration — RETIRED (statement kept, declaration removed)

```
theorem L27su_fittingPiIn_compl_ne_bot (T) (h22) (h23) (h26) (G) (hFT) (hCtx) (B) (M)
    (hD : L27Hyp B M) : F_{π'}(M) ≠ ⊥
```

— Bender's `F_{π'}(M) ≠ 1`.  Its proof (kept, hole-free, above) is
`L27su_fittingPiIn_compl_ne_bot_aux`, which needs `F^*(Ĥ) ≤ M` as an extra input; the final step
supplied it from the retired declaration `L27su_fstarIn_Hhat_le_M` (the Dedekind flagstone), so the
unconditional form is **not derivable** here.  The delivered Lemma 2.7 does not need it: design pass
12/18 replaces it by `L27su_A_ne_bot_v12` (`Submission/Work/CORE2B/L27su_assembly.lean`), which
derives `F_{π'}(M) ≠ ⊥` from conclusion (a) `⁅M,t⁆ ≤ F_{π'}(M)` alone.  The declaration has been
**removed** so that no module on the delivered path contains an unproved statement; `..._aux` and
the rest of the file stay available.  See
`Submission/Work/CORE2B/NOTES_FALSE_L27su_fittingPiIn_compl_ne_bot.md`.
-/

end Work.CORE2B
