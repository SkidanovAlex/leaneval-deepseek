import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.step1
import Submission.Work.ThmF.ChV3.Prove.S1_CG_card_orbit
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.CH_card_chainfree
import Submission.Work.ThmF.ChV3.Prove.s_inverts_T_101
import Submission.Work.ThmF.ChV3.Prove.CG_pPart_101
import Submission.Work.ThmF.ChV3.Prove.NG_ne_NG_P_101
import Submission.Work.ThmF.ChV3.Prove.orbit_count_101

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.m_eq_one_101` — §3 leaf **12a** (case (10-1): `m = 1`)

Peterfalvi II Ch. V §3, step (12) in case (10-1): the `N_G(R)`-orbit count.  Here the leaf is
stated chain-free (no `Chain15`): the near-field shadow is replaced by the explicit hypotheses
`hRc, hRn, hKer, hcardR, hcq, hNG` and the step-(11) output `h11`.

Assembly of the four proved sub-lemmas:
* `CG_pPart_101` : `pPart |P| |C_G(P)| = |P|^{m+1}` (S1 chain-free: `R` is a Sylow `p`-subgroup
  of `C_G(P)`);
* `s_inverts_T_101` : `s` inverts `T` (S3's first conjunct chain-free, from `h11.reg`);
* `NG_ne_NG_P_101` : `N_G(R) ≠ N_G(P)` (from the previous line and `|G|_p = |P|^{m+2}`);
* `orbit_count_101` : `|N_G(R)| = |P|^m · |C_G(P)|` (orbit of `P` under `N_G(R)` equals the set
  of order-`|P|` subgroups of `R` outside `T`).

Then `v_p |N_G(R)| = 2m + 1 ≤ m + 2 = v_p |G|` forces `m = 1`, and the order formula follows.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

theorem m_eq_one_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t))
    {R : Subgroup G} {m : ℕ}
    (hm : 1 ≤ m) (hRc : R ≤ Work.ThmF.ChV3.CG P) (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hKer : Work.ThmF.ChV3.Ker H Q P t = P)
    (hcardR : Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P)
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    (h101 : Work.ThmF.ChV3.Case101 H t P m) :
    m = 1 ∧ Nat.card ↥(Work.ThmF.ChV3.NG R) =
      Nat.card P * Nat.card ↥(Work.ThmF.ChV3.CG P) := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  -- ## the four sub-results
  have hCGp : Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card ↥(Work.ThmF.ChV3.CG P))
      = Nat.card P ^ (m + 1) := CG_pPart_101 hFT hC4 c hpf hm hcq h101
  have hsT : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹ :=
    s_inverts_T_101 hFT hC4 c hpf hm hRc hRn hKer hcardR hcq h11
  have hNGne : Work.ThmF.ChV3.NG R ≠ Work.ThmF.ChV3.NG P :=
    NG_ne_NG_P_101 c hpf hm hRc hRn hKer hcardR hNG hCGp h101
  have hOR : Nat.card ↥(Work.ThmF.ChV3.NG R)
      = Nat.card P ^ m * Nat.card ↥(Work.ThmF.ChV3.CG P) :=
    orbit_count_101 hC4 c hpf hm hRc hRn hKer hcardR hcq hNG h11 hsT hNGne
  -- ## the `p`-adic arithmetic
  have hP0 : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hCG0 : Nat.card ↥(Work.ThmF.ChV3.CG P) ≠ 0 := Nat.card_pos.ne'
  -- `v_p |C_G(P)| = m+1`
  have hCGfac : (Nat.card ↥(Work.ThmF.ChV3.CG P)).factorization (Nat.card P) = m + 1 := by
    have h := hCGp
    rw [Work.ThmF.ChV3.pPart] at h
    have h2 := congrArg (fun n => n.factorization (Nat.card P)) h
    rwa [Nat.factorization_pow_self hp, Nat.factorization_pow_self hp] at h2
  -- `v_p |N_G(R)| = 2m+1`
  have hNGRfac : (Nat.card ↥(Work.ThmF.ChV3.NG R)).factorization (Nat.card P) = 2 * m + 1 := by
    rw [hOR, Nat.factorization_mul (pow_ne_zero m hP0) hCG0, Finsupp.add_apply,
      Nat.factorization_pow_self hp, hCGfac]
    ring
  -- `v_p |G| = m+2`
  have hGfac : (Nat.card G).factorization (Nat.card P) = m + 2 := by
    have h := h101.2
    rw [Work.ThmF.ChV3.pPart] at h
    have h2 := congrArg (fun n => n.factorization (Nat.card P)) h
    rwa [Nat.factorization_pow_self hp, Nat.factorization_pow_self hp] at h2
  -- `|N_G(R)| ∣ |G|`, so `2m+1 ≤ m+2`
  have hdvd : Nat.card ↥(Work.ThmF.ChV3.NG R) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card (Work.ThmF.ChV3.NG R)
  have hle : (Nat.card ↥(Work.ThmF.ChV3.NG R)).factorization (Nat.card P)
      ≤ (Nat.card G).factorization (Nat.card P) :=
    (Finsupp.le_def.mp
      ((Nat.factorization_le_iff_dvd (d := Nat.card ↥(Work.ThmF.ChV3.NG R))
        (n := Nat.card G) (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hdvd)) (Nat.card P)
  rw [hNGRfac, hGfac] at hle
  have hm1 : m = 1 := by omega
  refine ⟨hm1, ?_⟩
  rw [hOR, hm1, pow_one]

end Work.ThmF.ChV3.Prove
