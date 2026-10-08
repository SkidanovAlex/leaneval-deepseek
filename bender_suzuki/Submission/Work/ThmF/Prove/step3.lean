import Mathlib
import Submission.Work.ThmF.ChV3.step3
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.Prove.step1
import Submission.Work.ThmF.Prove.step4
import Submission.Work.ThmF.ChV12.prop3_frobenius_power
import Submission.Work.ThmF.ChV12.prop1b
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.fpf_oddPart
import Submission.Work.S3.exists_minimal_invariant_ell_subgroup_v2
import Submission.Work.S3.P_card_ne_two
import Submission.Work.S3.oddPart_dvd_fpf
import Submission.Work.S3.ctxF_prop3_hstr
import Submission.Work.S3.KP_frobenius_cent
import Submission.Work.S3.cq_ell_subgroup_isCyclic
import Submission.Work.S3.modEq_two_pow_mod_reduce
import Submission.Work.S3.case1_modEq_one
import Submission.Work.S3.minimal_M_card_eq_prime_pow
import Submission.Work.S3.M_k_submodule_dichotomy
import Submission.Work.ThmF.Prove.S3.Case2PowerEll

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step3` — Peterfalvi II, Ch. V §3, step (3)

See `Submission/Work/ThmF/ChV3/step3.lean` for the source text and the discussion of the inputs.
This file assembles the statement from the pieces in `Submission/Work/S3/` and
`Submission/Work/ThmF/Prove/S3/`.

**Note (recorded by this agent).** The external input `ChV3.NearFieldAppXIProp` was missing the
conjunct making `R/N` a group carrying the `C_Q(P)`-action that its own docstring describes; it
has been completed in `ChV3/NearField.lean` (and `ChV3/step2.lean` adjusted accordingly).
-/

namespace Work.ThmF.Prove

open Classical
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- In the standing context, `K = Ksub H t` is `Kset H t` (Ch. V §1 Prop. 2). -/
private theorem ctxF_Ksub_eq_Kset {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 c.sit c.split).2.1

/-- `Ksub H t ≤ H`. -/
private theorem Ksub_le_H {H : Subgroup G} {t : G} : Work.ThmF.Ksub H t ≤ H :=
  (Subgroup.closure_le H).mpr fun x hx => (Subgroup.mem_inf.mp (Work.ThmF.Kset_subset H t hx)).1

/-- `P ≤ H` in the standing context (via `P ≤ V = centD H t ≤ twoPoint H t ≤ H`). -/
private theorem CtxF_P_le_H {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) : ∀ x ∈ P, x ∈ H :=
  fun _ hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (c.P_le hx)).1).1

/-- In the standing context, no non-trivial element of `P` centralises `K = Ksub H t`
(it would lie in `W = C_V(K)`, and `P ⊓ W = ⊥` by Ch. V §3 (1)). -/
private theorem CtxF_P_centralizer_Ksub {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∀ a ∈ P, (∀ k ∈ Work.ThmF.Ksub H t, a * k = k * a) → a = 1 := by
  intro a haP hcomm
  have hKseteq := ctxF_Ksub_eq_Kset hFT hC4 c
  have hPW : Work.ThmF.W H t ⊓ P = ⊥ := (Work.ThmF.Prove.step1 hFT hC4 c).1
  have hcent : a ∈ Subgroup.centralizer ((Work.ThmF.Kset H t : Set G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Work.ThmF.Ksub H t := (Set.ext_iff.mp hKseteq y).mpr hy
    exact (hcomm y hy').symm
  have hmem : a ∈ Work.ThmF.W H t ⊓ P :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨c.P_le haP, hcent⟩, haP⟩
  exact (Subgroup.eq_bot_iff_forall (Work.ThmF.W H t ⊓ P)).mp hPW a hmem

/-- In the standing context, `P` preserves `K = Ksub H t` under conjugation
(Ch. V §3 (1): `V = C_D(t)` normalises `K`, and `P ≤ V`). -/
private theorem CtxF_P_normalizes_Ksub {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∀ p ∈ P, ∀ k ∈ Work.ThmF.Ksub H t, p * k * p⁻¹ ∈ Work.ThmF.Ksub H t := by
  intro p hp k hk
  have hKseteq := ctxF_Ksub_eq_Kset hFT hC4 c
  have hk' : k ∈ Work.ThmF.Kset H t := (Set.ext_iff.mp hKseteq k).mp hk
  exact (Set.ext_iff.mp hKseteq (p * k * p⁻¹)).mpr
    (Work.ThmF.ChV3.CtxF.mem_Kset_conj_P c hp hk')

/-- In the standing context `P ⊓ K = ⊥` (`x ∈ P ⊓ K` is both fixed and inverted by `t`, hence
of order dividing `2`, while `|P|` is odd by (F1)). -/
private theorem CtxF_P_inf_Ksub {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) : P ⊓ Work.ThmF.Ksub H t = ⊥ := by
  have hKseteq := ctxF_Ksub_eq_Kset hFT hC4 c
  have hPodd : Odd (Nat.card P) :=
    Nat.odd_iff.mpr (c.P_prime.eq_two_or_odd.resolve_left (Work.S3.P_card_ne_two c))
  refine (Subgroup.eq_bot_iff_forall (P ⊓ Work.ThmF.Ksub H t)).mpr fun x hx => ?_
  obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.mp hx
  have hxKset : x ∈ Work.ThmF.Kset H t := (Set.ext_iff.mp hKseteq x).mp hxK
  have htx : t * x * t⁻¹ = x⁻¹ := (Work.ThmF.mem_Kset_iff.mp hxKset).2
  have hxc : t * x * t⁻¹ = x := by
    have h := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (c.P_le hxP)).2)
      t (Set.mem_singleton t)
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : x⁻¹ = x := htx.symm.trans hxc
  have hx2 : orderOf x ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by
      calc x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := by rw [hinv]
        _ = 1 := inv_mul_cancel x)
  have hdvd : orderOf x ∣ Nat.card ↥P := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (⟨x, hxP⟩ : ↥P))
    rw [Nat.card_zpowers] at h
    simpa using h
  rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (even_iff_two_dvd.mpr (h2 ▸ hdvd)) (Nat.not_even_iff_odd.mpr hPodd)

/-- `K = Ksub H t` acts fixed-point-freely on `M ≤ oddPart Q` (Ch. V §1 Prop. 1 a). -/
private theorem fpf_Ksub_on_M {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) {M : Subgroup G} (hMle : M ≤ Work.ThmF.oddPart Q) :
    ∀ k ∈ Work.ThmF.Ksub H t, k ≠ 1 → ∀ m ∈ M, k * m * k⁻¹ = m → m = 1 := by
  have hKseteq := ctxF_Ksub_eq_Kset hFT hC4 c
  intro k hk hk1 m hm hfix
  have hk' : k ∈ Work.ThmF.Kset H t := (Set.ext_iff.mp hKseteq k).mp hk
  have hcomm : m * k = k * m := by
    have h := congrArg (fun z => z * k) hfix
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  exact Work.ThmF.ChV3.fpf_Kset_oddPart c.sit hC4 c.split hk' hk1 (hMle hm) hcomm

/-- `C_M(K) = ⊥` for `M ≤ oddPart Q` (Ch. V §1 Prop. 1 a). -/
private theorem cent_Ksub_inf_M {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) {M : Subgroup G} (hMle : M ≤ Work.ThmF.oddPart Q) :
    Subgroup.centralizer ((Work.ThmF.Ksub H t : Subgroup G) : Set G) ⊓ M = ⊥ := by
  obtain ⟨k₀, hk₀, hk₀1⟩ := Work.ThmF.ChV3.CtxF.Kset_nontrivial c
  have hk₀sub : k₀ ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hk₀
  refine (Subgroup.eq_bot_iff_forall
    (Subgroup.centralizer ((Work.ThmF.Ksub H t : Subgroup G) : Set G) ⊓ M)).mpr fun m hm => ?_
  obtain ⟨hmc, hmM⟩ := Subgroup.mem_inf.mp hm
  have hk₀m : k₀ * m = m * k₀ := (Subgroup.mem_centralizer_iff.mp hmc) k₀ hk₀sub
  refine fpf_Ksub_on_M hFT hC4 c hMle k₀ hk₀sub hk₀1 m hmM ?_
  rw [hk₀m, mul_assoc, mul_inv_cancel, mul_one]

/-- The target of `step3`. -/
theorem step3 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hNF : Work.ThmF.ChV3.NearFieldAppXIProp) (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) → (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P := by
  intro ℓ hℓ hdvd
  -- (0) context
  obtain ⟨hKcyc, _hKseteq, _hKn⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 c.sit c.split
  have hKcard : Nat.card ↥(Work.ThmF.Ksub H t) = 2 ^ Nat.card P - 1 :=
    Work.ThmF.Prove.step4_Kcard hFT hC4 c
  have hQnil : Group.IsNilpotent ↥Q :=
    Work.ThmF.ChV12.prop1b c.sit hC4 hTh H Q t c.split
      (Work.ThmF.ChV3.CtxF.Kset_nontrivial c)
  obtain ⟨_hHnorm, hKdvd, hOddQ⟩ := Work.S3.oddPart_dvd_fpf hFT hC4 c hQnil
  have hPodd : Odd (Nat.card P) :=
    Nat.odd_iff.mpr (c.P_prime.eq_two_or_odd.resolve_left (Work.S3.P_card_ne_two c))
  have hℓ2 : ℓ ≠ 2 := by
    intro h
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr hOddQ) (even_iff_two_dvd.mpr hdvd)
  have hKlcop : ¬ ℓ ∣ Nat.card ↥(Work.ThmF.Ksub H t) := by
    intro h
    have h1 : ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) - 1 := h.trans hKdvd
    have h2 : ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) := hdvd
    have h3 : ℓ ∣ 1 := by
      have h4 : ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) -
          (Nat.card ↥(Work.ThmF.oddPart Q) - 1) := Nat.dvd_sub h2 h1
      rwa [Nat.sub_sub_self (Nat.card_pos (α := ↥(Work.ThmF.oddPart Q)))] at h4
    exact hℓ.ne_one (Nat.dvd_one.mp h3)
  have hKP : P ⊓ Work.ThmF.Ksub H t = ⊥ := CtxF_P_inf_Ksub hFT hC4 c
  have hKinv : ∀ p ∈ P, ∀ k ∈ Work.ThmF.Ksub H t, p * k * p⁻¹ ∈ Work.ThmF.Ksub H t :=
    CtxF_P_normalizes_Ksub hFT hC4 c
  have hPcent : ∀ a ∈ P, (∀ k ∈ Work.ThmF.Ksub H t, a * k = k * a) → a = 1 :=
    CtxF_P_centralizer_Ksub hFT hC4 c
  have hFrob : Work.CharPrelim.IsFrobeniusIn (Work.ThmF.Ksub H t ⊔ P)
      (Work.ThmF.Ksub H t) := Work.S3.KP_frobenius_cent hFT hC4 c
  -- (1) the minimal invariant elementary abelian `ℓ`-subgroup `M ≤ oddPart Q`
  obtain ⟨M, hMle, hMne, _hMPg, hMcomm, hMexp, hMinv, hMmin⟩ :=
    Work.S3.exists_minimal_invariant_ell_subgroup_v2 hQnil c.split.normal
      (CtxF_P_le_H c) (Ksub_le_H) hℓ hdvd
  have hMfpf := fpf_Ksub_on_M hFT hC4 c hMle
  have hMcent := cent_Ksub_inf_M hFT hC4 c hMle
  have hMcard : Nat.card ↥M = ℓ ^ Nat.card P :=
    Work.S3.minimal_M_card_eq_prime_pow hNF c hℓ hℓ2 hKcyc hKlcop hKP hFrob
      hMle hMne hMcomm hMexp hMinv hMmin hMcent
  -- (2) Clifford's dichotomy for `M` over `K = Ksub H t`
  rcases Work.S3.M_k_submodule_dichotomy c hℓ hKcyc hKlcop hKP hMne hMcomm hMexp hMinv
      hMcard hMmin with ⟨U, hUle, hUne, hUcard, hUinv⟩ | hKsim
  · -- Case 1: a one-dimensional `𝔽_ℓ[K]`-submodule
    have h1 : ℓ ≡ 1 [MOD Nat.card ↥(Work.ThmF.Ksub H t)] :=
      Work.S3.case1_modEq_one c hℓ hUle hUne hUcard hUinv hMfpf
    have h2 : ℓ ≡ 2 ^ 0 [MOD 2 ^ Nat.card P - 1] := by
      rw [hKcard] at h1
      simpa using h1
    exact ⟨⟨0, c.P_prime.pos, h2⟩,
      Work.ThmF.ChV3.prime_ne_of_modEq_one c.P_prime (by simpa using h2)⟩
  · -- Case 2: `M` is irreducible as `𝔽_ℓ[K]`-module
    obtain ⟨a, haP, hact⟩ := Work.ThmF.Prove.S3.case2PowerEll c hℓ hKcyc hKlcop hKP hKinv hPcent
      hMne hMcomm hMexp hMinv hMcard hMfpf hKsim
    -- the same `a` acts on `K` by a power of the Frobenius `x ↦ x ^ 2` (Ch. V §1 Prop. 3)
    obtain ⟨i, hi⟩ :=
      Work.ThmF.ChV12.prop3_frobenius_power H Q t (Work.S3.ctxF_prop3_hstr hFT hC4 c) a
        (c.P_le haP)
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hKcyc
    have hpow : ((g : Work.ThmF.Ksub H t) : G) ^ ℓ
        = ((g : Work.ThmF.Ksub H t) : G) ^ (2 ^ i) := by
      rw [← hact (g : Work.ThmF.Ksub H t) g.2, hi (g : Work.ThmF.Ksub H t) g.2]
    have hordg : orderOf ((g : Work.ThmF.Ksub H t) : G)
        = Nat.card ↥(Work.ThmF.Ksub H t) := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_zpowers_eq_top hg]
    have hmod : ℓ ≡ 2 ^ i [MOD Nat.card ↥(Work.ThmF.Ksub H t)] := by
      rw [← hordg]
      exact pow_eq_pow_iff_modEq.mp hpow
    have hmod' : ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1] := by
      rw [hKcard] at hmod
      exact hmod
    obtain ⟨j, hj, hjmod⟩ := Work.S3.modEq_two_pow_mod_reduce c.P_prime hmod'
    exact ⟨⟨j, hj, hjmod⟩,
      Work.ThmF.ChV3.prime_ne_of_modEq_two_pow c.P_prime hPodd hj hjmod⟩

end Work.ThmF.Prove
