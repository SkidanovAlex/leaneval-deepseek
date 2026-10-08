import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.ThreePoints.ThmC.app1_2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I Ch. II §3, condition (C1)

Let `H` be a strongly embedded subgroup of the finite group `G`, `t ∉ H` an involution and
`u ∈ H` an involution.  Writing `D = H ⊓ H^t` for the two-point stabiliser and
`M = D ⊓ D^u`, suppose some `y ∈ M` does not commute with `u`.  Then there is an odd prime `p`
and a `u`-invariant `p`-Sylow subgroup `P` of `M` which is not centralised by `u`.

This is exactly the input "(C1)" of Peterfalvi's Chapter II §3, Step 1: the Sylow `p`-subgroup of
`D ⊓ D^u` normalised but not centralised by `u`.

The mathematical content is the elementary coprime-action fact that a group of odd order on which
an involution acts non-trivially has an invariant Sylow subgroup which the involution does not
centralise.  Concretely: if `N = C_M(u)` and every `u`-invariant Sylow of `M` lay in `N`, then
taking, for every prime `p ∣ |M|`, a `u`-invariant Sylow `P_p` of `M` (Peterfalvi App. I (2)(a),
`Work.ThreePoints.ThmC.app1_2`) with `P_p ≤ N` would force the `p`-parts of `|N|` and `|M|` to
coincide for every `p`, hence `N = M`, contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

/-- A Sylow `p`-subgroup of a subgroup `X` of a finite group has order the `p`-part of `|X|`. -/
theorem IsSylowOf.card_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P X : Subgroup G} (h : IsSylowOf p P X) :
    Nat.card ↥P = p ^ (Nat.card ↥X).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := isSylowOf_toSylow h
  have h1 : Nat.card ↥(S : Subgroup ↥X) = p ^ (Nat.card ↥X).factorization p :=
    Sylow.card_eq_multiplicity S
  rw [hS] at h1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv]
  exact h1

theorem hA_c1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t u : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    (hnc : ∃ y ∈ Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u
        (Submission.Blueprint.twoPoint H t), u * y ≠ y * u) :
    ∃ p : ℕ, ∃ P : Subgroup G, p.Prime ∧ p ≠ 2 ∧
      Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H t ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) ∧
      u ∈ Subgroup.normalizer (P : Set G) ∧ ¬ (∀ x ∈ P, u * x = x * u) := by
  classical
  obtain ⟨y, hy, hyu⟩ := hnc
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hD
  set M : Subgroup G := D ⊓ Submission.Blueprint.conj u D with hMM
  have hyM : y ∈ M := hy
  have hu2 : orderOf u = 2 := hu.2
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2, pow_two] at h
    exact h
  -- `D` has odd order, hence so does `M ≤ D`
  have hoddD : Odd (Nat.card ↥D) := by
    have h := hH.2.2 t htH
    simpa only [Submission.Blueprint.twoPoint, Submission.Blueprint.conj, D] using h
  have hM_le_D : M ≤ D := by rw [hMM]; exact inf_le_left
  have hoddM : Odd (Nat.card ↥M) := Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le hM_le_D)
  -- `u` normalises `M = D ⊓ D^u`
  have hconj_conj : Submission.Blueprint.conj u (Submission.Blueprint.conj u D) = D := by
    rw [← Work.DoubleTransitivity.conj_mul, huu, Work.DoubleTransitivity.conj_one]
  have hu_norm_M : u ∈ Subgroup.normalizer (M : Set G) := by
    rw [← Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
    rw [hMM, Work.ThreePoints.conj_inf u D (Submission.Blueprint.conj u D), hconj_conj, inf_comm]
  -- `N = C_M(u)`, a proper subgroup of `M` because `y` does not commute with `u`
  set N : Subgroup G := M ⊓ Subgroup.centralizer ({u} : Set G) with hNN
  have hN_le_M : N ≤ M := by rw [hNN]; exact inf_le_left
  have hN_ne_M : N ≠ M := by
    intro h
    have hy' : y ∈ N := h ▸ hyM
    rw [hNN, Subgroup.mem_inf] at hy'
    have hc : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy'.2
    exact hyu hc.symm
  have hoddN : Odd (Nat.card ↥N) := Odd.of_dvd_nat hoddM (Subgroup.card_dvd_of_le hN_le_M)
  have hdvd : Nat.card ↥N ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hN_le_M
  have hcard_ne : Nat.card ↥N ≠ Nat.card ↥M := by
    intro h
    exact hN_ne_M (Subgroup.eq_of_le_of_card_ge hN_le_M (le_of_eq h.symm))
  -- pick a prime `p` at which the `p`-part of `|N|` is strictly below that of `|M|`
  obtain ⟨p, hp, hpdvd⟩ : ∃ p, Nat.Prime p ∧ p ∣ Nat.card ↥M / Nat.card ↥N := by
    refine Nat.exists_prime_and_dvd ?_
    intro h1
    have hMeq : Nat.card ↥M = Nat.card ↥N * (Nat.card ↥M / Nat.card ↥N) :=
      (Nat.mul_div_cancel' hdvd).symm
    rw [h1, mul_one] at hMeq
    exact hcard_ne hMeq.symm
  have hMeq : Nat.card ↥M = Nat.card ↥N * (Nat.card ↥M / Nat.card ↥N) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hk_ne : Nat.card ↥M / Nat.card ↥N ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hMeq
    exact Nat.card_pos.ne' hMeq
  have hfac : (Nat.card ↥M).factorization p
      = (Nat.card ↥N).factorization p + (Nat.card ↥M / Nat.card ↥N).factorization p := by
    conv_lhs => rw [hMeq]
    rw [Nat.factorization_mul (a := Nat.card ↥N) (b := Nat.card ↥M / Nat.card ↥N)
      Nat.card_pos.ne' hk_ne]
    rfl
  have hp1 : 1 ≤ (Nat.card ↥M / Nat.card ↥N).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hk_ne).mp hpdvd
  have hlt : (Nat.card ↥N).factorization p < (Nat.card ↥M).factorization p := by
    rw [hfac]; omega
  have hpne2 : p ≠ 2 := by
    intro hp2
    have hN2 : ¬ (2 ∣ Nat.card ↥N) := by
      rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hoddN
    have hM2 : ¬ (2 ∣ Nat.card ↥M) := by
      rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hoddM
    rw [hp2] at hlt
    rw [Nat.factorization_eq_zero_of_not_dvd hN2, Nat.factorization_eq_zero_of_not_dvd hM2] at hlt
    exact lt_irrefl 0 hlt
  -- `u` normalises `N`
  have hu_mem_C : u ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hu_norm_C : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({u} : Set G) : Set G) :=
    Subgroup.le_normalizer hu_mem_C
  have hu_norm_N : u ∈ Subgroup.normalizer (N : Set G) := by
    rw [hNN]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hu_norm_M, hu_norm_C⟩
  have hcopM : Nat.Coprime (Nat.card ↥M) 2 := Nat.coprime_two_right.mpr hoddM
  have hcopN : Nat.Coprime (Nat.card ↥N) 2 := Nat.coprime_two_right.mpr hoddN
  have hu_norm_bot : u ∈ Subgroup.normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  -- a `u`-invariant `p`-Sylow `T` of `N` ...
  obtain ⟨T, hbotT, hT_syl, huT⟩ :=
    (app1_2 (d := 2) Nat.prime_two hu2 (X := N) hcopN hu_norm_N
      (p := p) hp).1 ⊥ bot_le IsPGroup.of_bot hu_norm_bot
  have hT_le_M : T ≤ M := (hT_syl.1).trans hN_le_M
  -- ... lying in a `u`-invariant `p`-Sylow `P` of `M`
  obtain ⟨P, hTP, hP_syl, huP⟩ :=
    (app1_2 (d := 2) Nat.prime_two hu2 (X := M) hcopM hu_norm_M
      (p := p) hp).1 T hT_le_M hT_syl.2.1 huT
  have hP_not_le_N : ¬ (P ≤ N) := by
    intro hPN
    have hPT : P = T := hT_syl.2.2 P hTP hPN hP_syl.2.1
    have hcard : Nat.card ↥P = Nat.card ↥T := by rw [hPT]
    rw [IsSylowOf.card_eq hp hP_syl, IsSylowOf.card_eq hp hT_syl] at hcard
    have hstrict : p ^ (Nat.card ↥N).factorization p < p ^ (Nat.card ↥M).factorization p :=
      Nat.pow_lt_pow_right hp.one_lt hlt
    rw [← hcard] at hstrict
    exact lt_irrefl _ hstrict
  refine ⟨p, P, hp, hpne2, hP_syl, huP, ?_⟩
  intro hcomm
  exact hP_not_le_N fun x hx => by
    rw [hNN, Subgroup.mem_inf]
    exact ⟨hP_syl.1 hx, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx).symm⟩

end Work.ThreePoints.ThmC
