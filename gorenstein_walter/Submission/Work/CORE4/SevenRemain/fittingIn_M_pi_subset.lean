import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.A7V
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent
import Submission.Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le
import Submission.Work.CORE4.Case2SevenCentralizer

namespace Work.CORE4.SevenRemain

open Work.GW2 Subgroup

set_option linter.style.haveILetI false

/-- A `p`-subgroup of a group whose order is prime to `p` is trivial.

If `K ≤ L` and `|L|` is prime to `p`, then for `K` a `p`-subgroup the order `|K| = p ^ n` divides
`|L|`; if `n ≥ 1` this forces `p ∣ |L|`, contradicting `Nat.Coprime p |L|`, so `n = 0` and
`|K| = 1`. -/
theorem isPGroup_eq_bot_of_le_coprime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K L : Subgroup G} (hK : IsPGroup p K) (hKL : K ≤ L)
    (hc : Nat.Coprime p (Nat.card ↥L)) : K = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exfalso
      have hpdvdL : p ∣ Nat.card ↥L :=
        dvd_trans (dvd_pow_self p (Nat.pos_iff_ne_zero.mp h)) (hn ▸ Subgroup.card_dvd_of_le hKL)
      have hp1 : p = 1 := Nat.dvd_one.mp (hc ▸ Nat.dvd_gcd (dvd_refl p) hpdvdL)
      exact absurd hp1 (ne_of_gt hp.one_lt)
  exact Subgroup.card_eq_one.mp (by rw [hn0, pow_zero] at hn; exact hn)

/-- **Bender 1981, §4 (7): `π(F(M)) ⊆ π(F(U))`.**

Hypotheses: the §4 configuration `h : Case2Ctx B`, together with

* `F(M) ≤ U ⊓ M` (from "`F(M)` is odd and `F(M) ≤ H ⊓ M`": every odd-order subgroup of `H ⊓ M`
  lies in `U ⊓ M`, since `H ⊓ M = (U ⊓ M) ⊔ S` with `|H ⊓ M : U ⊓ M| = |S|` a 2-power);
* `O_p(F(M)) ≠ ⊥` for every prime `p ∣ |F(M)|` (`F(M)` is nilpotent).

Route (Bender p. 225).  Suppose `p ∣ |F(M)|` with `p ∉ π = π(F(U))`, and put
`Q := pCoreIn p (F(M)) ≠ ⊥`, a nontrivial `p`-group contained in `U ⊓ M`.  Since `F(M)` is
nilpotent (`SevenX.PiFU.isNilpotent_fittingIn`), `Q` is normalised by `M ⊇ U ⊓ M`, so
`Q ⊴ U ⊓ M` (the `p`-core of `F(M)` is characteristic in `F(M) ⊴ M`; `A7V_conj_mem_pCoreIn`
gives the conjugation-step inside `F(M)`), while `N := D.K0 ⊔ D.F ⊴ U ⊓ M` and `Q ⊓ N = ⊥`
(`|N|` is prime to `p` because `N ≤ F(U)`); hence `Q ≤ C_G(N)`
(`A7V_le_centralizer_of_normal_inf_eq_bot`).  Bender 1.1(iv) for nilpotent `F(U)`
(`SevenX.sevenX_le_centralizer_of_isNilpotent`, with `K = F(U)`, `K₀ = N = C_{F(U)}(F)` —
self-centralising by `SevenX.sevenX_fittingIn_inf_centralizer_sup_le`, using
`SixThree`: `F(U) ⊓ M = K₀ ⊔ F`) gives `Q ≤ C_G(F(U))`.  Then
`Q ≤ U ⊓ C_G(F(U)) ≤ F(U)` (P. Hall, `sevenX_centralizer_fittingIn_inf_le_fittingIn`), so `Q = ⊥`
since `p ∤ |F(U)|` — contradiction. -/
theorem fittingIn_M_pi_subset (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.fittingIn h.D.M ≤ B.U ⊓ h.D.M →
        (∀ (p : ℕ), p.Prime → p ∣ Nat.card ↥(Work.GW2.fittingIn h.D.M) →
          Work.GW2.pCore p ↥(Work.GW2.fittingIn h.D.M) ≠ ⊥) →
        Work.GW2.primesOf (Work.GW2.fittingIn h.D.M) ⊆ B.piFU := by
  intro G _ _ hbc B h hFM_le hne p hp
  show p ∈ Work.GW2.primesOf (Work.GW2.fittingIn B.U)
  rw [Work.GW2.primesOf] at hp ⊢
  obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  refine Nat.mem_primeFactors.mpr ⟨hpprime, ?_, Nat.card_pos.ne'⟩
  by_contra hndvd
  -- `Q := O_p(F(M))` is a nontrivial `p`-subgroup of `F(M) ≤ U ⊓ M`
  set Q : Subgroup G := Work.GW2.pCoreIn p (Work.GW2.fittingIn h.D.M) with hQ
  -- `N := K₀ ⊔ F = F(U) ⊓ M`
  set N : Subgroup G := h.D.K0 ⊔ h.D.F with hN
  have hSix : Work.GW2.fittingIn B.U ⊓ h.D.M = N := by
    rw [hN]; exact Work.CORE4.SixThree I G hbc B h.D h.pre
  have hcopFU : Nat.Coprime p (Nat.card ↥(Work.GW2.fittingIn B.U)) :=
    hpprime.coprime_iff_not_dvd.mpr hndvd
  have hQleFM : Q ≤ Work.GW2.fittingIn h.D.M := by
    rw [hQ]; exact Subgroup.map_subtype_le _
  have hQp : IsPGroup p Q := by rw [hQ]; exact Work.CORE4.A7V_isPGroup_pCoreIn p _
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hQ, Work.GW2.pCoreIn] at hbot
    refine hne p hpprime hpdvd ?_
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.subtype_injective (Work.GW2.fittingIn h.D.M))).mp hbot
  have hQleUM : Q ≤ B.U ⊓ h.D.M := hQleFM.trans hFM_le
  have hQleU : Q ≤ B.U := hQleUM.trans inf_le_left
  have hQleM : Q ≤ h.D.M := hQleUM.trans inf_le_right
  have hNleFU : N ≤ Work.GW2.fittingIn B.U := by rw [← hSix]; exact inf_le_left
  have hNleM : N ≤ h.D.M := by rw [← hSix]; exact inf_le_right
  -- `Q` is normal in `M`
  have hQn : (Q.subgroupOf h.D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQleM]
    intro x m hx hm
    rw [hQ] at hx ⊢
    exact Work.CORE4.conj_mem_pCoreIn_of_normal (Subgroup.map_subtype_le _)
      (Work.CORE4.fittingIn_subgroupOf_normal h.D.M) p hm hx
  have hMleNGQ : h.D.M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQn
  have hNleNGQ : N ≤ Subgroup.normalizer (Q : Set G) := hNleM.trans hMleNGQ
  -- `Q` normalizes `N`
  have hQFU : Q ≤ Subgroup.normalizer (Work.GW2.fittingIn B.U : Set G) :=
    hQleU.trans (Work.CORE4.le_normalizer_fittingIn B.U)
  have hQM : Q ≤ Subgroup.normalizer (h.D.M : Set G) := hQleM.trans Subgroup.le_normalizer
  have hQleNGN : Q ≤ Subgroup.normalizer (N : Set G) := by
    rw [← hSix]
    refine le_trans (le_inf hQFU hQM) ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := Work.GW2.fittingIn B.U) (K := h.D.M)
  -- `Q ⊓ N = ⊥`, since `Q` is a `p`-group and `N ≤ F(U)` has order prime to `p`
  have hQinfN : Q ⊓ N = ⊥ :=
    isPGroup_eq_bot_of_le_coprime hpprime (hQp.to_le inf_le_left)
      (le_trans inf_le_right hNleFU) hcopFU
  have hcomm : ⁅N, Q⁆ = ⊥ := by
    have h1 : ⁅N, Q⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.mp hNleNGQ
    have h2 : ⁅N, Q⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp hQleNGN
    exact le_bot_iff.mp ((le_inf h1 h2).trans (le_of_eq hQinfN))
  have hQleCN : Q ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (Subgroup.commutator_comm N Q ▸ hcomm)
  -- Bender 1.1(iv) for the nilpotent `F(U)` and `N = C_{F(U)}(F)`
  have hsc : Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer (N : Set G) ≤ N := by
    rw [hN]
    exact Work.CORE4.SevenX.sevenX_fittingIn_inf_centralizer_sup_le B h.D h.pre hSix
  have hQleCFU : Q ≤ Subgroup.centralizer (Work.GW2.fittingIn B.U : Set G) :=
    Work.CORE4.SevenX.sevenX_le_centralizer_of_isNilpotent I.toolkit.c11iv
      (Work.GW2.fittingIn B.U) N Q
      (Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn B.U) hNleFU hsc
      hpprime hQp hcopFU hQFU hQleCN
  -- P. Hall in the solvable odd-order group `U`: `Q ≤ U ⊓ C_G(F(U)) ≤ F(U)`
  have hsolv : Group.IsSolvable ↥B.U := I.toolkit.ft ↥B.U B.U_odd
  have hQleFUk : Q ≤ Work.GW2.fittingIn B.U :=
    (le_inf hQleCFU hQleU).trans (Work.CORE4.sevenX_centralizer_fittingIn_inf_le_fittingIn B.U hsolv)
  exact hQne (isPGroup_eq_bot_of_le_coprime hpprime hQp hQleFUk hcopFU)

end Work.CORE4.SevenRemain
