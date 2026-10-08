import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L29_tower
import Submission.Work.CORE2B.L29_hyp_normalizer
import Submission.Work.CORE2B.L27_su_not_le_h22_proved

/-!
# `Work.CORE2B.L29_case_i_good`

Bender 1981, Lemma 2.9, case (i), **good** sub-case (see `NOTES_L29_contra.md` §10):

> Otherwise, `V` acts faithfully on `A := F_{2'}(N)`.  Then `V` contains two involutions,
> say `t` and `s`, such that `X := [s, C_A(t)] ≠ 1`.  Lying in `O₂(N_G(X))`, `t` centralizes
> `N_A(X)`, hence (by 1.1.iv) centralizes `A`, a contradiction.

The hypothesis `hgood` **is** the non-triviality of that commutator, `X := [⟨s⟩, C_A(t)] ≠ ⊥`
where `C_A(t) = A ⊓ C_G(t)`; the contradiction comes from `t ∉ C_G(A)`.  The proof is the printed
one, with the two justifications the printed text leaves out:

* `X ≤ U = O(C(t))`.  `X ≤ A ⊓ C_G(t)` has odd order (`A` does), and odd-order subgroups of
  `C_G(t) = H` lie in `U`: this is `H = U ⊔ S` (`T.split`, Bender's Frobenius-normal-`p`-complement
  step), formalised in the workspace as `L27su_odd_subgroup_le_U`.
* `[⟨s⟩,X] = X`: this is Bender 1.1(i) (`T.c11i`), applicable because `s` normalizes `A`
  (`s ∈ V ≤ N_G(A)`) and centralizes `t` (`s, t ∈ V` and a group of exponent two is commutative).

Then `hyp` gives `t ∈ O₂(N_G(X))`, whence `[N_A(X), t] ≤ O₂(N_G(X)) ⊓ A = ⊥`, and the normalizer
tower of `X` inside the nilpotent `A` reaches `A` (`L29_tower`), so `t` centralizes `A` —
contradicting `hAcen`.  (This is what `L29_hyp_normalizer.centralizes_normalizer_of_hyp` packages
in the presence of a normal subgroup `N` with `A ◁ N`; the general lemma below does the two-line
commutator computation directly, so that it does not mention `N` at all.)

Main declarations:

* `L29_case_i_good_general` — the same statement with `N` removed: `V ≤ N_G(A)` and `t ∉ C_G(A)`
  replace `A ≤ N`, `A ◁ N`.  This is the form needed after the conjugation transport
  (`C15.L29TransportProp`, which conjugates `A` to a conjugate `A^g` without conjugating `N`),
  and it also yields the design leaf `C15.L29GoodProp` (P2).
* `L29_case_i_good` — the requested statement, a corollary.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

/-- A subgroup of exponent two is commutative: `(xy)² = 1` gives `xy = (xy)⁻¹ = y⁻¹x⁻¹ = yx`.
In particular a Klein four-group (`Work.GW2.IsFourGroup`) is commutative. -/
private theorem fourGroup_comm {G : Type} [Group G] (V : Subgroup G)
    (hV : Work.GW2.IsFourGroup V) : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  intro x hxV y hyV
  have hx : x * x = 1 := by simpa [pow_two] using hV.2 x hxV
  have hy : y * y = 1 := by simpa [pow_two] using hV.2 y hyV
  have hxy : (x * y) * (x * y) = 1 := by
    simpa [pow_two] using hV.2 (x * y) (V.mul_mem hxV hyV)
  have h2 : (x * y) * (y * x) = 1 := by
    calc (x * y) * (y * x) = x * (y * y) * x := by group
      _ = x * 1 * x := by rw [hy]
      _ = x * x := by rw [mul_one]
      _ = 1 := hx
  exact (mul_left_cancel (h2.trans hxy.symm)).symm

/-- An element normalizing both `H` and `K` normalizes `H ⊓ K`. -/
private theorem normalizer_inf_le {G : Type} [Group G] (H K : Subgroup G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgH, hgK⟩ := hg
  rw [Subgroup.mem_normalizer_iff] at hgH hgK ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hgH x, hgK x]

/-- A subgroup of an odd-order group has odd order. -/
private theorem odd_card_of_le {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (hK : Odd (Nat.card K)) : Odd (Nat.card H) := by
  have hdvd : Nat.card H ∣ Nat.card K := by
    have h1 := Subgroup.card_subgroup_dvd_card (H.subgroupOf K)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact Odd.of_dvd_nat hK hdvd

/-- **The good sub-case of Bender's case (i), in the form in which it is applied** (Lemma 2.9 of
Bender 1981, p. 222; `NOTES_L29_contra.md` §10).

`V ≤ S` is a Klein four-group containing `t`; `A` has odd order and is nilpotent, is normalized by
`V` (`V ≤ N_G(A)`), and is not centralized by `t`; `hyp` is the hypothesis clause of `L29Hyp`
(`t ∈ O₂(N_G(X))` for every `1 ≠ X = [⟨s⟩,X] ≤ U`, `s ∈ S`).  If `s ∈ V` has
`X := [⟨s⟩, C_A(t)] ≠ ⊥`, then `False`.

Unlike `L29_case_i_good`, this statement mentions no `N`: `N` enters the proof of `L29_case_i_good`
only through `V ≤ N` and `A ◁ N`, i.e. through `V ≤ N_G(A)`.  This is exactly the form in which
the statement is needed after the conjugation transport of a witness pair along
`g ∈ N_G(V)` (`C15.L29TransportProp`), where `A` is replaced by `A^g` while `t`, `V`, `S`, `U`
stay fixed; it also gives the design leaf `C15.L29GoodProp` (P2), whose `Faithful V A` is used
only at the involution `t ∈ V`. -/
theorem L29_case_i_good_general {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (V A : Subgroup G)
    (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V) (hfour : Work.GW2.IsFourGroup V)
    (hhyp : ∀ (s : G) (X : Subgroup G), s ∈ (B.S : Subgroup G) → X ≤ B.U → X ≠ ⊥ →
      ⁅Subgroup.zpowers s, X⁆ = X → B.t ∈ Work.GW2.pCoreIn 2 (normalizer (X : Set G)))
    (hAnil : Group.IsNilpotent ↥A) (hAodd : Odd (Nat.card A))
    (hVNA : V ≤ Subgroup.normalizer (A : Set G))
    (hAcen : B.t ∉ Subgroup.centralizer (A : Set G))
    (s : G) (hsV : s ∈ V)
    (hgood : ⁅Subgroup.zpowers s, (A ⊓ Subgroup.centralizer ({B.t} : Set G))⁆ ≠ ⊥) : False := by
  classical
  -- ## Basic membership facts
  have hsS : s ∈ (B.S : Subgroup G) := hVS hsV
  have htNA : B.t ∈ Subgroup.normalizer (A : Set G) := hVNA htV
  have hsNA : s ∈ Subgroup.normalizer (A : Set G) := hVNA hsV
  -- `V` is a Klein four-group, hence commutative: `s` and `t` commute.
  have hstc : s * B.t = B.t * s := fourGroup_comm V hfour s hsV B.t htV
  -- hence `s ∈ C_G(t) ≤ N_G(C_G(t))` (a group normalizes itself)
  have hsC : s ∈ Subgroup.centralizer ({B.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hstc
  have hsNC : s ∈ Subgroup.normalizer ((Subgroup.centralizer ({B.t} : Set G)) : Set G) :=
    (Subgroup.le_normalizer (H := Subgroup.centralizer ({B.t} : Set G))) hsC
  -- ## `K = C_A(t) = A ⊓ C_G(t)`
  set K : Subgroup G := A ⊓ Subgroup.centralizer ({B.t} : Set G) with hKdef
  -- `s` normalizes `K` (it normalizes both factors)
  have hsNK : s ∈ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact normalizer_inf_le A _ ⟨hsNA, hsNC⟩
  have hsNK' : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hsNK
  have hKodd : Odd (Nat.card K) := by
    rw [hKdef]
    exact odd_card_of_le inf_le_left hAodd
  have hKcop : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hKodd
  -- ## `⟨s⟩` is a `2`-group
  have hs2 : s ^ 2 = 1 := hfour.2 s hsV
  have hisP : IsPGroup 2 (Subgroup.zpowers s) := by
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  -- ## Bender 1.1(i): the commutator `X := [⟨s⟩, C_A(t)]` is `⟨s⟩`-invariant
  have hc11i := T.c11i G 2 (Subgroup.zpowers s) K hisP hKcop hsNK'
  set X : Subgroup G := ⁅Subgroup.zpowers s, K⁆ with hXdef
  have hXeq : ⁅Subgroup.zpowers s, X⁆ = X := by rw [hXdef]; exact hc11i.1
  have hXK : X ≤ K := by rw [hXdef]; exact le_trans le_sup_left hc11i.2.le
  have hXA : X ≤ A := le_trans hXK inf_le_left
  have hXH : X ≤ B.H := le_trans hXK inf_le_right
  have hXne : X ≠ ⊥ := by rw [hXdef, hKdef]; exact hgood
  have hXodd : Odd (Nat.card X) := odd_card_of_le hXA hAodd
  -- ## the odd subgroup `X` of `C(t) = H` lies in `U = O(H)`
  have hXU : X ≤ B.U := L27su_odd_subgroup_le_U T hctx B X hXH hXodd
  -- ## Bender's hypothesis: `t ∈ O₂(N_G(X))`, whence `t` centralizes `N_A(X)`
  have hcent : Subgroup.normalizer (X : Set G) ⊓ A ≤ Subgroup.centralizer ({B.t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyNX, hyA⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    set P : Subgroup G := Work.GW2.pCoreIn 2 (Subgroup.normalizer (X : Set G)) with hPdef
    have htP : B.t ∈ P := hhyp s X hsS hXU hXne hXeq
    -- `[y,t]` lies in `O₂(N_G(X))` …
    have hcommP : B.t * y * B.t⁻¹ * y⁻¹ ∈ P := by
      have hconj : y * B.t * y⁻¹ ∈ P := conj_mem_pCoreIn hyNX htP
      have h2 : (y * B.t * y⁻¹)⁻¹ ∈ P := P.inv_mem hconj
      have h3 : y * B.t⁻¹ * y⁻¹ ∈ P := by
        rw [show (y * B.t * y⁻¹)⁻¹ = y * B.t⁻¹ * y⁻¹ from by group] at h2
        exact h2
      have h4 : B.t * (y * B.t⁻¹ * y⁻¹) ∈ P := P.mul_mem htP h3
      rwa [show B.t * (y * B.t⁻¹ * y⁻¹) = B.t * y * B.t⁻¹ * y⁻¹ from by group] at h4
    -- … and in `A` (`t` normalizes `A` and `y ∈ A`)
    have hconjA : B.t * y * B.t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htNA y).mp hyA
    have hcommA : B.t * y * B.t⁻¹ * y⁻¹ ∈ A := A.mul_mem hconjA (A.inv_mem hyA)
    -- so it lies in `O₂(N_G(X)) ⊓ A = ⊥` (as `A` has odd order)
    have hbot : B.t * y * B.t⁻¹ * y⁻¹ = 1 := by
      have hmem : B.t * y * B.t⁻¹ * y⁻¹ ∈ (P ⊓ A) := ⟨hcommP, hcommA⟩
      rw [hPdef, pCoreIn_inf_eq_bot_of_odd (Subgroup.normalizer (X : Set G)) A hAodd] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hty : y * B.t = B.t * y := by
      have h : B.t * y * B.t⁻¹ = y := (mul_inv_eq_one).mp hbot
      calc y * B.t = (B.t * y * B.t⁻¹) * B.t := by rw [h]
        _ = B.t * y := by group
    exact hty
  -- ## the normalizer tower of `X` inside the nilpotent `A` reaches `A` (Bender 1.1(iv))
  have hAleC : A ≤ Subgroup.centralizer ({B.t} : Set G) :=
    L29_tower T.c11iv A hAnil hAodd B.t B.t_order htNA X hXA hcent
  -- ## contradiction: `t` centralizes `A`
  apply hAcen
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAleC ha)

theorem L29_case_i_good {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (V N A : Subgroup G)
    (h : Work.CORE2B.L29Hyp B V N)
    (hAN : A ≤ N) (hAnorm : (A.subgroupOf N).Normal) (hAodd : Odd (Nat.card A))
    (hAnil : Group.IsNilpotent ↥A) (hAcen : B.t ∉ Subgroup.centralizer (A : Set G))
    (s : G) (hsV : s ∈ V) (hst : s ≠ B.t)
    (hgood : ⁅Subgroup.zpowers s, (A ⊓ Subgroup.centralizer ({B.t} : Set G))⁆ ≠ ⊥) : False := by
  -- `A ◁ N` and `V ≤ N` give `V ≤ N_G(A)`; everything else is the general form.
  exact L29_case_i_good_general T hctx B V A h.V_le_S h.t_mem h.four h.hyp hAnil hAodd
    (h.V_le_N.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mp hAnorm))
    hAcen s hsV hgood

end Work.CORE2B
