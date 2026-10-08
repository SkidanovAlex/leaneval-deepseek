import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.VUCardTwelve
import Submission.Work.CORE3.OrderThreeLeCentralizer

namespace Work.CORE3

open Subgroup Work.GW2

set_option linter.style.haveILetI false

/-- In a group, if `w` has order `2`, then every element of `⟨w⟩` is `1` or `w`.
(The order-`3` companion of this is `Work.CORE3.mem_zpowers_of_orderOf_three`.) -/
private lemma mem_zpow_orderOf_two {G : Type*} [Group G] {w z : G} (hw : orderOf w = 2)
    (hz : z ∈ Subgroup.zpowers w) : z = 1 ∨ z = w := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hmod : w ^ (k % (2 : ℤ)) = z := by
    have h := zpow_mod_orderOf w k
    rw [hw] at h
    rw [← hk]
    exact h
  have h0 : 0 ≤ k % (2 : ℤ) := Int.emod_nonneg k (by norm_num)
  have h2 : k % (2 : ℤ) < 2 := Int.emod_lt_of_pos k (by norm_num)
  rcases (by omega : k % (2 : ℤ) = 0 ∨ k % (2 : ℤ) = 1) with h | h
  · left; rw [← hmod, h]; simp
  · right; rw [← hmod, h]; simp

/-- If `g` conjugates `x` to itself then `g` commutes with `x`. -/
private lemma mul_eq_of_conj_eq {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    g * x = x * g := by
  have := congrArg (· * g) h
  simpa [mul_assoc] using this

/-- In the `Case1bData` setting (`Case1 B`, `V = O₂(Ĥ)` a four-group, `|S| = 8`) with
`|U| = |O(Ĥ)| = 3`, every involution of `G` centralizing `U = O(Ĥ)` lies in `V = O₂(Ĥ)`.

Route (all ingredients are in the workspace and axiom-clean):
* `C_Ĥ(U) := C_G(U) ⊓ Ĥ` has index `2` in `Ĥ`: for `h ∈ Ĥ`, take a generator `x` of `U`
  (`|U| = 3` makes `U` cyclic); `h * x * h⁻¹ ∈ U` has order `3`, hence `h * x * h⁻¹ = x` or
  `x⁻¹ = x * x`, so `h` centralizes `U` or inverts `x` (hence all of `U = ⟨x⟩`).  The index is
  not `1`: if `Ĥ ≤ C_G(U)` then `S ≤ C_G(U)` and Theorem 2.6
  (`Work.CORE2A.thm26Concl_centralizer_eq h26 : B.S ⊓ C_G(U) = O₂(Ĥ)`) would give `V = S`,
  contradicting `|S| = 8 ≠ 4 = |V|` (`D.S8`, `D.four.1`).
  With `Subgroup.relIndex_dvd_two_iff` this yields `C_Ĥ(U).relIndex B.Hhat = 2`, and
  `Subgroup.relIndex_mul_card` plus `|Ĥ| = 72` (`I.h26`, `D.four`, `hU3`, `relIndex_VU_Hhat`,
  which needs `h1`) give `Nat.card ↥C_Ĥ(U) = 36`.
* `V ≤ C_Ĥ(U)` (Theorem 2.6 again), `V` is normal in `Ĥ` (`le_normalizer_map_subtype`), and
  `|V| = 4`.  If an involution `w ∈ C_Ĥ(U)` lay outside `V`, then `⟨w⟩ ⊓ V = ⊥` and, since
  `⟨w⟩ ≤ C_Ĥ(U) ≤ N_G(V)`, `Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot` gives
  `|V ⊔ ⟨w⟩| = 4 * 2 = 8`, contradicting Lagrange (`Nat.card ↥(V ⊔ ⟨w⟩) ∣ 36`).
* Finally `C_G(U) ≤ N_G(U) = Ĥ` (via `Work.CORE2A.normalizer_eq_of_coatom`, `B.Hhat_coatom`,
  `I.h26`), so the hypothesis `w ∈ C_G(U)` may be read as `w ∈ Ĥ`. -/
theorem InvolutionMemVOfMemCentralizer {G : Type} [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {w : G} (hw2 : w * w = 1) (hwC : w ∈ Subgroup.centralizer (B.U : Set G)) :
    w ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  classical
  haveI : IsSimpleGroup G := hBc.simple
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVS : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G)
      = Work.GW2.pCoreIn 2 B.Hhat := h26.2.1
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVleH : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUne : B.U ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot B.U).mp (by rw [hU3]; norm_num)
  -- `Ĥ ≤ N_G(U)`: `U = O(Ĥ)` is normal in `Ĥ`.
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h : B.Hhat ≤ Subgroup.normalizer
        (↑(Subgroup.map B.Hhat.subtype (Work.GW2.oddCore ↥B.Hhat)) : Set G) :=
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    have hUeq : (Subgroup.map B.Hhat.subtype (Work.GW2.oddCore ↥B.Hhat) : Subgroup G) = B.U :=
      h26.1
    rwa [hUeq] at h
  -- `N_G(U) = Ĥ` (coatom maximality, `U ≠ 1`), so the hypothesis `w ∈ C_G(U)` gives `w ∈ Ĥ`.
  have hNU : Subgroup.normalizer (B.U : Set G) = B.Hhat :=
    Work.CORE2A.normalizer_eq_of_coatom B.Hhat_coatom hUleH hUne hUnorm
  have hwH : w ∈ B.Hhat := by
    rw [← hNU]
    exact Subgroup.centralizer_le_normalizer (B.U : Set G) hwC
  -- `V = O₂(Ĥ) ⊴ Ĥ`.
  have hVnorm : B.Hhat ≤ Subgroup.normalizer (↑(Work.GW2.pCoreIn 2 B.Hhat) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  -- Pick a generator `x` of the cyclic group `U` of order `3`.
  obtain ⟨x₀, hx₀ne⟩ : ∃ a : ↥B.U, a ≠ 1 := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  set x : G := (x₀ : G) with hxdef
  have hxU : x ∈ B.U := x₀.2
  have hx1 : x ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  have hx3 : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hU3]; exact Subgroup.orderOf_dvd_natCard B.U hxU
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzp : Subgroup.zpowers x = B.U :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxU)
      (by rw [Nat.card_zpowers, hx3]; omega)
  -- `Cx = C_Ĥ(x) = C_G(⟨x⟩) ⊓ Ĥ = C_G(U) ⊓ Ĥ`.
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ B.Hhat with hCxdef
  have hCxmem : ∀ z : G, z ∈ Cx ↔ z ∈ B.Hhat ∧ z * x = x * z := by
    intro z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
      exact ⟨hz2, Subgroup.mem_centralizer_singleton_iff.mp hz1⟩
    · rintro ⟨hzH, hzx⟩
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzx, hzH⟩
  -- Conjugation by an element of `Ĥ` sends `x` to `x` or to `x ^ 2 = x⁻¹`.
  have hconj : ∀ g ∈ B.Hhat, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x ^ 2 := by
    intro g hg
    have hmem : g * x * g⁻¹ ∈ B.U :=
      (Subgroup.mem_normalizer_iff.mp (hUnorm hg) x).mp hxU
    have hord : orderOf (g * x * g⁻¹) = 3 := by
      have hsem : SemiconjBy g x (g * x * g⁻¹) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq g hsem).symm.trans hx3
    rw [← hzp] at hmem
    rcases Work.CORE3.mem_zpowers_of_orderOf_three hx3 hmem with h1 | h1 | h1
    · rw [h1] at hord
      simp only [orderOf_one] at hord
      omega
    · exact Or.inl h1
    · exact Or.inr h1
  have hVleCGU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← hVS]; exact inf_le_right
  -- The index of `Cx` in `Ĥ` is not `1`.
  have hnotle : ¬ (B.Hhat ≤ Cx) := by
    intro hle
    have hSle : (B.S : Subgroup G) ≤ Subgroup.centralizer (B.U : Set G) := by
      intro s hs
      have hsCx : s ∈ Cx := hle (Work.CORE2A.bSetup_S_le_Hhat B hs)
      have hsx : Commute s x := (hCxmem s).mp hsCx |>.2
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [← hzp] at hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (hsx.zpow_right k).eq.symm
    have hSV : (B.S : Subgroup G) ≤ Work.GW2.pCoreIn 2 B.Hhat := by
      have h : (B.S : Subgroup G) ≤ (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) :=
        le_inf le_rfl hSle
      rwa [hVS] at h
    have hVleS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
      have h : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) ≤ (B.S : Subgroup G) :=
        inf_le_left
      rwa [hVS] at h
    have hSeq : (B.S : Subgroup G) = Work.GW2.pCoreIn 2 B.Hhat := le_antisymm hSV hVleS
    have hcard : Nat.card ↥(B.S : Subgroup G) = Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
      rw [hSeq]
    rw [D.S8, D.four.1] at hcard
    exact absurd hcard (by norm_num)
  have hne1 : Cx.relIndex B.Hhat ≠ 1 := fun h1 => hnotle (Subgroup.relIndex_eq_one.mp h1)
  -- The index of `Cx` in `Ĥ` divides `2`.
  have hdvd : Cx.relIndex B.Hhat ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hle : B.Hhat ≤ Cx
    · exact ⟨1, B.Hhat.one_mem, fun b hb => Or.inr (hle hb)⟩
    · have hex : ∃ a ∈ B.Hhat, a ∉ Cx := by
        by_contra h
        apply hle
        intro b hb
        by_contra hbC
        exact h ⟨b, hb, hbC⟩
      obtain ⟨a, haH, haCx⟩ := hex
      have hax : a * x * a⁻¹ = x ^ 2 := by
        rcases hconj a haH with h | h
        · exact absurd (hCxmem a |>.mpr ⟨haH, mul_eq_of_conj_eq h⟩) haCx
        · exact h
      refine ⟨a, haH, fun b hb => ?_⟩
      by_cases hbC : b ∈ Cx
      · exact Or.inr hbC
      · left
        have hbx : b * x * b⁻¹ = x ^ 2 := by
          rcases hconj b hb with h | h
          · exact absurd (hCxmem b |>.mpr ⟨hb, mul_eq_of_conj_eq h⟩) hbC
          · exact h
        rw [hCxmem]
        refine ⟨B.Hhat.mul_mem hb haH, ?_⟩
        -- `b * a` also inverts `x`, hence centralizes it.
        have key : (b * a) * x * (b * a)⁻¹ = x := by
          calc (b * a) * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by group
            _ = b * (x * x) * b⁻¹ := by rw [hax]; simp only [pow_two]
            _ = (b * x * b⁻¹) * (b * x * b⁻¹) := by group
            _ = (x ^ 2) * (x ^ 2) := by rw [hbx]
            _ = x := by
                  rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, ← pow_mod_orderOf x 4, hx3]
                  norm_num
        have key2 : (b * a) * x = x * (b * a) := by
          have := congrArg (· * (b * a)) key
          simpa [mul_assoc] using this
        exact key2
  have hCxrel : Cx.relIndex B.Hhat = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  -- `|Ĥ| = 72`, hence `|Cx| = 72 / 2 = 36`.
  obtain ⟨-, hHhatcard⟩ := Work.CORE3.VUCardTwelve G I hBc B h1 D hU3
  have hCxcard : Nat.card ↥Cx = 36 := by
    have h := Subgroup.relIndex_mul_card Cx B.Hhat
    rw [hCxrel, hHhatcard] at h
    rw [show Cx ⊓ B.Hhat = Cx from inf_eq_left.mpr (inf_le_right : Cx ≤ B.Hhat)] at h
    omega
  have hVleCx : Work.GW2.pCoreIn 2 B.Hhat ≤ Cx := by
    intro v hv
    rw [hCxmem]
    exact ⟨hVleH hv, (Subgroup.mem_centralizer_iff.mp (hVleCGU hv) x hxU).symm⟩
  have hwCx : w ∈ Cx := by
    rw [hCxmem]
    exact ⟨hwH, (Subgroup.mem_centralizer_iff.mp hwC x hxU).symm⟩
  -- Suppose `w ∉ V`: then `V ⊔ ⟨w⟩` is an elementary subgroup of order `8` inside `Cx`, but
  -- `8 ∤ 36`.
  by_contra hwV
  have hw1 : w ≠ 1 := by rintro rfl; exact hwV (Subgroup.one_mem _)
  have hw2' : orderOf w = 2 := by
    have hdvd2 : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hw2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hinf : Work.GW2.pCoreIn 2 B.Hhat ⊓ Subgroup.zpowers w = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzV, hzW⟩ := Subgroup.mem_inf.mp hz
    rcases mem_zpow_orderOf_two hw2' hzW with h1 | h1
    · exact h1
    · exfalso
      exact hwV (by rw [← h1]; exact hzV)
  have hzwN : Subgroup.zpowers w ≤ Subgroup.normalizer (↑(Work.GW2.pCoreIn 2 B.Hhat) : Set G) :=
    Subgroup.zpowers_le.mpr (hVnorm hwH)
  have hcardsup : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ Subgroup.zpowers w) = 8 := by
    rw [Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hzwN hinf, D.four.1,
      Nat.card_zpowers, hw2']
  have hsupCx : Work.GW2.pCoreIn 2 B.Hhat ⊔ Subgroup.zpowers w ≤ Cx :=
    sup_le hVleCx (Subgroup.zpowers_le.mpr hwCx)
  have hdvd8 : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊔ Subgroup.zpowers w) ∣ Nat.card ↥Cx :=
    Subgroup.card_dvd_of_le hsupCx
  rw [hcardsup, hCxcard] at hdvd8
  exact absurd hdvd8 (by norm_num)

end Work.CORE3
