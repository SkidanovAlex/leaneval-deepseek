import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two
import Submission.Work.ThmF.ChV3.Prove.centralizer_odd_mem_twoPoint
import Submission.Work.ThmF.ChV3.Prove.Kset_card_seven
import Submission.Work.ThmF.ChV3.Prove.Ksub_inf_centD_and_card
import Submission.Work.ThmF.ChV3.Prove.exists_mem_mul_of_card_mul_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.cent_Kelem_order3_mem_W` — Peterfalvi II Ch. V §3, step (13), leaf 13b

For `k ∈ K^#` (where `K = J(D,t) = Kset H t`, `D = H ∩ H^t`), every element of order `3` of
`C_G(k)` lies in `W = C_V(K)` (`V = C_D(t)`).

This is the input to step (13) of §3 (`C_G(Z₁)` is a 3-group): an element `x` of order `7`
conjugate into `K^#` has `C_G(x) = K W`, so it cannot centralise a *strongly real* element of
order `3` (`ChV12.lemma4`), which is what step (13) needs.

The proof, in the source's words ("elements of `K^#` have only two fixed points",
`Ch. II §4 Prop. 2 (c)`, and `C_D(K) = K × W`):

* `k ∈ K^#` fixes exactly `H` and `Hᵗ` on `Ω = G ⧸ H` (`ChIIFourProp`), hence `C_G(k)` permutes
  `{H, Hᵗ}`; an element of **odd** order fixing a point of a two-element orbit lies in
  `H ⊓ Hᵗ = D` (`centralizer_odd_mem_twoPoint`).
* `K = J(D,t)` is cyclic of order `2^{|P|} - 1 = 7` here (`Kset_card_seven`), so `k` generates
  `K` and `C_D(k) = C_D(K)`.
* App. I gives `|K| · |V| = |D|` and `K ⊓ V = ⊥` (`Ksub_inf_centD_and_card`), so every
  `y ∈ D` is a product `y = k' v` with `k' ∈ K`, `v ∈ V` (`exists_mem_mul_of_card_eq`).
* `y = k' v` of order `3` commuting with `k` forces `v ∈ C_V(K) = W` (as `k` generates `K`) and
  then `k'³ = 1`, so `k' = 1` (as `|K| = 7` is prime to `3`) and `y = v ∈ W`.

Nothing in this file needs `h15`/`d` beyond the order `7` of `K`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

theorem cent_Kelem_order3_mem_W {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ k ∈ Work.ThmF.Kset H t, k ≠ 1 → ∀ y ∈ Subgroup.centralizer ({k} : Set G),
      orderOf y = 3 → y ∈ Work.ThmF.W H t := by
  intro k hk hk1 y hy hy3
  -- data on `K = J(D,t) = Kset H t`
  obtain ⟨hKsub_eq, _hcyc, hKcard, hgen⟩ := Kset_card_seven hFT hC4 c h15 d
  obtain ⟨hinfKV, hcardKV⟩ := Ksub_inf_centD_and_card hFT hC4 c h15 d
  have hgenK : Subgroup.zpowers k = Work.ThmF.Ksub H t := hgen k hk hk1
  -- `y` has odd order, hence lies in `D = twoPoint H t`
  have hodd : Odd (orderOf y) := by rw [hy3]; exact ⟨1, rfl⟩
  have hyD : y ∈ Submission.Blueprint.twoPoint H t :=
    centralizer_odd_mem_twoPoint c.sit hC4 c.split hk hk1 hy hodd
  have hcomm : y * k = k * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  -- decompose `y = k' * v` with `k' ∈ K`, `v ∈ V = centD H t`
  have hKle : Work.ThmF.Ksub H t ≤ Submission.Blueprint.twoPoint H t :=
    (Subgroup.closure_le _).mpr (Work.ThmF.Kset_subset H t)
  have hVle : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t := inf_le_left
  obtain ⟨k', hk', v, hv, hykv⟩ :=
    exists_mem_mul_of_card_mul_eq hKle hVle hinfKV hcardKV y hyD
  -- `k'` is a power of `k`, so it commutes with `k`
  have hk'gen : k' ∈ Subgroup.zpowers k := by rw [hgenK]; exact hk'
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk'gen
  have hk'k : k' * k = k * k' := by
    rw [← hn]
    exact Commute.zpow_left (Commute.refl k) n
  -- hence `v` commutes with `k`
  have hvk : v * k = k * v := by
    have h1 : k' * (v * k) = k' * (k * v) :=
      calc k' * (v * k) = (k' * v) * k := by group
        _ = y * k := by rw [← hykv]
        _ = k * y := hcomm
        _ = k * (k' * v) := by rw [hykv]
        _ = (k * k') * v := by group
        _ = (k' * k) * v := by rw [hk'k]
        _ = k' * (k * v) := by group
    exact mul_left_cancel h1
  -- since `k` generates `K`, `v` centralises `K`: `v ∈ W = C_V(K)`
  have hvW : v ∈ Work.ThmF.W H t := by
    rw [Work.ThmF.le_W_iff]
    refine ⟨hv, ?_⟩
    intro k₀ hk₀
    have hk₀K : k₀ ∈ Work.ThmF.Ksub H t := hKsub_eq.ge hk₀
    rw [← hgenK] at hk₀K
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk₀K
    rw [← hm]
    exact (Commute.zpow_right hvk m).symm
  have hvk' : k' * v = v * k' :=
    (Work.ThmF.le_W_iff.mp hvW).2 k' (hKsub_eq.le hk')
  -- `y ^ 3 = 1`, `y = k' * v`, `k' v = v k'` give `k' ^ 3 * v ^ 3 = 1`
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hk'3 : k' ^ 3 = 1 := by
    have hmul : k' ^ 3 * v ^ 3 = 1 := by
      rw [← Commute.mul_pow hvk' 3, ← hykv, hy3']
    have hW3 : k' ^ 3 ∈ Work.ThmF.W H t := by
      rw [eq_inv_of_mul_eq_one_left hmul]
      exact (Work.ThmF.W H t).inv_mem ((Work.ThmF.W H t).pow_mem hvW 3)
    have hK3 : k' ^ 3 ∈ Work.ThmF.Ksub H t := (Work.ThmF.Ksub H t).pow_mem hk' 3
    have hbot : Work.ThmF.Ksub H t ⊓ Work.ThmF.W H t = ⊥ := by
      refine le_bot_iff.mp ?_
      calc Work.ThmF.Ksub H t ⊓ Work.ThmF.W H t
          ≤ Work.ThmF.Ksub H t ⊓ Submission.Blueprint.centD H t :=
            inf_le_inf_left _ (Work.ThmF.W_le_centD H t)
        _ = ⊥ := hinfKV
    have := hbot ▸ (Subgroup.mem_inf.mpr ⟨hK3, hW3⟩)
    exact Subgroup.mem_bot.mp this
  -- `|K| = 7` is prime to `3`, so `k' ^ 3 = 1` forces `k' = 1`
  have hk'one : k' = 1 := by
    have hdvd3 : orderOf k' ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hk'3
    have hdvd7 : orderOf k' ∣ 7 := by
      have h := orderOf_dvd_natCard (⟨k', hk'⟩ : ↥(Work.ThmF.Ksub H t))
      rw [← Subgroup.orderOf_coe ⟨k', hk'⟩, hKcard] at h
      exact h
    have h1 : orderOf k' ∣ 1 := by
      simpa using Nat.dvd_gcd hdvd3 hdvd7
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  rw [show y = v from by rw [hykv, hk'one, one_mul]]
  exact hvW

end Work.ThmF.ChV3.Prove
