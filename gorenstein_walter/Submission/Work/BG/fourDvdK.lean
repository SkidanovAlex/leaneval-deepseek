import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.indexOdd
import Submission.Work.BG.nCases
import Submission.Work.BG.isFourGroup_closure_pair
import Submission.Work.BG.fourGroup_centralizer_card
import Submission.Work.BG.exists_odd_mul_of_odd_eq

/-!
# Area BG: `4 ∣ k` for `|S| ≥ 8` (`Work.GW2.C16.FourDvdKProp`)

Bender–Glauberman 1981, p. 207.  For a `BGData G` with `4 ≤ n` we show `4 ∣ k`, where
`k = k₁ + k₂` and `k_i = |H : C_H(t_i)| = C_G(t_i).relIndex H` with `H = C_G(t)`.

The argument:  `V_i := ⟨t, t_i⟩` is a Klein four-group contained in the Sylow 2-subgroup `S`,
and `V_i` is a Sylow 2-subgroup of `C_G(V_i) = H ⊓ C_G(t_i)` (four-groups are
self-centralizing in a dihedral 2-group).  Hence `a_i := [C_G(V_i) : V_i] = |C_G(V_i)|/4` is
odd.  Multiplying the two towers
`V_i ≤ C_G(V_i) ≤ H` and `V_i ≤ S ≤ H` gives
`a_i · k_i = [C_G(V_i) : V_i]·[H : C_G(t_i)] = [S : V_i]·[H : S] = (n/2)·[H:S]`,
and `[H:S]` is odd.  Since `n = 2^j` with `j ≥ 2`, this forces `k_i = (n/2)·m_i` with `m_i`
odd; then `k = (n/2)(m₁ + m₂)` is divisible by `4`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- Arithmetic: if `4 ∣ n` and `m₁, m₂` are odd, then `4 ∣ (n/2)·m₁ + (n/2)·m₂`. -/
private lemma four_dvd_half_mul_add {n m1 m2 : ℕ} (h4 : 4 ∣ n) (h1 : Odd m1) (h2 : Odd m2) :
    4 ∣ (n / 2) * m1 + (n / 2) * m2 := by
  obtain ⟨s1, hs1⟩ := h1
  obtain ⟨s2, hs2⟩ := h2
  obtain ⟨u, hu⟩ := h4
  refine ⟨u * (s1 + s2 + 1), ?_⟩
  rw [hu, hs1, hs2]
  have hdiv : 4 * u / 2 = 2 * u := by omega
  rw [hdiv]
  ring

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem fourDvdK : Work.GW2.C16.FourDvdKProp := by
  intro G _inst _inst2 D hn4
  -- ## Elementary facts about the involutions `t`, `t₁`, `t₂`
  have ht_sq : D.t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one D.t
    rwa [D.t_order] at h
  have ht1_sq : D.t1 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one D.t1
    rwa [D.t1_order] at h
  have ht2_sq : D.t2 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one D.t2
    rwa [D.t2_order] at h
  have ht_ne_one : D.t ≠ 1 := by
    intro h
    have := D.t_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have ht1_ne_one : D.t1 ≠ 1 := by
    intro h
    have := D.t1_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have ht2_ne_one : D.t2 ≠ 1 := by
    intro h
    have := D.t2_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have ht_mem : D.t ∈ Subgroup.zpowers (D.t1 * D.t2) := by rw [← D.gen]; exact D.t_mem
  have hcomm1 : D.t1 * D.t = D.t * D.t1 :=
    commute_of_mem_zpowers_mul (a := D.t1) (b := D.t2) (c := D.t)
      (by simpa [pow_two] using ht1_sq) (by simpa [pow_two] using ht2_sq) ht_mem
      (by simpa [pow_two] using ht_sq)
  have hcomm2 : D.t2 * D.t = D.t * D.t2 := by
    have hm : D.t ∈ Subgroup.zpowers (D.t2 * D.t1) := by
      rw [show D.t2 * D.t1 = (D.t1 * D.t2)⁻¹ from by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2_sq),
              inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht1_sq)]]
      rw [Subgroup.zpowers_inv]
      exact ht_mem
    exact commute_of_mem_zpowers_mul (a := D.t2) (b := D.t1) (c := D.t)
      (by simpa [pow_two] using ht2_sq) (by simpa [pow_two] using ht1_sq) hm
      (by simpa [pow_two] using ht_sq)
  -- ## `t` is central in `S`, so `S ≤ H`
  have hS0C : D.S0 ≤ Subgroup.centralizer ({D.t} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have hsu : s ∈ Subgroup.zpowers (D.t1 * D.t2) := by rw [← D.gen]; exact hs
    exact (commute_of_mem_zpowers hsu ht_mem).symm
  have hSup : D.S0 ⊔ Subgroup.zpowers D.t1 = (D.S : Subgroup G) :=
    sup_zpowers_eq_of_relIndex_eq_two D.S0_le D.S0_index D.t1_mem D.t1_nmem
  have hS_le_H : (D.S : Subgroup G) ≤ D.H := by
    rw [← hSup]
    refine sup_le hS0C ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm1
  -- ## `|S| = 2n`, `n = 2^(j-1)` with `2 ≤ j-1`
  obtain ⟨e0⟩ := D.dih
  have hcardS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e0.toEquiv, DihedralGroup.nat_card]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
  have hj1 : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    have h2n : 2 * D.n = 1 := by rw [← hcardS, hj, h0]; norm_num
    have := D.two_le
    omega
  have hn_pow : D.n = 2 ^ (j - 1) := by
    have h2n : 2 ^ j = 2 * D.n := by rw [← hj, hcardS]
    have h2 : 2 ^ j = 2 * 2 ^ (j - 1) := by
      calc 2 ^ j = 2 ^ ((j - 1) + 1) := by rw [show (j - 1) + 1 = j by omega]
        _ = 2 * 2 ^ (j - 1) := by rw [pow_succ']
    rw [h2] at h2n
    exact (Nat.mul_left_cancel (by norm_num) h2n).symm
  have hj2 : 2 ≤ j - 1 := by
    by_contra h
    have hle : j - 1 ≤ 1 := by omega
    have hp : 2 ^ (j - 1) ≤ 2 := by
      calc 2 ^ (j - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
        _ = 2 := by norm_num
    rw [hn_pow] at hn4
    omega
  have hn2dvd : 2 ∣ D.n := by
    rw [hn_pow]
    refine ⟨2 ^ (j - 2), ?_⟩
    rw [show j - 1 = (j - 2) + 1 by omega, pow_succ']
  have h4dvdn : 4 ∣ D.n := by
    rw [hn_pow, show (4 : ℕ) = 2 ^ 2 from by norm_num]
    refine ⟨2 ^ (j - 1 - 2), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hn_half : 2 * (D.n / 2) = D.n := Nat.mul_div_cancel' hn2dvd
  have hoddSidx : Odd (D.S : Subgroup G).index := by
    have h : ¬ 2 ∣ (D.S : Subgroup G).index := D.S.not_dvd_index
    exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact h)
  have hSrelH_odd : Odd ((D.S : Subgroup G).relIndex D.H) := by
    have hmul := Subgroup.relIndex_mul_index hS_le_H
    exact hoddSidx.of_dvd_nat ⟨D.H.index, hmul.symm⟩
  -- ## the key step for a single involution `c ∈ S ∖ S₀` commuting with `t`
  have key : ∀ c : G, c ∈ (D.S : Subgroup G) → c ∉ D.S0 → c ^ 2 = 1 →
      c * D.t = D.t * c →
      ∃ m : ℕ, Odd m ∧
        (Subgroup.centralizer ({c} : Set G)).relIndex D.H = (D.n / 2) * m := by
    intro c hcS hcnS0 hc_sq hc_comm
    have hc_ne_one : c ≠ 1 := fun h => hcnS0 (h ▸ D.S0.one_mem)
    have ht_ne_c : D.t ≠ c := fun h => hcnS0 (h ▸ D.t_mem)
    -- the Klein four-group `V = ⟨t, c⟩`
    let V : Subgroup G := Subgroup.closure ({D.t, c} : Set G)
    have hV : Work.GW2.IsFourGroup V :=
      isFourGroup_closure_pair ht_sq hc_sq hc_comm.symm ht_ne_one hc_ne_one ht_ne_c
    have hVS : V ≤ (D.S : Subgroup G) := by
      rw [show V = Subgroup.closure ({D.t, c} : Set G) from rfl, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact D.S0_le D.t_mem
      · exact hcS
    -- `C_G(V) = C_G(t) ⊓ C_G(c)`
    have hAV : Subgroup.centralizer (V : Set G)
        = Subgroup.centralizer ({D.t} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) := by
      rw [show (V : Set G) = ↑(Subgroup.closure ({D.t, c} : Set G)) from rfl,
        Subgroup.centralizer_closure]
      ext x
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    -- `a := |C_G(V)|/4` is odd
    obtain ⟨a, ha_odd, ha_card⟩ := fourGroup_centralizer_card D.S e0 hVS hV
    -- `V` lies in its own centralizer
    have hVA : V ≤ Subgroup.centralizer (V : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hv2 : v * v = 1 := by simpa [pow_two] using hV.2 v hv
      have hw2 : w * w = 1 := by simpa [pow_two] using hV.2 w hw
      have hvw2 : (v * w) * (v * w) = 1 := by
        simpa [pow_two] using hV.2 (v * w) (V.mul_mem hv hw)
      have hwvi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
      have hvvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
      have hvwi : (v * w)⁻¹ = v * w := inv_eq_of_mul_eq_one_right hvw2
      calc w * v = w⁻¹ * v⁻¹ := by rw [hwvi, hvvi]
        _ = (v * w)⁻¹ := (mul_inv_rev v w).symm
        _ = v * w := hvwi
    have hCV_le_H : Subgroup.centralizer (V : Set G) ≤ D.H := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hx D.t (Subgroup.subset_closure (by simp))
    -- towers
    have h1 : V.relIndex (Subgroup.centralizer (V : Set G))
        * (Subgroup.centralizer (V : Set G)).relIndex D.H = V.relIndex D.H :=
      Subgroup.relIndex_mul_relIndex V (Subgroup.centralizer (V : Set G)) D.H hVA hCV_le_H
    have h2 : V.relIndex (D.S : Subgroup G) * (D.S : Subgroup G).relIndex D.H
        = V.relIndex D.H :=
      Subgroup.relIndex_mul_relIndex V (D.S : Subgroup G) D.H hVS hS_le_H
    have hVSrel : V.relIndex (D.S : Subgroup G) = D.n / 2 := by
      have h := Subgroup.relIndex_mul_card V (D.S : Subgroup G)
      rw [inf_eq_left.mpr hVS, hV.1, hcardS] at h
      have h' : (D.n / 2) * 4 = 2 * D.n := by
        calc (D.n / 2) * 4 = 2 * (2 * (D.n / 2)) := by ring
          _ = 2 * D.n := by rw [hn_half]
      omega
    have hrelVA : V.relIndex (Subgroup.centralizer (V : Set G)) = a := by
      have h := Subgroup.relIndex_mul_card V (Subgroup.centralizer (V : Set G))
      rw [inf_eq_left.mpr hVA, hV.1, ha_card] at h
      omega
    -- `k_c := C_G(c).relIndex H = C_G(V).relIndex H`
    have hkc : (Subgroup.centralizer ({c} : Set G)).relIndex D.H
        = (Subgroup.centralizer (V : Set G)).relIndex D.H := by
      rw [Subgroup.relIndex, Subgroup.relIndex, hAV]
      congr 1
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    -- combine the towers
    have heq : a * ((Subgroup.centralizer (V : Set G)).relIndex D.H)
        = (D.n / 2) * ((D.S : Subgroup G).relIndex D.H) := by
      have h1' : a * (Subgroup.centralizer (V : Set G)).relIndex D.H = V.relIndex D.H := by
        rw [← hrelVA]; exact h1
      have h2' : (D.n / 2) * (D.S : Subgroup G).relIndex D.H = V.relIndex D.H := by
        rw [← hVSrel]; exact h2
      rw [h1', h2']
    -- arithmetic
    obtain ⟨m, hm_odd, hm⟩ :=
      exists_odd_mul_of_odd_eq (n := D.n) (a := a)
        (k := (Subgroup.centralizer (V : Set G)).relIndex D.H)
        (s := (D.S : Subgroup G).relIndex D.H) ⟨j - 1, hj2, hn_pow⟩ ha_odd hSrelH_odd heq
    exact ⟨m, hm_odd, by rw [hkc, hm]⟩
  -- ## apply to `t₁`, `t₂`
  obtain ⟨m1, hm1_odd, hm1⟩ := key D.t1 D.t1_mem D.t1_nmem ht1_sq hcomm1
  obtain ⟨m2, hm2_odd, hm2⟩ := key D.t2 D.t2_mem D.t2_nmem ht2_sq hcomm2
  have hk_eq : D.k = (D.n / 2) * m1 + (D.n / 2) * m2 := by
    unfold BGData.k
    rw [hm1, hm2]
  rw [hk_eq]
  exact four_dvd_half_mul_add h4dvdn hm1_odd hm2_odd

end Work.BG
