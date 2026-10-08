import Mathlib
import Submission.Work.BrauerSuzuki.Dade.defs
import Submission.Work.BrauerSuzuki.Dade.complement_and_sqrtSet
import Submission.Work.BrauerSuzuki.Dade.complement_hom
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical
open scoped Pointwise

/-- An element `z` of the generalized quaternion group `↥S` with `z ^ 2 = 1` is either `1` or
the unique involution `τ ^ (2 ^ (n-1))`. -/
private lemma eq_one_or_eq_halfpow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {z : ↥S} (hz : z ^ 2 = 1) :
    z = 1 ∨ z = d.tau ^ (2 ^ (d.n - 1)) := by
  by_cases h : z = 1
  · exact Or.inl h
  · right
    have hord : orderOf z = 2 := by
      have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) h
      · exact h1
    exact (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).2.2.2.1 z hord

/-- Every involution of `G` is conjugate to `ι`, the unique involution of the generalized
quaternion Sylow `2`-subgroup `S`. -/
theorem isConj_iota {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {t : G} (ht : orderOf t = 2) :
    IsConj t (iota S d) := by
  obtain ⟨T, htT⟩ := Work.BrauerSuzuki.Group.exists_sylow_mem_of_orderOf_eq_two ht
  obtain ⟨c, hc⟩ := (Sylow.isPretransitive_of_finite (p := 2) (G := G)).exists_smul_eq T S
  have hsub : (MulAut.conj c • (T : Subgroup G)) = (S : Subgroup G) := by
    rw [← Sylow.pointwise_smul_def (g := MulAut.conj c) (P := T), ← Sylow.smul_def, hc]
  have hmem : c * t * c⁻¹ ∈ (S : Subgroup G) := by
    have h0 : (MulAut.conj c) • t ∈ (S : Subgroup G) := by
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul t (MulAut.conj c) (T : Subgroup G) htT
    simpa [MulAut.smul_def, MulAut.conj_apply] using h0
  have hord : orderOf (c * t * c⁻¹) = 2 := by
    rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, ht]
  have hkey : c * t * c⁻¹ = iota S d := eq_iota_of_mem_sylow_of_orderOf_eq_two S d hmem hord
  rw [isConj_iff]
  exact ⟨c, hkey⟩

/-- **The involutions of `H = N_G(⟨σ⟩)` and of the TI set `√σ`** (Dade's Proposition 6.2 and
Corollary 5.22, in the form used in Theorem 6.8).  All five statements hold with the same
hypotheses:

1. every involution of `H = N_G(⟨σ⟩)` is `ι`;
2. `ι` is fixed by every element of `H`;
3. `ι ∉ √σ`;
4. `√σ` contains no involution;
5. a product of two involutions of `G` never lies in `√σ`. -/
theorem involution_structure {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) :
    (∀ x : G, x ∈ Hsub S d → orderOf x = 2 → x = iota S d) ∧
    (∀ h : G, h ∈ Hsub S d → h * iota S d * h⁻¹ = iota S d) ∧
    (iota S d ∉ Work.BrauerSuzuki.sqrtSet (sigma S d)) ∧
    (∀ x : G, x ∈ Work.BrauerSuzuki.sqrtSet (sigma S d) → orderOf x ≠ 2) ∧
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 →
        u * v ∉ Work.BrauerSuzuki.sqrtSet (sigma S d)) := by
  -- `2 ^ (n-1) ≤ 4` fails because `n ≥ 3`
  have hbig : ¬ (2 ^ (d.n - 1) ≤ 2) := by
    have h4 : 4 ≤ 2 ^ (d.n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (d.n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- the normal complement `K` of `Lemma 6.9`
  obtain ⟨K, hKC, hKN, hKodd, hKcent, hKS, hKSup, hKtv⟩ :=
    exists_normal_complement_centralizer S d hn
  have hHK : K ≤ Hsub S d := by
    have h : Hsub S d = K ⊔ (S : Subgroup G) := hKSup.symm
    rw [h]
    exact le_sup_left
  have hSH : (S : Subgroup G) ≤ Hsub S d := sylow_le_normalizer S d
  have hKn : ∀ k ∈ K, ∀ h ∈ Hsub S d, h * k * h⁻¹ ∈ K := fun k hk h hh =>
    (Subgroup.mem_normalizer_iff.mp (hKN hh) k).mp hk
  obtain ⟨φ, hφS, hφker, -, hφdec⟩ :=
    complement_hom (S : Subgroup G) K (Hsub S d) hHK hSH hKS hKSup hKn
  -- every involution of `H` is `ι`
  have hEqIota : ∀ x : G, x ∈ Hsub S d → orderOf x = 2 → x = iota S d := by
    intro x hx hx2
    have hxsq : x * x = 1 := by
      have h : x ^ 2 = (1 : G) := by
        rw [show (2 : ℕ) = orderOf x from hx2.symm]
        exact pow_orderOf_eq_one x
      simpa [pow_two] using h
    have hφsq : ((φ ⟨x, hx⟩) : ↥S) ^ 2 = 1 := by
      have h : (φ ⟨x, hx⟩ : ↥S) * φ ⟨x, hx⟩ = 1 := by
        rw [← map_mul]
        have hmul : (⟨x, hx⟩ : ↥(Hsub S d)) * ⟨x, hx⟩ = 1 := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_one]
          exact hxsq
        rw [hmul, map_one]
      simpa [pow_two] using h
    rcases eq_one_or_eq_halfpow S d hφsq with h1 | h2
    · -- `φ x = 1`: then `x ∈ K`, so `2 ∣ |K|`, contradicting `|K|` odd
      exfalso
      have hxK : x ∈ K := (hφker ⟨x, hx⟩).mp h1
      have hdiv : orderOf x ∣ Nat.card K := by
        have h := orderOf_dvd_natCard (⟨x, hxK⟩ : ↥K)
        rwa [← Subgroup.orderOf_coe (⟨x, hxK⟩ : ↥K)] at h
      have h2dvd : 2 ∣ Nat.card K := by rw [← hx2]; exact hdiv
      obtain ⟨m, hm⟩ := hKodd
      obtain ⟨t, ht⟩ := h2dvd
      omega
    · -- `φ x = τ ^ (2^(n-1))`: write `x = ι * k` and get `k ^ 2 = 1`, hence `k = 1`
      obtain ⟨k, hkK, hkdec⟩ := hφdec ⟨x, hx⟩
      have hkdec' : x = ((φ ⟨x, hx⟩ : ↥S) : G) * k := hkdec
      have hxeq : x = iota S d * k := by
        rw [h2] at hkdec'
        simpa [iota_def, Subgroup.coe_pow] using hkdec'
      have hcomm : k * iota S d = iota S d * k := by
        have hc : Commute k (sigma S d) := hKcent k hkK
        rw [iota_eq_sigma_zpow S d hn]
        exact (hc.pow_right (2 ^ (d.n - 2))).eq
      have hksq : k ^ 2 = 1 := by
        have h1 : (iota S d * k) * (iota S d * k) = k * k := by
          calc (iota S d * k) * (iota S d * k)
              = iota S d * (k * iota S d) * k := by group
            _ = iota S d * (iota S d * k) * k := by rw [hcomm]
            _ = (iota S d * iota S d) * (k * k) := by group
            _ = k * k := by rw [← pow_two, iota_sq S d, one_mul]
        rw [pow_two, ← h1, ← hxeq, hxsq]
      have hk1 : k = 1 := by
        have hdvd : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hksq
        have hdivK : orderOf k ∣ Nat.card K := by
          have h := orderOf_dvd_natCard (⟨k, hkK⟩ : ↥K)
          rwa [← Subgroup.orderOf_coe (⟨k, hkK⟩ : ↥K)] at h
        have hcop : orderOf k ∣ 1 := by
          have h1 : orderOf k ∣ Nat.gcd 2 (Nat.card K) := Nat.dvd_gcd hdvd hdivK
          rwa [show Nat.gcd 2 (Nat.card K) = 1 from Nat.coprime_two_left.mpr hKodd] at h1
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hcop)
      rw [hxeq, hk1, mul_one]
  refine ⟨hEqIota, ?_, ?_, ?_, ?_⟩
  · intro h hh
    have hmem : h * iota S d * h⁻¹ ∈ Subgroup.zpowers (sigma S d) :=
      (Subgroup.mem_normalizer_iff.mp hh (iota S d)).mp (iota_mem_zpowers_sigma S d hn)
    have hmemH : h * iota S d * h⁻¹ ∈ Hsub S d :=
      Subgroup.le_normalizer (H := Subgroup.zpowers (sigma S d)) hmem
    have hord : orderOf (h * iota S d * h⁻¹) = 2 := by
      rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, orderOf_iota]
    exact hEqIota _ hmemH hord
  · intro hi
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hi
    have hdiv : orderOf (sigma S d) ∣ orderOf (iota S d) := by
      rw [← Nat.card_zpowers (sigma S d), ← Nat.card_zpowers (iota S d)]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hi)
    rw [orderOf_iota S d, orderOf_sigma S d] at hdiv
    exact hbig (Nat.le_of_dvd (by norm_num) hdiv)
  · intro x hx hx2
    rw [Work.BrauerSuzuki.mem_sqrtSet] at hx
    have hdiv : orderOf (sigma S d) ∣ orderOf x := by
      rw [← Nat.card_zpowers (sigma S d), ← Nat.card_zpowers x]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
    rw [orderOf_sigma S d, hx2] at hdiv
    exact hbig (Nat.le_of_dvd (by norm_num) hdiv)
  · intro u v hu hv huv
    rw [Work.BrauerSuzuki.mem_sqrtSet] at huv
    -- `u` and `v` normalize `⟨σ⟩`, hence are involutions of `H`, hence equal `ι`
    have hmem_of : ∀ w z : G, orderOf w = 2 → orderOf z = 2 →
        w * z ∈ Work.BrauerSuzuki.sqrtSet (sigma S d) → w = iota S d := by
      intro w z hw hz hwz
      rw [Work.BrauerSuzuki.mem_sqrtSet] at hwz
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwz
      have hw2 : w * w = 1 := by
        have h := pow_orderOf_eq_one w
        rw [hw] at h
        simpa [pow_two] using h
      have hzz : z⁻¹ = z := by
        refine (inv_eq_iff_mul_eq_one).mpr ?_
        have h := pow_orderOf_eq_one z
        rw [hz] at h
        simpa [pow_two] using h
      have hconj : w * (w * z) * w⁻¹ = (w * z)⁻¹ := by
        calc w * (w * z) * w⁻¹ = (w * w) * (z * w⁻¹) := by group
          _ = z * w⁻¹ := by rw [hw2, one_mul]
          _ = z⁻¹ * w⁻¹ := by rw [hzz]
          _ = (w * z)⁻¹ := (mul_inv_rev w z).symm
      have h1 : w * (w * z) ^ j * w⁻¹ = ((w * z) ^ j)⁻¹ := by
        rw [← MulAut.conj_apply w ((w * z) ^ j), map_zpow (MulAut.conj w) (w * z) j,
          MulAut.conj_apply w (w * z), hconj, inv_zpow]
      rw [hj] at h1
      have hmap : (Subgroup.zpowers (sigma S d)).map (MulAut.conj w).toMonoidHom
          = Subgroup.zpowers (sigma S d) := by
        have h2 : (MulAut.conj w) (sigma S d) = (sigma S d)⁻¹ := by
          rw [MulAut.conj_apply]; exact h1
        rw [MonoidHom.map_zpowers]
        show Subgroup.zpowers ((MulAut.conj w) (sigma S d)) = Subgroup.zpowers (sigma S d)
        rw [h2, Subgroup.zpowers_inv]
      exact hEqIota w (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap) hw
    have hu' : u = iota S d := hmem_of u v hu hv huv
    have hv' : v = iota S d := by
      have hvu : v * u ∈ Work.BrauerSuzuki.sqrtSet (sigma S d) := by
        have hu_inv : u⁻¹ = u := by
          refine (inv_eq_iff_mul_eq_one).mpr ?_
          have h := pow_orderOf_eq_one u
          rw [hu] at h
          simpa [pow_two] using h
        have hv_inv : v⁻¹ = v := by
          refine (inv_eq_iff_mul_eq_one).mpr ?_
          have h := pow_orderOf_eq_one v
          rw [hv] at h
          simpa [pow_two] using h
        have hvu_eq : v * u = (u * v)⁻¹ := by
          rw [mul_inv_rev, hu_inv, hv_inv]
        rw [hvu_eq, Work.BrauerSuzuki.mem_sqrtSet, Subgroup.zpowers_inv]
        exact huv
      exact hmem_of v u hv hu hvu
    have huv1 : u * v = 1 := by rw [hu', hv', ← pow_two, iota_sq S d]
    rw [huv1] at huv
    exact one_notMem_sqrtSet S d hn huv

end Work.BrauerSuzuki.Dade
