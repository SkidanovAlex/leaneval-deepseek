import Mathlib
import Submission.Work.BSW.Vocab
import Submission.Work.BSW.Api.mem_centralizer_iff

namespace Work.BSW.Char

open Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- Elements of the abelian subgroup `K` commute (in the ambient group). -/
theorem IK_mul_comm_of_mem_K (h : Work.GW2.BSWHyps2 G t s K) {a b : G} (ha : a ∈ K)
    (hb : b ∈ K) : a * b = b * a := by
  have hmc : IsMulCommutative ↥K := Work.BSW.isMulCommutative_K h
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥K) ⟨b, hb⟩)

/-- `s` inverts `K`, so on the right coset we have `k * s = s * k⁻¹`. -/
theorem IK_mul_s_eq_s_mul_inv (h : Work.GW2.BSWHyps2 G t s K) {k : G} (hk : k ∈ K) :
    k * s = s * k⁻¹ := by
  have h1 : s * k⁻¹ = k * s := by
    calc s * k⁻¹ = (s * k⁻¹ * s⁻¹) * s := by group
      _ = (k⁻¹)⁻¹ * s := by rw [Work.BSW.inverts_s_K h k⁻¹ (K.inv_mem hk)]
      _ = k * s := by rw [inv_inv]
  exact h1.symm

/-- Every element of the coset `sK` is an involution. -/
theorem IK_orderOf_smul_mem_K (h : Work.GW2.BSWHyps2 G t s K) {k : G} (hk : k ∈ K) :
    orderOf (s * k) = 2 := by
  have hks : k * s = s * k⁻¹ := IK_mul_s_eq_s_mul_inv h hk
  have hsq : s * k * (s * k) = 1 := by
    calc s * k * (s * k) = s * (k * s) * k := by group
      _ = s * (s * k⁻¹) * k := by rw [hks]
      _ = (s * s) * k⁻¹ * k := by group
      _ = k⁻¹ * k := by rw [Work.BSW.s_mul_self h, one_mul]
      _ = 1 := inv_mul_cancel k
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hsq) ?_
  intro h1
  exact Work.BSW.s_notMem_K h (by
    have h2 : s = k⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]; exact K.inv_mem hk)

/-- Every element `s * k` of the coset `sK` inverts every element of `K`. -/
theorem IK_smul_inverts_mem_K (h : Work.GW2.BSWHyps2 G t s K) {x k : G} (hxK : x ∈ K)
    (hk : k ∈ K) : (s * k)⁻¹ * x * (s * k) = x⁻¹ := by
  have hsk : (s * k)⁻¹ = k⁻¹ * s := by rw [mul_inv_rev, Work.BSW.s_inv h]
  rw [hsk]
  have hsx : s * x * s = x⁻¹ := by
    have hh := Work.BSW.inverts_s_K h x hxK
    rwa [Work.BSW.s_inv h] at hh
  calc k⁻¹ * s * x * (s * k) = k⁻¹ * (s * x * s) * k := by group
    _ = k⁻¹ * x⁻¹ * k := by rw [hsx]
    _ = x⁻¹ := by
        have hc : k⁻¹ * x⁻¹ = x⁻¹ * k⁻¹ :=
          IK_mul_comm_of_mem_K h (K.inv_mem hk) (K.inv_mem hxK)
        rw [hc, mul_assoc, inv_mul_cancel, mul_one]

/-- If `u` inverts a nontrivial `x ∈ K`, then `u ∈ C_G(t)`: the TI condition applied to `u⁻¹`. -/
theorem IK_mem_centralizer_of_inverts (h : Work.GW2.BSWHyps2 G t s K) {x u : G} (hxK : x ∈ K)
    (hx1 : x ≠ 1) (hu : u⁻¹ * x * u = x⁻¹) : u ∈ Subgroup.centralizer ({t} : Set G) := by
  by_contra huc
  have huc' : u⁻¹ ∉ Subgroup.centralizer ({t} : Set G) := by
    intro hh
    exact huc (by simpa using (Subgroup.centralizer ({t} : Set G)).inv_mem hh)
  have hbot := Work.BSW.TI h u⁻¹ huc'
  have hxinv : x⁻¹ ∈ Work.GW2.conjSub u⁻¹ K := by
    rw [Work.GW2.conjSub, Subgroup.mem_map]
    refine ⟨x, hxK, ?_⟩
    show MulAut.conj u⁻¹ x = x⁻¹
    rw [MulAut.conj_apply, inv_inv]
    exact hu
  have hxconj : x ∈ Work.GW2.conjSub u⁻¹ K := by
    simpa using (Work.GW2.conjSub u⁻¹ K).inv_mem hxinv
  have hxmem : x ∈ K ⊓ Work.GW2.conjSub u⁻¹ K := ⟨hxK, hxconj⟩
  rw [hbot] at hxmem
  exact hx1 (Subgroup.mem_bot.mp hxmem)

/-- An involution of `C_G(t)` inverting `x ∈ K`, `x ≠ 1`, `x ≠ t`, lies in the coset `sK`. -/
theorem IK_exists_eq_smul_of_mem_centralizer_inverts (h : Work.GW2.BSWHyps2 G t s K) {x u : G}
    (huC : u ∈ Subgroup.centralizer ({t} : Set G)) (_hu2 : orderOf u = 2)
    (hu : u⁻¹ * x * u = x⁻¹) (hxK : x ∈ K) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ k ∈ K, u = s * k := by
  rcases (Work.BSW.Api.mem_centralizer_iff h u).mp huC with huK | ⟨k, hk, hk'⟩
  · exfalso
    have hux : u⁻¹ * x * u = x := by
      have hc : u⁻¹ * x = x * u⁻¹ := IK_mul_comm_of_mem_K h (K.inv_mem huK) hxK
      rw [hc, mul_assoc, inv_mul_cancel, mul_one]
    rw [hux] at hu
    have hxx : x * x = 1 := mul_eq_one_iff_eq_inv.mpr hu
    rcases Work.BSW.involution_mem_K h hxK hxx with hx | hx
    · exact hx1 hx
    · exact hxt hx
  · exact ⟨k⁻¹, K.inv_mem hk, by rw [hk']; exact IK_mul_s_eq_s_mul_inv h hk⟩

end Helpers

/-- For `x ∈ K` with `x ≠ 1` and `x ≠ t`: the involutions inverting `x` are exactly the elements
of the coset `sK` (every element of `sK` is an involution, and `s` inverts `K`), so `i(x) = |K|`.

Indeed if the involution `u` inverts `x ≠ 1`, then `x⁻¹ = u⁻¹ * x * u ∈ u⁻¹ K u`, so
`x ∈ K ⊓ conjSub u⁻¹ K ≠ ⊥`, and the TI condition gives `u ∈ C_G(t) = K ∪ sK`; the only involution
of `K` is `t`, which does not invert `x ≠ t`. -/
theorem iFn_eq_card_of_mem_K {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    Work.BSW.iFn G x = Nat.card ↥K := by
  -- Step 1: the involutions inverting `x` are exactly the elements of the coset `sK`.
  have hset : {u : G | orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹}
      = {u : G | ∃ k ∈ K, u = s * k} := by
    ext u
    constructor
    · intro hu
      obtain ⟨hu2, huinv⟩ := hu
      obtain ⟨k, hk, hku⟩ := IK_exists_eq_smul_of_mem_centralizer_inverts h
        (IK_mem_centralizer_of_inverts h hxK hx1 huinv) hu2 huinv hxK hx1 hxt
      exact ⟨k, hk, hku⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨IK_orderOf_smul_mem_K h hk, IK_smul_inverts_mem_K h hxK hk⟩
  -- Step 2: the coset `sK` has exactly `|K|` elements.
  have hcard : {u : G | ∃ k ∈ K, u = s * k}.ncard = Nat.card ↥K := by
    have key : (Set.univ : Set ↥K).ncard = {u : G | ∃ k ∈ K, u = s * k}.ncard :=
      Set.ncard_congr (fun k _ => s * (k : G))
        (fun k _ => ⟨(k : G), k.2, rfl⟩)
        (fun a b _ _ hab => Subtype.ext (mul_left_cancel hab))
        (fun u hu => by
          obtain ⟨k, hk, rfl⟩ := hu
          exact ⟨⟨k, hk⟩, Set.mem_univ _, rfl⟩)
    rw [← key]
    exact Set.ncard_univ ↥K
  rw [Work.BSW.iFn, hset]
  exact hcard

end Work.BSW.Char
