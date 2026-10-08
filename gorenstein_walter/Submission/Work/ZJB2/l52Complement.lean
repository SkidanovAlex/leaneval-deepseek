import Mathlib
import Submission.Work.ZJB2.Defs

/-!
# gorenstein_walter — `ZJB2.l52Complement`

If `T` is a Sylow `p`-subgroup of the finite group `X` lying in the centre of `X`, then `X` splits
as a direct product `X = K × T` where `K` is the normal Hall `p'`-subgroup of `X`, i.e. the
subgroup of all elements of order coprime to `p`.

The proof is short given the library: `T ≤ Z(X)` makes `T` normal; `|T|` is a `p`-power while
`[X : T]` is coprime to `p`, so `T` has order coprime to its index and Schur–Zassenhaus
(`Subgroup.exists_right_complement'_of_coprime`) supplies a complement `K`.  Because `T` is
central, `K` is normal, and since every element is uniquely `t * k` with `t` commuting past `k`,
an element lies in `K` exactly when its order is coprime to `p`.
-/

namespace Work.ZJB2

open Subgroup

/-- `p ^ n` is coprime to `p` only for `n = 0`. -/
private theorem coprime_pow_prime_self {p n : ℕ} (hp : p.Prime) (h : Nat.Coprime (p ^ n) p) :
    n = 0 := by
  by_contra hn
  have hdvd : p ∣ p ^ n := dvd_pow_self p hn
  have hgcd : (p ^ n).gcd p = 1 := Nat.coprime_iff_gcd_eq_one.mp h
  have : p ∣ 1 := by rw [← hgcd]; exact Nat.dvd_gcd hdvd (dvd_refl p)
  exact hp.ne_one (Nat.dvd_one.mp this)

/-- The complement of a central subgroup is normal: for `g = p * q` with `p ∈ H ≤ Z(G)`,
`q ∈ K`, one has `g * k * g⁻¹ = q * k * q⁻¹ ∈ K`. -/
private theorem complement_normal_of_le_center {G : Type*} [Group G] {H K : Subgroup G}
    (hHZ : H ≤ Subgroup.center G) (h : H.IsComplement' K) : K.Normal := by
  refine ⟨fun k hk g => ?_⟩
  obtain ⟨⟨p, q⟩, hpq, -⟩ := h.existsUnique g
  have hpcomm : ∀ y : G, (p : G) * y = y * (p : G) :=
    fun y => (Subgroup.mem_center_iff.mp (hHZ p.2) y).symm
  have hkq : (q : G) * (k : G) * (q : G)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem q.2 hk) (K.inv_mem q.2)
  have key : (p : G) * (q : G) * (k : G) * ((p : G) * (q : G))⁻¹
      = (q : G) * (k : G) * (q : G)⁻¹ := by
    rw [mul_inv_rev]
    calc (p : G) * (q : G) * (k : G) * ((q : G)⁻¹ * (p : G)⁻¹)
        = (p : G) * ((q : G) * (k : G) * (q : G)⁻¹) * (p : G)⁻¹ := by group
      _ = (q : G) * (k : G) * (q : G)⁻¹ := by rw [hpcomm]; group
  rw [← hpq, key]
  exact hkq

/-- Characterisation of the central complement: if `H ≤ Z(X)` is a `p`-group and `K` is a
complement of `H` of order coprime to `p`, then `K` is exactly the set of elements of order
coprime to `p`.  Indeed `x = h * k` uniquely with `h ∈ H`, `k ∈ K`; `h` and `k` commute, so
`orderOf x = orderOf h * orderOf k` with `orderOf h` a `p`-power and `orderOf k` coprime to `p`. -/
private theorem mem_of_coprime_order_complement {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup X} (hHZ : H ≤ Subgroup.center X) (hHP : IsPGroup p ↥H)
    (hK : H.IsComplement' K) (hKcard : Nat.Coprime (Nat.card ↥K) p) :
    ∀ x : X, x ∈ K ↔ Nat.Coprime (orderOf x) p := by
  intro x
  constructor
  · intro hx
    have hdvd : orderOf x ∣ Nat.card ↥K := by
      have h1 : orderOf x = orderOf (⟨x, hx⟩ : ↥K) :=
        Subgroup.orderOf_coe (⟨x, hx⟩ : ↥K)
      rw [h1]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd hKcard
  · intro hcop
    obtain ⟨w, hw, -⟩ := hK.existsUnique x
    obtain ⟨h, k⟩ := w
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hHP h
    have hkcop : Nat.Coprime (orderOf k) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard k) hKcard
    have hcomm : Commute (h : X) (k : X) := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp (hHZ h.2) (k : X)).symm
    have hcopprod : Nat.Coprime (orderOf (h : X)) (orderOf (k : X)) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]
      exact Nat.Coprime.pow_left n hkcop.symm
    have hord : orderOf x = p ^ n * orderOf k := by
      rw [← hw, Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcopprod,
        Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]
    have hx_cop' : Nat.Coprime (p ^ n * orderOf k) p := by rw [← hord]; exact hcop
    have hpn : Nat.Coprime (p ^ n) p :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right (p ^ n) (orderOf k)) hx_cop'
    have hn0 : n = 0 := coprime_pow_prime_self (Fact.out : p.Prime) hpn
    have hh1 : h = 1 := orderOf_eq_one_iff.mp (by rw [hn, hn0, pow_zero])
    have hh1' : (h : X) = 1 := by rw [← Subgroup.coe_one]; exact congrArg Subtype.val hh1
    rw [← hw, hh1', one_mul]
    exact k.2

theorem l52Complement {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (T : Sylow p X)
    (hT : (T : Subgroup X) ≤ Subgroup.center X) :
    ∃ K : Subgroup X, K.Normal ∧ K ⊔ (T : Subgroup X) = ⊤ ∧ Disjoint K (T : Subgroup X) ∧
      Nat.Coprime (Nat.card K) p ∧ ∀ x : X, x ∈ K ↔ Nat.Coprime (orderOf x) p := by
  have hp : p.Prime := Fact.out
  have hTnormal : (T : Subgroup X).Normal := Subgroup.normal_of_le_center hT
  have hndvd : ¬ p ∣ (T : Subgroup X).index := Sylow.not_dvd_index T
  have hidx : Nat.Coprime ((T : Subgroup X).index) p :=
    (hp.coprime_iff_not_dvd.mpr hndvd).symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hcardT : Nat.Coprime (Nat.card ↥(T : Subgroup X)) (T : Subgroup X).index := by
    rw [hn]; exact Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr hndvd)
  obtain ⟨K, hK⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := (T : Subgroup X)) hcardT
  have hcardK : Nat.Coprime (Nat.card ↥K) p := by
    have h1 : Nat.card ↥K = (T : Subgroup X).index := Subgroup.IsComplement.card_right hK
    rw [h1]; exact hidx
  have hmem := mem_of_coprime_order_complement hT T.isPGroup' hK hcardK
  exact ⟨K, complement_normal_of_le_center hT hK, by rw [sup_comm]; exact hK.sup_eq_top,
    hK.disjoint.symm, hcardK, hmem⟩

end Work.ZJB2
