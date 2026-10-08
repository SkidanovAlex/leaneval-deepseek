import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Commons.GroupTheory

/-! A surjective group homomorphism whose kernel is central of odd order preserves
the number of involutions (elements of order two).  The odd-order central kernel
contributes no involutions itself (oddness), merges none (centrality), and every
involution of the quotient lifts to a unique involution of the domain (oddness:
squaring is bijective on the kernel). -/

section CentralOddKer

variable {G H : Type*} [Group G] [Group H]

/-- In a subgroup of odd order, an element satisfying `x * x = 1` is trivial. -/
private lemma eq_one_of_mul_self_eq_one_of_odd_card {K : Subgroup G}
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) (hxx : x * x = 1) : x = 1 := by
  have hx2 : x ^ 2 = 1 := by simpa [pow_two] using hxx
  have hord2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hordK : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hx
  by_cases hx1 : x = 1
  · exact hx1
  · exfalso
    have hord_ne_one : orderOf x ≠ 1 := by
      intro h
      have : x = 1 := orderOf_eq_one_iff.mp h
      exact hx1 this
    have hord_pos : 0 < orderOf x := by
      have hne0 : orderOf x ≠ 0 := by
        intro hz
        rcases hord2 with ⟨c, hc⟩
        rw [hz] at hc
        norm_num at hc
      exact Nat.pos_of_ne_zero hne0
    have hord_le : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hord2
    have hord_two : orderOf x = 2 := by omega
    rcases hK with ⟨m, hm⟩
    rw [hord_two] at hordK
    rcases hordK with ⟨c, hc⟩
    omega

/-- In a subgroup of odd order, every element is a square. -/
private lemma exists_sq_eq_of_odd_card {K : Subgroup G}
    (hK : Odd (Nat.card K)) {x : G} (hx : x ∈ K) : ∃ y : G, y ∈ K ∧ y * y = x := by
  have hxcard : x ^ Nat.card K = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hx)
  rcases exists_pow_eq_pow_two_mul (x := x) hxcard hK 1 with ⟨m, hm⟩
  refine ⟨x ^ m, pow_mem hx m, ?_⟩
  calc
    x ^ m * x ^ m = x ^ (m + m) := by rw [pow_add]
    _ = x ^ (2 * m) := by congr 1; omega
    _ = x ^ 1 := hm.symm
    _ = x := by simp

/-- Under a surjective homomorphism with odd-order kernel, the image of an
involution is an involution. -/
private lemma orderOf_map_eq_two_of_orderOf_eq_two (φ : G →* H)
    (hkerOdd : Odd (Nat.card (MonoidHom.ker φ))) {t : G} (ht : orderOf t = 2) :
    orderOf (φ t) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime (p := 2)
  · have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
    rw [← map_pow, ht2, map_one]
  · intro hφ1
    have htKer : t ∈ MonoidHom.ker φ := MonoidHom.mem_ker.mpr hφ1
    have htt : t * t = 1 := by simpa [pow_two, ht] using pow_orderOf_eq_one t
    have ht1 : t = 1 :=
      eq_one_of_mul_self_eq_one_of_odd_card (K := MonoidHom.ker φ) hkerOdd htKer htt
    have hordt : orderOf t = 1 := by
      rw [ht1]
      exact orderOf_one
    omega

/-- A surjective homomorphism with central odd-order kernel is injective on the
involutions. -/
private lemma eq_of_map_eq_of_orderOf_eq_two (φ : G →* H)
    (hkerCenter : (MonoidHom.ker φ) ≤ Subgroup.center G)
    (hkerOdd : Odd (Nat.card (MonoidHom.ker φ))) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (h : φ t = φ u) : t = u := by
  let k : G := t⁻¹ * u
  have hkKer : k ∈ MonoidHom.ker φ := by
    rw [MonoidHom.mem_ker]
    dsimp [k]
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hkCenter : k ∈ Subgroup.center G := hkerCenter hkKer
  have hcomm : ∀ g : G, g * k = k * g := Subgroup.mem_center_iff.mp hkCenter
  have htu : t * k = u := by
    dsimp [k]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hkk : k * k = 1 := by
    have hsq : (t * k) * (t * k) = (t * t) * (k * k) := by
      calc
        (t * k) * (t * k) = (t * (k * t)) * k := by group
        _ = (t * (t * k)) * k := by rw [← hcomm t]
        _ = ((t * t) * k) * k := by group
        _ = (t * t) * (k * k) := by group
    have htt : t * t = 1 := by simpa [pow_two, ht] using pow_orderOf_eq_one t
    have huu : u * u = 1 := by simpa [pow_two, hu] using pow_orderOf_eq_one u
    have hmain : (t * k) * (t * k) = 1 := by
      calc
        (t * k) * (t * k) = u * u := by rw [htu]
        _ = 1 := huu
    have : (t * t) * (k * k) = 1 := by
      rw [← hsq]
      exact hmain
    rw [htt] at this
    simpa using this
  have hk1 : k = 1 :=
    eq_one_of_mul_self_eq_one_of_odd_card (K := MonoidHom.ker φ) hkerOdd hkKer hkk
  calc
    t = t * 1 := by rw [mul_one]
    _ = t * k := by rw [hk1]
    _ = u := htu

/-- A surjective homomorphism with central odd-order kernel maps the involutions
of `G` bijectively onto those of `H`; in particular the counts agree. -/
theorem involutions_card_eq_of_surjective_centralOddKer {G H : Type*} [Group G] [Group H]
    [Finite G] (φ : G →* H) (hsurj : Function.Surjective φ)
    (hkerCenter : (MonoidHom.ker φ) ≤ Subgroup.center G)
    (hkerOdd : Odd (Nat.card (MonoidHom.ker φ))) :
    Nat.card {t : G // orderOf t = 2} = Nat.card {s : H // orderOf s = 2} := by
  classical
  let f : {t : G // orderOf t = 2} → {s : H // orderOf s = 2} := fun t =>
    ⟨φ t.1, orderOf_map_eq_two_of_orderOf_eq_two φ hkerOdd t.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · -- injective
    intro a b hab
    apply Subtype.ext
    apply eq_of_map_eq_of_orderOf_eq_two φ hkerCenter hkerOdd a.2 b.2
    exact congrArg Subtype.val hab
  · -- surjective
    intro s
    rcases hsurj s.1 with ⟨g, hg⟩
    have hsu : s.1 * s.1 = 1 := by simpa [pow_two, s.2] using pow_orderOf_eq_one s.1
    have hsne : s.1 ≠ 1 := by
      intro h
      have : orderOf (1 : H) = 2 := by simpa [h] using s.2
      rw [orderOf_one] at this
      norm_num at this
    have hgg : φ (g * g) = 1 := by
      rw [map_mul, hg, hsu]
    have hc : (g * g)⁻¹ ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker, map_inv, hgg, inv_one]
    rcases exists_sq_eq_of_odd_card (K := MonoidHom.ker φ) hkerOdd hc with ⟨u, huK, huu⟩
    have hu1 : φ u = 1 := MonoidHom.mem_ker.mp huK
    have hcommu : ∀ a : G, a * u = u * a := Subgroup.mem_center_iff.mp (hkerCenter huK)
    have hφt : φ (g * u) = s.1 := by
      rw [map_mul, hg, hu1, mul_one]
    have hsq : (g * u) * (g * u) = (g * g) * (u * u) := by
      calc
        (g * u) * (g * u) = (g * (u * g)) * u := by group
        _ = (g * (g * u)) * u := by rw [hcommu g]
        _ = ((g * g) * u) * u := by group
        _ = (g * g) * (u * u) := by group
    have ht2 : (g * u) * (g * u) = 1 := by
      rw [hsq, huu]
      exact mul_inv_cancel (g * g)
    have hne : g * u ≠ 1 := by
      intro hgu1
      have hφgu : φ (g * u) = 1 := by
        rw [hgu1, map_one]
      have hs1 : s.1 = 1 := by
        rw [← hφt]
        exact hφgu
      exact hsne hs1
    have htord : orderOf (g * u) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply orderOf_eq_prime (p := 2)
      · simpa [pow_two] using ht2
      · exact hne
    refine ⟨⟨g * u, htord⟩, ?_⟩
    apply Subtype.ext
    exact hφt

end CentralOddKer

end Commons.GroupTheory
