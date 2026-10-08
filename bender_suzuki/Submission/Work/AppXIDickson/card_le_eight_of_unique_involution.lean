import Mathlib
import Submission.Work.AppXIDickson.card_center_le_four
import Submission.Work.AppXIDickson.card_center_le_two_of_ne_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.AppXIDickson

/-- In a group with at most one involution, every element `y` with `y ^ 2 = 1` is central. -/
lemma mem_center_of_sq_eq_one {P : Type*} [Group P]
    (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y)
    {y : P} (hy : y ^ 2 = 1) : y ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, one_mul]
  · have hy2 : orderOf y = 2 := orderOf_eq_prime hy hy1
    have hconj2 : (g * y * g⁻¹) ^ 2 = 1 := by
      have h1 : g * y * g⁻¹ = (MulAut.conj g) y := by rw [MulAut.conj_apply]
      rw [h1, ← map_pow, hy, map_one]
    have hconj1 : g * y * g⁻¹ ≠ 1 := by
      intro h
      apply hy1
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h]
        _ = 1 := by group
    have hconjord : orderOf (g * y * g⁻¹) = 2 := orderOf_eq_prime hconj2 hconj1
    have heq : g * y * g⁻¹ = y := huniq (g * y * g⁻¹) y hconjord hy2
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [heq]

/-- In a group where every element has order dividing `4` and with at most one involution,
every square is central. -/
lemma sq_mem_center {P : Type*} [Group P]
    (hpow : ∀ x : P, x ^ 4 = 1)
    (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  intro x
  apply mem_center_of_sq_eq_one huniq
  rw [← pow_mul]
  exact hpow x

/-- In a group where every element has order dividing `4` and with at most one involution,
every commutator is central. -/
lemma commutatorElement_mem_center {P : Type*} [Group P]
    (hpow : ∀ x : P, x ^ 4 = 1)
    (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P := by
  have hsq := sq_mem_center hpow huniq
  intro x y
  have hkey : x⁻¹ * ⁅y, x⁆ * x = (x ^ 2)⁻¹ * (x * y) ^ 2 * (y ^ 2)⁻¹ := by
    rw [commutatorElement_def, pow_two, pow_two]
    group
  have hmem : x⁻¹ * ⁅y, x⁆ * x ∈ Subgroup.center P := by
    rw [hkey]
    exact (Subgroup.center P).mul_mem
      ((Subgroup.center P).mul_mem ((Subgroup.center P).inv_mem (hsq x)) (hsq (x * y)))
      ((Subgroup.center P).inv_mem (hsq y))
  have hconj : x * (x⁻¹ * ⁅y, x⁆ * x) * x⁻¹ ∈ Subgroup.center P :=
    (Subgroup.instNormalCenter (G := P)).conj_mem (x⁻¹ * ⁅y, x⁆ * x) hmem x
  have hceq : x * (x⁻¹ * ⁅y, x⁆ * x) * x⁻¹ = ⁅y, x⁆ := by group
  rw [hceq] at hconj
  rw [← commutatorElement_inv y x]
  exact (Subgroup.center P).inv_mem hconj

/-- In a group where every element has order dividing `4` and with at most one involution,
every commutator has order dividing `2`. -/
lemma commutatorElement_sq_eq_one {P : Type*} [Group P]
    (hpow : ∀ x : P, x ^ 4 = 1)
    (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∀ x y : P, ⁅x, y⁆ ^ 2 = 1 := by
  have hcomm := commutatorElement_mem_center hpow huniq
  have hsq := sq_mem_center hpow huniq
  intro x y
  have hcx : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp (hcomm x y) x
  rw [Commute.commutatorElement_pow_left hcx 2, commutatorElement_eq_one_iff_mul_comm]
  exact ((Subgroup.mem_center_iff.mp (hsq x)) y).symm

theorem card_le_eight_of_unique_involution {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hpow : ∀ x : P, x ^ 4 = 1) (huniq : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → x = y) :
    Nat.card P ≤ 8 := by
  classical
  let Z : Subgroup P := Subgroup.center P
  have hcent : ∀ y : P, y ^ 2 = 1 → y ∈ Z := fun y hy => mem_center_of_sq_eq_one huniq hy
  have hsq : ∀ x : P, x ^ 2 ∈ Z := fun x => sq_mem_center hpow huniq x
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z := fun x y => commutatorElement_mem_center hpow huniq x y
  have hcomm2 : ∀ x y : P, ⁅x, y⁆ ^ 2 = 1 := fun x y => commutatorElement_sq_eq_one hpow huniq x y
  have hnon : ∀ w : P, w ∉ Z → w ^ 2 ≠ 1 := fun w hw hw2 => hw (hcent w hw2)
  -- ### the two bounds on the center
  have hZ4 : Nat.card Z ≤ 4 := card_center_le_four hpow huniq
  have hZ2 : Z ≠ ⊤ → Nat.card Z ≤ 2 := fun hne => card_center_le_two_of_ne_top hpow huniq hne
  -- ### bound on the quotient `P ⧸ Z`
  have hQle : Nat.card (P ⧸ Z) ≤ 4 := by
    -- **(P1'):** two elements of distinct nontrivial cosets do not commute
    have hP1 : ∀ g a : P, a ∉ Z → g ∉ Z → g * a ∉ Z → ⁅g, a⁆ ≠ 1 := by
      intro g a ha hg hga hconj
      have hcommute : Commute g a := commutatorElement_eq_one_iff_commute.mp hconj
      have hg2ne : g ^ 2 ≠ 1 := hnon g hg
      have ha2ne : a ^ 2 ≠ 1 := hnon a ha
      have hga2ne : (g * a) ^ 2 ≠ 1 := hnon (g * a) hga
      have hg2sq : (g ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hpow g
      have ha2sq : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hpow a
      have hg2ord : orderOf (g ^ 2) = 2 := orderOf_eq_prime hg2sq hg2ne
      have ha2ord : orderOf (a ^ 2) = 2 := orderOf_eq_prime ha2sq ha2ne
      have heq : g ^ 2 = a ^ 2 := huniq (g ^ 2) (a ^ 2) hg2ord ha2ord
      have hprod : (g * a) ^ 2 = 1 := by
        rw [hcommute.mul_pow, ← heq, ← pow_two]
        exact hg2sq
      exact hga2ne hprod
    -- **(P3):** `[g,a] ≠ 1` and `[h,a] ≠ 1` force `[g*h,a] = 1`
    have hP3 : ∀ g h a : P, ⁅g, a⁆ ≠ 1 → ⁅h, a⁆ ≠ 1 → ⁅g * h, a⁆ = 1 := by
      intro g h a hga hha
      have hhaz : ⁅h, a⁆ ∈ Z := hcomm h a
      have hga2 : ⁅g, a⁆ ^ 2 = 1 := hcomm2 g a
      have hha2 : ⁅h, a⁆ ^ 2 = 1 := hcomm2 h a
      have heq : ⁅g, a⁆ = ⁅h, a⁆ :=
        huniq _ _ (orderOf_eq_prime hga2 hga) (orderOf_eq_prime hha2 hha)
      have hconj : g * ⁅h, a⁆ * g⁻¹ = ⁅h, a⁆ := by
        rw [Subgroup.mem_center_iff.mp hhaz g, mul_assoc, mul_inv_cancel, mul_one]
      rw [commutatorElement_mul_left_eq_conj_mul, hconj, ← heq, ← pow_two]
      exact hga2
    -- coset bookkeeping: `u * v ∈ Z ↔ u⁻¹ * v ∈ Z` because `u ^ 2 ∈ Z`
    have hmuliff : ∀ u v : P, u * v ∈ Z ↔ u⁻¹ * v ∈ Z := by
      intro u v
      have h1 : u * v = u ^ 2 * (u⁻¹ * v) := by group
      rw [h1]
      constructor
      · intro hh
        have h2 : (u ^ 2)⁻¹ * (u ^ 2 * (u⁻¹ * v)) ∈ Z := Z.mul_mem (Z.inv_mem (hsq u)) hh
        rw [← mul_assoc, inv_mul_cancel, one_mul] at h2
        exact h2
      · intro hh
        exact Z.mul_mem (hsq u) hh
    have hpi1 : ∀ g : P, QuotientGroup.mk' Z g = 1 ↔ g ∈ Z := fun g => QuotientGroup.eq_one_iff g
    have hpi2 : ∀ g h : P, (QuotientGroup.mk' Z) g = (QuotientGroup.mk' Z) h ↔ g⁻¹ * h ∈ Z := by
      intro g h
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq
    -- **(P4):** there are no four "independent" cosets
    have hP4 : ∀ x y a : P, x ∉ Z → y ∉ Z → a ∉ Z →
        (QuotientGroup.mk' Z) x ≠ (QuotientGroup.mk' Z) y →
        (QuotientGroup.mk' Z) a ≠ (QuotientGroup.mk' Z) x →
        (QuotientGroup.mk' Z) a ≠ (QuotientGroup.mk' Z) y →
        (QuotientGroup.mk' Z) a ≠ (QuotientGroup.mk' Z) (x * y) → False := by
      intro x y a hx hy ha hxy hax hay haxy
      have hxa : ⁅x, a⁆ ≠ 1 := by
        apply hP1 x a ha hx
        rw [hmuliff x a]
        intro hmem
        exact hax ((hpi2 x a).mpr hmem).symm
      have hya : ⁅y, a⁆ ≠ 1 := by
        apply hP1 y a ha hy
        rw [hmuliff y a]
        intro hmem
        exact hay ((hpi2 y a).mpr hmem).symm
      have hxya : ⁅x * y, a⁆ = 1 := hP3 x y a hxa hya
      have hxyZ : x * y ∉ Z := by
        intro hmem
        have hmem' : x⁻¹ * y ∈ Z := (hmuliff x y).mp hmem
        exact hxy ((hpi2 x y).mpr hmem')
      have hcontra : ⁅x * y, a⁆ ≠ 1 := by
        apply hP1 (x * y) a ha hxyZ
        rw [hmuliff (x * y) a]
        intro hmem
        exact haxy ((hpi2 (x * y) a).mpr hmem).symm
      exact hcontra hxya
    by_cases hex : ∃ x y : P, x ∉ Z ∧ y ∉ Z ∧ (QuotientGroup.mk' Z) x ≠ (QuotientGroup.mk' Z) y
    · obtain ⟨x, y, hx, hy, hxy⟩ := hex
      -- every element of `P` lies in one of the four cosets `1, x, y, x*y`
      have hall : ∀ a : P, (QuotientGroup.mk' Z) a = 1 ∨
          (QuotientGroup.mk' Z) a = (QuotientGroup.mk' Z) x ∨
          (QuotientGroup.mk' Z) a = (QuotientGroup.mk' Z) y ∨
          (QuotientGroup.mk' Z) a = (QuotientGroup.mk' Z) (x * y) := by
        intro a
        by_contra h
        push_neg at h
        exact hP4 x y a hx hy (fun hm => h.1 ((hpi1 a).mpr hm)) hxy h.2.1 h.2.2.1 h.2.2.2
      have hsurj : Function.Surjective
          (fun i : Fin 4 => ![1, (QuotientGroup.mk' Z) x, (QuotientGroup.mk' Z) y,
            (QuotientGroup.mk' Z) (x * y)] i) := by
        intro q
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Z q
        rcases hall a with h | h | h | h
        · exact ⟨0, by rw [← ha, h]; simp⟩
        · exact ⟨1, by rw [← ha, h]; simp⟩
        · exact ⟨2, by rw [← ha, h]; simp⟩
        · exact ⟨3, by rw [← ha, h]; simp⟩
      have hbound := Nat.card_le_card_of_surjective
        (fun i : Fin 4 => ![1, (QuotientGroup.mk' Z) x, (QuotientGroup.mk' Z) y,
          (QuotientGroup.mk' Z) (x * y)] i) hsurj
      simpa using hbound
    · push_neg at hex
      by_cases hZtriv : ∀ x : P, x ∈ Z
      · have hall1 : ∀ q : P ⧸ Z, q = 1 := by
          intro q
          obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Z q
          rw [← ha, (hpi1 a).mpr (hZtriv a)]
        have hsurj : Function.Surjective (fun _ : Fin 4 => (1 : P ⧸ Z)) :=
          fun q => ⟨0, by rw [hall1 q]⟩
        have hbound := Nat.card_le_card_of_surjective (fun _ : Fin 4 => (1 : P ⧸ Z)) hsurj
        simpa using hbound
      · push_neg at hZtriv
        obtain ⟨y₀, hy₀⟩ := hZtriv
        have hall2 : ∀ q : P ⧸ Z, q = 1 ∨ q = (QuotientGroup.mk' Z) y₀ := by
          intro q
          obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective Z q
          by_cases hq : (QuotientGroup.mk' Z) a = 1
          · left; rw [← ha, hq]
          · right
            have haZ : a ∉ Z := fun hm => hq ((hpi1 a).mpr hm)
            rw [← ha, hex a y₀ haZ hy₀]
        have hsurj : Function.Surjective (fun i : Fin 2 => ![1, (QuotientGroup.mk' Z) y₀] i) := by
          intro q
          rcases hall2 q with h | h
          · exact ⟨0, by rw [h]; simp⟩
          · exact ⟨1, by rw [h]; simp⟩
        have hbound := Nat.card_le_card_of_surjective
          (fun i : Fin 2 => ![1, (QuotientGroup.mk' Z) y₀] i) hsurj
        have h2 : Nat.card (P ⧸ Z) ≤ 2 := by simpa using hbound
        omega
  -- ### final assembly
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hP
  have hZne3 : Nat.card Z ≠ 3 := by
    intro h3
    have hdvdP : 3 ∣ 2 ^ n := by
      rw [← hn]
      rw [← h3]
      exact Subgroup.card_subgroup_dvd_card Z
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvdP
    norm_num at h32
  have hcard : Nat.card P = Nat.card (P ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hcard]
  by_cases h4 : Nat.card Z = 4
  · have hZtop : Z = ⊤ := by
      by_contra hne
      have := hZ2 hne
      omega
    have hQ1 : Nat.card (P ⧸ Z) = 1 := by
      rw [hZtop, ← Subgroup.index_eq_card]
      exact Subgroup.index_top
    rw [hQ1, h4]
    norm_num
  · have hZle2 : Nat.card Z ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      have : Nat.card Z = 3 ∨ Nat.card Z = 4 := by omega
      rcases this with h | h
      · exact hZne3 h
      · exact h4 h
    calc Nat.card (P ⧸ Z) * Nat.card Z ≤ 4 * 2 := Nat.mul_le_mul hQle hZle2
      _ = 8 := by norm_num

end Work.AppXIDickson
