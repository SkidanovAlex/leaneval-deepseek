import Mathlib

/-!
# A permutation lemma on `Fin 7`

Let `P Q : Equiv.Perm (Fin 7)` with `P ^ 3 = 1`, `P ≠ 1`, `Q * Q = 1`, `Q * P = P * Q`
and `Q.support.card = 4`.  Then `P` and `Q` are `Disjoint` (no point is moved by both),
`P` consists of a single 3-cycle, and `Q.support` is exactly the complement of `P.support`.

The main combinatorial content is that the `P`-orbit `{x, P x, P² x}` of a point `x` that
is moved by both `P` and `Q` is disjoint from the `P`-orbit of `Q x`; both are 3-element
sets (so 6 points in total) and `Q` moves every point of their union, contradicting
`Q.support.card = 4`.
-/

namespace Work.CORE4.A7FGB

open Equiv

/-- The `P`-orbit of a point `y` (for `P ^ 3 = 1` it has at most three elements). -/
def pOrbit (P : Equiv.Perm (Fin 7)) (y : Fin 7) : Finset (Fin 7) := {y, P y, (P^2) y}

/-! ### Basic consequences of `P ^ 3 = 1` on a 3-element orbit -/

lemma pow3_e1 (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (t : Fin 7) :
    P ((P^2) t) = t := by
  have hh : (P^3) t = t := by rw [hP]; rfl
  rwa [show P^3 = P * P^2 from pow_succ' P 2, Equiv.Perm.mul_apply] at hh

lemma pow3_e2 (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (t : Fin 7) :
    (P^2) (P t) = t := by
  rw [show (P^2) (P t) = P ((P^2) t) from rfl, pow3_e1 P hP t]

lemma pow3_e3 (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (t : Fin 7) :
    (P^2) ((P^2) t) = P t := by
  rw [show (P^2) ((P^2) t) = P (P ((P^2) t)) from rfl, pow3_e1 P hP t]

lemma pow3_ne2 (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (t : Fin 7) (ht : P t ≠ t) :
    (P^2) t ≠ t := by
  intro h
  apply ht
  have h3 : P ((P^2) t) = t := pow3_e1 P hP t
  rw [h] at h3
  exact h3

lemma pow3_ne3 (P : Equiv.Perm (Fin 7)) (_hP : P ^ 3 = 1) (t : Fin 7) (ht : P t ≠ t) :
    (P^2) t ≠ P t := by
  intro h; exact ht (P.injective h)

@[simp] lemma mem_pOrbit {P : Equiv.Perm (Fin 7)} {y w : Fin 7} :
    w ∈ pOrbit P y ↔ w = y ∨ w = P y ∨ w = (P^2) y := by
  unfold pOrbit
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- A `P`-orbit of a moved point has exactly three points. -/
lemma pOrbit_card (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (y : Fin 7) (hy : P y ≠ y) :
    (pOrbit P y).card = 3 := by
  have h2 := pow3_ne2 P hP y hy
  have h3 := pow3_ne3 P hP y hy
  unfold pOrbit
  rw [Finset.card_eq_three]
  exact ⟨y, P y, (P^2) y, Ne.symm hy, Ne.symm h2, Ne.symm h3, rfl⟩

lemma pOrbit_mem_apply (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (y t : Fin 7)
    (ht : t ∈ pOrbit P y) : P t ∈ pOrbit P y := by
  rw [mem_pOrbit] at ht ⊢
  rcases ht with h | h | h
  · rw [h]; exact Or.inr (Or.inl rfl)
  · rw [h]; exact Or.inr (Or.inr rfl)
  · rw [h]; exact Or.inl (pow3_e1 P hP y)

lemma pOrbit_mem_apply2 (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (y t : Fin 7)
    (ht : t ∈ pOrbit P y) : (P^2) t ∈ pOrbit P y := by
  rw [mem_pOrbit] at ht ⊢
  rcases ht with h | h | h
  · rw [h]; exact Or.inr (Or.inr rfl)
  · rw [h]; exact Or.inl (pow3_e2 P hP y)
  · rw [h]; exact Or.inr (Or.inl (pow3_e3 P hP y))

/-- Two `P`-orbits are equal or disjoint: if they meet then `z` lies in the orbit of `y`. -/
lemma pOrbit_meet (P : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) {y z w : Fin 7}
    (h1 : w ∈ pOrbit P y) (h2 : w ∈ pOrbit P z) : z ∈ pOrbit P y := by
  rw [mem_pOrbit] at h2
  rcases h2 with h2 | h2 | h2
  · rw [← h2]; exact h1
  · have hz : z = (P^2) w := by rw [← pow3_e2 P hP z, h2]
    rw [hz]; exact pOrbit_mem_apply2 P hP y w h1
  · have hz : z = P w := by rw [← pow3_e1 P hP z, h2]
    rw [hz]; exact pOrbit_mem_apply P hP y w h1

/-! ### How `Q` interacts with `P`-orbits -/

lemma commute_pow_1 (P Q : Equiv.Perm (Fin 7)) (hcomm : Q * P = P * Q) (t : Fin 7) :
    Q (P t) = P (Q t) := by
  rw [← Equiv.Perm.mul_apply, hcomm, Equiv.Perm.mul_apply]

lemma commute_pow2 (P Q : Equiv.Perm (Fin 7)) (hcomm : Q * P = P * Q) (t : Fin 7) :
    Q ((P^2) t) = (P^2) (Q t) := by
  have h1 : Q (P t) = P (Q t) := commute_pow_1 P Q hcomm t
  show Q (P (P t)) = P (P (Q t))
  rw [show Q (P (P t)) = P (Q (P t)) from commute_pow_1 P Q hcomm (P t), h1]

/-- `Q` sends the `P`-orbit of `y` into the `P`-orbit of `Q y`. -/
lemma Q_map_pOrbit (P Q : Equiv.Perm (Fin 7)) (hcomm : Q * P = P * Q) (y t : Fin 7)
    (ht : t ∈ pOrbit P y) : Q t ∈ pOrbit P (Q y) := by
  rw [mem_pOrbit] at ht ⊢
  rcases ht with h | h | h
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr (Or.inl (commute_pow_1 P Q hcomm y))
  · rw [h]; exact Or.inr (Or.inr (commute_pow2 P Q hcomm y))

/-- If `x` is moved by both `P` and `Q`, then `Q x` is not in the `P`-orbit of `x`. -/
lemma Qx_not_mem (P Q : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (hQ : Q * Q = 1)
    (hcomm : Q * P = P * Q) (x : Fin 7) (hPx : P x ≠ x) (hQx : Q x ≠ x) :
    Q x ∉ pOrbit P x := by
  intro h
  have h2x := pow3_ne2 P hP x hPx
  have QQ : Q (Q x) = x := by rw [← Equiv.Perm.mul_apply, hQ, Equiv.Perm.one_apply]
  have QP : Q (P x) = P (Q x) := commute_pow_1 P Q hcomm x
  have QP2 : Q ((P^2) x) = (P^2) (Q x) := commute_pow2 P Q hcomm x
  rw [mem_pOrbit] at h
  rcases h with h | h | h
  · exact hQx h
  · have hx : x = (P^2) x := by
      calc x = Q (Q x) := QQ.symm
        _ = Q (P x) := by rw [h]
        _ = P (Q x) := QP
        _ = P (P x) := by rw [h]
        _ = (P^2) x := rfl
    exact h2x hx.symm
  · have hx : x = P x := by
      calc x = Q (Q x) := QQ.symm
        _ = Q ((P^2) x) := by rw [h]
        _ = (P^2) (Q x) := QP2
        _ = (P^2) ((P^2) x) := by rw [h]
        _ = P x := pow3_e3 P hP x
    exact hPx hx.symm

/-! ### The disjointness of `P` and `Q` -/

lemma key (P Q : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (_hP1 : P ≠ 1)
    (hQ : Q * Q = 1) (hcomm : Q * P = P * Q) (hQcard : Q.support.card = 4) :
    Perm.Disjoint P Q := by
  rw [Perm.disjoint_iff_eq_or_eq]
  by_contra h
  push Not at h
  obtain ⟨x, hPx, hQx⟩ := h
  have hO1card : (pOrbit P x).card = 3 := pOrbit_card P hP x hPx
  have hQx_not : Q x ∉ pOrbit P x := Qx_not_mem P Q hP hQ hcomm x hPx hQx
  have hPQx : P (Q x) ≠ Q x := by
    rw [show P (Q x) = Q (P x) from
      by rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply]]
    exact fun hh => hPx (Q.injective hh)
  have hO2card : (pOrbit P (Q x)).card = 3 := pOrbit_card P hP (Q x) hPQx
  have hdisjO : Disjoint (pOrbit P x) (pOrbit P (Q x)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    rw [hab] at ha
    exact hQx_not (pOrbit_meet P hP ha hb)
  have hQQx : Q (Q x) = x := by rw [← Equiv.Perm.mul_apply, hQ, Equiv.Perm.one_apply]
  have hSsub : pOrbit P x ∪ pOrbit P (Q x) ⊆ Q.support := by
    intro t ht
    rw [Finset.mem_union] at ht
    rw [Perm.mem_support]
    rcases ht with ht | ht
    · intro hQt
      have h2 : t ∈ pOrbit P (Q x) := by rw [← hQt]; exact Q_map_pOrbit P Q hcomm x t ht
      exact (Finset.disjoint_iff_ne.mp hdisjO t ht t h2) rfl
    · intro hQt
      have h2 : Q t ∈ pOrbit P x := by
        have hh := Q_map_pOrbit P Q hcomm (Q x) t ht
        rwa [hQQx] at hh
      exact (Finset.disjoint_iff_ne.mp hdisjO (Q t) h2 t ht) hQt
  have hcl := Finset.card_le_card hSsub
  rw [Finset.card_union_of_disjoint hdisjO, hO1card, hO2card, hQcard] at hcl
  omega

theorem commuting_support (P Q : Equiv.Perm (Fin 7)) (hP : P ^ 3 = 1) (hP1 : P ≠ 1)
    (hQ : Q * Q = 1) (hcomm : Q * P = P * Q) (hQcard : Q.support.card = 4) :
    Q.support = Finset.univ \ P.support ∧ P.support.card = 3 := by
  have hdisj : Perm.Disjoint P Q := key P Q hP hP1 hQ hcomm hQcard
  -- `P` moves at least three points.
  have hPne : ∃ x, P x ≠ x := by
    by_contra h
    push Not at h
    exact hP1 (Equiv.ext fun x => (h x).trans (Perm.one_apply x).symm)
  obtain ⟨x, hx⟩ := hPne
  have hsub : pOrbit P x ⊆ P.support := by
    intro t ht
    rw [mem_pOrbit] at ht
    rw [Perm.mem_support]
    rcases ht with h | h | h
    · rw [h]; exact hx
    · rw [h]; exact pow3_ne3 P hP x hx
    · rw [h, pow3_e1 P hP x]
      exact fun hh => pow3_ne2 P hP x hx hh.symm
  have hPge : 3 ≤ P.support.card := by
    have := Finset.card_le_card hsub
    rwa [pOrbit_card P hP x hx] at this
  -- `P.support` is disjoint from `Q.support`, which has four elements.
  have hsubQ : P.support ⊆ (Q.support)ᶜ := by
    intro t ht
    rw [Finset.mem_compl, Perm.mem_support]
    intro hQt
    rcases hdisj t with h | h
    · exact (Perm.mem_support.mp ht) h
    · exact hQt h
  have hPle : P.support.card ≤ 3 := by
    have h := Finset.card_le_card hsubQ
    rw [Finset.card_compl, hQcard, Fintype.card_fin] at h
    omega
  have hPcard : P.support.card = 3 := le_antisymm hPle hPge
  -- `Q.support` is contained in the complement of `P.support`, which has four elements.
  have hsubP : Q.support ⊆ (P.support)ᶜ := by
    intro t ht
    rw [Finset.mem_compl, Perm.mem_support]
    intro hPt
    rcases hdisj t with h | h
    · exact hPt h
    · exact (Perm.mem_support.mp ht) h
  refine ⟨?_, hPcard⟩
  rw [Finset.compl_eq_univ_sdiff] at hsubP
  refine Finset.eq_of_subset_of_card_le hsubP ?_
  rw [← Finset.compl_eq_univ_sdiff P.support, Finset.card_compl, hPcard, hQcard,
    Fintype.card_fin]

end Work.CORE4.A7FGB
