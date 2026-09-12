import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

noncomputable section

private theorem aux {k : Type} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) :
    ∀ (n : ℕ) (q : Fin n → Ideal (MvPolynomial (Fin m) k)),
      (∀ i, (q i).IsPrime) →
      (∀ i, ∀ x ∈ q i, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q i) →
      (∀ i, ¬ I ≤ q i) →
      ∃ (e : ℕ) (f : MvPolynomial (Fin m) k), f.IsHomogeneous e ∧ f ∈ I ∧ ∀ i, f ∉ q i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with _ | _ | n
    · intro q hqprime hqhom hqI
      exact ⟨0, 0, MvPolynomial.isHomogeneous_zero (Fin m) k 0, I.zero_mem,
        fun i => absurd i.isLt (Nat.not_lt_zero i.val)⟩
    · intro q hqprime hqhom hqI
      obtain ⟨g, hgI, hgq⟩ : ∃ g ∈ I, g ∉ q 0 := by
        by_contra h
        apply hqI 0
        intro x hx
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
      obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.homogeneousComponent j g ∉ q 0 := by
        by_contra h
        apply hgq
        rw [← MvPolynomial.sum_homogeneousComponent g]
        apply Ideal.sum_mem
        intro j _
        by_contra h'
        exact h ⟨j, h'⟩
      refine ⟨j, MvPolynomial.homogeneousComponent j g,
        MvPolynomial.homogeneousComponent_isHomogeneous j g, hI g hgI j, fun i => ?_⟩
      rw [Fin.eq_zero i]
      exact hj
    · intro q hqprime hqhom hqI
      by_contra hcon
      have hcon' : ∀ (e : ℕ) (f : MvPolynomial (Fin m) k),
          f.IsHomogeneous e → f ∈ I → ∃ i, f ∈ q i := by
        intro e f he hfI
        by_contra h
        exact hcon ⟨e, f, he, hfI, fun i hfi => h ⟨i, hfi⟩⟩
      have hkey : ∀ i : Fin (n + 2), ∃ (e : ℕ) (x : MvPolynomial (Fin m) k),
          x.IsHomogeneous e ∧ x ∈ I ∧ ∀ j : Fin (n + 1), x ∉ q (i.succAbove j) := by
        intro i
        exact IH (n + 1) (by omega) (fun j => q (i.succAbove j))
          (fun j => hqprime _) (fun j => hqhom _) (fun j => hqI _)
      let E : Fin (n + 2) → ℕ := fun i => Classical.choose (hkey i)
      let X : Fin (n + 2) → MvPolynomial (Fin m) k :=
        fun i => Classical.choose (Classical.choose_spec (hkey i))
      have hX : ∀ i, (X i).IsHomogeneous (E i) ∧ X i ∈ I ∧
          ∀ j : Fin (n + 1), X i ∉ q (i.succAbove j) :=
        fun i => Classical.choose_spec (Classical.choose_spec (hkey i))
      have hXq : ∀ i, X i ∈ q i := by
        intro i
        obtain ⟨k, hk⟩ := hcon' (E i) (X i) (hX i).1 (hX i).2.1
        by_cases hki : k = i
        · rw [hki] at hk; exact hk
        · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
          rw [← hj] at hk
          exact absurd hk ((hX i).2.2 j)
      have hXne : ∀ i, X i ≠ 0 := by
        intro i h0
        have hmem : (0 : MvPolynomial (Fin m) k) ∈ q (i.succAbove 0) := (q _).zero_mem
        rw [← h0] at hmem
        exact (hX i).2.2 0 hmem
      have hEpos : ∀ i, 1 ≤ E i := by
        intro i
        rw [Nat.one_le_iff_ne_zero]
        intro hE0
        have hhom0 : (X i).IsHomogeneous 0 := hE0 ▸ (hX i).1
        have htd : (X i).totalDegree = 0 := hhom0.totalDegree (hXne i)
        have hCe : X i = MvPolynomial.C ((X i).coeff 0) :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
        have hc : (X i).coeff 0 ≠ 0 := by
          intro hc
          exact hXne i (by rw [hCe, hc, map_zero])
        have hunit : IsUnit (X i) := by
          rw [hCe]
          exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc)
        exact (hqprime i).ne_top (Ideal.eq_top_of_isUnit_mem (q i) (hXq i) hunit)
      let M : ℕ := ∏ j : Fin (n + 1), E ((0 : Fin (n + 2)).succAbove j)
      let B : Fin (n + 1) → ℕ := fun j =>
        E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j')
      let a : ℕ := (n + 1) * M
      let z : MvPolynomial (Fin m) k :=
        (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)
      have hM : 1 ≤ M := Finset.one_le_prod' (fun j _ => hEpos _)
      have ha : 0 < a := by
        have : a = (n + 1) * M := rfl
        rw [this]
        exact Nat.mul_pos (by omega) (by omega)
      have hBpos : ∀ j, 0 < B j := by
        intro j
        have hB : B j = E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') := rfl
        rw [hB]
        have h1 : 1 ≤ ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') :=
          Finset.one_le_prod' (fun j' _ => hEpos _)
        have h2 : 1 ≤ E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') :=
          Nat.mul_le_mul (hEpos (0 : Fin (n + 2))) h1
        omega
      have hzI : z ∈ I := by
        have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
        rw [hzdef]
        exact I.add_mem (I.pow_mem_of_mem (hX 0).2.1 a ha)
          (Ideal.prod_mem I (Finset.mem_univ (0 : Fin (n + 1)))
            (I.pow_mem_of_mem (hX _).2.1 (B 0) (hBpos 0)))
      have hdeg : (∑ j ∈ Finset.univ, E ((0 : Fin (n + 2)).succAbove j) * B j) = E 0 * a := by
        have hterm : ∀ j : Fin (n + 1), E ((0 : Fin (n + 2)).succAbove j) * B j = E 0 * M := by
          intro j
          have h1 : E ((0 : Fin (n + 2)).succAbove j) *
              ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') = M :=
            Finset.mul_prod_erase Finset.univ (fun j' => E ((0 : Fin (n + 2)).succAbove j')) (Finset.mem_univ j)
          have hB : B j = E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') := rfl
          rw [hB, ← h1]
          ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        have : a = (n + 1) * M := rfl
        rw [this, smul_eq_mul]
        ring
      have hz_hom : z.IsHomogeneous (E 0 * a) := by
        have h1 : ((X 0)^a).IsHomogeneous (E 0 * a) := (hX 0).1.pow a
        have h2 : (∏ j : Fin (n + 1),
            (X ((0 : Fin (n + 2)).succAbove j))^(B j)).IsHomogeneous (E 0 * a) := by
          rw [← hdeg]
          exact IsHomogeneous.prod Finset.univ
            (fun j => (X ((0 : Fin (n + 2)).succAbove j))^(B j))
            (fun j => E ((0 : Fin (n + 2)).succAbove j) * B j)
            (fun j _ => (hX _).1.pow (B j))
        have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
        rw [hzdef]
        exact h1.add h2
      have hzq : ∀ i, z ∉ q i := by
        intro i
        by_cases hi : i = 0
        · rw [hi]
          intro hz
          have h1 : (X 0)^a ∈ q 0 := (q 0).pow_mem_of_mem (hXq 0) a ha
          have hprod : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) ∈ q 0 := by
            have heq : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) = z - (X 0)^a := by
              have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
              rw [hzdef]; ring
            rw [heq]
            exact (q 0).sub_mem hz h1
          rw [Ideal.IsPrime.prod_mem_iff (hp := hqprime 0)] at hprod
          obtain ⟨j, -, hjq⟩ := hprod
          have hnot : X ((0 : Fin (n + 2)).succAbove j) ∉ q 0 := by
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Fin.succAbove_ne (0 : Fin (n + 2)) j).symm
            have hh := (hX ((0 : Fin (n + 2)).succAbove j)).2.2 j'
            rw [hj'] at hh
            exact hh
          exact hnot (((hqprime 0).pow_mem_iff_mem (B j) (hBpos j)).mp hjq)
        · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
          intro hz
          have hx0 : X (0 : Fin (n + 2)) ∉ q i := by
            rw [← hj]
            exact (hX 0).2.2 j
          have h1 : (X 0)^a ∉ q i := fun hh => hx0 (((hqprime i).pow_mem_iff_mem a ha).mp hh)
          have hprod : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) ∈ q i := by
            apply Ideal.prod_mem (q i) (Finset.mem_univ j)
            rw [hj]
            exact (q i).pow_mem_of_mem (hXq i) (B j) (hBpos j)
          refine h1 ?_
          have heq : (X 0)^a = z - (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) := by
            have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
            rw [hzdef]; ring
          rw [heq]
          exact (q i).sub_mem hz hprod
      exact hcon ⟨E 0 * a, z, hz_hom, hzI, hzq⟩

theorem homogeneous_prime_avoidance {k : Type} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I)
    (P : Finset (Ideal (MvPolynomial (Fin m) k)))
    (hPprime : ∀ p ∈ P, p.IsPrime)
    (hPhom : ∀ p ∈ P, ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    (hIP : ∀ p ∈ P, ¬ I ≤ p) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin m) k), f.IsHomogeneous e ∧ f ∈ I ∧ ∀ p ∈ P, f ∉ p := by
  classical
  obtain ⟨e, f, hh, hI', hp⟩ := aux I hI P.card
    (fun i => (P.equivFin.symm i : {x // x ∈ P}).1)
    (fun i => hPprime _ (P.equivFin.symm i).2)
    (fun i => hPhom _ (P.equivFin.symm i).2)
    (fun i => hIP _ (P.equivFin.symm i).2)
  refine ⟨e, f, hh, hI', fun p hp_mem => ?_⟩
  simpa using hp (P.equivFin ⟨p, hp_mem⟩)

end

end Commons.RingTheory.Ideal.Hilbert