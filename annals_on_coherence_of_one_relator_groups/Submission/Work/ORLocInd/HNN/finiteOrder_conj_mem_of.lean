import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.HNN.HNNTorsionDefs

namespace Work.ORLocInd.HNN

open HNNExtension

set_option autoImplicit false

/-- **Finite-order elements of an HNN extension are conjugate into the base group.**
(Britton's lemma: a length-minimal conjugate of a torsion element is cyclically reduced, and powers
of a cyclically reduced word of positive length have positive length.) -/
theorem finiteOrder_conj_mem_of {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)
    (x : HNNExtension G A B φ) (hx : IsOfFinOrder x) :
    ∃ c : HNNExtension G A B φ, ∃ g : G, c * x * c⁻¹ = HNNExtension.of g := by
  classical
  obtain ⟨n, hnpos, hxn⟩ : ∃ n, 0 < n ∧ x ^ n = 1 :=
    ⟨orderOf x, hx.orderOf_pos, pow_orderOf_eq_one x⟩
  have hex : ∃ m, ∃ c : HNNExtension G A B φ, rlen φ (c * x * c⁻¹) = m := ⟨_, 1, rfl⟩
  obtain ⟨c₀, hc₀⟩ := Nat.find_spec hex
  set y := c₀ * x * c₀⁻¹ with hy
  have hyr : rlen φ y = Nat.find hex := hc₀
  have hmin : ∀ d : HNNExtension G A B φ, rlen φ y ≤ rlen φ (d * x * d⁻¹) := fun d => by
    rw [hyr]; exact Nat.find_min' hex ⟨d, rfl⟩
  have hyn : y ^ n = 1 := by rw [hy, conj_pow, hxn]; group
  by_cases hzero : rlen φ y = 0
  · obtain ⟨g, hg⟩ := exists_of_rlen_eq_zero φ hzero
    exact ⟨c₀, g, by rw [← hy]; exact hg⟩
  · exfalso
    have hy1 : 1 ≤ rlen φ y := Nat.one_le_iff_ne_zero.mpr hzero
    set W := NormalWord.equiv φ (stdTransversal G A B) y with hW
    have hWprod : NormalWord.ReducedWord.prod φ W.toReducedWord = y := normalWord_prod φ y
    have hch : W.toList.IsChain (rel A B) := normalWord_chain φ y
    have hlen : W.toList.length = rlen φ y := by rw [hW]; rfl
    have hl1 : 1 ≤ W.toList.length := by rw [hlen]; exact hy1
    have hlne : W.toList ≠ [] := by rw [← List.length_pos_iff]; omega
    -- `z = of h⁻¹ * y * of h` where `z = lprod φ (lmove l h)`
    have hz : lprod φ (lmove W.toList W.head) = of W.head⁻¹ * y * of W.head := by
      rw [lprod_lmove φ W.toList W.head hlne, ← hWprod, prod_eq_wProd]
      simp only [wProd, map_inv]
      group
    have hch' : (lmove W.toList W.head).IsChain (rel A B) :=
      (isChain_lmove_iff W.toList W.head).2 hch
    by_cases hcyc : ∀ u ∈ (lmove W.toList W.head).getLast?,
        ∀ v ∈ (lmove W.toList W.head).head?, rel A B u v
    · -- cyclically reduced: powers have length `k * ℓ`
      have hpow := rlen_lpow φ (lmove W.toList W.head) n hch' hcyc
      have hzp : (lprod φ (lmove W.toList W.head)) ^ n = 1 := by
        rw [hz]
        have hzinv : (of W.head : HNNExtension G A B φ) = ((of (W.head⁻¹) : HNNExtension G A B φ))⁻¹ := by
          rw [map_inv, inv_inv]
        rw [hzinv, conj_pow, hyn]
        group
      have h0 : n * (lmove W.toList W.head).length = 0 := by
        rw [← hpow, hzp, rlen_one]
      rw [lmove_length] at h0
      have hpos : 0 < n * W.toList.length := Nat.mul_pos hnpos (by omega)
      omega
    · -- not cyclically reduced: a conjugate of smaller length
      have hl'1 : 1 ≤ (lmove W.toList W.head).length := by rw [lmove_length]; omega
      have h2 : 2 ≤ (lmove W.toList W.head).length := by
        rcases Nat.lt_or_ge (lmove W.toList W.head).length 2 with hlt | hge
        · exact absurd (hcyc_of_length_le_one (A:=A) (B:=B) (by omega)) hcyc
        · exact hge
      obtain ⟨p, q, mid, hd, hp, hq, hmlen, hchmid⟩ :=
        exists_decomp (lmove W.toList W.head) h2
      have hnot : ¬ rel A B q p := by
        intro hrel
        apply hcyc
        intro u hu v hv
        rw [hq, Option.mem_def, Option.some.injEq] at hu
        rw [hp, Option.mem_def, Option.some.injEq] at hv
        rw [← hu, ← hv]
        exact hrel
      have hkey := reduce_not_cyclic φ p q mid (hchmid hch') hnot
      rw [← hd] at hkey
      have hdm : mid.length = W.toList.length - 2 := by rw [hmlen, lmove_length]
      have hdconj : (t : HNNExtension G A B φ) ^ (q.1 : ℤ) * lprod φ (lmove W.toList W.head)
            * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ))⁻¹
          = ((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * of W.head⁻¹ * c₀)
              * x * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * of W.head⁻¹ * c₀)⁻¹ := by
        rw [hz, hy]
        simp only [map_inv, inv_inv]
        group
      have h4 : rlen φ y ≤ mid.length := by
        calc rlen φ y ≤ rlen φ (((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * of W.head⁻¹ * c₀)
              * x * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * of W.head⁻¹ * c₀)⁻¹) := hmin _
          _ = rlen φ ((t : HNNExtension G A B φ) ^ (q.1 : ℤ) * lprod φ (lmove W.toList W.head)
                * ((t : HNNExtension G A B φ) ^ (q.1 : ℤ))⁻¹) := by rw [hdconj]
          _ ≤ mid.length := hkey
      rw [hdm, hlen] at h4
      omega

end Work.ORLocInd.HNN
