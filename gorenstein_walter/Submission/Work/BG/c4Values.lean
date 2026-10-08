import Mathlib
import Submission.Work.BG.c4Aux
import Submission.Work.BG.c4InnerOne
import Submission.Work.BG.c4TripleSum
import Submission.Work.BG.wsL41Val
import Submission.Work.BG.thm43Hat
import Submission.Work.BG.ubkIrr
import Submission.Work.BG.Hat
import Submission.Work.BG.constituentSum

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23


open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c4Values {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (K1 K2 : Subgroup G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.C4ValuesProp D C K1 K2 := by
  intro hC hn hHyps β₂ hβ κ hκ χ₁ χ₂ χ₃ χ₄ hpm1 hpm2 hpm3 hpm4 hdec hid
  have hcard2 : Nat.card (quotGroup C.P) = 2 := by
    rw [← Subgroup.index_eq_card (Uin C), rem31IndexUin D C hC, hn]
  have hκ4 : κ ∈ S4Index C := kappa_mem_S4Index D C hC hn hκ
  have hZ : delta C β₂ κ ∈ ZIrr G := l41_delta_mem_ZIrr C hκ.1
  have hnorm : ClassFunction.inner (delta C β₂ κ) (delta C β₂ κ) = 4 := by
    rw [l41_delta_inner_self (C := C) (β₂ := β₂) hcard2 hβ hκ.1, if_pos hκ.2.2.1]
  have h0 : delta C β₂ κ 1 = 0 := l41_delta_apply_one C hκ.1
  obtain ⟨hi1, hi2, hi3, hi4⟩ :=
    c4InnerOne (delta C β₂ κ) hZ hnorm h0 χ₁ χ₂ χ₃ χ₄ hpm1 hpm2 hpm3 hpm4 hdec
  have h41 : Lemma41Prop D C := wsL41Val D C
  rcases thm43Hat D C hC hn β₂ hβ κ hκ4 with hiso | htri
  · -- isolated case
    left
    have hbinj : ∀ ν ∈ S4Index C, delta C β₂ ν = delta C β₂ κ → ν = κ :=
      fun ν hν heq => delta_injective D C hC hn hβ hκ4 hν hnorm heq
    have hbset : ∀ (χ : ClassFunction G ℂ), IsPmIrr χ →
        ClassFunction.inner χ (delta C β₂ κ) = 1 → bset' C β₂ χ = {κ} := by
      intro χ hχ hinner
      ext ν
      constructor
      · intro hν
        obtain ⟨hνS, hνne⟩ := hν
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hδne : delta C β₂ ν ≠ delta C β₂ κ := fun hh => hne (hbinj ν hνS hh)
        exact not_disjointCF_of_inner_ne_zero hχ (by rw [hinner]; norm_num) hνne
          (hiso ν hνS hδne)
      · intro hν
        rw [Set.mem_singleton_iff] at hν
        rw [hν]
        exact ⟨hκ4, by rw [hinner]; norm_num⟩
    have hval : ∀ (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
        (hinner : ClassFunction.inner χ (delta C β₂ κ) = 1), χ (C.t : G) = 1 := by
      intro χ hχ hinner
      have hmem : (bset' C β₂ χ).Nonempty :=
        ⟨κ, hκ4, by rw [hinner]; norm_num⟩
      obtain ⟨-, hsum, -⟩ := h41 hC hn β₂ hβ χ hχ hmem
      rw [hbset χ hχ hinner] at hsum
      have hsingle : (∑ᶠ ν ∈ ({κ} : Set (ClassFunction ↥C.P.H0 ℂ)),
          ClassFunction.inner χ (delta C β₂ ν) * ν 1)
          = ClassFunction.inner χ (delta C β₂ κ) * κ 1 := by
        rw [finsum_mem_def, finsum_eq_single _ κ]
        · rw [Set.indicator_of_mem (Set.mem_singleton _)]
        · intro b hb
          rw [Set.indicator_of_notMem (by
            simp only [Set.mem_singleton_iff]; exact hb)]
      rw [hsingle] at hsum
      rw [hsum, hinner, hκ.2.1]
      ring
    exact ⟨hval χ₁ hpm1 hi1, hval χ₂ hpm2 hi2, hval χ₃ hpm3 hi3, hval χ₄ hpm4 hi4⟩
  · -- triple case
    right
    obtain ⟨μ₂, hμ₂, μ₃, hμ₃, ψ₁, ψ₂, ψ₃, ψ₄, hψ1, hψ2, hψ3, hψ4, heq1, heq2, heq3, hhat⟩ := htri
    -- linearity of the three triple members
    obtain ⟨θκ, hθκ⟩ := (Hat D C hC hn κ hκ4).1
    obtain ⟨⟨θ₂, hθ₂, hconj₂⟩, ⟨θ₃, hθ₃, hconj₃⟩⟩ := hhat θκ hθκ
    have hκone : θκ 1 = κ 1 := ubkIrr D C K1 K2 hC hn hHyps κ hκ4 θκ hθκ
    have hdeg₂ : θ₂ 1 = θκ 1 := by
      obtain ⟨x, hx, hcb⟩ := hconj₂
      exact hcb 1 1 (by simp)
    have hdeg₃ : θ₃ 1 = θκ 1 := by
      obtain ⟨x, hx, hcb⟩ := hconj₃
      exact hcb 1 1 (by simp)
    have hμ₂one : μ₂ 1 = 1 := by
      rw [← ubkIrr D C K1 K2 hC hn hHyps μ₂ hμ₂ θ₂ hθ₂, hdeg₂, hκone, hκ.2.1]
    have hμ₃one : μ₃ 1 = 1 := by
      rw [← ubkIrr D C K1 K2 hC hn hHyps μ₃ hμ₃ θ₃ hθ₃, hdeg₃, hκone, hκ.2.1]
    obtain ⟨d, hdval, hdsum⟩ :=
      c4TripleSum D C hC hn hβ hκ h41 hμ₂ hμ₃ hμ₂one hμ₃one hψ1 hψ2 hψ3 hψ4
        heq1 heq2 heq3
    haveI : Fintype (IrreducibleCharacter G) := inferInstance
    -- the two X1 evaluations agree with the given decomposition
    have hX1χ :
        (∑ χ : IrreducibleCharacter G, (χ : ClassFunction G ℂ) (C.t : G) ^ 2 /
            (χ : ClassFunction G ℂ) 1 *
              ClassFunction.inner
                (∑ i : Fin 4, (![χ₁, χ₂, χ₃, χ₄] : Fin 4 → ClassFunction G ℂ) i)
                (χ : ClassFunction G ℂ))
          = χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
            χ₃ (C.t : G) ^ 2 / χ₃ 1 + χ₄ (C.t : G) ^ 2 / χ₄ 1 := by
      have h := constituentSum (K := G) (![χ₁, χ₂, χ₃, χ₄] : Fin 4 → ClassFunction G ℂ)
        (by intro i; fin_cases i
            · simpa using hpm1
            · simpa using hpm2
            · simpa using hpm3
            · simpa using hpm4) (C.t : G)
      simpa [Fin.sum_univ_four] using h
    have hX1ψ :
        (∑ χ : IrreducibleCharacter G, (χ : ClassFunction G ℂ) (C.t : G) ^ 2 /
            (χ : ClassFunction G ℂ) 1 *
              ClassFunction.inner
                (∑ i : Fin 4, (![ψ₁, ψ₂, ψ₃, ψ₄] : Fin 4 → ClassFunction G ℂ) i)
                (χ : ClassFunction G ℂ))
          = ψ₁ (C.t : G) ^ 2 / ψ₁ 1 + ψ₂ (C.t : G) ^ 2 / ψ₂ 1 +
            ψ₃ (C.t : G) ^ 2 / ψ₃ 1 + ψ₄ (C.t : G) ^ 2 / ψ₄ 1 := by
      have h := constituentSum (K := G) (![ψ₁, ψ₂, ψ₃, ψ₄] : Fin 4 → ClassFunction G ℂ)
        (by intro i; fin_cases i
            · simpa using hψ1
            · simpa using hψ2
            · simpa using hψ3
            · simpa using hψ4) (C.t : G)
      simpa [Fin.sum_univ_four] using h
    have hsumχ : (∑ i : Fin 4, (![χ₁, χ₂, χ₃, χ₄] : Fin 4 → ClassFunction G ℂ) i)
        = χ₁ + χ₂ + χ₃ + χ₄ := by
      rw [Fin.sum_univ_four]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val',
        Function.comp_apply]
    have hsumψ : (∑ i : Fin 4, (![ψ₁, ψ₂, ψ₃, ψ₄] : Fin 4 → ClassFunction G ℂ) i)
        = ψ₁ + ψ₂ + ψ₃ + ψ₄ := by
      rw [Fin.sum_univ_four]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val',
        Function.comp_apply]
    have hsum_eq : (∑ i : Fin 4, (![χ₁, χ₂, χ₃, χ₄] : Fin 4 → ClassFunction G ℂ) i)
        = (∑ i : Fin 4, (![ψ₁, ψ₂, ψ₃, ψ₄] : Fin 4 → ClassFunction G ℂ) i) := by
      rw [hsumχ, hsumψ, ← hdec, heq1]
    have hX1eq : χ₁ (C.t : G) ^ 2 / χ₁ 1 + χ₂ (C.t : G) ^ 2 / χ₂ 1 +
          χ₃ (C.t : G) ^ 2 / χ₃ 1 + χ₄ (C.t : G) ^ 2 / χ₄ 1
        = ψ₁ (C.t : G) ^ 2 / ψ₁ 1 + ψ₂ (C.t : G) ^ 2 / ψ₂ 1 +
          ψ₃ (C.t : G) ^ 2 / ψ₃ 1 + ψ₄ (C.t : G) ^ 2 / ψ₄ 1 := by
      rw [← hX1χ, hsum_eq, hX1ψ]
    have hN : (D.H.index : ℂ) * (8 / (d : ℂ)) = 2 * (D.k : ℂ) ^ 2 := by
      rw [← hdsum, ← hX1eq]
      exact hid
    have hd0 : (d : ℂ) ≠ 0 := by rw [← hdval]; exact IsPmIrr.apply_one_ne_zero hψ1
    have hmul : 8 * (D.H.index : ℂ) = 2 * (D.k : ℂ) ^ 2 * (d : ℂ) := by
      have h := congrArg (fun z : ℂ => z * (d : ℂ)) hN
      rw [mul_assoc, div_mul_cancel₀ 8 hd0] at h
      rw [show (8 : ℂ) * (D.H.index : ℂ) = (D.H.index : ℂ) * 8 from by ring]
      exact h
    have hZ : 8 * (D.H.index : ℤ) = 2 * (D.k : ℤ) ^ 2 * d := by
      apply Int.cast_injective (α := ℂ)
      have e1 : (((8 * (D.H.index : ℤ) : ℤ)) : ℂ) = 8 * (D.H.index : ℂ) := by
        push_cast; ring
      have e2 : (((2 * (D.k : ℤ) ^ 2 * d : ℤ)) : ℂ) = 2 * (D.k : ℂ) ^ 2 * (d : ℂ) := by
        push_cast; ring
      rw [e1, e2]
      exact hmul
    exact ⟨d, hZ.symm⟩

end Work.BG
