import Mathlib
import Submission.Work.Peluse.Ulower.assemble
import Submission.Work.Peluse.Ulower.sparse_to_dense_uniform
import Submission.Work.Peluse.Ulower.dense_le_apBoxNorm
import Submission.Work.Peluse.Ulower.rankInduction

/-!
# The chain bound

`chain_bound` feeds the main argument (`StepLe`, the single §8 step) into the target's final
comparison: from the target's hypothesis at level `s` it produces a lower bound
`c · δ^A · (D/Ns)^B ≤ uNormPow 2 …`.  Both the exponents `A, B ≥ 1` and the constant `c > 0`
are *uniform in the data* (they depend only on `P`, `K`, `s`), which is what lets the final
comparison produce a single exponent `K` for the whole theorem.

The hypotheses are the two interfaces of the argument: `hstep` (the single step `StepLe`) and
`sparse_to_dense_uniform` (the uniform sparse-to-dense comparison).  The rest is bookkeeping:
`iterate_steps` runs the chain down to level two, `dense_le_apBoxNorm` moves the direction set back
to `arithIcc P.leadingCoeff D`, and the support box is shrunk back to `symIcc (dSup P Ns N)`.
-/

set_option maxHeartbeats 800000

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The cast of `natAbs` of an integer to `ℝ` is its absolute value. -/
lemma natAbs_cast_real (n : ℤ) : (((n.natAbs : ℕ)) : ℝ) = |((n : ℤ) : ℝ)| := by
  cases n with
  | ofNat m => simp
  | negSucc m =>
      rw [show ((Int.negSucc m).natAbs : ℕ) = m + 1 from Int.natAbs_negSucc m]
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]

theorem chain_bound {P : Polynomial ℤ} {K : ℝ} (hK : 0 < K)
    (hKc : |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ K) (hstep : StepLe P K) (htop : 2 ≤ P.natDegree)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ A B : ℕ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ (Ns : ℝ) → SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → 0 < δ → δ ≤ 1 →
        δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
              (dualFn N P f₀ f₁) →
        c * δ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ B ≤
          uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
            (dualFn N P f₀ f₁) := by
  have hc₀ : P.leadingCoeff ≠ 0 := by
    intro h
    have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
    rw [hP] at htop
    simp at htop
  by_cases hs2 : s = 2
  · subst hs2
    refine ⟨1, 1, le_refl 1, le_refl 1, 1, one_pos, ?_⟩
    intro Ns N D f₀ f₁ δ hd hN hNs hSc hNNs hD hDNs hsp0 hsp1 hb0 hb1 hδ0 hδ1 hbox
    have hNs' : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hq : (D : ℝ) / (Ns : ℝ) ≤ 1 := by
      rw [div_le_one hNs']; exact_mod_cast hDNs
    have h1 : (1 : ℝ) * δ ^ 1 * ((D : ℝ)/(Ns:ℝ))^1 ≤ δ := by
      rw [pow_one, pow_one, one_mul]
      nlinarith [hδ0, hq]
    exact le_trans h1 hbox
  · have hs3 : 3 ≤ s := by omega
    obtain ⟨A, Bv, hA, hBv, cc₂, hcc₂pos, hbody⟩ := iterate_steps hK hstep htop s hs
    obtain ⟨C₁, hC₁pos, hC₁u⟩ := sparse_to_dense_uniform (t := s) hs P.leadingCoeff hc₀
    set κ : ℝ := 1 / (1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ)) with hκ
    have hκpos : 0 < κ := by
      rw [hκ]
      exact div_pos one_pos (by positivity)
    have habs : (0 : ℝ) < |(((P.leadingCoeff : ℤ)) : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast hc₀)
    refine ⟨A, Bv, hA, hBv, cc₂ * (κ * C₁) ^ A * |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv / 4,
      div_pos (mul_pos (mul_pos hcc₂pos (pow_pos (mul_pos hκpos hC₁pos) A)) (pow_pos habs Bv))
        (by norm_num), ?_⟩
    intro Ns N D f₀ f₁ δ hd hN hNs hSc hNNs hD hDNs hsp0 hsp1 hb0 hb1 hδ0 hδ1 hbox
    set Dd : ℕ := P.leadingCoeff.natAbs * D with hDd
    set Bx : ℕ := dSup P Ns N + 2 * (s - 2) * Dd with hBx
    set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
    set CL : ℝ := ((symIcc (dSup P Ns N)).card : ℝ) with hCL
    set CB : ℝ := ((symIcc Bx).card : ℝ) with hCB
    have hCLpos : 0 < CL := by
      rw [hCL]; exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    have hCBpos : 0 < CB := by
      rw [hCB]; exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    have hDd1 : 1 ≤ Dd := by
      rw [hDd]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hB1 : 1 ≤ Bx := by
      rw [hBx]
      have h1 : 1 ≤ dSup P Ns N := by
        have : Ns ≤ dSup P Ns N := Nat.le_add_right _ _
        omega
      exact le_trans h1 (Nat.le_add_right _ _)
    have hDdB : Dd ≤ Bx := by
      rw [hBx]
      have h2 : (1 : ℕ) * Dd ≤ 2 * (s - 2) * Dd := by
        have : 1 ≤ 2 * (s - 2) := by omega
        exact Nat.mul_le_mul_right Dd this
      exact le_trans (by simpa using h2) (Nat.le_add_left _ _)
    obtain ⟨hbF, hsuppB⟩ := dualFn_data hN hNNs (le_refl (dSup P Ns N)) hsp0 hsp1 hb0 hb1
    have hsuppL : ∀ x : ℤ, x ∉ symIcc (dSup P Ns N) → F x = 0 := by
      intro x hx
      rw [hF]
      exact hsuppB x (fun h => hx (by rw [mem_symIcc_iff] at h ⊢; omega))
    have hbF' : ∀ x : ℤ, ‖F x‖ ≤ 1 := by intro x; rw [hF]; exact hbF x
    have hsuppB' : ∀ x : ℤ, x ∉ symIcc Bx → F x = 0 := by
      intro x hx
      exact hsuppL x (fun h => hx (by rw [mem_symIcc_iff] at h ⊢; omega))
    have hC₁ := hC₁u D hD (dSup P Ns N) F hbF' hsuppL
    have hboxL : δ ≤ boxNormPow s (fun _ : Fin s => arithIcc P.leadingCoeff D)
        (symIcc (dSup P Ns N)) F := by
      have h1 := hbox
      rw [hF] at h1
      simpa only [uNormPow] using h1
    have hdenseL : C₁ * δ ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 Dd)
        (symIcc (dSup P Ns N)) F := by
      have h := mul_le_mul_of_nonneg_left hboxL hC₁pos.le
      rw [hDd]
      exact le_trans h hC₁
    have hcardCL : CL = 2 * (((dSup P Ns N) : ℕ) : ℝ) + 1 := by
      rw [hCL, card_symIcc]; push_cast; ring
    have hcardCB : CB = 2 * ((Bx : ℕ) : ℝ) + 1 := by
      rw [hCB, card_symIcc]; push_cast; ring
    have hDs : Dd ≤ P.leadingCoeff.natAbs * dSup P Ns N := by
      rw [hDd]
      exact Nat.mul_le_mul_left _ (le_trans (by exact_mod_cast hDNs) (Nat.le_add_right _ _))
    have hCBle : CB ≤ CL * (1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ)) := by
      rw [hcardCL, hcardCB, hBx]
      push_cast
      have h1 : ((Dd : ℕ) : ℝ) ≤ ((P.leadingCoeff.natAbs : ℕ) : ℝ) * ((dSup P Ns N : ℕ) : ℝ) := by
        exact_mod_cast hDs
      have h2 : (0 : ℝ) ≤ ((dSup P Ns N : ℕ) : ℝ) := by positivity
      nlinarith [h1, h2]
    have hratio_ge : κ ≤ CL / CB := by
      rw [hκ, le_div_iff₀ hCBpos]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
        (0:ℝ) < 1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ))]
      simpa using hCBle
    have hboxB : CL / CB * (C₁ * δ) ≤
        boxNormPow s (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx) F := by
      have h := boxNormPow_eq_mul_card s (fun _ : Fin s => arithIcc 1 Dd)
        (symIcc Bx) (symIcc (dSup P Ns N)) F (by simp [symIcc])
      rw [← hCL, ← hCB] at h
      rw [h]
      exact mul_le_mul_of_nonneg_left hdenseL (div_nonneg hCLpos.le hCBpos.le)
    have hθbox : κ * (C₁ * δ) ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx) F :=
      le_trans (mul_le_mul_of_nonneg_right hratio_ge (mul_nonneg hC₁pos.le hδ0.le)) hboxB
    have hθ0 : 0 < κ * (C₁ * δ) := mul_pos hκpos (mul_pos hC₁pos hδ0)
    have hθ1 : κ * (C₁ * δ) ≤ 1 := by
      refine le_trans hθbox ?_
      simpa using boxNormPow_le_of_bound (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx)
        zero_le_one hbF' hsuppB'
    have hcast : ((Dd : ℕ) : ℝ) = |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) := by
      rw [hDd, Nat.cast_mul, natAbs_cast_real]
    have hratio : ((Dd : ℕ) : ℝ) ≤ K * (Ns : ℝ) := by
      rw [hcast]
      have hDle : (D : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hDNs
      have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
      nlinarith [hKc, hDle, hD0, hK.le]
    have hbound := hbody Bx Ns N Dd f₀ f₁ (κ * (C₁ * δ))
      hN hNs hSc hNNs hDd1 hratio hsp0 hsp1 hb0 hb1 (by rw [hBx]) hθ0 hθ1 hθbox
    have hcDB : (D : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ (Bx : ℝ) := by
      have h2 : ((Dd : ℕ) : ℝ) ≤ (Bx : ℝ) := by exact_mod_cast hDdB
      linarith [hcast, h2]
    have hspB : SupportIn F Bx := by
      intro x hx
      exact hsuppB' x (by rw [mem_symIcc_iff]; omega)
    have hC₃ := dense_le_apBoxNorm (c := P.leadingCoeff) (D := D) (N := Bx) hc₀ hD hB1 hcDB
      hbF' hspB
    have hshrink : boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc Bx) F ≤
        boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) F := by
      refine boxNormPow_le_of_subset _ ?_ (by simp [symIcc]) F
      intro x hx
      rw [symIcc, Finset.mem_Icc] at hx
      rw [symIcc, Finset.mem_Icc]
      omega
    have hgoal : cc₂ * (κ * C₁) ^ A * |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv / 4 *
          δ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ Bv
        = (1 / 4) * (cc₂ * (κ * (C₁ * δ)) ^ A * (((Dd : ℕ) : ℝ) / (Ns : ℝ)) ^ Bv) := by
      have h1 : (κ * (C₁ * δ)) ^ A = (κ * C₁) ^ A * δ ^ A := by
        rw [show κ * (C₁ * δ) = κ * C₁ * δ from by ring, mul_pow]
      have h2 : (((Dd : ℕ) : ℝ) / (Ns : ℝ)) ^ Bv =
          |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv * ((D : ℝ) / (Ns : ℝ)) ^ Bv := by
        rw [hcast]
        rw [show |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) / (Ns : ℝ) =
            |(((P.leadingCoeff : ℤ)) : ℝ)| * ((D : ℝ) / (Ns : ℝ)) from by ring, mul_pow]
      rw [h2, h1]
      ring
    rw [hgoal]
    exact le_trans (mul_le_mul_of_nonneg_left hbound (by norm_num)) (le_trans hC₃ hshrink)

end

end Work.Peluse.Ulower
