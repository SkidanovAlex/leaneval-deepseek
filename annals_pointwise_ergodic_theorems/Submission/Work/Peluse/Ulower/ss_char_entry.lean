import Mathlib
import Submission.Work.Peluse.Ulower.helpers
import Submission.Work.Peluse.Ulower.boxSumPow_neg
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one
import Submission.Work.Peluse.Ulower.char_dilate_le
import Submission.Work.Peluse.Ulower.ss_decimate
import Submission.Work.Peluse.Ulower.dSup_div_add_one_le
import Submission.Work.Peluse.Ulower.symIcc_ratio_lower
import Submission.Work.Peluse.Ulower.const_compare

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **The `U²`-inverse entry of the `Ulower` chain, for the dual function** (Peluse's Lemma 2.4 /
Lemma 3.11 entry, arXiv:1909.00309 §9).

From a *level* lower bound `δ` for the second-order box norm of the dual function
`F₂ = dualFn N P f₀ f₁` at the shift set `c[D] = arithIcc P.leadingCoeff D` (`c = P.leadingCoeff`)
and the support box `symIcc (dSup P Ns N)`, with `f₀,f₁` 1-bounded supported in `[-Ns,Ns]`,
`Ns ≍ N^d` (`Scaled Ns N P.natDegree`), `1 ≤ D ≤ Ns`, one gets a **Fourier coefficient of `F₂` of
size proportional to `Ns`**:
`∃ξ, C₀ δ^{K₀} (D/Ns)^{K₀} Ns ≤ ‖∑_x F₂(x) e(ξx)‖`.

Route (all pieces already PROVED in the workspace):
1. the dilation identity `Work.Peluse.Ulower.boxNormPow_two_dilate`:
   `boxNormPow 2 (arithIcc c D) (symIcc L) F
     = |symIcc L|⁻¹ ∑_{r < |c|} |symIcc (L/|c|+1)| ·
         boxNormPow 2 (arithIcc 1 D) (symIcc (L/|c|+1)) (fun z => F (c z + r))`,
   `L = dSup P Ns N`; hence (pigeonholing over `r < |c|`) some decimate `g_r` has box norm
   `η ≥ c_P δ` with `c_P = |symIcc L|/(|c|·|symIcc (L/|c|+1)|) ≥` a constant depending only on `P`
   (use `Scaled` to see `L ≤ Ns·(1 + 2∑|a_i|)`);
2. `SupportIn g_r L'` for `L' := L/|c| + 1` (if `|z| > L'` then `|c z + r| > L`), and
   `g_r` is 1-bounded;
3. `Work.Peluse.Ulower.char_of_boxNormPow_two h1` (PROVED, in `Ulower/helpers.lean`) applied to
   `g_r` with radius `L'' := max L' D` (so that `D ≤ L''`, using `SupportIn.mono`): gives
   `∃β, C₀' η^{K₀'} (D/L'')^{K₀'} L'' ≤ ‖∑_z g_r z e(βz)‖`;
4. `Work.Peluse.Ulower.ss_char_dilate` (proved in this same directory as
   `Submission/Work/Peluse/Ulower/ss_char_dilate.lean`) turns that into a Fourier coefficient of
   `F₂` itself (the frequency changes to some `ξ`);
5. bookkeeping: `(Ns/L'')^{K₀'-1} ≥` a constant depending only on `P` (by `Scaled`), so a suitable
   `C₀ > 0` and `K₀ := K₀'` give the claim; `P.leadingCoeff ≠ 0` since `2 ≤ P.natDegree`.

The statement is *false* without `Scaled` (take `P = M X²` with `M ≫ Ns` in `L'' = max L' D`), and
false without `(D : ℝ) ≤ (Ns : ℝ)`; both are hypotheses here. -/
theorem ss_char_entry {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        1 ≤ N → 1 ≤ Ns → 1 ≤ D → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
        (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) →
        ∃ ξ : ℝ, C₀ * δ ^ K₀ * ((D : ℝ) / (Ns : ℝ)) ^ K₀ * (Ns : ℝ) ≤
          ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ := by
  obtain ⟨C₀', hC₀', K₀', hK₀'1, hchar⟩ := char_of_boxNormPow_two h1
  have hPne : P ≠ 0 := by intro hzero; rw [hzero] at hd; simp at hd
  have hclead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hclead1 : 1 ≤ P.leadingCoeff.natAbs := Int.natAbs_pos.mpr hclead
  have hAmaxpos : 0 < (ssAmax P : ℝ) := by exact_mod_cast ssAmax_pos P
  have hcnpos : (0 : ℝ) < ((P.leadingCoeff).natAbs : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hclead1)
  refine ⟨C₀' * (2 / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ))) ^ K₀' /
      (ssAmax P : ℝ) ^ (K₀' - 1), ?_, K₀', hK₀'1, ?_⟩
  · have hb1 : 0 < (2 : ℝ) / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) := by positivity
    exact div_pos (mul_pos hC₀' (pow_pos hb1 K₀')) (pow_pos hAmaxpos (K₀' - 1))
  · intro Ns N D f₀ f₁ δ hN hNs hD1 hSc hNNs hDNs hsupp0 hsupp1 hb0 hb1 hδ0 hδ1 hbox
    have hsuppF : Work.Peluse.SupportIn (Work.Peluse.dualFn N P f₀ f₁) (Work.Peluse.dSup P Ns N) :=
      Work.Peluse.Tools.dualFn_supportIn (by omega) P f₀ f₁ hsupp0 hsupp1 hNNs
    have hbndF : ∀ x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖ ≤ 1 :=
      Work.Peluse.Ulower.dualFn_norm_le_one hN P f₀ f₁ hb0 hb1
    have hbox' : δ ≤ Work.Peluse.boxNormPow 2
        (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) := hbox
    obtain ⟨r, hr, hηdec⟩ := ss_decimate hclead hD1 hsuppF hbndF hδ0 hbox'
    set L'' : ℕ := max ((Work.Peluse.dSup P Ns N) / P.leadingCoeff.natAbs + 1) D with hL''def
    have hL''1 : 1 ≤ L'' := le_trans hD1 (le_max_right _ _)
    have hL''D : D ≤ L'' := le_max_right _ _
    have hgsupp : Work.Peluse.SupportIn
        (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))) L'' := by
      rw [hL''def]
      exact ss_support_dilate hclead (D := D) (L := Work.Peluse.dSup P Ns N)
        (fun z => Work.Peluse.dualFn N P f₀ f₁ z) hsuppF r hr
    have hgbnd : ∀ z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))‖ ≤ 1 :=
      fun z => hbndF _
    set η : ℝ := ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
        ((P.leadingCoeff.natAbs : ℝ) * ((Work.Peluse.symIcc L'').card : ℝ)) * δ with hηdef
    have hηdec' : η ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
        (Work.Peluse.symIcc L'')
          (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))) := by
      rw [hηdef, hL''def]
      exact hηdec
    have hηpos : 0 < η := by
      have hs : (0:ℝ) < ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) := by
        have : 0 < (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card := by rw [card_symIcc]; positivity
        exact_mod_cast this
      have hs2 : (0:ℝ) < ((Work.Peluse.symIcc L'').card : ℝ) := by
        have : 0 < (Work.Peluse.symIcc L'').card := by rw [card_symIcc]; positivity
        exact_mod_cast this
      rw [hηdef]
      positivity
    have hηle1 : η ≤ 1 := by
      refine le_trans hηdec' ?_
      refine Work.Peluse.BoxNorm.boxNormPow_le_one hgbnd ?_
      intro x hx
      exact hgsupp x (Nat.lt_of_not_le (by rwa [symIcc_mem_iff] at hx))
    obtain ⟨β, hβ⟩ := hchar L'' D
      (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ)))
      η hL''1 hD1 (by exact_mod_cast hL''D) hgsupp hgbnd hηpos hηle1 hηdec'
    have hsumF : Summable (fun x : ℤ => ‖Work.Peluse.dualFn N P f₀ f₁ x‖) := by
      apply summable_of_ne_finset_zero (s := Work.Peluse.symIcc (Work.Peluse.dSup P Ns N))
      intro x hx
      rw [norm_eq_zero]
      exact hsuppF x (Nat.lt_of_not_le (by rwa [symIcc_mem_iff] at hx))
    obtain ⟨ξ, hξ⟩ := char_dilate_le (F := Work.Peluse.dualFn N P f₀ f₁) hclead hsumF r hr β
    have hβ' : C₀' * η ^ K₀' * ((D:ℝ)/(L'':ℝ)) ^ K₀' * (L'':ℝ) ≤
        ‖∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
          * Work.Peluse.ee (β * (z:ℝ))‖ := by
      have hcongr : (∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Complex.exp (2 * Real.pi * Complex.I * (β:ℂ) * (z:ℂ)))
          = ∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Work.Peluse.ee (β * (z:ℝ)) := by
        refine tsum_congr (fun z => ?_)
        rw [Work.Peluse.exp_mul_eq_ee]
      rw [← hcongr]
      exact hβ
    have hL''Amax_nat : L'' ≤ ssAmax P * Ns := by
      rw [hL''def]
      refine max_le ?_ ?_
      · exact dSup_div_add_one_le (P := P) (c := P.leadingCoeff) (by omega) hclead1 hNs hN hSc
      · calc D ≤ Ns := Nat.cast_le.mp hDNs
          _ ≤ ssAmax P * Ns := Nat.le_mul_of_pos_left Ns (ssAmax_pos P)
    have hL''Amax : (L'':ℝ) ≤ (ssAmax P : ℝ) * (Ns:ℝ) := by
      rw [← Nat.cast_mul]; exact_mod_cast hL''Amax_nat
    have hL''pos : (0:ℝ) < (L'':ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL''1)
    have hNspos : (0:ℝ) < (Ns:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs)
    have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
    have hratio : 2 / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) ≤
        ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
          (((P.leadingCoeff).natAbs : ℝ) * ((Work.Peluse.symIcc L'').card : ℝ)) := by
      have htmp : max ((Work.Peluse.dSup P Ns N) / P.leadingCoeff.natAbs + 1) D ≤ ssAmax P * Ns := by
        rw [← hL''def]; exact hL''Amax_nat
      have h := symIcc_ratio_lower (P := P) (c := P.leadingCoeff) hclead hclead1 hNs hD1 htmp
      rw [hL''def]
      exact h
    have hηlb : 2 / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) * δ ≤ η := by
      rw [hηdef]
      exact mul_le_mul_of_nonneg_right hratio hδ0.le
    refine ⟨ξ, ?_⟩
    calc C₀' * (2 / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ))) ^ K₀' /
            (ssAmax P : ℝ) ^ (K₀' - 1) * δ ^ K₀' * ((D:ℝ)/(Ns:ℝ)) ^ K₀' * (Ns:ℝ)
        ≤ C₀' * η ^ K₀' * ((D:ℝ)/(L'':ℝ)) ^ K₀' * (L'':ℝ) :=
          const_compare (K := K₀') (C := C₀') (δ := δ) (η := η)
            (cmin := 2 / (3 * (ssAmax P : ℝ) * ((P.leadingCoeff).natAbs : ℝ)))
            (Amax := (ssAmax P : ℝ)) (Ns := (Ns:ℝ)) (D := (D:ℝ)) (L'' := (L'':ℝ))
            hK₀'1 hC₀' (by positivity) hAmaxpos hδ0 hDpos hηlb hNspos hL''pos hL''Amax
      _ ≤ ‖∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Work.Peluse.ee (β * (z:ℝ))‖ := hβ'
      _ ≤ ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * Work.Peluse.ee (ξ * (x:ℝ))‖ := hξ
      _ = ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ := by
            congr 1
            exact tsum_congr (fun x => by rw [ss_ee_eq_exp])


end

end Work.Peluse.Ulower
