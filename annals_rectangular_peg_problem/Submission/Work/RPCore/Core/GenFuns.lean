import Submission.Work.RPCore.Core.Steps
import Submission.Work.RPCore.GenFun.exists_type2GF
import Submission.Work.RPCore.GenFun.wrot_isType2GF

/-!
# Type-2 generating functions of the `3N` chain steps

For the assembly of `Work.RPCore.Core.core` each of the `3N` steps of the decomposition of
`Φ_1⁻¹ ∘ τ_θ ∘ Φ_1` (see `Core/Steps`) has a global type-2 generating function (`Work.RPV.IsType2GF`):

* the flow slices `Phi Hh a b` are near-identity symplectic maps with a compactly supported,
  `2π`-periodic generating function, supplied by `GenFun.exists_type2GF`;
* the rotation slices `tau δ` (`|δ| < π/2`) have the explicit generating function `Wrot δ`
  (`GenFun.wrot_isType2GF`).

`gfFam Hh N hN δ hKN` is this family of generating functions, and `gfFam_mid`, `gfFam_contDiff`,
`gfFam_per`, `gfFam_sup`, `gfFam_isType2GF` record the hypotheses that the saddle-point step
(`Core.ChainHasCrit`) requires.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Core

open Work.RPV Work.RPCore.Chain Work.RPCore.Flow Work.RPCore.GenFun

theorem contDiff_Wrot (δ : ℝ) : ContDiff ℝ 3 (Wrot δ) := by
  unfold Wrot
  fun_prop

theorem Wrot_Tk (δ : ℝ) (x : PS) : Wrot δ (Tk 1 x) = Wrot δ x := by
  simp [Wrot, Tk]

/-- A generating function of the flow slice `Phi Hh a b`, obtained from `exists_type2GF`
(the slice is `C³`, symplectic, `2π`-equivariant, identity outside the slab, and near the
identity as soon as `Real.exp (K |b - a|) - 1 ≤ 1/4`). -/
noncomputable def sliceGF (Hh : CptPerHam) (a b : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 2)
    (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hsm : Real.exp ((clampedData Hh).K * |b - a|) - 1 ≤ 1 / 4) : PS → ℝ :=
  Classical.choose (exists_type2GF (Phi Hh a b) (Phi_contDiff Hh a b)
    (fun x u v => Phi_symplectic Hh ha hb x u v)
    (fun x => le_trans (Phi_nearId Hh ha hb x) hsm)
    (Phi_Tk Hh a b) Hh.R (fun x hx => Phi_slab Hh hx))

theorem sliceGF_spec (Hh : CptPerHam) (a b : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 2)
    (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hsm : Real.exp ((clampedData Hh).K * |b - a|) - 1 ≤ 1 / 4) :
    ContDiff ℝ 3 (sliceGF Hh a b ha hb hsm) ∧
    IsType2GF (Phi Hh a b) (sliceGF Hh a b ha hb hsm) ∧
    (∀ x, sliceGF Hh a b ha hb hsm (Tk 1 x) = sliceGF Hh a b ha hb hsm x) ∧
    (∃ R, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → sliceGF Hh a b ha hb hsm x = 0) := by
  have h := Classical.choose_spec (show ∃ W : PS → ℝ,
      ContDiff ℝ 3 W ∧ IsType2GF (Phi Hh a b) W ∧
      (∀ x, W (Tk 1 x) = W x) ∧
      ∃ R, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → W x = 0 from
    exists_type2GF (Phi Hh a b) (Phi_contDiff Hh a b)
      (fun x u v => Phi_symplectic Hh ha hb x u v)
      (fun x => le_trans (Phi_nearId Hh ha hb x) hsm)
      (Phi_Tk Hh a b) Hh.R (fun x hx => Phi_slab Hh hx))
  simpa only [sliceGF] using h

/-- The smallness hypothesis for a forward slice: the slice length is `1/N`. -/
theorem hsm_of_sub {K : ℝ} {N : ℕ} {a b : ℝ} (hab : b - a = 1 / (N : ℝ))
    (hKN : Real.exp (K / N) - 1 ≤ 1 / 4) :
    Real.exp (K * |b - a|) - 1 ≤ 1 / 4 := by
  rw [hab, abs_of_nonneg (by positivity), mul_one_div]
  exact hKN

/-- The smallness hypothesis for a backward slice: the slice length is `1/N`. -/
theorem hsm_of_pred {K : ℝ} {N m : ℕ} (hm : 1 ≤ m)
    (hKN : Real.exp (K / N) - 1 ≤ 1 / 4) :
    Real.exp (K * |ph N (m - 1) - ph N m|) - 1 ≤ 1 / 4 := by
  rw [ph_pred_sub N m hm, mul_one_div]
  exact hKN

/-- The family of generating functions of the `3N` steps: the generating function of the flow
slice on the two outer blocks and `Wrot δ` on the middle block. -/
noncomputable def gfFam (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (j : Fin (n + 1)) : PS → ℝ :=
  if _h : (j : ℕ) < N then
    sliceGF Hh (ph N (j : ℕ)) (ph N ((j : ℕ) + 1))
      (ph_mem_Icc N (j : ℕ) hN (by omega))
      (ph_mem_Icc N ((j : ℕ) + 1) hN (by omega))
      (hsm_of_sub (ph_succ_sub N (j : ℕ)) hKN)
  else if _h2 : (j : ℕ) < 2 * N then Wrot δ
  else
    sliceGF Hh (ph N (3 * N - (j : ℕ))) (ph N (3 * N - (j : ℕ) - 1))
      (ph_mem_Icc N (3 * N - (j : ℕ)) hN (by omega))
      (ph_mem_Icc N (3 * N - (j : ℕ) - 1) hN (by omega))
      (hsm_of_pred (N := N) (m := 3 * N - (j : ℕ)) (by omega) hKN)

theorem gfFam_mid (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (j : Fin (n + 1))
    (hj : midBlock N (j : ℕ)) : gfFam Hh n N hN hn δ hKN j = Wrot δ := by
  unfold gfFam
  rw [dif_neg (not_lt.mpr hj.1), dif_pos hj.2]

theorem gfFam_contDiff (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (j : Fin (n + 1)) :
    ContDiff ℝ 3 (gfFam Hh n N hN hn δ hKN j) := by
  unfold gfFam
  by_cases h : (j : ℕ) < N
  · rw [dif_pos h]
    exact (sliceGF_spec Hh _ _ _ _ _).1
  · rw [dif_neg h]
    by_cases h2 : (j : ℕ) < 2 * N
    · rw [dif_pos h2]
      exact contDiff_Wrot δ
    · rw [dif_neg h2]
      exact (sliceGF_spec Hh _ _ _ _ _).1

theorem gfFam_per (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (j : Fin (n + 1)) (x : PS) :
    gfFam Hh n N hN hn δ hKN j (Tk 1 x) = gfFam Hh n N hN hn δ hKN j x := by
  unfold gfFam
  by_cases h : (j : ℕ) < N
  · rw [dif_pos h]
    exact (sliceGF_spec Hh _ _ _ _ _).2.2.1 x
  · rw [dif_neg h]
    by_cases h2 : (j : ℕ) < 2 * N
    · rw [dif_pos h2]
      exact Wrot_Tk δ x
    · rw [dif_neg h2]
      exact (sliceGF_spec Hh _ _ _ _ _).2.2.1 x

theorem gfFam_sup (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (j : Fin (n + 1))
    (hj : ¬ midBlock N (j : ℕ)) :
    ∃ R : ℝ, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → gfFam Hh n N hN hn δ hKN j x = 0 := by
  unfold gfFam
  by_cases h : (j : ℕ) < N
  · rw [dif_pos h]
    exact (sliceGF_spec Hh _ _ _ _ _).2.2.2
  · rw [dif_neg h]
    by_cases h2 : (j : ℕ) < 2 * N
    · exact absurd ⟨Nat.not_lt.mp h, h2⟩ hj
    · rw [dif_neg h2]
      exact (sliceGF_spec Hh _ _ _ _ _).2.2.2

theorem gfFam_isType2GF (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4) (hδ : |δ| < Real.pi / 2)
    (j : Fin (n + 1)) :
    IsType2GF (stepMap Hh n N δ j) (gfFam Hh n N hN hn δ hKN j) := by
  by_cases h : (j : ℕ) < N
  · rw [stepMap_of_lt Hh n N δ h]
    unfold gfFam
    rw [dif_pos h]
    exact (sliceGF_spec Hh _ _ _ _ _).2.1
  · by_cases h2 : (j : ℕ) < 2 * N
    · rw [stepMap_of_mid Hh n N δ h h2]
      unfold gfFam
      rw [dif_neg h, dif_pos h2]
      exact wrot_isType2GF δ hδ
    · rw [stepMap_of_late Hh n N δ h h2]
      unfold gfFam
      rw [dif_neg h, dif_neg h2]
      exact (sliceGF_spec Hh _ _ _ _ _).2.1

end Work.RPCore.Core
