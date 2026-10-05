import Mathlib
import Submission.Work.RPB.B3.EsTauAux
import Submission.Work.RPB.B3.esTauMultiLin

/-!
# Jet matching for the finite reflection

If `h` is `C^N` on the right half `esHalfR δ` of the box `(-1,1) × ℝ × (-δ,δ)`, then the finite
reflection `z ↦ ∑ j, a j • h (reflLin (c j) z)` (whose weights reproduce `1` on powers of `c j`
up to order `N`) is `C^N` on the left half, and the two functions have the same `m`-th iterated
derivatives (`m ≤ N`) at every point of the seam `{τ = 0}`.

The left-half version `esTauJetMatchL` is deduced from the right-half one by composing with the
negation `τ ↦ -τ`.
-/

open scoped ContDiff Topology
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B3

/-- **Jet matching, right half.**  If `h` is `C^N` on `esHalfR δ`, then its finite reflection
`∑ j, a j • h (reflLin (c j) ·)` has the same iterated derivatives as `h` at the seam `τ = 0`. -/
theorem esTauJetMatchR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ × (ℝ × ℝ) → E) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hh : ContDiffOn ℝ N h (esHalfR δ))
    {n : ℕ} (c a : Fin n → ℝ) (hc : ∀ j, c j ∈ Set.Ioo (-1) 0)
    (hid : ∀ m : ℕ, m ≤ N → ∑ j, a j * (c j)^m = 1) :
    ∀ z ∈ esBox δ, z.1 = 0 → ∀ m : ℕ, m ≤ N →
      iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (reflLin (c j) z)) (esHalfL δ) z
        = iteratedFDerivWithin ℝ m h (esHalfR δ) z := by
  intro z hzbox hz0 m hm
  have hzL : z ∈ esHalfL δ := ⟨hzbox, by show z.1 ≤ 0; rw [hz0]⟩
  -- each summand is `C^m` at `z`
  have hcd : ∀ j, ContDiffWithinAt ℝ m (fun z => h (reflLin (c j) z)) (esHalfL δ) z := fun j =>
    (((hh.comp_continuousLinearMap (reflLin (c j))).mono
      (esHalfL_subset_preimage_halfR (hc j))).of_le (Nat.cast_le.mpr hm)).contDiffWithinAt hzL
  have hsummand : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ContDiffWithinAt ℝ m (fun z => a j • h (reflLin (c j) z)) (esHalfL δ) z :=
    fun j _ => (hcd j).const_smul (a j)
  -- step 1: linearity in the sum
  have hstep1 : iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (reflLin (c j) z)) (esHalfL δ) z
      = ∑ j, a j • iteratedFDerivWithin ℝ m (fun z => h (reflLin (c j) z)) (esHalfL δ) z := by
    rw [iteratedFDerivWithin_fun_sum_apply (uniqueDiffOn_esHalfL hδ) hzL hsummand]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact iteratedFDerivWithin_const_smul_apply (hcd j) (uniqueDiffOn_esHalfL hδ) hzL
  -- step 2: chain rule for the reflection
  have hstep2 : ∀ j, iteratedFDerivWithin ℝ m (fun z => h (reflLin (c j) z)) (esHalfL δ) z
      = (iteratedFDerivWithin ℝ m h (esHalfR δ) (reflLin (c j) z)).compContinuousLinearMap
          (fun _ : Fin m => reflLin (c j)) := by
    intro j
    have hUdiff : UniqueDiffOn ℝ ((reflLin (c j)) ⁻¹' esHalfR δ) := by
      rw [preimage_halfR_eq (hc j).2]
      exact uniqueDiffOn_halfBand (by exact one_div_neg.mpr (hc j).2) hδ
    have hev : esHalfL δ =ᶠ[𝓝 z] ((reflLin (c j)) ⁻¹' esHalfR δ) := by
      rw [esHalfL_eq_halfBand, preimage_halfR_eq (hc j).2]
      exact halfBand_eventuallyEq (hc j) hz0
    rw [iteratedFDerivWithin_congr_set hev m]
    exact ContinuousLinearMap.iteratedFDerivWithin_comp_right (reflLin (c j))
      (hh.of_le (Nat.cast_le.mpr hm))
      (uniqueDiffOn_esHalfR hδ) hUdiff (esHalfL_subset_preimage_halfR (hc j) hzL) le_rfl
  -- step 3: the multilinear identity
  have hstep3 : (∑ j, a j • iteratedFDerivWithin ℝ m (fun z => h (reflLin (c j) z))
        (esHalfL δ) z) = iteratedFDerivWithin ℝ m h (esHalfR δ) z := by
    have hzj : ∀ j, reflLin (c j) z = z := fun j => by
      obtain ⟨τ, s, r⟩ := z
      simp only at hz0
      simp [reflLin_apply, hz0]
    simp only [hstep2, hzj]
    exact esTauMultiLin c a (fun m' hm' => hid m' (le_trans hm' hm))
      (iteratedFDerivWithin ℝ m h (esHalfR δ) z)
  rw [hstep1, hstep3]

/-- Negation of the `τ`-coordinate, as a continuous linear equivalence. -/
def tauNeg : (ℝ × (ℝ × ℝ)) ≃L[ℝ] (ℝ × (ℝ × ℝ)) where
  toFun := reflLin (-1)
  invFun := reflLin (-1)
  map_add' := (reflLin (-1)).map_add
  map_smul' := (reflLin (-1)).map_smul
  left_inv := fun z => by obtain ⟨τ, s, r⟩ := z; simp [reflLin]
  right_inv := fun z => by obtain ⟨τ, s, r⟩ := z; simp [reflLin]
  continuous_toFun := (reflLin (-1)).continuous
  continuous_invFun := (reflLin (-1)).continuous

@[simp] theorem tauNeg_apply (z : ℝ × (ℝ × ℝ)) : tauNeg z = (-z.1, z.2.1, z.2.2) := by
  obtain ⟨τ, s, r⟩ := z; simp [tauNeg, reflLin]

theorem mem_tauNeg_esBox (δ : ℝ) (z : ℝ × (ℝ × ℝ)) : tauNeg z ∈ esBox δ ↔ z ∈ esBox δ := by
  rw [mem_esBox, mem_esBox, tauNeg_apply]
  simp only [Prod.fst, Prod.snd]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩, h2⟩

theorem preimage_tauNeg_box (δ : ℝ) : tauNeg ⁻¹' esBox δ = esBox δ := by
  ext z; rw [Set.mem_preimage, mem_tauNeg_esBox]

theorem preimage_tauNeg_halfL (δ : ℝ) : tauNeg ⁻¹' esHalfL δ = esHalfR δ := by
  ext z
  simp only [Set.mem_preimage, tauNeg_apply, esHalfL, esHalfR, esBox, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_Ioo, Set.mem_univ, Set.mem_setOf_eq, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, h2⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, h2⟩, by linarith⟩

theorem preimage_tauNeg_halfR (δ : ℝ) : tauNeg ⁻¹' esHalfR δ = esHalfL δ := by
  ext z
  simp only [Set.mem_preimage, tauNeg_apply, esHalfL, esHalfR, esBox, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_Ioo, Set.mem_univ, Set.mem_setOf_eq, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, h2⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, h2⟩, by linarith⟩

/-- **Jet matching, left half.**  Mirror image of `esTauJetMatchR`. -/
theorem esTauJetMatchL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ × (ℝ × ℝ) → E) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hh : ContDiffOn ℝ N h (esHalfL δ))
    {n : ℕ} (c a : Fin n → ℝ) (hc : ∀ j, c j ∈ Set.Ioo (-1) 0)
    (hid : ∀ m : ℕ, m ≤ N → ∑ j, a j * (c j)^m = 1) :
    ∀ z ∈ esBox δ, z.1 = 0 → ∀ m : ℕ, m ≤ N →
      iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (reflLin (c j) z)) (esHalfR δ) z
        = iteratedFDerivWithin ℝ m h (esHalfL δ) z := by
  intro z hzbox hz0 m hm
  have hz0' : (tauNeg z).1 = 0 := by simp [hz0]
  have hzbox' : tauNeg z ∈ esBox δ := (mem_tauNeg_esBox δ z).mpr hzbox
  have hzL : z ∈ esHalfL δ := ⟨hzbox, by show z.1 ≤ 0; rw [hz0]⟩
  have hzR : z ∈ esHalfR δ := ⟨hzbox, by show 0 ≤ z.1; rw [hz0]⟩
  have hmemL : tauNeg z ∈ esHalfL δ := by
    have : z ∈ (tauNeg ⁻¹' esHalfL δ) := by rw [preimage_tauNeg_halfL δ]; exact hzR
    exact this
  have hmemR : tauNeg z ∈ esHalfR δ := by
    have : z ∈ (tauNeg ⁻¹' esHalfR δ) := by rw [preimage_tauNeg_halfR δ]; exact hzL
    exact this
  have hh' : ContDiffOn ℝ N (fun w => h (tauNeg w)) (esHalfR δ) := by
    rw [← preimage_tauNeg_halfL δ]
    exact hh.comp_continuousLinearMap (tauNeg : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)))
  have hR0 := esTauJetMatchR (fun w => h (tauNeg w)) N hδ hh' c a hc hid
    (tauNeg z) hzbox' hz0' m hm
  have hR : iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (tauNeg (reflLin (c j) z)))
        (esHalfL δ) (tauNeg z)
      = iteratedFDerivWithin ℝ m (fun w => h (tauNeg w)) (esHalfR δ) (tauNeg z) := hR0
  have hAν : (fun z => ∑ j, a j • h (reflLin (c j) z))
      = (fun z => ∑ j, a j • h (tauNeg (reflLin (c j) z))) ∘ tauNeg := by
    funext w
    simp only [Function.comp_apply, tauNeg_apply, reflLin_apply']
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2
    ring
  have hνh : (fun w => h (tauNeg w)) ∘ tauNeg = (h : ℝ × (ℝ × ℝ) → E) := by
    funext w; simp [Function.comp_apply, tauNeg_apply]
  have hcompX := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right tauNeg
    (fun z => ∑ j, a j • h (tauNeg (reflLin (c j) z))) (uniqueDiffOn_esHalfL hδ) hmemL m
  rw [preimage_tauNeg_halfL δ] at hcompX
  have hcompY := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right tauNeg
    (fun w => h (tauNeg w)) (uniqueDiffOn_esHalfR hδ) hmemR m
  rw [preimage_tauNeg_halfR δ] at hcompY
  calc iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (reflLin (c j) z)) (esHalfR δ) z
      = iteratedFDerivWithin ℝ m ((fun z => ∑ j, a j • h (tauNeg (reflLin (c j) z))) ∘ tauNeg)
          (esHalfR δ) z := by rw [hAν]
    _ = (iteratedFDerivWithin ℝ m (fun z => ∑ j, a j • h (tauNeg (reflLin (c j) z)))
          (esHalfL δ) (tauNeg z)).compContinuousLinearMap (fun _ : Fin m => tauNeg) := hcompX
    _ = (iteratedFDerivWithin ℝ m (fun w => h (tauNeg w)) (esHalfR δ)
          (tauNeg z)).compContinuousLinearMap (fun _ : Fin m => tauNeg) := by rw [hR]
    _ = iteratedFDerivWithin ℝ m ((fun w => h (tauNeg w)) ∘ tauNeg) (esHalfL δ) z := hcompY.symm
    _ = iteratedFDerivWithin ℝ m h (esHalfL δ) z := by rw [hνh]

end Work.RPB.B3
