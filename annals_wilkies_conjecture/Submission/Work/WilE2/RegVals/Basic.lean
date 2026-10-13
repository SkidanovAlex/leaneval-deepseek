/-
  `Work.WilE2.RegVals.Basic` — infrastructure for the regularity/density lemma
  `Work.WilE2.regular_values_dense`.

  * `critSet f` — the critical set of `f : ℝⁿ → ℝᵐ`;
  * `fderiv_coord` — coordinates of the derivative;
  * `volume_eq_zero_of_slices_null` — Fubini in `ℝʳ × ℝˢ`;
  * `surjective_fst_prod_iff` — block-matrix surjectivity;
  * `splitEquiv` — the (measure preserving) linear equivalence `ℝᵐ ≃ ℝʳ × ℝᵐ⁻ʳ`.
-/
import Mathlib

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.WilE2

/-- The critical set of `f : ℝⁿ → ℝᵐ`: the points where the differential of `f` fails to be
surjective (equivalently, where the Jacobian has rank `< m`). -/
def critSet {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  {z | ¬ Function.Surjective (fderiv ℝ f z)}

@[simp] theorem mem_critSet {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)} {z : Fin n → ℝ} :
    z ∈ critSet f ↔ ¬ Function.Surjective (fderiv ℝ f z) := Iff.rfl

/-- The `a`-th coordinate of `fderiv ℝ G z` is the derivative of the `a`-th coordinate function
`w ↦ G w a`. -/
theorem fderiv_coord {n m : ℕ} (G : (Fin n → ℝ) → (Fin m → ℝ)) (z : Fin n → ℝ)
    (hG : DifferentiableAt ℝ G z) (a : Fin m) :
    fderiv ℝ (fun w => G w a) z = (ContinuousLinearMap.proj a).comp (fderiv ℝ G z) := by
  have hπ : HasFDerivAt (fun v : Fin m → ℝ => v a)
      (ContinuousLinearMap.proj a : (Fin m → ℝ) →L[ℝ] ℝ) (G z) :=
    (ContinuousLinearMap.proj a : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt G (fderiv ℝ G z) z := hG.hasFDerivAt
  exact (hπ.comp z h1).fderiv

/-- **Fubini.** A measurable subset of `ℝʳ × ℝˢ` all of whose slices are null is null. -/
theorem volume_eq_zero_of_slices_null {r s : ℕ} {K : Set ((Fin r → ℝ) × (Fin s → ℝ))}
    (hK : MeasurableSet K) (h : ∀ a, volume (Prod.mk a ⁻¹' K) = 0) : volume K = 0 := by
  rw [Measure.volume_eq_prod (Fin r → ℝ) (Fin s → ℝ), Measure.prod_apply hK]
  simp [h]

/-- **Block-matrix surjectivity criterion.**  For a continuous linear map
`S : ℝʳ × ℝˢ → ℝᵗ`, the map `p ↦ (p.1, S p) : ℝʳ × ℝˢ → ℝʳ × ℝᵗ` is surjective if and only if
the restriction `S ∘ inr : ℝˢ → ℝᵗ` is surjective. -/
theorem surjective_fst_prod_iff {r s t : ℕ}
    (S : ((Fin r → ℝ) × (Fin s → ℝ)) →L[ℝ] (Fin t → ℝ)) :
    Function.Surjective (fun p : (Fin r → ℝ) × (Fin s → ℝ) => (p.1, S p))
      ↔ Function.Surjective (S.comp (ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ))) := by
  constructor
  · intro h z
    obtain ⟨p, hp⟩ := h (0, z)
    have hp1 : p.1 = 0 := congrArg Prod.fst hp
    have hp2 : S p = z := congrArg Prod.snd hp
    have hp3 : p = ((0 : Fin r → ℝ), p.2) := Prod.ext (by rw [hp1]) rfl
    refine ⟨p.2, ?_⟩
    rw [ContinuousLinearMap.comp_apply]
    have hinr : ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ) p.2 = p := by
      rw [show ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ) p.2
          = ((0 : Fin r → ℝ), p.2) from by simp]
      exact hp3.symm
    rw [hinr, hp2]
  · intro h p
    obtain ⟨b, hb⟩ := h (p.2 - S (p.1, 0))
    rw [ContinuousLinearMap.comp_apply] at hb
    refine ⟨(p.1, b), ?_⟩
    change ((p.1, b).1, S (p.1, b)) = p
    have hsum : (p.1, b) = (p.1, 0) + ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ) b := by
      ext <;> simp
    have hS : S (p.1, b) = S (p.1, 0)
        + S (ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin s → ℝ) b) := by
      rw [hsum, map_add]
    rw [hS, hb]
    exact Prod.ext rfl (by abel)

/-! ### Measure preserving equivalences preserve nullity -/

/-- A measure preserving measurable equivalence pushes null sets to null sets. -/
theorem image_null_of_measurePreserving {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]
    {ρ : Measure γ} {σ' : Measure δ} (f : γ ≃ᵐ δ) (hf : MeasurePreserving f ρ σ') (C : Set γ)
    (hC : ρ C = 0) : σ' (f '' C) = 0 := by
  set C' := toMeasurable ρ C with hC'
  have hC'm : MeasurableSet C' := measurableSet_toMeasurable _ _
  have hC'0 : ρ C' = 0 := by rw [measure_toMeasurable]; exact hC
  have hsub : f '' C ⊆ f '' C' := Set.image_mono (subset_toMeasurable _ _)
  refine le_antisymm ((measure_mono hsub).trans ?_) bot_le
  have h1 : f '' C' = f.symm ⁻¹' C' := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa using hx,
      fun hy => ⟨f.symm y, hy, by simp⟩⟩
  rw [h1, hf.symm.measure_preimage hC'm.nullMeasurableSet]
  exact le_of_eq hC'0

/-- A measure preserving measurable equivalence preserves nullity of images. -/
theorem image_null_iff_of_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (h : MeasurePreserving e μ ν) (B : Set α) :
    ν (e '' B) = 0 ↔ μ B = 0 := by
  constructor
  · intro hB
    have heq : e.symm '' (e '' B) = B := by
      ext y
      simp only [Set.mem_image]
      exact ⟨fun ⟨x, ⟨w, hw, hwx⟩, hxy⟩ => by rw [← hxy, ← hwx]; simpa using hw,
        fun hy => ⟨e y, ⟨y, hy, rfl⟩, by simp⟩⟩
    rw [← heq]
    exact image_null_of_measurePreserving e.symm h.symm (e '' B) hB
  · exact image_null_of_measurePreserving e h B

/-! ### Splitting off the first `r` coordinates -/

/-- `Fin m ≃ Fin r ⊕ Fin (m - r)`. -/
noncomputable def finSplitEquiv (r m : ℕ) (hr : r ≤ m) :
    Fin m ≃ (Fin r ⊕ Fin (m - r)) :=
  (finCongr (Nat.add_sub_of_le hr)).symm.trans finSumFinEquiv.symm

/-- The linear equivalence `ℝᵐ ≃ ℝʳ × ℝᵐ⁻ʳ` splitting off the first `r` coordinates. -/
noncomputable def splitLinearEquiv (r m : ℕ) (hr : r ≤ m) :
    (Fin m → ℝ) ≃ₗ[ℝ] ((Fin r → ℝ) × (Fin (m - r) → ℝ)) :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : Fin r ⊕ Fin (m - r) => ℝ) (finSplitEquiv r m hr)).trans
    (LinearEquiv.sumPiEquivProdPi ℝ (Fin r) (Fin (m - r)) (fun _ => ℝ))

/-- The continuous linear equivalence `ℝᵐ ≃ ℝʳ × ℝᵐ⁻ʳ` splitting off the first `r` coordinates. -/
noncomputable def splitEquiv (r m : ℕ) (hr : r ≤ m) :
    (Fin m → ℝ) ≃L[ℝ] ((Fin r → ℝ) × (Fin (m - r) → ℝ)) :=
  (splitLinearEquiv r m hr).toContinuousLinearEquiv

/-- The measurable equivalence `ℝᵐ ≃ ℝʳ × ℝᵐ⁻ʳ` splitting off the first `r` coordinates. -/
noncomputable def splitMeas (r m : ℕ) (hr : r ≤ m) :
    (Fin m → ℝ) ≃ᵐ ((Fin r → ℝ) × (Fin (m - r) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin r ⊕ Fin (m - r) => ℝ) (finSplitEquiv r m hr)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin (m - r) => ℝ))

theorem splitMeas_coe_eq (r m : ℕ) (hr : r ≤ m) :
    (⇑(splitMeas r m hr) : (Fin m → ℝ) → ((Fin r → ℝ) × (Fin (m - r) → ℝ)))
      = ⇑(splitEquiv r m hr) := by
  funext x
  rfl

theorem measurePreserving_splitMeas (r m : ℕ) (hr : r ≤ m) :
    MeasurePreserving (splitMeas r m hr : (Fin m → ℝ) → _) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin (m - r) => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin r ⊕ Fin (m - r) => ℝ) (finSplitEquiv r m hr))

theorem measurePreserving_splitEquiv (r m : ℕ) (hr : r ≤ m) :
    MeasurePreserving (splitEquiv r m hr : (Fin m → ℝ) → _) volume volume := by
  rw [← splitMeas_coe_eq r m hr]
  exact measurePreserving_splitMeas r m hr

/-- Null sets are preserved by the coordinate splitting. -/
theorem splitEquiv_volume_image_eq_zero_iff (r m : ℕ) (hr : r ≤ m) (A : Set (Fin m → ℝ)) :
    volume (splitEquiv r m hr '' A) = 0 ↔ volume A = 0 := by
  rw [← splitMeas_coe_eq r m hr]
  exact image_null_iff_of_measurePreserving (splitMeas r m hr) (measurePreserving_splitMeas r m hr) A

end Work.WilE2
