import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Analysis.Measure.Fubini

open MeasureTheory

/-! ### Helpers for splitting integrals over `Fin (n+1) → ℝ` -/

/-- The measurable equivalence `(s, w) ↦ Fin.cons s w` between `ℝ × (Fin n → ℝ)` and
`Fin (n + 1) → ℝ`. -/
noncomputable def finConsMeasurableEquiv (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

@[simp]
theorem finConsMeasurableEquiv_apply (n : ℕ) (s : ℝ) (w : Fin n → ℝ) :
    finConsMeasurableEquiv n (s, w) = Fin.cons s w := by
  funext i
  simp [finConsMeasurableEquiv]

theorem finConsMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (finConsMeasurableEquiv n) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

/-- `MeasurePreserving` for `MeasurableEquiv.prodCongr`. -/
theorem measurePreserving_prodCongr {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}
    {e1 : α ≃ᵐ β} {e2 : γ ≃ᵐ δ}
    (h1 : MeasurePreserving e1 μa μb) (h2 : MeasurePreserving e2 μc μd)
    [SFinite μa] [SFinite μc] :
    MeasurePreserving (e1.prodCongr e2) (μa.prod μc) (μb.prod μd) := by
  have := MeasurePreserving.prod h1 h2
  convert this using 1
  funext x
  rfl

/-- The "middle swap" measurable equivalence
`((s, s'), (w, w')) ↦ ((s, w), (s', w'))`. -/
noncomputable def midSwap (n : ℕ) :
    ((ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) ≃ᵐ
      ((ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ))) :=
  MeasurableEquiv.prodAssoc.trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodAssoc.symm).trans <|
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
          (MeasurableEquiv.refl (Fin n → ℝ)))).trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodAssoc).trans <|
          MeasurableEquiv.prodAssoc.symm

@[simp]
theorem midSwap_apply (n : ℕ) (s s' : ℝ) (w w' : Fin n → ℝ) :
    midSwap n ((s, s'), (w, w')) = ((s, w), (s', w')) := rfl

@[simp]
theorem prodCongr_apply_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (e1 : α ≃ᵐ β) (e2 : γ ≃ᵐ δ) (x : α × γ) :
    (e1.prodCongr e2 x).1 = e1 x.1 := rfl

@[simp]
theorem prodCongr_apply_snd {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (e1 : α ≃ᵐ β) (e2 : γ ≃ᵐ δ) (x : α × γ) :
    (e1.prodCongr e2 x).2 = e2 x.2 := rfl

theorem midSwap_measurePreserving (n : ℕ) :
    MeasurePreserving (midSwap n) volume volume := by
  rw [midSwap]
  refine MeasurePreserving.trans (μb := volume) volume_preserving_prodAssoc ?_
  refine MeasurePreserving.trans (μb := volume) ?_ ?_
  · exact measurePreserving_prodCongr (MeasurePreserving.id volume)
      (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin n → ℝ) (γ₁ := Fin n → ℝ)).symm
  · refine MeasurePreserving.trans (μb := volume) ?_ ?_
    · refine measurePreserving_prodCongr (MeasurePreserving.id volume) ?_
      exact measurePreserving_prodCongr MeasureTheory.Measure.measurePreserving_swap
        (MeasurePreserving.id volume)
    · refine MeasurePreserving.trans (μb := volume) ?_ ?_
      · exact measurePreserving_prodCongr (MeasurePreserving.id volume)
          (volume_preserving_prodAssoc (α₁ := Fin n → ℝ) (β₁ := ℝ) (γ₁ := Fin n → ℝ))
      · exact (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin n → ℝ)
          (γ₁ := ℝ × (Fin n → ℝ))).symm

/-! ### The main result -/

theorem integral_fin_cons_split {n : ℕ}
    (Φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℂ)
    (hΦ : MeasureTheory.Integrable (Function.uncurry Φ)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)))) :
    ∫ t : Fin (n + 1) → ℝ, ∫ t' : Fin (n + 1) → ℝ, Φ t t'
      = ∫ s : ℝ, ∫ s' : ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ,
          Φ (Fin.cons s w) (Fin.cons s' w') := by
  have he : MeasurePreserving (finConsMeasurableEquiv n) volume volume :=
    finConsMeasurableEquiv_measurePreserving n
  have heProd : MeasurePreserving
      ((finConsMeasurableEquiv n).prodCongr (finConsMeasurableEquiv n)) volume volume :=
    measurePreserving_prodCongr he he
  have hs : MeasurePreserving (midSwap n) volume volume := midSwap_measurePreserving n
  -- Step A: LHS as an integral over the product `X × X`.
  have stepA :
      (∫ t : Fin (n + 1) → ℝ, ∫ t' : Fin (n + 1) → ℝ, Φ t t')
        = ∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ), Φ z.1 z.2 :=
    integral_integral hΦ
  -- Step B: change variables on `X × X` by `eProd`.
  have stepB :
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ), Φ z.1 z.2)
        = ∫ x : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
            Φ (finConsMeasurableEquiv n x.1) (finConsMeasurableEquiv n x.2) := by
    have h := heProd.integral_comp'
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => Φ z.1 z.2)
    exact h.symm
  -- Step C: change variables by `s`.
  have stepC :
      (∫ x : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
            Φ (finConsMeasurableEquiv n x.1) (finConsMeasurableEquiv n x.2))
        = ∫ y : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)),
            Φ (Fin.cons y.1.1 y.2.1) (Fin.cons y.1.2 y.2.2) := by
    have h := hs.integral_comp'
      (fun x : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)) =>
        Φ (finConsMeasurableEquiv n x.1) (finConsMeasurableEquiv n x.2))
    rw [h.symm]
    apply integral_congr_ae
    filter_upwards with y
    obtain ⟨⟨s, s'⟩, ⟨w, w'⟩⟩ := y
    simp only [midSwap_apply, finConsMeasurableEquiv_apply]
  -- Step D: Fubini on `(ℝ × ℝ) × (W × W)`.
  have stepD :
      (∫ y : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)),
            Φ (Fin.cons y.1.1 y.2.1) (Fin.cons y.1.2 y.2.2))
        = ∫ s0 : ℝ, ∫ s1 : ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ,
            Φ (Fin.cons s0 w) (Fin.cons s1 w') := by
    set F : ((ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))) → ℂ :=
      fun y => Φ (Fin.cons y.1.1 y.2.1) (Fin.cons y.1.2 y.2.2) with hFdef
    have hF : Integrable F volume := by
      have hcomp : MeasurePreserving
          ((midSwap n).trans ((finConsMeasurableEquiv n).prodCongr (finConsMeasurableEquiv n)))
          volume volume := hs.trans heProd
      have h1 := (hcomp.integrable_comp_emb
        ((midSwap n).trans ((finConsMeasurableEquiv n).prodCongr
          (finConsMeasurableEquiv n))).measurableEmbedding).mpr hΦ
      convert h1 using 1
      ext y
      obtain ⟨⟨s, s'⟩, ⟨w, w'⟩⟩ := y
      simp only [Function.comp_apply, Function.uncurry, MeasurableEquiv.trans_apply,
        midSwap_apply, prodCongr_apply_fst, prodCongr_apply_snd,
        finConsMeasurableEquiv_apply, hFdef]
    have key1 : ∫ y, F y
        = ∫ z1 : ℝ × ℝ, ∫ z2 : (Fin n → ℝ) × (Fin n → ℝ), F (z1, z2) :=
      integral_prod F hF
    have hG : Integrable (fun z1 : ℝ × ℝ =>
        ∫ z2 : (Fin n → ℝ) × (Fin n → ℝ), F (z1, z2)) volume :=
      hF.integral_prod_left
    have key2 : (∫ z1 : ℝ × ℝ, ∫ z2 : (Fin n → ℝ) × (Fin n → ℝ), F (z1, z2))
        = ∫ z1 : ℝ × ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, F (z1, (w, w')) := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae] with z1 hz1
      exact integral_prod (fun z2 => F (z1, z2)) hz1
    have hG' : Integrable (fun z1 : ℝ × ℝ =>
        ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, F (z1, (w, w'))) volume := by
      refine hG.congr ?_
      filter_upwards [hF.prod_right_ae] with z1 hz1
      exact integral_prod (fun z2 => F (z1, z2)) hz1
    have key3 : (∫ z1 : ℝ × ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, F (z1, (w, w')))
        = ∫ s0 : ℝ, ∫ s1 : ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ,
            F ((s0, s1), (w, w')) :=
      integral_prod (fun z1 : ℝ × ℝ =>
        ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, F (z1, (w, w'))) hG'
    calc ∫ y, F y
        = ∫ z1 : ℝ × ℝ, ∫ z2 : (Fin n → ℝ) × (Fin n → ℝ), F (z1, z2) := key1
      _ = ∫ z1 : ℝ × ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, F (z1, (w, w')) := key2
      _ = ∫ s0 : ℝ, ∫ s1 : ℝ, ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ,
            F ((s0, s1), (w, w')) := key3
  exact stepA.trans (stepB.trans (stepC.trans stepD))

end Commons.Analysis.Measure.Fubini