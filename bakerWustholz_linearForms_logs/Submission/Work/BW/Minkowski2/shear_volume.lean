import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Volume of a coordinate shear

For `i : Fin d`, `c > 0` and a measurable `g : (Fin d → ℝ) → ℝ` which only depends on the
coordinates different from `i`, the map

`x ↦ Function.update x i (c * x i + g x)`

is a bijection of `Fin d → ℝ` whose restriction to every affine line parallel to the `i`-th
coordinate axis is an affine map with slope `c`.  Hence it multiplies Lebesgue measure by `c`.

The proof splits off the coordinate `i` (`MeasurableEquiv.piFinSuccAbove`), so that the map
becomes the "fiberwise affine" map `(a, f) ↦ (c * a + h f, f)` on `ℝ × (Fin n → ℝ)`.  The key
ingredient is that the pushforward of a product measure under a fiberwise affine map
`(f, a) ↦ (f, (a - h f)/c)` is `ENNReal.ofReal c` times the product measure; this is
`MeasureTheory.MeasurePreserving.skew_product` together with the one dimensional computation
`volume ((· / c) ⁻¹' B) = c * volume B`.

The result is then transported back along the measure preserving coordinate splitting.
-/

namespace Work.BW.Minkowski2

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise

/-- Pushforward of a product measure under a fiberwise affine map.

For a measurable `h : α → ℝ` and `c > 0`, the map `(f, a) ↦ (f, (a - h f)/c)` pushes
`μ.prod volume` forward to `ENNReal.ofReal c • (μ.prod volume)`. -/
private theorem shear_fiber_volume_aux {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] {h : α → ℝ} (hh : Measurable h) {c : ℝ} (hc : 0 < c) :
    Measure.map (fun p : α × ℝ => (p.1, (p.2 - h p.1) / c))
        (μ.prod (volume : Measure ℝ))
      = ENNReal.ofReal c • (μ.prod (volume : Measure ℝ)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  -- the one dimensional rescaling `a ↦ a / c`
  have hdiv_map : Measure.map (fun s : ℝ => s / c) (volume : Measure ℝ)
      = ENNReal.ofReal c • (volume : Measure ℝ) := by
    ext B hB
    have hmap := Measure.map_apply (μ := (volume : Measure ℝ)) (f := fun s : ℝ => s / c)
      (measurable_id.div_const c) hB
    rw [hmap, Measure.smul_apply, smul_eq_mul]
    have hpre : (fun s : ℝ => s / c) ⁻¹' B = c • B := by
      ext s
      rw [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · intro hs
        exact ⟨s / c, hs, by rw [smul_eq_mul, mul_div_cancel₀ s hcne]⟩
      · rintro ⟨b, hb, hbs⟩
        rw [← hbs, smul_eq_mul, mul_div_cancel_left₀ b hcne]
        exact hb
    rw [hpre, addHaar_smul_of_nonneg (volume : Measure ℝ) hc.le B, Module.finrank_self, pow_one]
  -- adding the measurable shift `h a` does not change the fiberwise pushforward
  have hfib : ∀ a : α, Measure.map (fun s : ℝ => (s - h a) / c) (volume : Measure ℝ)
      = ENNReal.ofReal c • (volume : Measure ℝ) := by
    intro a
    have hcomp : (fun s : ℝ => (s - h a) / c)
        = (fun s : ℝ => s / c) ∘ (fun s : ℝ => s - h a) := rfl
    rw [hcomp, ← Measure.map_map (f := fun s : ℝ => s - h a) (g := fun s : ℝ => s / c)
        (measurable_id.div_const c) (measurable_id.sub measurable_const),
      map_sub_right_eq_self, hdiv_map]
  -- skew product: the fiber maps are measure preserving up to the constant `ofReal c`
  have hmain := MeasurePreserving.skew_product (μa := μ) (μb := μ)
      (μc := (volume : Measure ℝ)) (μd := ENNReal.ofReal c • (volume : Measure ℝ))
      (MeasurePreserving.id μ) (g := fun (a : α) (s : ℝ) => (s - h a) / c)
      (by fun_prop) (Filter.Eventually.of_forall hfib)
  rw [Measure.prod_smul_right] at hmain
  exact hmain.map_eq

theorem shear_volume {d : ℕ} (i : Fin d) {c : ℝ} (hc : 0 < c)
    {g : (Fin d → ℝ) → ℝ} (hg : Measurable g)
    (hgi : ∀ x y : Fin d → ℝ, (∀ m : Fin d, m ≠ i → x m = y m) → g x = g y)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasureTheory.volume ((fun x : Fin d → ℝ => Function.update x i (c * x i + g x)) '' A)
      = ENNReal.ofReal c * MeasureTheory.volume A := by
  have hd : 0 < d := by have := i.isLt; omega
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  -- split off the coordinate `i`
  let e1 : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  let h : (Fin n → ℝ) → ℝ := fun f => g (e1.symm (0, f))
  let T : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) := fun x => Function.update x i (c * x i + g x)
  let Tinv : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) := fun y => Function.update y i ((y i - g y)/c)
  let F : ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ) := fun p => ((p.1 - h p.2)/c, p.2)
  have e1_apply : ∀ x : Fin (n+1) → ℝ, e1 x = (x i, Fin.removeNth i x) := fun x => rfl
  have e1_symm : ∀ (a : ℝ) (f : Fin n → ℝ), e1.symm (a, f) = Fin.insertNth i a f := fun a f => rfl
  have hh : Measurable h :=
    hg.comp (e1.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hcne : c ≠ 0 := ne_of_gt hc
  -- `g` agrees with `h` evaluated on the remaining coordinates
  have hEg : ∀ x : Fin (n+1) → ℝ, h (Fin.removeNth i x) = g x := by
    intro x
    show g (e1.symm (0, Fin.removeNth i x)) = g x
    rw [e1_symm, Fin.insertNth_removeNth]
    exact hgi (Function.update x i 0) x (by intro m hm; rw [Function.update_apply, if_neg hm])
  have hT_apply : ∀ x, (T x) i = c * x i + g x := by
    intro x
    show Function.update x i (c * x i + g x) i = c * x i + g x
    rw [Function.update_apply, if_pos rfl]
  have hgT : ∀ x, g (T x) = g x := by
    intro x
    show g (Function.update x i (c * x i + g x)) = g x
    exact hgi _ x (by intro m hm; rw [Function.update_apply, if_neg hm])
  have hTinv_apply : ∀ y, (Tinv y) i = (y i - g y)/c := by
    intro y
    show Function.update y i ((y i - g y)/c) i = (y i - g y)/c
    rw [Function.update_apply, if_pos rfl]
  have hgTinv : ∀ y, g (Tinv y) = g y := by
    intro y
    show g (Function.update y i ((y i - g y)/c)) = g y
    exact hgi _ y (by intro m hm; rw [Function.update_apply, if_neg hm])
  have hupd_self : ∀ (x : Fin (n+1) → ℝ) (v : ℝ),
      Function.update (Function.update x i v) i (x i) = x := by
    intro x v
    rw [Function.update_idem, Function.update_eq_self]
  -- `T` and `Tinv` are mutually inverse
  have hTinv_T : ∀ x, Tinv (T x) = x := by
    intro x
    have hdiv : ((T x) i - g (T x))/c = x i := by
      rw [hT_apply x, hgT x, div_eq_iff hcne]
      ring
    show Function.update (T x) i (((T x) i - g (T x))/c) = x
    rw [hdiv]
    show Function.update (Function.update x i (c * x i + g x)) i (x i) = x
    exact hupd_self x (c * x i + g x)
  have hT_Tinv : ∀ y, T (Tinv y) = y := by
    intro y
    have hdiv : c * ((Tinv y) i) + g (Tinv y) = y i := by
      rw [hTinv_apply y, hgTinv y, mul_div_cancel₀ _ hcne]
      ring
    show Function.update (Tinv y) i (c * (Tinv y) i + g (Tinv y)) = y
    rw [hdiv]
    show Function.update (Function.update y i ((y i - g y)/c)) i (y i) = y
    exact hupd_self y ((y i - g y)/c)
  have hImg : T '' A = Tinv ⁻¹' A := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩
      show Tinv (T x) ∈ A
      rw [hTinv_T]; exact hx
    · intro hz
      exact ⟨Tinv z, hz, hT_Tinv z⟩
  have hFmeas : Measurable F := by
    show Measurable (fun p : ℝ × (Fin n → ℝ) => ((p.1 - h p.2)/c, p.2))
    fun_prop
  have hGmeas : Measurable (fun p : (Fin n → ℝ) × ℝ => (p.1, (p.2 - h p.1)/c)) := by
    fun_prop
  -- the fiberwise affine map on `ℝ × (Fin n → ℝ)`: transfer the auxiliary lemma by swapping
  have hFmap : Measure.map F (volume : Measure (ℝ × (Fin n → ℝ)))
      = ENNReal.ofReal c • (volume : Measure (ℝ × (Fin n → ℝ))) := by
    show Measure.map F ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      = ENNReal.ofReal c • ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
    have hG := shear_fiber_volume_aux (volume : Measure (Fin n → ℝ)) hh hc
    have hswap_Ra : Measure.map (fun p : ℝ × (Fin n → ℝ) => Prod.swap p)
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        = (volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ) := Measure.prod_swap
    have hswap_aR : Measure.map (fun p : (Fin n → ℝ) × ℝ => Prod.swap p)
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
        = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) := Measure.prod_swap
    have hfun : F = (fun p : (Fin n → ℝ) × ℝ => Prod.swap p) ∘
        ((fun p : (Fin n → ℝ) × ℝ => (p.1, (p.2 - h p.1)/c)) ∘
          (fun p : ℝ × (Fin n → ℝ) => Prod.swap p)) := by
      funext p
      rcases p with ⟨a, f⟩
      rfl
    rw [hfun]
    rw [← Measure.map_map measurable_swap (hGmeas.comp measurable_swap),
        ← Measure.map_map hGmeas measurable_swap, hswap_Ra, hG,
        Measure.map_smul (ENNReal.ofReal c) measurable_swap.aemeasurable, hswap_aR]
  have he1 : MeasurePreserving (⇑e1) volume volume :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) i
  have hfun_Tinv : Tinv = ⇑e1.symm ∘ (F ∘ ⇑e1) := by
    funext y
    show Function.update y i ((y i - g y)/c) = e1.symm (F (e1 y))
    have hFe : F (e1 y) = ((y i - h (Fin.removeNth i y))/c, Fin.removeNth i y) := by
      rw [e1_apply]
    rw [hFe, e1_symm, Fin.insertNth_removeNth, hEg y]
  have hTinv_meas : Measurable Tinv := by
    rw [hfun_Tinv]
    exact e1.symm.measurable.comp (hFmeas.comp e1.measurable)
  have hmapTinv : Measure.map Tinv volume = ENNReal.ofReal c • volume := by
    rw [hfun_Tinv]
    rw [← Measure.map_map e1.symm.measurable (hFmeas.comp e1.measurable),
        ← Measure.map_map hFmeas e1.measurable, he1.map_eq, hFmap,
        Measure.map_smul (ENNReal.ofReal c) e1.symm.measurable.aemeasurable,
        he1.symm.map_eq]
  have hmapA : (Measure.map Tinv volume) A = volume (Tinv ⁻¹' A) :=
    Measure.map_apply hTinv_meas hA
  rw [hmapTinv, Measure.smul_apply, smul_eq_mul] at hmapA
  rw [hImg]
  exact hmapA.symm

end Work.BW.Minkowski2
