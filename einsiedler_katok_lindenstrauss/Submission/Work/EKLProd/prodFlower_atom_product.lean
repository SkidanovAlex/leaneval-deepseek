import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLProd.prodFlower_Lambda_prod
import Submission.Work.EKLProd.post_null_transfer_gen
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLRelCross.SL3criterion
import Submission.Work.EKLRelProduct.psiEqNuU
import Submission.Work.EKLProd.measurableSet_atomBad
import Submission.Work.EKLProd.atomBad_fibre_null
import Submission.Work.EKLProd.atomId_iff_not_atomBad
import Submission.Work.EKLProd.atomId_derives_target

/-!
# `Work.EKLProd.prodFlower_atom_product`

The atom-level product structure of a product-box flower at a.e. base point (plan §12.3,
`(AL_z)`):  for a.e. base point `x` of the `n`-th flower, the leafwise measure `νH x` restricted
to the `H`-shape of the flower is proportional to the image, under the multiplication map, of
`νT x ⊗ νU x`, restricted to the same shape.

## The route

Write `M := (νH x) ↾ shape` and `R := (ι_*(νT x ⊗ νU x)) ↾ shape` (`ι(t,u) = t·u`).  Both are
carried by the shape, and on the shape the plaque coordinate
`ϑ(g) = (hT T U g, hU T U g)` is injective with `mul ∘ ϑ = id`; hence `M = c · R` is *equivalent*
to the identity of the two coordinate laws.  A computation ("unwinding") shows:

* `prodFlower_Lambda_prod` gives the coordinate law of `M` at a.e. `x`:
  `ΛTP x = κ_x ⊗ σ_x` (`prodFlowerκ` and the `U`-marginal `σ_x`);
* `atomId x` — the identification `(8.12c)` *at the base point*
  `(uShift x) ↾ V R ∩ U ∝ σ_x ↾ V R ∩ U` — identifies `σ_x` with the `(8.12c)` translate of
  `νU x`; after the substitutions `t = t'·t_x`, `u = t_x⁻¹u't_xu_x` (with `co n x = t_x u_x`) the
  map `(t,u) ↦ tu·(co n x)⁻¹` becomes plain multiplication, and the two sides match.  This is
  `atomId_derives_target`.

So everything reduces to the identification *at the base point*, i.e. to `psiEqNuU` evaluated at
`h = 1`.  `psiEqNuU` gives it only for `(νH x) ↾ shape`-a.e. `h`; the passage from the fibre to the
base point is the "diagonal" step.  It is done here with a **sound Borel** bad set:

* `atomBad hf n XH XU νH νU` is the set of `y` where the countable proportionality criterion
  `SL3Criterion` fails (with both measures nonzero) — by `SL3criterion` this is equivalent to the
  failure of `atomId` on the conull locus (`atomId_iff_not_atomBad`), and it is Borel
  (`measurableSet_atomBad`, via the section measurability of weakly measurable, locally finite
  families);
* `atomBad` is `(νH x) ↾ shape`-invisible for a.e. `x`, because `psiEqNuU` (at `h`) says exactly
  that `atomId (h•x)` holds for a.e. `h`, and `atomBad y → ¬ atomId y` (`atomBad_fibre_null`);
* the condexp/globalisation argument `post_null_transfer_gen` (the converse of the leafwise null
  transfer) then gives `(μ ↾ Z n) atomBad = 0`, i.e. `atomId` at a.e. base point.

The remaining assembly in this file supplies the a.e. non-degeneracy of the two measures at the
base point (positivity/finiteness of the `U`-shape mass) and the two carrier facts
`νT x (Tᶜ) = 0`, `νU x (Uᶜ) = 0` from the `IsLeafwise` fields, and feeds
`atomId_derives_target`.
-/

open MeasureTheory
open Work.EKLContract

namespace Work.EKLProd

open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

/-- The `U`-marginal of the joint `(T,U)`-law is the `uMarg` of the U-side development. -/
private theorem prodfLowerATPMapSnd {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) :
    (Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd
      = Work.EKLRelProduct.uMarg hf νH n x := by
  classical
  have hpair : Measurable (fun g : Work.EKLContract.SL3 =>
      (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc
  have hUmeas : Measurable (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) :=
    measurable_snd.comp hpair
  have hSmeas : MeasurableSet (Work.EKLContract.shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hx).2.2.1
    rw [hOsh]
    exact hOo.measurableSet.inter hHc.measurableSet
  have hcoe : ∀ h ∈ Work.EKLContract.shape (hf.mH n) H x,
      Work.EKLProd.hU T U (h * hf.co n x) = Work.EKLProd.hU T U (hf.co n (h • x)) := by
    intro h hh
    rw [hf.co_smul n x hx h hh.1 hh.2]
  calc (Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd
      = (Work.EKLProd.prodFlowerΛ hf n νH x).map
          (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) := by
        rw [Work.EKLProd.prodFlowerΛTP, MeasureTheory.Measure.map_map measurable_snd hpair]
        rfl
    _ = (((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          (fun h : Work.EKLContract.SL3 => h * hf.co n x)).map
            (fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) := by
        rw [Work.EKLProd.prodFlowerΛ]
    _ = ((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          ((fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) ∘
            (fun h : Work.EKLContract.SL3 => h * hf.co n x)) := by
        rw [MeasureTheory.Measure.map_map hUmeas (continuous_mul_const (hf.co n x)).measurable]
    _ = ((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)).map
          (fun h => Work.EKLProd.hU T U (hf.co n (h • x))) := by
        have hae : ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
            ((fun g : Work.EKLContract.SL3 => Work.EKLProd.hU T U g) ∘
              (fun h : Work.EKLContract.SL3 => h * hf.co n x)) h
              = Work.EKLProd.hU T U (hf.co n (h • x)) := by
          rw [MeasureTheory.ae_restrict_iff' hSmeas]
          exact Filter.Eventually.of_forall (fun h hh => hcoe h hh)
        exact MeasureTheory.Measure.map_congr hae
    _ = Work.EKLRelProduct.uMarg hf νH n x := by rw [Work.EKLRelProduct.uMarg]

/-- The mass of the `(8.12c)` translate on the ball is the `U`-shape mass. -/
private theorem atomShU_apply_ball {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) :
    (Work.EKLProd.atomShU hf n νU x) (V hf.R ∩ (U : Set Work.EKLContract.SL3))
      = (νU x) (Work.EKLContract.shape (hf.mU n) U x) := by
  classical
  have hWmeas : MeasurableSet (V hf.R ∩ (U : Set Work.EKLContract.SL3)) :=
    ((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet.inter
      hUc.measurableSet
  have hshape := Work.EKLRelProduct.shapeU_eq_shift hTH hUH hnorm hcop hdisj hf n hx
  have hS : Work.EKLRelProduct.S_U hf n x = Work.EKLContract.shape (hf.mU n) U x := by
    rw [hshape]
    rfl
  have hpre : (Work.EKLRelProduct.shiftMap (Work.EKLProd.hT T U (hf.co n x))
        (Work.EKLProd.hU T U (hf.co n x))) ⁻¹' (V hf.R ∩ (U : Set Work.EKLContract.SL3))
      = Work.EKLRelProduct.S_U hf n x := rfl
  have hkey : (Work.EKLRelProduct.uShift hf νU n x) (V hf.R ∩ (U : Set Work.EKLContract.SL3))
      = (νU x) (Work.EKLRelProduct.S_U hf n x) := by
    have h1 : (Work.EKLRelProduct.uShift hf νU n x) (V hf.R ∩ (U : Set Work.EKLContract.SL3))
        = ((Work.EKLRelProduct.uShift hf νU n x).restrict (V hf.R ∩ (U : Set Work.EKLContract.SL3)))
            (V hf.R ∩ (U : Set Work.EKLContract.SL3)) := by
      rw [MeasureTheory.Measure.restrict_apply hWmeas, Set.inter_self]
    have hSUmeas : MeasurableSet (Work.EKLRelProduct.S_U hf n x) := by
      rw [← hpre]
      exact hWmeas.preimage
        (Work.EKLRelProduct.measurableEmbedding_shiftMap _ _).measurable
    rw [h1, Work.EKLRelProduct.uShift_restrict_eq_shiftMap hf n νU x,
      MeasureTheory.Measure.map_apply
        (Work.EKLRelProduct.measurableEmbedding_shiftMap _ _).measurable hWmeas,
      hpre, MeasureTheory.Measure.restrict_apply hSUmeas, Set.inter_self]
  rw [Work.EKLProd.atomShU, MeasureTheory.Measure.restrict_apply hWmeas, Set.inter_self, hkey, hS]


/-- <<< SCRATCH COPY of the target, assembled >>> -/
theorem prodFlower_atom_product (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hmu : Work.EKLContract.IsAInvariant μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) (t₀ : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t₀ * g = g * Work.EKLContract.aDiag t₀) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t₀ ^ k * u * (Work.EKLContract.aDiag t₀ ^ k)⁻¹) Filter.atTop (nhds 1)) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∃ c : ℝ, 0 < c ∧ (νH x).restrict (Work.EKLContract.shape (hf.mH n) H x) = ENNReal.ofReal c • ((((νT x).prod (νU x)).map (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2)).restrict (Work.EKLContract.shape (hf.mH n) H x)) := by
  classical
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hWmeas : MeasurableSet (V hf.R ∩ (U : Set Work.EKLContract.SL3)) :=
    ((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet.inter
      hU.1.measurableSet
  have hP1 := Work.EKLProd.prodFlower_Lambda_prod hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj
    hf hνH hνT n t₀ hcent hcontr
  have hmassH := Work.EKLProd.prodFlower_shape_mass hf hνH n
  have hZae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ hf.Z n := MeasureTheory.ae_restrict_mem hZmeas
  have hXHae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XH := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (MeasureTheory.Measure.restrict_apply_le (hf.Z n) XHᶜ)
      (le_of_eq hνH.conull)) bot_le
  have hXTae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XT := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (MeasureTheory.Measure.restrict_apply_le (hf.Z n) XTᶜ)
      (le_of_eq hνT.conull)) bot_le
  have hXUae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XU := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (MeasureTheory.Measure.restrict_apply_le (hf.Z n) XUᶜ)
      (le_of_eq hνU.conull)) bot_le
  have hUsh : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      0 < (νU x) (Work.EKLContract.shape (hf.mU n) U x) ∧
        (νU x) (Work.EKLContract.shape (hf.mU n) U x) < ⊤ := by
    filter_upwards [hXUae, hZae] with x hxU hxZ
    exact Work.EKLC6Core.shape_mass_pos hνU (hf.plaqU n) hxU hxZ
  have hbadnull : (μ.restrict (hf.Z n)) (Work.EKLProd.atomBad hf n XH XU νH νU) = 0 :=
    Work.EKLProd.post_null_transfer_gen hνH (hf.plaqH n)
      (measurableSet_atomBad hTH hUH hnorm hcop hdisj hH.1 hT.1 hU.1 hf n hνH hνU)
      (atomBad_fibre_null hX3 hLeaf hBirk hmu hH hT hU hTH hUH hnorm hcop hdisj hf n
        hνH hνT hνU t₀ hcent hcontr)
  have hbadae : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      x ∉ Work.EKLProd.atomBad hf n XH XU νH νU := by
    rw [MeasureTheory.ae_iff]
    simpa using hbadnull
  filter_upwards [hP1, hmassH, hZae, hXHae, hXTae, hXUae, hUsh, hbadae]
    with x hP1x hmassx hxZ hxXH hxXT hxXU hUx hxbad
  have hL1 := prodfLowerATPMapSnd hTH hUH hnorm hcop hdisj hH.1 hT.1 hU.1 hf n νH hxZ
  have h2W : Work.EKLProd.atomMargU hf n νH x (V hf.R ∩ (U : Set Work.EKLContract.SL3))
      = (νH x) (Work.EKLContract.shape (hf.mH n) H x) := by
    rw [Work.EKLProd.atomMargU, MeasureTheory.Measure.restrict_apply hWmeas, Set.inter_self, hL1,
      Work.EKLRelProduct.uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hWmeas]
  have h2ne : Work.EKLProd.atomMargU hf n νH x ≠ 0 := by
    intro h
    have h0 : Work.EKLProd.atomMargU hf n νH x (V hf.R ∩ (U : Set Work.EKLContract.SL3)) = 0 := by
      rw [h]; simp
    rw [h2W] at h0
    exact absurd h0 (ne_of_gt hmassx.1)
  have hm2W : (MeasureTheory.Measure.map Prod.snd (Work.EKLProd.prodFlowerΛTP hf n νH x))
      (V hf.R ∩ (U : Set Work.EKLContract.SL3)) < ⊤ := by
    have h := h2W
    rw [Work.EKLProd.atomMargU, MeasureTheory.Measure.restrict_apply hWmeas, Set.inter_self] at h
    rw [h]
    exact hmassx.2
  have h2t : MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLProd.atomMargU hf n νH x) := by
    refine ⟨fun K hK => ?_⟩
    rw [Work.EKLProd.atomMargU, MeasureTheory.Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hm2W
  have h1W : Work.EKLProd.atomShU hf n νU x (V hf.R ∩ (U : Set Work.EKLContract.SL3))
      = (νU x) (Work.EKLContract.shape (hf.mU n) U x) :=
    atomShU_apply_ball hTH hUH hnorm hcop hdisj hU.1 hf n νU hxZ
  have h1ne : Work.EKLProd.atomShU hf n νU x ≠ 0 := by
    intro h
    have h0 : Work.EKLProd.atomShU hf n νU x (V hf.R ∩ (U : Set Work.EKLContract.SL3)) = 0 := by
      rw [h]; simp
    rw [h1W] at h0
    exact absurd h0 (ne_of_gt hUx.1)
  have hm1W : (Work.EKLRelProduct.uShift hf νU n x) (V hf.R ∩ (U : Set Work.EKLContract.SL3)) < ⊤ := by
    have h := h1W
    rw [Work.EKLProd.atomShU, MeasureTheory.Measure.restrict_apply hWmeas, Set.inter_self] at h
    rw [h]
    exact hUx.2
  have h1t : MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLProd.atomShU hf n νU x) := by
    refine ⟨fun K hK => ?_⟩
    rw [Work.EKLProd.atomShU, MeasureTheory.Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hm1W
  have hid : Work.EKLProd.atomId hf n νH νU x :=
    (atomId_iff_not_atomBad hTH hUH hnorm hcop hdisj hf n hxZ hxXH hxXU h1ne h2ne
      h1t h2t).mpr hxbad
  have hcarT : (νT x) (T : Set Work.EKLContract.SL3)ᶜ = 0 := hνT.carried x hxXT
  have hcarU : (νU x) (U : Set Work.EKLContract.SL3)ᶜ = 0 := hνU.carried x hxXU
  have hfinT : MeasureTheory.IsFiniteMeasureOnCompacts (νT x) := hνT.radon x hxXT
  have hfinU : MeasureTheory.IsFiniteMeasureOnCompacts (νU x) := hνU.radon x hxXU
  exact atomId_derives_target hTH hUH hnorm hcop hdisj hH.1 hT.1 hU.1 hf n hxZ hcarT hcarU
    hfinT hfinU hP1x.2 hmassx hid

end

end Work.EKLProd
