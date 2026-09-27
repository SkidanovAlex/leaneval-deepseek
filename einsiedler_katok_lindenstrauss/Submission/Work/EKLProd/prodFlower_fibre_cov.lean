import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.leafwise_null_transfer_gen

/-!
# Fibre covariance of the `(T,U)`-joint law of a product-box flower

`Work.EKLProd.prodFlower_fibre_cov`: along the `H`-shape of a product-box flower the joint law
`prodFlowerΛTP hf n νH` of the `T`- and `U`-parts of the plaque coordinate is invariant up to a
constant.  This is the "`H`-covariance of the fibre measures" ingredient of
`EKLComp/ProductPlan.md` §11.3 (the step that lets the ball-level identification of `νU`,
established at one base point of the collar `Z n`, propagate to the whole `H`-leaf).

The proof has two layers.

* **Pointwise** (`prodFlowerLambda_smul_aux`, for `h` in the `H`-shape *with* `h • x ∈ XH`):
  this is the `equivariant` field of `IsLeafwise`, which gives
  `νH (h • x) = c • (νH x).map (· * h⁻¹)`, combined with the two flower fields
  – `shape (mH n) H (h • x) = (fun g => g * h⁻¹) '' shape (mH n) H x` (the atom of a plaque
    algebra is constant on itself; `h ∈ shape` means `h • x ∈ atom (mH n) x`),
  – `co n (h • x) = h * co n x` (`co_smul`) —
  after which `Measure.restrict_map`, `Measure.map_smul`, `Measure.restrict_smul` and
  `Measure.map_map` turn the definitional unfolding of `prodFlowerΛ` into the claim
  (`(g * h⁻¹) * (h * co n x) = g * co n x`).
* **Transfer of `h • x ∈ XH` to a.e. `h`** (`prodFlower_fibre_cov`): the set `XHᶜ` is `μ`-null, so
  by the `condexp` field of `IsLeafwise` in its null-transfer form
  `Work.EKLProd.leafwise_null_transfer_gen` its `νH x`-slice inside the shape is null for a.e.
  base point `x ∈ Z n`.  This is the only content of the theorem beyond the pointwise statement,
  and the reason the statement is not the una.e.-restricted pointwise one: the leafwise measure
  at an arbitrary `h` of the shape says nothing about `h • x` unless `h • x` is in the domain of
  the `H`-leafwise system.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-! ## Two elementary facts about atoms and shapes -/

/-- The atom of a σ-algebra is constant on itself: `y ∈ [x]_m` implies `[y]_m = [x]_m`.
(No countable generation, no separability: contraposition against the complement of an
`m`-measurable set is all that is used.) -/
private theorem atom_eq_of_mem_atom_aux {m : MeasurableSpace X3} {x y : X3}
    (hy : y ∈ atom m x) : atom m y = atom m x := by
  have key : ∀ (a b : X3), b ∈ atom m a →
      ∀ s : Set X3, MeasurableSet[m] s → a ∈ s → b ∈ s := by
    intro a b hab s hs ha
    rw [atom, Set.mem_sInter] at hab
    exact hab s ⟨hs, ha⟩
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, key x y hy s hs.1 hs.2⟩
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    have hxs : x ∈ s := by
      by_contra hx
      exact (key x y hy sᶜ hs.1.compl hx) hs.2
    exact hz s ⟨hs.1, hxs⟩

/-- The shape at the translated point: if `u • x` lies in the atom of `m` at `x`, then the shape
at `u • x` is the right translate by `u⁻¹` of the shape at `x`. -/
private theorem shape_smul_right_aux {U : Subgroup SL3} {u : SL3} (hu : u ∈ U)
    {m : MeasurableSpace X3} {x : X3} (hatom : u • x ∈ atom m x) :
    shape m U (u • x) = (fun g : SL3 => g * u⁻¹) '' shape m U x := by
  have hatomeq := atom_eq_of_mem_atom_aux hatom
  ext g
  rw [shape, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hgU, hgmem⟩
    refine ⟨g * u, ⟨U.mul_mem hgU hu, ?_⟩, by group⟩
    rw [mul_smul]
    rwa [hatomeq] at hgmem
  · rintro ⟨k, ⟨hkU, hkmem⟩, rfl⟩
    refine ⟨U.mul_mem hkU (U.inv_mem hu), ?_⟩
    rw [mul_smul, inv_smul_smul, hatomeq]
    exact hkmem

/-! ## The pointwise covariance -/

/-- **Pointwise fibre covariance**: for `h` in the `H`-shape at `x` *with* `h • x` in the domain
of the `H`-leafwise system, the once-pushed-forward leafwise measure transforms by a constant
along the shape. -/
private theorem prodFlowerLambda_smul_aux {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}
    (hf : ProdFlowerFam H T U μ) (hHcl : IsClosed (H : Set SL3))
    {νH : X3 → MeasureTheory.Measure SL3} {XH : Set X3} (hνH : IsLeafwise μ H νH XH) (n : ℕ)
    {x : X3} (hxZ : x ∈ hf.Z n) (hxXH : x ∈ XH) {h : SL3}
    (hh : h ∈ shape (hf.mH n) H x) (hhXH : h • x ∈ XH) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      prodFlowerΛ hf n νH (h • x) = c • prodFlowerΛ hf n νH x := by
  -- the equivariance of the leafwise system, at the pair `(h • x, x)`
  obtain ⟨c₀, hc₀0, hc₀top, heq⟩ :=
    hνH.equivariant (h • x) hhXH h⁻¹ (H.inv_mem hh.1) (by simpa using hxXH)
  have heq' : νH (h • x) = c₀ • (νH x).map (fun g : SL3 => g * h⁻¹) := by
    simpa using heq
  -- the shape at `h • x` is the right translate of the shape at `x`
  have hshape : shape (hf.mH n) H (h • x)
      = (fun g : SL3 => g * h⁻¹) '' shape (hf.mH n) H x :=
    shape_smul_right_aux hh.1 hh.2
  -- points of the atom of `x` lie in the carrier `Z n`, so the shape at `h • x` is measurable
  have hhZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hh.2
  have hS'meas : MeasurableSet (shape (hf.mH n) H (h • x)) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 (h • x) hhZ).2.2.1
    rw [hOshape]
    exact hOo.measurableSet.inter hHcl.measurableSet
  have hSpre : (fun g : SL3 => g * h⁻¹) ⁻¹' shape (hf.mH n) H (h • x)
      = shape (hf.mH n) H x := by
    rw [hshape]
    exact Set.preimage_image_eq _ (fun a b hab => mul_right_cancel hab)
  refine ⟨c₀, hc₀0, hc₀top, ?_⟩
  rw [prodFlowerΛ, prodFlowerΛ]
  calc ((νH (h • x)).restrict (shape (hf.mH n) H (h • x))).map
          (fun g : SL3 => g * hf.co n (h • x))
      = ((c₀ • (νH x).map (fun g : SL3 => g * h⁻¹)).restrict
          (shape (hf.mH n) H (h • x))).map
          (fun g : SL3 => g * hf.co n (h • x)) := by rw [heq']
    _ = (c₀ • (((νH x).map (fun g : SL3 => g * h⁻¹)).restrict
          (shape (hf.mH n) H (h • x)))).map
          (fun g : SL3 => g * hf.co n (h • x)) := by
        rw [Measure.restrict_smul]
    _ = c₀ • ((((νH x).map (fun g : SL3 => g * h⁻¹)).restrict
          (shape (hf.mH n) H (h • x))).map
          (fun g : SL3 => g * hf.co n (h • x))) := by
        rw [Measure.map_smul] <;> try fun_prop
    _ = c₀ • ((((νH x).restrict ((fun g : SL3 => g * h⁻¹) ⁻¹'
            shape (hf.mH n) H (h • x))).map
            (fun g : SL3 => g * h⁻¹)).map
          (fun g : SL3 => g * hf.co n (h • x))) := by
        rw [Measure.restrict_map (continuous_mul_const h⁻¹).measurable hS'meas]
    _ = c₀ • ((((νH x).restrict (shape (hf.mH n) H x)).map
            (fun g : SL3 => g * h⁻¹)).map
          (fun g : SL3 => g * hf.co n (h • x))) := by
        rw [hSpre]
    _ = c₀ • (((νH x).restrict (shape (hf.mH n) H x)).map
          ((fun g : SL3 => g * hf.co n (h • x)) ∘
            (fun g : SL3 => g * h⁻¹))) := by
        rw [Measure.map_map (continuous_mul_const (hf.co n (h • x))).measurable
          (continuous_mul_const h⁻¹).measurable]
    _ = c₀ • (((νH x).restrict (shape (hf.mH n) H x)).map
          (fun g : SL3 => g * hf.co n x)) := by
        rw [hf.co_smul n x hxZ h hh.1 hh.2,
          show ((fun g : SL3 => g * (h * hf.co n x)) ∘ (fun g : SL3 => g * h⁻¹))
            = (fun g : SL3 => g * hf.co n x)
            from funext fun g => by simp only [Function.comp_apply]; group]

/-! ## The a.e. statement -/

theorem prodFlower_fibre_cov (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) (n : ℕ) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)), ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Work.EKLProd.prodFlowerΛTP hf n νH (h • x) = c • Work.EKLProd.prodFlowerΛTP hf n νH x := by
  classical
  -- the flower domain is measurable
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  -- `XH` is conull for `μ`, hence for the restricted measure
  have hXHaeμ : ∀ᵐ x ∂μ, x ∈ XH := by
    rw [MeasureTheory.ae_iff]
    exact hνH.conull
  have hNnull : (μ.restrict (hf.Z n)) XHᶜ = 0 := by
    apply le_antisymm
    · exact le_trans (Measure.restrict_apply_le (hf.Z n) XHᶜ) (le_of_eq hνH.conull)
    · exact bot_le
  -- the null transfer: for a.e. base point, `νH x`-a.e. `h` of the shape has `h • x ∈ XH`
  have hNT := leafwise_null_transfer_gen (U := H) hνH (hf.plaqH n)
    (prodFlower_shape_mass hf hνH n) hNnull
  filter_upwards [hNT, MeasureTheory.ae_restrict_of_ae hXHaeμ,
    MeasureTheory.ae_restrict_mem hZmeas] with x hNTx hxXH hxZ
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]
    exact hOo.measurableSet.inter hH.1.measurableSet
  rw [MeasureTheory.ae_restrict_iff' hSmeas]
  have hbad : ∀ᵐ h ∂(νH x), ¬ (h ∈ shape (hf.mH n) H x ∧ h • x ∈ XHᶜ) := by
    rw [MeasureTheory.ae_iff]
    simpa using hNTx
  filter_upwards [hbad] with h hhbad hh
  have hhXH : h • x ∈ XH := by
    by_contra hcon
    exact hhbad ⟨hh, hcon⟩
  obtain ⟨c, hc0, hctop, heq⟩ :=
    prodFlowerLambda_smul_aux hf hH.1 hνH n hxZ hxXH hh hhXH
  by_cases hmeas : AEMeasurable (fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g))
      (prodFlowerΛ hf n νH x)
  · exact ⟨c, hc0, hctop, by
      rw [prodFlowerΛTP, prodFlowerΛTP, heq, Measure.map_smul _ hmeas]⟩
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
    rw [one_smul, prodFlowerΛTP, prodFlowerΛTP, heq]
    rcases eq_or_ne (prodFlowerΛ hf n νH x) 0 with h0 | h0
    · simp [h0]
    · have hc' : ¬ AEMeasurable (fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g))
          (c • prodFlowerΛ hf n νH x) := by
        rwa [aemeasurable_smul_measure_iff hc0]
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hc' (by
          rw [Ne, ← Measure.measure_univ_eq_zero, Measure.smul_apply, smul_eq_mul, mul_eq_zero,
            not_or, Measure.measure_univ_eq_zero]
          exact ⟨hc0, h0⟩),
        Measure.map_of_not_aemeasurable_of_ne_zero hmeas h0]

end Work.EKLProd
