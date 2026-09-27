import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLProd.prodFlower_T_slice
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLProd.prodFlower_Lambda_prod
import Submission.Work.EKLProd.ProdFlowerLemmas

/-!
# `Work.EKLRelProduct.structAtH`

The product structure of the `H`-plaquette measure at the translate `h • x` of a point `x` of the
`n`-th product-box flower: the joint law of the two plaque coordinates `hT T U ·`, `hU T U ·` is
the product of the `T`-factor `etaT` and the `U`-factor `psi`.

The proof has four ingredients.

* **Measurability of the coordinates.**  `hT T U`, `hU T U` are defined by `Classical.choose`, so
  measurability is not automatic.  On `H` however the *contraction* hypothesis `hcontr` (together
  with `hcent`) computes them as limits of the continuous maps `h ↦ aDiag t ^ k * h * (aDiag t ^ k)⁻¹`,
  hence they are Borel on the closed set `H` (`measurable_coord_of_contracting`).
* **The product structure at the base point** `Work.EKLProd.prodFlower_Lambda_prod`, which holds for
  `μ`-a.e. `y ∈ hf.Z n`; the passage to `(νH x) ↾ shape (mH n) H x`-a.e. `h` for `μ`-a.e. `x` is the
  null transfer `Work.EKLProd.leafwise_null_transfer_gen`.
* **The rewinding algebra** `hT_hU_mul_inv_co`: on the `H`-shape at `y`, writing `co n y = t_y * u_y`,
  `hT T U w = hT T U (w * co n y) * t_y⁻¹` and `hU T U w = t_y * hU T U (w * co n y) * u_y⁻¹ * t_y⁻¹`.
* **The identification of the factors**: `etaT` is `prodFlowerκ` after the shift by `t_y`
  (`etaT_apply_eq_prodFlowerκ`) and `psi` is the second marginal of the joint law
  (`prodFlowerΛTP`); everything else is `Measure.map_apply`/`Measure.restrict_apply` bookkeeping.
-/

open MeasureTheory
open scoped Pointwise ENNReal

open Work.EKLContract Work.EKLProd

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

variable {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}

/-! ## Measurability of the coordinates of the decomposition `H = T · U` -/

/-- **The coordinates `hT T U`, `hU T U` are Borel measurable**, provided `T` centralises the
diagonal element `aDiag t` while `U` is contracted by it.  Indeed for `h ∈ H` with decomposition
`h = g * u` (`g ∈ T`, `u ∈ U`) one has
`aDiag t ^ k * h * (aDiag t ^ k)⁻¹ = g * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹) → g = hT T U h`,
so `hT T U` is a pointwise limit of continuous functions on the closed set `H`, and
`hU T U h = (hT T U h)⁻¹ * h`; outside `H` both coordinates are the junk value `1`. -/
theorem measurable_coord_of_contracting {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3))
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, aDiag t * g = g * aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun k : ℕ => aDiag t ^ k * u * (aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) :
    Measurable (fun w : SL3 => (hT T U w, hU T U w)) := by
  classical
  have hlim : ∀ h : ↥H, Filter.Tendsto
      (fun k : ℕ => aDiag t ^ k * (h : SL3) * (aDiag t ^ k)⁻¹)
      Filter.atTop (nhds (hT T U (h : SL3))) := by
    intro h
    obtain ⟨g, hgT, u, huU, hgu⟩ := hcop (h : SL3) h.2
    have hTeq : hT T U (h : SL3) = g := hT_eq_of_factor hcop hdisj h.2 hgT huU hgu.symm
    have hpow : ∀ k : ℕ, (aDiag t) ^ k * g = g * (aDiag t) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
        calc (aDiag t) ^ (n+1) * g
            = aDiag t * ((aDiag t) ^ n * g) := by rw [pow_succ', mul_assoc]
          _ = aDiag t * (g * (aDiag t) ^ n) := by rw [ih]
          _ = (aDiag t * g) * (aDiag t) ^ n := by group
          _ = (g * aDiag t) * (aDiag t) ^ n := by rw [hcent g hgT]
          _ = g * ((aDiag t) ^ n * aDiag t) := by group
          _ = g * (aDiag t) ^ (n+1) := by rw [pow_succ]
    have hkey : (fun k : ℕ => aDiag t ^ k * (h : SL3) * (aDiag t ^ k)⁻¹)
        = fun k : ℕ => g * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹) := by
      funext k
      rw [hgu]
      calc aDiag t ^ k * (g * u) * (aDiag t ^ k)⁻¹
          = (aDiag t ^ k * g) * (u * (aDiag t ^ k)⁻¹) := by group
        _ = (g * aDiag t ^ k) * (u * (aDiag t ^ k)⁻¹) := by rw [hpow k]
        _ = g * (aDiag t ^ k * u * (aDiag t ^ k)⁻¹) := by group
    rw [hkey, hTeq]
    simpa using (hcontr u huU).const_mul g
  have hTmeas : Measurable (fun h : ↥H => hT T U (h : SL3)) :=
    measurable_of_tendsto_metrizable
      (f := fun k : ℕ => fun h : ↥H => aDiag t ^ k * (h : SL3) * (aDiag t ^ k)⁻¹)
      (fun _ => by fun_prop) (tendsto_pi_nhds.mpr (fun h => hlim h))
  have hUmeas : Measurable (fun h : ↥H => hU T U (h : SL3)) := by
    have hfun : (fun h : ↥H => hU T U (h : SL3))
        = fun h : ↥H => (hT T U (h : SL3))⁻¹ * (h : SL3) := by
      funext h
      obtain ⟨g, hgT, u, huU, hgu⟩ := hcop (h : SL3) h.2
      have hdec := hT_mul_hU ⟨g, hgT, u, huU, hgu⟩
      calc hU T U (h : SL3)
          = (hT T U (h : SL3))⁻¹ * (hT T U (h : SL3) * hU T U (h : SL3)) := by group
        _ = (hT T U (h : SL3))⁻¹ * (h : SL3) := by rw [hdec]
    rw [hfun]
    exact (hTmeas.inv).mul measurable_subtype_coe
  have hpair : Measurable (fun h : ↥H => (hT T U (h : SL3), hU T U (h : SL3))) :=
    hTmeas.prod hUmeas
  have hpiece : Measurable (fun w : SL3 => if _hw : w ∈ (H : Set SL3) then
      (hT T U w, hU T U w) else (1, 1)) :=
    Measurable.dite hpair (g := fun _ : ↥(H : Set SL3)ᶜ => (1, 1)) measurable_const
      hHc.measurableSet
  have heq : (fun w : SL3 => (hT T U w, hU T U w))
      = fun w : SL3 => if _hw : w ∈ (H : Set SL3) then (hT T U w, hU T U w) else (1, 1) := by
    funext w
    by_cases hw : w ∈ (H : Set SL3)
    · simp [hw]
    · rw [dif_neg hw]
      have hno : ¬ ∃ p : SL3 × SL3, p.1 ∈ T ∧ p.2 ∈ U ∧ p.1 * p.2 = w := by
        rintro ⟨p, hp1, hp2, hpw⟩
        exact hw (hpw ▸ H.mul_mem (hTH hp1) (hUH hp2))
      have hdec : decompose T U w = (1, 1) := by
        rw [decompose]; exact dif_neg hno
      simp [hT, hU, hdec]
  rw [heq]
  exact hpiece

/-- The product box `(V R ∩ T) * (V R ∩ U)` is Borel: it is the set of `g ∈ H` whose two
coordinates lie in `V R`. -/
theorem measurableSet_prodBox {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3))
    (hcoord : Measurable (fun w : SL3 => (hT T U w, hU T U w))) (R : ℝ) :
    MeasurableSet (prodBox T U R) := by
  have hset : prodBox T U R
      = (H : Set SL3) ∩ (fun w : SL3 => (hT T U w, hU T U w)) ⁻¹' (V R ×ˢ V R) := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, haV, b, hbV, hab⟩ := Set.mem_mul.mp hg
      have hgH : g ∈ H := hab ▸ H.mul_mem (hTH haV.2) (hUH hbV.2)
      have hT' : hT T U g = a := hT_eq_of_factor hcop hdisj hgH haV.2 hbV.2 hab
      have hdec : hT T U g * hU T U g = g := hT_mul_hU ⟨a, haV.2, b, hbV.2, hab.symm⟩
      have hU' : hU T U g = b := by
        rw [hT'] at hdec
        exact mul_left_cancel (by rw [hdec, hab])
      refine ⟨hgH, ?_⟩
      simp only [Set.mem_preimage, Set.mem_prod, hT', hU']
      exact ⟨haV.1, hbV.1⟩
    · rintro ⟨hgH, hgV⟩
      rw [Set.mem_preimage, Set.mem_prod] at hgV
      exact ⟨hT T U g, ⟨hgV.1, hT_mem (hcop g hgH)⟩, hU T U g, ⟨hgV.2, hU_mem (hcop g hgH)⟩,
        hT_mul_hU (hcop g hgH)⟩
  rw [hset]
  exact hHc.measurableSet.inter
    (hcoord ((Work.EKLComp.isOpen_V R).measurableSet.prod (Work.EKLComp.isOpen_V R).measurableSet))

/-- **The rewinding algebra.**  With `c = co n y = t_y * u_y` and `w * c` in the product box,
the coordinates of `w` are obtained from those of `w * c` by right translation with `t_y⁻¹`
respectively by conjugation (and translation) with `t_y, u_y`. -/
theorem hT_hU_mul_inv_co {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {R : ℝ} {c w : SL3} (hc : c ∈ prodBox T U R) (hw : w * c ∈ prodBox T U R) :
    hT T U w = hT T U (w * c) * (hT T U c)⁻¹ ∧
    hU T U w = hT T U c * hU T U (w * c) * (hU T U c)⁻¹ * (hT T U c)⁻¹ := by
  obtain ⟨a, haV, b, hbV, hab⟩ := Set.mem_mul.mp hc
  obtain ⟨a', ha'V, b', hb'V, ha'b'⟩ := Set.mem_mul.mp hw
  have hcH : c ∈ H := prodBox_subset_H hTH hUH hc
  have hwcH : w * c ∈ H := prodBox_subset_H hTH hUH hw
  have hwH : w ∈ H := by
    have h := H.mul_mem hwcH (H.inv_mem hcH)
    rwa [mul_inv_cancel_right] at h
  have hTc : hT T U c = a := hT_eq_of_factor hcop hdisj hcH haV.2 hbV.2 hab
  have hTwc : hT T U (w * c) = a' := hT_eq_of_factor hcop hdisj hwcH ha'V.2 hb'V.2 ha'b'
  have hUc : hU T U c = b := by
    have hdec : hT T U c * hU T U c = c := hT_mul_hU ⟨a, haV.2, b, hbV.2, hab.symm⟩
    rw [hTc] at hdec
    exact mul_left_cancel (by rw [hdec, hab])
  have hUwc : hU T U (w * c) = b' := by
    have hdec : hT T U (w * c) * hU T U (w * c) = w * c :=
      hT_mul_hU ⟨a', ha'V.2, b', hb'V.2, ha'b'.symm⟩
    rw [hTwc] at hdec
    exact mul_left_cancel (by rw [hdec, ha'b'])
  have hUfac : a * (b' * b⁻¹) * a⁻¹ ∈ U :=
    hnorm a haV.2 (b' * b⁻¹) (U.mul_mem hb'V.2 (U.inv_mem hbV.2))
  have hfac : (a' * a⁻¹) * (a * (b' * b⁻¹) * a⁻¹) = w := by
    have h1 : w = (w * c) * c⁻¹ := by group
    rw [h1, ← ha'b', ← hab]
    group
  have hTw : hT T U w = a' * a⁻¹ :=
    hT_eq_of_factor hcop hdisj hwH (T.mul_mem ha'V.2 (T.inv_mem haV.2)) hUfac hfac
  have hUw : hU T U w = a * (b' * b⁻¹) * a⁻¹ := by
    have hdec : hT T U w * hU T U w = w :=
      hT_mul_hU ⟨a' * a⁻¹, T.mul_mem ha'V.2 (T.inv_mem haV.2), a * (b' * b⁻¹) * a⁻¹, hUfac,
        hfac.symm⟩
    rw [hTw] at hdec
    exact mul_left_cancel (by rw [hdec, hfac])
  refine ⟨?_, ?_⟩
  · rw [hTw, hTwc, hTc]
  · rw [hUw, hUwc, hUc, hTc]
    group

/-- **`etaT` is `prodFlowerκ` after the shift by the `T`-part of the coordinate**: both are the
normalised restriction of `νT y` to the source set `S_T`, the one written with the shifted
argument `A' * {t_y}`. -/
theorem etaT_apply_eq_prodFlowerκ {H T U : Subgroup SL3} {μ : Measure X3}
    (hf : ProdFlowerFam H T U μ) (hTc : IsClosed (T : Set SL3))
    (νT : X3 → Measure SL3) (n : ℕ) (y : X3) {A' : Set SL3} (hA' : MeasurableSet A') :
    etaT hf νT n y A' = prodFlowerκ hf n νT y (A' * ({hT T U (hf.co n y)} : Set SL3)) := by
  set t : SL3 := hT T U (hf.co n y) with ht
  have hA''meas : MeasurableSet (A' * ({t} : Set SL3)) := by
    rw [Set.mul_singleton, Set.image_mul_right]
    exact hA'.preimage (continuous_mul_const t⁻¹).measurable
  have hmeas1 : MeasurableSet (V hf.R ∩ (T : Set SL3)) :=
    (Work.EKLComp.isOpen_V hf.R).measurableSet.inter hTc.measurableSet
  have hmeas2 : MeasurableSet ((A' * ({t} : Set SL3)) ∩ (V hf.R ∩ (T : Set SL3))) :=
    hA''meas.inter hmeas1
  have hsetX : (fun g : SL3 => g * t) ⁻¹' (V hf.R ∩ (T : Set SL3)) = S_T hf n y := by
    unfold S_T
    rw [← ht]
    rfl
  have hsetY : (fun g : SL3 => g * t) ⁻¹'
        ((A' * ({t} : Set SL3)) ∩ (V hf.R ∩ (T : Set SL3))) = A' ∩ S_T hf n y := by
    rw [show S_T hf n y = (fun g : SL3 => g * t) ⁻¹' (V hf.R ∩ (T : Set SL3))
      from hsetX.symm]
    ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hg1
      rw [Set.mem_singleton_iff] at hb
      subst hb
      have hag : a = g := mul_right_cancel hab
      subst hag
      exact ⟨ha, hg2⟩
    · rintro ⟨hA', hS⟩
      exact ⟨⟨g, hA', t, rfl, rfl⟩, hS⟩
  have hX : ((νT y).map (fun g : SL3 => g * t)) (V hf.R ∩ (T : Set SL3))
      = (νT y) (S_T hf n y) := by
    rw [Measure.map_apply (continuous_mul_const t).measurable hmeas1, hsetX]
  have hY : ((νT y).map (fun g : SL3 => g * t))
        ((A' * ({t} : Set SL3)) ∩ (V hf.R ∩ (T : Set SL3)))
      = (νT y) (A' ∩ S_T hf n y) := by
    rw [Measure.map_apply (continuous_mul_const t).measurable hmeas2, hsetY]
  rw [etaT, prodFlowerκ, Measure.smul_apply, Measure.smul_apply,
      Measure.restrict_apply hA', Measure.restrict_apply hA''meas, smul_eq_mul, smul_eq_mul,
      hX, hY]

theorem structAtH {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff)
    (hHoroH : Work.EKLContract.IsHoro H) (hHoroT : Work.EKLContract.IsHoro T) (hUH : U ≤ H) (hTH : T ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hmu : Work.EKLContract.IsAInvariant μ) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      ∀ {A' B' : Set Work.EKLContract.SL3}, MeasurableSet A' → MeasurableSet B' →
        ((νH (h • x)).restrict (Work.EKLContract.shape (hf.mH n) H (h • x)))
            {w : Work.EKLContract.SL3 | Work.EKLProd.hT T U w ∈ A' ∧ Work.EKLProd.hU T U w ∈ B'}
          = Work.EKLRelProduct.etaT hf νT n (h • x) A' * Work.EKLRelProduct.psi hf νH n (h • x) B' := by


  classical
  have hHc : IsClosed (H : Set SL3) := hHoroH.1
  have hTc : IsClosed (T : Set SL3) := hHoroT.1
  have hcoord : Measurable (fun w : SL3 => (hT T U w, hU T U w)) :=
    measurable_coord_of_contracting hTH hUH hcop hdisj hHc t hcent hcontr
  have hUmeas : Measurable (fun w : SL3 => hU T U w) := measurable_snd.comp hcoord
  have hprodBox : ∀ R : ℝ, MeasurableSet (prodBox T U R) :=
    fun R => measurableSet_prodBox hTH hUH hcop hdisj hHc hcoord R
  -- the product structure at `μ`-a.e. base point
  have hprod := prodFlower_Lambda_prod hX3 hLeaf hBirk hmu hHoroH hHoroT hTH hUH hnorm hcop hdisj
    hf hνH hνT n t hcent hcontr
  set N : Set X3 := {y : X3 | ¬ (IsFiniteMeasure (prodFlowerΛTP hf n νH y) ∧
      prodFlowerΛTP hf n νH y
        = (prodFlowerκ hf n νT y).prod ((prodFlowerΛTP hf n νH y).map Prod.snd))} with hN
  have hNnull : (μ.restrict (hf.Z n)) N = 0 := by
    rw [hN]
    exact ae_iff.mp hprod
  have htransfer := leafwise_null_transfer_gen hνH (hf.plaqH n) (prodFlower_shape_mass hf hνH n)
    hNnull
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  filter_upwards [htransfer, MeasureTheory.ae_restrict_mem hZmeas] with x hxN hxZ
  have hshapeX : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hO, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]
    exact hO.measurableSet.inter hHc.measurableSet
  have hxNae : ∀ᵐ h ∂(νH x), ¬ (h ∈ shape (hf.mH n) H x ∧ h • x ∈ N) := by
    rw [ae_iff]
    simpa only [not_not] using hxN
  have hxN' : ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)), h • x ∉ N := by
    refine (MeasureTheory.ae_restrict_iff' hshapeX).mpr ?_
    filter_upwards [hxNae] with h hh hhshape
    exact fun hN => hh ⟨hhshape, hN⟩
  filter_upwards [MeasureTheory.ae_restrict_mem hshapeX, hxN'] with h hhshape hhN
  intro A' B' hA' hB'
  set y : X3 := h • x with hy
  have hyZ : y ∈ hf.Z n := by
    rw [hy]
    exact ((hf.plaqH n).2.2.2 x hxZ).1 hhshape.2
  have hhy : y ∉ N := by
    rw [hy]
    exact hhN
  have hgood : IsFiniteMeasure (prodFlowerΛTP hf n νH y) ∧
      prodFlowerΛTP hf n νH y
        = (prodFlowerκ hf n νT y).prod ((prodFlowerΛTP hf n νH y).map Prod.snd) :=
    not_not.mp hhy
  haveI hfin : IsFiniteMeasure (prodFlowerΛTP hf n νH y) := hgood.1
  -- abbreviations
  set S : Set SL3 := {w : SL3 | hT T U w ∈ A' ∧ hU T U w ∈ B'} with hS
  set ta : SL3 := hT T U (hf.co n y) with hta
  set ua : SL3 := hU T U (hf.co n y) with hua
  set c : SL3 := hf.co n y with hc
  set A'' : Set SL3 := A' * ({ta} : Set SL3) with hA''
  set AU : Set SL3 := (fun u : SL3 => ta * u * ua⁻¹ * ta⁻¹) ⁻¹' B' with hAU
  set Mo : MeasureTheory.Measure SL3 := (νH y).restrict (shape (hf.mH n) H y) with hM
  set La : MeasureTheory.Measure SL3 := Mo.map (fun w : SL3 => w * c) with hL
  have hta' : ta = hT T U c := by rw [hta, hc]
  have hua' : ua = hU T U c := by rw [hua, hc]
  have hc_mem : c ∈ prodBox T U hf.R := by
    rw [hc]
    exact hf.co_mem n y hyZ
  have hshapeY : MeasurableSet (shape (hf.mH n) H y) := by
    rw [hf.shapeH n y hyZ]
    have hset : {g : SL3 | g ∈ H ∧ g * hf.co n y ∈ prodBox T U hf.R}
        = (H : Set SL3) ∩ (fun g : SL3 => g * hf.co n y) ⁻¹' prodBox T U hf.R := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      exact Iff.rfl
    rw [hset]
    exact hHc.measurableSet.inter
      ((continuous_mul_const (hf.co n y)).measurable (hprodBox hf.R))
  have hLeq : prodFlowerΛ hf n νH y = La := by
    rw [prodFlowerΛ, hL, hM, hc]
  have hTPeq : prodFlowerΛTP hf n νH y
      = La.map (fun g : SL3 => (hT T U g, hU T U g)) := by
    rw [prodFlowerΛTP, hLeq]
  have hpsieq : psi hf νH n y = Mo.map (fun w : SL3 => hU T U w) := by
    rw [psi, hM]
  have hSmeas : MeasurableSet S := by
    rw [hS]
    have hset : {w : SL3 | hT T U w ∈ A' ∧ hU T U w ∈ B'}
        = (fun w : SL3 => (hT T U w, hU T U w)) ⁻¹' (A' ×ˢ B') := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod]
    rw [hset]
    exact hcoord (hA'.prod hB')
  have hA''meas : MeasurableSet A'' := by
    rw [hA'', Set.mul_singleton, Set.image_mul_right]
    exact hA'.preimage (continuous_mul_const ta⁻¹).measurable
  have hAUmeas : MeasurableSet AU := by
    rw [hAU]
    exact hB'.preimage (by fun_prop)
  have hWmeas : MeasurableSet (A'' ×ˢ AU) := hA''meas.prod hAUmeas
  have hcoordW : MeasurableSet ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU)) :=
    hcoord hWmeas
  have hXmeas : MeasurableSet ((fun w : SL3 => w * c) ⁻¹'
      ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU))) :=
    hcoordW.preimage (continuous_mul_const c).measurable
  -- rewinding the coordinates: the pointwise statement inside the shape
  have hkey_pt : ∀ w : SL3, w ∈ shape (hf.mH n) H y →
      ((hT T U w, hU T U w) ∈ A' ×ˢ B' ↔
        (hT T U (w * c), hU T U (w * c)) ∈ A'' ×ˢ AU) := by
    intro w hwsh
    have hwc : w * c ∈ prodBox T U hf.R := by
      have h1 := hwsh
      rw [hf.shapeH n y hyZ] at h1
      obtain ⟨-, hwc₀⟩ := h1
      rw [hc]
      exact hwc₀
    obtain ⟨hTw, hUw⟩ := hT_hU_mul_inv_co hTH hUH hnorm hcop hdisj hc_mem hwc
    constructor
    · rintro ⟨hwA, hwB⟩
      refine ⟨?_, ?_⟩
      · rw [hA'', Set.mem_mul]
        refine ⟨hT T U w, hwA, ta, rfl, ?_⟩
        rw [hTw, ← hta']
        group
      · show ta * hU T U (w * c) * ua⁻¹ * ta⁻¹ ∈ B'
        rw [hta', hua', ← hUw]
        exact hwB
    · rintro ⟨hwT, hwU⟩
      have hwT' : hT T U (w * c) ∈ A' * ({ta} : Set SL3) := by
        rw [hA''] at hwT
        exact hwT
      have hwU' : ta * hU T U (w * c) * ua⁻¹ * ta⁻¹ ∈ B' := hwU
      obtain ⟨a, haA, b, hb, hab⟩ := Set.mem_mul.mp hwT'
      rw [Set.mem_singleton_iff] at hb
      subst hb
      refine ⟨?_, ?_⟩
      · have hTwa : hT T U w = a := by
          rw [hTw, ← hta', ← hab]
          group
        rw [hTwa]
        exact haA
      · show hU T U w ∈ B'
        rw [hUw]
        rw [hta', hua'] at hwU'
        exact hwU'
  have hkey : S ∩ shape (hf.mH n) H y
      = (fun w : SL3 => w * c) ⁻¹' ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU))
        ∩ shape (hf.mH n) H y := by
    ext w
    constructor
    · rintro ⟨hwS, hwsh⟩
      exact ⟨(hkey_pt w hwsh).mp hwS, hwsh⟩
    · rintro ⟨hwW, hwsh⟩
      exact ⟨(hkey_pt w hwsh).mpr hwW, hwsh⟩
  -- the second marginal of the joint law is `psi`
  have hX2meas : MeasurableSet ((fun w : SL3 => w * c) ⁻¹'
      ((fun g : SL3 => hU T U g) ⁻¹' AU)) :=
    (hAUmeas.preimage hUmeas).preimage (continuous_mul_const c).measurable
  have hsetid_pt : ∀ w : SL3, w ∈ shape (hf.mH n) H y →
      (hU T U (w * c) ∈ AU ↔ hU T U w ∈ B') := by
    intro w hwsh
    have hwc : w * c ∈ prodBox T U hf.R := by
      have h1 := hwsh
      rw [hf.shapeH n y hyZ] at h1
      obtain ⟨-, hwc₀⟩ := h1
      rw [hc]
      exact hwc₀
    obtain ⟨hTw, hUw⟩ := hT_hU_mul_inv_co hTH hUH hnorm hcop hdisj hc_mem hwc
    constructor
    · intro hw
      have hw' : ta * hU T U (w * c) * ua⁻¹ * ta⁻¹ ∈ B' := hw
      rw [hta', hua'] at hw'
      show hU T U w ∈ B'
      rw [hUw]
      exact hw'
    · intro hw
      have hgoal : ta * hU T U (w * c) * ua⁻¹ * ta⁻¹ ∈ B' := by
        rw [hta', hua', ← hUw]
        exact hw
      exact hgoal
  have hsetid : (fun w : SL3 => w * c) ⁻¹' ((fun g : SL3 => hU T U g) ⁻¹' AU)
      ∩ shape (hf.mH n) H y
      = (fun w : SL3 => hU T U w) ⁻¹' B' ∩ shape (hf.mH n) H y := by
    ext w
    constructor
    · rintro ⟨hw, hwsh⟩
      exact ⟨(hsetid_pt w hwsh).mp hw, hwsh⟩
    · rintro ⟨hw, hwsh⟩
      exact ⟨(hsetid_pt w hwsh).mpr hw, hwsh⟩
  have hsig : ((prodFlowerΛTP hf n νH y).map Prod.snd) AU = psi hf νH n y B' := by
    have hσeq : (prodFlowerΛTP hf n νH y).map Prod.snd = La.map (fun g : SL3 => hU T U g) := by
      rw [hTPeq, Measure.map_map measurable_snd hcoord]
      rfl
    calc ((prodFlowerΛTP hf n νH y).map Prod.snd) AU
        = (La.map (fun g : SL3 => hU T U g)) AU := by rw [hσeq]
      _ = La ((fun g : SL3 => hU T U g) ⁻¹' AU) := by
            rw [Measure.map_apply hUmeas hAUmeas]
      _ = Mo ((fun w : SL3 => w * c) ⁻¹' ((fun g : SL3 => hU T U g) ⁻¹' AU)) := by
            rw [hL, Measure.map_apply (continuous_mul_const c).measurable
              (hAUmeas.preimage hUmeas)]
      _ = (νH y) ((fun w : SL3 => w * c) ⁻¹' ((fun g : SL3 => hU T U g) ⁻¹' AU)
            ∩ shape (hf.mH n) H y) := by
            rw [hM, Measure.restrict_apply hX2meas]
      _ = (νH y) ((fun w : SL3 => hU T U w) ⁻¹' B' ∩ shape (hf.mH n) H y) := by
            rw [hsetid]
      _ = Mo ((fun w : SL3 => hU T U w) ⁻¹' B') := by
            rw [hM, Measure.restrict_apply (hB'.preimage hUmeas)]
      _ = (Mo.map (fun w : SL3 => hU T U w)) B' := by
            rw [Measure.map_apply hUmeas hB']
      _ = psi hf νH n y B' := by rw [hpsieq]
  -- the `T`-factor
  have hk : (prodFlowerκ hf n νT y) A'' = etaT hf νT n y A' := by
    rw [hA'', hta]
    exact (etaT_apply_eq_prodFlowerκ hf hTc νT n y hA').symm
  -- assembly
  have hstep1 : Mo S = Mo (S ∩ shape (hf.mH n) H y) := by
    rw [hM, Measure.restrict_apply hSmeas,
      Measure.restrict_apply (hSmeas.inter hshapeY), Set.inter_assoc, Set.inter_self]
  have hstep2 : Mo ((fun w : SL3 => w * c) ⁻¹'
        ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU))
        ∩ shape (hf.mH n) H y)
      = La ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU)) := by
    rw [hL, Measure.map_apply (continuous_mul_const c).measurable hcoordW,
      hM, Measure.restrict_apply (hXmeas.inter hshapeY), Measure.restrict_apply hXmeas,
      Set.inter_assoc, Set.inter_self]
  have hstep3 : La ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU))
      = (La.map (fun g : SL3 => (hT T U g, hU T U g))) (A'' ×ˢ AU) := by
    rw [Measure.map_apply hcoord hWmeas]
  have hstep4 : (La.map (fun g : SL3 => (hT T U g, hU T U g))) (A'' ×ˢ AU)
      = ((prodFlowerκ hf n νT y).prod ((prodFlowerΛTP hf n νH y).map Prod.snd))
          (A'' ×ˢ AU) := by
    have h1 : La.map (fun g : SL3 => (hT T U g, hU T U g)) = prodFlowerΛTP hf n νH y :=
      hTPeq.symm
    rw [h1]
    exact congrArg (fun m => m (A'' ×ˢ AU)) hgood.2
  have hstep5 : ((prodFlowerκ hf n νT y).prod ((prodFlowerΛTP hf n νH y).map Prod.snd))
        (A'' ×ˢ AU)
      = (prodFlowerκ hf n νT y) A'' * ((prodFlowerΛTP hf n νH y).map Prod.snd) AU := by
    rw [Measure.prod_prod]
  have hkey' : Mo S = Mo ((fun w : SL3 => w * c) ⁻¹'
        ((fun g : SL3 => (hT T U g, hU T U g)) ⁻¹' (A'' ×ˢ AU))
        ∩ shape (hf.mH n) H y) := by rw [hstep1, hkey]
  exact hkey'.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans
    (by rw [hk, hsig])))))


end Work.EKLRelProduct

end
