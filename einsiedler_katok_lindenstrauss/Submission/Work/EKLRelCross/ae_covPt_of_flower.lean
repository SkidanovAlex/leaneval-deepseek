import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLRelCross.plaque_ratio
import Submission.Work.EKLRelCross.CovarianceDefs

/-!
# `Work.EKLRelCross.ae_covPt_of_flower`

`A`-covariance of a system of leafwise measures for a *single* diagonal element `aDiag t`,
starting from a countable *flower family* of plaque algebras whose bases cover `μ`-almost every
point and whose atoms contain the `R`-plaques of `U` (Pisa Cor. 6.15).

The local input is Pisa 7.17 (`Work.EKLRelCross.covariant_shape_aux`, proved in this workspace):
for a plaque algebra `(Z, m)` it gives, at `μ`-a.e. base point, the proportionality of
`ν (aDiag t • x)` and the `aDiag t`-conjugate of `ν x` on the shape of the atom at `x`
(`Work.EKLRelCross.local_covPt_shape`, which drops the inessential hypothesis `μ Z ≠ 0`).

The flower family is used twice:

* it lets us *choose*, at `μ`-a.e. `x` and for every `n`, one plaque algebra of the family at
  the scale `R = n + 3` whose shape at `x` contains `V (n+3) ∩ U`;
* comparing the several proportionality constants on the fixed set `V 3 ∩ U` — which has positive
  finite `ν x`-mass — shows that they all agree, and since `⋃_n V (n+3) ∩ U = U` and both
  `ν (aDiag t • x)` and the conjugate of `ν x` are carried by `U`, continuity from below of the
  two measures upgrades the identity from `V (n+3) ∩ U` to all of `U`.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

/-! ## Elementary facts about the diagonal conjugation -/

/-- Monotonicity of the displacement neighbourhoods in the radius. -/
theorem covPt_V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

/-- Conjugation by `aDiag t` is measurable. -/
theorem covPt_conj_measurable (t : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-- Conjugation by `aDiag t` is injective. -/
theorem covPt_conj_injective (t : Fin 3 → ℝ) :
    Function.Injective (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) := by
  intro g h hgh
  have hgh' : aDiag t * g * (aDiag t)⁻¹ = aDiag t * h * (aDiag t)⁻¹ := hgh
  calc g = (aDiag t)⁻¹ * (aDiag t * g * (aDiag t)⁻¹) * aDiag t := by group
    _ = (aDiag t)⁻¹ * (aDiag t * h * (aDiag t)⁻¹) * aDiag t := by rw [hgh']
    _ = h := by group

/-- Conjugation by `aDiag t` is surjective. -/
theorem covPt_conj_surjective (t : Fin 3 → ℝ) :
    Function.Surjective (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  fun z => ⟨(aDiag t)⁻¹ * z * aDiag t, by group⟩

/-- The left inverse used for the injectivity of the conjugation. -/
theorem covPt_conj_left (t : Fin 3 → ℝ) (g : SL3) :
    (aDiag t)⁻¹ * (aDiag t * g * (aDiag t)⁻¹) * aDiag t = g := by group

/-- The right inverse used for the surjectivity of the conjugation. -/
theorem covPt_conj_right (t : Fin 3 → ℝ) (g : SL3) :
    aDiag t * ((aDiag t)⁻¹ * g * aDiag t) * (aDiag t)⁻¹ = g := by group

/-- The preimage of the conjugated image is the original set. -/
theorem covPt_preimage_conjDs (t : Fin 3 → ℝ) (D : Set SL3) :
    (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' (conjDs t D) = D := by
  have h : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' (conjDs t D)
      = (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹'
          ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' D) := rfl
  rw [h, Set.preimage_image_eq _ (covPt_conj_injective t)]

/-- `aDiag t`-conjugation preserves `U` (for the horospherical subgroups we use). -/
theorem covPt_conj_mem_U {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) (g : SL3) :
    aDiag t * g * (aDiag t)⁻¹ ∈ U ↔ g ∈ U := by
  constructor
  · intro hg
    have h1 := hU.2.1 (-t) _ hg
    rw [Work.EKLC6Core.aDiag_neg_eq_inv t, inv_inv] at h1
    rwa [covPt_conj_left t g] at h1
  · intro hg
    exact hU.2.1 t g hg

/-- The preimage of `U` under `aDiag t`-conjugation is `U`. -/
theorem covPt_conj_preimage_U {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' (U : Set SL3) = (U : Set SL3) :=
  Set.ext fun g => covPt_conj_mem_U hU t g

/-- The image of `U` under `aDiag t`-conjugation is `U`. -/
theorem covPt_conj_image_U {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' (U : Set SL3) = (U : Set SL3) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨g, hg, rfl⟩
    exact (covPt_conj_mem_U hU t g).mpr hg
  · intro z hz
    refine ⟨(aDiag t)⁻¹ * z * aDiag t, ?_, covPt_conj_right t z⟩
    have h1 := hU.2.1 (-t) z hz
    rw [Work.EKLC6Core.aDiag_neg_eq_inv t, inv_inv] at h1
    exact h1

/-- `U` is the union of the increasing family `n ↦ V (n+3) ∩ U`. -/
theorem covPt_U_subset_iUnion_V3 {U : Subgroup SL3} :
    (U : Set SL3) ⊆ ⋃ n : ℕ, (V ((n : ℝ) + 3) ∩ (U : Set SL3)) := by
  intro z hz
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i j, |(z : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < M := by
    refine ⟨(Finset.univ.sup' Finset.univ_nonempty (fun p : Fin 3 × Fin 3 =>
      |(z : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)) + 1, ?_⟩
    intro i j
    have hle := Finset.le_sup' (f := fun p : Fin 3 × Fin 3 =>
      |(z : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine Set.mem_iUnion.mpr ⟨N, ?_, hz⟩
  intro i j
  have hNM : M < (N : ℝ) := hN
  linarith [hM i j]

/-! ## Pisa 7.17 in the orientation used below -/

/-- **Pisa 7.17, orientation of the flower argument.**  For a plaque algebra `(Z, m)`, at
`μ`-a.e. base point `x` with `x ∈ X'`, `aDiag t • x ∈ X'`, `x ∈ Z` and free `U`-orbit, the
leafwise measure at `aDiag t • x` is proportional to the conjugate of `ν x` *on the conjugate of
the shape at `x`*.

This is `Work.EKLRelCross.covariant_shape_aux` with `t` replaced by `-t` and applied at the point
`aDiag t • x`; unlike the version recorded in `ae_covariance` it needs no positivity of `μ Z`. -/
theorem local_covPt_shape {U : Subgroup SL3} (hU : IsHoro U)
    {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ) (ht : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {Z : Set X3} (S : MAlgX) (hpla : IsPlaqueAlgebra U Z S.m) :
    ∀ᵐ x ∂μ, x ∈ X' → aDiag t • x ∈ X' → x ∈ Z →
      (∀ u ∈ U, u • x = x → u = 1) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ D : Set SL3, MeasurableSet D →
        D ⊆ shape S.m U x → ν (aDiag t • x) (conjDs t D) = c * ν x D := by
  have htneg : MeasurePreserving (fun x : X3 => aDiag (-t) • x) μ μ := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    have hcomp : (fun x : X3 => aDiag (-t) • x) ∘ (fun x : X3 => aDiag t • x) = id := by
      funext x
      simp only [Function.comp_apply, id_eq]
      exact aDiag_neg_smul t x
    calc μ.map (fun x : X3 => aDiag (-t) • x)
        = (μ.map (fun x : X3 => aDiag t • x)).map (fun x : X3 => aDiag (-t) • x) := by
          rw [ht.map_eq]
      _ = μ.map ((fun x : X3 => aDiag (-t) • x) ∘ (fun x : X3 => aDiag t • x)) := by
          rw [Measure.map_map (continuous_const_smul _).measurable
            (continuous_const_smul _).measurable]
      _ = μ.map id := by rw [hcomp]
      _ = μ := Measure.map_id
  have hcs := covariant_shape_aux (U := U) hU (μ := μ) (ν := ν) (X' := X') hL (-t) htneg S hpla
  have hcs' := ht.quasiMeasurePreserving.ae hcs
  filter_upwards [hcs'] with x hx
  intro hxX hxX' hxZ hfree
  have hx0 : smulDiag (-t) (aDiag t • x) = x := aDiag_neg_smul t x
  have h := hx hxX' (by rw [hx0]; exact hxX) (by rw [hx0]; exact hxZ) (by rw [hx0]; exact hfree)
  obtain ⟨c, hc0, hct, hcc⟩ := h
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  intro D hD hDsub
  have h1 := hcc D hD (by rw [hx0]; exact hDsub)
  rw [hx0] at h1
  have hmap : (ν (aDiag t • x)).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) D
      = ν (aDiag t • x) (conjDs t D) := by
    have h0 := Measure.map_apply (μ := ν (aDiag t • x))
      (f := fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) (s := D)
      (((continuous_const.mul continuous_id).mul continuous_const).measurable) hD
    rw [h0, preimage_conjDs_neg]
  rw [hmap] at h1
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/-! ## The main theorem -/

theorem ae_covPt_of_flower {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hfree : Filter.Eventually (fun x => ∀ u ∈ U, u • x = x → u = 1) (MeasureTheory.ae μ))
    (hfam : ∀ R : ℝ, 0 < R → ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set Work.EKLContract.X3)
      (mm : ι → MeasurableSpace Work.EKLContract.X3) (G : ι → Set Work.EKLContract.X3),
      (∀ i, Work.EKLContract.IsPlaqueAlgebra U (Z i) (mm i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)
        ⊆ Work.EKLContract.shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0)
    (t : Fin 3 → ℝ)
    (ht : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ) :
    Filter.Eventually (fun x => ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (Work.EKLContract.aDiag t • x) =
        c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹))
      (MeasureTheory.ae μ) := by
  classical
  -- the flower families, at the radii `n + 3`
  have hfam' : ∀ n : ℕ, ∃ (ι : Type) (_ : Countable ι) (Z : ι → Set X3)
      (mm : ι → MeasurableSpace X3) (G : ι → Set X3),
      (∀ i, IsPlaqueAlgebra U (Z i) (mm i)) ∧ (∀ i, MeasurableSet (G i)) ∧
      (∀ i, G i ⊆ Z i) ∧
      (∀ i, ∀ x ∈ G i, V ((n : ℝ) + 3) ∩ (U : Set SL3) ⊆ shape (mm i) U x) ∧
      μ (⋃ i, G i)ᶜ = 0 := fun n => hfam ((n : ℝ) + 3) (by positivity)
  choose ι hι Z mm G h1 h2 h3 h4 h5 using hfam'
  -- the conull statements
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [ae_iff]
    exact hL.conull
  have hX'tae : ∀ᵐ x ∂μ, aDiag t • x ∈ X' := ht.quasiMeasurePreserving.ae hX'ae
  have hcovfl : ∀ᵐ x ∂μ, ∀ n : ℕ, ∃ k : ι n, x ∈ G n k := by
    rw [ae_all_iff]
    intro n
    haveI : Countable (ι n) := hι n
    rw [ae_iff]
    have hset : {x : X3 | ¬ ∃ k : ι n, x ∈ G n k} = (⋃ k, G n k)ᶜ := by
      ext x
      simp
    rw [hset]
    exact h5 n
  have hloc : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ k : ι n,
      (x ∈ X' → aDiag t • x ∈ X' → x ∈ Z n k →
        (∀ u ∈ U, u • x = x → u = 1) →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ D : Set SL3, MeasurableSet D →
          D ⊆ shape (mm n k) U x → ν (aDiag t • x) (conjDs t D) = c * ν x D) := by
    rw [ae_all_iff]
    intro n
    haveI : Countable (ι n) := hι n
    rw [ae_all_iff]
    intro k
    exact local_covPt_shape (U := U) hU (μ := μ) (ν := ν) (X' := X') hL t ht
      (Z := Z n k) ⟨mm n k⟩ (h1 n k)
  filter_upwards [hloc, hcovfl, hX'ae, hX'tae, hfree] with x hlocx hxG hxX hytX hfreex
  have hkk : ∀ n : ℕ, x ∈ G n (Classical.choose (hxG n)) := fun n => Classical.choose_spec (hxG n)
  have hlocn : ∀ n : ℕ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ D : Set SL3, MeasurableSet D →
        D ⊆ shape (mm n (Classical.choose (hxG n))) U x →
        ν (aDiag t • x) (conjDs t D) = c * ν x D := by
    intro n
    obtain ⟨c, hc0, hcT, hcD⟩ :=
      hlocx n (Classical.choose (hxG n)) hxX hytX (h3 n _ (hkk n)) hfreex
    exact ⟨c, hc0, hcT, hcD⟩
  choose cc hcc0 hccT hccD using hlocn
  -- the reference set `V 3 ∩ U` has positive finite `ν x`-mass
  have hD0meas : MeasurableSet (V 3 ∩ (U : Set SL3)) :=
    ((Work.EKLContract.Lemmas.V_open_one 3 (by norm_num)).1).measurableSet.inter
      hU.1.measurableSet
  have hD0pos : 0 < ν x (V 3 ∩ (U : Set SL3)) :=
    plaqueRatio_box_pos (U := U) hL hxX (δ := 3) (by norm_num)
  have hD0lt : ν x (V 3 ∩ (U : Set SL3)) < ⊤ := plaqueRatio_box_lt_top (U := U) hL hxX 3
  have hD0shape : ∀ n : ℕ,
      V 3 ∩ (U : Set SL3) ⊆ shape (mm n (Classical.choose (hxG n))) U x := by
    intro n z hz
    refine h4 n (Classical.choose (hxG n)) x (hkk n) ⟨fun i j => ?_, hz.2⟩
    have h3le : (3 : ℝ) ≤ (n : ℝ) + 3 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact lt_of_lt_of_le (hz.1 i j) h3le
  -- all the local constants agree
  have hceq : ∀ n : ℕ, cc n = cc 0 := by
    intro n
    have h1 := hccD n (V 3 ∩ (U : Set SL3)) hD0meas (hD0shape n)
    have h2 := hccD 0 (V 3 ∩ (U : Set SL3)) hD0meas (hD0shape 0)
    have h3 : cc n * ν x (V 3 ∩ (U : Set SL3)) = cc 0 * ν x (V 3 ∩ (U : Set SL3)) := by
      rw [← h1, h2]
    exact (ENNReal.mul_left_inj hD0pos.ne' hD0lt.ne).mp h3
  have hstep : ∀ n : ℕ, ∀ D : Set SL3, MeasurableSet D →
      D ⊆ V ((n : ℝ) + 3) ∩ (U : Set SL3) →
      ν (aDiag t • x) (conjDs t D) = cc 0 * ν x D := by
    intro n D hD hDsub
    rw [← hceq n]
    exact hccD n D hD (fun z hz => h4 n (Classical.choose (hxG n)) x (hkk n) (hDsub hz))
  -- the increasing family covering `U`
  have hWUnion : (⋃ n : ℕ, (V ((n : ℝ) + 3) ∩ (U : Set SL3))) = (U : Set SL3) :=
    Set.Subset.antisymm (Set.iUnion_subset fun n => Set.inter_subset_right) covPt_U_subset_iUnion_V3
  have hconjU : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' (U : Set SL3) = (U : Set SL3) :=
    covPt_conj_image_U hU t
  have hνcar : ν (aDiag t • x) ((U : Set SL3)ᶜ) = 0 := hL.carried _ hytX
  have hρcar : ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)) ((U : Set SL3)ᶜ) = 0 := by
    rw [Measure.map_apply (covPt_conj_measurable t) hU.1.measurableSet.compl, Set.preimage_compl,
      covPt_conj_preimage_U hU t]
    exact hL.carried x hxX
  refine ⟨cc 0, hcc0 0, hccT 0, Measure.ext fun C hC => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  have hTUnion : (⋃ n : ℕ, ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
        (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C)) = C ∩ (U : Set SL3) := by
    have himage : (⋃ n : ℕ, (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
        (V ((n : ℝ) + 3) ∩ (U : Set SL3))) = (U : Set SL3) := by
      rw [← Set.image_iUnion, hWUnion, hconjU]
    rw [← Set.iUnion_inter, himage, Set.inter_comm]
  have hTmono : Monotone (fun n : ℕ => (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
      (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C) := by
    intro a b hab
    have hle : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    have hWab : V ((a : ℝ) + 3) ∩ (U : Set SL3) ⊆ V ((b : ℝ) + 3) ∩ (U : Set SL3) :=
      Set.inter_subset_inter_left _ (covPt_V_mono (by linarith))
    exact Set.inter_subset_inter_left C (Set.image_mono hWab)
  have hstep' : ∀ n : ℕ, ν (aDiag t • x) ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
        (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C)
      = cc 0 * ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
        ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C) := by
    intro n
    have hT : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) '' (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C
        = conjDs t ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
            ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3))) := by
      have hT0 : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
            ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
              ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3)))
          = (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
              (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C := by
        rw [Set.image_inter (covPt_conj_injective t),
          Set.image_preimage_eq _ (covPt_conj_surjective t), Set.inter_comm]
      rw [conjDs, ← hT0]
    have hDnmeas : MeasurableSet ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
        ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3))) :=
      (hC.preimage (covPt_conj_measurable t)).inter
        (((Work.EKLContract.Lemmas.V_open_one ((n : ℝ) + 3) (by positivity)).1).measurableSet.inter
          hU.1.measurableSet)
    have h1 := hstep n _ hDnmeas Set.inter_subset_right
    have h2 : ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
        (conjDs t ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
          ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3))))
        = ν x ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
            ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3))) := by
      have h2a := Measure.map_apply (μ := ν x)
        (f := fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)
        (s := conjDs t ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' C
          ∩ (V ((n : ℝ) + 3) ∩ (U : Set SL3))))
        (covPt_conj_measurable t) (measurableSet_conjDs t hDnmeas)
      rw [h2a, covPt_preimage_conjDs]
    rw [hT, h1, h2]
  have hCU : ν (aDiag t • x) (C ∩ (U : Set SL3)) =
      cc 0 * ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)) (C ∩ (U : Set SL3)) := by
    rw [← hTUnion]
    rw [show ν (aDiag t • x) (⋃ n : ℕ, ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
          (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C))
        = ⨆ n : ℕ, ν (aDiag t • x) ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
          (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C) from hTmono.measure_iUnion]
    rw [show ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
          (⋃ n : ℕ, ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
            (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C))
        = ⨆ n : ℕ, ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
            ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
              (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C) from hTmono.measure_iUnion]
    rw [show (⨆ n : ℕ, ν (aDiag t • x) ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
          (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C))
        = ⨆ n : ℕ, cc 0 * ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
            ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ''
              (V ((n : ℝ) + 3) ∩ (U : Set SL3)) ∩ C) from iSup_congr fun n => hstep' n]
    rw [ENNReal.mul_iSup]
  have hνC : ν (aDiag t • x) C = ν (aDiag t • x) (C ∩ (U : Set SL3)) := by
    conv_lhs => rw [← Set.inter_union_compl C (U : Set SL3)]
    rw [measure_union (Set.disjoint_left.mpr fun z hz1 hz2 => hz2.2 hz1.2)
        (hC.inter hU.1.measurableSet.compl),
      measure_mono_null (Set.inter_subset_right : C ∩ (U : Set SL3)ᶜ ⊆ (U : Set SL3)ᶜ) hνcar,
      add_zero]
  have hρC : ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)) C =
      ((ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)) (C ∩ (U : Set SL3)) := by
    conv_lhs => rw [← Set.inter_union_compl C (U : Set SL3)]
    rw [measure_union (Set.disjoint_left.mpr fun z hz1 hz2 => hz2.2 hz1.2)
        (hC.inter hU.1.measurableSet.compl),
      measure_mono_null (Set.inter_subset_right : C ∩ (U : Set SL3)ᶜ ⊆ (U : Set SL3)ᶜ) hρcar,
      add_zero]
  rw [hνC, hρC]
  exact hCU

end

end Work.EKLRelCross
