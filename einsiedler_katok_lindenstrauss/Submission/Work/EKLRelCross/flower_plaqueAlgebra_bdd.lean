import Mathlib
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLProd.inv_entries_bound
import Submission.Work.EKLProd.plaque_shape_mass

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## 1. Borelness of the flower set from the *local* cross-section property

The global version `Work.EKLRelCross.flowerSet_borel` uses `hCS` for all `u ∈ U`; here the
cross-section property is only assumed on the displacement box `V b`, and the hypothesis
`hprod2` (`(V δ ∩ U)⁻¹ (V δ ∩ U) ⊆ V b`) supplies the missing products.  Everything else is the
Lusin–Souslin argument: the flower set is the image of the Borel set
`(V δ ∩ U) × (C ∩ W)` under the continuous action map, which is injective on that set.
-/

theorem flowerSet_borel_local (h2 : Work.EKLContract.P_X3) {U : Subgroup SL3}
    (hUcl : IsClosed (U : Set SL3)) {C : Set X3} (hC : MeasurableSet C) {b : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1)
    {δ : ℝ}
    (hprod2 : ∀ a ∈ U, a ∈ V δ → ∀ c ∈ U, c ∈ V δ → a⁻¹ * c ∈ V b)
    {W : Set X3} (hW : MeasurableSet W) :
    MeasurableSet (flowerSet U δ C W) := by
  rw [flowerSet_eq_image]
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace X3 := h2.2.1
  refine MeasurableSet.image_of_continuousOn_injOn ?_ continuous_smul.continuousOn ?_
  · exact ((isOpen_V δ).measurableSet.inter hUcl.measurableSet).prod (hC.inter hW)
  · rintro ⟨v, x⟩ ⟨hv, hx⟩ ⟨v', x'⟩ ⟨hv', hx'⟩ heq
    change v • x = v' • x' at heq
    obtain ⟨hvV, hvU⟩ := hv
    obtain ⟨hv'V, hv'U⟩ := hv'
    obtain ⟨hxC, -⟩ := hx
    obtain ⟨hx'C, -⟩ := hx'
    have hmul : (v⁻¹ * v') • x' = x := by rw [mul_smul, ← heq, inv_smul_smul]
    have hmemC : (v⁻¹ * v') • x' ∈ C := by rw [hmul]; exact hxC
    have hU1 : v⁻¹ * v' ∈ U := U.mul_mem (U.inv_mem hvU) hv'U
    have hVb : v⁻¹ * v' ∈ V b := hprod2 v hvU hvV v' hv'U hv'V
    have hone : v⁻¹ * v' = 1 := hCS x' hx'C _ hU1 hVb hmemC
    have hvv : v = v' := inv_mul_eq_one.mp hone
    have hxx : x = x' := by
      rw [← hvv] at heq
      exact smul_left_cancel v heq
    rw [hvv, hxx]

/-! ## 2. The collar of the cross-section and its base point -/

/-- The collar: the `(V δ)⁻¹ ∩ U`-collar of the cross-section `C`. -/
abbrev collar (U : Subgroup SL3) (δ : ℝ) (C : Set X3) : Set X3 := flowerSet U δ C Set.univ

/-- The base point exists: a point of the collar is `v • z` with `v ∈ (V δ)⁻¹ ∩ U`, `z ∈ C`. -/
lemma basePt_exists {U : Subgroup SL3} {δ : ℝ} {C : Set X3} {x : X3}
    (hx : x ∈ collar U δ C) :
    ∃ z : X3, z ∈ C ∧ ∃ v ∈ Vinv δ ∩ (U : Set SL3), v • x = z := by
  obtain ⟨v, hv, hxv⟩ := hx
  exact ⟨v • x, hxv.1, v, hv, rfl⟩

/-- The base point of a point of the collar: the point of `C` from which `x` is obtained by an
element of `(V δ)⁻¹ ∩ U`.  Outside the collar it is set to the fixed point `mkX 1`, so that the
map is total and `m`-measurable. -/
noncomputable def basePt (U : Subgroup SL3) (δ : ℝ) (C : Set X3) (x : X3) : X3 := by
  classical
  exact if h : x ∈ collar U δ C then Classical.choose (basePt_exists h) else mkX 1

/-- An element of `V δ` has its inverse in the inverse box `Vinv δ`. -/
lemma inv_mem_Vinv_of_mem_V {δ : ℝ} {g : SL3} (hg : g ∈ V δ) : g⁻¹ ∈ Vinv δ := by
  rw [mem_Vinv_iff]
  simpa using hg

lemma basePt_mem {U : Subgroup SL3} {δ : ℝ} {C : Set X3} {x : X3} (hx : x ∈ collar U δ C) :
    basePt U δ C x ∈ C ∧ ∃ v ∈ Vinv δ ∩ (U : Set SL3), v • x = basePt U δ C x := by
  rw [basePt, dif_pos hx]
  exact Classical.choose_spec (basePt_exists hx)

lemma basePt_not_mem {U : Subgroup SL3} {δ : ℝ} {C : Set X3} {x : X3}
    (hx : x ∉ collar U δ C) : basePt U δ C x = mkX 1 := by
  rw [basePt, dif_neg hx]

/-- The pattern of the base point: `basePt x ∈ W` iff `x` lies in the flower over `W`. -/
lemma basePt_pattern {U : Subgroup SL3} {C W : Set X3} {b δ : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1)
    (hprod : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b)
    {x : X3} (hx : x ∈ collar U δ C) :
    basePt U δ C x ∈ W ↔ x ∈ flowerSet U δ C W := by
  obtain ⟨hxC, v, hv, hvx⟩ := basePt_mem hx
  obtain ⟨hvV, hvU⟩ := hv
  have hxeq : x = v⁻¹ • basePt U δ C x := by
    rw [← hvx, ← mul_smul, inv_mul_cancel, one_smul]
  conv_rhs => rw [hxeq]
  exact (flowerSet_mem_iff_of_mem_local hCS hprod (W := W) (u := v⁻¹)
    ⟨mem_Vinv_iff.mp hvV, U.inv_mem hvU⟩ hxC).symm

/-- **Entrywise bound on a translate of `V ε`.**  For `u₀ ∈ V ε`, the set of `u` with
`u * u₀ ∈ V ε` is entrywise bounded: `u = (u * u₀) * u₀⁻¹` with `u * u₀` entrywise bounded by
`1 + ε` and `u₀⁻¹` by the adjugate bound. -/
lemma mulV_entries_bound {ε : ℝ} (hε : 0 < ε) {u₀ : SL3} (hu₀ : u₀ ∈ V ε) :
    ∃ C : ℝ, ∀ u : SL3, u * u₀ ∈ V ε → ∀ i j, |u i j| ≤ C := by
  obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound ε hε
  refine ⟨3 * (1 + ε) * C, ?_⟩
  intro u hu i j
  have hA : ∀ k l, |((u * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ 1 + ε :=
    fun k l => Work.EKLProd.mem_V_entries_le hu k l
  have hB : ∀ k l, |((u₀⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ C :=
    fun k l => hC u₀ hu₀ k l
  have hcoe : ((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((u * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) *
        ((u₀⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_right]
  rw [hcoe, Matrix.mul_apply]
  calc |∑ k : Fin 3, ((u * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k *
          ((u₀⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j|
      ≤ ∑ k : Fin 3, |((u * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k *
          ((u₀⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 3, |((u * u₀ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i k| *
          |((u₀⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, (1 + ε) * C := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) (by linarith)
    _ = 3 * (1 + ε) * C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 3. The flower σ-algebra of a bounded cross-section is a plaque algebra -/

open MeasureTheory in
theorem flower_plaqueAlgebra_bdd (h2 : Work.EKLContract.P_X3)
    {U : Subgroup Work.EKLContract.SL3} (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {C : Set Work.EKLContract.X3} (hC : MeasurableSet C)
    {b : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ Work.EKLContract.V b → u • z ∈ C → u = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hprod : ∀ w ∈ U, w ∈ Work.EKLRelCross.Vinv δ → ∀ u ∈ U, u ∈ Work.EKLContract.V δ →
      w * u ∈ Work.EKLContract.V b)
    (hprod2 : ∀ a ∈ U, a ∈ Work.EKLContract.V δ → ∀ c ∈ U, c ∈ Work.EKLContract.V δ →
      a⁻¹ * c ∈ Work.EKLContract.V b)
    {W : ℕ → Set Work.EKLContract.X3} (hW0 : W 0 = Set.univ) (hWopen : ∀ n, IsOpen (W n))
    (hWgen : borel Work.EKLContract.X3 = MeasurableSpace.generateFrom (Set.range W))
    (hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z') :
    Work.EKLContract.IsPlaqueAlgebra U
      (⋃ c ∈ C ∩ {x : Work.EKLContract.X3 | ∀ u ∈ U, u • x = x → u = 1},
        Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) c)
      (Work.EKLRelCross.flowerSigma U δ C W) := by
  classical
  have hmemV1 : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  -- (1) each generator is Borel, so `m ≤ borel X₃`
  have hgen : ∀ n, MeasurableSet (flowerSet U δ C (W n)) := fun n =>
    flowerSet_borel_local h2 hUcl hC hCS hprod2 (hWopen n).measurableSet
  have hm_borel : flowerSigma U δ C W ≤ borel X3 := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨n, rfl⟩
    exact hgen n
  -- (2) `m` is countably generated
  have hm_cnt : ∃ bb : Set (Set X3), bb.Countable ∧
      flowerSigma U δ C W = MeasurableSpace.generateFrom bb :=
    ⟨Set.range (fun n => flowerSet U δ C (W n)),
      Set.countable_range (fun n => flowerSet U δ C (W n)), rfl⟩
  -- (3) the collar is `m`-measurable (it is the generator `n = 0`)
  have hmcoll : MeasurableSet[flowerSigma U δ C W] (collar U δ C) := by
    rw [show (collar U δ C : Set X3) = flowerSet U δ C (W 0) by simp only [collar, hW0]]
    exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self 0)
  -- (4) the base map is `m`-measurable
  have hconst : ∀ n, MeasurableSet[flowerSigma U δ C W] {x : X3 | mkX 1 ∈ W n} := by
    intro n
    by_cases hd : mkX 1 ∈ W n
    · rw [show {x : X3 | mkX 1 ∈ W n} = (Set.univ : Set X3) from
          Set.eq_univ_of_forall (fun _ => hd)]
      exact MeasurableSet.univ
    · rw [show {x : X3 | mkX 1 ∈ W n} = (∅ : Set X3) from by
          ext x; exact ⟨fun h => absurd h hd, fun h => h.elim⟩]
      exact MeasurableSpace.measurableSet_empty (flowerSigma U δ C W)
  have hbase_meas : Measurable[flowerSigma U δ C W] (basePt U δ C) := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (basePt U δ C) (borel X3) ≤ flowerSigma U δ C W
    rw [hWgen, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨n, hn, rfl⟩
    obtain ⟨m, rfl⟩ := hn
    have hpre : basePt U δ C ⁻¹' (W m)
        = flowerSet U δ C (W m) ∪ ((collar U δ C)ᶜ ∩ {x : X3 | mkX 1 ∈ W m}) := by
      ext x
      by_cases hx : x ∈ collar U δ C
      · have hp := basePt_pattern hCS hprod (U := U) (δ := δ) (C := C) (W := W m) hx
        rw [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        refine ⟨fun h => Or.inl (hp.mp h), ?_⟩
        rintro (h1 | ⟨h2, -⟩)
        · exact hp.mpr h1
        · exact absurd hx h2
      · have hd := basePt_not_mem (U := U) (δ := δ) (C := C) hx
        rw [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, hd]
        refine ⟨fun h => Or.inr ⟨hx, h⟩, ?_⟩
        rintro (h1 | ⟨-, h2⟩)
        · exact absurd (flowerSet_mono (Set.subset_univ (W m)) h1) hx
        · exact h2
    rw [hpre]
    exact (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self m)).union
      (hmcoll.compl.inter (hconst m))
  -- (5) the collar cut at the free-based points of `C` is the union of the atoms over them
  have hZeq : (⋃ c ∈ C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1},
        atom (flowerSigma U δ C W) c)
      = collar U δ C ∩ basePt U δ C ⁻¹' (C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1}) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨c, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hc, hxc⟩ := hx
      obtain ⟨hcC, hcfree⟩ := hc
      have hxc' : x ∈ atom (MeasurableSpace.generateFrom
          (Set.range (fun n => flowerSet U δ C (W n)))) c := by
        rwa [show flowerSigma U δ C W
          = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n)))
          from rfl] at hxc
      have hpat : ∀ n, x ∈ flowerSet U δ C (W n) ↔ c ∈ W n := by
        intro n
        have h1 := mem_atom_iff_pattern.mp hxc' (flowerSet U δ C (W n)) (Set.mem_range_self n)
        have h2 := flowerSet_mem_iff_of_mem_local hCS hprod (W := W n) (u := (1 : SL3))
          ⟨hmemV1, U.one_mem⟩ hcC
        simp only [one_smul] at h2
        exact h1.trans h2
      have hxcoll : x ∈ collar U δ C := by
        have h0 : x ∈ flowerSet U δ C (W 0) := (hpat 0).mpr (by rw [hW0]; exact Set.mem_univ c)
        rw [show (collar U δ C : Set X3) = flowerSet U δ C (W 0) by simp only [collar, hW0]]
        exact h0
      have hbaseC : basePt U δ C x ∈ C := (basePt_mem hxcoll).1
      have hbasec : basePt U δ C x = c := by
        refine hsep (basePt U δ C x) hbaseC c hcC ?_
        intro n
        exact (basePt_pattern hCS hprod (U := U) (δ := δ) (C := C) (W := W n) hxcoll).trans
          (hpat n)
      refine ⟨hxcoll, ?_⟩
      rw [Set.mem_preimage]
      exact ⟨by rw [hbasec]; exact hcC, by rw [hbasec]; exact hcfree⟩
    · rintro ⟨hxcoll, hxbase⟩
      rw [Set.mem_preimage] at hxbase
      obtain ⟨hbaseC, hbasefree⟩ := hxbase
      have hkey : ∀ n, x ∈ flowerSet U δ C (W n) ↔
          basePt U δ C x ∈ flowerSet U δ C (W n) := by
        intro n
        have h1 := basePt_pattern hCS hprod (U := U) (δ := δ) (C := C) (W := W n) hxcoll
        have h2 := flowerSet_mem_iff_of_mem_local hCS hprod (W := W n) (u := (1 : SL3))
          ⟨hmemV1, U.one_mem⟩ hbaseC
        simp only [one_smul] at h2
        exact h1.symm.trans h2.symm
      rw [Set.mem_iUnion]
      refine ⟨basePt U δ C x, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨hbaseC, hbasefree⟩, ?_⟩
      rw [show flowerSigma U δ C W
        = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n))) from rfl]
      refine mem_atom_iff_pattern.mpr ?_
      rintro A ⟨n, rfl⟩
      exact hkey n
  -- (6) `Z` is `m`-measurable
  have hZ_meas : MeasurableSet[flowerSigma U δ C W]
      (⋃ c ∈ C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1},
        atom (flowerSigma U δ C W) c) := by
    rw [hZeq]
    exact hmcoll.inter (hbase_meas (hC.inter (freeSet_borel hUcl)))
  refine ⟨hm_borel, hm_cnt, hZ_meas, ?_⟩
  intro x hxZ
  rw [hZeq] at hxZ
  obtain ⟨hxcoll, hxbase⟩ := hxZ
  rw [Set.mem_preimage] at hxbase
  obtain ⟨hbaseC, hbasefree⟩ := hxbase
  obtain ⟨-, v, hv, hvx⟩ := basePt_mem (U := U) (δ := δ) (C := C) hxcoll
  obtain ⟨hvVinv, hvU⟩ := hv
  have hvV : v⁻¹ ∈ V δ := mem_Vinv_iff.mp hvVinv
  have hvU' : v⁻¹ ∈ U := U.inv_mem hvU
  have hxeq : x = v⁻¹ • basePt U δ C x := by
    rw [← hvx, ← mul_smul, inv_mul_cancel, one_smul]
  have hatom : atom (flowerSigma U δ C W) x
      = (fun u : SL3 => u • basePt U δ C x) '' (V δ ∩ (U : Set SL3)) :=
    atom_flower_local hCS hδ hprod hW0 hsep (v := v⁻¹) hvV hvU' hbaseC hxeq
  have hshape : shape (flowerSigma U δ C W) U x
      = {g : SL3 | g * v⁻¹ ∈ V δ} ∩ (U : Set SL3) := by
    ext u
    constructor
    · intro hu
      have huU : u ∈ U := hu.1
      have huAtom : u • x ∈ atom (flowerSigma U δ C W) x := hu.2
      rw [hatom] at huAtom
      obtain ⟨w', ⟨hw'V, hw'U⟩, hw'eq⟩ := huAtom
      have hw'' : w' • basePt U δ C x = u • x := hw'eq
      have hux : (u * v⁻¹) • basePt U δ C x = u • x := by
        rw [mul_smul]
        exact (congrArg (fun t => u • t) hxeq).symm
      have hfix : (w'⁻¹ * (u * v⁻¹)) • basePt U δ C x = basePt U δ C x := by
        rw [mul_smul, hux, ← hw'', inv_smul_smul]
      have hUmem : w'⁻¹ * (u * v⁻¹) ∈ U := U.mul_mem (U.inv_mem hw'U) (U.mul_mem huU hvU')
      have hone : w'⁻¹ * (u * v⁻¹) = 1 := hbasefree _ hUmem hfix
      have hone' : u * v⁻¹ = w' := (inv_mul_eq_one.mp hone).symm
      refine ⟨?_, huU⟩
      show u * v⁻¹ ∈ V δ
      rw [hone']
      exact hw'V
    · rintro ⟨huV, huU⟩
      refine ⟨huU, ?_⟩
      rw [hatom]
      refine ⟨u * v⁻¹, ⟨huV, U.mul_mem huU hvU'⟩, ?_⟩
      show (u * v⁻¹) • basePt U δ C x = u • x
      rw [mul_smul]
      exact (congrArg (fun t => u • t) hxeq).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the atom of a point of `Z` is contained in `Z`
    intro y hy
    rw [hatom] at hy
    obtain ⟨u, ⟨huV, huU⟩, hy_eq⟩ := hy
    have hy' : u • basePt U δ C x = y := hy_eq
    have hyc : u • basePt U δ C x ∈ collar U δ C := by
      refine ⟨u⁻¹, ⟨inv_mem_Vinv_of_mem_V huV, U.inv_mem huU⟩, ?_⟩
      rw [inv_smul_smul]
      exact ⟨hbaseC, Set.mem_univ _⟩
    have hybase : basePt U δ C (u • basePt U δ C x) = basePt U δ C x := by
      refine hsep _ (basePt_mem hyc).1 _ hbaseC ?_
      intro n
      exact (basePt_pattern hCS hprod (U := U) (δ := δ) (C := C) (W := W n) hyc).trans
        (flowerSet_mem_iff_of_mem_local hCS hprod (W := W n) (u := u) ⟨huV, huU⟩ hbaseC)
    rw [hZeq, ← hy']
    exact ⟨hyc, by rw [Set.mem_preimage, hybase]; exact ⟨hbaseC, hbasefree⟩⟩
  · -- the atom of a point of `Z` lies in the `U`-orbit of that point
    intro y hy
    rw [hatom] at hy
    obtain ⟨u, ⟨huV, huU⟩, hy_eq⟩ := hy
    have hy' : u • basePt U δ C x = y := hy_eq
    refine ⟨u * v, U.mul_mem huU hvU, ?_⟩
    have hstep : (u * v) • x = u • basePt U δ C x := by
      rw [mul_smul]
      exact congrArg (fun t => u • t) hvx
    show (u * v) • x = y
    rw [hstep, hy']
  · -- the shape is `O ∩ U` with `O` open
    exact ⟨{g : SL3 | g * v⁻¹ ∈ V δ}, (isOpen_V δ).preimage (by fun_prop), hshape⟩
  · -- the shape is entrywise bounded
    obtain ⟨C₀, hC₀⟩ := mulV_entries_bound hδ hvV
    refine ⟨C₀, ?_⟩
    intro u hu i j
    have huv : u * v⁻¹ ∈ V δ := by
      have h2 := hu
      rw [hshape] at h2
      exact h2.1
    exact hC₀ u huv i j

end Work.EKLRelCross
