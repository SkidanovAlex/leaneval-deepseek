import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.shape_smulMS
import Submission.Work.EKLC7.restrict_smulSt
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLC7.atom_smulMS
import Submission.Work.EKLC7.BigShapeFlowers
import Submission.Work.EKLC7.AeFreeStab
import Submission.Work.EKLC7.LeafNuFields
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.propor_aux
import Submission.Work.EKLRelCross.rightQuasiInv
import Submission.Work.EKLRelCross.leafwise_propor

/-!
# `Work.EKLC7Ae.Endgame` — assembly of the direction `IsUInvariant μ U ⟹ a.e. Haar (U4)`

The target of this file is clause (U4) of the frozen leafwise-measure contract, in the direction

  `IsUInvariant μ U` ⟹ `∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (g ↦ g * u) = ν x`.

The content is the *assembly*: given

* a countable family of plaque algebras `(Z n, m n)` with measurable bases `G n` whose shapes at
  the base points contain the plaques `V (R n + 2) ∩ U` (produced from
  `Work.EKLC7.BigShapeFlowers`),
* the *shape proportionality* (Pisa 6.27 at the level of a single plaque; EKL (6)): for every
  `u ∈ U` and a.e. `x`, the left translate `(ν x).map (g ↦ u⁻¹ * g)` of the leafwise measure is
  proportional to `ν x` on every shape `shape (m n) U x` whose carrier contains `x`,
* the closedness of the set of multipliers `{u | σ.map (g ↦ u * g) ∝ σ}` for `σ = ν x`,

we deduce the conclusion, using the dichotomy `(U5)` (`Work.EKLRelCross.leafwise_propor`) and
`Work.EKLRelCross.rightQuasiInv` (left quasi-invariance ⟹ right quasi-invariance).

The globalisation argument: the shapes `shape (m n) U x` over the indices `n` with `x ∈ Z n`
cover `U` (for every radius `r` some shape contains `V (r + 2) ∩ U`), and all the proportionality
constants agree — comparing two shapes on the normalised box `Box1 U`, which lies in all of them
and has `ν x`-mass one.  Continuity from below then gives the equality on
`⋃_r (V (r + 2) ∩ U) = U`, hence on all of `SL₃(ℝ)` since both measures are carried by `U`.
-/

namespace Work.EKLC7Ae

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}
  {ν : X3 → MeasureTheory.Measure SL3} {X' : Set X3}

/-! ## 1. Elementary facts -/

/-- `V δ` is monotone in `δ`. -/
lemma V_mono {δ δ' : ℝ} (h : δ ≤ δ') : (V δ : Set SL3) ⊆ V δ' :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- Every element of `SL₃(ℝ)` lies in the `(r + c)`-neighbourhood of the identity for large `r`. -/
theorem exists_mem_V_add (y : SL3) (c : ℝ) : ∃ r : ℕ, y ∈ V ((r : ℝ) + c) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (∑ p : Fin 3 × Fin 3,
    |((y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| - c)
  refine ⟨r, fun i j => ?_⟩
  have h1 : |((y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ ∑ p : Fin 3 × Fin 3, |((y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| :=
    Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 =>
      |((y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
  linarith

/-- If `μ` is `U`-invariant and `X'` is conull, then `u • x ∈ X'` for a.e. `x`. -/
theorem ae_smul_mem_of_invariant (hinv : IsUInvariant μ U) {u : SL3} (hu : u ∈ U)
    {X' : Set X3} (hX'meas : MeasurableSet X') (hX' : μ X'ᶜ = 0) :
    ∀ᵐ x ∂μ, u • x ∈ X' := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : X3 | ¬ u • x ∈ X'} = (fun y : X3 => u⁻¹ • y) '' X'ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨u • x, hx, ?_⟩
      show u⁻¹ • (u • x) = x
      rw [inv_smul_smul]
    · rintro ⟨y, hy, hyx⟩ hmem
      rw [← hyx] at hmem
      have h2 : u • (u⁻¹ • y) = y := by rw [smul_inv_smul]
      rw [h2] at hmem
      exact hy hmem
  rw [hset]
  have hΦ : Function.Injective (fun y : X3 => u⁻¹ • y) := Work.EKLC7.smul_injective u⁻¹
  have hmeas : Measurable (fun y : X3 => u⁻¹ • y) := by fun_prop
  have himg : MeasurableSet ((fun y : X3 => u⁻¹ • y) '' X'ᶜ) :=
    (Homeomorph.smul u⁻¹).toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr
      hX'meas.compl
  have hmap : Measure.map (fun y : X3 => u⁻¹ • y) μ = μ := (hinv u⁻¹ (U.inv_mem hu)).map_eq
  calc μ ((fun y : X3 => u⁻¹ • y) '' X'ᶜ)
      = Measure.map (fun y : X3 => u⁻¹ • y) μ ((fun y : X3 => u⁻¹ • y) '' X'ᶜ) := by rw [hmap]
    _ = μ ((fun y : X3 => u⁻¹ • y) ⁻¹' ((fun y : X3 => u⁻¹ • y) '' X'ᶜ)) :=
        Measure.map_apply hmeas himg
    _ = μ X'ᶜ := by rw [Set.preimage_image_eq _ hΦ]
    _ = 0 := hX'

/-- The set of multipliers `u` for which `σ.map (g ↦ u * g)` is a finite non-zero multiple
of `σ`.  This is the subgroup of `SL₃(ℝ)` whose closedness (`Work.EKLComp.quasiInv_closed`)
upgrades quasi-invariance from a dense countable set to the whole group. -/
def QuasiInvLeft (σ : MeasureTheory.Measure SL3) : Set SL3 :=
  {u : SL3 | ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ σ.map (fun g => u * g) = c • σ}

/-- A measure carried by `U` is unchanged by intersecting with `U`. -/
lemma measure_inter_U_eq_carried {σ : MeasureTheory.Measure SL3}
    (hcar : σ (U : Set SL3)ᶜ = 0) (S : Set SL3) : σ (S ∩ (U : Set SL3)) = σ S := by
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  have h : S ⊆ S ∩ (U : Set SL3) ∪ S ∩ (U : Set SL3)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Set.mem_union_left _ ⟨hy, hyU⟩
    · exact Set.mem_union_right _ ⟨hy, hyU⟩
  calc σ S ≤ σ (S ∩ (U : Set SL3) ∪ S ∩ (U : Set SL3)ᶜ) := measure_mono h
    _ ≤ σ (S ∩ (U : Set SL3)) + σ (S ∩ (U : Set SL3)ᶜ) := measure_union_le _ _
    _ ≤ σ (S ∩ (U : Set SL3)) + 0 := by
        refine add_le_add le_rfl (le_of_eq ?_)
        exact measure_mono_null (Set.inter_subset_right : (S ∩ (U : Set SL3)ᶜ) ⊆ (U : Set SL3)ᶜ) hcar
    _ = σ (S ∩ (U : Set SL3)) := add_zero _

/-- Left multiplication by `u ∈ U` preserves the carrier `U`, so the translated measure is still
carried by `U`. -/
lemma map_mul_left_carried (hUcl : IsClosed (U : Set SL3)) {σ : MeasureTheory.Measure SL3}
    (hcar : σ (U : Set SL3)ᶜ = 0) {u : SL3} (hu : u ∈ U) :
    (σ.map (fun g : SL3 => u * g)) (U : Set SL3)ᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) hUcl.measurableSet.compl]
  have hpre : (fun g : SL3 => u * g) ⁻¹' (U : Set SL3)ᶜ = (U : Set SL3)ᶜ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro h hgU
      exact h (U.mul_mem hu hgU)
    · intro hg hgu
      exact hg (by
        have h2 : u⁻¹ * (u * g) ∈ U := U.mul_mem (U.inv_mem hu) hgu
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2)
  rw [hpre]
  exact hcar

/-! ## 2. The countable family of plaque algebras with arbitrarily large shapes -/

/-- **A countable family of plaque algebras with arbitrarily large shapes.**

For every `r : ℕ` there is a countable family of plaque algebras whose bases are conull and at
whose points the shape contains `V (r + 2) ∩ U`.  Collecting the countably many families into one
`ℕ`-indexed family (via `Nat.pair`) gives the data used below. -/
theorem exists_shape_family (h2 : P_X3) (μ : MeasureTheory.Measure X3)
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup SL3) (hU : IsHoro U)
    (t0 : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1)) :
    ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (R : ℕ → ℕ),
      (∀ n, IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      (∀ n, R n = (Nat.unpair n).1) ∧
      (∀ n, ∀ x ∈ G n, V ((R n : ℝ) + 2) ∩ (U : Set SL3) ⊆ shape (m n) U x) ∧
      (∀ᵐ x ∂μ, ∀ r : ℕ, ∃ n, R n = r ∧ x ∈ G n) := by
  choose Z G m hpa hbase hcov hshape using fun r : ℕ =>
    Work.EKLC7.BigShapeFlowers h2 μ U hU t0 hmp hcontr ((r : ℝ) + 2) (by positivity)
  refine ⟨fun n => Z (Nat.unpair n).1 (Nat.unpair n).2,
    fun n => G (Nat.unpair n).1 (Nat.unpair n).2,
    fun n => m (Nat.unpair n).1 (Nat.unpair n).2, fun n => (Nat.unpair n).1,
    fun n => hpa _ _, fun n => hbase _ _, fun n => rfl, ?_, ?_⟩
  · intro n x hx u hu
    exact ⟨hu.2, hshape (Nat.unpair n).1 (Nat.unpair n).2 x hx u hu⟩
  · rw [MeasureTheory.ae_all_iff]
    intro r
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ ⋃ k, G r k from by
      rw [MeasureTheory.ae_iff]; exact hcov r] with x hx
    obtain ⟨k, hk⟩ : ∃ k, x ∈ G r k := by simpa only [Set.mem_iUnion] using hx
    exact ⟨Nat.pair r k, by simp [Nat.unpair_pair], by simpa only [Nat.unpair_pair] using hk⟩

/-! ## 3. The per-point globalisation -/

/-- **Per-point globalisation.**  At a fixed point `x` at which the shape proportionality holds
for all multipliers `u ∈ D`, the left translate of `ν x` by any `v ∈ D` is a multiple of `ν x`. -/
theorem exists_scaling_of_shape_propor (hUcl : IsClosed (U : Set SL3))
    (hL : IsLeafwise μ U ν X') {x : X3} (hxX' : x ∈ X')
    {D : Set SL3} (hDU : D ⊆ (U : Set SL3)) (hDsymm : ∀ u : SL3, u ∈ D → u⁻¹ ∈ D)
    {Z G : ℕ → Set X3} {m : ℕ → MeasurableSpace X3} {R : ℕ → ℕ}
    (hGZ : ∀ n, G n ⊆ Z n)
    (hshape : ∀ n, ∀ y ∈ G n, V ((R n : ℝ) + 2) ∩ (U : Set SL3) ⊆ shape (m n) U y)
    (hcover : ∀ r : ℕ, ∃ n, R n = r ∧ x ∈ G n)
    (hprop : ∀ u ∈ D, ∀ n, x ∈ Z n → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
      ((ν x).map (fun g => u⁻¹ * g)).restrict (shape (m n) U x)
        = κ • (ν x).restrict (shape (m n) U x))
    {v : SL3} (hv : v ∈ D) :
    ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ (ν x).map (fun g => v * g) = κ • ν x := by
  classical
  choose nf hnf using hcover
  have hnfZ : ∀ r : ℕ, x ∈ Z (nf r) := fun r => hGZ _ (hnf r).2
  have hnfT : ∀ r : ℕ, V ((r : ℝ) + 2) ∩ (U : Set SL3) ⊆ shape (m (nf r)) U x := by
    intro r
    have h := hshape (nf r) x (hnf r).2
    have hcast : ((R (nf r) : ℝ)) = (r : ℝ) := by exact_mod_cast (hnf r).1
    rw [hcast] at h
    exact h
  have hv' : v⁻¹ ∈ D := hDsymm v hv
  have hcf : ∀ r : ℕ, ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ((ν x).map (fun g : SL3 => v * g)).restrict (shape (m (nf r)) U x)
        = c • (ν x).restrict (shape (m (nf r)) U x) := by
    intro r
    obtain ⟨c, hc0, hct, hc⟩ := hprop v⁻¹ hv' (nf r) (hnfZ r)
    rw [inv_inv] at hc
    exact ⟨c, hc0, hct, hc⟩
  choose cf hcf0 hcft hcfA using hcf
  -- the constants agree, compared on `Box1 U`
  have hbox : ∀ r : ℕ, Box1 U ⊆ shape (m (nf r)) U x := by
    intro r g hg
    exact hnfT r ⟨Work.EKLRelCross.Box1_subset_V (U := U) (R := (r : ℝ) + 2)
      (by have h : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r; linarith) hg, hg.1⟩
  have hboxmeas : MeasurableSet (Box1 U) := Work.EKLC7.measurableSet_Box1 hUcl
  have hcf_eq : ∀ r r' : ℕ, cf r = cf r' := by
    have key : ∀ r r' : ℕ, r ≤ r' → cf r = cf r' := by
      intro r r' _
      have h1 : ((ν x).map (fun g : SL3 => v * g)) (Box1 U) = cf r * (ν x) (Box1 U) := by
        have h := congrArg (fun (s : MeasureTheory.Measure SL3) => s (Box1 U)) (hcfA r)
        simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply hboxmeas,
          smul_eq_mul] at h
        rwa [Set.inter_eq_left.mpr (hbox r)] at h
      have h2 : ((ν x).map (fun g : SL3 => v * g)) (Box1 U) = cf r' * (ν x) (Box1 U) := by
        have h := congrArg (fun (s : MeasureTheory.Measure SL3) => s (Box1 U)) (hcfA r')
        simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply hboxmeas,
          smul_eq_mul] at h
        rwa [Set.inter_eq_left.mpr (hbox r')] at h
      rw [hL.normalised x hxX', mul_one] at h1
      rw [hL.normalised x hxX', mul_one] at h2
      rw [h1] at h2
      exact h2
    intro r r'
    rcases le_total r r' with h | h
    · exact key r r' h
    · exact (key r' r h).symm
  -- continuity from below
  have hAcar : ((ν x).map (fun g : SL3 => v * g)) (U : Set SL3)ᶜ = 0 :=
    map_mul_left_carried hUcl (hL.carried x hxX') (hDU hv)
  have hunion : ∀ C : Set SL3, MeasurableSet C →
      ((ν x).map (fun g : SL3 => v * g)) C = cf 0 * (ν x) C := by
    intro C hC
    have hmono : Monotone (fun r : ℕ => C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3))) := by
      intro r r' hrr'
      have hc : ((r : ℝ) + 2) ≤ ((r' : ℝ) + 2) := by
        have h : r + 2 ≤ r' + 2 := Nat.add_le_add_right hrr' 2
        exact_mod_cast h
      exact Set.inter_subset_inter subset_rfl (Set.inter_subset_inter (V_mono hc) subset_rfl)
    have hUi : (⋃ r : ℕ, C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3))) = C ∩ (U : Set SL3) := by
      refine le_antisymm (Set.iUnion_subset fun r => ?_) ?_
      · intro y hy
        exact ⟨hy.1, hy.2.2⟩
      · rintro y ⟨hyC, hyU⟩
        obtain ⟨r, hr⟩ := exists_mem_V_add y 2
        exact Set.mem_iUnion.mpr ⟨r, ⟨hyC, hr, hyU⟩⟩
    have hstep : ∀ r : ℕ, ((ν x).map (fun g : SL3 => v * g))
          (C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3)))
        = cf 0 * (ν x) (C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3))) := by
      intro r
      have hT : MeasurableSet (V ((r : ℝ) + 2) ∩ (U : Set SL3)) :=
        (Lemmas.V_open_one _ (by positivity)).1.measurableSet.inter hUcl.measurableSet
      have h := congrArg (fun (s : MeasureTheory.Measure SL3) =>
        s (C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3)))) (hcfA r)
      simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply
        (hC.inter hT), smul_eq_mul] at h
      rw [show C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3)) ∩ shape (m (nf r)) U x
          = C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3)) from
        Set.inter_eq_left.mpr (Set.inter_subset_right.trans (hnfT r))] at h
      rw [h, hcf_eq r 0]
    have hA1 : ((ν x).map (fun g : SL3 => v * g)) (C ∩ (U : Set SL3))
        = ⨆ r : ℕ, ((ν x).map (fun g : SL3 => v * g))
            (C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3))) := by
      rw [← hUi]
      exact Monotone.measure_iUnion hmono
    have hν1 : (ν x) (C ∩ (U : Set SL3))
        = ⨆ r : ℕ, (ν x) (C ∩ (V ((r : ℝ) + 2) ∩ (U : Set SL3))) := by
      rw [← hUi]
      exact Monotone.measure_iUnion hmono
    rw [← measure_inter_U_eq_carried hAcar C, ← measure_inter_U_eq_carried (hL.carried x hxX') C,
      hA1, hν1, ENNReal.mul_iSup]
    exact iSup_congr hstep
  refine ⟨cf 0, hcf0 0, hcft 0, ?_⟩
  refine MeasureTheory.Measure.ext fun C hC => ?_
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  exact hunion C hC

/-! ## 4. The endgame -/

/-- **The endgame.**  From the shape proportionality (for a countable dense set `D ⊆ U` of
multipliers) and the closedness of the quasi-invariance group of `ν x`, deduce the a.e.
right-`U`-invariance of the leafwise measures, i.e. clause (U4) in the direction
`IsUInvariant μ U ⟹ a.e. Haar`. -/
theorem aeHaar_of_shape_propor (h2 : P_X3) (μ : MeasureTheory.Measure X3)
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup SL3) (hU : IsHoro U)
    (t0 : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1))
    (ν : X3 → MeasureTheory.Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hinv : IsUInvariant μ U)
    {Z G : ℕ → Set X3} {m : ℕ → MeasurableSpace X3} {R : ℕ → ℕ}
    (hGZ : ∀ n, G n ⊆ Z n)
    (hshapeF : ∀ n, ∀ y ∈ G n, V ((R n : ℝ) + 2) ∩ (U : Set SL3) ⊆ shape (m n) U y)
    (hcover : ∀ᵐ x ∂μ, ∀ r : ℕ, ∃ n, R n = r ∧ x ∈ G n)
    (D : Set SL3) (hDU : D ⊆ (U : Set SL3)) (hDc : D.Countable)
    (hDsymm : ∀ u : SL3, u ∈ D → u⁻¹ ∈ D) (hDdense : closure D = (U : Set SL3))
    (hprop : ∀ᵐ x ∂μ, x ∈ X' → ∀ u ∈ D, u • x ∈ X' → ∀ n, x ∈ Z n →
      ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
        ((ν x).map (fun g => u⁻¹ * g)).restrict (shape (m n) U x)
          = κ • (ν x).restrict (shape (m n) U x))
    (hclosed : ∀ x ∈ X', IsClosed (QuasiInvLeft (ν x))) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x := by
  have hU5 := Work.EKLRelCross.leafwise_propor h2 μ U hU t0 hmp hcontr ν X' hL
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff, show {x : X3 | ¬ x ∈ X'} = X'ᶜ from rfl]
    exact hL.conull
  have hux : ∀ᵐ x ∂μ, ∀ v ∈ D, v • x ∈ X' := by
    haveI : Countable ↥D := hDc.to_subtype
    have h2' : ∀ᵐ x ∂μ, ∀ v : ↥D, (v : SL3) • x ∈ X' :=
      MeasureTheory.ae_all_iff.mpr
        (fun v => ae_smul_mem_of_invariant hinv (hDU v.2) hL.meas_dom hL.conull)
    simpa only [Subtype.forall] using h2'
  filter_upwards [hX'ae, hux, hcover, hprop, hU5] with x hxX' huxv hcov hpropx h5
  have hne : ν x ≠ 0 := by
    intro h0
    have h1 := hL.normalised x hxX'
    rw [h0] at h1
    simp at h1
  have hscal : ∀ v ∈ D, ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
      (ν x).map (fun g => v * g) = κ • ν x := by
    intro v hv
    exact exists_scaling_of_shape_propor hU.1 hL hxX' hDU hDsymm hGZ hshapeF
      (fun r => hcov r) (fun u hu n hn => hpropx hxX' u hu (huxv u hu) n hn) hv
  have hQI : ∀ v ∈ U, ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧
      (ν x).map (fun g => v * g) = κ • ν x := by
    have hsub : closure D ⊆ QuasiInvLeft (ν x) := closure_minimal hscal (hclosed x hxX')
    have hUsub : (U : Set SL3) ⊆ QuasiInvLeft (ν x) := by
      rw [← hDdense]
      exact hsub
    intro v hv
    exact hUsub hv
  intro u hu
  obtain ⟨c, hc0, hct, hc⟩ := Work.EKLRelCross.rightQuasiInv U hU (ν x)
    (hL.radon x hxX') (hL.carried x hxX') hne hQI u hu
  exact h5 u hu c hc

end

end Work.EKLC7Ae
