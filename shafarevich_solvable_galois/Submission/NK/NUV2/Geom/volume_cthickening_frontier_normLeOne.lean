import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.NK.NUV2.Geom.volume_cthickening_levelSet_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Geom

set_option autoImplicit false
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Classical
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units.dirichletUnitTheorem
open NumberField.InfinitePlace

section Part1

variable {K : Type*} [Field K] [NumberField K]

/-- The linear map inverse to `x ↦ log ∘ expMapBasis` on the positive orthant: for `z : realSpace K`,
`LamInvL z` is the vector of coordinates of `(z w * mult w : ℝ)` in the basis `completeBasis K`.
It satisfies `expMapBasis (LamInvL z) w = Real.exp (z w)`. -/
noncomputable def LamInvL : realSpace K →ₗ[ℝ] realSpace K where
  toFun z := (completeBasis K).repr (fun w ↦ z w * (mult w : ℝ))
  map_add' z z' := by
    have h : (fun w ↦ (z + z') w * (mult w : ℝ))
        = (fun w ↦ z w * (mult w : ℝ)) + (fun w ↦ z' w * (mult w : ℝ)) := by
      ext w; simp [add_mul]
    rw [h, map_add]
    ext w
    simp
  map_smul' c z := by
    have h : (fun w ↦ (c • z) w * (mult w : ℝ))
        = c • (fun w ↦ z w * (mult w : ℝ)) := by
      ext w; simp [mul_assoc]
    rw [h, map_smul]
    ext w
    simp

/-- The map `x ↦ log ∘ (expMapBasis x)`. -/
noncomputable def LamLogFun (x : realSpace K) : realSpace K :=
  fun w ↦ ((completeBasis K).equivFun.symm x) w * (mult w : ℝ)⁻¹

/-- The coefficient of `x i` in `LamLogFun x w`. -/
noncomputable def nu (i w : InfinitePlace K) : ℝ := (completeBasis K) i w / (mult w : ℝ)


theorem expMapBasis_eq_exp (x : realSpace K) (w : InfinitePlace K) :
    expMapBasis x w = Real.exp (LamLogFun x w) := by
  rw [expMapBasis_apply, expMap_apply, LamLogFun, mul_comm]

theorem LamInvL_LamLogFun (x : realSpace K) : LamInvL (LamLogFun x) = x := by
  ext j
  have h1 : (fun w ↦ LamLogFun x w * (mult w : ℝ))
      = fun w ↦ ((completeBasis K).equivFun.symm x) w := by
    ext w
    simp only [LamLogFun]
    rw [mul_assoc, inv_mul_cancel₀ (InfinitePlace.mult_coe_ne_zero (w := w)), mul_one]
  have h2 : LamInvL (LamLogFun x) j
      = ((completeBasis K).repr ((completeBasis K).equivFun.symm x)) j := by
    simp only [LamInvL, LinearMap.coe_mk, AddHom.coe_mk, h1]
  rw [h2, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem expMapBasis_LamInvL (z : realSpace K) (w : InfinitePlace K) :
    expMapBasis (LamInvL z) w = Real.exp (z w) := by
  rw [expMapBasis_eq_exp, LamLogFun]
  have h : (completeBasis K).equivFun.symm (LamInvL z) = fun w ↦ z w * (mult w : ℝ) := by
    rw [show LamInvL z
        = ((completeBasis K).repr (fun w ↦ z w * (mult w : ℝ)) : realSpace K) from rfl,
      ← Module.Basis.equivFun_apply]
    exact LinearEquiv.symm_apply_apply _ _
  rw [h, mul_assoc, mul_inv_cancel₀ (InfinitePlace.mult_coe_ne_zero (w := w)), mul_one]

/-- The coordinate functionals of `LamInvL`. -/
noncomputable def lam (j : InfinitePlace K) : realSpace K →ₗ[ℝ] ℝ :=
  (LinearMap.proj j).comp LamInvL

theorem lam_LamLogFun (j : InfinitePlace K) (x : realSpace K) : lam j (LamLogFun x) = x j := by
  simp only [lam, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [LamInvL_LamLogFun]

theorem lam_ne_zero (j : InfinitePlace K) : lam j ≠ 0 := by
  intro h
  have h1 := lam_LamLogFun j (Pi.single j (1 : ℝ))
  rw [h] at h1
  simp only [LinearMap.zero_apply] at h1
  rw [Pi.single_eq_same] at h1
  exact one_ne_zero h1.symm

theorem LamLogFun_eq_sum' (x : realSpace K) (w : InfinitePlace K) :
    LamLogFun x w = ∑ i, x i * ((completeBasis K) i w / (mult w : ℝ)) := by
  rw [LamLogFun, Module.Basis.equivFun_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [div_eq_mul_inv]; ring

theorem LamLogFun_eq_sum (x : realSpace K) (w : InfinitePlace K) :
    LamLogFun x w = ∑ i, x i * nu i w := by
  rw [LamLogFun_eq_sum']
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [nu]

theorem nu_w₀ (w : InfinitePlace K) :
    (completeBasis K) w₀ w / (mult w : ℝ) = 1 := by
  rw [completeBasis_apply_of_eq]
  field_simp


/-- The set of points of `realSpace K` satisfying the coordinate bounds of `closure (paramSet K)`. -/
def InBox (x : realSpace K) : Prop := x w₀ ≤ 0 ∧ ∀ i ≠ w₀, 0 ≤ x i ∧ x i ≤ 1

theorem mem_closure_paramSet_iff {x : realSpace K} :
    x ∈ closure (paramSet K) ↔ InBox x := by
  rw [closure_paramSet, Set.mem_univ_pi]
  constructor
  · intro h
    refine ⟨?_, fun i hi ↦ ?_⟩
    · simpa using h w₀
    · simpa [hi] using h i
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = w₀
    · subst hi; simpa using h1
    · simpa [hi] using h2 i hi

theorem nu_w₀' (w : InfinitePlace K) : nu w₀ w = 1 := by
  rw [nu, completeBasis_apply_of_eq]
  exact div_self (InfinitePlace.mult_coe_ne_zero (w := w))

theorem LamLogFun_sub (x : realSpace K) (w k : InfinitePlace K) :
    LamLogFun x w - LamLogFun x k
      = ∑ i ∈ Finset.univ.erase w₀, x i * (nu i w - nu i k) := by
  have key : (∑ i : InfinitePlace K, (x i * nu i w - x i * nu i k))
      = ∑ i : InfinitePlace K, x i * (nu i w - nu i k) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  have hsplit : (∑ i : InfinitePlace K, x i * (nu i w - nu i k))
      = (∑ i ∈ Finset.univ.erase w₀, x i * (nu i w - nu i k))
        + x w₀ * (nu w₀ w - nu w₀ k) :=
    (Finset.sum_erase_add Finset.univ (fun i ↦ x i * (nu i w - nu i k))
      (Finset.mem_univ w₀)).symm
  rw [LamLogFun_eq_sum, LamLogFun_eq_sum, ← Finset.sum_sub_distrib, key, hsplit, nu_w₀', nu_w₀']
  ring

theorem exists_ratio_bound : ∃ Kb : ℝ, 1 ≤ Kb ∧ ∀ x : realSpace K, InBox x →
    ∀ w k : InfinitePlace K, LamLogFun x w - LamLogFun x k ≤ Real.log Kb := by
  classical
  let E : InfinitePlace K → InfinitePlace K → ℝ :=
    fun w k ↦ ∑ i ∈ Finset.univ.erase w₀, max 0 (nu i w - nu i k)
  have hEpos : ∀ w k : InfinitePlace K, 0 < Real.exp (E w k) := fun w k ↦ Real.exp_pos _
  refine ⟨∑ w : InfinitePlace K, ∑ k : InfinitePlace K, (1 + Real.exp (E w k)), ?_, ?_⟩
  · obtain ⟨w₁⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hw : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)),
        0 ≤ ∑ k : InfinitePlace K, (1 + Real.exp (E w k)) :=
      fun w _ ↦ Finset.sum_nonneg fun k _ ↦ by linarith [hEpos w k]
    have h1 := Finset.single_le_sum hw (Finset.mem_univ w₁)
    have h2 : (1 : ℝ) ≤ ∑ k : InfinitePlace K, (1 + Real.exp (E w₁ k)) := by
      have hpos : ∀ k ∈ (Finset.univ : Finset (InfinitePlace K)),
          0 ≤ 1 + Real.exp (E w₁ k) := fun k _ ↦ by linarith [hEpos w₁ k]
      have := Finset.single_le_sum hpos (Finset.mem_univ w₁)
      linarith [hEpos w₁ w₁]
    linarith
  · intro x hx w k
    rw [LamLogFun_sub]
    have hterm : ∀ i ∈ Finset.univ.erase w₀,
        x i * (nu i w - nu i k) ≤ max 0 (nu i w - nu i k) := by
      intro i hi
      have hi' : i ≠ w₀ := (Finset.mem_erase.mp hi).1
      obtain ⟨h0, h1⟩ := hx.2 i hi'
      by_cases h : 0 ≤ nu i w - nu i k
      · rw [max_eq_right h]; nlinarith [h0, h1]
      · rw [max_eq_left (not_le.mp h).le]; nlinarith [h0, not_le.mp h]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hEwk : (∑ i ∈ Finset.univ.erase w₀, max 0 (nu i w - nu i k)) = E w k := rfl
    rw [hEwk, ← Real.log_exp (E w k)]
    refine Real.log_le_log (hEpos w k) ?_
    have hw : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace K)),
        0 ≤ ∑ k' : InfinitePlace K, (1 + Real.exp (E w' k')) :=
      fun w' _ ↦ Finset.sum_nonneg fun k' _ ↦ by linarith [hEpos w' k']
    have h1 := Finset.single_le_sum hw (Finset.mem_univ w)
    have h2 : Real.exp (E w k) ≤ ∑ k' : InfinitePlace K, (1 + Real.exp (E w k')) := by
      have hpos : ∀ k' ∈ (Finset.univ : Finset (InfinitePlace K)),
          0 ≤ 1 + Real.exp (E w k') := fun k' _ ↦ by linarith [hEpos w k']
      have := Finset.single_le_sum hpos (Finset.mem_univ k)
      linarith [hEpos w k]
    linarith

theorem exists_upper_bound : ∃ Cb : ℝ, 0 < Cb ∧ ∀ x : realSpace K, InBox x →
    ∀ w : InfinitePlace K, LamLogFun x w ≤ Real.log Cb := by
  classical
  let F : InfinitePlace K → ℝ := fun w ↦ ∑ i ∈ Finset.univ.erase w₀, max 0 (nu i w)
  have hFpos : ∀ w : InfinitePlace K, 0 < Real.exp (F w) := fun w ↦ Real.exp_pos _
  refine ⟨∑ w : InfinitePlace K, (1 + Real.exp (F w)), ?_, ?_⟩
  · obtain ⟨w₁⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hpos : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)), 0 ≤ 1 + Real.exp (F w) :=
      fun w _ ↦ by linarith [hFpos w]
    have := Finset.single_le_sum hpos (Finset.mem_univ w₁)
    linarith [hFpos w₁]
  · intro x hx w
    have key : (∑ i : InfinitePlace K, x i * nu i w)
        = x w₀ + ∑ i ∈ Finset.univ.erase w₀, x i * nu i w := by
      have hsplit : (∑ i : InfinitePlace K, x i * nu i w)
          = (∑ i ∈ Finset.univ.erase w₀, x i * nu i w) + x w₀ * nu w₀ w :=
        (Finset.sum_erase_add Finset.univ (fun i ↦ x i * nu i w)
          (Finset.mem_univ w₀)).symm
      rw [hsplit, nu_w₀', mul_one]
      ring
    rw [LamLogFun_eq_sum, key]
    have hterm : ∀ i ∈ Finset.univ.erase w₀, x i * nu i w ≤ max 0 (nu i w) := by
      intro i hi
      have hi' : i ≠ w₀ := (Finset.mem_erase.mp hi).1
      obtain ⟨h0, h1⟩ := hx.2 i hi'
      by_cases h : 0 ≤ nu i w
      · rw [max_eq_right h]; nlinarith [h0, h1]
      · rw [max_eq_left (not_le.mp h).le]; nlinarith [h0, not_le.mp h]
    have hsum := Finset.sum_le_sum hterm
    have hFw : F w = ∑ i ∈ Finset.univ.erase w₀, max 0 (nu i w) := rfl
    calc x w₀ + ∑ i ∈ Finset.univ.erase w₀, x i * nu i w
        ≤ x w₀ + ∑ i ∈ Finset.univ.erase w₀, max 0 (nu i w) := by linarith
      _ ≤ F w := by rw [hFw]; linarith [hx.1]
      _ ≤ Real.log (∑ w : InfinitePlace K, (1 + Real.exp (F w))) := by
          rw [← Real.log_exp (F w)]
          refine Real.log_le_log (hFpos w) ?_
          have hpos : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace K)),
              0 ≤ 1 + Real.exp (F w') := fun w' _ ↦ by linarith [hFpos w']
          have := Finset.single_le_sum hpos (Finset.mem_univ w)
          linarith [hFpos w]

theorem LamLogFun_zero : LamLogFun (0 : realSpace K) = 0 := by
  ext w
  simp [LamLogFun]


theorem expMapBasis_phi (z : realSpace K) (hz : ∀ w, 0 < z w) :
    expMapBasis (LamInvL (fun w ↦ Real.log (z w))) = z := by
  ext w
  rw [expMapBasis_LamInvL, Real.exp_log (hz w)]

theorem continuousAt_phi {y : realSpace K} (hy : ∀ w, 0 < y w) :
    ContinuousAt (fun z : realSpace K ↦ LamInvL (fun w ↦ Real.log (z w))) y := by
  have h2 : ContinuousAt (fun z : realSpace K ↦ (fun w ↦ Real.log (z w))) y := by
    rw [continuousAt_pi]
    intro w
    exact (continuousAt_apply w y).log (ne_of_gt (hy w))
  exact (LinearMap.continuous_of_finiteDimensional LamInvL).continuousAt.comp h2

theorem closure_expMapBasis_paramSet_subset :
    closure (expMapBasis '' paramSet K) ⊆ expMapBasis '' closure (paramSet K) ∪ {0} := by
  intro y hy
  by_cases hpos : ∀ w, 0 < y w
  · left
    obtain ⟨u, huS, hutend⟩ := mem_closure_iff_seq_limit.mp hy
    have hupos : ∀ n w, 0 < u n w := by
      intro n w
      obtain ⟨x', -, hx'⟩ := huS n
      rw [← hx']
      exact expMapBasis_pos _ _
    refine ⟨LamInvL (fun w ↦ Real.log (y w)), ?_, expMapBasis_phi y hpos⟩
    refine mem_closure_iff_seq_limit.mpr
      ⟨fun n ↦ LamInvL (fun w ↦ Real.log (u n w)), fun n ↦ ?_, ?_⟩
    · obtain ⟨x', hx'mem, hx'val⟩ := huS n
      have h1 : LamInvL (fun w ↦ Real.log (u n w)) = x' :=
        injective_expMapBasis K (by rw [expMapBasis_phi (u n) (hupos n), hx'val])
      show LamInvL (fun w ↦ Real.log (u n w)) ∈ paramSet K
      rw [h1]
      exact hx'mem
    · exact (continuousAt_phi hpos).tendsto.comp hutend
  · right
    push_neg at hpos
    obtain ⟨w, hw⟩ := hpos
    obtain ⟨Kb, hKb1, hKb⟩ := exists_ratio_bound (K := K)
    obtain ⟨u, huS, hutend⟩ := mem_closure_iff_seq_limit.mp hy
    choose x hx using fun n ↦ huS n
    have hxmem : ∀ n, x n ∈ paramSet K := fun n ↦ (hx n).1
    have hxval : ∀ n, expMapBasis (x n) = u n := fun n ↦ (hx n).2
    have hxbox : ∀ n, InBox (x n) :=
      fun n ↦ mem_closure_paramSet_iff.mp (subset_closure (hxmem n))
    have hineq : ∀ n w', u n w' ≤ Kb * u n w := by
      intro n w'
      have h := hKb (x n) (hxbox n) w' w
      rw [← hxval n, expMapBasis_eq_exp, expMapBasis_eq_exp]
      calc Real.exp (LamLogFun (x n) w')
          ≤ Real.exp (LamLogFun (x n) w + Real.log Kb) := Real.exp_le_exp.mpr (by linarith)
        _ = Kb * Real.exp (LamLogFun (x n) w) := by
            rw [Real.exp_add, Real.exp_log (by linarith)]
            ring
    have hzero : ∀ w', y w' = 0 := by
      intro w'
      have ht1 : Filter.Tendsto (fun n ↦ u n w') Filter.atTop (nhds (y w')) :=
        (continuousAt_apply w' y).tendsto.comp hutend
      have ht2 : Filter.Tendsto (fun n ↦ Kb * u n w) Filter.atTop (nhds (Kb * y w)) :=
        tendsto_const_nhds.mul ((continuousAt_apply w y).tendsto.comp hutend)
      have hle : y w' ≤ Kb * y w :=
        le_of_tendsto_of_tendsto' ht1 ht2 fun n ↦ hineq n w'
      have hge : 0 ≤ y w' := by
        refine ge_of_tendsto ht1 (Filter.Eventually.of_forall fun n ↦ ?_)
        rw [← hxval n]
        exact (expMapBasis_pos (x n) w').le
      have hKb0 : 0 < Kb := by linarith
      have hle0 : Kb * y w ≤ 0 := by nlinarith
      exact le_antisymm (le_trans hle hle0) hge
    exact funext hzero

theorem interior_expMapBasis_paramSet :
    interior (expMapBasis '' paramSet K) = expMapBasis '' interior (paramSet K) := by
  refine subset_antisymm ?_ ?_
  · intro y hy
    have hyS : y ∈ expMapBasis '' paramSet K := interior_subset hy
    obtain ⟨x, hxmem, hxval⟩ := hyS
    refine ⟨x, ?_, hxval⟩
    have hpre : expMapBasis ⁻¹' (expMapBasis '' paramSet K) = paramSet K := by
      ext z
      constructor
      · rintro ⟨x', hx'mem, hx'val⟩
        rw [← injective_expMapBasis K hx'val]
        exact hx'mem
      · intro hz
        exact ⟨z, hz, rfl⟩
    have h1 : x ∈ expMapBasis ⁻¹' interior (expMapBasis '' paramSet K) := by
      show expMapBasis x ∈ interior (expMapBasis '' paramSet K)
      rw [hxval]; exact hy
    have h2 := preimage_interior_subset_interior_preimage (continuous_expMapBasis K) h1
    rwa [hpre] at h2
  · intro y hy
    obtain ⟨x, hxmem, hxval⟩ := hy
    have hopen : IsOpen (expMapBasis '' interior (paramSet K)) :=
      expMapBasis.isOpen_image_of_subset_source isOpen_interior
        (by rw [expMapBasis_source]; exact Set.subset_univ _)
    exact interior_maximal (Set.image_mono interior_subset) hopen ⟨x, hxmem, hxval⟩

theorem frontier_expMapBasis_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      (⋃ j : InfinitePlace K, (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 0}
        ∪ expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 1})) ∪ {0} := by
  intro y hy
  rw [frontier, Set.mem_sdiff] at hy
  obtain ⟨hycl, hyint⟩ := hy
  rcases closure_expMapBasis_paramSet_subset (K := K) hycl with ⟨x, hxmem, hxval⟩ | h0
  · have hxbox := mem_closure_paramSet_iff.mp hxmem
    have hxnotint : x ∉ interior (paramSet K) := by
      intro hxint
      exact hyint (by rw [← hxval, interior_expMapBasis_paramSet]; exact ⟨x, hxint, rfl⟩)
    have hx' : x w₀ = 0 ∨ ∃ i ≠ w₀, x i = 0 ∨ x i = 1 := by
      by_cases h1 : x w₀ = 0
      · exact Or.inl h1
      · right
        by_contra hcon
        push_neg at hcon
        exact hxnotint (by
          rw [interior_paramSet, Set.mem_univ_pi]
          intro i
          by_cases hi : i = w₀
          · subst hi
            simpa using lt_of_le_of_ne hxbox.1 h1
          · obtain ⟨h0, h1'⟩ := hxbox.2 i hi
            obtain ⟨hne0, hne1⟩ := hcon i hi
            simpa [hi] using ⟨lt_of_le_of_ne h0 (Ne.symm hne0), lt_of_le_of_ne h1' hne1⟩)
    rcases hx' with h0 | ⟨i, _, hi0 | hi1⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w₀, Or.inl ⟨x, ⟨hxmem, h0⟩, hxval⟩⟩)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, Or.inl ⟨x, ⟨hxmem, hi0⟩, hxval⟩⟩)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, Or.inr ⟨x, ⟨hxmem, hi1⟩, hxval⟩⟩)
  · exact Or.inr h0


theorem dist_normAtAllPlaces_le (a b : mixedSpace K) :
    dist (normAtAllPlaces a) (normAtAllPlaces b) ≤ dist a b := by
  rw [dist_pi_le_iff (by positivity)]
  intro w
  rw [Real.dist_eq]
  have h1 : |normAtPlace w a - normAtPlace w b| ≤ normAtPlace w (a - b) := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · have h := normAtPlace_add_le w (a - b) b
      have h' : normAtPlace w a ≤ normAtPlace w (a - b) + normAtPlace w b := by
        simpa only [sub_add_cancel] using h
      linarith
    · have h := normAtPlace_add_le w (b - a) a
      have h' : normAtPlace w b ≤ normAtPlace w (b - a) + normAtPlace w a := by
        simpa only [sub_add_cancel] using h
      have h2 : normAtPlace w (b - a) = normAtPlace w (a - b) := by
        rw [show b - a = -(a - b) by abel, normAtPlace_neg]
      linarith [h', h2.le, h2.ge]
  refine le_trans h1 ?_
  rw [dist_eq_norm]
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun v ↦ normAtPlace v (a - b)) (Finset.mem_univ w)

theorem frontier_normLeOne_subset :
    frontier (fundamentalCone.normLeOne K) ⊆
      normAtAllPlaces ⁻¹' frontier (expMapBasis '' paramSet K) := by
  intro z hz
  rw [frontier, Set.mem_sdiff] at hz
  obtain ⟨hzcl, hzint⟩ := hz
  rw [Set.mem_preimage]
  have hPS : fundamentalCone.normLeOne K = normAtAllPlaces ⁻¹' (expMapBasis '' paramSet K) :=
    normLeOne_eq_preimage K
  refine ⟨?_, ?_⟩
  · rw [hPS] at hzcl
    exact (continuous_normAtAllPlaces K).closure_preimage_subset _ hzcl
  · intro hmem
    apply hzint
    have h2 : normAtAllPlaces ⁻¹' interior (expMapBasis '' paramSet K)
        ⊆ interior (fundamentalCone.normLeOne K) := by
      rw [hPS]
      exact interior_maximal (Set.preimage_mono interior_subset)
        (isOpen_interior.preimage (continuous_normAtAllPlaces K))
    exact h2 hmem

theorem face_hyp (j : InfinitePlace K) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume (Metric.cthickening ε
          (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 0}))
        ≤ ENNReal.ofReal (c₀ * ε) ∧
       volume (Metric.cthickening ε
          (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 1}))
        ≤ ENNReal.ofReal (c₀ * ε)) := by
  obtain ⟨Kb, hKb1, hKb⟩ := exists_ratio_bound (K := K)
  obtain ⟨Cb, hCb0, hCb⟩ := exists_upper_bound (K := K)
  have hmain : ∀ t : ℝ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε
          (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = t}))
        ≤ ENNReal.ofReal (c₀ * ε) := by
    intro t
    refine volume_cthickening_levelSet_le (lam j) (lam_ne_zero j) t Kb Cb hKb1 hCb0
      (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = t}) ?_
    rintro y ⟨x, ⟨hxcl, hxj⟩, rfl⟩
    have hxbox : InBox x := mem_closure_paramSet_iff.mp hxcl
    refine ⟨fun w ↦ expMapBasis_pos x w, ?_, ?_, ?_⟩
    · intro w k
      have h := hKb x hxbox w k
      rw [expMapBasis_eq_exp, expMapBasis_eq_exp]
      calc Real.exp (LamLogFun x w) ≤ Real.exp (LamLogFun x k + Real.log Kb) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Kb * Real.exp (LamLogFun x k) := by
            rw [Real.exp_add, Real.exp_log (by linarith)]
            ring
    · intro w
      have h := hCb x hxbox w
      rw [expMapBasis_eq_exp]
      calc Real.exp (LamLogFun x w) ≤ Real.exp (Real.log Cb) := Real.exp_le_exp.mpr h
        _ = Cb := Real.exp_log (by linarith)
    · rw [show (fun w ↦ Real.log (expMapBasis x w)) = LamLogFun x from by
            ext w; rw [expMapBasis_eq_exp, Real.log_exp], lam_LamLogFun, hxj]
  obtain ⟨c0, hc0, h0⟩ := hmain 0
  obtain ⟨c1, hc1, h1⟩ := hmain 1
  refine ⟨max c0 c1, lt_max_of_lt_left hc0, fun ε hε hε1 ↦ ⟨?_, ?_⟩⟩
  · exact le_trans (h0 ε hε hε1) (ENNReal.ofReal_le_ofReal (by nlinarith [le_max_left c0 c1]))
  · exact le_trans (h1 ε hε hε1) (ENNReal.ofReal_le_ofReal (by nlinarith [le_max_right c0 c1]))

theorem expMapBasis_le_of_mem_closure {Cb : ℝ} (hCb0 : 0 < Cb)
    (hCb : ∀ x : realSpace K, InBox x → ∀ w : InfinitePlace K, LamLogFun x w ≤ Real.log Cb)
    {x : realSpace K} (hx : x ∈ closure (paramSet K)) (w : InfinitePlace K) :
    expMapBasis x w ≤ Cb := by
  rw [expMapBasis_eq_exp]
  calc Real.exp (LamLogFun x w) ≤ Real.exp (Real.log Cb) :=
        Real.exp_le_exp.mpr (hCb x (mem_closure_paramSet_iff.mp hx) w)
    _ = Cb := Real.exp_log hCb0

theorem isBounded_image_closure_paramSet :
    Bornology.IsBounded (expMapBasis '' closure (paramSet K) ∪ {(0 : realSpace K)}) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_upper_bound (K := K)
  refine isBounded_iff_forall_norm_le.mpr ⟨max Cb 1, fun y hy ↦ ?_⟩
  rcases hy with ⟨x, hx, rfl⟩ | hy
  · rw [pi_norm_le_iff_of_nonempty]
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (expMapBasis_pos x w).le]
    exact le_trans (expMapBasis_le_of_mem_closure hCb0 hCb hx w) (le_max_left _ _)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    simp only [norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

end Part1

open MeasureTheory NumberField NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem in
theorem volume_cthickening_frontier_normLeOne (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε (frontier (fundamentalCone.normLeOne K)))
        ≤ ENNReal.ofReal (c * ε) := by
  classical
  obtain ⟨Rb, hRb0, hRb⟩ : ∃ Rb : ℝ, 0 < Rb ∧
      ∀ z ∈ Metric.cthickening (1 : ℝ) (frontier (fundamentalCone.normLeOne K)), ‖z‖ ≤ Rb := by
    have hbdd : Bornology.IsBounded (frontier (fundamentalCone.normLeOne K)) :=
      ((isBounded_normLeOne K).closure).subset frontier_subset_closure
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hbdd.cthickening (δ := 1))
    exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun z hz ↦ le_trans (hC z hz) (le_max_left _ _)⟩
  choose cf hcf using fun j : InfinitePlace K ↦ face_hyp (K := K) j
  have hcfpos : ∀ j : InfinitePlace K, 0 < cf j := fun j ↦ (hcf j).1
  have hsumpos : 0 < ∑ j : InfinitePlace K, cf j := by
    obtain ⟨j₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    exact Finset.sum_pos (fun j _ ↦ hcfpos j) ⟨j₀, Finset.mem_univ j₀⟩
  have hQ : (0:ℝ) ≤ 2 * (∑ j : InfinitePlace K, cf j) + 2 ^ Fintype.card (InfinitePlace K) := by
    have := hsumpos; positivity
  refine ⟨2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * Rb ^ nrComplexPlaces K *
      (2 * (∑ j, cf j) + 2 ^ Fintype.card (InfinitePlace K)), ?_, ?_⟩
  · have h1 : (0:ℝ) < 2 ^ nrRealPlaces K := by positivity
    have h2 : (0:ℝ) < (2 * Real.pi) ^ nrComplexPlaces K := by positivity
    have h3 : (0:ℝ) < Rb ^ nrComplexPlaces K := by positivity
    have h4 : (0:ℝ) < 2 * (∑ j, cf j) + 2 ^ Fintype.card (InfinitePlace K) := by
      have := hsumpos; positivity
    exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4
  · intro ε hε0 hε1
    have hQ2 : (0:ℝ) ≤ 2 * (∑ j : InfinitePlace K, cf j) * ε := by
      have := hsumpos; have := hε0; positivity
    set V : Set (realSpace K) := Metric.cthickening ε
        (frontier (expMapBasis '' paramSet K) ∪ {(0 : realSpace K)}) ∩
        {y : realSpace K | (∀ w, 0 ≤ y w) ∧ (∀ w, y w ≤ Rb)} with hVdef
    have hsub : Metric.cthickening ε (frontier (fundamentalCone.normLeOne K))
        ⊆ normAtAllPlaces ⁻¹' V := by
      intro z hz
      rw [Set.mem_preimage, hVdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
      have hbdd : Bornology.IsBounded (frontier (fundamentalCone.normLeOne K)) :=
        ((isBounded_normLeOne K).closure).subset frontier_subset_closure
      have hcompact : IsCompact (frontier (fundamentalCone.normLeOne K)) :=
        Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_frontier, hbdd⟩
      have hz1 : z ∈ Metric.cthickening (1 : ℝ) (frontier (fundamentalCone.normLeOne K)) :=
        Metric.cthickening_mono hε1 _ hz
      rw [hcompact.cthickening_eq_biUnion_closedBall hε0.le] at hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨y, hyE, hzy⟩ := hz
      have hzy' : dist z y ≤ ε := Metric.mem_closedBall.mp hzy
      refine ⟨?_, fun w ↦ normAtAllPlaces_nonneg z w, fun w ↦ ?_⟩
      · exact Metric.mem_cthickening_of_dist_le (normAtAllPlaces z) (normAtAllPlaces y) ε _
          (Set.mem_union_left _ (frontier_normLeOne_subset (K := K) hyE))
          (le_trans (dist_normAtAllPlaces_le z y) hzy')
      · have h1 : normAtAllPlaces z w ≤ ‖z‖ := by
          rw [norm_eq_sup'_normAtPlace]
          exact Finset.le_sup' (fun v ↦ normAtPlace v z) (Finset.mem_univ w)
        exact le_trans h1 (hRb z hz1)
    have hmeasV : MeasurableSet V := by
      rw [hVdef, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
      refine MeasurableSet.inter Metric.isClosed_cthickening.measurableSet ?_
      exact (MeasurableSet.iInter fun w ↦
          measurableSet_le measurable_const (measurable_pi_apply w)).inter
        (MeasurableSet.iInter fun w ↦
          measurableSet_le (measurable_pi_apply w) measurable_const)
    have hstable : normAtAllPlaces ⁻¹' (normAtAllPlaces '' (normAtAllPlaces ⁻¹' V))
        = normAtAllPlaces ⁻¹' V := by
      rw [Set.image_preimage_eq_inter_range, Set.preimage_inter, Set.preimage_range,
        Set.inter_univ]
    have hmeaspre : MeasurableSet (normAtAllPlaces ⁻¹' V) :=
      hmeasV.preimage (continuous_normAtAllPlaces K).measurable
    have himg : normAtAllPlaces '' (normAtAllPlaces ⁻¹' V) = V := by
      rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
      intro y hy
      exact ⟨mixedSpaceOfRealSpace y, by
        rw [normAtAllPlaces_mixedSpaceOfRealSpace (fun w ↦ hy.2.1 w)]⟩
    have hvolformula := volume_eq_two_pow_mul_two_pi_pow_mul_integral (K := K)
      (A := normAtAllPlaces ⁻¹' V) hstable hmeaspre
    have hvol1 : volume (Metric.cthickening ε (frontier (fundamentalCone.normLeOne K)))
        ≤ 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
          ∫⁻ y in V, ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (y w.1) := by
      refine le_trans (measure_mono hsub) ?_
      rw [hvolformula, himg]
    have hint : ∫⁻ y in V, ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (y w.1)
        ≤ ENNReal.ofReal (Rb ^ nrComplexPlaces K) * volume V := by
      refine le_trans (setLIntegral_mono measurable_const ?_)
        (le_of_eq (setLIntegral_const V _))
      intro y hy
      calc ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (y w.1)
          ≤ ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal Rb :=
            Finset.prod_le_prod₀ (fun w _ ↦ (zero_le : (0:ENNReal) ≤ ENNReal.ofReal (y w.1)))
              (fun w _ ↦ ENNReal.ofReal_le_ofReal (hy.2.2 w.1))
        _ = ENNReal.ofReal (Rb ^ nrComplexPlaces K) := by
            rw [Finset.prod_const, ← ENNReal.ofReal_pow hRb0.le]
            rfl
    have hclosedS : IsClosed (frontier (expMapBasis '' paramSet K) ∪ {(0 : realSpace K)}) :=
      isClosed_frontier.union isClosed_singleton
    have hbddS : Bornology.IsBounded
        (frontier (expMapBasis '' paramSet K) ∪ {(0 : realSpace K)}) :=
      Bornology.IsBounded.subset (isBounded_image_closure_paramSet (K := K))
        (Set.union_subset
          (frontier_subset_closure.trans (closure_expMapBasis_paramSet_subset (K := K)))
          (by rintro x rfl; exact Set.mem_union_right _ rfl))
    have hcompactS : IsCompact (frontier (expMapBasis '' paramSet K) ∪ {(0 : realSpace K)}) :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosedS, hbddS⟩
    have hcover : V ⊆ (⋃ j : InfinitePlace K,
        (Metric.cthickening ε
            (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 0}) ∪
          Metric.cthickening ε
            (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 1}))) ∪
        Metric.cthickening ε ({(0 : realSpace K)} : Set (realSpace K)) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [hcompactS.cthickening_eq_biUnion_closedBall hε0.le] at hy1
      simp only [Set.mem_iUnion, exists_prop] at hy1
      obtain ⟨w, hwE, hyw⟩ := hy1
      have hyw' : dist y w ≤ ε := Metric.mem_closedBall.mp hyw
      by_cases hwF : w ∈ frontier (expMapBasis '' paramSet K)
      · rcases frontier_expMapBasis_paramSet_subset (K := K) hwF with hj | hw0
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hj
          rcases hj with hj | hj
          · exact Or.inl (Set.mem_iUnion.mpr ⟨j, Or.inl
              (Metric.mem_cthickening_of_dist_le y w ε _ hj hyw')⟩)
          · exact Or.inl (Set.mem_iUnion.mpr ⟨j, Or.inr
              (Metric.mem_cthickening_of_dist_le y w ε _ hj hyw')⟩)
        · exact Or.inr (hw0 ▸ Metric.mem_cthickening_of_dist_le y w ε _
            (Set.mem_singleton w) hyw')
      · have hw0 : w = 0 := by
          rcases hwE with h | h
          · exact absurd h hwF
          · simpa using h
        exact Or.inr (hw0 ▸ Metric.mem_cthickening_of_dist_le y w ε _
          (Set.mem_singleton w) hyw')
    have hvolV : volume V ≤
        (∑ j : InfinitePlace K,
          (volume (Metric.cthickening ε
              (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 0})) +
           volume (Metric.cthickening ε
              (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 1})))) +
        volume (Metric.cthickening ε ({(0 : realSpace K)} : Set (realSpace K))) := by
      refine le_trans (measure_mono hcover) ?_
      refine le_trans (measure_union_le _ _) ?_
      refine le_trans (add_le_add (measure_iUnion_le _) le_rfl) ?_
      rw [tsum_fintype]
      exact add_le_add (Finset.sum_le_sum fun j _ ↦ measure_union_le _ _) le_rfl
    have hY0b : volume (Metric.cthickening ε ({(0 : realSpace K)} : Set (realSpace K)))
        ≤ ENNReal.ofReal (2 ^ Fintype.card (InfinitePlace K) * ε) := by
      rw [Metric.cthickening_singleton _ hε0.le]
      have hball : Metric.closedBall (0 : realSpace K) ε
          = Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Icc (-ε) ε) := by
        ext y
        rw [Metric.mem_closedBall, dist_pi_le_iff hε0.le, Set.mem_univ_pi]
        exact forall_congr' fun w ↦ by
          simp only [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le, Set.mem_Icc]
      rw [hball, volume_pi, Measure.pi_pi]
      simp only [Real.volume_Icc, sub_neg_eq_add]
      rw [Finset.prod_const, ← two_mul (ε : ℝ),
        ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * ε)]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨j₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
      have hcard : 1 ≤ Fintype.card (InfinitePlace K) :=
        Fintype.card_pos_iff.mpr ⟨j₀⟩
      calc (2 * ε) ^ Fintype.card (InfinitePlace K)
          = 2 ^ Fintype.card (InfinitePlace K) * ε ^ Fintype.card (InfinitePlace K) :=
            mul_pow _ _ _
        _ ≤ 2 ^ Fintype.card (InfinitePlace K) * ε := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            simpa using pow_le_pow_of_le_one hε0.le hε1 hcard
    have hboundV : volume V ≤ ENNReal.ofReal
        ((2 * (∑ j : InfinitePlace K, cf j) + 2 ^ Fintype.card (InfinitePlace K)) * ε) := by
      refine le_trans hvolV ?_
      have hXb : ∀ j : InfinitePlace K,
          volume (Metric.cthickening ε
              (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 0}))
            ≤ ENNReal.ofReal (cf j * ε) := fun j ↦ ((hcf j).2 ε hε0 hε1).1
      have hYb : ∀ j : InfinitePlace K,
          volume (Metric.cthickening ε
              (expMapBasis '' {x : realSpace K | x ∈ closure (paramSet K) ∧ x j = 1}))
            ≤ ENNReal.ofReal (cf j * ε) := fun j ↦ ((hcf j).2 ε hε0 hε1).2
      have hstep : ∀ j : InfinitePlace K,
          ENNReal.ofReal (cf j * ε) + ENNReal.ofReal (cf j * ε)
            = ENNReal.ofReal (2 * (cf j * ε)) := by
        intro j
        rw [← ENNReal.ofReal_add (by nlinarith [hcfpos j, hε0]) (by nlinarith [hcfpos j, hε0])]
        ring_nf
      have hq : ∀ j : InfinitePlace K, 0 ≤ 2 * (cf j * ε) :=
        fun j ↦ by nlinarith [hcfpos j, hε0]
      have hsum2 : (∑ j : InfinitePlace K, 2 * (cf j * ε)) = 2 * (∑ j, cf j) * ε := by
        rw [Finset.sum_congr rfl (fun j _ ↦ by ring : ∀ j ∈ Finset.univ,
          2 * (cf j * ε) = (2 * ε) * cf j)]
        rw [← Finset.mul_sum]
        ring
      refine le_trans (add_le_add (Finset.sum_le_sum fun j _ ↦ add_le_add (hXb j) (hYb j)) hY0b) ?_
      rw [Finset.sum_congr rfl fun j _ ↦ hstep j]
      rw [← ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (InfinitePlace K)))
        (f := fun j ↦ 2 * (cf j * ε)) (fun j _ ↦ hq j)]
      rw [hsum2]
      rw [← ENNReal.ofReal_add hQ2 (by positivity)]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hnorm : ∀ a b c d e : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → 0 ≤ e →
        ENNReal.ofReal a * ENNReal.ofReal b *
            (ENNReal.ofReal c * (ENNReal.ofReal d * ENNReal.ofReal e))
          = ENNReal.ofReal (a * b * c * d * e) := by
      intro a b c d e ha hb hc hd he
      rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_mul ha,
        ← ENNReal.ofReal_mul (mul_nonneg ha hb)]
      ring_nf
    refine le_trans hvol1 ?_
    calc 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
          ∫⁻ y in V, ∏ w : {w : InfinitePlace K // w.IsComplex}, ENNReal.ofReal (y w.1)
        ≤ 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
            (ENNReal.ofReal (Rb ^ nrComplexPlaces K) * volume V) :=
          mul_le_mul_right hint _
      _ ≤ 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
            (ENNReal.ofReal (Rb ^ nrComplexPlaces K) * ENNReal.ofReal
              ((2 * (∑ j : InfinitePlace K, cf j) + 2 ^ Fintype.card (InfinitePlace K)) * ε)) :=
          mul_le_mul_right (mul_le_mul_right hboundV _) _
      _ = ENNReal.ofReal ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
            Rb ^ nrComplexPlaces K *
            (2 * (∑ j : InfinitePlace K, cf j) + 2 ^ Fintype.card (InfinitePlace K))) * ε) := by
          rw [show (2 : ENNReal) ^ nrRealPlaces K =
                ENNReal.ofReal ((2 : ℝ) ^ nrRealPlaces K) by
              rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
                ← ENNReal.ofReal_pow (n := nrRealPlaces K) (by norm_num : (0:ℝ) ≤ (2:ℝ))],
            show ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K =
                ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) by
              rw [← ENNReal.ofReal_pow (by nlinarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)],
            show ENNReal.ofReal ((2 * (∑ j : InfinitePlace K, cf j)
                  + 2 ^ Fintype.card (InfinitePlace K)) * ε)
                = ENNReal.ofReal (2 * (∑ j : InfinitePlace K, cf j)
                    + 2 ^ Fintype.card (InfinitePlace K)) * ENNReal.ofReal ε by
              rw [ENNReal.ofReal_mul hQ],
            hnorm _ _ _ _ _ (by positivity) (by positivity)
              (by positivity) hQ hε0.le]

end NK.NUV2.Geom
