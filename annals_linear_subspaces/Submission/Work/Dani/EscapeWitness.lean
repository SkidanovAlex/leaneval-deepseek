import Mathlib
import ChallengeDeps
import Submission.Work.Dani.EscapeConvert
import Submission.Work.Dani.EscapeMeasure
import Submission.Work.Dani.EscapeGlueEps
import Submission.Work.Dani.OrthoRep
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Bridge.Challenge

/-!
# The witness plane of conjunct 2: chart facts and the escape assembly

This file turns a "good matrix" `c : Fin ℓ → Fin (d−ℓ) → ℝ` (in the unit box, with no rational
point on `graphPlane c`, and with only finitely many bad integer times at every rate `ε > 0`)
into the witness required by `Submission.EscapeGlueEps.conjunct2_of_witness_eps`:

* the plane `x = graphPlane c` has dimension `ℓ` and meets `ℤᵈ` only in `0`
  (`finrank_graphPlane`, `graphPlane_inf_intPoints_eq_bot`),
* hence every rational `k`-plane is at positive distance from `x`
  (`dist_pos_of_inf_intPoints_eq_bot`),
* and the escape hypothesis `∀ ε > 0, ∃ T, ∀ t ≥ T, e^{−εt} ≤ λ₁(a_t s_x ℤᵈ)` holds
  (`escape_of_absent`), by the conversion `EscapeConvert.bad_imp_event` and the bridge
  `EscapeMetric.successiveMinimum_ge_of_no_bad`.

Module `Submission.Work.Dani.EscapeWitness`, namespace `Submission.EscapeWitness`.
-/

noncomputable section

open LinearSubspaces Module Real MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Submission.EscapeWitness

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

open Submission.EscapeMetric

/-! ### The graph plane: injectivity, dimension, and the integer meet -/

lemma graphLinearMap_injective (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) :
    Function.Injective (graphLinearMap l hld c) := by
  intro a b hab
  have hab' : graphVec l hld c a = graphVec l hld c b := hab
  funext i
  have h1 : graphVec l hld c a (headIdx l hld i) = graphVec l hld c b (headIdx l hld i) := by
    rw [hab']
  rwa [Submission.EscapeConvert.graphVec_apply_head,
    Submission.EscapeConvert.graphVec_apply_head] at h1

lemma finrank_graphPlane (l : ℕ) (hld : l < d) (c : Fin l → Fin (d - l) → ℝ) :
    Module.finrank ℝ (graphPlane l hld c) = l := by
  have hker : LinearMap.ker (graphLinearMap l hld c) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (graphLinearMap_injective l hld c)
  have h := LinearMap.finrank_range_add_finrank_ker (graphLinearMap l hld c)
  rw [hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
  exact h

/-- **The graph plane has no nonzero integer point** when the matrix `c` is such that
`∑_i aᵢ c_{ij} = b_j` has no non-trivial integer solution. -/
theorem graphPlane_no_intPoint {l : ℕ} (hld : l < d)
    (c : Fin l → Fin (d - l) → ℝ)
    (hno : ¬ ∃ a : Fin l → ℤ, (∃ i, a i ≠ 0) ∧ ∃ b : Fin (d - l) → ℤ,
      ∀ j, (∑ i, (a i : ℝ) * c i j) = (b j : ℝ)) :
    ∀ n : ℝᵈ, n ∈ intPoints (d := d) → n ≠ 0 → n ∉ graphPlane l hld c := by
  classical
  rintro n hnZ hn0 hnx
  obtain ⟨a, ha⟩ := hnx
  have ha' : graphVec l hld c a = n := ha
  have ha0 : a ≠ 0 := by
    intro h0
    exact hn0 (by rw [← ha', h0, Submission.EscapeConvert.graphVec_zero])
  choose aZ haZ using fun i : Fin l =>
    Submission.EscapeGlue.intPoints_coord_int n hnZ (headIdx l hld i)
  choose bZ hbZ using fun j : Fin (d - l) =>
    Submission.EscapeGlue.intPoints_coord_int n hnZ (tailIdx l hld j)
  have hhead : ∀ i, (aZ i : ℝ) = a i := by
    intro i
    rw [← haZ i, ← ha']
    exact Submission.EscapeConvert.graphVec_apply_head l hld c a i
  have htail : ∀ j, (∑ i, (aZ i : ℝ) * c i j) = (bZ j : ℝ) := by
    intro j
    have hzw : graphVec l hld c (fun i => (aZ i : ℝ)) = n := by
      rw [← ha']
      congr 1
      exact funext fun i => hhead i
    rw [show (∑ i, (aZ i : ℝ) * c i j) = cComb l c (fun i => (aZ i : ℝ)) j from rfl,
      ← Submission.EscapeConvert.graphVec_apply_tail l hld c (fun i => (aZ i : ℝ)) j, hzw,
      hbZ j]
  refine hno ⟨aZ, ?_, bZ, htail⟩
  by_contra hc
  refine ha0 (funext fun i => ?_)
  have hzi : aZ i = 0 := not_not.mp (not_exists.mp hc i)
  rw [← hhead i, hzi]
  norm_num

/-! ### The box bound on the slope mass -/

lemma cterm_le_of_box {l : ℕ} {c : Fin l → Fin (d - l) → ℝ}
    (hbox : ∀ i j, c i j ∈ Set.Ico (0:ℝ) 1) :
    Submission.EscapeConvert.cterm l c ≤ (l : ℝ) * ((d - l : ℕ) : ℝ) := by
  have h1 : ∀ j : Fin (d - l), ∑ i, (c i j) ^ 2 ≤ (l : ℝ) := by
    intro j
    calc ∑ i : Fin l, (c i j) ^ 2 ≤ ∑ _ : Fin l, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hbox i j
          rw [Set.mem_Ico] at h
          nlinarith [h.1, h.2]
      _ = (l : ℝ) := by simp
  calc Submission.EscapeConvert.cterm l c = ∑ j, ∑ i, (c i j) ^ 2 := rfl
    _ ≤ ∑ _ : Fin (d - l), (l : ℝ) := Finset.sum_le_sum fun j _ => h1 j
    _ = ((d - l : ℕ) : ℝ) * (l : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (l : ℝ) * ((d - l : ℕ) : ℝ) := by ring

lemma sqrt_cterm_le_angleConst {l : ℕ} {c : Fin l → Fin (d - l) → ℝ}
    (hbox : ∀ i j, c i j ∈ Set.Ico (0:ℝ) 1) :
    Real.sqrt (2 + Submission.EscapeConvert.cterm l c) ≤
      Submission.EscapeMeasure.angleConst l (d - l) := by
  rw [Submission.EscapeMeasure.angleConst]
  refine Real.sqrt_le_sqrt ?_
  have h := cterm_le_of_box (d := d) hbox
  have hnn : (0 : ℝ) ≤ (l : ℝ) * ((d - l : ℕ) : ℝ) := by positivity
  linarith

/-! ### Positivity of the distance to rational subspaces -/

/-- If `x` meets `ℤᵈ` only in `0`, then every rational `k`-plane (`k ≥ 1`) is at positive
distance from `x`. -/
theorem dist_pos_of_no_intPoint {k l : ℕ} (hk1 : 1 ≤ k)
    {v x : Submodule ℝ ℝᵈ} (hvk : Module.finrank ℝ v = k) (hxl : Module.finrank ℝ x = l)
    (hkl : k ≤ l) (hsep : ∀ n : ℝᵈ, n ∈ intPoints (d := d) → n ≠ 0 → n ∉ x)
    (hv : IsRational v) :
    0 < distSubspaces v x := by
  classical
  by_contra hnot
  have hle : distSubspaces v x ≤ 0 := le_of_not_gt hnot
  have hfr : Module.finrank ℝ v ≤ Module.finrank ℝ x := by rw [hvk, hxl]; exact hkl
  have hvne : v ≠ ⊥ := by
    intro h; rw [h] at hvk; simp at hvk; omega
  have hxne : x ≠ ⊥ := by
    intro h; rw [h] at hxl; simp at hxl; omega
  have hres : Submission.ProjectionDistance.planeResidual v x ≤ 0 := by
    rw [← Submission.Bridge.distSubspaces_eq_planeResidual_of_le v x hfr hvne hxne]
    exact hle
  have hvx : v ≤ x := Submission.EscapeGlue.le_of_planeResidual_le_zero hres
  have hrank : Module.finrank ℤ (intPointsSubspace v) = k := by
    rw [ZLattice.rank ℝ, hvk]
  have hnt : Nontrivial (intPointsSubspace v) :=
    Module.nontrivial_of_finrank_pos (R := ℤ) (by rw [hrank]; omega)
  haveI := hnt
  obtain ⟨y, hy0⟩ := exists_ne (0 : intPointsSubspace v)
  have hyv : ((y : intPointsSubspace v) : v) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hyE : (((y : intPointsSubspace v) : v) : ℝᵈ) ≠ 0 := fun h => hyv (Subtype.ext h)
  exact hsep _ (y : intPointsSubspace v).2 hyE (hvx ((y : intPointsSubspace v).1.2))


/-! ### The escape assembly -/

/-- **Zero escape rate from the absence of bad integer times.**  If the matrix `c` (in the unit
box) has only finitely many bad integer times at every rate `ε > 0`, then the plane
`x = graphPlane c` (with orthogonal representative `s`) has zero escape rate. -/
theorem escape_of_absent {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (x : Submodule ℝ ℝᵈ) (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (hs : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) l)
    (c : Fin l → Fin (d - l) → ℝ) (hx : x = graphPlane l hld c)
    (hbox : ∀ i j, c i j ∈ Set.Ico (0:ℝ) 1)
    {ε₀ : ℝ} (hε₀0 : 0 < ε₀) (hε₀l : ε₀ ≤ 1 / (l : ℝ))
    (habsent : ∃ N : ℕ, ∀ n ≥ N,
      Submission.EscapeMeasure.rateD l (d - l) ε₀ n ≤ 1 / 2 ∧
      c ∉ Submission.EscapeMeasure.badEvent l (d - l)
        (Submission.EscapeMeasure.rateA l ε₀ n)
        (Submission.EscapeMeasure.rateD l (d - l) ε₀ n))
    {ε : ℝ} (_hε : 0 < ε) (hε₀ε : ε₀ ≤ ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Real.exp (-(ε * t)) ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum
        (Submission.ImageLattice.imageSpan (Submission.EscapeGlue.flowMap (d := d) l s t)) 1 := by
  obtain ⟨N, hN⟩ := habsent
  refine ⟨max (N : ℝ) 1, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans zero_le_one (le_trans (le_max_right (N : ℝ) 1) ht)
  have htN : (N : ℝ) ≤ t := le_trans (le_max_left (N : ℝ) 1) ht
  refine Submission.EscapeMetric.successiveMinimum_ge_of_no_bad hld s x hs ?_
  intro n hnmem hn0
  by_contra hcon
  push Not at hcon
  obtain ⟨hb1, hb2⟩ := max_lt_iff.mp hcon
  set n' : ℕ := Nat.floor t with hn'def
  have hn'2 : (n' : ℝ) ≤ t := by rw [hn'def]; exact Nat.floor_le ht0
  have hn'1 : t < (n' : ℝ) + 1 := by rw [hn'def]; exact Nat.lt_floor_add_one t
  have hn'N : N ≤ n' := by
    rw [hn'def]
    exact (Nat.le_floor_iff ht0).mpr htN
  obtain ⟨hδ1, hcnot⟩ := hN n' hn'N
  -- weaken the real bad event at rate `ε` to rate `ε₀ ≤ ε`
  have hb1' : Real.exp (-t / (l : ℝ)) *
      ‖((graphPlane l hld c).starProjection n : ℝᵈ)‖ < Real.exp (-(ε₀ * t)) := by
    have h := hb1
    rw [hx] at h
    refine lt_of_lt_of_le h ?_
    exact Real.exp_le_exp.mpr (by nlinarith [ht0, hε₀ε])
  have hb2' : Real.exp (t / ((d : ℝ) - (l : ℝ))) *
      ‖(((graphPlane l hld c)ᗮ).starProjection n : ℝᵈ)‖ < Real.exp (-(ε₀ * t)) := by
    have h := hb2
    rw [hx] at h
    refine lt_of_lt_of_le h ?_
    exact Real.exp_le_exp.mpr (by nlinarith [ht0, hε₀ε])
  have hA : 2 * Real.exp (t * (1 / (l : ℝ) - ε₀)) ≤
      Submission.EscapeMeasure.rateA l ε₀ n' := by
    rw [Submission.EscapeMeasure.rateA]
    have hc0 : 0 ≤ 1 / (l : ℝ) - ε₀ := by
      have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
      have h1 : 0 < 1 / (l : ℝ) := by positivity
      linarith
    have h1 : t * (1 / (l : ℝ) - ε₀) ≤ ((n' : ℝ) + 1) * (1 / (l : ℝ) - ε₀) :=
      mul_le_mul_of_nonneg_right hn'1.le hc0
    have h4 := Real.exp_le_exp.mpr h1
    linarith
  have hδ : Real.sqrt (2 + Submission.EscapeConvert.cterm l c) *
      Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε₀))) ≤
      Submission.EscapeMeasure.rateD l (d - l) ε₀ n' := by
    have hC := sqrt_cterm_le_angleConst (d := d) hbox
    have hDnn : (0 : ℝ) ≤ Submission.EscapeMeasure.angleConst l (d - l) := Real.sqrt_nonneg _
    have hexp_le : Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε₀))) ≤
        Real.exp (-((n' : ℝ) * (1 / ((d - l : ℕ) : ℝ) + ε₀))) := by
      have hcast : ((d - l : ℕ) : ℝ) = (d : ℝ) - (l : ℝ) := Nat.cast_sub (le_of_lt hld)
      rw [hcast]
      refine Real.exp_le_exp.mpr ?_
      have hdl : (0 : ℝ) < (d : ℝ) - (l : ℝ) := by
        have hlt : (l : ℝ) < (d : ℝ) := by exact_mod_cast hld
        linarith
      have hB : 0 ≤ 1 / ((d : ℝ) - (l : ℝ)) + ε₀ := by
        have hp : 0 < 1 / ((d : ℝ) - (l : ℝ)) := by positivity
        linarith
      have h1 : (n' : ℝ) * (1 / ((d : ℝ) - (l : ℝ)) + ε₀) ≤
          t * (1 / ((d : ℝ) - (l : ℝ)) + ε₀) :=
        mul_le_mul_of_nonneg_right hn'2 hB
      linarith
    rw [Submission.EscapeMeasure.rateD]
    calc Real.sqrt (2 + Submission.EscapeConvert.cterm l c) *
          Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε₀)))
        ≤ Submission.EscapeMeasure.angleConst l (d - l) *
          Real.exp (-(t * (1 / ((d : ℝ) - (l : ℝ)) + ε₀))) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ Submission.EscapeMeasure.angleConst l (d - l) *
          Real.exp (-((n' : ℝ) * (1 / ((d - l : ℕ) : ℝ) + ε₀))) :=
          mul_le_mul_of_nonneg_left hexp_le hDnn
  obtain ⟨a, ha0, hAle, b, hb⟩ := Submission.EscapeConvert.bad_imp_event l hl0 hld c ht0 hδ1
    hnmem hn0 hb1' hb2' hA hδ
  exact hcnot ⟨⟨a, ha0, hAle, b, hb⟩, hbox⟩

end Submission.EscapeWitness

end
