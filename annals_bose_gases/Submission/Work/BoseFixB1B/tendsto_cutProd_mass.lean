import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.sectorCountBoxAux
import Submission.Work.BoseFixB1S.boxPoincareBox3
import Submission.Work.BoseFixB3.QBop.ae_abox_slot_notMem_frontier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.tendsto_cutProd_mass`

The **mass convergence** along the smooth approximants of the sharp box state:

    ∫_{abox k L}(∏ᵢγ_δ(xᵢ))²ψ² → ∫_{abox k L}(1_{B(u)^k}ψ)²   as δ → 0⁺,

for any family `γ_δ` of smooth cutoffs of the sliding box `B(u) = dlBox L d u`
(`Work.BoseFixB1B.IsCutFamily`).

The convergence is *pointwise* off a null set.  Say that the configuration `x` is **good** if
either every coordinate lies *strictly* inside both cubes of the sliding box (`Intra`), or some
coordinate lies outside the box; the complement consists of configurations with a coordinate on a
*face* of one of the two cubes, i.e. a finite union of coordinate hyperplanes, which is Lebesgue-null
(`Work.BoseFixB1S.volume_coord_eq` + `Work.BoseFixB3.QBop.volume_preimage_slot_null`).  On the good
set the approximants are *eventually* equal to the sharp state:

* if some coordinate is outside the box, the cutoff vanishes there (its support is inside the box)
  and the sharp state vanishes too;
* if all coordinates are strictly inside, the box margin of each coordinate is positive, so for
  small `δ` the cutoff is `1` on every coordinate, and the sharp state is the fibre.

The convergence of the integrals then follows by dominated convergence
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) with the constant bound `Cb²`
on the (finite-measure) box.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge Work.PerSector Work.SlotWord

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The good configurations -/

/-- **Strictly inside the sliding box**: both coordinate inequalities of the two cubes are strict. -/
def Intra (L d : ℝ) (u y : E3) : Prop :=
  (∀ m : Fin 3, |y m| < L / 2) ∧ (∀ m : Fin 3, |(y - (L * d) • u) m| < L * d / 2)

/-- **Good configurations** for the mass convergence: all coordinates strictly inside the box, or
some coordinate outside the box.  Configurations with a coordinate on a face of one of the two cubes
are the bad ones, and they form a Lebesgue-null set. -/
def GoodCollar (L d : ℝ) (u : E3) {k : ℕ} (x : X k) : Prop :=
  (∀ i : Fin k, Intra L d u (x i)) ∨ (∃ i : Fin k, x i ∉ dlBox L d u)

/-- A point strictly inside the box has *positive* box margin. -/
theorem boxMargin_pos_of_intra {L d : ℝ} {u y : E3} (h : Intra L d u y) :
    0 < boxMargin L d u y := by
  rw [boxMargin]
  refine lt_min ?_ ?_
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun m _ => by linarith [h.1 m])
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun m _ => by linarith [h.2 m])

/-! ## 2. The pointwise convergence on a good configuration -/

/-- **The pointwise convergence at a good configuration.**  Good configurations are points where the
approximant is *eventually* equal to the sharp state, hence `(∏ᵢγ_δ(xᵢ)ψ(x))² → (1_{B^k}ψ(x))²`
as `δ → 0⁺`. -/
theorem tendsto_cutProd_sq_pointwise {k : ℕ} {L d : ℝ} {u : E3} {ψ : X k → ℝ}
    {γ : ℝ → E3 → ℝ} (hγsupp : ∀ δ : ℝ, 0 < δ → ∀ y, γ δ y ≠ 0 → y ∈ dlBox L d u)
    (hγone : ∀ δ : ℝ, 0 < δ → ∀ y, boxMargin L d u y ≥ δ → γ δ y = 1)
    {x : X k} (hG : GoodCollar L d u x) :
    Filter.Tendsto (fun δ : ℝ => (cutProd (γ δ) ψ x) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((sharpBoxState (dlBox L d u) ψ x) ^ 2)) := by
  have heq : (fun δ : ℝ => (cutProd (γ δ) ψ x) ^ 2)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (sharpBoxState (dlBox L d u) ψ x) ^ 2) := by
    rcases hG with hG | hG
    · -- all coordinates strictly inside the box: eventually the cutoff is `1` everywhere
      have hbm : ∀ i : Fin k, 0 < boxMargin L d u (x i) := fun i => boxMargin_pos_of_intra (hG i)
      have hmem : ∀ i : Fin k, x i ∈ dlBox L d u := by
        intro i
        by_contra hni
        have hle := boxMargin_nonpos_of_notMem (ℓ := L) (d := d) (u := u) hni
        linarith [hbm i]
      have hev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, γ δ (x i) = 1 := by
        rw [Filter.eventually_all]
        intro i
        filter_upwards [Filter.Eventually.filter_mono
            (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0)) (Iio_mem_nhds (hbm i)),
          self_mem_nhdsWithin] with δ hlt hpos
        exact hγone δ hpos (x i) hlt.le
      filter_upwards [hev] with δ hδ
      have hprod : (∏ i : Fin k, γ δ (x i)) = 1 := Finset.prod_eq_one (fun i _ => hδ i)
      have hsharp : sharpBoxState (dlBox L d u) ψ x = ψ x :=
        sharpState_eq_self_of_mem (fun i => hmem i)
      rw [cutProd_apply, hprod, one_mul, hsharp]
    · -- some coordinate outside the box: both states vanish
      obtain ⟨i, hi⟩ := hG
      filter_upwards [self_mem_nhdsWithin] with δ hpos
      have hγ0 : γ δ (x i) = 0 := by
        by_contra hne
        exact hi (hγsupp δ hpos (x i) hne)
      have hcut0 : cutProd (γ δ) ψ x = 0 := by
        rw [cutProd_apply, Finset.prod_eq_zero (Finset.mem_univ i) hγ0, zero_mul]
      have hsh0 : sharpBoxState (dlBox L d u) ψ x = 0 :=
        sharpState_eq_zero_of_notMem (fun h => hi (h i))
      rw [hcut0, hsh0]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-! ## 3. The bad set is null -/

/-- **The complement of the good set is Lebesgue-null**: it consists of configurations some of whose
coordinates lie on a face of one of the two cubes, i.e. a finite union of coordinate hyperplanes. -/
theorem volume_goodCollar_compl {k : ℕ} {L d : ℝ} (u : E3) :
    (volume : Measure (X k)) {x : X k | ¬ GoodCollar L d u x} = 0 := by
  classical
  set T : Set (X k) := ⋃ p : Fin k × Fin 3,
    ({x : X k | x p.1 p.2 = L / 2} ∪ {x : X k | x p.1 p.2 = -(L / 2)}
      ∪ {x : X k | x p.1 p.2 = L * d / 2 + ((L * d) • u) p.2}
      ∪ {x : X k | x p.1 p.2 = -(L * d / 2) + ((L * d) • u) p.2}) with hT
  have hsub : {x : X k | ¬ GoodCollar L d u x} ⊆ T := by
    intro x hx
    rw [Set.mem_setOf_eq, GoodCollar, not_or] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [not_forall] at h1
    obtain ⟨i, hi⟩ := h1
    have hmem : x i ∈ dlBox L d u := by
      by_contra hni
      exact h2 ⟨i, hni⟩
    obtain ⟨hac, hsh⟩ := (mem_dlBox_iff L d u (x i)).mp hmem
    rw [mem_acube_iff] at hac hsh
    rw [Intra, not_and_or] at hi
    rcases hi with hi | hi
    · rw [not_forall] at hi
      obtain ⟨m, hm⟩ := hi
      rw [not_lt] at hm
      have hle : |(x i).ofLp m| ≤ L / 2 :=
        abs_le.mpr ⟨by linarith [(hac m).1], (hac m).2⟩
      have heq : |(x i).ofLp m| = L / 2 := le_antisymm hle hm
      refine Set.mem_iUnion.mpr ⟨(i, m), ?_⟩
      rw [Set.mem_union, Set.mem_union, Set.mem_union]
      rcases abs_choice ((x i).ofLp m) with h | h
      · exact Or.inl (Or.inl (Or.inl (show (x i).ofLp m = L / 2 from by linarith)))
      · exact Or.inl (Or.inl (Or.inr (show (x i).ofLp m = -(L / 2) from by linarith)))
    · rw [not_forall] at hi
      obtain ⟨m, hm⟩ := hi
      rw [not_lt] at hm
      have hle : |(x i - (L * d) • u).ofLp m| ≤ L * d / 2 :=
        abs_le.mpr ⟨by linarith [(hsh m).1], (hsh m).2⟩
      have heq : |(x i - (L * d) • u).ofLp m| = L * d / 2 := le_antisymm hle hm
      have hcoord : (x i - (L * d) • u).ofLp m
          = (x i).ofLp m - ((L * d) • u).ofLp m := by simp
      rw [hcoord] at heq
      refine Set.mem_iUnion.mpr ⟨(i, m), ?_⟩
      rw [Set.mem_union, Set.mem_union, Set.mem_union]
      rcases abs_choice ((x i).ofLp m - ((L * d) • u).ofLp m) with h | h
      · exact Or.inl (Or.inr (show (x i).ofLp m
          = L * d / 2 + ((L * d) • u).ofLp m from by linarith))
      · exact Or.inr (show (x i).ofLp m
          = -(L * d / 2) + ((L * d) • u).ofLp m from by linarith)
  refine measure_mono_null hsub ?_
  rw [hT]
  refine measure_iUnion_null fun p => ?_
  refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
  · simpa using Work.BoseFixB3.QBop.volume_preimage_slot_null (N := k) p.1
      (Work.BoseFixB1S.volume_coord_eq p.2 (L / 2))
  · simpa using Work.BoseFixB3.QBop.volume_preimage_slot_null (N := k) p.1
      (Work.BoseFixB1S.volume_coord_eq p.2 (-(L / 2)))
  · simpa using Work.BoseFixB3.QBop.volume_preimage_slot_null (N := k) p.1
      (Work.BoseFixB1S.volume_coord_eq p.2 (L * d / 2 + ((L * d) • u) p.2))
  · simpa using Work.BoseFixB3.QBop.volume_preimage_slot_null (N := k) p.1
      (Work.BoseFixB1S.volume_coord_eq p.2 (-(L * d / 2) + ((L * d) • u) p.2))

/-! ## 4. The mass convergence -/

theorem tendsto_cutProd_mass {k : ℕ} {L d : ℝ} {u : E3}
    {ψ : X k → ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ}
    (hL : 0 < L) (hd : 0 < d) (hcut : IsCutFamily L d u K γ)
    (hψ : Continuous ψ) :
    Filter.Tendsto
      (fun δ : ℝ => ∫ x in abox k L, (cutProd (γ δ) ψ x) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in abox k L, (sharpBoxState (dlBox L d u) ψ x) ^ 2)) := by
  classical
  obtain ⟨hK0, hcutδ⟩ := hcut
  obtain ⟨Cb, hCb⟩ := (abox_compact k hL).exists_bound_of_continuousOn hψ.continuousOn
  set Cb' : ℝ := max Cb 0 with hCb'def
  have hCb'0 : 0 ≤ Cb' := le_max_right _ _
  have hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb' := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hCb x hx) (le_max_left _ _)
  have haboxm : MeasurableSet (abox k L) := (abox_isClosed k L).measurableSet
  haveI hfin : IsFiniteMeasure ((volume : Measure (X k)).restrict (abox k L)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (abox_compact k hL).measure_lt_top)
  have hγsupp : ∀ δ : ℝ, 0 < δ → ∀ y, γ δ y ≠ 0 → y ∈ dlBox L d u := fun δ hδ y hy =>
    (hcutδ δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hy))
  have hγone : ∀ δ : ℝ, 0 < δ → ∀ y, boxMargin L d u y ≥ δ → γ δ y = 1 :=
    fun δ hδ => (hcutδ δ hδ).2.2.2.1
  have hnull : (volume : Measure (X k)) {x : X k | ¬ GoodCollar L d u x} = 0 :=
    volume_goodCollar_compl (k := k) (L := L) (d := d) u
  have hae : ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)), GoodCollar L d u x := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) hnull.le) bot_le
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (X k)).restrict (abox k L))
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun δ x => (cutProd (γ δ) ψ x) ^ 2)
    (f := fun x => (sharpBoxState (dlBox L d u) ψ x) ^ 2)
    (bound := fun _ => Cb' ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Continuous.aestronglyMeasurable ?_
    have hprod : Continuous (fun x : X k => ∏ i : Fin k, γ δ (x i)) :=
      continuous_finsetProd (Finset.univ : Finset (Fin k))
        (fun i _ => (hcutδ δ hδ).1.continuous.comp (continuous_apply i))
    exact (hprod.mul hψ).pow 2
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem haboxm] with x hx
    have h01 : ∀ y, 0 ≤ γ δ y ∧ γ δ y ≤ 1 := (hcutδ δ hδ).2.2.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hprod : 0 ≤ ∏ i : Fin k, γ δ (x i) := Finset.prod_nonneg (fun i _ => (h01 (x i)).1)
    have hprod1 : (∏ i : Fin k, γ δ (x i)) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => (h01 (x i)).1) (fun i _ => (h01 (x i)).2)
    have hcutb : |cutProd (γ δ) ψ x| ≤ Cb' := by
      rw [cutProd_apply, abs_mul, abs_of_nonneg hprod]
      calc (∏ i : Fin k, γ δ (x i)) * |ψ x| ≤ 1 * Cb' :=
            mul_le_mul hprod1 (hψb x hx) (abs_nonneg _) zero_le_one
        _ = Cb' := one_mul Cb'
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (cutProd (γ δ) ψ x)) hcutb 2
  · exact integrable_const _
  · filter_upwards [hae] with x hx
    exact tendsto_cutProd_sq_pointwise hγsupp hγone hx

end Work.BoseFixB1B
