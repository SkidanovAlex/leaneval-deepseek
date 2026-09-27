import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.SupportFacts
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.Box1_Uij

/-!
# C7: the periods of the central leafwise measure are arbitrarily small

`Work.EKLC7.PeriodSmallIter`: given the commutator relation `CommRel2 νij νjk νik c` between the
leafwise measures of the three root groups of a Heisenberg configuration, together with
non-trivial points of the supports of `νij` (arbitrarily small ones, `u_ij(p)` with `p → 0`) and
of `νjk` (`u_jk(r)`, `r ≠ 0`), the central leafwise measure `νik` is invariant under right
translation by arbitrarily small non-trivial elements `u_ik(τ)` of `U_ik`.

The proof is a measure-theoretic "a.e. at a point of the support" argument; no regularity
(σ-finiteness, finiteness on compact sets) of the measures is used:

* `CommRel2` says that for `νij`-a.e. `x` and `νjk`-a.e. `y` the right translate of `νik` by the
  commutator `[x,y]` is proportional to `νik` with constant `c`;
* a null set is disjoint from every open set of positive measure, so the set of "good" `x` meets
  every neighbourhood of a point of the support of `νij`; likewise for `y`;
* taking `x` close to `u_ij(p₀)`, `p₀ ≠ 0` a small point of the support of `νij`, and `y` close
  to `u_jk(r)`, `r ≠ 0` a point of the support of `νjk`, the commutator is `[x,y] = u_ik(τ)` with
  `τ = p r` non-zero and `|τ| ≤ ε`;
* the "proportional implies equal" hypothesis (U5) for the group `U_ik` converts the
  proportionality into the invariance `νik · u_ik(τ) = νik`.

The two metric neighbourhoods used are the coordinate neighbourhoods
`{x | |p_ij(x) - p₀| < |p₀|/2}`, `{y | |r_jk(y) - r| < |r|/2}`; they are open because the matrix
entries are continuous, and they have positive measure because they contain points of the support.
-/

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- If two sets `A`, `C` are null for `μ` while `B` is not, then `B` meets the complement of
`A ∪ C`.  Only monotonicity and subadditivity of a measure are used, so no regularity hypothesis
on `μ` is needed. -/
lemma exists_mem_notMem_of_measure_eq_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A C B : Set α} (hA : μ A = 0) (hC : μ C = 0) (hB : μ B ≠ 0) :
    ∃ x ∈ B, x ∉ A ∧ x ∉ C := by
  by_contra h
  have h' : ∀ x, x ∈ B → x ∈ A ∨ x ∈ C := by
    intro x hxB
    by_contra hc
    rw [not_or] at hc
    exact h ⟨x, hxB, hc.1, hc.2⟩
  have hsub : B ⊆ A ∪ C := fun x hx => h' x hx
  have hle : μ B ≤ μ (A ∪ C) := measure_mono hsub
  have h0 : μ (A ∪ C) = 0 := by
    rw [measure_union_null_iff]
    exact ⟨hA, hC⟩
  exact hB (le_antisymm (h0 ▸ hle) (by simp))

/-- The `(i,j)`-entry of `u_ij(s)` is `s`. -/
lemma pcoord_uij {i j : Fin 3} (hij : i ≠ j) (s : ℝ) : pcoord i j (uij hij s) = s :=
  Work.EKLContract.Lemmas.uij_apply_self hij s

/-- The `(j,k)`-entry of `u_jk(s)` is `s`. -/
lemma rcoord_uij {j k : Fin 3} (hjk : j ≠ k) (s : ℝ) : rcoord j k (uij hjk s) = s :=
  Work.EKLContract.Lemmas.uij_apply_self hjk s

/-- **C7, the small-periods statement** (Pisa 9.11): from the commutator relation between the
three leafwise measures of a Heisenberg configuration, the small support points of `νij` and a
non-trivial support point of `νjk`, the central leafwise measure `νik` has non-trivial periods
`τ` of arbitrarily small modulus. -/
theorem PeriodSmallIter :
    ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik : Work.EKLC7.SLm) (c : ℝ),
      νij (Work.EKLContract.Uij hij)ᶜ = 0 → νjk (Work.EKLContract.Uij hjk)ᶜ = 0 →
      Work.EKLC7.CommRel2 νij νjk νik c →
      (∀ u ∈ Work.EKLContract.Uij hik, ∀ c' : ENNReal,
        MeasureTheory.Measure.map (fun g => g * u) νik = c' • νik →
        MeasureTheory.Measure.map (fun g => g * u) νik = νik) →
      (∀ ε : ℝ, 0 < ε → ∃ p : ℝ, p ≠ 0 ∧ |p| ≤ ε ∧
        Work.EKLContract.uij hij p ∈ (νij).support) →
      (∃ r : ℝ, r ≠ 0 ∧ Work.EKLContract.uij hjk r ∈ (νjk).support) →
      Work.EKLC7.SmallPeriods hik νik := by
  intro i j k hij hjk hik νij νjk νik c hcar_ij hcar_jk hcomm hprop hsmall hnonzero

  rw [SmallPeriods]
  intro ε hε
  obtain ⟨r, hrne, hrsupp⟩ := hnonzero
  have hrpos : 0 < |r| := abs_pos.mpr hrne
  have hbad : νij {x : SL3 | ¬ (∀ᵐ y ∂νjk,
      (νik).map (fun g => g * comm x y) = ENNReal.ofReal c • νik)} = 0 := by
    have h := hcomm
    simp only [CommRel2] at h
    rwa [ae_iff] at h
  set ρ : ℝ := ε / (8 * (|r| + 1)) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  obtain ⟨p₀, hp₀ne, hp₀le, hp₀supp⟩ := hsmall ρ hρpos
  have hp₀pos : 0 < |p₀| := abs_pos.mpr hp₀ne
  have hBxopen : IsOpen {x : SL3 | |pcoord i j x - p₀| < |p₀| / 2} := by
    have hEq : {x : SL3 | |pcoord i j x - p₀| < |p₀| / 2}
        = (fun x : SL3 => pcoord i j x) ⁻¹' Metric.ball p₀ (|p₀| / 2) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, Real.dist_eq]
    rw [hEq]
    exact (continuous_pcoord i j).isOpen_preimage _ Metric.isOpen_ball
  have hxstarB : (uij hij p₀) ∈ {x : SL3 | |pcoord i j x - p₀| < |p₀| / 2} := by
    simp only [Set.mem_ofPred_eq, pcoord_uij hij p₀, sub_self, abs_zero]
    linarith
  have hballx : 0 < νij {x : SL3 | |pcoord i j x - p₀| < |p₀| / 2} := by
    have hs := hp₀supp
    rw [Measure.support_eq_forall_isOpen (μ := νij)] at hs
    exact hs _ hxstarB hBxopen
  obtain ⟨x, hxB, hxbad, hxU⟩ :=
    exists_mem_notMem_of_measure_eq_zero νij hbad hcar_ij (ne_of_gt hballx)
  have hxU' : x ∈ (Uij hij : Set SL3) := by simpa using hxU
  have hinner : ∀ᵐ y ∂νjk, (νik).map (fun g => g * comm x y) = ENNReal.ofReal c • νik := by
    by_contra h
    exact hxbad h
  set p : ℝ := pcoord i j x with hpdef
  have hp_close : |p - p₀| < |p₀| / 2 := hxB
  have hp_ne : p ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hp_close
    linarith
  have hp_le : |p| ≤ 3 * |p₀| / 2 := by
    have habs : |p| ≤ |p - p₀| + |p₀| := by
      calc |p| = |(p - p₀) + p₀| := by ring_nf
        _ ≤ |p - p₀| + |p₀| := abs_add_le _ _
    linarith
  have hx_eq : uij hij p = x := by
    obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hij x).mp hxU'
    have hps : p = s := by
      rw [hpdef, ← hs]
      exact pcoord_uij hij s
    rw [hps, hs]
  have hbad_y : νjk {y : SL3 | ¬ ((νik).map (fun g => g * comm x y)
      = ENNReal.ofReal c • νik)} = 0 := by
    have h := hinner
    rwa [ae_iff] at h
  have hByopen : IsOpen {y : SL3 | |rcoord j k y - r| < |r| / 2} := by
    have hEq : {y : SL3 | |rcoord j k y - r| < |r| / 2}
        = (fun y : SL3 => rcoord j k y) ⁻¹' Metric.ball r (|r| / 2) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, Real.dist_eq]
    rw [hEq]
    exact (continuous_rcoord j k).isOpen_preimage _ Metric.isOpen_ball
  have hystarB : (uij hjk r) ∈ {y : SL3 | |rcoord j k y - r| < |r| / 2} := by
    simp only [Set.mem_ofPred_eq, rcoord_uij hjk r, sub_self, abs_zero]
    linarith
  have hbally : 0 < νjk {y : SL3 | |rcoord j k y - r| < |r| / 2} := by
    have hs := hrsupp
    rw [Measure.support_eq_forall_isOpen (μ := νjk)] at hs
    exact hs _ hystarB hByopen
  obtain ⟨y, hyB, hybad, hyU⟩ :=
    exists_mem_notMem_of_measure_eq_zero νjk hbad_y hcar_jk (ne_of_gt hbally)
  have hyU' : y ∈ (Uij hjk : Set SL3) := by simpa using hyU
  have hyM : (νik).map (fun g => g * comm x y) = ENNReal.ofReal c • νik := by
    by_contra h
    exact hybad h
  set rx : ℝ := rcoord j k y with hrxdef
  have hrx_close : |rx - r| < |r| / 2 := hyB
  have hrx_ne : rx ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hrx_close
    linarith
  have hrx_le : |rx| ≤ 3 * (|r| + 1) / 2 := by
    have habs : |rx| ≤ |rx - r| + |r| := by
      calc |rx| = |(rx - r) + r| := by ring_nf
        _ ≤ |rx - r| + |r| := abs_add_le _ _
    linarith
  have hy_eq : uij hjk rx = y := by
    obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hjk y).mp hyU'
    have hrs : rx = s := by
      rw [hrxdef, ← hs]
      exact rcoord_uij hjk s
    rw [hrs, hs]
  have hcomm_eq : comm x y = uij hik (p * rx) := by
    rw [← hx_eq, ← hy_eq, comm]
    exact uij_commutator hij hjk hik p rx
  have hprop_xy : (νik).map (fun g => g * uij hik (p * rx)) = ENNReal.ofReal c • νik := by
    rw [← hcomm_eq]
    exact hyM
  refine ⟨p * rx, mul_ne_zero hp_ne hrx_ne, ?_, ?_⟩
  · rw [abs_mul]
    have h1 : |p| ≤ 3 * |p₀| / 2 := hp_le
    have h2 : |rx| ≤ 3 * (|r| + 1) / 2 := hrx_le
    have hmul : |p₀| * (|r| + 1) ≤ ε / 8 := by
      rw [hρdef] at hp₀le
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (|r| + 1))] at hp₀le
      have h8 : |p₀| * (8 * (|r| + 1)) = 8 * (|p₀| * (|r| + 1)) := by ring
      rw [h8] at hp₀le
      linarith
    have hbd : (3 * |p₀| / 2) * (3 * (|r| + 1) / 2) = (9 / 4) * (|p₀| * (|r| + 1)) := by ring
    have hkey : (3 * |p₀| / 2) * (3 * (|r| + 1) / 2) ≤ ε := by
      rw [hbd]
      linarith
    exact le_trans (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) hkey
  · exact hprop (uij hik (p * rx)) (Subgroup.subset_closure ⟨p * rx, rfl⟩)
      (ENNReal.ofReal c) hprop_xy

end EKLC7


