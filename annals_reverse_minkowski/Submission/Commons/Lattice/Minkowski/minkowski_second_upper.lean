import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.Minkowski.flag_basis
import Submission.Commons.Lattice.Minkowski.ball_packing
import Submission.Commons.Lattice.Minkowski.closedBall_packing
import Submission.Commons.Lattice.Minkowski.lower_product_bound
import Submission.Commons.Lattice.Minkowski.covolume_eq_of_eq
import Submission.Commons.Lattice.Minkowski.covolume_le_covolume_of_le
import Submission.Commons.Lattice.Counting.card_inter_closedBall_tendsto
import Submission.Commons.Lattice.Counting.lattice_count_int


namespace Commons.Lattice.Minkowski

noncomputable section
open MeasureTheory Set Metric Module Filter
open scoped ENNReal Pointwise Topology
open Commons.Lattice.SuccessiveMinima
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Development for Minkowski's second theorem (upper bound)

Strategy (Henk, *Successive minima and lattice points*, arXiv math/0204158, §4 / intro):
the theorem follows from a lattice-point counting bound with a factor `2^(d-1)` plus an
asymptotic lattice-count limit, valid in any finite-dimensional real inner-product space.
-/

/-- prefix span: span of the family `v : Fin d → E` restricted to indices `< t` -/
def PreSet {E : Type*} [AddCommGroup E] [Module ℝ E] (d : ℕ) (v : Fin d → E) (t : ℕ) :
    Submodule ℝ E :=
  Submodule.span ℝ {x | ∃ j : Fin d, j.val < t ∧ x = v j}

/-- A `ℝ`-linearly independent family in a real normed space is `ℤ`-linearly independent
(for the induced `ℤ`-module structure): integer relations are real relations. -/
lemma li_int_of_li_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : ι → E) (h : LinearIndependent ℝ f) : LinearIndependent ℤ f := by
  exact LinearIndependent.restrict_scalars (R := ℤ) (K := ℝ) (M := E) (v := f)
    (by
      intro a b hab
      have hab' : (a : ℝ) = (b : ℝ) := by simpa [zsmul_eq_mul] using hab
      exact_mod_cast hab') h

/-- Interior exclusion: exact realisers at their successive minima force every lattice point of
norm `< λ_ℓ` into the span of the first `ℓ-1` realisers (`PreSet v (ℓ-1)`). -/
lemma interior_exclusion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {d : ℕ} (hfin : Module.finrank ℤ L = d)
    (v : Fin d → L) (hvind : LinearIndependent ℝ (fun j : Fin d => (v j : E)))
    (hv : ∀ j : Fin d, ‖(v j : E)‖ ≤ successiveMinimum L (j.val + 1)) :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d → ∀ y : L,
      ‖(y : E)‖ < successiveMinimum L ℓ →
      (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) (ℓ - 1) := by
  classical
  -- exclusion at level 1: only the zero point is strictly inside the λ₁-ball
  have hlevel1 : ∀ h1 : 1 ≤ (1 : ℕ), ∀ hd : (1 : ℕ) ≤ d, ∀ y : L,
      ‖(y : E)‖ < successiveMinimum L 1 →
      (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) (1 - 1) := by
    intro h1 hd y hy
    have hyz : y = 0 := by
      by_contra hy0
      have hle := first_successiveMinimum_le_of_mem (L := L) y hy0
      linarith
    subst hyz
    simp [PreSet]
  -- successor step, assuming exclusion at level ℓ (ℓ ≥ 1)
  have hstep : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
      (∀ y : L, ‖(y : E)‖ < successiveMinimum L ℓ →
        (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) (ℓ - 1)) →
      ∀ h1 : 1 ≤ ℓ + 1, ∀ hd : ℓ + 1 ≤ d, ∀ y : L,
        ‖(y : E)‖ < successiveMinimum L (ℓ + 1) →
        (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) ((ℓ + 1) - 1) := by
    intro ℓ hℓ1 hℓd ih h1 hd y hy
    have hminus : (ℓ + 1) - 1 = ℓ := by omega
    change (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) ℓ
    by_contra hyF
    -- monotonicity λ_ℓ ≤ λ_{ℓ+1}
    have hmono : successiveMinimum L ℓ ≤ successiveMinimum L (ℓ + 1) := by
      refine successiveMinimum_mono (L := L) (i := ℓ) (j := ℓ + 1) (by omega) ?_
      rw [hfin]
      omega
    rcases lt_or_ge (successiveMinimum L ℓ) (successiveMinimum L (ℓ + 1)) with hlt | hge
    · -- λ_ℓ < λ_{ℓ+1} : build ℓ+1 independent points of norm < λ_{ℓ+1}
      let r : ℝ := max (successiveMinimum L ℓ) ‖(y : E)‖
      have hr : r < successiveMinimum L (ℓ + 1) := by
        dsimp [r]
        exact max_lt hlt hy
      have hlam0 : 0 ≤ successiveMinimum L ℓ := by
        exact successiveMinimum_nonneg L ℓ (by rw [hfin]; omega)
      have hr0 : 0 ≤ r := le_trans hlam0 (le_max_left _ _)
      let f : Fin (ℓ + 1) → L := fun j => if hjl : j.val < ℓ then
          v ⟨j.val, by omega⟩ else y
      have hpre_img_LI : LinearIndependent ℝ
          (fun j : Fin ℓ => ((v ⟨j.val, by omega⟩ : L) : E)) := by
        have hc : LinearIndependent ℝ (fun j : Fin ℓ => (v (Fin.castLEEmb (by omega : ℓ ≤ d) j) : E)) :=
          hvind.comp (Fin.castLEEmb (by omega : ℓ ≤ d)) (Fin.castLEEmb (by omega : ℓ ≤ d)).injective
        convert hc using 1
        ext j
        congr 1
      have hyF' : (y : E) ∉ Submodule.span ℝ
          (Set.range (fun j : Fin ℓ => ((v ⟨j.val, by omega⟩ : L) : E))) := by
        intro hmem
        have hset : {x : E | ∃ j : Fin d, j.val < ℓ ∧ x = (v j : E)} =
            Set.range (fun j : Fin ℓ => ((v ⟨j.val, by omega⟩ : L) : E)) := by
          ext x
          constructor
          · rintro ⟨j, hj, rfl⟩
            exact ⟨⟨j.val, by omega⟩, by simpa using hj⟩
          · rintro ⟨j, rfl⟩
            exact ⟨⟨j.val, by omega⟩, by simp, rfl⟩
        have hspan : PreSet d (fun j : Fin d => (v j : E)) ℓ =
            Submodule.span ℝ (Set.range (fun j : Fin ℓ => ((v ⟨j.val, by omega⟩ : L) : E))) := by
          dsimp [PreSet]
          rw [hset]
        exact hyF (by simpa [hspan] using hmem)
      have himg_LI : LinearIndependent ℝ (fun j : Fin (ℓ + 1) => ((f j : L) : E)) := by
        have hsnoc : (fun j : Fin (ℓ + 1) => ((f j : L) : E)) =
            Fin.snoc (fun j : Fin ℓ => ((v ⟨j.val, by omega⟩ : L) : E)) (y : E) := by
          ext j
          by_cases hj : j.val < ℓ
          · simp [f, hj, Fin.snoc]
          · have hjeq : j = Fin.last ℓ := by
              apply Fin.ext
              simp [Fin.last]
              omega
            simp [f, hj, hjeq, Fin.snoc]
        rw [hsnoc]
        rw [linearIndependent_finSnoc]
        exact ⟨hpre_img_LI, hyF'⟩
      have hf_img_int_LI : LinearIndependent ℤ (fun j : Fin (ℓ + 1) => ((f j : L) : E)) := by
        exact li_int_of_li_real (fun j : Fin (ℓ + 1) => ((f j : L) : E)) himg_LI
      have hnorm : ∀ j : Fin (ℓ + 1), ‖((f j : L) : E)‖ ≤ r := by
        intro j
        by_cases hj : j.val < ℓ
        · have hle : ‖((v ⟨j.val, by omega⟩ : L) : E)‖ ≤ successiveMinimum L ℓ := by
            have hb := hv ⟨j.val, by omega⟩
            refine le_trans hb ?_
            refine successiveMinimum_mono (L := L) (i := j.val + 1) (j := ℓ) ?_ ?_
            · omega
            · rw [hfin]
              omega
          rw [show ‖((f j : L) : E)‖ = ‖((v ⟨j.val, by omega⟩ : L) : E)‖ by simp [f, hj]]
          exact le_trans hle (le_max_left _ _)
        · have hjeq : j = Fin.last ℓ := by
            apply Fin.ext
            simp [Fin.last]
            omega
          rw [hjeq]
          simp [f]
          exact le_max_right (successiveMinimum L ℓ) ‖(y : E)‖
      have hcon : successiveMinimum L (ℓ + 1) ≤ r :=
        successiveMinimum_le_of_exists L (ℓ + 1) hr0 f hf_img_int_LI hnorm
      linarith
    · -- λ_{ℓ+1} ≤ λ_ℓ : use exclusion at level ℓ
      have hyle : ‖(y : E)‖ < successiveMinimum L ℓ := lt_of_lt_of_le hy hge
      have hmem := ih y hyle
      have hsub : PreSet d (fun j : Fin d => (v j : E)) (ℓ - 1) ≤
          PreSet d (fun j : Fin d => (v j : E)) ℓ := by
        dsimp [PreSet]
        exact Submodule.span_mono (by
          intro x hx
          rcases hx with ⟨j, hj, rfl⟩
          exact ⟨j, lt_of_lt_of_le hj (by omega), rfl⟩)
      exact hyF (hsub hmem)
  -- induction over the level
  intro ℓ
  induction ℓ with
  | zero =>
      intro h1 hd y hy
      omega
  | succ ℓ ih =>
      intro h1 hd y hy
      by_cases hℓ0 : ℓ = 0
      · subst ℓ
        simpa using hlevel1 h1 (by omega) y (by simpa using hy)
      · have hℓ1 : 1 ≤ ℓ := by omega
        have hℓd : ℓ ≤ d := by omega
        have hQ : ∀ y : L, ‖(y : E)‖ < successiveMinimum L ℓ →
            (y : E) ∈ PreSet d (fun j : Fin d => (v j : E)) (ℓ - 1) := by
          exact ih hℓ1 hℓd
        exact hstep ℓ hℓ1 hℓd hQ h1 hd y hy

/-- Lattice points in a closed ball of radius `N` (`N : ℕ`): reindexing to the scaled lattice. -/
lemma lattice_ball_card_eq_smulSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) {N : ℕ} (hN : 1 ≤ N) :
    Nat.card {v : L // ‖(v : E)‖ ≤ N} =
      Nat.card ↑(Metric.closedBall (0 : E) 1 ∩ (N : ℝ)⁻¹ • (L : Set E)) := by
  have hc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hset : Metric.closedBall (0 : E) (N : ℝ) = (N : ℝ) • Metric.closedBall (0 : E) 1 := by
    rw [smul_closedBall' hc (0 : E) 1]
    simp
  calc
    Nat.card {v : L // ‖(v : E)‖ ≤ N}
        = Nat.card {x : E // x ∈ (L : Set E) ∧ ‖x‖ ≤ N} := by
            refine Nat.card_congr ?_
            exact Equiv.subtypeSubtypeEquivSubtypeInter (fun x : E => x ∈ (L : Set E))
              (fun x => ‖x‖ ≤ N)
    _ = Nat.card {x : E // x ∈ (L : Set E) ∧ x ∈ Metric.closedBall (0 : E) (N : ℝ)} := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [and_congr_right_iff]
            intro hx
            exact mem_closedBall_zero_iff.symm
    _ = Nat.card ↑(Metric.closedBall (0 : E) (N : ℝ) ∩ (L : Set E)) := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [Set.mem_inter_iff, and_comm]
    _ = Nat.card ↑(((N : ℝ) • Metric.closedBall (0 : E) 1) ∩ (L : Set E)) := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [hset]
    _ = Nat.card ↑(Metric.closedBall (0 : E) 1 ∩ (N : ℝ)⁻¹ • (L : Set E)) := by
            refine Nat.card_congr ?_
            refine (Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x ↦ by
                simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
                  ← Set.mem_inv_smul_set_iff₀ hc])).symm

/-- The number of lattice points in the closed ball of radius `N` over `N^dim` tends to the
volume of the unit ball divided by the covolume (Riemann-sum asymptotics for lattices). -/
lemma card_inter_closedBall_tendsto_general {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Filter.Tendsto (fun N : ℕ =>
        (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℝ) / (N : ℝ) ^ Module.finrank ℝ E)
      Filter.atTop (nhds ((volume (Metric.closedBall (0 : E) 1)).toReal /
        ZLattice.covolume L)) := by
  have hfront : volume (frontier (Metric.closedBall (0 : E) 1)) = 0 := by
    have hsub : frontier (Metric.closedBall (0 : E) 1) ⊆ Metric.sphere (0 : E) (1 : ℝ) :=
      Metric.frontier_closedBall_subset_sphere
    have hsphere : volume (Metric.sphere (0 : E) (1 : ℝ)) = 0 := by
      simpa using (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume (0 : E)
        (by norm_num : (1 : ℝ) ≠ 0))
    apply le_antisymm
    · simpa [hsphere] using (measure_mono (μ := volume) hsub)
    · simp
  have hmain := ZLattice.covolume.tendsto_card_div_pow' (E := E) L
      (s := Metric.closedBall (0 : E) 1)
      (Metric.isBounded_closedBall) (Metric.isClosed_closedBall.measurableSet) hfront
  refine Filter.Tendsto.congr' ?event (by simpa [measureReal_def] using hmain)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  congr 1
  apply congrArg (fun k : ℕ => (k : ℝ))
  exact (lattice_ball_card_eq_smulSet (E := E) L hN).symm


/-! ## Glue: from the counting bound to Minkowski's second theorem (upper bound).

`lattice_count_int` bounds the number of lattice points in `B(N)` by a product of
floors of `2N/λᵢ`; dividing by `N^d` and taking `N → ∞` against the Riemann-sum limit
`card_inter_closedBall_tendsto_general` yields
`∏λᵢ · vol(B₁) ≤ 2^(2d-1) · covol L`. -/

/-- `(⌊2N/x⌋₊ + 1)/N → 2/x` for `x > 0` (squeeze between `2/x` and `2/x + 1/N`). -/
lemma tendsto_floor_div_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ =>
        (((Int.floor ((2 * (N : ℝ)) / x)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (2 / x)) := by
  classical
  let f : ℕ → ℝ := fun N => (((Int.floor ((2 * (N : ℝ)) / x)).toNat + 1 : ℕ) : ℝ) / (N : ℝ)
  let g : ℕ → ℝ := fun _ => 2 / x
  let h : ℕ → ℝ := fun N => 2 / x + (1 : ℝ) / (N : ℝ)
  have hg : Tendsto g atTop (nhds (2 / x)) := by
    simpa [g] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 / x : ℝ)) atTop (nhds (2 / x)))
  have hh : Tendsto h atTop (nhds (2 / x)) := by
    have hh' := (tendsto_const_nhds (x := (2 / x : ℝ))).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [h] using hh'
  have hge : ∀ᶠ N : ℕ in atTop, g N ≤ f N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    let y : ℝ := (2 * (N : ℝ)) / x
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hy : (2 / x : ℝ) = y / (N : ℝ) := by
      dsimp [y]
      field_simp [hx.ne', hNpos.ne']
    have hy0 : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (by positivity) (le_of_lt hx)
    have hqcast : (((Int.floor y).toNat + 1 : ℕ) : ℝ) = (Int.floor y : ℝ) + 1 := by
      have hf0 : 0 ≤ Int.floor y := Int.floor_nonneg.mpr hy0
      have hc : (((Int.floor y).toNat : ℕ) : ℝ) = (Int.floor y : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hf0
      rw [Nat.cast_add, Nat.cast_one, hc]
    have hylt : y < (((Int.floor y).toNat + 1 : ℕ) : ℝ) := by
      rw [hqcast]
      exact Int.lt_floor_add_one y
    have hmain : (2 / x : ℝ) < f N := by
      dsimp [f]
      rw [hy]
      have hdiv : y / (N : ℝ) < (((Int.floor y).toNat + 1 : ℕ) : ℝ) / (N : ℝ) := by
        exact div_lt_div_of_pos_right hylt hNpos
      simpa using hdiv
    exact le_of_lt hmain
  have hle : ∀ᶠ N : ℕ in atTop, f N ≤ h N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    let y : ℝ := (2 * (N : ℝ)) / x
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hy0 : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (by positivity) (le_of_lt hx)
    have hqcast : (((Int.floor y).toNat + 1 : ℕ) : ℝ) = (Int.floor y : ℝ) + 1 := by
      have hf0 : 0 ≤ Int.floor y := Int.floor_nonneg.mpr hy0
      have hc : (((Int.floor y).toNat : ℕ) : ℝ) = (Int.floor y : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hf0
      rw [Nat.cast_add, Nat.cast_one, hc]
    have hfloorle : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    have hnum : (((Int.floor y).toNat + 1 : ℕ) : ℝ) ≤ y + 1 := by
      rw [hqcast]
      linarith
    dsimp [f, h]
    have hdiv : (((Int.floor ((2 * (N : ℝ)) / x)).toNat + 1 : ℕ) : ℝ) / (N : ℝ) ≤
        (y + 1) / (N : ℝ) := by
      simpa [y] using (div_le_div_of_nonneg_right hnum (le_of_lt hNpos))
    have hR : (y + 1) / (N : ℝ) = (2 / x) + (1 : ℝ) / (N : ℝ) := by
      dsimp [y]
      field_simp [hx.ne', hNpos.ne']
    rw [← hR]
    exact hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh hge hle

/-- Product version: `∏ᵢ (⌊2N/λᵢ⌋₊ + 1)/N → ∏ᵢ (2/λᵢ)`. -/
lemma tendsto_prodQ {d : ℕ} (lam : Fin d → ℝ) (hlam : ∀ i : Fin d, 0 < lam i) :
    Tendsto (fun N : ℕ =>
        ∏ i : Fin d, (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∏ i : Fin d, 2 / lam i)) := by
  classical
  have hper : ∀ i : Fin d, Tendsto (fun N : ℕ =>
        (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (2 / lam i)) := fun i => tendsto_floor_div_atTop (hlam i)
  have hmain := tendsto_finsetProd (s := Finset.univ) (f := fun i : Fin d => fun N : ℕ =>
        (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
    (a := fun i : Fin d => 2 / lam i) (fun i _ => hper i)
  simpa using hmain

/-- `(∏ aᵢ)/N^d = ∏ (aᵢ/N)` for `N ≥ 1`. -/
lemma prod_div_pow {d : ℕ} (a : Fin d → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∏ i : Fin d, a i) / (N : ℝ) ^ d = ∏ i : Fin d, (a i / (N : ℝ)) := by
  have hpow : (N : ℝ) ^ d = ∏ i : Fin d, (N : ℝ) := by
    simp [Finset.prod_const, Fintype.card_fin]
  calc
    (∏ i : Fin d, a i) / (N : ℝ) ^ d
        = (∏ i : Fin d, a i) / (∏ i : Fin d, (N : ℝ)) := by rw [hpow]
    _ = ∏ i : Fin d, (a i / (N : ℝ)) := by
        rw [Finset.prod_div_distrib]

/-- Intermediate bound: `∏λᵢ · vol(B₁) ≤ 2^(2d-1) · covol L`, from the lattice-count
bound and the ball-counting asymptotics. -/
lemma product_upper_bound {d : ℕ} (hd : 0 < d) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = d) :
    (∏ i : Fin d, Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) ≤
      (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L := by
  classical
  let lam : Fin d → ℝ := fun i => Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)
  have hlam_pos : ∀ i : Fin d, 0 < lam i := by
    intro i
    dsimp [lam]
    exact Commons.Lattice.SuccessiveMinima.positive L (i.val + 1) (by omega) (by rw [hfin]; omega)
  have hcov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hfdim : Module.finrank ℝ E = d := by
    exact (ZLattice.rank ℝ L).symm.trans hfin
  let cN : ℕ → ℕ := fun N => Nat.card {v : L // ‖(v : E)‖ ≤ N}
  let qN : ℕ → Fin d → ℕ := fun N i => (Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1
  let f : ℕ → ℝ := fun N => (cN N : ℝ) / (N : ℝ) ^ d
  let h : ℕ → ℝ := fun N => (∏ i : Fin d, (qN N i : ℝ)) / (N : ℝ) ^ d
  let g : ℕ → ℝ := fun N => (2 : ℝ) ^ (d - 1) * h N
  let A : ℝ := ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) / ZLattice.covolume L
  let B : ℝ := (2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)
  have hlimf : Tendsto f atTop (nhds A) := by
    have hgen := card_inter_closedBall_tendsto_general (E := E) L
    dsimp [f, cN, A]
    simpa [hfdim] using hgen
  have hlimh : Tendsto h atTop (nhds (∏ i : Fin d, 2 / lam i)) := by
    have hQ := tendsto_prodQ lam hlam_pos
    dsimp [h, qN]
    have heq : (fun N : ℕ =>
        ∏ i : Fin d, (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
        =ᶠ[atTop] (fun N : ℕ => (∏ i : Fin d, (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ)) / (N : ℝ) ^ d) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (prod_div_pow (fun i : Fin d => (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ)) N hN).symm
    exact hQ.congr' heq
  have hlimg : Tendsto g atTop (nhds B) := by
    have hc : Tendsto (fun _ : ℕ => (2 : ℝ) ^ (d - 1)) atTop
        (nhds ((2 : ℝ) ^ (d - 1))) := tendsto_const_nhds
    dsimp [g, B]
    exact hc.mul hlimh
  have hev : ∀ᶠ N : ℕ in atTop, f N ≤ g N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcnt : (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤
        2 ^ (d - 1) * ∏ i : Fin d,
          ((Int.floor ((2 * (N : ℝ)) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1))).toNat + 1) := by
      exact Commons.Lattice.Counting.lattice_count_int (E := E) L hfin hd N hN
    have hcntR : (cN N : ℝ) ≤ (2 : ℝ) ^ (d - 1) * (∏ i : Fin d, (qN N i : ℝ)) := by
      dsimp [cN, qN, lam]
      exact_mod_cast hcnt
    have hNpow : 0 ≤ (N : ℝ) ^ d := pow_nonneg (by exact_mod_cast (Nat.zero_le N)) d
    have hdiv := div_le_div_of_nonneg_right hcntR hNpow
    dsimp [f, g, h]
    rw [mul_div_assoc] at hdiv
    exact hdiv
  have hlim := le_of_tendsto_of_tendsto hlimf hlimg hev
  have hvol : ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) ≤
      ((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L := by
    dsimp [A, B] at hlim
    exact (div_le_iff₀ hcov_pos).mp hlim
  let P : ℝ := ∏ i : Fin d, lam i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (s := Finset.univ) (fun i _ => hlam_pos i)
  have hper : ∀ i : Fin d, lam i * (2 / lam i) = 2 := by
    intro i
    field_simp [ne_of_gt (hlam_pos i)]
  have hPQ : P * (∏ i : Fin d, 2 / lam i) = (2 : ℝ) ^ d := by
    dsimp [P]
    rw [← Finset.prod_mul_distrib]
    rw [show (∏ i : Fin d, lam i * (2 / lam i)) = ∏ i : Fin d, (2 : ℝ) by
      exact Finset.prod_congr rfl (fun i hi => hper i)]
    simp [Finset.prod_const, Fintype.card_fin]
  have hA_pow : (2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ d = (2 : ℝ) ^ (2 * d - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep1 : P * ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) ≤
      P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L) := by
    exact mul_le_mul_of_nonneg_left hvol (le_of_lt hPpos)
  have hstep2 : P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L)
      = (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L := by
    have hmm : P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L)
        = ((2 : ℝ) ^ (d - 1) * (P * ∏ i : Fin d, (2 / lam i))) * ZLattice.covolume L := by
          ac_rfl
    calc
      P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L)
          = ((2 : ℝ) ^ (d - 1) * (P * ∏ i : Fin d, (2 / lam i))) * ZLattice.covolume L := hmm
      _ = ((2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ d) * ZLattice.covolume L := by rw [hPQ]
      _ = (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L := by rw [hA_pow]
  exact le_trans hstep1 (le_of_eq hstep2)


/-- **Minkowski's second theorem (upper bound), normed-lattice form**: if `L` is a full
`ℤ`-lattice of rank `d` in a finite-dimensional real inner-product space `E`, and
`λᵢ = successiveMinimum L i` are the successive minima of the closed unit ball of the
ambient norm with respect to `L`, then
`λ₁·…·λ_d · volume (closedBall 0 1) ≤ (2·2)^d · covolume L`.
(Volume is the canonical measure attached to the inner product; the statement is
normalisation-invariant.  Prove by the classical covering argument of Minkowski's second
theorem — cf. Cassels, *Geometry of Numbers*, Ch. VIII Thm. II, or Henk's short proof
"Successive minima and lattice points", arXiv:math/0204158 §4.) -/
theorem minkowski_second_upper {d : ℕ} (hd : 0 < d) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = d) :
    (∏ i : Fin d, Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : E) 1)) ≤
      (2 : ℝ) ^ (2 * d) * ZLattice.covolume L := by
  have hup := product_upper_bound (E := E) (d := d) hd L hfin
  have hcov_nonneg : 0 ≤ ZLattice.covolume L := le_of_lt (ZLattice.covolume_pos L)
  have hpow : (2 : ℝ) ^ (2 * d - 1) ≤ (2 : ℝ) ^ (2 * d) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 * d - 1 ≤ 2 * d)
  exact le_trans hup (mul_le_mul_of_nonneg_right hpow hcov_nonneg)

end

end Commons.Lattice.Minkowski
