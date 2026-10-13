/-
  WilE9G / Assembly — **`Good` for the boundary-compatible Lagrange stratum `lagStratumAE`**.

  `lagStratumAE S Phi c` differs from `Lagrange.lagStratum S Phi c` in two respects: its DNF runs
  over the basics `B` of the input stratum `S.X` (each basic carrying the equations of `S` and the
  Lagrange equations together, and the strict inequalities `lagDet² > 0` together with the `pos`
  of `B`), and it drops the interior (open cube) conditions of `lagStratum`.

  The three clauses of `EffStratum.Good` are checked at a point `z` of the set:

  * the equations vanish because they are part of the eqs of the disjunct containing `z`;
  * the fibre determinant does not vanish because `lagDet²` is one of the strict inequalities;
  * locality is where the two changes matter.  If `z'` is near `z` and satisfies the equations
    `lagEqs S Phi c`, then

    - the equations of `S` hold at the base-and-fibre part `takeZ z'` (these are the `lagH` block
      of `lagEqs`), so the *ambient* locality of the `Good` stratum `S` puts `takeZ z'` in
      `S.X.set`; some basic `B''` of `S` holds there, and `z'` satisfies the corresponding padded
      basic of `lagStratumAE` (the eqs are the very `lagEqs` and the padded `B''.eqs`, the strict
      inequalities are `lagDet² > 0`, which holds on a neighbourhood of `z` by continuity, and the
      padded `B''.pos`);
    - the cube condition on `z'` follows: the base-and-fibre part is in `S.X.set ⊆ cubeC` (so
      `|z'_j| ≤ 1` for `j < n + (1 + m)`), and the multiplier coordinates are bounded by the
      normalisation equation `∑ μ_a² + μ₀² = 1`, which is part of `lagEqs`.

  This last point is exactly why `lagStratumAE` keeps the `pos` of `S` instead of the interior cube
  conditions: `Good` holds also at Lagrange points whose base-and-fibre part lies on the boundary of
  the cube.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.lagStratum_good
import Submission.Work.WilE7.pad_component_proj

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## Evaluation of the padded vocabulary in the chain of the Lagrange stratum -/

/-- A polynomial of `S`, padded to the ambient space of the Lagrange stratum, evaluates there as
the original polynomial at the base-and-fibre part of the point. -/
theorem eaEval_lagChain_pad {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (Q : EAPoly (n + (1 + m)) S.X.r) (w : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    eaEval (lagChain S) (Work.WilE7.EAPoly.pad hm Q) w
      = eaEval S.X.c Q (Work.WilE7.takeZ hm w) :=
  (Work.WilE7.pad_eval hm S.X.c).2.2 Q w

/-- A basic set of `S`, padded to the ambient space of the Lagrange stratum, holds at a point
exactly when the original basic set holds at the base-and-fibre part of the point. -/
theorem holds_lagChain_pad {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (B : Basic (n + (1 + m)) S.X.r) (w : Fin (n + (1 + (m + S.j + 1))) → ℝ) :
    (Work.WilE7.Basic.pad hm B).holds (lagChain S) w ↔ B.holds S.X.c (Work.WilE7.takeZ hm w) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · intro f hf
    have h' := h.1 (Work.WilE7.EAPoly.pad hm f) (List.mem_map_of_mem hf)
    rwa [eaEval_lagChain_pad S hm f w] at h'
  · intro g hg
    have h' := h.2 (Work.WilE7.EAPoly.pad hm g) (List.mem_map_of_mem hg)
    rwa [eaEval_lagChain_pad S hm g w] at h'
  · intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
    rw [eaEval_lagChain_pad S hm f₀ w]
    exact h.1 f₀ hf₀
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    rw [eaEval_lagChain_pad S hm g₀ w]
    exact h.2 g₀ hg₀

/-! ## Index bookkeeping for the equations of the Lagrange stratum -/

/-- At the index of the `b`-th equation of `S`, the equation of the constructed stratum is
`lagH S b`. -/
theorem lagEqs_at_lagH {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) (b : Fin S.j) :
    lagEqs S Phi c ⟨1 + m + b.val, by omega⟩ = lagH S b := by
  unfold lagEqs
  have h : lagEquiv m S.j ⟨1 + m + b.val, by omega⟩
      = Fin.natAdd (1 + m) (Fin.castAdd 1 b) := by
    apply Fin.ext
    simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]
  rw [h, Fin.addCases_right, Fin.addCases_left]

/-- The `b`-th equation of the constructed stratum, evaluated at a point, is the `b`-th equation
of `S` evaluated at the base-and-fibre part of the point. -/
theorem lagEqs_at_lagH_eval {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) (b : Fin S.j)
    (w : Fin (n + (1 + (m + S.j + 1))) → ℝ)
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) :
    eaEval (lagChain S) (lagEqs S Phi c ⟨1 + m + b.val, by omega⟩) w
      = eaEval S.X.c (S.h b) (Work.WilE7.takeZ hm w) := by
  rw [lagEqs_at_lagH S Phi c b]
  exact eaEval_lagChain_pad S hm (S.h b) w

/-! ## `Good` for the boundary-compatible Lagrange stratum -/

theorem lagStratumAE_good {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (Work.WilE9G.Assembly.lagStratumAE S Phi c).Good := by
  intro z hz
  simp only [lagStratumAE] at hz ⊢
  simp only [WilkiesDesign.E.SemiPf.set, Set.mem_ofPred_eq] at hz
  obtain ⟨hzcube, B, hBmem, hBeq, hBpos⟩ := hz
  obtain ⟨B₀, hB₀mem, rfl⟩ := List.mem_map.mp hBmem
  have hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)) := by omega
  -- the equations of the stratum vanish at `z`
  have heqs : ∀ a, eaEval (lagChain S) (lagEqs S Phi c a) z = 0 := by
    intro a
    exact hBeq _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨a, rfl⟩))
  -- the square of the fibre determinant is one of the strict inequalities at `z`
  have hdetpos : 0 < eaEval (lagChain S) (lagDet S Phi c * lagDet S Phi c) z :=
    hBpos _ List.mem_cons_self
  have hdet : eaEval (lagChain S) (lagDet S Phi c) z ≠ 0 := by
    rw [lagStratum_eaEval_lagDet_sq S Phi c z] at hdetpos
    exact mul_self_pos.mp hdetpos
  refine ⟨heqs, ?_, ?_⟩
  · -- the fibre block is invertible
    change (lagBlock S Phi c z).det ≠ 0
    rw [← lagStratum_eaEval_lagDet S Phi c z]
    exact hdet
  · -- ambient locality
    -- the base-and-fibre part of `z` lies in `S.X.set`
    have hBF : Work.WilE7.takeZ hm z ∈ S.X.set := by
      refine ⟨Work.WilE7.takeZ_mem_cubeC hm hzcube, B₀, hB₀mem, ?_, ?_⟩
      · intro f hf
        have h := hBeq (Work.WilE7.EAPoly.pad hm f)
          (List.mem_append_right _ (List.mem_map_of_mem hf))
        rwa [eaEval_lagChain_pad S hm f z] at h
      · intro g hg
        have h := hBpos (Work.WilE7.EAPoly.pad hm g)
          (List.mem_append_right _ (List.mem_map_of_mem hg))
        rwa [eaEval_lagChain_pad S hm g z] at h
    -- ambient locality of `S`, pulled back along `takeZ`
    have hSloc : ∀ᶠ w in 𝓝 (Work.WilE7.takeZ hm z),
        (∀ b, eaEval S.X.c (S.h b) w = 0) → w ∈ S.X.set :=
      AmbStratum_locality S hS hBF
    have hSloc' : ∀ᶠ z' in 𝓝 z,
        (∀ b, eaEval S.X.c (S.h b) (Work.WilE7.takeZ hm z') = 0) →
          Work.WilE7.takeZ hm z' ∈ S.X.set :=
      (Work.WilE7.continuous_takeZ hm).continuousAt.eventually hSloc
    -- `lagDet` does not vanish near `z`
    have hdet_ev : ∀ᶠ z' in 𝓝 z, eaEval (lagChain S) (lagDet S Phi c) z' ≠ 0 :=
      (lagStratum_continuous_eaEval (lagChain S) (lagDet S Phi c)).continuousAt.eventually_ne
        hdet
    filter_upwards [hdet_ev, hSloc'] with z' hz'det hz'loc hLagEqs
    -- the equations of `S` hold at the base-and-fibre part of `z'`
    have hS_eqs : ∀ b : Fin S.j, eaEval S.X.c (S.h b) (Work.WilE7.takeZ hm z') = 0 := by
      intro b
      rw [← lagEqs_at_lagH_eval S Phi c b z' hm]
      exact hLagEqs ⟨1 + m + b.val, by omega⟩
    have hBF' : Work.WilE7.takeZ hm z' ∈ S.X.set := hz'loc hS_eqs
    simp only [WilkiesDesign.E.SemiPf.set, Set.mem_ofPred_eq] at hBF'
    obtain ⟨hz'cubeBF, B'', hB''mem, hB''eq, hB''pos⟩ := hBF'
    refine ⟨?_, ?_⟩
    · -- the cube bound
      intro i
      by_cases hi : i.val < n + (1 + m)
      · -- a base-and-fibre coordinate: it is bounded since `takeZ hm z' ∈ S.X.set ⊆ cubeC`
        exact hz'cubeBF ⟨i.val, hi⟩
      · -- a multiplier coordinate: it is bounded by the normalisation equation
        have hnorm : (∑ a : Fin S.j, (z' (muIdx n m a)) ^ 2) + (z' (mu0Idx n m S.j)) ^ 2 = 1 := by
          have h := hLagEqs ⟨m + S.j + 1, by omega⟩
          rw [lagStratum_lagEqs_last S Phi c] at h
          rw [lagStratum_eaEval_lagN S z'] at h
          linarith
        have hbound : (∑ a : Fin S.j, (z' (muIdx n m a)) ^ 2) ≤ 1 := by
          have := sq_nonneg (z' (mu0Idx n m S.j)); linarith
        have hgt : n + (1 + m) ≤ i.val := Nat.le_of_not_lt hi
        have hlt : i.val - (n + (1 + m)) < S.j + 1 := by
          have := i.isLt; omega
        by_cases ht : i.val - (n + (1 + m)) < S.j
        · have he : muIdx n m (⟨i.val - (n + (1 + m)), ht⟩ : Fin S.j) = i := by
            apply Fin.ext
            simp only [muIdx_val]
            omega
          rw [← he, ← sq_le_one_iff_abs_le_one]
          exact le_trans (Finset.single_le_sum
            (f := fun a : Fin S.j => (z' (muIdx n m a)) ^ 2) (fun a _ => sq_nonneg _)
            (Finset.mem_univ (⟨i.val - (n + (1 + m)), ht⟩ : Fin S.j))) hbound
        · have hts : i.val - (n + (1 + m)) = S.j := by omega
          have he : mu0Idx n m S.j = i := by
            apply Fin.ext
            simp only [mu0Idx_val]
            omega
          rw [← he, ← sq_le_one_iff_abs_le_one]
          exact le_trans (le_add_of_nonneg_left (Finset.sum_nonneg fun a _ => sq_nonneg _))
            (le_of_eq hnorm)
    · -- the padded basic of `B''` holds at `z'`
      refine ⟨⟨List.ofFn (lagEqs S Phi c) ++ B''.eqs.map (Work.WilE7.EAPoly.pad hm),
        [lagDet S Phi c * lagDet S Phi c] ++ B''.pos.map (Work.WilE7.EAPoly.pad hm)⟩,
        List.mem_map_of_mem hB''mem, ?_, ?_⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hf
          exact hLagEqs a
        · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
          rw [eaEval_lagChain_pad S hm f₀ z']
          exact hB''eq f₀ hf₀
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · obtain rfl := List.mem_singleton.mp hg
          rw [lagStratum_eaEval_lagDet_sq S Phi c z']
          exact mul_self_pos.mpr hz'det
        · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
          rw [eaEval_lagChain_pad S hm g₀ z']
          exact hB''pos g₀ hg₀

end Work.WilE9G.Assembly
