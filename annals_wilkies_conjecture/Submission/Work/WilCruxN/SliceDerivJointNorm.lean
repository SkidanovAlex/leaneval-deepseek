import Mathlib
import Submission.Work.WilCruxN.SliceDerivJointPerJ

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

/-! ## Two elementary helpers

The first is the linear-algebra input: for `T : (Fin b → ℝ) →L[ℝ] ℝ` the operator norm is bounded
by the sum of the absolute values of `T` on the standard basis (`T v = ∑ j, v j * T (Pi.single j
1)` combined with `|v j| ≤ ‖v‖`).  The second is the topological input: a finite intersection of
open sets, each dense in an open `Q`, is still dense in `Q`. -/

/-- For `T : (Fin b → ℝ) →L[ℝ] ℝ`, if every value on a standard basis vector is smaller than
`ε/(b+1)`, then the operator norm of `T` is smaller than `ε`. -/
private theorem opNorm_lt_of_forall_single_lt {b : ℕ} (T : (Fin b → ℝ) →L[ℝ] ℝ) {ε : ℝ}
    (hε : 0 < ε) (h : ∀ j : Fin b, |T (Pi.single j 1)| < ε / ((b : ℝ) + 1)) : ‖T‖ < ε := by
  -- `v = ∑ j, v j • Pi.single j 1`, hence `T v = ∑ j, v j * T (Pi.single j 1)`
  have hdecomp : ∀ v : Fin b → ℝ, T v = ∑ j : Fin b, v j * T (Pi.single j (1 : ℝ)) := by
    intro v
    have hv : v = ∑ j : Fin b, v j • (Pi.single j (1 : ℝ) : Fin b → ℝ) := by
      funext i
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne (Ne.symm hji)]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  -- the operator norm is bounded by the sum of the single-basis values
  have hnorm : ‖T‖ ≤ ∑ j : Fin b, |T (Pi.single j (1 : ℝ))| := by
    refine ContinuousLinearMap.opNorm_le_bound T
      (Finset.sum_nonneg fun j _ => abs_nonneg _) fun v => ?_
    rw [hdecomp v]
    calc ‖∑ j : Fin b, v j * T (Pi.single j (1 : ℝ))‖
        ≤ ∑ j : Fin b, ‖v j * T (Pi.single j (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ j : Fin b, |v j| * |T (Pi.single j (1 : ℝ))| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ ∑ j : Fin b, ‖v‖ * |T (Pi.single j (1 : ℝ))| := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
      _ = ‖v‖ * ∑ j : Fin b, |T (Pi.single j (1 : ℝ))| := by rw [Finset.mul_sum]
      _ = (∑ j : Fin b, |T (Pi.single j (1 : ℝ))|) * ‖v‖ := by rw [mul_comm]
  -- the numerical estimate `b · ε/(b+1) < ε`
  have hlt : (b : ℝ) * (ε / ((b : ℝ) + 1)) < ε := by
    have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hdiv : (b : ℝ) / ((b : ℝ) + 1) < 1 := by
      rw [div_lt_one hb1]; linarith
    have heq : (b : ℝ) * (ε / ((b : ℝ) + 1)) = ε * ((b : ℝ) / ((b : ℝ) + 1)) := by ring
    rw [heq]
    calc ε * ((b : ℝ) / ((b : ℝ) + 1)) < ε * 1 := mul_lt_mul_of_pos_left hdiv hε
      _ = ε := mul_one ε
  calc ‖T‖ ≤ ∑ j : Fin b, |T (Pi.single j (1 : ℝ))| := hnorm
    _ ≤ ∑ _j : Fin b, ε / ((b : ℝ) + 1) := Finset.sum_le_sum fun j _ => le_of_lt (h j)
    _ = (b : ℝ) * (ε / ((b : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ε := hlt

/-- If `Q` is open and each `U i` is open and dense in `Q` (meaning `Q ⊆ closure (U i)`), then
`Q` is contained in the closure of the finite intersection `Q ∩ ⋂ i ∈ s, U i`. -/
private theorem subset_closure_inter_biInter {X : Type*} [TopologicalSpace X] {ι : Type*}
    [DecidableEq ι] (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) {Q : Set X} (hQ : IsOpen Q)
    (hU : ∀ i, Q ⊆ closure (U i)) (s : Finset ι) :
    Q ⊆ closure (Q ∩ ⋂ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using subset_closure (s := Q)
  | insert a s ha ih =>
      intro x hx
      rw [mem_closure_iff]
      intro o ho hxo
      have hxA : x ∈ closure (Q ∩ ⋂ i ∈ s, U i) := ih hx
      obtain ⟨y, hyo, hyQ, hys⟩ := (mem_closure_iff.mp hxA) o ho hxo
      have hAopen : IsOpen (Q ∩ ⋂ i ∈ s, U i) :=
        hQ.inter (isOpen_biInter_finset fun i _ => hUo i)
      obtain ⟨w, hw, hwa⟩ := (mem_closure_iff.mp (hU a hyQ))
        (o ∩ (Q ∩ ⋂ i ∈ s, U i)) (ho.inter hAopen) ⟨hyo, hyQ, hys⟩
      obtain ⟨hwo, hwQ, hws⟩ := hw
      have hws' : ∀ i ∈ s, w ∈ U i := fun i hi =>
        (Set.mem_iInter.mp (Set.mem_iInter.mp hws i)) hi
      refine ⟨w, hwo, hwQ, ?_⟩
      simpa using (show w ∈ U a ∧ ∀ i ∈ s, w ∈ U i from ⟨hwa, hws'⟩)

/-
  **Node N4b of the flat-sheet chain, without `SharpDeriv`: the norm form.**

  This is the statement of `Work.WilCrux.SliceDerivJointContV2` with the hypothesis
  `hder : S.SharpDeriv` removed (everything else verbatim).  It assembles the per-direction form
  `Work.WilCruxN.SliceDerivJointPerJ` (proved in the sibling file):  each direction `j` supplies an
  open `Q1 j` with `Q ⊆ closure (Q1 j)`; on `Q1 := Q ∩ ⋂ j, Q1 j` (a *finite* intersection of open
  dense subsets of `Q`, so open and dense in `Q`) the coordinatewise bounds combine:

  * the operator norm of `T := fderiv ℝ (G w) z - fderiv ℝ (G w) 0 : (Fin b → ℝ) →L[ℝ] ℝ` is at
    most `∑ j, |T (Pi.single j 1)|` (because `T v = ∑ j, v j * T (Pi.single j 1)`; the triangle
    inequality then gives the estimate), so bounds `|T (Pi.single j 1)| < ε / (b+1)` for all `j`
    give `‖T‖ < ε`;
  * the continuity conjunct is the conjunction of the per-direction ones.

  The case `b = 0` is degenerate but harmless: `Fin 0 →L[ℝ] ℝ` is the zero space, so the norm
  bound is trivial (and `Q1 := Q` works).

  Note: `Submission/Work/WilCruxN/SliceDerivJointClean.lean` is an earlier, non-building attempt
  at the same statement; do not edit it, work in the new module.  Do **not** use
  `Work.WilG4b.derivGraph_mem` nor any `hder`-taking declaration: `#print axioms` must show only
  `[propext, Classical.choice, Quot.sound]`.
-/
theorem SliceDerivJointNorm (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z)) :
    ∃ Q1 : Set (Fin a → ℝ), IsOpen Q1 ∧ Q1 ⊆ Q ∧ Q ⊆ closure Q1 ∧
      (∀ w₀ ∈ Q1, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
        dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
          ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε) ∧
      (∀ w₀ ∈ Q1, ∀ j : Fin b, Filter.Tendsto (fun w => fderiv ℝ (G w) 0 (Pi.single j 1))
        (nhds w₀) (nhds (fderiv ℝ (G w₀) 0 (Pi.single j 1)))) := by
  classical
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- Degenerate fibre: `Fin 0 →L[ℝ] ℝ` is trivial, so `Q1 := Q` works.
    subst hb0
    refine ⟨Q, hQ, fun x hx => hx, subset_closure, ?_, ?_⟩
    · intro w₀ hw₀ ε hε
      exact ⟨1, one_pos, fun w z _ hz _ =>
        opNorm_lt_of_forall_single_lt _ hε (fun j : Fin 0 => j.elim0)⟩
    · intro w₀ hw₀ j
      exact j.elim0
  · -- Non-degenerate fibre: intersect the (finitely many) per-direction open dense sets.
    have hne : (Finset.univ : Finset (Fin b)).Nonempty :=
      ⟨⟨0, hbpos⟩, Finset.mem_univ _⟩
    have hP : ∀ j : Fin b, ∃ Q1 : Set (Fin a → ℝ), IsOpen Q1 ∧ Q1 ⊆ Q ∧ Q ⊆ closure Q1 ∧
        (∀ w₀ ∈ Q1, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
          dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
            |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| < ε) ∧
        (∀ w₀ ∈ Q1, Filter.Tendsto (fun w => fderiv ℝ (G w) 0 (Pi.single j 1)) (nhds w₀)
          (nhds (fderiv ℝ (G w₀) 0 (Pi.single j 1)))) :=
      fun j => SliceDerivJointPerJ S hcd G hG Q hQ r0 hr0 hsl hoff j
    let Qj : Fin b → Set (Fin a → ℝ) := fun j => (hP j).choose
    have hQj : ∀ j, IsOpen (Qj j) ∧ Qj j ⊆ Q ∧ Q ⊆ closure (Qj j) ∧
        (∀ w₀ ∈ Qj j, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
          dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
            |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| < ε) ∧
        (∀ w₀ ∈ Qj j, Filter.Tendsto (fun w => fderiv ℝ (G w) 0 (Pi.single j 1)) (nhds w₀)
          (nhds (fderiv ℝ (G w₀) 0 (Pi.single j 1)))) :=
      fun j => (hP j).choose_spec
    have hdense : Q ⊆ closure (Q ∩ ⋂ j ∈ (Finset.univ : Finset (Fin b)), Qj j) :=
      subset_closure_inter_biInter (fun j : Fin b => Qj j)
        (fun j => (hQj j).1) hQ (fun j => (hQj j).2.2.1) (Finset.univ : Finset (Fin b))
    refine ⟨Q ∩ ⋂ j, Qj j, hQ.inter (isOpen_iInter_of_finite fun j => (hQj j).1),
      Set.inter_subset_left, ?_, ?_, ?_⟩
    · simpa using hdense
    · intro w₀ hw₀ ε hε
      obtain ⟨hw₀Q, hw₀I⟩ := hw₀
      have hε' : 0 < ε / ((b : ℝ) + 1) := by positivity
      have hwit : ∀ j : Fin b, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
          dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
            |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| < ε / ((b : ℝ) + 1) :=
        fun j => (hQj j).2.2.2.1 w₀ (Set.mem_iInter.mp hw₀I j) _ hε'
      choose ηj hηj using hwit
      refine ⟨Finset.univ.inf' hne ηj, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hne).mpr fun j _ => (hηj j).1
      · intro w z hw hz hzl
        refine opNorm_lt_of_forall_single_lt _ hε ?_
        intro j
        have hle : Finset.univ.inf' hne ηj ≤ ηj j := Finset.inf'_le ηj (Finset.mem_univ j)
        exact (hηj j).2 w z (lt_of_lt_of_le hw hle) hz (lt_of_lt_of_le hzl hle)
    · intro w₀ hw₀ j
      exact (hQj j).2.2.2.2 w₀ (Set.mem_iInter.mp hw₀.2 j)

end Work.WilCruxN
