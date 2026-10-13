/-
  Elementary `Ω`-membership facts used to cut and combine the sets built by the cell-section
  recursion `Work.WilkG4c.PinnedSection`:

  * a metric ball of `Fin n → ℝ` (sup metric) is an `Ω`-set (used to cut the open set down to a
    *smaller* `Ω`-definable open neighbourhood of a point, so that the section values land in a
    prescribed open set, or so that the fibre coordinate stays inside a band);
  * a coordinate hyperplane `{z | z i = c}` is an `Ω`-set (the constant fibre coordinate on a
    band step);
  * the *fibre end* of a band cell is recoverable from the cell's `Ω`-membership:
    `projLast (κ ∩ {z | z last < t}) = {u ∈ base | a u < t}`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign

/-- **Balls are `Ω`-definable.**  For the sup-metric on `Fin n → ℝ` the ball is the open box
`∏ᵢ (cᵢ - r, cᵢ + r)`, a finite intersection of basic `Ω`-sets. -/
theorem dsg_ball_mem (S : WilkiesDesign.SOMin) {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ F D : ℕ, Metric.ball c r ∈ S.Ω F D n := by
  have hsingle : ∀ i : Fin n, {x : Fin n → ℝ | x i ∈ Set.Ioo (c i - r) (c i + r)} ∈
      S.Ω (4 * n + 21) 16 n := by
    intro i
    have h1 : {x : Fin n → ℝ | c i - r < x i} ∈ S.Ω (4 * n + 20) 8 n :=
      Work.WilG5.ltSet_mem (S := S) i (c i - r)
    have h2 : {x : Fin n → ℝ | x i < c i + r} ∈ S.Ω (4 * n + 20) 8 n :=
      Work.WilG5.gtSet_mem (S := S) i (c i + r)
    have h := S.inter (F := 4 * n + 20) (n := n) (k := 2) (fun _ : Fin 2 => 8)
      (fun j : Fin 2 => if j = 0 then {x : Fin n → ℝ | c i - r < x i}
        else {x : Fin n → ℝ | x i < c i + r})
      (by
        intro j
        fin_cases j
        · simpa using h1
        · simpa using h2)
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    have he : ({x : Fin n → ℝ | c i - r < x i} ∩ {x : Fin n → ℝ | x i < c i + r})
        = {x : Fin n → ℝ | x i ∈ Set.Ioo (c i - r) (c i + r)} := by
      ext x; simp [Set.mem_Ioo, and_comm]
    rw [he] at h
    simpa using h
  have h := S.inter (F := 4 * n + 21) (n := n) (k := n) (fun _ : Fin n => 16)
    (fun i : Fin n => {x : Fin n → ℝ | x i ∈ Set.Ioo (c i - r) (c i + r)}) hsingle
  have hsum : (∑ _ : Fin n, (16 : ℕ)) = 16 * n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [hsum] at h
  have heq : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ Set.Ioo (c i - r) (c i + r)})
      = Metric.ball c r := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ioo, Metric.mem_ball, dist_pi_lt_iff hr, Real.dist_eq,
      abs_lt]
    constructor
    · intro hx i; exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    · intro hx i; exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  rw [heq] at h
  exact ⟨4 * n + 21 + 1, 16 * n, h⟩

/-- **Intersection of two `Ω`-sets**, with explicit format/degree bookkeeping: the format is the
max of the two (plus one) and the degrees add. -/
theorem dsg_inter2 (S : WilkiesDesign.SOMin) {n : ℕ} {A B : Set (Fin n → ℝ)} {FA DA FB DB : ℕ}
    (hA : A ∈ S.Ω FA DA n) (hB : B ∈ S.Ω FB DB n) :
    A ∩ B ∈ S.Ω (max FA FB + 1) (DA + DB) n := by
  have h1 : A ∈ S.Ω (max FA FB) DA n := Work.WilG5.mem_mono hA _ _ (le_max_left _ _) le_rfl
  have h2 : B ∈ S.Ω (max FA FB) DB n := Work.WilG5.mem_mono hB _ _ (le_max_right _ _) le_rfl
  have h3 := S.inter (fun i : Fin 2 => if i = 0 then DA else DB)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by
      intro i
      fin_cases i
      · simpa using h1
      · simpa using h2)
  rw [show (∑ i : Fin 2, (if i = 0 then DA else DB)) = DA + DB from by
    rw [Fin.sum_univ_two]; norm_num] at h3
  rw [show (⋂ i : Fin 2, (if i = 0 then A else B)) = A ∩ B from by
    ext z; simp [Fin.forall_fin_two]] at h3
  exact h3

/-- **Coordinate hyperplanes are `Ω`-definable**: `{z | z i = c}` is the zero set of the
degree-`1` polynomial `X i - C c`. -/
theorem dsg_coord_eq_mem (S : WilkiesDesign.SOMin) {n : ℕ} (i : Fin n) (c : ℝ) :
    {z : Fin n → ℝ | z i = c} ∈ S.Ω n 1 n := by
  have hdeg : (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
    · exact Work.WilG5.td_X_le i
    · exact le_trans (Work.WilG5.td_C_le c) (Nat.zero_le 1)
  have h := S.hyp n (MvPolynomial.X i - MvPolynomial.C c)
  have he : {z : Fin n → ℝ |
        MvPolynomial.eval z (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = 0}
      = {z : Fin n → ℝ | z i = c} := by
    ext z
    simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]
  rw [he] at h
  exact Work.WilG5.mem_mono h n 1 le_rfl hdeg

set_option maxHeartbeats 800000 in
/-- **The fibre end of a band cell is recoverable from the cell.**  For a band cell over a base
`C` with ends `a < b` (as produced by `WilkiesDesign.IsCell.band`), the projection of the part of
the cell below the level `t` is exactly the set of base points at which the lower end is `< t`.
This is what turns `{u | a u < t}` (a pullback along the *non*-definable band end) into an
`Ω`-set: `projLast (κ ∩ {z | z last < t})` with `κ ∈ Ω`. -/
theorem dsg_projLast_inter_lt {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (hab : ∀ x ∈ C, a x < b x) (t : ℝ) :
    WilkiesDesign.projLast ({z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} ∩
      {z : Fin (n + 1) → ℝ | z (Fin.last n) < t}) =
    {u : Fin n → ℝ | u ∈ C ∧ a u < (t : EReal)} := by
  ext u
  constructor
  · intro hu
    obtain ⟨t', hband, hlt⟩ := hu
    simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hband hlt
    exact ⟨hband.1, lt_trans hband.2.1 (by exact_mod_cast hlt)⟩
  · rintro ⟨huC, hlt⟩
    have hmin : a u < min (b u) (t : EReal) := lt_min (hab u huC) hlt
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hmin
    refine ⟨s, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨huC, hs1, lt_of_lt_of_le hs2 (min_le_left _ _)⟩
    · have hfac : (s : EReal) < (t : EReal) := lt_of_lt_of_le hs2 (min_le_right _ _)
      simpa only [Set.mem_ofPred_eq, Fin.snoc_last] using (show (s : ℝ) < t by exact_mod_cast hfac)

end Work.WilkG4c
