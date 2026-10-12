import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.chatSqDefs
import Submission.Work.BoseRowQ2.chiHatSq_tsum_le
import Submission.Work.BoseRowQ2.chiLatticeParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chatTailAux` — the lattice vocabulary of the `Tail` quadratic form

The mask row of FS l.3253 decomposes `Gop ⪯ Σ_k a_k†a_k + (correction)` with the
correction carried by the *lattice tail* matrix

    `Tail N i j = Mc N i j − ∑_k Chat N k i · Chat N k j`,
    `Mc N i j = χ̂²(vec (K i − K j))`,  `Chat N k i = χ̂(vec (K k − K i))`

(`K = labVec : Lab N → ℤ³`, `χ̂(p) = ∫χ cos⟪p,x⟫`, `χ̂²(p) = ∫χ² cos⟪p,x⟫`).  This module
sets up the vocabulary of the quadratic form of `Tail` on the vector `Chat w`:

* `ChatW N w k = ∑_i Chat N k i · w i` — the vector the row applies `Tail` to;
* `Fhat N w k` — its identification with the Fourier coefficients of `χW` on the full
  lattice, `W(x) = ∑_i w i e^{i⟪K i,x⟫}`:  `ChatW N w k = Fhat N w (K k)`;
* `highMode N w m = ∑_k ChatW N w k · χ̂(vec (m − K k))` — the "high-mode" coefficients
  `ĝ(m)` of `g = χ·(low part of χW)`: the quadratic form of `Tail` is the sum of
  `highMode`² over the *lattice points outside the cube* (`cube N = [−N,N]³ ∩ ℤ³`);
* `highIdeal N w m = ∑_i w i χ̂²(vec (m − K i))` — the ideal high-mode coefficient
  `(χ²W)^m`;
* `highErr` / `nu` — the truncation error `(χ²W)^m − ĝ(m)` and its `ℓ¹`-mass.

All the declarations of this module are elementary rewriting; the two analytic inputs
(the shifted lattice Parseval identity `shifted_parseval` for the first, and the
lattice-tail bounds of the sibling modules for the estimates) are imported.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Z3" => Fin 3 → ℤ

/-! ## 1. The vocabulary -/

/-- The vector `Chat w` of the mask row: `c k = ∑_i χ̂(vec (K k − K i)) w i`. -/
noncomputable def ChatW (N : ℕ) (w : Lab N → ℝ) (k : Lab N) : ℝ :=
  ∑ i : Lab N, Chat N k i * w i

/-- The Fourier coefficients of `χW` on the full lattice `ℤ³`: `F̂(k) = ∑_i w i χ̂(vec (k − K i))`. -/
noncomputable def Fhat (N : ℕ) (w : Lab N → ℝ) (k : Z3) : ℝ :=
  ∑ i : Lab N, w i * chiHat (Work.BoseB4.vec (k - labVec N i))

/-- The "high-mode" coefficient `ĝ(m) = ∑_k c k · χ̂(vec (m − K k))` of `g = χ·P`, where `P` is
the partial sum of the Fourier series of `χW` over the cube modes. -/
noncomputable def highMode (N : ℕ) (w : Lab N → ℝ) (m : Z3) : ℝ :=
  ∑ k : Lab N, ChatW N w k * chiHat (Work.BoseB4.vec (m - labVec N k))

/-- The ideal high-mode coefficient `(χ²W)^m = ∑_i w i χ̂²(vec (m − K i))`. -/
noncomputable def highIdeal (N : ℕ) (w : Lab N → ℝ) (m : Z3) : ℝ :=
  ∑ i : Lab N, w i * chiHatSq (Work.BoseB4.vec (m - labVec N i))

/-- The truncation error of the coefficient decomposition: `(χ²W)^m − ĝ(m) = ∑_{k ∉ cube} F̂(k) χ̂(vec (m − k))`,
i.e. `highMode = highIdeal − highErr` (see `highMode_eq_ideal_sub_err`). -/
noncomputable def highErr (N : ℕ) (w : Lab N → ℝ) (m : Z3) : ℝ :=
  ∑' k : {k : Z3 // k ∉ cube N}, Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val))

/-- The `ℓ¹`-mass of the high part of `F̂`, the key small quantity. -/
noncomputable def nu (N : ℕ) (w : Lab N → ℝ) : ℝ :=
  ∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|

/-- The inradius-like quantity of the statement. -/
noncomputable def rad (N : ℕ) (L : ℝ) : ℝ := 2 * Real.pi * ((N : ℝ) + 1) - L

/-- The label set carrying `w`. -/
noncomputable def suppW (N : ℕ) (w : Lab N → ℝ) : Finset (Lab N) :=
  Finset.univ.filter (fun i => w i ≠ 0)

/-! ## 2. Elementary identifications -/

/-- `ChatW` at a label is `Fhat` at the label's lattice vector. -/
theorem ChatW_eq_Fhat (N : ℕ) (w : Lab N → ℝ) (k : Lab N) :
    ChatW N w k = Fhat N w (labVec N k) := by
  simp only [ChatW, Fhat, Chat]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The symmetric form of `Chat`. -/
theorem Chat_comm (N : ℕ) (k i : Lab N) : Chat N k i = Chat N i k := by
  have h : Work.BoseB4.vec (labVec N i - labVec N k)
      = -Work.BoseB4.vec (labVec N k - labVec N i) := by
    rw [vec_sub, vec_sub]
    abel
  simp only [Chat]
  rw [h, chiHat_neg]

/-- `highMode` at a cube label is the matrix product with `Chat`. -/
theorem highMode_labVec (N : ℕ) (w : Lab N → ℝ) (j : Lab N) :
    highMode N w (labVec N j) = ∑ k : Lab N, ChatW N w k * Chat N j k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Chat]

/-- The quadratic form of `ChatᵀChat` on `ChatW` is the low-mode part of `highMode`. -/
theorem sum_chatTchat (N : ℕ) (w : Lab N → ℝ) :
    (∑ j : Lab N, (∑ k : Lab N, Chat N j k * ChatW N w k) ^ 2)
      = ∑ j : Lab N, highMode N w (labVec N j) ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [highMode_labVec]
  refine congrArg (fun t => t ^ 2) ?_
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The quadratic form of `Tail` on `ChatW` splits into the `Mc`-form minus the
`ChatᵀChat`-form. -/
theorem chatTail_quad_eq (N : ℕ) (w : Lab N → ℝ) :
    (∑ k : Lab N, ∑ j : Lab N,
        ChatW N w k * ChatW N w j * Tail N k j)
      = (∑ k : Lab N, ∑ j : Lab N, ChatW N w k * ChatW N w j * Mc N k j)
        - ∑ j : Lab N, highMode N w (labVec N j) ^ 2 := by
  have hT : ∀ k j : Lab N,
      Tail N k j = Mc N k j - ∑ l : Lab N, Chat N l k * Chat N l j := fun k j => rfl
  have hexp : ∀ k : Lab N, (∑ j : Lab N, ChatW N w k * ChatW N w j * Tail N k j)
      = (∑ j : Lab N, ChatW N w k * ChatW N w j * Mc N k j)
        - (∑ j : Lab N, ChatW N w k * ChatW N w j
            * (∑ l : Lab N, Chat N l k * Chat N l j)) := by
    intro k
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT k j, mul_sub]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => hexp k) ?_
  rw [Finset.sum_sub_distrib]
  have hB : (∑ k : Lab N, ∑ j : Lab N, ChatW N w k * ChatW N w j
      * (∑ l : Lab N, Chat N l k * Chat N l j))
      = ∑ j : Lab N, highMode N w (labVec N j) ^ 2 := by
    have hstep1 : (∑ k : Lab N, ∑ j : Lab N, ChatW N w k * ChatW N w j
        * (∑ l : Lab N, Chat N l k * Chat N l j))
        = ∑ k : Lab N, ∑ l : Lab N, ∑ j : Lab N,
            (Chat N l k * ChatW N w k) * (Chat N l j * ChatW N w j) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hstep2 : (∑ k : Lab N, ∑ l : Lab N, ∑ j : Lab N,
            (Chat N l k * ChatW N w k) * (Chat N l j * ChatW N w j))
        = ∑ l : Lab N, (∑ k : Lab N, Chat N l k * ChatW N w k) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_two, Finset.sum_mul_sum]
    rw [hstep1, hstep2]
    exact sum_chatTchat N w
  rw [hB]

/-! ## 3. Geometry of the cube -/

theorem vec_component (v : Z3) (i : Fin 3) :
    (Work.BoseB4.vec v) i = 2 * Real.pi * (v i : ℝ) := by
  simp [Work.BoseB4.vec]

/-- **The geometric input of the tail estimates.**  If `m` is a lattice point *outside* the
cube `[−N,N]³` and `‖vec i‖ ≤ L`, then the shifted momentum satisfies
`‖vec (m − i)‖ ≥ 2π(N+1) − L`. -/
theorem exists_abs_component_ge {N : ℕ} {m : Z3} (hm : m ∉ cube N) :
    ∃ j : Fin 3, ((N : ℤ) + 1) ≤ |m j| := by
  have h : ¬ ∀ i, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) := by
    intro hc
    exact hm (mem_cube.mpr hc)
  obtain ⟨j, hj⟩ := not_forall.mp h
  refine ⟨j, ?_⟩
  rcases (not_and_or.mp hj) with h1 | h2
  · have : m j < -(N : ℤ) := not_le.mp h1
    rw [abs_of_neg (by omega)]; omega
  · have : (N : ℤ) < m j := not_le.mp h2
    rw [abs_of_pos (by omega)]; omega

theorem rad_le_norm_vec_sub {N : ℕ} {L : ℝ} {m i : Z3} (hm : m ∉ cube N)
    (hi : ‖Work.BoseB4.vec i‖ ≤ L) :
    rad N L ≤ ‖Work.BoseB4.vec (m - i)‖ := by
  obtain ⟨j, hj⟩ := exists_abs_component_ge hm
  have hjR : ((N : ℝ) + 1) ≤ |((m j : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hj
  have hcomp : |Work.BoseB4.vec (m - i) j| ≤ ‖Work.BoseB4.vec (m - i)‖ :=
    PiLp.norm_apply_le (Work.BoseB4.vec (m - i)) j
  have hvec : Work.BoseB4.vec (m - i) = Work.BoseB4.vec m - Work.BoseB4.vec i :=
    vec_sub m i
  have hcomp2 : |Work.BoseB4.vec (m - i) j|
      = 2 * Real.pi * |((m j : ℤ) : ℝ) - ((i j : ℤ) : ℝ)| := by
    rw [hvec, PiLp.sub_apply, vec_component, vec_component, ← mul_sub, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hi2 : 2 * Real.pi * |((i j : ℤ) : ℝ)| ≤ L := by
    have h1 : |(Work.BoseB4.vec i) j| ≤ ‖Work.BoseB4.vec i‖ :=
      PiLp.norm_apply_le (Work.BoseB4.vec i) j
    have h2 : |(Work.BoseB4.vec i) j| = 2 * Real.pi * |((i j : ℤ) : ℝ)| := by
      rw [vec_component, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [h2] at h1
    linarith
  have h1 : 2 * Real.pi * ((N : ℝ) + 1) - L
      ≤ 2 * Real.pi * (((N : ℝ) + 1) - |((i j : ℤ) : ℝ)|) := by
    have h2 : 2 * Real.pi * |((i j : ℤ) : ℝ)| ≤ L := hi2
    linarith
  have h3 : ((N : ℝ) + 1) - |((i j : ℤ) : ℝ)| ≤ |((m j : ℤ) : ℝ)| - |((i j : ℤ) : ℝ)| :=
    sub_le_sub_right hjR _
  have h4 : |((m j : ℤ) : ℝ)| - |((i j : ℤ) : ℝ)| ≤ |((m j : ℤ) : ℝ) - ((i j : ℤ) : ℝ)| :=
    abs_sub_abs_le_abs_sub _ _
  rw [rad]
  calc 2 * Real.pi * ((N : ℝ) + 1) - L
      ≤ 2 * Real.pi * (((N : ℝ) + 1) - |((i j : ℤ) : ℝ)|) := h1
    _ ≤ 2 * Real.pi * (|((m j : ℤ) : ℝ)| - |((i j : ℤ) : ℝ)|) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 2 * Real.pi * |((m j : ℤ) : ℝ) - ((i j : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = |Work.BoseB4.vec (m - i) j| := hcomp2.symm
    _ ≤ ‖Work.BoseB4.vec (m - i)‖ := hcomp

/-- A lattice point outside the cube has momentum at least `2π(N+1)`. -/
theorem norm_vec_ge_of_notMem_cube {N : ℕ} {m : Z3} (hm : m ∉ cube N) :
    2 * Real.pi * ((N : ℝ) + 1) ≤ ‖Work.BoseB4.vec m‖ := by
  obtain ⟨j, hj⟩ := exists_abs_component_ge hm
  have hjR : ((N : ℝ) + 1) ≤ |((m j : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hj
  have hcomp : |(Work.BoseB4.vec m) j| ≤ ‖Work.BoseB4.vec m‖ :=
    PiLp.norm_apply_le (Work.BoseB4.vec m) j
  have hvec : |(Work.BoseB4.vec m) j| = 2 * Real.pi * |((m j : ℤ) : ℝ)| := by
    rw [vec_component, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [hvec] at hcomp
  calc 2 * Real.pi * ((N : ℝ) + 1) ≤ 2 * Real.pi * |((m j : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_left hjR (by positivity)
    _ ≤ ‖Work.BoseB4.vec m‖ := hcomp

end Work.BoseRowQ2
