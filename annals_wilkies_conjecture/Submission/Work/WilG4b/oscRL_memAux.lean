/-
  WilG4bF — `oscRL_mem`: the one-sided oscillation sets of an `Ω`-definable unary function are
  `Ω`-definable, *uniformly in the slope* `q`.

  ## What is proved

  For `g : ℝ → ℝ` whose graph is an `Ω`-set of format `F` and degree `D` in `ℝ²`, there are a
  numeral `K` (here `700`) and a polynomial `p` (here `2 * (C 4 + Qpoly)`) such that for **every**
  real `q`

      `{x | x ∈ oscR g q}`  and  `{x | x ∈ oscL g q}`  lie in  `Ω (F + K) (p.eval D) 1`,

  where `oscR`/`oscL` are the one-sided oscillation sets of `Work.WilG1` (defined through the
  difference quotient `dq g x y = (g y - g x)/(y - x)`).

  ## The shape of the argument

  `oscR g q` is the conjunction of two *first-order* conditions on the graph of `g`:

      x ∈ oscR g q  ↔  (∀δ>0 ∃y, x<y<x+δ ∧ q < dq g x y) ∧ (∀δ>0 ∃y, x<y<x+δ ∧ dq g x y < q),

  and `oscL g q` is the same with `x-δ < y < x`.  Each of the four conditions is realised as an
  `Ω`-shape on the five coordinates `(x, δ, y, u, v)` with `u = g x`, `v = g y`:

  * the *core* `coreP g Ps Pw Pc` collects the two graph atoms `u = g x`, `v = g y`, the two
    linear atoms cut out by `Ps` (side) and `Pw` (width), and the strict inequality cut out by
    `Pc`.  On `y > x` the quotient condition `q < dq` is *polynomial*: it is the positivity of
    `(v-u) - q(y-x)` (`shiftHiP q`), dually `dq < q` is the positivity of `q(y-x) - (v-u)`
    (`shiftLoP q`).  On `y < x` the roles of the two shift polynomials are exchanged (the
    denominator is negative), which is the only difference between the "R" and the "L" shapes.
  * `bodyP = projN 3 coreP` existentially quantifies `(y,u,v)`, leaving the pair `(x,δ)`;
  * intersecting with `posU2 = {0 < δ}`, complementing and projecting out `δ` produces the
    *negated* shape `W`, whose complement is exactly the `∀δ>0 ∃y` condition.

  Both the core membership and the semantic identification are proved here from the generic
  `Ω`-calculus alone (`SOMin` axioms via `Work.WilG1.Omega`, the positivity of a polynomial via
  `Work.WilG4b.posPoly_mem`, coordinate pullbacks via `Work.WilG5`).  The vocabulary of shapes
  (`coreP`, `bodyP`, `WHi`, …) is the shared one of `Work.WilG4b.osc_defs`.

  The format `F + 700` and the degree polynomial `p` are uniform in `q` because `q` occurs in
  the shift polynomials only as a *coefficient*: `(shiftHiP q).totalDegree ≤ 1` for every `q`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG4b.osc_defs
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4b.MeasBound.levelSet_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical

namespace Work.WilG4bF

open WilkiesDesign WilkiesConjecture

/-! ## 1. Coordinates of the layouts `Fin 5 = Fin 2 ⊕ Fin 3` and `Fin 2 = Fin 1 ⊕ Fin 1` -/

theorem append5_zero (x : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (Fin.append x w : Fin 5 → ℝ) 0 = x 0 := by
  have h : (0 : Fin 5) = Fin.castAdd 3 (0 : Fin 2) := Fin.ext rfl
  rw [h, Fin.append_left]

theorem append5_one (x : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (Fin.append x w : Fin 5 → ℝ) 1 = x 1 := by
  have h : (1 : Fin 5) = Fin.castAdd 3 (1 : Fin 2) := Fin.ext rfl
  rw [h, Fin.append_left]

theorem append5_two (x : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (Fin.append x w : Fin 5 → ℝ) 2 = w 0 := by
  have h : (2 : Fin 5) = Fin.natAdd 2 (0 : Fin 3) := Fin.ext rfl
  rw [h, Fin.append_right]

theorem append5_three (x : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (Fin.append x w : Fin 5 → ℝ) 3 = w 1 := by
  have h : (3 : Fin 5) = Fin.natAdd 2 (1 : Fin 3) := Fin.ext rfl
  rw [h, Fin.append_right]

theorem append5_four (x : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    (Fin.append x w : Fin 5 → ℝ) 4 = w 2 := by
  have h : (4 : Fin 5) = Fin.natAdd 2 (2 : Fin 3) := Fin.ext rfl
  rw [h, Fin.append_right]

theorem snoc2_zero (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 0 = z 0 := by
  have h : (0 : Fin 2) = Fin.castSucc (0 : Fin 1) := Fin.ext rfl
  rw [h, Fin.snoc_castSucc]

theorem snoc2_one (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 1 = t := by
  have h : (1 : Fin 2) = Fin.last 1 := Fin.ext rfl
  rw [h, Fin.snoc_last]

/-- A three-vector, written so that its coordinates compute by `simp`. -/
def vec3 (a b c : ℝ) : Fin 3 → ℝ := fun j => if j = 0 then a else if j = 1 then b else c

theorem vec3_zero (a b c : ℝ) : vec3 a b c 0 = a := by simp [vec3]

theorem vec3_one (a b c : ℝ) : vec3 a b c 1 = b := by simp [vec3]

theorem vec3_two (a b c : ℝ) : vec3 a b c 2 = c := by simp [vec3]

theorem iotaA_zero : Work.WilG4b.iotaA 0 = (0 : Fin 5) := by decide

theorem iotaA_one : Work.WilG4b.iotaA 1 = (3 : Fin 5) := by decide

theorem iotaB_zero : Work.WilG4b.iotaB 0 = (2 : Fin 5) := by decide

theorem iotaB_one : Work.WilG4b.iotaB 1 = (4 : Fin 5) := by decide

/-! ## 2. Evaluating the config polynomials -/

theorem eval_sideP5 (z : Fin 5 → ℝ) :
    MvPolynomial.eval z Work.WilG4b.sideP5 = z 2 - z 0 := by
  simp [Work.WilG4b.sideP5]

theorem eval_sideP5L (z : Fin 5 → ℝ) :
    MvPolynomial.eval z Work.WilG4b.sideP5L = z 0 - z 2 := by
  simp [Work.WilG4b.sideP5L]

theorem eval_widthP5 (z : Fin 5 → ℝ) :
    MvPolynomial.eval z Work.WilG4b.widthP5 = z 1 - z 2 + z 0 := by
  simp [Work.WilG4b.widthP5]

theorem eval_widthP5L (z : Fin 5 → ℝ) :
    MvPolynomial.eval z Work.WilG4b.widthP5L = z 2 - z 0 + z 1 := by
  simp [Work.WilG4b.widthP5L]

theorem eval_shiftHiP (q : ℝ) (z : Fin 5 → ℝ) :
    MvPolynomial.eval z (Work.WilG4b.shiftHiP q) = z 4 - z 3 - q * (z 2 - z 0) := by
  simp [Work.WilG4b.shiftHiP]

theorem eval_shiftLoP (q : ℝ) (z : Fin 5 → ℝ) :
    MvPolynomial.eval z (Work.WilG4b.shiftLoP q) = q * (z 2 - z 0) - (z 4 - z 3) := by
  simp [Work.WilG4b.shiftLoP]

/-! ## 3. Unfolding the core -/

theorem mem_atomA (g : ℝ → ℝ) (z : Fin 5 → ℝ) :
    z ∈ Work.WilG4b.atomA g ↔ z 3 = g (z 0) := by
  rw [Work.WilG4b.atomA, Work.WilG5.coordPre, Set.mem_ofPred_eq, Work.WilG4b.Ggraph,
    Work.WilG4b.MeasBound.mem_graphOf_one]
  simp only [Function.comp_apply, iotaA_zero, iotaA_one]

theorem mem_atomB (g : ℝ → ℝ) (z : Fin 5 → ℝ) :
    z ∈ Work.WilG4b.atomB g ↔ z 4 = g (z 2) := by
  rw [Work.WilG4b.atomB, Work.WilG5.coordPre, Set.mem_ofPred_eq, Work.WilG4b.Ggraph,
    Work.WilG4b.MeasBound.mem_graphOf_one]
  simp only [Function.comp_apply, iotaB_zero, iotaB_one]

/-- Membership in the five-atom core, in coordinates. -/
theorem mem_coreP (g : ℝ → ℝ) (Ps Pw Pc : MvPolynomial (Fin 5) ℝ) (z : Fin 5 → ℝ) :
    z ∈ Work.WilG4b.coreP g Ps Pw Pc ↔
      z 3 = g (z 0) ∧ z 4 = g (z 2) ∧ 0 < MvPolynomial.eval z Ps ∧
        0 < MvPolynomial.eval z Pw ∧ 0 < MvPolynomial.eval z Pc := by
  simp only [Work.WilG4b.coreP, Work.WilG4b.posOf, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_atomA, mem_atomB]
  tauto

/-! ## 4. The bodies, in coordinates -/

theorem mem_bodyHi_iff (g : ℝ → ℝ) (q : ℝ) (δ : ℝ) (z : Fin 1 → ℝ) :
    (Fin.snoc z δ : Fin 2 → ℝ) ∈ Work.WilG4b.bodyHi g q ↔
      ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ q < Work.WilG1.dq g (z 0) y := by
  rw [Work.WilG4b.bodyHi, Work.WilG4b.bodyP, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_coreP] at hw
    obtain ⟨h1, h2, hs, hwd, hc⟩ := hw
    simp only [eval_sideP5, eval_widthP5, eval_shiftHiP, append5_zero, append5_one,
      append5_two, append5_three, append5_four, snoc2_zero, snoc2_one] at h1 h2 hs hwd hc
    refine ⟨w 0, by linarith, by linarith, ?_⟩
    have hpos : 0 < w 0 - z 0 := by linarith
    have hkey : q * (w 0 - z 0) < g (w 0) - g (z 0) := by
      rw [h1, h2] at hc
      linarith
    rw [Work.WilG1.dq, lt_div_iff₀ hpos]
    exact hkey
  · rintro ⟨y, hy1, hy2, hq⟩
    refine ⟨vec3 y (g (z 0)) (g y), ?_⟩
    rw [mem_coreP]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [append5_zero, append5_three, vec3_one, snoc2_zero]
    · simp only [append5_two, append5_four, vec3_zero, vec3_two]
    · simp only [eval_sideP5, append5_zero, append5_two, vec3_zero, snoc2_zero]
      linarith
    · simp only [eval_widthP5, append5_zero, append5_one, append5_two, vec3_zero,
        snoc2_zero, snoc2_one]
      linarith
    · have hpos : 0 < y - z 0 := by linarith
      have hkey : q * (y - z 0) < g y - g (z 0) := by
        rw [Work.WilG1.dq, lt_div_iff₀ hpos] at hq
        exact hq
      simp only [eval_shiftHiP, append5_zero, append5_two, append5_three, append5_four,
        vec3_zero, vec3_one, vec3_two, snoc2_zero, snoc2_one]
      linarith

theorem mem_bodyLo_iff (g : ℝ → ℝ) (q : ℝ) (δ : ℝ) (z : Fin 1 → ℝ) :
    (Fin.snoc z δ : Fin 2 → ℝ) ∈ Work.WilG4b.bodyLo g q ↔
      ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ Work.WilG1.dq g (z 0) y < q := by
  rw [Work.WilG4b.bodyLo, Work.WilG4b.bodyP, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_coreP] at hw
    obtain ⟨h1, h2, hs, hwd, hc⟩ := hw
    simp only [eval_sideP5, eval_widthP5, eval_shiftLoP, append5_zero, append5_one,
      append5_two, append5_three, append5_four, snoc2_zero, snoc2_one] at h1 h2 hs hwd hc
    refine ⟨w 0, by linarith, by linarith, ?_⟩
    have hpos : 0 < w 0 - z 0 := by linarith
    have hkey : g (w 0) - g (z 0) < q * (w 0 - z 0) := by
      rw [h1, h2] at hc
      linarith
    rw [Work.WilG1.dq, div_lt_iff₀ hpos]
    exact hkey
  · rintro ⟨y, hy1, hy2, hq⟩
    refine ⟨vec3 y (g (z 0)) (g y), ?_⟩
    rw [mem_coreP]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [append5_zero, append5_three, vec3_one, snoc2_zero]
    · simp only [append5_two, append5_four, vec3_zero, vec3_two]
    · simp only [eval_sideP5, append5_zero, append5_two, vec3_zero, snoc2_zero]
      linarith
    · simp only [eval_widthP5, append5_zero, append5_one, append5_two, vec3_zero,
        snoc2_zero, snoc2_one]
      linarith
    · have hpos : 0 < y - z 0 := by linarith
      have hkey : g y - g (z 0) < q * (y - z 0) := by
        rw [Work.WilG1.dq, div_lt_iff₀ hpos] at hq
        exact hq
      simp only [eval_shiftLoP, append5_zero, append5_two, append5_three, append5_four,
        vec3_zero, vec3_one, vec3_two, snoc2_zero, snoc2_one]
      linarith

theorem mem_bodyHiL_iff (g : ℝ → ℝ) (q : ℝ) (δ : ℝ) (z : Fin 1 → ℝ) :
    (Fin.snoc z δ : Fin 2 → ℝ) ∈ Work.WilG4b.bodyHiL g q ↔
      ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ q < Work.WilG1.dq g (z 0) y := by
  rw [Work.WilG4b.bodyHiL, Work.WilG4b.bodyP, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_coreP] at hw
    obtain ⟨h1, h2, hs, hwd, hc⟩ := hw
    simp only [eval_sideP5L, eval_widthP5L, eval_shiftLoP, append5_zero, append5_one,
      append5_two, append5_three, append5_four, snoc2_zero, snoc2_one] at h1 h2 hs hwd hc
    refine ⟨w 0, by linarith, by linarith, ?_⟩
    have hneg : w 0 - z 0 < 0 := by linarith
    have hkey : g (w 0) - g (z 0) < q * (w 0 - z 0) := by
      rw [h1, h2] at hc
      linarith
    rw [Work.WilG1.dq, lt_div_iff_of_neg hneg]
    exact hkey
  · rintro ⟨y, hy1, hy2, hq⟩
    refine ⟨vec3 y (g (z 0)) (g y), ?_⟩
    rw [mem_coreP]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [append5_zero, append5_three, vec3_one, snoc2_zero]
    · simp only [append5_two, append5_four, vec3_zero, vec3_two]
    · simp only [eval_sideP5L, append5_zero, append5_two, vec3_zero, snoc2_zero]
      linarith
    · simp only [eval_widthP5L, append5_zero, append5_one, append5_two, vec3_zero,
        snoc2_zero, snoc2_one]
      linarith
    · have hneg : y - z 0 < 0 := by linarith
      have hkey : g y - g (z 0) < q * (y - z 0) := by
        rw [Work.WilG1.dq, lt_div_iff_of_neg hneg] at hq
        exact hq
      simp only [eval_shiftLoP, append5_zero, append5_two, append5_three, append5_four,
        vec3_zero, vec3_one, vec3_two, snoc2_zero, snoc2_one]
      linarith

theorem mem_bodyLoL_iff (g : ℝ → ℝ) (q : ℝ) (δ : ℝ) (z : Fin 1 → ℝ) :
    (Fin.snoc z δ : Fin 2 → ℝ) ∈ Work.WilG4b.bodyLoL g q ↔
      ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ Work.WilG1.dq g (z 0) y < q := by
  rw [Work.WilG4b.bodyLoL, Work.WilG4b.bodyP, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_coreP] at hw
    obtain ⟨h1, h2, hs, hwd, hc⟩ := hw
    simp only [eval_sideP5L, eval_widthP5L, eval_shiftHiP, append5_zero, append5_one,
      append5_two, append5_three, append5_four, snoc2_zero, snoc2_one] at h1 h2 hs hwd hc
    refine ⟨w 0, by linarith, by linarith, ?_⟩
    have hneg : w 0 - z 0 < 0 := by linarith
    have hkey : q * (w 0 - z 0) < g (w 0) - g (z 0) := by
      rw [h1, h2] at hc
      linarith
    rw [Work.WilG1.dq, div_lt_iff_of_neg hneg]
    exact hkey
  · rintro ⟨y, hy1, hy2, hq⟩
    refine ⟨vec3 y (g (z 0)) (g y), ?_⟩
    rw [mem_coreP]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [append5_zero, append5_three, vec3_one, snoc2_zero]
    · simp only [append5_two, append5_four, vec3_zero, vec3_two]
    · simp only [eval_sideP5L, append5_zero, append5_two, vec3_zero, snoc2_zero]
      linarith
    · simp only [eval_widthP5L, append5_zero, append5_one, append5_two, vec3_zero,
        snoc2_zero, snoc2_one]
      linarith
    · have hneg : y - z 0 < 0 := by linarith
      have hkey : q * (y - z 0) < g y - g (z 0) := by
        rw [Work.WilG1.dq, div_lt_iff_of_neg hneg] at hq
        exact hq
      simp only [eval_shiftHiP, append5_zero, append5_two, append5_three, append5_four,
        vec3_zero, vec3_one, vec3_two, snoc2_zero, snoc2_one]
      linarith

/-! ## 5. The complement of a shape is the `∀δ>0 ∃y` condition -/

theorem compl_W_general (B : Set (Fin 2 → ℝ)) (P : (Fin 1 → ℝ) → ℝ → Prop)
    (hB : ∀ (z : Fin 1 → ℝ) (δ : ℝ), (Fin.snoc z δ : Fin 2 → ℝ) ∈ B ↔ P z δ) :
    (projLast (Work.WilG4b.posU2 ∩ Bᶜ))ᶜ = {z : Fin 1 → ℝ | ∀ δ : ℝ, 0 < δ → P z δ} := by
  ext z
  simp only [Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, not_exists,
    Work.WilG4b.posU2, snoc2_one]
  constructor
  · intro h δ hδ
    exact (hB z δ).mp (not_not.mp (not_and.mp (h δ) hδ))
  · rintro h t ⟨ht1, ht2⟩
    exact ht2 ((hB z t).mpr (h t ht1))

theorem compl_WHi (g : ℝ → ℝ) (q : ℝ) :
    (Work.WilG4b.WHi g q)ᶜ = Work.WilG4b.HighR g q := by
  rw [Work.WilG4b.WHi, Work.WilG4b.HighR]
  exact compl_W_general (Work.WilG4b.bodyHi g q)
    (fun z δ => ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ q < Work.WilG1.dq g (z 0) y)
    (fun z δ => mem_bodyHi_iff g q δ z)

theorem compl_WLo (g : ℝ → ℝ) (q : ℝ) :
    (Work.WilG4b.WLo g q)ᶜ = Work.WilG4b.LowR g q := by
  rw [Work.WilG4b.WLo, Work.WilG4b.LowR]
  exact compl_W_general (Work.WilG4b.bodyLo g q)
    (fun z δ => ∃ y : ℝ, z 0 < y ∧ y < z 0 + δ ∧ Work.WilG1.dq g (z 0) y < q)
    (fun z δ => mem_bodyLo_iff g q δ z)

theorem compl_WHiL (g : ℝ → ℝ) (q : ℝ) :
    (Work.WilG4b.WHiL g q)ᶜ = Work.WilG4b.HighL g q := by
  rw [Work.WilG4b.WHiL, Work.WilG4b.HighL]
  exact compl_W_general (Work.WilG4b.bodyHiL g q)
    (fun z δ => ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ q < Work.WilG1.dq g (z 0) y)
    (fun z δ => mem_bodyHiL_iff g q δ z)

theorem compl_WLoL (g : ℝ → ℝ) (q : ℝ) :
    (Work.WilG4b.WLoL g q)ᶜ = Work.WilG4b.LowL g q := by
  rw [Work.WilG4b.WLoL, Work.WilG4b.LowL]
  exact compl_W_general (Work.WilG4b.bodyLoL g q)
    (fun z δ => ∃ y : ℝ, z 0 - δ < y ∧ y < z 0 ∧ Work.WilG1.dq g (z 0) y < q)
    (fun z δ => mem_bodyLoL_iff g q δ z)

/-! ## 6. Degree bounds of the config polynomials -/

theorem td_sideP5 : Work.WilG4b.sideP5.totalDegree ≤ 1 := by
  rw [Work.WilG4b.sideP5]
  exact le_trans (MvPolynomial.totalDegree_sub _ _)
    (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))

theorem td_sideP5L : Work.WilG4b.sideP5L.totalDegree ≤ 1 := by
  rw [Work.WilG4b.sideP5L]
  exact le_trans (MvPolynomial.totalDegree_sub _ _)
    (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))

theorem td_widthP5 : Work.WilG4b.widthP5.totalDegree ≤ 1 := by
  rw [Work.WilG4b.widthP5]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  exact max_le (le_trans (MvPolynomial.totalDegree_sub _ _)
    (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))) (Work.WilG5.td_X_le _)

theorem td_widthP5L : Work.WilG4b.widthP5L.totalDegree ≤ 1 := by
  rw [Work.WilG4b.widthP5L]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  exact max_le (le_trans (MvPolynomial.totalDegree_sub _ _)
    (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))) (Work.WilG5.td_X_le _)

theorem td_shiftHiP (q : ℝ) : (Work.WilG4b.shiftHiP q).totalDegree ≤ 1 := by
  rw [Work.WilG4b.shiftHiP]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  refine max_le ?_ ?_
  · exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))

theorem td_shiftLoP (q : ℝ) : (Work.WilG4b.shiftLoP q).totalDegree ≤ 1 := by
  rw [Work.WilG4b.shiftLoP]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))
  · exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))

/-! ## 7. `Ω`-membership of the core, the body and the shape -/

/-- The degree polynomial carried by the core sets (uniform in `q`). -/
def Qpoly : Polynomial ℕ := Polynomial.C 8 * (Polynomial.X + Polynomial.C 500)

/-- `posU2 = {0 < w 1}` is `Ω`-definable with numeral format and degree. -/
theorem posU2_mem (S : SOMin) (d : ℕ) :
    Work.WilG4b.posU2 ∈ S.Ω 6 ((Polynomial.C 4).eval d) 2 := by
  have h : {x : Fin 2 → ℝ | 0 < MvPolynomial.eval x (MvPolynomial.X (1 : Fin 2))}
      ∈ S.Ω (2 + 4) ((MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree + 3) 2 :=
    Work.WilG4b.posPoly_mem S (MvPolynomial.X (1 : Fin 2))
  have hset : {x : Fin 2 → ℝ | 0 < MvPolynomial.eval x (MvPolynomial.X (1 : Fin 2))}
      = Work.WilG4b.posU2 := by
    ext x
    simp [Work.WilG4b.posU2]
  rw [hset] at h
  refine Work.WilG5.mem_mono h 6 ((Polynomial.C 4).eval d) (by omega) ?_
  show (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree + 3 ≤ (Polynomial.C 4).eval d
  simp [Polynomial.eval_C]

/-- The five-atom core of any three degree-`≤ 1` config polynomials is `Ω`-definable. -/
theorem coreP_omega (S : SOMin) {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2)
    (Ps Pw Pc : MvPolynomial (Fin 5) ℝ) (hPs : Ps.totalDegree ≤ 1)
    (hPw : Pw.totalDegree ≤ 1) (hPc : Pc.totalDegree ≤ 1) :
    Work.WilG4b.coreP g Ps Pw Pc ∈ S.Ω (F + 600) (Qpoly.eval D) 5 := by
  have hAG : Work.WilG4b.atomA g ∈
      S.Ω (F + 512) ((Polynomial.X + Polynomial.C 256).eval D) 5 := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := 2) (N := 5) (F := F) (D := D)
      (ι := Work.WilG4b.iotaA) (A := Work.WilG4b.Ggraph g) hg
    refine Work.WilG5.mem_mono h (F + 512) ((Polynomial.X + Polynomial.C 256).eval D)
      (by omega) ?_
    simp [Polynomial.eval_add]
  have hBG : Work.WilG4b.atomB g ∈
      S.Ω (F + 512) ((Polynomial.X + Polynomial.C 256).eval D) 5 := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := 2) (N := 5) (F := F) (D := D)
      (ι := Work.WilG4b.iotaB) (A := Work.WilG4b.Ggraph g) hg
    refine Work.WilG5.mem_mono h (F + 512) ((Polynomial.X + Polynomial.C 256).eval D)
      (by omega) ?_
    simp [Polynomial.eval_add]
  have hS : Work.WilG4b.posOf Ps ∈ S.Ω 9 ((Polynomial.C (Ps.totalDegree + 3)).eval D) 5 := by
    have h : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Ps}
        ∈ S.Ω (5 + 4) (Ps.totalDegree + 3) 5 := Work.WilG4b.posPoly_mem S Ps
    have hset : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Ps} = Work.WilG4b.posOf Ps := rfl
    rw [hset] at h
    refine Work.WilG5.mem_mono h 9 ((Polynomial.C (Ps.totalDegree + 3)).eval D) (by omega) ?_
    rw [Polynomial.eval_C]
  have hW : Work.WilG4b.posOf Pw ∈ S.Ω 9 ((Polynomial.C (Pw.totalDegree + 3)).eval D) 5 := by
    have h : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Pw}
        ∈ S.Ω (5 + 4) (Pw.totalDegree + 3) 5 := Work.WilG4b.posPoly_mem S Pw
    have hset : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Pw} = Work.WilG4b.posOf Pw := rfl
    rw [hset] at h
    refine Work.WilG5.mem_mono h 9 ((Polynomial.C (Pw.totalDegree + 3)).eval D) (by omega) ?_
    rw [Polynomial.eval_C]
  have hC : Work.WilG4b.posOf Pc ∈ S.Ω 9 ((Polynomial.C (Pc.totalDegree + 3)).eval D) 5 := by
    have h : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Pc}
        ∈ S.Ω (5 + 4) (Pc.totalDegree + 3) 5 := Work.WilG4b.posPoly_mem S Pc
    have hset : {x : Fin 5 → ℝ | 0 < MvPolynomial.eval x Pc} = Work.WilG4b.posOf Pc := rfl
    rw [hset] at h
    refine Work.WilG5.mem_mono h 9 ((Polynomial.C (Pc.totalDegree + 3)).eval D) (by omega) ?_
    rw [Polynomial.eval_C]
  have h1 := Work.WilG1.Omega.inter₂ (S := S) hAG hBG
  have h2 := Work.WilG1.Omega.inter₂ (S := S) h1 hS
  have h3 := Work.WilG1.Omega.inter₂ (S := S) h2 hW
  have h4 := Work.WilG1.Omega.inter₂ (S := S) h3 hC
  refine Work.WilG5.mem_mono h4 (F + 600) (Qpoly.eval D) (by omega) ?_
  simp only [Qpoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C]
  omega

/-- The negated shape `projLast (posU2 ∩ bodyᶜ)` built from an `Ω`-definable core. -/
theorem W_omega_of_core {S : SOMin} {a d : ℕ} {X : Set (Fin 5 → ℝ)} {b : Polynomial ℕ}
    (h : X ∈ S.Ω a (b.eval d) 5) :
    projLast (Work.WilG4b.posU2 ∩ (Work.WilG5.projN 3 X)ᶜ) ∈
      S.Ω (max 6 ((a + 3) + 1) + 1 + 1) ((Polynomial.C 4 + b).eval d) 1 := by
  have hbody : Work.WilG5.projN 3 X ∈ S.Ω (a + 3) (b.eval d) 2 :=
    Work.WilG5.projN_mem (S := S) (n := 2) 3 a (b.eval d) h
  have hbodyc : (Work.WilG5.projN 3 X)ᶜ ∈ S.Ω ((a + 3) + 1) (b.eval d) 2 :=
    Work.WilG1.Omega.compl_mem (S := S) hbody
  have hpos : Work.WilG4b.posU2 ∈ S.Ω 6 ((Polynomial.C 4).eval d) 2 := posU2_mem S d
  have hI : Work.WilG4b.posU2 ∩ (Work.WilG5.projN 3 X)ᶜ ∈
      S.Ω (max 6 ((a + 3) + 1) + 1) ((Polynomial.C 4 + b).eval d) 2 :=
    Work.WilG1.Omega.inter₂ (S := S) hpos hbodyc
  exact Work.WilG1.Omega.projLast_mem (S := S) (n := 1)
    (a := max 6 ((a + 3) + 1) + 1) (b := Polynomial.C 4 + b) (D := d) hI

/-! ## 8. The oscillation sets -/

theorem liftR_oscR (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.liftR (Work.WilG1.oscR g q)
      = Work.WilG4b.HighR g q ∩ Work.WilG4b.LowR g q := by
  ext z
  simp only [Work.WilG1.liftR, Work.WilG1.oscR, Work.WilG4b.HighR, Work.WilG4b.LowR,
    Set.mem_ofPred_eq, Set.mem_inter_iff]

theorem liftR_oscL (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.liftR (Work.WilG1.oscL g q)
      = Work.WilG4b.HighL g q ∩ Work.WilG4b.LowL g q := by
  ext z
  simp only [Work.WilG1.liftR, Work.WilG1.oscL, Work.WilG4b.HighL, Work.WilG4b.LowL,
    Set.mem_ofPred_eq, Set.mem_inter_iff]

/-! ## 9. The theorem -/

theorem oscRL_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    ∃ K : ℕ, ∃ p : Polynomial ℕ, ∀ q : ℝ,
      (Work.WilG1.liftR (Work.WilG1.oscR g q) ∈ S.Ω (F + K) (p.eval D) 1) ∧
      (Work.WilG1.liftR (Work.WilG1.oscL g q) ∈ S.Ω (F + K) (p.eval D) 1) := by
  refine ⟨700, (Polynomial.C 4 + Qpoly) + (Polynomial.C 4 + Qpoly), fun q => ⟨?_, ?_⟩⟩
  · have hHi : Work.WilG4b.HighR g q ∈
        S.Ω (max 6 ((F + 600 + 3) + 1) + 1 + 1 + 1) ((Polynomial.C 4 + Qpoly).eval D) 1 := by
      rw [← compl_WHi g q]
      exact Work.WilG1.Omega.compl_mem (S := S)
        (W_omega_of_core (S := S)
          (coreP_omega (S := S) (F := F) (D := D) g hg Work.WilG4b.sideP5 Work.WilG4b.widthP5
            (Work.WilG4b.shiftHiP q) td_sideP5 td_widthP5 (td_shiftHiP q)))
    have hLo : Work.WilG4b.LowR g q ∈
        S.Ω (max 6 ((F + 600 + 3) + 1) + 1 + 1 + 1) ((Polynomial.C 4 + Qpoly).eval D) 1 := by
      rw [← compl_WLo g q]
      exact Work.WilG1.Omega.compl_mem (S := S)
        (W_omega_of_core (S := S)
          (coreP_omega (S := S) (F := F) (D := D) g hg Work.WilG4b.sideP5 Work.WilG4b.widthP5
            (Work.WilG4b.shiftLoP q) td_sideP5 td_widthP5 (td_shiftLoP q)))
    have hI := Work.WilG1.Omega.inter₂ (S := S) hHi hLo
    rw [liftR_oscR g q]
    exact Work.WilG5.mem_mono hI (F + 700)
      (((Polynomial.C 4 + Qpoly) + (Polynomial.C 4 + Qpoly)).eval D) (by omega) le_rfl
  · have hHi : Work.WilG4b.HighL g q ∈
        S.Ω (max 6 ((F + 600 + 3) + 1) + 1 + 1 + 1) ((Polynomial.C 4 + Qpoly).eval D) 1 := by
      rw [← compl_WHiL g q]
      exact Work.WilG1.Omega.compl_mem (S := S)
        (W_omega_of_core (S := S)
          (coreP_omega (S := S) (F := F) (D := D) g hg Work.WilG4b.sideP5L Work.WilG4b.widthP5L
            (Work.WilG4b.shiftLoP q) td_sideP5L td_widthP5L (td_shiftLoP q)))
    have hLo : Work.WilG4b.LowL g q ∈
        S.Ω (max 6 ((F + 600 + 3) + 1) + 1 + 1 + 1) ((Polynomial.C 4 + Qpoly).eval D) 1 := by
      rw [← compl_WLoL g q]
      exact Work.WilG1.Omega.compl_mem (S := S)
        (W_omega_of_core (S := S)
          (coreP_omega (S := S) (F := F) (D := D) g hg Work.WilG4b.sideP5L Work.WilG4b.widthP5L
            (Work.WilG4b.shiftHiP q) td_sideP5L td_widthP5L (td_shiftHiP q)))
    have hI := Work.WilG1.Omega.inter₂ (S := S) hHi hLo
    rw [liftR_oscL g q]
    exact Work.WilG5.mem_mono hI (F + 700)
      (((Polynomial.C 4 + Qpoly) + (Polynomial.C 4 + Qpoly)).eval D) (by omega) le_rfl

end Work.WilG4bF
