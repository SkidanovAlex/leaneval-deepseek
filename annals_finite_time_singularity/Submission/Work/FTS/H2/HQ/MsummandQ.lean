import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The weight `Wt` vanishes on the boundary lines

`RegQ` constrains `f` only on the *open* quadrant, so all the pointwise estimates below
have to be taken where the weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` does not vanish.
On the two lines `θ = 0`, `θ = π/2` and on `z = 0` the weight is `0` (Lean's totalised
division and `Real.zero_rpow`), which is exactly what makes the pointwise estimates at
those lines trivial: both sides of each of them vanish. -/

/-- `Wt α 0 θ = 0`: the radial weight vanishes at `z = 0`. -/
private theorem Wt_zero_left (α θ : ℝ) : Wt α 0 θ = 0 := by
  simp [Wt, w]

/-- `Wt α z 0 = 0` for `α > 0`: the angular weight vanishes at `θ = 0`. -/
private theorem Wt_zero_theta_zero (α z : ℝ) (hα : 0 < α) : Wt α z 0 = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show Real.sin (2 * 0) = 0 by norm_num, Real.zero_rpow hexp, mul_zero]

/-- `Wt α z (π/2) = 0` for `α > 0`: the angular weight vanishes at `θ = π/2`. -/
private theorem Wt_zero_theta_pi (α z : ℝ) (hα : 0 < α) : Wt α z (π / 2) = 0 := by
  have hgam : 0 < gam α := by rw [gam]; linarith
  have hexp : -(gam α / 2) ≠ 0 := by linarith
  rw [Wt, wTheta, show 2 * (π / 2) = π by ring, Real.sin_pi, Real.zero_rpow hexp, mul_zero]

/-- The weight vanishes on the boundary of the closed quadrant. -/
private theorem Wt_eq_zero_of_boundary (α z θ : ℝ) (hα : 0 < α) (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) : Wt α z θ = 0 := by
  by_cases hz0 : z = 0
  · subst hz0
    exact Wt_zero_left α θ
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hθ' : θ = 0 ∨ θ = π / 2 := by
      rcases Set.mem_Icc.mp hθ with ⟨h1, h2⟩
      by_contra hc
      push_neg at hc
      exact h ⟨hzpos, lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩
    rcases hθ' with rfl | rfl
    · exact Wt_zero_theta_zero α z hα
    · exact Wt_zero_theta_pi α z hα

/-! ## The pointwise `L^∞`-bound of the factor of order `≤ 2` -/

/-- The square of the pointwise `L^∞`-bound of the factor of total order `≤ 2`:
`Cf/(γ-1)·|f|²_{ℋ⁴}`, exactly the right hand side of `PwBd.bound`. -/
private def PWBQ (α : ℝ) (f : ℝ → ℝ → ℝ) (Cf : ℝ) : ℝ := Cf / (gam α - 1) * HkSq α 4 f

/-- `PWBQ` is nonnegative for `α > 0` and `Cf ≥ 0`. -/
private theorem PWBQ_nonneg {α Cf : ℝ} (hα : 0 < α) (hC : 0 ≤ Cf) (f : ℝ → ℝ → ℝ) :
    0 ≤ PWBQ α f Cf := by
  rw [PWBQ]
  exact mul_nonneg (div_nonneg hC (by linarith [one_lt_gam hα])) (HkSq_nonneg α 4 f)

/-- The pointwise `L^∞`-bound of `PwBd`, in the `PWBQ` shape. -/
private theorem PWBQ_bound {α Cf : ℝ} {f : ℝ → ℝ → ℝ} (hb : PwBd α f Cf)
    {b a : ℕ} (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2) :
    (mixed b a f z θ) ^ 2 ≤ PWBQ α f Cf :=
  hb.bound b a hab z hz θ hθ1 hθ2

/-! ## The combinatorial case analysis -/

/-- For the pairs `(a,b)` occurring in the Leibniz expansion of `mixed j i (f g)` (so that
`a ≤ i`, `b ≤ j`) with `1 ≤ i`, `i + j ≤ 4` and `(j,i) ≠ (3,1)`, at least one of the two
factors has total order `≤ 2` while the *other* one carries a `θ`-derivative of order
`≥ 1`.  This is what makes the paper's "all other terms can be treated as `D_θ^4(fg)`"
precise: the exceptional configurations are exactly `(j,i) = (3,1)` with `a = 0, b = 3`
or `a = 1, b = 0`. -/
private lemma msum_orders {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    (1 ≤ a ∧ (i - a) + (j - b) ≤ 2) ∨ (1 ≤ i - a ∧ a + b ≤ 2) := by
  by_cases hc : 1 ≤ a
  · by_cases hd : (i - a) + (j - b) ≤ 2
    · exact Or.inl ⟨hc, hd⟩
    · refine Or.inr ⟨?_, by omega⟩
      by_contra h
      push_neg at h
      omega
  · push_neg at hc
    exact Or.inr ⟨by omega, by omega⟩

/-! ## Cauchy–Schwarz on the Leibniz expansion -/

/-- Leibniz expansion of `D_z^j D_θ^i (f g)`, followed by Cauchy–Schwarz: the squared
weighted summand is bounded by `6400` times the sum over the expansion pairs of the
squared weighted pieces.  The constant is very generous: `25` for the cardinality of the
index set `(i+1)(j+1)` and `256 = 4^{i+j}` for the squared binomial coefficients.

The `RegQ` Leibniz rule `mixed_mul_eq_quad` is only available for `0 < θ < π/2`; at the
two lines `θ = 0`, `θ = π/2` both sides of the inequality vanish because the weight
`Wt α z θ` does, so the estimate holds for every `θ ∈ Iθ`. -/
private lemma expansion_cs (α : ℝ) (hα : 0 < α) (i j : ℕ) (hij : i + j ≤ 4)
    (f g : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hg : SmoothQuad g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
  intro z hz θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (j + 1) with hs
    set X : ℕ × ℕ → ℝ := fun p => (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
        * ((mixed p.2 p.1 f z θ * Wt α z θ) * mixed (j - p.2) (i - p.1) g z θ) with hX
    set Y : ℕ × ℕ → ℝ := fun p => (mixed p.2 p.1 f z θ * Wt α z θ) ^ 2
        * (mixed (j - p.2) (i - p.1) g z θ) ^ 2 with hY
    -- the exact Leibniz expansion, with the weight distributed
    have hexp : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ = ∑ p ∈ s, X p := by
      have h1 : mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * ((mixed b a f z θ * Wt α z θ) * mixed (j - b) (i - a) g z θ) := by
        rw [mixed_mul_eq_quad j i f g hf hg z hz θ hθi]
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        refine Finset.sum_congr rfl (fun b hb => ?_)
        ring
      rw [h1, hs, Finset.sum_product]
    -- the Cauchy–Schwarz step
    have hcard : ((s.card : ℕ) : ℝ) ≤ 25 := by
      have h25 : s.card ≤ 25 := by
        rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]
        have hi5 : i + 1 ≤ 5 := by omega
        have hj5 : j + 1 ≤ 5 := by omega
        calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
          _ = 25 := rfl
      exact_mod_cast h25
    have hcoef : ∀ p ∈ s, X p ^ 2 ≤ 256 * Y p := by
      intro p hp
      rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      have hc16 : (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ) ≤ 16 := by
        have h1 : (i.choose p.1 : ℝ) ≤ 2 ^ i := by
          exact_mod_cast Nat.choose_le_two_pow i p.1
        have h2 : (j.choose p.2 : ℝ) ≤ 2 ^ j := by
          exact_mod_cast Nat.choose_le_two_pow j p.2
        calc (i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)
            ≤ 2 ^ i * 2 ^ j := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 2 ^ (i + j) := by rw [← pow_add]
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 16 := by norm_num
      have hid : X p ^ 2 = ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p := by
        simp only [hX, hY]; ring
      have hYnn : 0 ≤ Y p := by simp only [hY]; positivity
      rw [hid]
      calc ((i.choose p.1 : ℝ) * (j.choose p.2 : ℝ)) ^ 2 * Y p
          ≤ 16 ^ 2 * Y p :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc16 2) hYnn
        _ = 256 * Y p := by norm_num
    have hYsum : ∑ p ∈ s, Y p = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
      rw [hs, Finset.sum_product]
    have hYnn : 0 ≤ ∑ p ∈ s, Y p :=
      Finset.sum_nonneg (fun p _ => by simp only [hY]; positivity)
    have hX2nn : 0 ≤ ∑ p ∈ s, X p ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    have hbound : (∑ p ∈ s, X p) ^ 2 ≤ 6400 * ∑ p ∈ s, Y p := by
      calc (∑ p ∈ s, X p) ^ 2 ≤ (s.card : ℝ) * ∑ p ∈ s, X p ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ ≤ 25 * ∑ p ∈ s, X p ^ 2 := mul_le_mul_of_nonneg_right hcard hX2nn
        _ ≤ 25 * (256 * ∑ p ∈ s, Y p) :=
            mul_le_mul_of_nonneg_left
              (by
                calc ∑ p ∈ s, X p ^ 2 ≤ ∑ p ∈ s, 256 * Y p := Finset.sum_le_sum hcoef
                  _ = 256 * ∑ p ∈ s, Y p := by rw [Finset.mul_sum])
              (by norm_num)
        _ = 6400 * ∑ p ∈ s, Y p := by ring
    calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        = (∑ p ∈ s, X p) ^ 2 := by rw [hexp]
      _ ≤ 6400 * ∑ p ∈ s, Y p := hbound
      _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
          rw [hYsum]
  · have hW : Wt α z θ = 0 :=
      Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc => hθi hc.2)
    have hL : (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 = 0 := by
      rw [hW]; ring
    have hR : 0 ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => ?_)
      exact Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [hL]; exact hR

/-! ## The majorant attached to a pair `(a,b)` of the Leibniz expansion -/

/-- The majorant of a single pair `(a,b)` of the Leibniz expansion of `mixed j i (f g)`:
whichever of the two factors has total order `≤ 2` is pulled out into its pointwise
`L^∞`-bound `PWBQ`, and the other one keeps its weighted `L²`-norm.

The two branches are `(a,b)` with `1 ≤ a` and `(i-a) + (j-b) ≤ 2` (the `g`-factor is
pulled out, with constant `Cg`; the `f`-factor is a weighted mixed derivative with
`1 ≤ a`), resp. the complementary situation (`msum_orders` guarantees that at least one
branch applies for every pair occurring in the expansion, under the hypotheses of
`MsummandQ`). -/
private def MAJ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => if 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    then PWBQ α g Cg * (mixed b a f z θ * Wt α z θ) ^ 2
    else PWBQ α f Cf * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2

/-- The majorant is nonnegative. -/
private lemma MAJ_nonneg {α Cf Cg : ℝ} (hα : 0 < α) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (f g : ℝ → ℝ → ℝ) (j i a b : ℕ) (z θ : ℝ) :
    0 ≤ MAJ α f g Cf Cg j i a b z θ := by
  rw [MAJ]
  split
  · exact mul_nonneg (PWBQ_nonneg hα hCg g) (sq_nonneg _)
  · exact mul_nonneg (PWBQ_nonneg hα hCf f) (sq_nonneg _)

/-- The pointwise domination of a pair of the Leibniz expansion by its majorant. -/
private lemma MAJ_pw_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ)
    (hCfb : PwBd α f Cf) (hCgb : PwBd α g Cg)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
      ≤ MAJ α f g Cf Cg j i a b z θ := by
  by_cases hgen : 0 < z ∧ 0 < θ ∧ θ < π / 2
  · obtain ⟨hzpos, hθ1, hθ2⟩ := hgen
    by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    · have hB : (mixed (j - b) (i - a) g z θ) ^ 2 ≤ PWBQ α g Cg :=
        PWBQ_bound hCgb hc.2 hzpos hθ1 hθ2
      have hnn : 0 ≤ (mixed b a f z θ * Wt α z θ) ^ 2 := sq_nonneg _
      rw [MAJ, if_pos hc]
      calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          = (mixed (j - b) (i - a) g z θ) ^ 2 * (mixed b a f z θ * Wt α z θ) ^ 2 := by ring
        _ ≤ PWBQ α g Cg * (mixed b a f z θ * Wt α z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hB hnn
    · have h2 : 1 ≤ i - a ∧ a + b ≤ 2 := by
        rcases msum_orders hi hij hne hai hbj with h | h
        · exact absurd h hc
        · exact h
      have hA : (mixed b a f z θ) ^ 2 ≤ PWBQ α f Cf :=
        PWBQ_bound hCfb h2.2 hzpos hθ1 hθ2
      rw [MAJ, if_neg hc]
      calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          = (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
            rw [mul_pow]
        _ ≤ PWBQ α f Cf * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (sq_nonneg _)
        _ = PWBQ α f Cf * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
            rw [mul_pow]; ring
  · have hW : Wt α z θ = 0 :=
      Wt_eq_zero_of_boundary α z θ hα hz hθ (fun hc => hgen hc)
    have h0 : (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 = 0 := by
      rw [hW]; ring
    rw [h0]
    exact MAJ_nonneg hα hCfb.nonneg hCgb.nonneg f g j i a b z θ

/-! ## Integrability of the majorant -/

/-- A finite sum of functions integrable on a set is integrable on that set. -/
private theorem integrableOn_finsetSum {ι : Type*} {s : Set ℝ} {φ : ι → ℝ → ℝ} (t : Finset ι)
    (h : ∀ i ∈ t, IntegrableOn (φ i) s) : IntegrableOn (fun x => ∑ i ∈ t, φ i x) s := by
  classical
  induction t using Finset.induction with
  | empty =>
      simpa using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) s (μ := volume))
  | insert a t ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a t, φ i x)
          = (fun x => φ a x) + (fun x => ∑ i ∈ t, φ i x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The `θ`-slice of the majorant is integrable. -/
private lemma MAJ_integrableOn_theta (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j)
    {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => MAJ α f g Cf Cg j i a b z θ) Iθ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed b a f z θ * Wt α z θ) ^ 2) Iθ :=
      integrableOn_slice_mixed_Wt_sq α f hfsq hmemf b a hc.1 hab hz
    have h2 := h1.const_mul (PWBQ α g Cg)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_pos hc]) measurableSet_Icc
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iθ :=
      integrableOn_slice_mixed_Wt_sq α g hgsq hmemg (j - b) (i - a) h2'.1 hab hz
    have h2 := h1.const_mul (PWBQ α f Cf)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_neg hc]) measurableSet_Icc

/-- `L2Mem` for a weighted mixed derivative of order between `1` and `4`. -/
private theorem L2Mem_mixed_Wt_qd (α : ℝ) (u : ℝ → ℝ → ℝ) (hu : SmoothQuad u)
    (hmem : HkMem α 4 u) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 4) :
    L2Mem (fun z θ => mixed b a u z θ * Wt α z θ) := by
  constructor
  · intro z hz
    exact integrableOn_slice_mixed_Wt_sq α u hu hmem b a ha hab hz
  · exact (bt_prod_integrable_quad α u hu hmem b a ha hab).1.integral_prod_left

/-- Integrability in `z` of the angular integral of the majorant. -/
private lemma MAJ_integrableOn_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (j i a b : ℕ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    IntegrableOn (fun z => ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt_qd α f hfsq hmemf b a hc.1 hab).2
    have h2 := h1.const_mul (PWBQ α g Cg)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWBQ α g Cg * ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_pos hc]
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn
        (fun z => ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt_qd α g hgsq hmemg (j - b) (i - a) h2'.1 hab).2
    have h2 := h1.const_mul (PWBQ α f Cf)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWBQ α f Cf * ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_neg hc]

/-! ## Strong measurability of the weighted summand -/

/-- The squared weighted mixed derivative of a `SmoothQuad` function is a.e. strongly
measurable on every angular slice, for every `z ∈ Iz` (at `z = 0` the function vanishes
identically). -/
private lemma aesm_slice_mixed_qd (α : ℝ) {u : ℝ → ℝ → ℝ} (hu : SmoothQuad u) (j i : ℕ)
    {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable (fun θ => (mixed j i u z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    have hzero : (fun θ => (mixed j i u 0 θ * Wt α 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ; rw [Wt_zero_left]; ring
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact aesm_slice_mixed_Wt_sq α u hu j i hpos

/-! ## The per-pair integral bound -/

/-- The integral of the majorant of a single pair of the Leibniz expansion. -/
private lemma MAJ_pair_integral_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ)
    (hfsq : SmoothQuad f) (hmemf : HkMem α 4 f) (hgsq : SmoothQuad g) (hmemg : HkMem α 4 g)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) :
    (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
      ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        = PWBQ α g Cg * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2 := by
      simp only [MAJ, if_pos hc, MeasureTheory.integral_const_mul]
    rw [hInt]
    have hstep : (∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f :=
      L2Sq_mixed_le_HkSq α 4 f hmemf a b hc.1 hab
    have hCg' : Cg ≤ Cf + Cg := by linarith
    calc PWBQ α g Cg * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        ≤ PWBQ α g Cg * HkSq α 4 f :=
          mul_le_mul_of_nonneg_left hstep (PWBQ_nonneg hα hCg g)
      _ ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          rw [PWBQ]
          calc Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
              = (Cg * (gam α - 1)⁻¹) * (HkSq α 4 g * HkSq α 4 f) := by ring
            _ ≤ ((Cf + Cg) * (gam α - 1)⁻¹) * (HkSq α 4 g * HkSq α 4 f) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCg' (inv_nonneg.mpr hγ.le))
                  (mul_nonneg (HkSq_nonneg α 4 g) (HkSq_nonneg α 4 f))
            _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        = PWBQ α f Cf * ∫ z in Iz, ∫ θ in Iθ,
            (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
      simp only [MAJ, if_neg hc, MeasureTheory.integral_const_mul]
    rw [hInt]
    have hstep : (∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2)
        ≤ HkSq α 4 g :=
      L2Sq_mixed_le_HkSq α 4 g hmemg (i - a) (j - b) h2'.1 hab
    have hCf' : Cf ≤ Cf + Cg := by linarith
    calc PWBQ α f Cf * ∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        ≤ PWBQ α f Cf * HkSq α 4 g :=
          mul_le_mul_of_nonneg_left hstep (PWBQ_nonneg hα hCf f)
      _ ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          rw [PWBQ]
          calc Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
              = (Cf * (gam α - 1)⁻¹) * (HkSq α 4 f * HkSq α 4 g) := by ring
            _ ≤ ((Cf + Cg) * (gam α - 1)⁻¹) * (HkSq α 4 f * HkSq α 4 g) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hCf' (inv_nonneg.mpr hγ.le))
                  (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
            _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring

/-- **The "middle" mixed summands of the interior product rule `HProdQ`.**

For `f, g` in the interior class `Work.FTS.Nonlin.RegQ α 4` and pointwise `L^∞`-bound packages
`PwBd α f Cf`, `PwBd α g Cg`, every weighted mixed slot of the product with `1 ≤ i`,
`i + j ≤ 4`, except the exceptional pair `(j,i) = (3,1)` (which is `BadsummandQ`), satisfies
`L2Mem (mixed j i (f g) · Wt α)` and
`L2Sq (mixed j i (f g) · Wt α) ≤ C/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}`.

This is `Work.Spaces.HProductRule_Msummand` (proved) with `Spaces.SmoothNbhd` (analyticity on a
neighbourhood of the closed quadrant) replaced by `SmoothQuad`, `VanishTheta` dropped, the decay
hypotheses dropped, and the pointwise `L^∞`-bound of order `≤ 2` supplied abstractly by `PwBd`
(instead of `Work.Spaces.MixedSqPointwiseBound`).  Route: copy the proof of
`Submission/Work/Spaces/HProductRule_Msummand.lean`:
* `Work.FTS.H2.HQ.mixed_mul_eq_quad` replaces `Work.Spaces.mixed_mul_eq` — note that the
  `RegQ` version is *only* available for `0 < θ < π/2` (the `SmoothQuad` Leibniz is interior),
  so the pointwise step `expansion_cs`/`hpoint` must be stated with
  `∀ᵐ θ ∂(volume.restrict Iθ)` (use `ae_restrict_mem measurableSet_Ioo`) rather than for all
  `θ ∈ Iθ`; at `θ = 0, π/2` and at `z = 0` both sides of every pointwise inequality used here
  vanish because the weights `Wt α z θ = w z · sin(2θ)^{-γ/2}` do (in Lean `w 0 = 0` and
  `(sin 0)^c = 0` by totalised division/`Real.zero_rpow`), so this loses nothing;
* `Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq`, `Work.FTS.H2.HQ.aesm_mixed_Wt_sq_prod_quad`,
  `Work.FTS.H2.HQ.aesm_slice_mixed_Wt_sq`, `Work.FTS.H2.HQ.bt_prod_integrable_quad` (in
  `HQ/Glue.lean`) replace `Work.Spaces.mixed_sq_integrableOn`, `Work.Spaces.aesm_mixed_Wt_sq_prod`
  and `Work.Spaces.bt_prod_integrable`, and `Work.FTS.LocData.smoothQuad_mul` gives
  `SmoothQuad (f·g)`;
* `Work.Spaces.L2Sq_mixed_le_HkSq` and `Work.Spaces.sq_le_HkIntegrand_mixed` are pure and are
  reused unchanged;
* the arithmetic is as in `HProductRule_Msummand`, with `PwBd.bound` (and `PwBd.nonneg`)
  supplying the two `PWB` values, so the final constant is again some absolute `C`. -/
theorem MsummandQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn)
    (Cf Cg : ℝ), 0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg →
    ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 4 → ¬ (j = 3 ∧ i = 1) →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g Cf Cg hα hα1 hregf hregg hCfb hCgb j i hi hij hne
  obtain ⟨hfsq, hmemf, _⟩ := hregf
  obtain ⟨hgsq, hmemg, _⟩ := hregg
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hCf : 0 ≤ Cf := hCfb.nonneg
  have hCg : 0 ≤ Cg := hCgb.nonneg
  have hsmFG : SmoothQuad (fun z θ => f z θ * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hfsq hgsq
  -- the pointwise bound
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ := by
    intro z hz θ hθ
    have hcs := expansion_cs α hα i j hij f g hfsq hgsq z hz θ hθ
    have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          ≤ MAJ α f g Cf Cg j i a b z θ := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      exact MAJ_pw_le α hα f g Cf Cg hCfb hCgb j i hi hij hne
        (by omega) (by omega) hz hθ
    calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := hcs
      _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun a ha =>
            Finset.sum_le_sum fun b hb => hterm a ha b hb
  -- integrability of the majorant sums
  have hsumθ_int : ∀ z ∈ Iz, IntegrableOn (fun θ => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), MAJ α f g Cf Cg j i a b z θ) Iθ := by
    intro z hz
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_theta α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega) hz
  have hsumz_int : IntegrableOn (fun z => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz := by
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega)
  -- integrability of the angular slices of the target
  have hIntTheta : ∀ z ∈ Iz, IntegrableOn
      (fun θ => (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iθ := by
    intro z hz
    refine Integrable.mono' ((hsumθ_int z hz).const_mul 6400)
      (aesm_slice_mixed_qd α hsmFG j i hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint z hz θ hθ
  -- the (pointwise in `z`) domination of the angular integral
  have hdom : ∀ z ∈ Iz, (∫ θ in Iθ,
        (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2)
      ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
    intro z hz
    have h2 : IntegrableOn (fun θ => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), MAJ α f g Cf Cg j i a b z θ) Iθ :=
      (hsumθ_int z hz).const_mul 6400
    calc ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g Cf Cg j i a b z θ :=
          integral_mono_ae (hIntTheta z hz) h2
            (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpoint z hz θ hθ)
      _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [MeasureTheory.integral_finsetSum _ (fun a ha =>
            integrableOn_finsetSum _ fun b hb => MAJ_integrableOn_theta α f g Cf Cg j i a b
              hfsq hmemf hgsq hmemg hCf hCg hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz)]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [MeasureTheory.integral_finsetSum _ fun b hb =>
            MAJ_integrableOn_theta α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg
              hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz]
  -- integrability of the outer integral of the target
  have hOuterInt : IntegrableOn
      (fun z => ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iz := by
    have hmaj : IntegrableOn (fun z => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ) Iz :=
      hsumz_int.const_mul 6400
    refine Integrable.mono' hmaj ?_ ?_
    · have hAESM := aesm_mixed_Wt_sq_prod_quad α (fun z θ => f z θ * g z θ) hsmFG j i
      simpa only [Function.uncurry] using hAESM.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
      exact hdom z hz
  refine ⟨⟨hIntTheta, hOuterInt⟩, ?_⟩
  rw [L2Sq]
  -- the per-pair integral bound
  have hXnn : (0 : ℝ) ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hγ.le) (HkSq_nonneg α 4 f))
      (HkSq_nonneg α 4 g)
  have hTerg : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ)
        ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro a ha b hb
    exact MAJ_pair_integral_le α hα f g Cf Cg hfsq hmemf hgsq hmemg hCf hCg j i hi hij hne
      (by have := Finset.mem_range.mp ha; omega) (by have := Finset.mem_range.mp hb; omega)
  calc ∫ z in Iz, ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      ≤ ∫ z in Iz, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ :=
        setIntegral_mono_of_nonneg
          (fun z hz => integral_nonneg fun θ => sq_nonneg _)
          (fun z hz => hdom z hz) (hsumz_int.const_mul 6400)
    _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ z in Iz, ∫ θ in Iθ, MAJ α f g Cf Cg j i a b z θ := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun a ha => integrableOn_finsetSum _
          fun b hb => MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg
            hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega))]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [MeasureTheory.integral_finsetSum _ fun b hb =>
          MAJ_integrableOn_z α f g Cf Cg j i a b hfsq hmemf hgsq hmemg hCf hCg hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega)]
    _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hTerg a ha b hb
    _ = 6400 * ((((i + 1) * (j + 1) : ℕ) : ℝ)
          * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          Finset.card_range, Finset.card_range]
        push_cast
        ring
    _ ≤ 6400 * (25 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) := by
        have hcard25 : ((((i + 1) * (j + 1) : ℕ)) : ℝ) ≤ 25 := by
          have h5 : (i + 1) * (j + 1) ≤ 25 := by
            have hi5 : i + 1 ≤ 5 := by omega
            have hj5 : j + 1 ≤ 5 := by omega
            calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
              _ = 25 := rfl
          exact_mod_cast h5
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard25 hXnn)
          (by norm_num)
    _ = (160000 : ℝ) * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by ring
    _ ≤ 10 ^ 12 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
        mul_le_mul_of_nonneg_right (by norm_num) hXnn
    _ = 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.FTS.H2.HQ
