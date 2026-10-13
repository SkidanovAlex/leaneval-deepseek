/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "middle" mixed summands of the `H^4` product rule

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021, Lemma
*HProductRule* (paper lines 1068–1085).

`HkSq α 4 (f·g)` is the sum of the squared weighted `L²`-norms of the derivatives
`D_z^i (f g)` (with the weaker weight `w·sin(2θ)^{-η/2}`) and of the mixed derivatives
`D_z^j D_θ^i (f g)` with `i ≥ 1` (with the stronger weight `W = w·sin(2θ)^{-γ/2}`).
This file bounds every *mixed* summand with `i ≥ 1`, `i+j ≤ 4`, except the exceptional
pair `(j,i) = (3,1)` (which needs the full force of the one-dimensional Hardy
inequalities and is treated separately in `HProductRule_bad_term`).

The strategy is the paper's.  By the exact Leibniz expansion `mixed_mul_eq`

`mixed j i (f g) = ∑_{a≤i} ∑_{b≤j} C(i,a)C(j,b) · (mixed b a f)(mixed (j-b) (i-a) g)`

and Cauchy–Schwarz, the squared weighted summand is bounded by a constant times
`∑_{a,b} (mixed b a f · W)² · (mixed (j-b) (i-a) g)²`.  For each pair `(a,b)` one of the
two factors has total order `≤ 2` and can be pulled out by the pointwise `L^∞`-bound
`HPwH2` (Corollary *SecondDerivativesBounded*), while the *other* factor carries a
`θ`-derivative with `1 ≤ order ≤ 4` and retains its full weighted `L²`-norm, which is a
single summand of `HkSq α 4 f` resp. `HkSq α 4 g`.  The only pairs for which neither
alternative is available are exactly `(j,i) = (3,1)` with `(a,b) ∈ {(0,3),(1,0)}` — these
are the terms `D_z³f·D_θ g` and `D_θ f·D_z³ g` excluded by the hypothesis
`¬ (j = 3 ∧ i = 1)`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.HPwH2
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary closure properties -/

/-- The pointwise product of two functions smooth on a neighbourhood of the closed
quadrant is again smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) (hg : SmoothNbhd g) :
    SmoothNbhd (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) nbhU
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [h]
  exact hf.mul hg

/-- `SmoothNbhd` implies `SmoothInt` (local copy; the version in `WProductRule` belongs to
another area of the project). -/
private theorem SmoothInt_of_SmoothNbhd {u : ℝ → ℝ → ℝ} (h : SmoothNbhd u) : SmoothInt u := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-- `VanishTheta` is preserved by iterated `D_z`-derivatives. -/
private lemma DzIter_vanish {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (n : ℕ) :
    VanishTheta (DzIter n f) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [DzIter_succ, Dz, pz, hfun]
      · intro z
        have hfun : (fun z' => DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) := funext ih.2
        simp [DzIter_succ, Dz, pz, hfun]

/-- Any positive iterate of `D_θ` vanishes on the two angular boundaries. -/
private lemma DthIter_vanish_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    VanishTheta (DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * pth (DthIter a' f) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * pth (DthIter a' f) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- `VanishTheta` is preserved by the mixed derivatives `D_z^b D_θ^a`. -/
private lemma VanishTheta_mixed {f : ℝ → ℝ → ℝ} (h : VanishTheta f) (b a : ℕ) :
    VanishTheta (mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa [mixed] using DzIter_vanish h b
  · have h1 : VanishTheta (DthIter a f) := DthIter_vanish_of_pos f ha
    simpa [mixed] using DzIter_vanish h1 b

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

/-! ## The pointwise `L^∞` bound for derivatives of order at most `2` -/

/-- `PWB α u` is the square of the pointwise `L^∞` bound for `u` and all its first and
second `D_z`/`D_θ` derivatives: `(100²/(γ-1))·HkSq α 4 u` (Corollary
*SecondDerivativesBounded* of the paper). -/
private def PWB (α : ℝ) (u : ℝ → ℝ → ℝ) : ℝ := 100 ^ 2 / (gam α - 1) * HkSq α 4 u

private lemma PWB_nonneg (α : ℝ) (hα : 0 < α) (u : ℝ → ℝ → ℝ) : 0 ≤ PWB α u := by
  rw [PWB]
  exact mul_nonneg (div_nonneg (by norm_num) (by linarith [one_lt_gam hα]))
    (HkSq_nonneg α 4 u)

/-- Pointwise form of the paper's Corollary *SecondDerivativesBounded*: every mixed
derivative of order `a + b ≤ 2` is pointwise bounded by `100²/(γ-1)·HkSq α 4 u` on the
domain. -/
private lemma mixed_sq_pw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd u) (hvt : VanishTheta u) (hdec : DecayMixed 2 u) (hmem : HkMem α 4 u)
    (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ, (mixed b a u z θ) ^ 2 ≤ PWB α u := by
  have hsm' : SmoothNbhd (mixed b a u) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hvt' : VanishTheta (mixed b a u) := VanishTheta_mixed hvt b a
  have hdec' : ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a u z θ) atTop (𝓝 0) :=
    fun θ hθ => hdec a b hab θ hθ
  have hmem' : HkMem α 2 (mixed b a u) := HkMem_mixed_le α hα hα1 u hsm hmem b a hab
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcoef : 100 / (gam α - 1) ≤ 100 ^ 2 / (gam α - 1) :=
    div_le_div_of_nonneg_right (by norm_num) hγ.le
  intro z hz θ hθ
  calc (mixed b a u z θ) ^ 2
      ≤ 100 / (gam α - 1) * HkSq α 2 (mixed b a u) :=
        HPwH2 α hα hα1 (mixed b a u) hsm' hvt' hdec' hmem' z hz θ hθ
    _ ≤ 100 ^ 2 / (gam α - 1) * HkSq α 2 (mixed b a u) :=
        mul_le_mul_of_nonneg_right hcoef (HkSq_nonneg α 2 (mixed b a u))
    _ ≤ 100 ^ 2 / (gam α - 1) * HkSq α 4 u :=
        mul_le_mul_of_nonneg_left (HkSq_mixed_le α hα hα1 u hsm hmem b a hab)
          (div_nonneg (by norm_num) hγ.le)
    _ = PWB α u := rfl

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

/-! ## The Cauchy–Schwarz step of the Leibniz expansion -/

/-- Leibniz expansion of `D_z^j D_θ^i (f g)`, followed by Cauchy–Schwarz: the squared
weighted summand is bounded by `6400` times the sum over the expansion pairs of the
squared weighted pieces.  The constant is very generous: `25` for the cardinality of the
index set `(i+1)(j+1)` and `256 = 4^{i+j}` for the squared binomial coefficients. -/
private lemma expansion_cs (α : ℝ) (i j : ℕ) (hij : i + j ≤ 4) (f g : ℝ → ℝ → ℝ)
    (hfi : SmoothInt f) (hgi : SmoothInt g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
  intro z hz θ hθ
  set s : Finset (ℕ × ℕ) := Finset.range (i + 1) ×ˢ Finset.range (j + 1) with hs
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
      rw [mixed_mul_eq j i f g hfi hgi z hz θ hθ]
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
    have hai : p.1 ≤ i := by omega
    have hbj : p.2 ≤ j := by omega
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


/-! ## The majorant attached to a pair `(a,b)` of the Leibniz expansion -/

/-- The majorant of a single pair `(a,b)` of the Leibniz expansion of `mixed j i (f g)`:
whichever of the two factors has total order `≤ 2` is pulled out into its pointwise
`L^∞`-bound `PWB`, and the other one keeps its weighted `L²`-norm.

The two branches are `(a,b)` with `1 ≤ a` and `(i-a) + (j-b) ≤ 2` (the `g`-factor is
pulled out; the `f`-factor is a weighted mixed derivative with `1 ≤ a`), resp. the
complementary situation (`msum_orders` guarantees that at least one branch applies for
every pair occurring in the expansion, under the hypotheses of
`HProductRule_Msummand`). -/
private def MAJ (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => if 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    then PWB α g * (mixed b a f z θ * Wt α z θ) ^ 2
    else PWB α f * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2

/-- The pointwise domination of a pair of the Leibniz expansion by its majorant. -/
private lemma MAJ_pw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : SmoothNbhd f) (hvtf : VanishTheta f) (hdecf : DecayMixed 2 f) (hmemf : HkMem α 4 f)
    (hsimg : SmoothNbhd g) (hvtg : VanishTheta g) (hdecg : DecayMixed 2 g) (hmemg : HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1))
    {a b : ℕ} (hai : a ≤ i) (hbj : b ≤ j) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
      ≤ MAJ α f g j i a b z θ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hB : (mixed (j - b) (i - a) g z θ) ^ 2 ≤ PWB α g :=
      mixed_sq_pw_le α hα hα1 g hsimg hvtg hdecg hmemg (j - b) (i - a) hc.2 z hz θ hθ
    have hnn : 0 ≤ (mixed b a f z θ * Wt α z θ) ^ 2 := sq_nonneg _
    rw [MAJ, if_pos hc]
    calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
        = (mixed (j - b) (i - a) g z θ) ^ 2 * (mixed b a f z θ * Wt α z θ) ^ 2 := by ring
      _ ≤ PWB α g * (mixed b a f z θ * Wt α z θ) ^ 2 := mul_le_mul_of_nonneg_right hB hnn
  · have h2 : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hA : (mixed b a f z θ) ^ 2 ≤ PWB α f :=
      mixed_sq_pw_le α hα hα1 f hsmf hvtf hdecf hmemf b a h2.2 z hz θ hθ
    rw [MAJ, if_neg hc]
    calc (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
        = (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := by
          rw [mul_pow]
      _ ≤ PWB α f * (Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (sq_nonneg _)
      _ = PWB α f * (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by rw [mul_pow]; ring

/-- The `θ`-slice of the majorant is integrable. -/
private lemma MAJ_integrableOn_theta (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ)
    (hsmf : SmoothNbhd f) (hmemf : HkMem α 4 f) (hsimg : SmoothNbhd g) (hmemg : HkMem α 4 g)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j)
    {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => MAJ α f g j i a b z θ) Iθ := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed b a f z θ * Wt α z θ) ^ 2) Iθ :=
      mixed_sq_integrableOn hsmf hmemf a b hc.1 hab hz
    have h2 := h1.const_mul (PWB α g)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_pos hc]) measurableSet_Icc
  · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
      rcases msum_orders hi hij hne hai hbj with h | h
      · exact absurd h hc
      · exact h
    have hab : (i - a) + (j - b) ≤ 4 := by omega
    have h1 : IntegrableOn (fun θ => (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iθ :=
      mixed_sq_integrableOn hsimg hmemg (i - a) (j - b) h2'.1 hab hz
    have h2 := h1.const_mul (PWB α f)
    exact MeasureTheory.IntegrableOn.congr_fun h2
      (fun θ _ => by simp only [MAJ]; rw [if_neg hc]) measurableSet_Icc

/-- `L2Mem` for a weighted mixed derivative of order between `1` and `4`. -/
private theorem L2Mem_mixed_Wt (α : ℝ) (u : ℝ → ℝ → ℝ) (hsm : SmoothNbhd u)
    (hmem : HkMem α 4 u) (b a : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ 4) :
    L2Mem (fun z θ => mixed b a u z θ * Wt α z θ) := by
  constructor
  · intro z hz
    exact mixed_sq_integrableOn hsm hmem a b ha hab hz
  · exact (bt_prod_integrable α u hsm hmem b a ha hab).1.integral_prod_left

/-- Integrability in `z` of the angular integral of the majorant. -/
private lemma MAJ_integrableOn_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i a b : ℕ)
    (hsmf : SmoothNbhd f) (hmemf : HkMem α 4 f) (hsimg : SmoothNbhd g) (hmemg : HkMem α 4 g)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) (hai : a ≤ i) (hbj : b ≤ j) :
    IntegrableOn (fun z => ∫ θ in Iθ, MAJ α f g j i a b z θ) Iz := by
  by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
  · have hab : a + b ≤ 4 := by omega
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt α f hsmf hmemf b a hc.1 hab).2
    have h2 := h1.const_mul (PWB α g)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWB α g * ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g j i a b z θ
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
    have h1 : IntegrableOn (fun z => ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2) Iz :=
      (L2Mem_mixed_Wt α g hsimg hmemg (j - b) (i - a) h2'.1 hab).2
    have h2 := h1.const_mul (PWB α f)
    refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ici
    intro z hz
    show PWB α f * ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
        = ∫ θ in Iθ, MAJ α f g j i a b z θ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    simp only [MAJ]
    rw [if_neg hc]

/-! ## Measurability of the weighted summand -/

/-- The angular slice of the weight is measurable. -/
private lemma measurable_Wt_slice (α z : ℝ) : Measurable (fun θ : ℝ => Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    hsin.pow_const _
  have h : Measurable (fun θ : ℝ => w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    measurable_const.mul hpow
  simpa only [Wt, wTheta] using h

/-- The squared weighted mixed derivative of a smooth function is a.e. strongly measurable
on every angular slice; the `θ`-slice is continuous because the mixed derivative is
smooth on a neighbourhood of the closed quadrant. -/
private lemma aesm_slice_mixed (α : ℝ) {u : ℝ → ℝ → ℝ} (hsm : SmoothNbhd u) (j i : ℕ)
    {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable (fun θ : ℝ => (mixed j i u z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := by
  have hsm' : SmoothNbhd (mixed j i u) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm i) j
  have hcont : ContinuousOn (fun θ : ℝ => mixed j i u z θ) Iθ := by
    intro θ hθ
    have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (mixed j i u)) (z, θ) :=
      hsm'.contDiffAt (isOpen_nbhU.mem_nhds (mem_nbhU hz hθ))
    exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt
  have h1 : AEStronglyMeasurable (fun θ : ℝ => mixed j i u z θ) (volume.restrict Iθ) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  have h2 : AEStronglyMeasurable (fun θ : ℝ => Wt α z θ) (volume.restrict Iθ) :=
    (measurable_Wt_slice α z).aestronglyMeasurable
  exact (h1.mul h2).pow 2


theorem HProductRule_Msummand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsimg : Work.Spaces.SmoothNbhd g)
    (hvtf : Work.Spaces.VanishTheta f) (hvtg : Work.Spaces.VanishTheta g)
    (hdecf : Work.Spaces.DecayMixed 2 f) (hdecg : Work.Spaces.DecayMixed 2 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hne : ¬ (j = 3 ∧ i = 1)) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ (10 ^ 12 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  have hγ : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hsmFG : SmoothNbhd (fun z θ => f z θ * g z θ) := smoothNbhd_mul hsmf hsimg
  have hFGsm : SmoothInt f := SmoothInt_of_SmoothNbhd hsmf
  have hGsm : SmoothInt g := SmoothInt_of_SmoothNbhd hsimg
  -- the pointwise bound
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g j i a b z θ := by
    intro z hz θ hθ
    have hcs := expansion_cs α i j hij f g hFGsm hGsm z hz θ hθ
    have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2
          ≤ MAJ α f g j i a b z θ := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      exact MAJ_pw_le α hα hα1 f g hsmf hvtf hdecf hmemf hsimg hvtg hdecg hmemg j i hi hij hne
        (by omega) (by omega) hz hθ
    calc (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (mixed b a f z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a) g z θ) ^ 2 := hcs
      _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g j i a b z θ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun a ha =>
            Finset.sum_le_sum fun b hb => hterm a ha b hb
  -- integrability of the majorant sums
  have hsumθ_int : ∀ z ∈ Iz, IntegrableOn (fun θ => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), MAJ α f g j i a b z θ) Iθ := by
    intro z hz
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_theta α f g j i a b hsmf hmemf hsimg hmemg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega) hz
  have hsumz_int : IntegrableOn (fun z => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g j i a b z θ) Iz := by
    exact integrableOn_finsetSum _ fun a ha => integrableOn_finsetSum _ fun b hb =>
      MAJ_integrableOn_z α f g j i a b hsmf hmemf hsimg hmemg hi hij hne
        (by have := Finset.mem_range.mp ha; omega)
        (by have := Finset.mem_range.mp hb; omega)
  -- integrability of the angular slices of the target
  have hIntTheta : ∀ z ∈ Iz, IntegrableOn
      (fun θ => (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iθ := by
    intro z hz
    refine Integrable.mono' ((hsumθ_int z hz).const_mul 6400)
      (aesm_slice_mixed α hsmFG j i hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint z hz θ hθ
  -- the (pointwise in `z`) domination of the angular integral
  have hdom : ∀ z ∈ Iz, (∫ θ in Iθ,
        (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2)
      ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g j i a b z θ := by
    intro z hz
    have h2 : IntegrableOn (fun θ => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), MAJ α f g j i a b z θ) Iθ :=
      (hsumθ_int z hz).const_mul 6400
    calc ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            MAJ α f g j i a b z θ :=
          integral_mono_ae (hIntTheta z hz) h2
            (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpoint z hz θ hθ)
      _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ∫ θ in Iθ, MAJ α f g j i a b z θ := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [MeasureTheory.integral_finsetSum _ (fun a ha =>
            integrableOn_finsetSum _ fun b hb => MAJ_integrableOn_theta α f g j i a b
              hsmf hmemf hsimg hmemg hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz)]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [MeasureTheory.integral_finsetSum _ fun b hb =>
            MAJ_integrableOn_theta α f g j i a b hsmf hmemf hsimg hmemg hi hij hne
              (by have := Finset.mem_range.mp ha; omega)
              (by have := Finset.mem_range.mp hb; omega) hz]
  -- integrability of the outer integral of the target
  have hOuterInt : IntegrableOn
      (fun z => ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2) Iz := by
    have hmaj : IntegrableOn (fun z => 6400 * ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), ∫ θ in Iθ, MAJ α f g j i a b z θ) Iz :=
      hsumz_int.const_mul 6400
    refine Integrable.mono' hmaj ?_ ?_
    · have hAESM := aesm_mixed_Wt_sq_prod α (fun z θ => f z θ * g z θ) hsmFG j i
      simpa only [Function.uncurry] using hAESM.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
      exact hdom z hz
  refine ⟨⟨hIntTheta, hOuterInt⟩, ?_⟩
  rw [L2Sq]
  -- the per-pair integral bound
  have hTerg : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (∫ z in Iz, ∫ θ in Iθ, MAJ α f g j i a b z θ)
        ≤ (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro a ha b hb
    have hai : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hbj : b ≤ j := by have := Finset.mem_range.mp hb; omega
    by_cases hc : 1 ≤ a ∧ (i - a) + (j - b) ≤ 2
    · have hab : a + b ≤ 4 := by omega
      have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g j i a b z θ)
          = PWB α g * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2 := by
        simp only [MAJ, if_pos hc, MeasureTheory.integral_const_mul]
      rw [hInt]
      calc PWB α g * ∫ z in Iz, ∫ θ in Iθ, (mixed b a f z θ * Wt α z θ) ^ 2
          ≤ PWB α g * HkSq α 4 f :=
            mul_le_mul_of_nonneg_left (L2Sq_mixed_le_HkSq α 4 f hmemf a b hc.1 hab)
              (PWB_nonneg α hα g)
        _ = (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
            rw [PWB]; ring
    · have h2' : 1 ≤ i - a ∧ a + b ≤ 2 := by
        rcases msum_orders hi hij hne hai hbj with h | h
        · exact absurd h hc
        · exact h
      have hab : (i - a) + (j - b) ≤ 4 := by omega
      have hInt : (∫ z in Iz, ∫ θ in Iθ, MAJ α f g j i a b z θ)
          = PWB α f * ∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2 := by
        simp only [MAJ, if_neg hc, MeasureTheory.integral_const_mul]
      rw [hInt]
      calc PWB α f * ∫ z in Iz, ∫ θ in Iθ, (mixed (j - b) (i - a) g z θ * Wt α z θ) ^ 2
          ≤ PWB α f * HkSq α 4 g :=
            mul_le_mul_of_nonneg_left
              (L2Sq_mixed_le_HkSq α 4 g hmemg (i - a) (j - b) h2'.1 hab) (PWB_nonneg α hα f)
        _ = (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
            rw [PWB]; ring
  calc ∫ z in Iz, ∫ θ in Iθ, (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      ≤ ∫ z in Iz, 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ θ in Iθ, MAJ α f g j i a b z θ :=
        setIntegral_mono_of_nonneg
          (fun z hz => integral_nonneg fun θ => sq_nonneg _)
          (fun z hz => hdom z hz) (hsumz_int.const_mul 6400)
    _ = 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ∫ z in Iz, ∫ θ in Iθ, MAJ α f g j i a b z θ := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun a ha => integrableOn_finsetSum _
          fun b hb => MAJ_integrableOn_z α f g j i a b hsmf hmemf hsimg hmemg hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega))]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [MeasureTheory.integral_finsetSum _ fun b hb =>
          MAJ_integrableOn_z α f g j i a b hsmf hmemf hsimg hmemg hi hij hne
            (by have := Finset.mem_range.mp ha; omega)
            (by have := Finset.mem_range.mp hb; omega)]
    _ ≤ 6400 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hTerg a ha b hb
    _ ≤ 10 ^ 12 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
        have hcard25 : ((i + 1) * (j + 1) : ℕ) ≤ 25 := by
          have hi5 : i + 1 ≤ 5 := by omega
          have hj5 : j + 1 ≤ 5 := by omega
          calc (i + 1) * (j + 1) ≤ 5 * 5 := Nat.mul_le_mul hi5 hj5
            _ = 25 := rfl
        have hcard25' : ((((i + 1) * (j + 1) : ℕ)) : ℝ) ≤ 25 := by exact_mod_cast hcard25
        have hTnn : (0 : ℝ) ≤ (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
          mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hγ.le) (HkSq_nonneg α 4 f))
            (HkSq_nonneg α 4 g)
        have hsumval : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)
            = (((i + 1) * (j + 1) : ℕ) : ℝ)
              * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
            Finset.card_range, Finset.card_range]
          push_cast
          ring
        rw [hsumval]
        have hcoef : (6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1))) ≤
            (10 : ℝ) ^ 12 / (gam α - 1) := by
          have e1 : (6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1)))
              = (6400 * (25 * (10 : ℝ) ^ 4)) / (gam α - 1) := by ring
          rw [e1]
          exact div_le_div_of_nonneg_right (by norm_num) hγ.le
        have hinner : (((i + 1) * (j + 1) : ℕ) : ℝ)
              * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)
            ≤ 25 * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_right hcard25' hTnn
        have h1 : (6400 : ℝ) * ((((i + 1) * (j + 1) : ℕ) : ℝ)
              * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g))
            ≤ (6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
        have h2 : (6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g))
            ≤ (10 : ℝ) ^ 12 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          have heq : (6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g))
              = ((6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1))))
                * (HkSq α 4 f * HkSq α 4 g) := by ring
          rw [heq]
          calc ((6400 : ℝ) * (25 * ((10 : ℝ) ^ 4 / (gam α - 1))))
                * (HkSq α 4 f * HkSq α 4 g)
              ≤ ((10 : ℝ) ^ 12 / (gam α - 1)) * (HkSq α 4 f * HkSq α 4 g) :=
                mul_le_mul_of_nonneg_right hcoef
                  (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
            _ = (10 : ℝ) ^ 12 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
        exact le_trans h1 h2

end Work.Spaces
