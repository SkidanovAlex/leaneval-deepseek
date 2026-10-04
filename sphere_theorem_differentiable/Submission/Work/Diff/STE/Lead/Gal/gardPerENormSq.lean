import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.Lead.Gal.gardENormSq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Hᵏ` energy of the periodisation of a ball-supported function

Let `F : (Fin n → ℝ) → ℂ` be smooth, supported in the closed ball of radius `R < 1/2` (and hence
in the open unit cube), and suppose that all its iterated partial derivatives of order `≤ k` are
bounded by `C0` on that ball.  Then the `Hᵐ` energy (`m ≤ k`) of the periodisation
`P z = ∑' q : Fin n → ℤ, F (z + iVec q)` is bounded by a constant times `C0 ^ 2`.

The proof is short: hypothesis `R < ‖x‖ → F x = 0` forces `F` (and therefore every iterated
partial derivative of `F`, whose support lies in the closure of the support of `F`) to vanish in a
neighbourhood of every point outside the ball, so the pointwise bound `‖∂^β F‖ ≤ C0` is *global*.
On the closed unit cube the periodisation is a finite sum of the `2 ^ n` lattice translates
`F (· + q)`, `q ∈ {-1,0}ⁿ`, and the `Fin`-indexed iterated derivatives commute with translations and
finite sums, so `‖∂^β P‖ ≤ 2 ^ n * C0` on the cube.  Integrating the square over the cube (volume
`1`) and summing over the `n ^ m` multi-indices `Fin m → Fin n` gives the claim; the whole argument
is the already-proved `Work.Diff.STE.csqp_ENormSq_periodization_le`.
-/

noncomputable section

open Function
open scoped BigOperators Topology

namespace Work.Diff.STE.Lead.Gal

/-! ## Iterated partial derivatives of the zero function -/

/-- `pd` of the zero function vanishes. -/
private lemma gal_pd_zero {ι : Type*} [DecidableEq ι] (i : ι) :
    Work.Diff.STE.pd i (fun _ : ι → ℝ => (0 : ℂ)) = (fun _ : ι → ℝ => (0 : ℂ)) := by
  funext x
  simp [Work.Diff.STE.pd]

/-- `pdList` of the zero function vanishes. -/
private lemma gal_pdList_zero {ι : Type*} [DecidableEq ι] (L : List ι) :
    Work.Diff.STE.pdList L (fun _ : ι → ℝ => (0 : ℂ)) = (fun _ : ι → ℝ => (0 : ℂ)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      show Work.Diff.STE.pd a (Work.Diff.STE.pdList L (fun _ : ι → ℝ => (0 : ℂ)))
        = (fun _ : ι → ℝ => (0 : ℂ))
      rw [ih, gal_pd_zero a]

/-- `pdVec` of the zero function vanishes. -/
private lemma gal_pdVec_zero {ι : Type*} [DecidableEq ι] {k : ℕ} (l : Fin k → ι) :
    Work.Diff.STE.pdVec k l (fun _ : ι → ℝ => (0 : ℂ)) = (fun _ : ι → ℝ => (0 : ℂ)) := by
  simp only [Work.Diff.STE.pdVec]
  exact gal_pdList_zero (List.ofFn l)

/-- If `f` agrees with `0` in a neighbourhood of `x`, then every iterated partial derivative of
`f` vanishes at `x`. -/
private lemma gal_pdVec_eq_zero_of_eventuallyEq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ} {x : ι → ℝ} (m : ℕ) (l : Fin m → ι)
    (hf : f =ᶠ[𝓝 x] (fun _ : ι → ℝ => (0 : ℂ))) :
    Work.Diff.STE.pdVec m l f x = 0 := by
  rw [Work.Diff.STE.csqp_pdVec_congr (l := l) hf, gal_pdVec_zero l]

theorem gardPerENormSq {n : ℕ} (k : ℕ) (R : ℝ) (hR : R < 1 / 2) (hR0 : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : (Fin n → ℝ) → ℂ) (C0 : ℝ), 0 ≤ C0 →
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F →
        Function.support F ⊆ {z : Fin n → ℝ | ∀ i : Fin n, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)} →
        (∀ x : Fin n → ℝ, R < ‖x‖ → F x = 0) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ),
          ‖z‖ ≤ R → ‖Work.Diff.STE.pdVec m β F z‖ ≤ C0) →
        ∀ m : ℕ, m ≤ k →
          Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ =>
            ∑' q : Fin n → ℤ, F (z + Work.Diff.STE.iVec q)) ≤ C * C0 ^ 2 := by
  classical
  refine ⟨((n : ℝ) + 1) ^ k * ((2 : ℝ) ^ n) ^ 2, by positivity, ?_⟩
  intro F C0 hC0 hF hsupp hball hbound m hm
  -- the support of `F` is contained in the open unit cube, in the form needed below
  have hsuppcube : Function.support F ⊆ Set.pi Set.univ
      (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    rw [Set.mem_pi]
    intro i _
    exact hsupp hz i
  -- the pointwise bound on the derivatives of `F` is global: outside the ball `F` vanishes
  -- on a neighbourhood, hence so does every iterated partial derivative of `F`
  have hglob : ∀ (l : Fin m → Fin n) (x : Fin n → ℝ),
      ‖Work.Diff.STE.pdVec m l F x‖ ≤ C0 := by
    intro l x
    by_cases hx : ‖x‖ ≤ R
    · exact hbound m hm l x hx
    · have hxR : R < ‖x‖ := not_le.mp hx
      have hopen : IsOpen {y : Fin n → ℝ | R < ‖y‖} :=
        isOpen_lt continuous_const continuous_norm
      have hnear : F =ᶠ[𝓝 x] (fun _ : Fin n → ℝ => (0 : ℂ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hxR) (fun y hy => hball y hy)
      rw [gal_pdVec_eq_zero_of_eventuallyEq_zero m l hnear, norm_zero]
      exact hC0
  have hEN := Work.Diff.STE.csqp_ENormSq_periodization_le (ι := Fin n) (j := m) (M := C0)
    hF hsuppcube hglob hC0
  have hcard : (Fintype.card (Fin m → Fin n) : ℝ) = (n : ℝ) ^ m := by
    rw [Fintype.card_fun]
    simp
  have hbox : ((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) = (2 : ℝ) ^ n := by
    rw [Work.Diff.STE.csqp_card_boxIdx, Fintype.card_fin]
    norm_num
  have hpow : (n : ℝ) ^ m ≤ ((n : ℝ) + 1) ^ k := by
    refine le_trans (pow_le_pow_left₀ (Nat.cast_nonneg n)
      (le_add_of_nonneg_right zero_le_one) m) ?_
    exact pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg n)) hm
  have hmain : Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ =>
        ∑' q : Fin n → ℤ, F (z + fun i => (q i : ℝ)))
      ≤ ((n : ℝ) + 1) ^ k * ((2 : ℝ) ^ n) ^ 2 * C0 ^ 2 := by
    calc Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ =>
          ∑' q : Fin n → ℤ, F (z + fun i => (q i : ℝ)))
        ≤ (Fintype.card (Fin m → Fin n) : ℝ)
            * (((Work.Diff.STE.csqp_boxIdx (Fin n)).card : ℝ) * C0) ^ 2 := hEN
      _ = (n : ℝ) ^ m * (((2 : ℝ) ^ n) ^ 2 * C0 ^ 2) := by rw [hcard, hbox]; ring
      _ ≤ ((n : ℝ) + 1) ^ k * (((2 : ℝ) ^ n) ^ 2 * C0 ^ 2) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = ((n : ℝ) + 1) ^ k * ((2 : ℝ) ^ n) ^ 2 * C0 ^ 2 := by ring
  exact hmain

end Work.Diff.STE.Lead.Gal

