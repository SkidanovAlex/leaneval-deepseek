import Submission.Work.FinSigma
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.dual_first
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg
import Submission.Commons.Combinatorics.Transference.dualFunc_bound
import Submission.Work.PseudoCube

set_option linter.unusedSectionVars false

/-!
# Green–Tao Lemma 7.3 (anti-uniformity): the dual function and the `U^{k-1}` norm

The identity `𝔼(F · 𝒟F) = ‖F‖_{U^d}^{2^d}`, which converts a lower bound on the Gowers
`U^d` norm of `F` into a *correlation* of `F` with the Gowers anti-uniform (dual)
function `𝒟F`, together with the sup-norm bound for `𝒟F` coming from the linear forms
condition on `ν` (`dualFunc_bound`).
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference

lemma sum_ite_one_mul {p : ℕ} [Fact p.Prime] {d : ℕ} (ω : Fin d → Bool) (h : Fin d → ZMod p) :
    (∑ j, (if ω j then (1 : ZMod p) else 0) * h j) = ∑ j, (if ω j then h j else 0) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp [hj]

/-- `⟨F, 𝒟F⟩` computed as the normalised `d`-cube sum of `F`. -/
lemma dual_first_davg {p : ℕ} [Fact p.Prime] {d : ℕ} (F : ZMod p → ℝ) :
    ∑ x : ZMod p, F x * davg d F x
      = ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ * (∑ h : Fin d → ZMod p, ∑ x : ZMod p,
          ∏ ω : Fin d → Bool, F (x + ∑ i, (if ω i then h i else 0))) := by
  have h1 : ∑ x : ZMod p, F x * davg d F x
      = ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ x : ZMod p, F x * (∑ h : Fin d → ZMod p, ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          F (x + ∑ i, (if ω i then h i else 0)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [davg]
    ring
  rw [h1, dual_first]

/-- **Green–Tao Lemma 7.3**, normalised form: `⟨F, 𝒟F⟩ = |G| · ‖F‖_{U^d}^{2^d}`. -/
theorem dual_inner_unorm {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (F : ZMod p → ℝ) :
    ∑ x : ZMod p, F x * davg d F x
      = (Fintype.card (ZMod p) : ℝ) * (Unorm d F) ^ (2 ^ d) := by
  rw [dual_first_davg, ← cubeSum, Unorm_pow d hd F]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN : ((Fintype.card (ZMod p) : ℝ)) ≠ 0 := by
    rw [ZMod.card]
    exact_mod_cast (by omega : p ≠ 0)
  have hNd : ((Fintype.card (Fin d → ZMod p) : ℝ)) = ((Fintype.card (ZMod p) : ℝ)) ^ d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  rw [hNd]
  field_simp
  ring

/-- **Anti-uniformity (Green–Tao Lemma 7.3).**  If the Gowers `U^d` norm of `F` is at least `γ`,
then `F` correlates with the bounded Gowers anti-uniform function `𝒟F`:
`|G| γ^{2^d} ≤ ∑_x F x · 𝒟F(x)`. -/
theorem unorm_le_sum_dual {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (F : ZMod p → ℝ)
    {γ : ℝ} (hγ : 0 ≤ γ) (h : γ ≤ Unorm d F) :
    (Fintype.card (ZMod p) : ℝ) * γ ^ (2 ^ d) ≤ ∑ x : ZMod p, F x * davg d F x := by
  rw [dual_inner_unorm hd F]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hγ h _) (by positivity)

/-- The sup-norm bound for the dual function, from the local linear forms condition. -/
theorem davg_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν F : ZMod p → ℝ)
    (hF : ∀ x, |F x| ≤ ν x + 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε)
    (b : ZMod p) : |davg d F b| ≤ ((2 : ℝ) ^ (2 ^ d - 1)) * (1 + ε) := by
  have h := Commons.Combinatorics.Transference.dualFunc_bound hd ν F hF hε hLFC b
  have e : (∑ h : Fin d → ZMod p,
        ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
          F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
      = ∑ h : Fin d → ZMod p, ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
          F (b + ∑ j : Fin d, (if ω j then h j else 0)) :=
    Finset.sum_congr rfl fun h _ => Finset.prod_congr rfl fun ω _ => by rw [sum_ite_one_mul]
  rw [e] at h
  rwa [davg]

/-- The sup-norm bound for the dual function, stated directly for a `k`-pseudorandom measure
(the `(d, d·2^d, 3(d+1)-4, d+1)`-linear forms condition on `ν`). -/
theorem davg_bound_of_LinFormsCond {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d)
    (ν F : ZMod p → ℝ) (hF : ∀ x, |F x| ≤ ν x + 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : LinFormsCond p ν (d * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε) (b : ZMod p) :
    |davg d F b| ≤ ((2 : ℝ) ^ (2 ^ d - 1)) * (1 + ε) :=
  davg_bound hd ν F hF hε
    (fun A hA hAne b' =>
      cube_lfc_fixed hd ν ε hLFC A hAne (fun h0 => by have := hA h0; simp at this) b') b

end GTTrans
