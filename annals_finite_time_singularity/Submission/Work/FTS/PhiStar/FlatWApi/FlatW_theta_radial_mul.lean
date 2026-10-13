import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FlatW` is stable under multiplication by a radial factor

The operator `pzIter k` is the `k`-fold `∂_z` (applied to the `z`-slice), and `DthIter i` is the
`i`-fold `D_θ = sin(2θ)·∂_θ`.  Multiplying a function by a factor `a z` depending on `z` alone
interacts trivially with both: the `θ`-derivatives never see it and the `z`-derivatives act on it
by the Leibniz rule with a constant (`iteratedDeriv_mul_const_field`).  Consequently the flat
weighted bound `FlatW l` is multiplicative: if `a` satisfies the radial estimate
`|(z+1)^k ∂_z^k a| ≤ A` for `k ≤ l` and `θ ↦ u θ` satisfies `FlatW l _ K`, then
`(z,θ) ↦ a z * u θ` satisfies `FlatW l _ (A·K)`.

The identities are unconditional (no differentiability is assumed): the totalised `deriv` of
`c * f` is `c * deriv f` in a division ring, so the iterated versions
`iteratedDeriv_mul_const_field` / `deriv_const_mul_field` hold pointwise everywhere.
-/

namespace Work.FTS.PhiStar.FlatWApi

open Work.Spaces (Lop pzIter pth Dth DthIter pz)

set_option autoImplicit false

/-! ## The two structural identities -/

/-- Iterated `z`-derivatives commute with multiplication by a function of `θ` alone:
`∂_z^k (b z * φ θ) = (∂_z^k b z) * φ θ`. -/
lemma pzIter_mul_const (b φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    pzIter k (fun z' θ' => b z' * φ θ') z θ = iteratedDeriv k b z * φ θ := by
  have h1 : pzIter k (fun z' θ' => b z' * φ θ') z θ
      = iteratedDeriv k (fun z' => b z' * φ θ) z :=
    Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ
  rw [h1]
  exact iteratedDeriv_mul_const_field b (φ θ)

/-- `Lop u θ = sin(2θ)·u'(θ)` is linear: `Lop (c * g) = c * Lop g`. -/
lemma Lop_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Lop (fun θ => c * g θ) = fun θ => c * Lop g θ := by
  funext θ
  simp only [Lop]
  rw [deriv_const_mul_field]
  ring

/-- Iterated `Lop` is linear. -/
lemma Lop_iter_const_mul (c : ℝ) (g : ℝ → ℝ) (i : ℕ) :
    Lop^[i] (fun θ => c * g θ) = fun θ => c * Lop^[i] g θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      calc Lop^[i.succ] (fun θ => c * g θ)
          = Lop (Lop^[i] (fun θ => c * g θ)) := Function.iterate_succ_apply' Lop i _
        _ = Lop (fun θ => c * Lop^[i] g θ) := by rw [ih]
        _ = (fun θ => c * Lop^[i.succ] g θ) := by
              rw [Lop_const_mul, ← Function.iterate_succ_apply' Lop i g]

/-- Iterated angular derivatives commute with multiplication by a function of `z` alone:
`D_θ^i (b z * φ θ) = b z * (Lop^i φ)(θ)`. -/
lemma DthIter_mul_const (b φ : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    DthIter i (fun z' θ' => b z' * φ θ') z θ = b z * Lop^[i] φ θ := by
  have h1 : DthIter i (fun z' θ' => b z' * φ θ') z = Lop^[i] (fun θ' => b z * φ θ') :=
    Work.Spaces.DthIter_eq_iterate_Lop i _ z
  have h2 : Lop^[i] (fun θ' => b z * φ θ') = fun θ' => b z * Lop^[i] φ θ' :=
    Lop_iter_const_mul (b z) φ i
  have h3 := congrFun h2 θ
  rw [← h1] at h3
  exact h3

/-! ## The multiplication theorem -/

theorem FlatW_theta_radial_mul : ∃ C : ℝ, 0 < C ∧
  ∀ (l : ℕ) (a u : ℝ → ℝ) (A K : ℝ), 0 ≤ A → 0 ≤ K →
    (∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 < z → |(z + 1) ^ k * iteratedDeriv k a z| ≤ A) →
    Work.FTS.VocabO2.FlatW l (fun _ θ => u θ) K →
    Work.FTS.VocabO2.FlatW l (fun z θ => a z * u θ) (C * (A * K)) := by
  refine ⟨1, one_pos, ?_⟩
  intro l a u A K hA _ ha hU z θ hz hθ hπ
  have hUz := hU z θ hz hθ hπ
  have huz : |u θ| ≤ K := by
    simpa using hUz.1 0 (Nat.zero_le l)
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [pzIter_mul_const a u k z θ]
    have hmul : |(z + 1) ^ k * (iteratedDeriv k a z * u θ)|
        = |(z + 1) ^ k * iteratedDeriv k a z| * |u θ| := by
      rw [show (z + 1) ^ k * (iteratedDeriv k a z * u θ)
            = ((z + 1) ^ k * iteratedDeriv k a z) * u θ from (mul_assoc _ _ _).symm, abs_mul]
    rw [hmul]
    calc |(z + 1) ^ k * iteratedDeriv k a z| * |u θ| ≤ A * K :=
          mul_le_mul (ha k hk z hz) huz (abs_nonneg _) hA
      _ = 1 * (A * K) := by ring
  · intro k i hki
    have hpth : pth (fun z θ => a z * u θ)
        = fun z θ => a z * deriv (fun θ'' => u θ'') θ := by
      funext z' θ'
      simp only [Work.Spaces.pth]
      exact deriv_const_mul_field (a z')
    have hDth : DthIter i (pth (fun z θ => a z * u θ))
        = fun z θ => a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ := by
      rw [hpth]
      funext z' θ'
      exact DthIter_mul_const a (deriv (fun θ'' => u θ'')) i z' θ'
    have hpz : pzIter k (DthIter i (pth (fun z θ => a z * u θ))) z θ
        = iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ := by
      rw [hDth]
      exact pzIter_mul_const a (Lop^[i] (deriv (fun θ'' => u θ''))) k z θ
    rw [hpz]
    have hpthU : (fun θ' => pth (fun _ θ'' => u θ'') z θ') = deriv (fun θ'' => u θ'') := by
      funext θ'
      rfl
    have hLopDth : Lop^[i] (deriv (fun θ'' => u θ'')) θ
        = DthIter i (pth (fun _ θ'' => u θ'')) z θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop, hpthU]
    have hKl : |Lop^[i] (deriv (fun θ'' => u θ'')) θ| ≤ K := by
      rw [hLopDth]
      simpa using hUz.2 0 i (by omega)
    have hmul : |(z + 1) ^ k * (iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ)|
        = |(z + 1) ^ k * iteratedDeriv k a z| * |Lop^[i] (deriv (fun θ'' => u θ'')) θ| := by
      rw [show (z + 1) ^ k * (iteratedDeriv k a z * Lop^[i] (deriv (fun θ'' => u θ'')) θ)
            = ((z + 1) ^ k * iteratedDeriv k a z) * Lop^[i] (deriv (fun θ'' => u θ'')) θ
          from (mul_assoc _ _ _).symm, abs_mul]
    rw [hmul]
    calc |(z + 1) ^ k * iteratedDeriv k a z| * |Lop^[i] (deriv (fun θ'' => u θ'')) θ|
          ≤ A * K := mul_le_mul (ha k (by omega) z hz) hKl (abs_nonneg _) hA
      _ = 1 * (A * K) := by ring

end Work.FTS.PhiStar.FlatWApi
