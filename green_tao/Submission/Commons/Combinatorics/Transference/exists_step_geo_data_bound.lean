import Mathlib
import Submission.Commons.Combinatorics.Transference.exists_boundary_family
import Submission.Commons.Combinatorics.Transference.davg_halfC_bound
import Submission.Commons.Combinatorics.Transference.davg_div_bound
import Submission.Commons.Combinatorics.Transference.davg_div_close

namespace Commons.Combinatorics.Transference

/-- **The geometric data of a single Green–Tao §7 step, with explicit constants.**

This is `exists_step_geo_data` with the two existential constants `Mraw`, `εraw` instantiated at
their effective values `(2C)^{2^d-1}·2^{2^d-1}(1+εp)` and `(2C)^{2^d-1}·ε`. The proof follows
the same route: `exists_boundary_family` for the shift and the boundary set,
`davg_halfC_bound` for the scaled sup norm `2^{2^d-1}(1+εp)`, `davg_div_bound` for the sup-norm
bound of `davg d F`, and `davg_div_close` for the Lipschitz constant. -/
theorem exists_step_geo_data_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {C ε η : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    {ν F : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hF : ∀ x, |F x| ≤ C * (ν x + 1))
    {εp : ℝ} (hεp : 0 ≤ εp)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ εp) :
    ∃ (αnew : ℝ) (Tnew : Finset (ZMod p)),
      0 ≤ αnew ∧ αnew < ε ∧
      (∀ y : ZMod p,
        (∃ m : ℤ, |(davg d (fun z => F z / (2 * C)) y - αnew) / ε - (m : ℝ)| ≤ η) → y ∈ Tnew) ∧
      (∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)) ∧
      (∀ x : ZMod p,
        |davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * ((2 : ℝ) ^ (2 ^ d - 1) * (1 + εp))) ∧
      (∀ x y : ZMod p,
        ⌊(davg d (fun z => F z / (2 * C)) y - αnew) / ε⌋
            = ⌊(davg d (fun z => F z / (2 * C)) x - αnew) / ε⌋ →
        |davg d F y - davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * ε) := by
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  -- The boundary family for the single generator `davg d (F/(2C))`.
  obtain ⟨α, T, hα, hT, hTsum⟩ :=
    exists_boundary_family (K := 1) (fun _ => davg d (fun z => F z / (2 * C))) ν hε hη hη1 hν
  -- The scaled sup-norm bound `2^{2^d-1}(1+εp)` for `davg d (F/(2C))`.
  have hscaled : ∀ x, |davg d (fun y => F y / (2 * C)) x| ≤ (2 : ℝ) ^ (2 ^ d - 1) * (1 + εp) :=
    davg_halfC_bound hd ν F hν hC hF hεp hLFC
  refine ⟨α 0, T 0, (hα 0).1, (hα 0).2, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hT 0 y hy
  · simpa using hTsum
  · intro x
    exact davg_div_bound hCpos F hscaled x
  · intro x y hxy
    exact davg_div_close hCpos hε hxy

end Commons.Combinatorics.Transference
