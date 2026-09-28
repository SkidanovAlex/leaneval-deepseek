import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sk2_short_sum_le
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDBasic.finite_sets

namespace Work.HP.MM2

open Work.HP

/-- Monotonicity of a `finsum` over a set under inclusion of the summation set, for a
nonnegative summand and a finite ambient set. -/
lemma finsum_mem_le_of_subset {ι : Type*} [Fintype ι] {S B : Set (ι → ℤ)}
    (hSB : S ⊆ B) (hBfin : B.Finite) (f : (ι → ℤ) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ᶠ a ∈ S, f a) ≤ ∑ᶠ a ∈ B, f a := by
  have hSfin : S.Finite := hBfin.subset hSB
  rw [finsum_mem_eq_finite_toFinset_sum f hSfin, finsum_mem_eq_finite_toFinset_sum f hBfin]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun x hx => hBfin.mem_toFinset.mpr (hSB (hSfin.mem_toFinset.mp hx)))
    (fun x _ _ => hf x)

/-- Crude bound for the local second-moment sum: for `T ≥ 1` the sum
`𝓢_2(Γ^{loc}_{x,y}(Q); 𝒯^{loc}_{x,y}(T,α))` is `≪ T^{N-2}`, uniformly in `x, y, Q, α`
(Browning--Le Boudec--Sawin, "Upper bound trivial t", `k = 2`, `u = T`).
Route: `TlocSet d n x y T α = {a | eNorm a ≤ T ∧ toR a ∈ Cgam (toR (veronese d n x)) α ∧
toR a ∈ Cgam (toR (veronese d n y)) α}` is contained in the ball of radius `T`, so the
summed set is a subset of `{a | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T}` and
`Sk2_short_sum_le (Mon d n) (3 ≤ Fintype.card (Mon d n))` applies; `six_le_NN` gives
`6 ≤ NN d n = Fintype.card (Mon d n)`.  For the set containment use
`finsum_mem_eq_finite_toFinset_sum` + `Finset.sum_le_sum_of_subset_of_nonneg`
(as in `Sk2_short_sum_le.finsum_lattice_le_ball`), or `finsum_mem_mono` with the
finiteness of the ball (`MDBasic.finite_eNorm_le`). -/
theorem Sk2_Tloc_le_pow (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x y : Fin (n + 1) → ℤ) (Q : ℕ) (T α : ℝ), 1 ≤ T →
      Sk d n 2 (GamLoc d n x y Q) (TlocSet d n x y T α) ≤ K * T ^ (NN d n - 2) := by
  classical
  have h3 : 3 ≤ Fintype.card (Mon d n) := by
    have h6 : 6 ≤ NN d n := six_le_NN d n hd hdn
    simp only [NN] at h6
    omega
  obtain ⟨K, hKpos, hK⟩ := Sk2_short_sum_le (ι := Mon d n) h3
  refine ⟨K, hKpos, ?_⟩
  intro x y Q T α hT
  have hsub : ({a : Mon d n → ℤ | a ∈ GamLoc d n x y Q ∧ a ≠ 0 ∧ a ∈ TlocSet d n x y T α} : Set _)
      ⊆ ({a : Mon d n → ℤ | a ∈ GamLoc d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ T} : Set _) := by
    rintro a ⟨haL, ha0, haT⟩
    exact ⟨haL, ha0, haT.1⟩
  have hBfin : ({a : Mon d n → ℤ | a ∈ GamLoc d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ T} : Set _).Finite :=
    (MDBasic.finite_eNorm_le T).subset (fun a ha => ha.2.2)
  have hmono := finsum_mem_le_of_subset hsub hBfin
    (fun a : Mon d n → ℤ => 1 / eNorm a ^ 2)
    (fun a => div_nonneg zero_le_one (sq_nonneg (eNorm a)))
  have hball := hK (GamLoc d n x y Q) T hT
  calc Sk d n 2 (GamLoc d n x y Q) (TlocSet d n x y T α)
      = ∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ GamLoc d n x y Q ∧ a ≠ 0 ∧
            a ∈ TlocSet d n x y T α} : Set _), 1 / eNorm a ^ 2 := rfl
    _ ≤ ∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ GamLoc d n x y Q ∧ a ≠ 0 ∧
            eNorm a ≤ T} : Set _), 1 / eNorm a ^ 2 := hmono
    _ ≤ K * T ^ (NN d n - 2) := hball

end Work.HP.MM2
