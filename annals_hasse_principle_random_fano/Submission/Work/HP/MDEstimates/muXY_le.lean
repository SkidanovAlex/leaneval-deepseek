import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.HPgram
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.span_pair_lattice

/-!
# `μ(x,y) ≤ 3n² ‖x‖‖y‖`

The quantity of the second-moment computation

`μ(x,y) = 3n² max(𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²)`,   `𝔡_r = dmin r {x,y}`,

(Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 2023, §4)
is used as the threshold `A = μ(x,y)` up to which the archimedean density is approximated by its
main term.  Here we prove the elementary bound

`μ(x,y) ≤ 3n² ‖x‖‖y‖`

which is what the summation over dyadic windows needs: `μ` is never larger than the trivial bound
`3n²` times the product of the two norms.  Concretely it suffices to know

* `𝔡₂ ≤ ‖x‖‖y‖` (`Work.HP.Lat.span_pair_lattice`: the lattice `span_ℤ {x,y}` is admissible for
  `dmin 2 {x,y}` and has covolume `√(‖x‖²‖y‖² - ⟨x,y⟩²) ≤ ‖x‖‖y‖`), and
* `𝔡_r ≥ 1` for `r = 2,3` (`Work.HP.Lat.detL_ge_one`: the covolume of an integral lattice is
  `√(det Gram)` with an integral positive definite Gram matrix, hence at least `1`); combined
  with the convention `sInf ∅ = 0` this gives `𝔡_r = 0 ∨ 1 ≤ 𝔡_r`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-! ## `dmin` as an infimum: two elementary consequences -/

/-- The set of determinants over which `dmin` is defined is bounded below by `0`. -/
private lemma bddBelow_dminSet {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    BddBelow {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} := by
  refine ⟨0, ?_⟩
  rintro D ⟨L, -, -, rfl⟩
  exact detL_nonneg L

/-- An admissible lattice gives an upper bound for `dmin`. -/
lemma dmin_le_detL {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ))
    (L : Submodule ℤ (ι → ℤ)) (hr : rk L = r) (hS : S ⊆ L) : dmin r S ≤ detL L :=
  csInf_le (bddBelow_dminSet r S) ⟨L, hr, hS, rfl⟩

/-- If every admissible lattice has determinant at least `c`, then either the defining set of
`dmin` is empty (so `dmin = sInf ∅ = 0`) or `c ≤ dmin`. -/
lemma dmin_eq_zero_or_le {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ))
    {c : ℝ} (h : ∀ L : Submodule ℤ (ι → ℤ), rk L = r → S ⊆ L → c ≤ detL L) :
    dmin r S = 0 ∨ c ≤ dmin r S := by
  set T : Set ℝ := {D | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} with hT
  have hd : dmin r S = sInf T := rfl
  rw [hd]
  by_cases hne : T.Nonempty
  · right
    exact le_csInf hne fun D hD => by
      obtain ⟨L, hr, hS, rfl⟩ := hD
      exact h L hr hS
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-! ## The elementary real-arithmetic core -/

/-- If `d₂ ≥ 1` (or `d₂ = 0`), `d₃ ≥ 1` (or `d₃ = 0`) and `d₂ ≤ c`, then
`max (d₂/d₃) (c/d₂²) ≤ c` for `c ≥ 0`. -/
private lemma max_div_bound (c d2 d3 : ℝ) (hc : 0 ≤ c) (hd2 : d2 = 0 ∨ 1 ≤ d2)
    (hd3 : d3 = 0 ∨ 1 ≤ d3) (hu : d2 ≤ c) : max (d2 / d3) (c / d2 ^ 2) ≤ c := by
  rw [max_le_iff]
  constructor
  · rcases hd3 with h3 | h3
    · rw [h3, div_zero]
      exact hc
    · have hd2nn : 0 ≤ d2 := by rcases hd2 with h | h <;> linarith
      calc d2 / d3 ≤ d2 / 1 := div_le_div_of_nonneg_left hd2nn one_pos h3
        _ = d2 := div_one _
        _ ≤ c := hu
  · rcases hd2 with h2 | h2
    · rw [h2]
      norm_num
      exact hc
    · have hsq : (1 : ℝ) ≤ d2 ^ 2 := one_le_pow₀ h2
      have hpos : 0 < d2 ^ 2 := by linarith
      rw [div_le_iff₀ hpos]
      calc c = c * 1 := by ring
        _ ≤ c * d2 ^ 2 := mul_le_mul_of_nonneg_left hsq hc

/-! ## The main bound -/

theorem muXY_le (d n : ℕ) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hind : LinearIndependent ℤ ![x, y]) :
    muXY n x y ≤ 3 * (n : ℝ) ^ 2 * (eNorm x * eNorm y) := by
  obtain ⟨L, hLrank, hxL, hyL, hLdet⟩ := Lat.span_pair_lattice x y hind
  have hsub : ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hxL
    · exact hyL
  have h2ub : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * eNorm y :=
    (dmin_le_detL 2 ({x, y} : Set (Fin (n + 1) → ℤ)) L hLrank hsub).trans hLdet
  have h2 : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) = 0 ∨
      1 ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    dmin_eq_zero_or_le 2 ({x, y} : Set (Fin (n + 1) → ℤ)) (fun L' _ _ => Lat.detL_ge_one L')
  have h3 : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) = 0 ∨
      1 ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    dmin_eq_zero_or_le 3 ({x, y} : Set (Fin (n + 1) → ℤ)) (fun L' _ _ => Lat.detL_ge_one L')
  have hc : 0 ≤ eNorm x * eNorm y := mul_nonneg (eNorm_nonneg x) (eNorm_nonneg y)
  have hmain := max_div_bound (eNorm x * eNorm y) (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) hc h2 h3 h2ub
  rw [muXY]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Work.HP.MDEstimates
