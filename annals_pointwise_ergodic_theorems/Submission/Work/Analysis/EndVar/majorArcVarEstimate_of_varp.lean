import Mathlib
import Submission.Work.Analysis.EndVar.VarpTools
import Submission.Work.Analysis.EndVar.VarpWeight
import Submission.Work.Analysis.EndVar.VarpQuadTsum

/-!
# **(A)** the major-arc variational estimate from Theorem `varp`

This module proves the reduction `majorArcVarEstimate_of_varp`: the variational paraproduct
estimates of Theorem `varp` (`VarpStatement`) imply the major-arc variational estimate
`MajorArcVarEstimate (majorArcPartR Pj P d C₀) p₁ p₂ p r Cv` for the family of major-arc parts of
the halved averages.

The proof is the last page of §5 of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals 195 (2022):

* `majorArcPartR_eq_sum_varpPiece` (`VarpTools`) writes the major arc part at scale `N` as the
  quadruple sum of the pieces `varpPiece` over the box `0 ≤ l₁,l₂,k₁,k₂ ≤ l_{(N)}` (the arithmetic
  dyadic decomposition `Π_{≤l,≤m} = ∑_{l'≤l} Π_{l',≤m}` followed by the continuous decomposition
  `Π_{l,≤m} = ∑_{s≤M} F^{0,l,s}_N`, with bottom scale `u = 0`);
* the clamping of each piece to its index set `I^{max(l₁,l₂),k₁,k₂}` turns the summand into
  exactly the family estimated by `VarpStatement` at `u = 0`;
* `variationalNorm_quad_tsum_eLpNorm_le` (`VarpQuadTsum`) upgrades the pointwise decomposition to
  the `ℓ^p(ℤ;V^r)` level, reducing the estimate to the quadruple series of the gains
  `2^{-c·lmax(l₁,l₂,k₁,k₂)}`;
* `tsum_rpow_lmax_lt_top` (`VarpWeight`) shows that series is finite, so the constant `Cv Λ` may
  be taken independent of `Λ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-- **The quadruple series of the clamped columns collapses to the finite box of the index set.**
Since `varpCol` vanishes as soon as one of its four indices exceeds the height scale
`l_{(N)} = heightScale C₀ ⌊a n⌋`, the fourfold sum over `ℕ` is the sum over the box
`0 ≤ l₁,l₂,k₁,k₂ ≤ l_{(N)}`. -/
lemma varpCol_quad_tsum_eq_sum (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (n : ℕ) (x : ℤ) :
    (∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ, varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
      = ∑ l₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
  have hvan : ∀ (l₁ l₂ k₁ k₂ : ℕ),
      (heightScale C₀ (Nat.floor (a n)) < l₁ ∨ heightScale C₀ (Nat.floor (a n)) < l₂ ∨
        heightScale C₀ (Nat.floor (a n)) < k₁ ∨ heightScale C₀ (Nat.floor (a n)) < k₂) →
      varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    rintro l₁ l₂ k₁ k₂ (h | h | h | h)
    · exact varpCol_eq_zero (by rintro ⟨h', -, -, -⟩; omega)
    · exact varpCol_eq_zero (by rintro ⟨-, h', -, -⟩; omega)
    · exact varpCol_eq_zero (by rintro ⟨-, -, h', -⟩; omega)
    · exact varpCol_eq_zero (by rintro ⟨-, -, -, h'⟩; omega)
  have h4 : ∀ l₁ l₂ k₁,
      (∑' k₂ : ℕ, varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
        = ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
    intro l₁ l₂ k₁
    refine tsum_eq_sum (fun k₂ hk₂ => ?_)
    simp only [Finset.mem_range, not_lt] at hk₂
    exact hvan l₁ l₂ k₁ k₂ (Or.inr (Or.inr (Or.inr (by omega))))
  have h3 : ∀ l₁ l₂,
      (∑' k₁ : ℕ, ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
        = ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
    intro l₁ l₂
    refine tsum_eq_sum (fun k₁ hk₁ => ?_)
    simp only [Finset.mem_range, not_lt] at hk₁
    exact Finset.sum_eq_zero
      (fun k₂ _ => hvan l₁ l₂ k₁ k₂ (Or.inr (Or.inr (Or.inl (by omega)))))
  have h2 : ∀ l₁,
      (∑' l₂ : ℕ, ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
        = ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
                varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
    intro l₁
    refine tsum_eq_sum (fun l₂ hl₂ => ?_)
    simp only [Finset.mem_range, not_lt] at hl₂
    refine Finset.sum_eq_zero (fun k₁ _ => ?_)
    exact Finset.sum_eq_zero
      (fun k₂ _ => hvan l₁ l₂ k₁ k₂ (Or.inr (Or.inl (by omega))))
  have h1 : (∑' l₁ : ℕ, ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
                varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
        = ∑ l₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
                ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
                  varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
    refine tsum_eq_sum (fun l₁ hl₁ => ?_)
    simp only [Finset.mem_range, not_lt] at hl₁
    refine Finset.sum_eq_zero (fun l₂ _ => ?_)
    refine Finset.sum_eq_zero (fun k₁ _ => ?_)
    exact Finset.sum_eq_zero (fun k₂ _ => hvan l₁ l₂ k₁ k₂ (Or.inl (by omega)))
  calc (∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
          varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
      = ∑' l₁ : ℕ, ∑' l₂ : ℕ,
          ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by simp only [h4, h3]
    _ = ∑' l₁ : ℕ, ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by simp only [h2]
    _ = ∑ l₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
          ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := h1

/-- **The §5 reduction (A)**: Theorem `varp` implies the major-arc variational estimate. -/
theorem majorArcVarEstimate_of_varp {Pj : Work.Analysis.Paraproduct.IWProjections}
    {P : Polynomial ℤ} {d C₀ : ℕ} {p₁ p₂ p : ENNReal} {r : NNReal} (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hmeasPj : ∀ (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      AEMeasurable (Pj.proj l k f) MeasureTheory.Measure.count)
    (hvarp : Work.Analysis.EndVar.VarpStatement Pj P d C₀ p₁ p₂ p r) :
    ∃ Cv : NNReal → NNReal,
      Work.Analysis.EndVar.MajorArcVarEstimate (Work.Analysis.EndVar.majorArcPartR Pj P d C₀)
        p₁ p₂ p r Cv := by
  obtain ⟨c, C, hc, hC⟩ := hvarp
  set W : ℝ≥0∞ := ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ)))) with hWdef
  have hWtop : W < ⊤ := by rw [hWdef]; exact tsum_rpow_lmax_lt_top hc
  have hWne : W ≠ ⊤ := hWtop.ne
  refine ⟨fun _ => C * W.toNNReal, ?_⟩
  intro a Λ f g hΛ ha ha1
  have hb1 : ∀ n : ℕ, ∃ K : ℕ, ∀ l₁ ≥ K, ∀ l₂ k₁ k₂ (x : ℤ),
      varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    intro n
    refine ⟨heightScale C₀ (Nat.floor (a n)) + 1, fun l₁ hl₁ l₂ k₁ k₂ x => ?_⟩
    exact varpCol_eq_zero (by rintro ⟨h', -, -, -⟩; omega)
  have hb2 : ∀ n l₁ : ℕ, ∃ K : ℕ, ∀ l₂ ≥ K, ∀ k₁ k₂ (x : ℤ),
      varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    intro n l₁
    refine ⟨heightScale C₀ (Nat.floor (a n)) + 1, fun l₂ hl₂ k₁ k₂ x => ?_⟩
    exact varpCol_eq_zero (by rintro ⟨-, h', -, -⟩; omega)
  have hb3 : ∀ n l₁ l₂ : ℕ, ∃ K : ℕ, ∀ k₁ ≥ K, ∀ k₂ (x : ℤ),
      varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    intro n l₁ l₂
    refine ⟨heightScale C₀ (Nat.floor (a n)) + 1, fun k₁ hk₁ k₂ x => ?_⟩
    exact varpCol_eq_zero (by rintro ⟨-, -, h', -⟩; omega)
  have hb4 : ∀ n l₁ l₂ k₁ : ℕ, ∃ K : ℕ, ∀ k₂ ≥ K, ∀ x : ℤ,
      varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    intro n l₁ l₂ k₁
    refine ⟨heightScale C₀ (Nat.floor (a n)) + 1, fun k₂ hk₂ x => ?_⟩
    exact varpCol_eq_zero (by rintro ⟨-, -, -, h'⟩; omega)
  have hpt : ∀ (n : ℕ) (x : ℤ), majorArcPartR Pj P d C₀ (a n) f g x
      = ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
          varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x := by
    intro n x
    have h1 : majorArcPartR Pj P d C₀ (a n) f g x
        = ∑ l₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
            ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor (a n)) + 1),
              varpPiece Pj P d (a n) f g l₁ l₂ k₁ k₂ x :=
      congrFun (majorArcPartR_eq_sum_varpPiece Pj P d C₀ (a n) f g) x
    rw [h1, varpCol_quad_tsum_eq_sum Pj P d C₀ a f g n x]
    refine Finset.sum_congr rfl (fun l₁ hl₁ => ?_)
    refine Finset.sum_congr rfl (fun l₂ hl₂ => ?_)
    refine Finset.sum_congr rfl (fun k₁ hk₁ => ?_)
    refine Finset.sum_congr rfl (fun k₂ hk₂ => ?_)
    simp only [Finset.mem_range] at hl₁ hl₂ hk₁ hk₂
    exact (varpCol_eq_piece (by omega : l₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧
      l₂ ≤ heightScale C₀ (Nat.floor (a n)) ∧ k₁ ≤ heightScale C₀ (Nat.floor (a n)) ∧
      k₂ ≤ heightScale C₀ (Nat.floor (a n)))).symm
  have hdecomp : (fun x : ℤ =>
        variationalNorm r (fun n : ℕ => majorArcPartR Pj P d C₀ (a n) f g x))
      = fun x : ℤ => variationalNorm r (fun n : ℕ =>
          ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
            varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    funext x
    congr 1
    funext n
    exact hpt n x
  rw [hdecomp]
  refine (variationalNorm_quad_tsum_eLpNorm_le (r := r) hr (p := p) hp
    (b := fun l₁ l₂ k₁ k₂ n x => varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)
    hb1 hb2 hb3 hb4).trans ?_
  calc ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
        eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x)) p Measure.count
      ≤ ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
          (C : ℝ≥0∞) * ENNReal.ofReal
              ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ))))
            * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
        ENNReal.tsum_le_tsum (fun l₁ => ENNReal.tsum_le_tsum (fun l₂ =>
          ENNReal.tsum_le_tsum (fun k₁ => ENNReal.tsum_le_tsum (fun k₂ =>
            hC a Λ l₁ l₂ 0 (k₁ : ℤ) (k₂ : ℤ) f g hΛ ha ha1))))
    _ = (C : ℝ≥0∞) * W
          * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
        rw [hWdef]
        simp only [mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ = ((C * W.toNNReal : ℝ≥0) : ℝ≥0∞)
          * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hWne]
        ring

end

end Work.Analysis.EndVar
