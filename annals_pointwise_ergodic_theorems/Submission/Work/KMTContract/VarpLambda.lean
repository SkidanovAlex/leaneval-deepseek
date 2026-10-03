/-
# The Λ-dependent form of Theorem `varp`, and the `end-var` assembly on it

This module is part of the contract of `Submission/Work/KMTContract/` (see
`Submission/Work/KMTPlan/ROUTE_LEAD.md`, §3.0 step A0, and the findings F2/F3/F4 of its §0).

**Why a Λ-dependent constant is forced.**  The workspace's `Work.Analysis.EndVar.VarpStatement`
asks for a constant `C : ℝ≥0` that is *uniform in the lacunarity parameter* `Λ` of the scale
sequence.  That statement is (at least) an open problem: as `Λ → 1⁺` a finite `Λ`-lacunary set can
contain any prescribed finite set of integers, so a `Λ`-uniform bound would give the *full*
variational estimate, which Krause--Mirek--Tao list as open question 2 of the paper.  The paper's
Theorem `varp` has a constant depending on `λ = Λ`.  Accordingly the contract uses

* `VarpStatementΛ` — Theorem `varp` with the constant `C : ℝ≥0 → ℝ≥0` a function of the
  lacunarity parameter, stated for exactly the family of columns `varpCol` (bottom scale `u = 0`,
  `s₁, s₂ ∈ ℕ`) that the §5 assembly consumes;

and this module reproves the §5 reduction **(A)** (`majorArcVarEstimate_of_varpΛ`: the major-arc
variational estimate from Theorem `varp`) and the capstone
`exists_varEstHalfFin_of_varpΛ_minorArc` (`end-var` from `varp` + the single-scale minor arc
input) on that statement.  The proofs are the ones of
`Work.Analysis.EndVar.majorArcVarEstimate_of_varp` /
`Work.Analysis.EndVar.exists_varEstHalfFin_of_varp_minorArc` with the constant `C` replaced by
`C Λ`; everything else (the quadruple arithmetic/continuous dyadic decomposition of §5, the
geometric summation, the clamping and the assembly) is reused verbatim from the `EndVar` chapter.
-/
import Mathlib
import Submission.Work.Analysis.EndVar.Assembly
import Submission.Work.KMTContract.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTContract

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.Analysis.Paraproduct (IWProjections)

/-- **Theorem `varp` with a lacunarity-dependent constant** (Krause--Mirek--Tao §4).

There are a rate `c > 0` — depending only on `P`, the exponents and (in the paper) on the
lacunarity, but *not* on `ρ` — and a constant `C : ℝ≥0 → ℝ≥0` such that for every `Λ > 1`, every
`Λ`-lacunary sequence `a` with `a n ≥ 1`, every height parameters `l₁, l₂` and every `s₁, s₂ ∈ ℕ`
the columns `varpCol` (the §5 pieces `Ã_N(F^{0,l₁,s₁}_N f, G^{0,l₂,s₂}_N g)` clamped to the index
set `I^{max(l₁,l₂),s₁,s₂} = {N : max(l₁,l₂), s₁, s₂ ≤ l_{(N)}}`) obey

`‖ (varpCol …)_N ‖_{ℓ^p(ℤ;V^r)} ≤ C Λ · 2^{-c·max(max l₁ l₂)(max s₁ s₂)} ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`.

This is the form in which the §5 assembly consumes Theorem `varp`: the constant depends on the
lacunarity parameter `Λ` of the sequence of scales (which is what makes the small scales
`N < C₃` harmless, see `ROUTE_LEAD.md` §1.2 S1), and only the bottom scale `u = 0` with
non-negative `s` occurs (S2).  See the module docstring for why `C` cannot be `Λ`-independent. -/
def VarpStatementΛ (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ)
    (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) : Prop :=
  ∃ (c : ℝ) (C : ℝ≥0 → ℝ≥0), 0 < c ∧
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x))
        p Measure.count
      ≤ (C Λ : ℝ≥0∞) *
          ENNReal.ofReal ((2 : ℝ) ^ (-(c * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count


/-- **The §5 reduction (A)**: Theorem `varp` implies the major-arc variational estimate. -/
theorem majorArcVarEstimate_of_varpΛ {Pj : Work.Analysis.Paraproduct.IWProjections}
    {P : Polynomial ℤ} {d C₀ : ℕ} {p₁ p₂ p : ENNReal} {r : NNReal} (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hmeasPj : ∀ (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
      AEMeasurable (Pj.proj l k f) MeasureTheory.Measure.count)
    (hvarp : VarpStatementΛ Pj P d C₀ p₁ p₂ p r) :
    ∃ Cv : NNReal → NNReal,
      MajorArcVarEstimate (majorArcPartR Pj P d C₀)
        p₁ p₂ p r Cv := by
  obtain ⟨c, C, hc, hC⟩ := hvarp
  set W : ℝ≥0∞ := ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ)))) with hWdef
  have hWtop : W < ⊤ := by rw [hWdef]; exact tsum_rpow_lmax_lt_top hc
  have hWne : W ≠ ⊤ := hWtop.ne
  refine ⟨fun Λ => C Λ * W.toNNReal, ?_⟩
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
          (C Λ : ℝ≥0∞) * ENNReal.ofReal
              ((2 : ℝ) ^ (-(c * ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℤ) : ℝ))))
            * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count :=
        ENNReal.tsum_le_tsum (fun l₁ => ENNReal.tsum_le_tsum (fun l₂ =>
          ENNReal.tsum_le_tsum (fun k₁ => ENNReal.tsum_le_tsum (fun k₂ =>
            hC a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1))))
    _ = (C Λ : ℝ≥0∞) * W
          * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
        rw [hWdef]
        simp only [mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ = ((C Λ * W.toNNReal : ℝ≥0) : ℝ≥0∞)
          * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hWne]
        ring


/-- **The capstone on the Λ-dependent statement**: `end-var` from `varp` and the single-scale
minor arc input.  This is `Work.Analysis.EndVar.exists_varEstHalfFin_of_varp_minorArc` with the
Λ-uniform `VarpStatement` replaced by the forced Λ-dependent `VarpStatementΛ`. -/
theorem exists_varEstHalfFin_of_varpΛ_minorArc {Pj : IWProjections} {P : Polynomial ℤ}
    {d C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0} (hr : 1 ≤ r) (hp : 1 ≤ p)
    (hvarp : VarpStatementΛ Pj P d C₀ p₁ p₂ p r) (hB : MinorArcInput Pj P d C₀ p₁ p₂ p) :
    ∃ Cv : ℝ≥0 → ℝ≥0, VarEstHalfFin TZ Measure.count P p₁ p₂ p r Cv := by
  obtain ⟨Cv, hA⟩ := majorArcVarEstimate_of_varpΛ hr hp
    (fun _ _ f => (measurable_of_countable _).aemeasurable) hvarp
  exact Work.Analysis.EndVar.exists_varEstHalfFin_of_majorArcVar_minorArc
    ⟨Cv, hA⟩ hB hp hr

end

end Work.KMTContract
