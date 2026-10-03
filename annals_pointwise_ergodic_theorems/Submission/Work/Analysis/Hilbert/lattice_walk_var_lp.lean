import Mathlib
import Submission.Work.Analysis.Hilbert.lattice_exp_cond_exp
import Submission.Work.Analysis.Probability.lepingle_variation_lp_le

/-!
# The martingale part of the truncation walk is Lépingle-bounded

Combining the two "engine" stones

* `lattice_exp_cond_exp` — the shifted lattice average is the conditional expectation
  `condExp (latticeSpan k τ) count g`, and
* `lattice_exp_average` — averaging those conditional expectations over a complete residue system
  of shifts gives the triangular smoothing `triConv k g`,

with the tree's Lépingle inequality `Work.Analysis.Probability.lepingle_variation_lp_le`, this file
proves that the variation of the "martingale part" of the truncation walk of the discrete Hilbert
transform is controlled by `‖g‖_{ℓ^p}`.

The σ-algebras `latticeSpan k τ` are *decreasing* in `k`, so `k ↦ latticeExp k τ g` is a reverse
martingale; reading the index backwards from scale `K` gives the filtration
`latticeFiltration K τ j = latticeSpan (K - j) τ` and the honest `condExp`-martingale
`j ↦ condExp (latticeFiltration K τ j) count g`.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Work.Analysis.Hilbert

noncomputable section

/-! ## On the counting measure, almost-everywhere is everywhere -/

lemma ae_count_iff {α : Type*} [MeasurableSpace α] {p : α → Prop} :
    (∀ᵐ x ∂(Measure.count : Measure α), p x) ↔ ∀ x, p x := by
  rw [MeasureTheory.ae_iff, MeasureTheory.Measure.count_eq_zero_iff]
  constructor
  · intro h x
    by_contra hx
    have : x ∈ ({x : α | ¬ p x} : Set α) := hx
    rw [h] at this
    exact this
  · intro h
    ext x
    simp [h x]

lemma ae_eq_count_iff {α β : Type*} [MeasurableSpace α] {f g : α → β} :
    f =ᵐ[Measure.count] g ↔ ∀ x, f x = g x :=
  ae_count_iff

/-! ## The filtration of the shifted lattices, read backwards -/

/-- The filtration whose `j`-th σ-algebra is the shifted lattice of scale `2^{K-j}`. -/
def latticeFiltration (K : ℕ) (τ : ℤ) : Filtration ℕ (⊤ : MeasurableSpace ℤ) where
  seq j := latticeSpan (K - j) τ
  mono' := fun i j hij => latticeSpan_anti (Nat.sub_le_sub_left hij K) τ
  le' := fun _ => le_top

lemma latticeFiltration_apply (K : ℕ) (τ : ℤ) (j : ℕ) :
    (latticeFiltration K τ) j = latticeSpan (K - j) τ := rfl

lemma condExp_latticeFiltration (K : ℕ) (τ : ℤ) (j : ℕ) (g : ℤ → ℝ)
    (hg : Integrable g (Measure.count : Measure ℤ)) :
    (fun n => MeasureTheory.condExp ((latticeFiltration K τ) j) (Measure.count : Measure ℤ) g n)
      = fun n => latticeExpR (K - j) τ g n := by
  rw [latticeFiltration_apply]
  funext n
  exact (ae_eq_count_iff.mp (lattice_exp_cond_exp (K - j) τ g hg).symm) n

/-! ## Lépingle for the lattice walk -/

theorem latticeWalk_var_le {p r : ℝ} (hp : 1 < p) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (τ : ℤ) (g : ℤ → ℝ),
      Integrable g (Measure.count : Measure ℤ) →
      MemLp g (ENNReal.ofReal p) (Measure.count : Measure ℤ) →
      eLpNorm (fun ω : ℤ => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |latticeExpR (K - u.1 (j + 1)) τ g ω - latticeExpR (K - u.1 j) τ g ω| ^ r) ^ (1 / r))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  obtain ⟨C, hC, hlep⟩ := Work.Analysis.Probability.lepingle_variation_lp_le hp hr
  refine ⟨C, hC, fun K τ g hg hgp => ?_⟩
  have h := hlep (Measure.count : Measure ℤ) (latticeFiltration K τ) g hgp
  refine le_trans (le_of_eq ?_) h
  refine MeasureTheory.eLpNorm_congr_ae ?_
  have hcond : ∀ m : ℕ,
      (fun n => MeasureTheory.condExp ((latticeFiltration K τ) m) (Measure.count : Measure ℤ) g n)
        = fun n => latticeExpR (K - m) τ g n := fun m => condExp_latticeFiltration K τ m g hg
  filter_upwards with ω
  congr 1
  ext u
  congr 1
  ext J
  congr 1
  exact Finset.sum_congr rfl fun j _ => by simp only [hcond]





/-! ## Chain reversal: increasing chains in the scale are the reversed Lépingle chains -/

/-! ## The `ℝ≥0∞`-supremum of a bounded family of `ofReal`s -/

/-- For a bounded-above family of nonnegative reals, the `ℝ≥0∞`-supremum of the `ofReal`s is the
`ofReal` of the real supremum.  (The reverse inequality is `ENNReal.ofReal_iSup_le`.) -/
lemma iSup_ofReal_le_ofReal_iSup {ι : Type*} (f : ι → ℝ) (hb : BddAbove (Set.range f)) :
    (⨆ i, ENNReal.ofReal (f i)) ≤ ENNReal.ofReal (⨆ i, f i) :=
  iSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup hb i)


/-- **The sup-type bridge.**  If a family of reals is bounded above by an explicit constant `C`, then
the `ℝ≥0∞`-supremum of the `ofReal`s is dominated by `ofReal (max 0 C)`.  This is the form in which
the `ℝ`-valued left-hand side of the tree's Lépingle inequality
(`Work.Analysis.Probability.lepingle_variation_lp_le`) converts into the `ℝ≥0∞`-valued variation
`varPathC`/`Vpath`: the chain-sums over a *fixed horizon* form a bounded family. -/
lemma iSup_ofReal_le_ofReal_bound {ι : Type*} (f : ι → ℝ) {C : ℝ} (h : ∀ i, f i ≤ C) :
    (⨆ i, ENNReal.ofReal (f i)) ≤ ENNReal.ofReal (max 0 C) :=
  iSup_le fun i => ENNReal.ofReal_le_ofReal (le_trans (h i) (le_max_right 0 C))

end

end Work.Analysis.Hilbert
