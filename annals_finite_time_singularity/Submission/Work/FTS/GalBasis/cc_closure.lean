/-
# `Work.FTS.GalBasis.cc_closure` — the test-function class `Ccφ` is closed under the
operations of the Galerkin span

`Ccφ f` (def. `Defs.lean`) says: `f` is `C^∞` on all of `ℝ²` and is supported *strictly inside*
a box `[a,b] × [δ, π/2-δ]` with `0 < a < b`, `0 < δ < π/2`.

The point of this file is that this class is closed under the four operations that build the
Galerkin span: addition, subtraction, scalar multiplication and *finite* linear combination
(`galFun φ c = ∑_{k : Fin n} c k · φ k`).  Each closure step only has to produce *some* box:

* for a *single* `f` (scalar multiples, and the zero function) any box that works for `f`
  works for the multiple, because `c * 0 = 0`;
* for a *pair* `f, g` one enlarges as follows.  If `f` is supported in `[a₁,b₁] × [δ₁, π/2-δ₁]`
  and `g` in `[a₂,b₂] × [δ₂, π/2-δ₂]`, then both are supported in the common box
  `[min a₁ a₂, max b₁ b₂] × [min δ₁ δ₂, π/2 - min δ₁ δ₂]`
  (the lower end decreases, the upper end increases, so the box contains both), and `f ± g`
  is supported there.  The same enlargement is applied to the two *inner* boxes, which is the
  box the resulting `Ccφ`-witness exhibits (`Ccφ` asks the support to be inside a box strictly
  smaller than the regularity box; both requirements are met by the pointwise min/max box).
  Strictness is preserved because `min δ₁' δ₂' ≤ δ₁' < π/2 - δ₁' ≤ π/2 - min δ₁' δ₂'`.

The finiteness of the span is handled by induction over the `Finset` of indices, with the
empty combination being the zero function.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.GalBasis.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## The zero function -/

/-- The zero profile is a test function: it is `C^∞` and vanishes off any box. -/
theorem Ccφ.zero : Ccφ (fun _ _ : ℝ => (0 : ℝ)) := by
  refine ⟨1, 2, 1 / 10, by norm_num, by norm_num, by norm_num, by linarith [Real.pi_gt_three],
    ?_, 11 / 10, 19 / 10, 1 / 8, by norm_num, by norm_num, by norm_num, by norm_num,
    by linarith [Real.pi_gt_three], ?_⟩
  · rw [show Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ : ℝ × ℝ => (0 : ℝ) from rfl]
    exact contDiff_const
  · intro z θ _
    rfl

/-! ## Closure under addition -/

/-- `Ccφ` is closed under addition: the two support boxes are replaced by their pointwise
enclosure (min of the lower ends, max of the upper ends). -/
theorem Ccφ.add {f g : Fn} (hf : Ccφ f) (hg : Ccφ g) :
    Ccφ (fun z θ => f z θ + g z θ) := by
  obtain ⟨a₁, b₁, δ₁, ha₁, hab₁, hδ₁, hδπ₁, hd₁, a₁', b₁', δ₁', haa₁, hab₁', hbb₁, hδδ₁,
    hδδπ₁, hs₁⟩ := hf
  obtain ⟨a₂, b₂, δ₂, ha₂, hab₂, hδ₂, hδπ₂, hd₂, a₂', b₂', δ₂', haa₂, hab₂', hbb₂, hδδ₂,
    hδδπ₂, hs₂⟩ := hg
  refine ⟨min a₁ a₂, max b₁ b₂, min δ₁ δ₂, lt_min ha₁ ha₂, ?_, lt_min hδ₁ hδ₂,
    lt_of_le_of_lt (min_le_left _ _) hδπ₁, ?_,
    min a₁' a₂', max b₁' b₂', min δ₁' δ₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁) (le_max_left _ _)
  · rw [show Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
        = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p from rfl]
    exact hd₁.add hd₂
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) haa₁) (lt_of_le_of_lt (min_le_right _ _) haa₂)
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁') (le_max_left _ _)
  · exact max_lt (lt_of_lt_of_le hbb₁ (le_max_left _ _)) (lt_of_lt_of_le hbb₂ (le_max_right _ _))
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) hδδ₁) (lt_of_le_of_lt (min_le_right _ _) hδδ₂)
  · have h1 : δ₁' < π / 4 := by linarith
    have h3 : min δ₁' δ₂' < π / 4 := lt_of_le_of_lt (min_le_left _ _) h1
    linarith
  · intro z θ hz
    have hf' : SuppIn f (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₁.mono (min_le_left _ _) (le_max_left _ _) (min_le_left _ _)
        (by linarith [min_le_left δ₁' δ₂'])
    have hg' : SuppIn g (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₂.mono (min_le_right _ _) (le_max_right _ _) (min_le_right _ _)
        (by linarith [min_le_right δ₁' δ₂'])
    simp [hf' z θ hz, hg' z θ hz]

/-! ## Closure under subtraction -/

/-- `Ccφ` is closed under subtraction (same box argument as for addition). -/
theorem Ccφ.sub {f g : Fn} (hf : Ccφ f) (hg : Ccφ g) :
    Ccφ (fun z θ => f z θ - g z θ) := by
  obtain ⟨a₁, b₁, δ₁, ha₁, hab₁, hδ₁, hδπ₁, hd₁, a₁', b₁', δ₁', haa₁, hab₁', hbb₁, hδδ₁,
    hδδπ₁, hs₁⟩ := hf
  obtain ⟨a₂, b₂, δ₂, ha₂, hab₂, hδ₂, hδπ₂, hd₂, a₂', b₂', δ₂', haa₂, hab₂', hbb₂, hδδ₂,
    hδδπ₂, hs₂⟩ := hg
  refine ⟨min a₁ a₂, max b₁ b₂, min δ₁ δ₂, lt_min ha₁ ha₂, ?_, lt_min hδ₁ hδ₂,
    lt_of_le_of_lt (min_le_left _ _) hδπ₁, ?_,
    min a₁' a₂', max b₁' b₂', min δ₁' δ₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁) (le_max_left _ _)
  · rw [show Function.uncurry (fun z θ : ℝ => f z θ - g z θ)
        = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p from rfl]
    exact hd₁.sub hd₂
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) haa₁) (lt_of_le_of_lt (min_le_right _ _) haa₂)
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁') (le_max_left _ _)
  · exact max_lt (lt_of_lt_of_le hbb₁ (le_max_left _ _)) (lt_of_lt_of_le hbb₂ (le_max_right _ _))
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) hδδ₁) (lt_of_le_of_lt (min_le_right _ _) hδδ₂)
  · have h1 : δ₁' < π / 4 := by linarith
    have h3 : min δ₁' δ₂' < π / 4 := lt_of_le_of_lt (min_le_left _ _) h1
    linarith
  · intro z θ hz
    have hf' : SuppIn f (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₁.mono (min_le_left _ _) (le_max_left _ _) (min_le_left _ _)
        (by linarith [min_le_left δ₁' δ₂'])
    have hg' : SuppIn g (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₂.mono (min_le_right _ _) (le_max_right _ _) (min_le_right _ _)
        (by linarith [min_le_right δ₁' δ₂'])
    simp [hf' z θ hz, hg' z θ hz]

/-! ## Closure under scalar multiplication -/

/-- `Ccφ` is closed under scalar multiplication: the box of `f` also supports `c * f`
(because `c * 0 = 0`), so no enlargement is needed. -/
theorem Ccφ.smul (c : ℝ) {f : Fn} (hf : Ccφ f) : Ccφ (fun z θ => c * f z θ) := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδπ, hd, a', b', δ', haa, hab', hbb, hδδ, hδδπ, hs⟩ := hf
  refine ⟨a, b, δ, ha, hab, hδ, hδπ, ?_, a', b', δ', haa, hab', hbb, hδδ, hδδπ, ?_⟩
  · rw [show Function.uncurry (fun z θ : ℝ => c * f z θ)
        = fun p : ℝ × ℝ => c * Function.uncurry f p from rfl]
    simpa using hd.const_smul c
  · intro z θ hz
    show c * f z θ = 0
    rw [hs z θ hz, mul_zero]

/-! ## Closure under finite linear combinations -/

/-- `Ccφ` is closed under an arbitrary finite linear combination: induction over the `Finset`
of indices, using the empty combination (the zero function), addition and scalar
multiplication. -/
theorem Ccφ.finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → Fn)
    (h : ∀ i ∈ s, Ccφ (F i)) : Ccφ (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Ccφ.zero
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact Ccφ.add (Ccφ.smul (c a) (h a (Finset.mem_insert_self a s)))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- `galFun φ c = ∑_{k : Fin n} c k · φ k` is a test function whenever all the `φ k` are. -/
theorem Ccφ.galFun {n : ℕ} (φ : ℕ → Fn) (c : Fin n → ℝ) (h : ∀ k : Fin n, Ccφ (φ k)) :
    Ccφ (galFun φ c) := by
  show Ccφ (fun z θ => ∑ k : Fin n, c k * φ (k : ℕ) z θ)
  exact Ccφ.finset_sum Finset.univ c (fun k => φ (k : ℕ)) (fun k _ => h k)

/-! ## The target -/

theorem cc_closure :
    (∀ f g : Work.FTS.Galerkin.Fn, Ccφ f → Ccφ g → Ccφ (fun z θ => f z θ + g z θ)) ∧
    (∀ f g : Work.FTS.Galerkin.Fn, Ccφ f → Ccφ g → Ccφ (fun z θ => f z θ - g z θ)) ∧
    (∀ (c : ℝ) (f : Work.FTS.Galerkin.Fn), Ccφ f → Ccφ (fun z θ => c * f z θ)) ∧
    (∀ (n : ℕ) (φ : ℕ → Work.FTS.Galerkin.Fn), (∀ k : Fin n, Ccφ (φ k)) → ∀ c : Fin n → ℝ,
      Ccφ (Work.FTS.Galerkin.galFun φ c)) := by
  exact ⟨fun f g hf hg => Ccφ.add hf hg, fun f g hf hg => Ccφ.sub hf hg,
    fun c f hf => Ccφ.smul c hf, fun n φ h c => Ccφ.galFun φ c h⟩

end Work.FTS.GalBasis
