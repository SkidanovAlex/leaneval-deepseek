import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability of the weight `⟨k⟩^{-2N}` on the lattice `ℤ^ι`

Layer A of the STE development needs the multi-dimensional `p`-series `∑_{k : ℤ^ι} ⟨k⟩^{-2N}`
to converge as soon as `card ι < 2 * N`, where `⟨k⟩² = 1 + ∑ kᵢ²` is `Work.Diff.STE.wt`
(see `Submission/Work/Diff/STE/Torus.lean`).

We obtain this from the general `p`-series on a lattice, `ZLattice.summable_norm_rpow`
(Mathlib, `Mathlib/Algebra/Module/ZLattice/Summable.lean`): if `L` is a `ℤ`-lattice of rank `d`
in a finite dimensional real normed space, then `∑_{z : L} ‖z‖^r` converges for `r < -d`.
For the standard lattice `ℤ^ι ⊆ ι → ℝ` (equipped with the ambient sup norm) the rank is
`card ι`, and `‖k‖² ≤ ⟨k⟩²`, which gives exactly the exponent range `card ι < 2 * N`.

Main results:

* `Work.Diff.STE.summable_norm_intCast_rpow` — the `p`-series `∑_{k : ℤ^ι} ‖k‖^r` on the
  standard lattice, for any `r < -card ι`;
* `Work.Diff.STE.summable_wt_zpow` — `∑_{k : ℤ^ι} ⟨k⟩^{-2N}` converges when `card ι < 2 * N`.
-/

noncomputable section

namespace Work.Diff.STE

open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `p`-series on the standard lattice `ℤ^ι`.**  For `r < -card ι` the function
`k ↦ ‖k‖ ^ r` (the ambient norm on `ι → ℝ`, i.e. the sup norm) is summable over `ℤ^ι`.

This is the multi-dimensional `p`-series used throughout Layer A: instantiating
`r = -(s - j)` gives `∑_k ⟨k⟩^{-2(s-j)} < ∞` whenever `s - j > card ι / 2`. -/
theorem summable_norm_intCast_rpow (r : ℝ) (hr : r < -(Fintype.card ι : ℝ)) :
    Summable (fun k : ι → ℤ => ‖(fun i => (k i : ℝ))‖ ^ r) := by
  let L : Submodule ℤ (ι → ℝ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  haveI hdisc : DiscreteTopology L := ZSpan.discreteTopology_pi_basisFun
  have hcard : Module.finrank ℤ L = Fintype.card ι := by
    rw [ZLattice.rank ℝ L, Module.finrank_fintype_fun_eq_card]
  have hLs : Summable (fun z : L => ‖z‖ ^ r) := by
    refine ZLattice.summable_norm_rpow L r ?_
    rw [hcard]
    exact hr
  -- the integer vector `k` is the element `∑ i, (k i) • eᵢ` of the lattice
  have hrepr : ∀ k : ι → ℤ, (fun i => (k i : ℝ)) = ∑ i, (k i : ℤ) • (Pi.basisFun ℝ ι) i := by
    intro k
    ext j
    simp only [Finset.sum_apply, Pi.basisFun_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro hj; simp at hj
  have hmem : ∀ k : ι → ℤ, (fun i => (k i : ℝ)) ∈ L := by
    intro k
    rw [hrepr k]
    change (∑ i, (k i : ℤ) • (Pi.basisFun ℝ ι) i) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (show Pi.basisFun ℝ ι i ∈ Set.range (Pi.basisFun ℝ ι) from
          Set.mem_range_self i))
  let toL : (ι → ℤ) → L := fun k => Subtype.mk (fun i => (k i : ℝ)) (hmem k)
  have toL_inj : Function.Injective toL := by
    intro k k' h
    funext i
    have h1 : (k i : ℝ) = (k' i : ℝ) := by
      have := congrFun (congrArg Subtype.val h) i
      simpa [toL] using this
    exact_mod_cast h1
  refine (hLs.comp_injective toL_inj).congr fun k => ?_
  show ‖toL k‖ ^ r = ‖(fun i => (k i : ℝ))‖ ^ r
  rw [← Submodule.norm_coe (toL k)]

/-- The norm bound `‖k‖² ≤ ⟨k⟩²` on the integer lattice: the sup norm squared is the largest
square coordinate, hence at most the sum of squares occurring in `wt`. -/
lemma sq_norm_intCast_le_wt (k : ι → ℤ) :
    ‖(fun i => (k i : ℝ))‖ ^ 2 ≤ wt k := by
  have hsum : 0 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm : ‖(fun i => (k i : ℝ))‖ ≤ Real.sqrt (∑ i, ((k i : ℤ) : ℝ) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    have hcoord : ‖((fun i => (k i : ℝ)) i)‖ = |((k i : ℤ) : ℝ)| := by
      simp [Real.norm_eq_abs]
    rw [hcoord, Real.le_sqrt (abs_nonneg _) hsum, sq_abs]
    exact Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ‖(fun i => (k i : ℝ))‖ ^ 2 ≤ (Real.sqrt (∑ i, ((k i : ℤ) : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [Real.sq_sqrt hsum] at h2
  have hwt : wt k = 1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2 := rfl
  rw [hwt]
  linarith

/-- **Summability of the weight `⟨k⟩^{-2N}` on `ℤ^ι`.** -/
theorem summable_wt_zpow {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (hN : Fintype.card ι < 2 * N) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (-(N : ℤ))) := by
  have hr : -(2 * (N : ℝ)) < -(Fintype.card ι : ℝ) := by
    rw [neg_lt_neg_iff]
    exact_mod_cast hN
  refine Summable.of_norm_bounded_eventually
    (f := fun k : ι → ℤ => (wt k) ^ (-(N : ℤ)))
    (g := fun k : ι → ℤ => ‖(fun i => (k i : ℝ))‖ ^ (-(2 * (N : ℝ))))
    (summable_norm_intCast_rpow (ι := ι) _ hr) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ι → ℤ)] with k hk
  have hkne : (fun i => (k i : ℝ)) ≠ 0 := by
    intro h
    refine hk (funext fun i => ?_)
    have : (k i : ℝ) = 0 := by simpa using congrFun h i
    exact_mod_cast this
  have hpos : 0 < ‖(fun i => (k i : ℝ))‖ := norm_pos_iff.mpr hkne
  have hpos2 : 0 < ‖(fun i => (k i : ℝ))‖ ^ 2 := pow_pos hpos 2
  have hfnn : 0 ≤ (wt k) ^ (-(N : ℤ)) := zpow_nonneg (wt_pos k).le _
  rw [Real.norm_of_nonneg hfnn]
  have hbridge : (wt k) ^ (-(N : ℤ)) = (wt k) ^ (-(N : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  rw [hbridge]
  refine (Real.rpow_le_rpow_of_nonpos hpos2 (sq_norm_intCast_le_wt k) (by linarith)).trans ?_
  rw [← Real.rpow_two ‖(fun i => (k i : ℝ))‖, ← Real.rpow_mul (norm_nonneg _),
    show (2 : ℝ) * -(N : ℝ) = -(2 * (N : ℝ)) by ring]

end Work.Diff.STE
