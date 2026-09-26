import Mathlib
import Submission.Work.Modular.Poisson.Std

/-!
# Summability of `(1 + ‖intVec m‖) ^ (-N)` over `ℤ^ι`

For an integer vector `m : ι → ℤ` with `Fintype.card ι = d`, the series
`∑_{m : ι → ℤ} (1 + ‖intVec m‖) ^ (-N)` converges as soon as `N > d`.

This is the standard `p`-series bound on the lattice `ℤ^d ⊆ ℝ^d`, obtained here from
Mathlib's `ZLattice.summable_norm_zpow` applied to the standard lattice
`Work.Modular.stdLattice ι = span ℤ (range (Pi.basisFun ℝ ι))`.
-/

set_option linter.style.haveILetI false

namespace Work.Poisson

open Work.Modular

/-- On nonzero vectors the `N`-th power of `1 + ‖v‖` is at least the `N`-th power of `‖v‖`,
so the negative powers are ordered the other way. -/
private lemma zpow_neg_le_of_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (N : ℕ) :
    s ^ (-(N : ℤ)) ≤ r ^ (-(N : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (hr.trans_le hrs) N) (pow_pos hr N)).mpr
    (pow_le_pow_left₀ hr.le hrs N)

theorem summable_intVec_zpow_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (hN : Fintype.card ι < N) :
    Summable fun m : ι → ℤ => (1 + ‖Work.Modular.intVec m‖) ^ (-(N : ℤ)) := by
  haveI : DiscreteTopology (stdLattice ι) := by unfold stdLattice; infer_instance
  haveI : IsZLattice ℝ (stdLattice ι) := by unfold stdLattice; infer_instance
  -- The standard lattice `ℤ^ι` has rank `card ι`.
  have hfin : Module.finrank ℤ (stdLattice ι) = Fintype.card ι := by
    rw [ZLattice.rank ℝ (stdLattice ι)]; simp
  -- Hence `-N < -rank` because `card ι < N`.
  have hn : (-(N : ℤ)) < -Module.finrank ℤ (stdLattice ι) := by
    rw [hfin]
    exact neg_lt_neg_iff.mpr (by exact_mod_cast hN)
  -- Mathlib: the `p`-series over a lattice of rank `d` converges for `p < -d`.
  have hsumm : Summable fun z : stdLattice ι => ‖z‖ ^ (-(N : ℤ)) :=
    ZLattice.summable_norm_zpow (stdLattice ι) (-(N : ℤ)) hn
  -- `intVec` is a bijection from `ι → ℤ` onto the standard lattice.
  have hmem : ∀ m : ι → ℤ, intVec m ∈ stdLattice ι := by
    intro m
    rw [stdLattice, Module.Basis.mem_span_iff_repr_mem]
    intro i
    exact ⟨m i, by simp [intVec]⟩
  have hinj : Function.Injective (fun m : ι → ℤ => (⟨intVec m, hmem m⟩ : stdLattice ι)) := by
    intro m m' h
    have h1 : intVec m = intVec m' := congrArg Subtype.val h
    funext i
    have h2 := congrFun h1 i
    simp only [intVec_apply] at h2
    exact_mod_cast h2
  have hsumm2 : Summable fun m : ι → ℤ => ‖intVec m‖ ^ (-(N : ℤ)) := by
    have h := hsumm.comp_injective hinj
    have hfun : (fun m : ι → ℤ => ‖intVec m‖ ^ (-(N : ℤ))) =
        (fun z : stdLattice ι => ‖z‖ ^ (-(N : ℤ))) ∘
          (fun m => (⟨intVec m, hmem m⟩ : stdLattice ι)) := by
      funext m
      simp
    rw [hfun]
    exact h
  -- Finally compare `(1 + ‖v‖) ^ (-N)` with `‖v‖ ^ (-N)`, which differs only at `v = 0`.
  refine hsumm2.of_norm_bounded_eventually ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ι → ℤ)).subset ?_
  intro m hm
  by_contra hne
  refine hm ?_
  have hpos : 0 < ‖intVec m‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hm0 : m = 0 := by
      funext i
      have h2 := congrFun hzero i
      simp only [intVec_apply, Pi.zero_apply] at h2
      exact_mod_cast h2
    exact hne hm0
  rw [Real.norm_eq_abs, abs_of_nonneg (zpow_nonneg (by positivity) _)]
  exact zpow_neg_le_of_le hpos (by linarith) N

end Work.Poisson
