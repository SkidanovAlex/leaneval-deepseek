/-
  Area C4aU: from the finite cluster set to a finite exponent set.

  `ClusterSet Y` is countable (`clusterSet_countable`) and existentially definable
  (`clusterFam_rexExist`), hence finite by uniform finiteness at `k = 0`
  (`finite_of_countable_rexExist`).  Every exponent `q` that occurs for some parameter `c` has
  `2 ^ q` in the cluster set (`ratioCluster_of_asymSect` together with `xSupp_eventually`), and
  `q ↦ 2 ^ q` is injective on `ℚ`, so the occurring exponents form a finite set: the preimage of
  the finite set `ClusterSet Y` under `expPreimage`.
-/
import Submission.Work.WilC4aU.Defs

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical Topology
namespace Work.WilC4aU

open WilkiesDesign.CG.C4a (PBOne)

/-- The rational `q` with `2 ^ q = lam`, if it exists (default `0`). -/
def expPreimage (lam : ℝ) : ℚ :=
  if h : ∃ q : ℚ, (2 : ℝ) ^ (q : ℝ) = lam then h.choose else 0

/-- `expPreimage` is a left inverse of `q ↦ 2 ^ q` on `ℚ`. -/
theorem expPreimage_exp (q : ℚ) : expPreimage ((2 : ℝ) ^ (q : ℝ)) = q := by
  have hwit : ∃ q' : ℚ, (2 : ℝ) ^ (q' : ℝ) = (2 : ℝ) ^ (q : ℝ) := ⟨q, rfl⟩
  have hinj : ∀ x y : ℝ, (2 : ℝ) ^ x = (2 : ℝ) ^ y → x = y := by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd hxy (ne_of_lt ((Real.rpow_lt_rpow_left_iff one_lt_two).mpr hlt))
    · exact heq
    · exact absurd hxy.symm (ne_of_lt ((Real.rpow_lt_rpow_left_iff one_lt_two).mpr hgt))
  rw [expPreimage, dite_eq_left hwit]
  exact_mod_cast hinj _ _ hwit.choose_spec

/-- **C4aU.Extract.**  If every fibre is either eventually zero or asymptotic to `a * x ^ q` with
`a ≠ 0`, and the cluster-value set of the ratios `f (2 x) / f x` is finite, then one FINITE set of
exponents `Qs` serves all fibres. -/
theorem exists_exponent_finset {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (h1 : ∀ c : Fin k → ℝ, PBOne Y c)
    (hpair : ∀ (c : Fin k → ℝ) (q : ℚ) (a : ℝ), AsymSect Y c q a → ¬ ZeroSect Y c →
      RatioCluster Y c ((2 : ℝ) ^ (q : ℝ)))
    (hfin : (ClusterSet Y).Finite) :
    ∃ Qs : Finset ℚ, ∀ c : Fin k → ℝ,
      ZeroSect Y c ∨ ∃ q ∈ Qs, ∃ a : ℝ, AsymSect Y c q a := by
  refine ⟨hfin.toFinset.image expPreimage, fun c => ?_⟩
  rcases (pbOne_iff Y c).mp (h1 c) with hZ | ⟨q, a, hA⟩
  · exact Or.inl hZ
  · by_cases hZ : ZeroSect Y c
    · exact Or.inl hZ
    · refine Or.inr ⟨q, ?_, a, hA⟩
      have hmem : ((2 : ℝ) ^ (q : ℝ)) ∈ ClusterSet Y := ⟨c, hpair c q a hA hZ⟩
      have hmem' : ((2 : ℝ) ^ (q : ℝ)) ∈ hfin.toFinset := by
        rwa [Set.Finite.mem_toFinset]
      have himg : expPreimage ((2 : ℝ) ^ (q : ℝ)) ∈ hfin.toFinset.image expPreimage :=
        Finset.mem_image_of_mem expPreimage hmem'
      rwa [expPreimage_exp q] at himg

end Work.WilC4aU
