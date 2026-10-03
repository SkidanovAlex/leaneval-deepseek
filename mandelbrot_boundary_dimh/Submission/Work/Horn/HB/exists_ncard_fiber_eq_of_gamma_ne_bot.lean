import Mathlib
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Lib.Unif2.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected

/-!
# Fibres of a connected covering of the punctured disc have constant cardinality

Let `q : Z → 𝔻*` be a covering map with `Z` path connected, `z₀ : Z` a point over `u t₀`, and
`Γ = Gamma hcov t₀ z₀ hz ≤ ℤ` the stabiliser of `z₀` under the `ℤ`-action on the fibre of `q` over
`u t₀` induced by the universal covering `u t = exp (-t)`.

The main result of this file is that `Γ ≠ ⊥` forces *every* fibre of `q` to be finite of one and
the same cardinality, i.e. the covering has a well defined positive degree.

The mathematics is the following.  A non-zero element `a` of `Γ` gives a non-zero period `N` of the
action `ℤ → Z`, `j ↦ T j z₀`; since the action is transitive on the fibre over `u t₀`
(`T_base_surjective`), every element of that fibre is of the form `T (j % N) z₀` with
`0 ≤ j % N < N`, so the fibre is finite.  Cardinalities of fibres of a covering map are locally
constant, hence constant on the preconnected base `𝔻*`
(`Commons.Topology.Covering.natCard_fiber_eq_of_preconnected`), which upgrades finiteness of the
fibre over `u t₀` to the constancy of `ncard` over all of `𝔻*`.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology
open Work.BasinSC.CoverDisc

/-- The punctured unit disc is preconnected. -/
theorem isPreconnected_puncturedDisc : IsPreconnected Work.BasinSC.puncturedDisc := by
  have h1 : IsPreconnected (Metric.ball (0 : ℂ) (1 : ℝ) \ {0}) :=
    Work.Modulus.isPreconnected_ball_diff_center (by norm_num : (0 : ℝ) < 1)
  have h2 : Metric.ball (0 : ℂ) (1 : ℝ) \ {0} = Work.BasinSC.puncturedDisc := by
    ext w
    simp only [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff,
      Work.BasinSC.mem_puncturedDisc]
    tauto
  rwa [h2] at h1

/-- **A connected covering of the punctured disc with non-trivial deck stabiliser has a well
defined positive degree.** -/
theorem exists_ncard_fiber_eq_of_gamma_ne_bot {Z : Type*} [TopologicalSpace Z]
    [PathConnectedSpace Z] {q : Z → ↥Work.BasinSC.puncturedDisc} (hcov : IsCoveringMap q)
    {t₀ : ↥Work.BasinSC.CoverDisc.U} {z₀ : Z} (hz : q z₀ = Work.BasinSC.CoverDisc.u t₀)
    (hΓ : Work.BasinSC.CoverDisc.Gamma hcov t₀ z₀ hz ≠ ⊥) :
    ∃ d : ℕ, 0 < d ∧ ∀ w : ↥Work.BasinSC.puncturedDisc, (q ⁻¹' {w}).ncard = d := by
  classical
  haveI hpre : PreconnectedSpace ↥Work.BasinSC.puncturedDisc :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_puncturedDisc
  -- ## 1. A non-zero element of the deck group furnishes a positive period `N` of the action
  obtain ⟨a, ha0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have ha : (a : ℤ) ∈ Gamma hcov t₀ z₀ hz := a.2
  have hane : (a : ℤ) ≠ 0 := fun h => ha0 (Subtype.ext h)
  set N : ℤ := ((((a : ℤ).natAbs : ℕ)) : ℤ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Int.natAbs_pos.mpr hane
  have hNm : N ∈ Gamma hcov t₀ z₀ hz := by
    rw [hN]
    have hle : AddSubgroup.zmultiples (((((a : ℤ).natAbs : ℕ)) : ℤ)) ≤
        Gamma hcov t₀ z₀ hz := by
      rw [Int.zmultiples_natAbs]
      exact AddSubgroup.zmultiples_le.mpr ha
    exact hle (AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_zsmul _⟩)
  -- the element `N` of the deck group is a period of the action on `Z`
  have hperiod : ∀ j : ℤ, T hcov t₀ (N * j) ⟨z₀, hz⟩ = ⟨z₀, hz⟩ := by
    intro j
    have hmem : N * j ∈ Gamma hcov t₀ z₀ hz := by
      have h1 := AddSubgroup.zsmul_mem (Gamma hcov t₀ z₀ hz) hNm j
      rwa [zsmul_eq_mul, mul_comm] at h1
    exact (T_base_stabilizer hcov t₀ z₀ hz (N * j)).mpr hmem
  -- ## 2. The fibre over `u t₀` is finite
  have hfin : (q ⁻¹' {u t₀}).Finite := by
    have hS : ((fun j : ℤ => (T hcov t₀ j ⟨z₀, hz⟩ : Z)) ''
        ((Finset.Ico (0 : ℤ) N : Finset ℤ) : Set ℤ)).Finite :=
      (Finset.finite_toSet _).image _
    have hsub : (q ⁻¹' {u t₀}) ⊆ (fun j : ℤ => (T hcov t₀ j ⟨z₀, hz⟩ : Z)) ''
        ((Finset.Ico (0 : ℤ) N : Finset ℤ) : Set ℤ) := by
      intro v hv
      obtain ⟨j, hj⟩ := T_base_surjective hcov t₀ z₀ hz ⟨v, hv⟩
      refine ⟨j % N, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨Int.emod_nonneg j hNpos.ne', Int.emod_lt_of_pos j hNpos⟩
      · have hkey : T hcov t₀ j ⟨z₀, hz⟩ = T hcov t₀ (j % N) ⟨z₀, hz⟩ := by
          have hdec : j = j % N + N * (j / N) := (Int.emod_add_mul_ediv j N).symm
          calc T hcov t₀ j ⟨z₀, hz⟩
              = T hcov t₀ (j % N + N * (j / N)) ⟨z₀, hz⟩ := by
                conv_lhs => rw [hdec]
            _ = T hcov t₀ (j % N) (T hcov t₀ (N * (j / N)) ⟨z₀, hz⟩) := by rw [T_add]
            _ = T hcov t₀ (j % N) ⟨z₀, hz⟩ := by rw [hperiod (j / N)]
        change (T hcov t₀ (j % N) ⟨z₀, hz⟩ : Z) = v
        rw [← congrArg Subtype.val hkey]
        exact congrArg Subtype.val hj
    exact Set.Finite.subset hS hsub
  -- ## 3. Assembling the degree
  refine ⟨(q ⁻¹' {u t₀}).ncard, (Set.ncard_pos hfin).mpr ⟨z₀, hz⟩, fun w => ?_⟩
  have hcard := Commons.Topology.Covering.natCard_fiber_eq_of_preconnected (f := q)
    hcov.isCoveringMapOn isPreconnected_univ (Set.mem_univ w) (Set.mem_univ (u t₀))
  simpa only [Nat.card_coe_set_eq] using hcard

end Work.Horn.HB
