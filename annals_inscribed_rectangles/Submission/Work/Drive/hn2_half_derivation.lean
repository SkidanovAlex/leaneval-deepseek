import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideGermLocalconstUnconditional
import Submission.Work.Drive.DirCTools

/-!
# `hn2` at the `2`-torsion angle: the antisymmetry **derives** the inscribed square

`Work.Drive.hn2_sideGerm_reference` asks for

> `e (v - u) + e (u - v) = 1` for `v - u ∈ Zc γ`,  where `e := sideGerm Ξ Q c`.

Since the negation of `UnitAddCircle` has the fixed point `1/2`, the `u = 0`, `v = 1/2` instance of that
statement reads `x + x = 1` in `ZMod 2`, i.e. `0 = 1`: **the statement asserts `1/2 ∉ Zc γ`, hence
`1/2 ∈ GoodC γ`, i.e. the existence of an inscribed square** (`half_mem_GoodC.lean` identifies
`1/2 ∈ GoodC γ` with the inscribed square theorem in collision form).  This is exactly the paper's
Corollary ("Theorem 2 can be used to give proofs of the fact that every smooth Jordan curve has an
inscribed square"): the antisymmetry at the half-turn *is* the square theorem.

This file pins the logical step that makes the two compatible, so that the square theorem needs **no
separate input**: the germ side value is *locally constant* in the angle at every non-collision angle
(`Work.Drive.sideGerm_localconst_of_planeChart_unconditional`, the germ route's `hn4`), so

* if `1/2` were a non-collision angle, the local constancy at `1/2` (and at its negative, which is `1/2`
  itself) would transfer the off-`1/2` antisymmetry to `1/2`, giving `2 x = 1` — a contradiction.

Hence `1/2 ∈ GoodC γ`, and the antisymmetry then holds at **every** `u ∈ Zc γ` as soon as it holds at
every `u ∈ Zc γ` with `u ≠ 1/2` — with `IsOpen (Zc γ)` (the only topological input, supplied by
smoothness of `γ`: `Work.Drive.isOpen_Zc`) as the sole extra hypothesis.

## What this buys for `hn2_sideGerm_reference`

The node reduces to its **off-half** form plus the openness of `Zc γ`:

```
Work.Drive.hn2_off_half          -- ∀ u ∈ Zc γ, u ≠ 1/2 → e u + e (-u) = 1   (the reference-triple machinery)
Work.Drive.isOpen_Zc-of-chart    -- IsOpen (Zc γ)                            (`Work.Drive.isOpen_Zc`)
```

and `Work.Drive.antisym_of_antisym_off_half` below is the passage between them.  In particular **no**
`IsSmoothEmbedding γ` hypothesis has to be added to the statement for the `2`-torsion angle: the square
is *derived*.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

lemma zmod2_add_self'' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- `1/2` is its own negative in `UnitAddCircle`. -/
lemma half_eq_neg_half' :
    (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) = -(((1 : ℝ) / 2 : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_neg]
  have h1 : (((1 : ℝ)) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
  rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, AddCircle.coe_sub, h1, sub_zero]

/-- **A neighbourhood of a point of the circle contains a point different from it.**  (`UnitAddCircle`
has no isolated points: a small translate of the centre lies in any prescribed neighbourhood.) -/
lemma exists_ne_of_mem_nhds' (x : UnitAddCircle) {S : Set UnitAddCircle} (hS : S ∈ 𝓝 x) :
    ∃ w : UnitAddCircle, w ∈ S ∧ w ≠ x := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
  set t : ℝ := min ε 1 / 2 with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htlt : t < ε := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    rw [ht]; linarith
  have htle : t ≤ 1 / 2 := by
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    rw [ht]; linarith
  have hnorm_eq : ‖((t : ℝ) : UnitAddCircle)‖ = |t| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
      (by rw [abs_of_pos htpos, abs_one]; exact htle)
  have hnorm : ‖((t : ℝ) : UnitAddCircle)‖ = t := by
    rw [hnorm_eq, abs_of_pos htpos]
  have hne : ((t : ℝ) : UnitAddCircle) ≠ 0 := by
    intro h0
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨n, hn⟩ := h0
    have hn' : ((n : ℤ) : ℝ) = t := by simpa using hn
    have h0' : (0 : ℤ) < n := by
      have : (0 : ℝ) < (n : ℝ) := by rw [hn']; exact htpos
      exact_mod_cast this
    have h1' : (n : ℤ) < 1 := by
      have : (n : ℝ) < 1 := by rw [hn']; linarith
      exact_mod_cast this
    omega
  refine ⟨x + ((t : ℝ) : UnitAddCircle), hεS ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + ((t : ℝ) : UnitAddCircle) - x = ((t : ℝ) : UnitAddCircle) := by abel
    rw [hsub, hnorm]
    exact htlt
  · intro h
    have h1 : x + ((t : ℝ) : UnitAddCircle) - x = 0 := sub_eq_zero.mpr h
    have h2 : x + ((t : ℝ) : UnitAddCircle) - x = ((t : ℝ) : UnitAddCircle) := by abel
    exact hne (by rw [h2] at h1; exact h1)

/-- **The half-turn angle is a collision angle, *derived* from the off-half antisymmetry.**

Assume the germ side value `e := sideGerm Ξ Q c` is antisymmetric at every non-collision angle
different from `1/2`, and that the non-collision set `Zc γ` is open.  Then `1/2 ∈ GoodC γ`: otherwise
the local constancy of `e` at `1/2` (and at `-1/2 = 1/2`) would give a non-collision angle `w'` with
`e w' = e (1/2)` and `e (-w') = e (1/2)`, and the off-half antisymmetry at `w'` would read
`e (1/2) + e (1/2) = 1`, i.e. `0 = 1`. -/
theorem one_half_mem_GoodC_of_antisym_off_half {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hopen : IsOpen (Zc γ))
    (hloop : ∀ u : UnitAddCircle, u ∈ Zc γ → u ≠ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) →
      sideGerm Ξ Q c u + sideGerm Ξ Q c (-u) = 1) :
    (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) ∈ Submission.Configuration.GoodC γ := by
  by_contra hnotmem
  have hmem : (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) ∈ Zc γ := by
    simpa [Zc] using hnotmem
  -- the local constancy of `e` at the half-turn angle, and at its negative (the same angle)
  have hoc : ∀ᶠ w' in 𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle),
      sideGerm Ξ Q c w' = sideGerm Ξ Q c (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) :=
    sideGerm_localconst_of_planeChart_unconditional Ξ Q c hγne hγinj hQ hΞ hc hcbot hmem
  have hcontH : Filter.Tendsto (fun w : UnitAddCircle => -w)
      (𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle)) (𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle)) := by
    have h := continuous_neg.tendsto (((1 : ℝ) / 2 : ℝ) : UnitAddCircle)
    simpa only [← half_eq_neg_half'] using h
  have hocneg : ∀ᶠ w' in 𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle),
      sideGerm Ξ Q c (-w') = sideGerm Ξ Q c (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) :=
    hcontH.eventually hoc
  have hZc : ∀ᶠ w' in 𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle), w' ∈ Zc γ :=
    hopen.mem_nhds hmem
  have hZcneg : ∀ᶠ w' in 𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle), -w' ∈ Zc γ := by
    have hcont : Filter.Tendsto (fun w : UnitAddCircle => -w)
        (𝓝 (((1 : ℝ) / 2 : ℝ) : UnitAddCircle))
        (𝓝 (-(((1 : ℝ) / 2 : ℝ) : UnitAddCircle))) :=
      continuous_neg.continuousAt
    have hZc' : ∀ᶠ w'' in 𝓝 (-(((1 : ℝ) / 2 : ℝ) : UnitAddCircle)), w'' ∈ Zc γ :=
      hopen.mem_nhds (by rw [← half_eq_neg_half']; exact hmem)
    exact hcont.eventually hZc'
  obtain ⟨w', ⟨hw1, hw2, hw3, hw4⟩, hwne⟩ :=
    exists_ne_of_mem_nhds' _ (hoc.and (hocneg.and (hZc.and hZcneg)))
  have hanti := hloop w' hw3 hwne
  rw [hw1, hw2] at hanti
  have hzero : sideGerm Ξ Q c (((1 : ℝ) / 2 : ℝ) : UnitAddCircle)
      + sideGerm Ξ Q c (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) = 0 := zmod2_add_self'' _
  rw [hzero] at hanti
  exact absurd hanti (by decide)

/-- **The `hn2` antisymmetry at every non-collision angle, from its off-half form.**

The germ route's local constancy at `1/2` turns the off-half antisymmetry into the full one; the
`1/2`-instance of the latter is exactly the inscribed square theorem, which is *derived* here
(`Work.Drive.one_half_mem_GoodC_of_antisym_off_half`). -/
theorem antisym_of_antisym_off_half {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hopen : IsOpen (Zc γ))
    (hloop : ∀ u : UnitAddCircle, u ∈ Zc γ → u ≠ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) →
      sideGerm Ξ Q c u + sideGerm Ξ Q c (-u) = 1) :
    ∀ (u v : UnitAddCircle), v - u ∈ Zc γ →
      sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1 := by
  have hhalf := one_half_mem_GoodC_of_antisym_off_half Ξ Q c hγne hγinj hQ hΞ hc hcbot hopen hloop
  intro u v hv
  rcases eq_or_ne (v - u) (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) with h | h
  · exfalso
    have hmem : v - u ∈ Submission.Configuration.GoodC γ := h ▸ hhalf
    exact hv hmem
  · have h1 := hloop (v - u) hv h
    have h2 : u - v = -(v - u) := by rw [neg_sub]
    rw [h2]
    exact h1

end

end Work.Drive
