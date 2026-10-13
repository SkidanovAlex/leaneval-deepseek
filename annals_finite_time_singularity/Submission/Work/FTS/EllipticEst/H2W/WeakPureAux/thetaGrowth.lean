import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-growth vocabulary for slices

To *state* the residual gap of `WeakPureAux/weakPhiPoleBound` (see
`NOTES_weakPhiPoleBound.md` §J) one needs a name for "the slice `f` grows at most like
`(π/2-θ)^{-R}` (resp. `θ^{-R}`) as `θ` approaches an endpoint".  Mathlib has no such notion
(asymptotic expansions of smooth functions at a point are not available), so it is introduced
here, together with the closure properties the index-descent argument uses.

`R` is the *pole order*: `RightGrowth f 1` is exactly "`f` grows no faster than the reciprocal
distance to `π/2`", i.e. the conclusion of the target at the right endpoint.  The predicates are
germ conditions (`∀ᶠ`), which is what makes them usable for a.e.-in-`z` statements.

## Contents

* the two predicates `RightGrowth`, `LeftGrowth` and their unfolding characterisations;
* `rpow_neg_mono` (`t^{-R}` is antitone in `R` on `t ∈ (0,1]`), the two one-sided neighbourhood
  lemmas (`π/2 - θ ≤ 1` near `π/2`, `θ ≤ 1` near `0`), the extraction lemmas
  `exists_pos_of_eventually_nhdsGT` / `exists_pos_of_eventually_nhdsLT_pi_div_two` that turn the
  germ statements into statements on `(0, δ)` / `(π/2-δ, π/2)`;
* the closure properties of the two predicates: `mono` (weakening the exponent), `rpow`,
  `const_mul`, `add`;
* **`poleBound_of_growth`**: `RightGrowth f 1` + `LeftGrowth f 1` + continuity in the middle
  gives the *shape of the target*, `|f θ| ≤ C(1/θ + 1/(π/2-θ))`.  This is what turns a pair of
  growth statements (the output of the index-descent argument) into the conclusion of
  `WeakPureAux.weakPhiPoleBound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-- `RightGrowth f R`: near `θ = π/2` the slice `f` grows at most like `(π/2-θ)^{-R}`. -/
def RightGrowth (f : ℝ → ℝ) (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
    |f θ| ≤ C * (Real.pi / 2 - θ) ^ (-R)

/-- `LeftGrowth f R`: near `θ = 0` the slice `f` grows at most like `θ^{-R}`. -/
def LeftGrowth (f : ℝ → ℝ) (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[>] (0 : ℝ), |f θ| ≤ C * θ ^ (-R)

/-- Unfolding characterisation, right endpoint. -/
theorem RightGrowth_iff {f : ℝ → ℝ} {R : ℝ} :
    RightGrowth f R ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
      |f θ| ≤ C * (Real.pi / 2 - θ) ^ (-R) := Iff.rfl

/-- Unfolding characterisation, left endpoint. -/
theorem LeftGrowth_iff {f : ℝ → ℝ} {R : ℝ} :
    LeftGrowth f R ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      |f θ| ≤ C * θ ^ (-R) := Iff.rfl

/-- `t^{-R}` is antitone in the exponent on `t ∈ (0,1]`. -/
theorem rpow_neg_mono {t R R' : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hRR' : R ≤ R') :
    t ^ (-R) ≤ t ^ (-R') := by
  have h1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht1
  calc t ^ (-R) = (t ^ R)⁻¹ := Real.rpow_neg (le_of_lt ht0) R
    _ = (t⁻¹) ^ R := (Real.inv_rpow (le_of_lt ht0) R).symm
    _ ≤ (t⁻¹) ^ R' := Real.rpow_le_rpow_of_exponent_le h1 hRR'
    _ = (t ^ R')⁻¹ := Real.inv_rpow (le_of_lt ht0) R'
    _ = t ^ (-R') := (Real.rpow_neg (le_of_lt ht0) R').symm

/-- A neighbourhood of `π/2` on which `π/2 - θ ≤ 1` (frequently used below). -/
theorem eventually_pi_div_two_sub_le_one : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), Real.pi / 2 - θ ≤ 1 := by
  have hmem : ∀ᶠ θ in 𝓝 (Real.pi / 2 : ℝ),
      θ ∈ Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2 + 1) :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with θ hθ
  have h1 : Real.pi / 2 - 1 < θ := (Set.mem_Ioo.mp hθ).1
  linarith

/-- A neighbourhood of `0` on which `θ ≤ 1` (frequently used below). -/
theorem eventually_le_one_of_nhdsGT_zero :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ≤ 1 := by
  have hmem : ∀ᶠ θ in 𝓝 (0 : ℝ), θ ∈ Set.Ioo (-1 : ℝ) 1 :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by norm_num, by norm_num⟩
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with θ hθ
  have h2 : θ < 1 := (Set.mem_Ioo.mp hθ).2
  linarith

/-- **Extraction, left endpoint.**  An eventual statement in `𝓝[>] (0:ℝ)` holds on some
interval `(0, δ)` with `δ > 0`. -/
theorem exists_pos_of_eventually_nhdsGT {p : ℝ → Prop}
    (h : ∀ᶠ θ in 𝓝[>] (0 : ℝ), p θ) : ∃ δ : ℝ, 0 < δ ∧ ∀ θ, 0 < θ → θ < δ → p θ := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨u, hu, huu⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε, hε, fun θ hθ0 hθε => huu θ ?_ hθ0⟩
  refine hεu ?_
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ0]
  exact hθε

/-- **Extraction, right endpoint.**  An eventual statement in `𝓝[<] (π/2)` holds on some
interval `(π/2-δ, π/2)` with `δ > 0`. -/
theorem exists_pos_of_eventually_nhdsLT_pi_div_two {p : ℝ → Prop}
    (h : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), p θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ, θ < Real.pi / 2 → Real.pi / 2 - θ < δ → p θ := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨u, hu, huu⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε, hε, fun θ hθ hδ => huu θ ?_ hθ⟩
  refine hεu ?_
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : |θ - Real.pi / 2| = Real.pi / 2 - θ := by
    rw [abs_of_neg (by linarith), neg_sub]
  rw [h1]
  exact hδ

/-- **Monotonicity in the exponent**, right endpoint. -/
theorem RightGrowth.mono {f : ℝ → ℝ} {R R' : ℝ} (h : RightGrowth f R) (hRR' : R ≤ R') :
    RightGrowth f R' := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2)),
    eventually_pi_div_two_sub_le_one] with θ hle ht hlt
  have ht0 : 0 < Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  exact le_trans hle (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt hRR') hC)

/-- **Monotonicity in the exponent**, left endpoint. -/
theorem LeftGrowth.mono {f : ℝ → ℝ} {R R' : ℝ} (h : LeftGrowth f R) (hRR' : R ≤ R') :
    LeftGrowth f R' := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)),
    eventually_le_one_of_nhdsGT_zero] with θ hle ht hlt
  have ht0 : 0 < θ := Set.mem_Ioi.mp ht
  exact le_trans hle (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt hRR') hC)

/-- The pure power `θ ↦ (π/2-θ)^{-R}` has right growth `R`. -/
theorem RightGrowth.rpow {R : ℝ} :
    RightGrowth (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-R)) R := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [(self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2))] with θ ht
  have ht0 : 0 ≤ Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  rw [abs_of_nonneg (Real.rpow_nonneg ht0 _), one_mul]

/-- The pure power `θ ↦ θ^{-R}` has left growth `R`. -/
theorem LeftGrowth.rpow {R : ℝ} :
    LeftGrowth (fun θ : ℝ => θ ^ (-R)) R := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with θ hθ
  rw [abs_of_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp hθ).le _), one_mul]

/-- Multiplication by a scalar (weakening the exponent), right endpoint. -/
theorem RightGrowth.const_mul {f : ℝ → ℝ} {R : ℝ} (c : ℝ) (hf : RightGrowth f R)
    {R' : ℝ} (hRR' : R ≤ R') : RightGrowth (fun θ => c * f θ) R' := by
  obtain ⟨C, hC, hf'⟩ := hf.mono hRR'
  refine ⟨|c| * C, by positivity, ?_⟩
  filter_upwards [hf'] with θ hθ
  calc |c * f θ| = |c| * |f θ| := abs_mul _ _
    _ ≤ |c| * (C * (Real.pi / 2 - θ) ^ (-R')) := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = (|c| * C) * (Real.pi / 2 - θ) ^ (-R') := by ring

/-- Multiplication by a scalar (weakening the exponent), left endpoint. -/
theorem LeftGrowth.const_mul {f : ℝ → ℝ} {R : ℝ} (c : ℝ) (hf : LeftGrowth f R)
    {R' : ℝ} (hRR' : R ≤ R') : LeftGrowth (fun θ => c * f θ) R' := by
  obtain ⟨C, hC, hf'⟩ := hf.mono hRR'
  refine ⟨|c| * C, by positivity, ?_⟩
  filter_upwards [hf'] with θ hθ
  calc |c * f θ| = |c| * |f θ| := abs_mul _ _
    _ ≤ |c| * (C * θ ^ (-R')) := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = (|c| * C) * θ ^ (-R') := by ring

/-- Sums: the pole order of a sum is at most the larger of the two, right endpoint. -/
theorem RightGrowth.add {f g : ℝ → ℝ} {R S : ℝ} (hf : RightGrowth f R) (hg : RightGrowth g S) :
    RightGrowth (fun θ => f θ + g θ) (max R S) := by
  obtain ⟨Cf, hCf, hf'⟩ := hf
  obtain ⟨Cg, hCg, hg'⟩ := hg
  refine ⟨Cf + Cg, by positivity, ?_⟩
  filter_upwards [hf', hg', (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2)),
    eventually_pi_div_two_sub_le_one] with θ hfθ hgθ ht hlt
  have ht0 : 0 < Real.pi / 2 - θ := by
    have := Set.mem_Iio.mp ht
    linarith
  calc |f θ + g θ| ≤ |f θ| + |g θ| := abs_add_le _ _
    _ ≤ Cf * (Real.pi / 2 - θ) ^ (-R) + Cg * (Real.pi / 2 - θ) ^ (-S) := add_le_add hfθ hgθ
    _ ≤ Cf * (Real.pi / 2 - θ) ^ (-max R S) + Cg * (Real.pi / 2 - θ) ^ (-max R S) :=
        add_le_add (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_left R S)) hCf)
          (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_right R S)) hCg)
    _ = (Cf + Cg) * (Real.pi / 2 - θ) ^ (-max R S) := by ring

/-- Sums: the pole order of a sum is at most the larger of the two, left endpoint. -/
theorem LeftGrowth.add {f g : ℝ → ℝ} {R S : ℝ} (hf : LeftGrowth f R) (hg : LeftGrowth g S) :
    LeftGrowth (fun θ => f θ + g θ) (max R S) := by
  obtain ⟨Cf, hCf, hf'⟩ := hf
  obtain ⟨Cg, hCg, hg'⟩ := hg
  refine ⟨Cf + Cg, by positivity, ?_⟩
  filter_upwards [hf', hg', (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)),
    eventually_le_one_of_nhdsGT_zero] with θ hfθ hgθ ht hlt
  have ht0 : 0 < θ := Set.mem_Ioi.mp ht
  calc |f θ + g θ| ≤ |f θ| + |g θ| := abs_add_le _ _
    _ ≤ Cf * θ ^ (-R) + Cg * θ ^ (-S) := add_le_add hfθ hgθ
    _ ≤ Cf * θ ^ (-max R S) + Cg * θ ^ (-max R S) :=
        add_le_add (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_left R S)) hCf)
          (mul_le_mul_of_nonneg_left (rpow_neg_mono ht0 hlt (le_max_right R S)) hCg)
    _ = (Cf + Cg) * θ ^ (-max R S) := by ring

/-- **The bridge from the growth germs to the shape of the target.**

A slice that is `C⁰` on `(0, π/2)` and grows at most like the reciprocal distance at *both*
endpoints satisfies `|f θ| ≤ C(1/θ + 1/(π/2-θ))`; this is the exact shape of the conclusion of
`WeakPureAux.weakPhiPoleBound`.  The two germ hypotheses hold on `(0, δ_L)` and `(π/2-δ_R, π/2)`;
in between the slice is bounded by compactness. -/
theorem poleBound_of_growth {f : ℝ → ℝ} (hR : RightGrowth f 1) (hL : LeftGrowth f 1)
    (hcont : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ C * (1 / θ + 1 / (Real.pi / 2 - θ)) := by
  obtain ⟨CL, hCL, hL'⟩ := hL
  obtain ⟨CR, hCR, hR'⟩ := hR
  obtain ⟨δL, hδL0, hδL⟩ := exists_pos_of_eventually_nhdsGT hL'
  obtain ⟨δR, hδR0, hδR⟩ := exists_pos_of_eventually_nhdsLT_pi_div_two hR'
  set a : ℝ := min δL (Real.pi / 4) with ha
  set b : ℝ := max (Real.pi / 2 - δR) (3 * Real.pi / 8) with hb
  have ha0 : 0 < a := lt_min hδL0 (by linarith [Real.pi_pos])
  have hab : a ≤ b := by
    have h1 : a ≤ Real.pi / 4 := min_le_right _ _
    have h2 : 3 * Real.pi / 8 ≤ b := le_max_right _ _
    linarith [Real.pi_pos]
  have hb1 : b < Real.pi / 2 := max_lt (by linarith) (by linarith [Real.pi_pos])
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Icc a b, |f θ| ≤ M := by
    have h : ContinuousOn f (Set.Icc a b) :=
      hcont.mono (fun θ hθ => ⟨lt_of_lt_of_le ha0 hθ.1, lt_of_le_of_lt hθ.2 hb1⟩)
    obtain ⟨M, hMb⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn h
    refine ⟨M, ?_, fun θ hθ => by simpa [Real.norm_eq_abs] using hMb θ hθ⟩
    have haa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hMa := hMb a haa
    rw [Real.norm_eq_abs] at hMa
    linarith [abs_nonneg (f a)]
  refine ⟨CL + CR + M + 1, by positivity, fun θ hθ => ?_⟩
  have hθ0 : 0 < θ := hθ.1
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hpos : 0 ≤ 1 / θ + 1 / (Real.pi / 2 - θ) := by positivity
  have hC0 : 0 ≤ CL + CR + M + 1 := by positivity
  rcases lt_or_ge θ a with hcase | hcase
  · -- left endpoint region: `θ < a ≤ δL`
    have hle := hδL θ hθ0 (lt_of_lt_of_le hcase (min_le_left δL (Real.pi / 4)))
    rw [Real.rpow_neg_one] at hle
    calc |f θ| ≤ CL * θ⁻¹ := hle
      _ = CL * (1 / θ) := by rw [one_div]
      _ ≤ (CL + CR + M + 1) * (1 / θ + 1 / (Real.pi / 2 - θ)) :=
          mul_le_mul (by linarith) (le_add_of_nonneg_right (by positivity)) (by positivity) hC0
  · rcases lt_or_ge b θ with hcase2 | hcase2
    · -- right endpoint region: `π/2 - θ < δR`
      have hbd : Real.pi / 2 - δR ≤ b := le_max_left _ _
      have hle := hδR θ hθ.2 (by linarith)
      rw [Real.rpow_neg_one] at hle
      calc |f θ| ≤ CR * (Real.pi / 2 - θ)⁻¹ := hle
        _ = CR * (1 / (Real.pi / 2 - θ)) := by rw [one_div]
        _ ≤ (CL + CR + M + 1) * (1 / θ + 1 / (Real.pi / 2 - θ)) :=
            mul_le_mul (by linarith) (le_add_of_nonneg_left (by positivity)) (by positivity) hC0
    · -- the middle: bounded by compactness, and `1/θ + 1/(π/2-θ) ≥ 1` there
      have hm := hM θ ⟨hcase, hcase2⟩
      have hX1 : (1 : ℝ) ≤ 1 / θ + 1 / (Real.pi / 2 - θ) := by
        have hle2 : θ ≤ 2 := by linarith [Real.pi_lt_four, hθ.2]
        have hle2' : Real.pi / 2 - θ ≤ 2 := by linarith [Real.pi_lt_four, ht0]
        have h1a : (1 : ℝ) / 2 ≤ 1 / θ := one_div_le_one_div_of_le hθ0 hle2
        have h1b : (1 : ℝ) / 2 ≤ 1 / (Real.pi / 2 - θ) :=
          one_div_le_one_div_of_le ht0 hle2'
        linarith
      calc |f θ| ≤ M := hm
        _ ≤ M * (1 / θ + 1 / (Real.pi / 2 - θ)) := by
            have h := mul_le_mul_of_nonneg_left hX1 hM0
            simpa using h
        _ ≤ (CL + CR + M + 1) * (1 / θ + 1 / (Real.pi / 2 - θ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos

end Work.FTS.EllipticEst.H2W.WeakPureAux
