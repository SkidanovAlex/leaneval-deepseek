/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The polar ("multi-radial") Seeley extension for a polydisc pair

This file sets up the construction of the polar Seeley extension operator for the pair
`pd n ρ 1 ⊂ pd n ρ 2`, together with the two elementary properties (agreement on `pd n ρ 1` and
dependence only on the restriction to `pd n ρ 1`).  The `C^{k,α}` estimate is in
`Submission.Work.NN.Final.exists_extension_polar`.

In the log-radius variables `u_j = log (ρ_j / ‖z_j‖)` (positive inside `pd1`), the reflection in the
`j`-th coordinate sends `u_j` to `-b m * u_j` when `u_j < 0` and keeps `z_j` when `u_j ≥ 0`, i.e.
`z_j ↦ z_j * (ρ_j / ‖z_j‖) ^ (b m)` (a dilation fixing the argument).  The cutoff factor is `1`
when `u_j ≥ 0` and `χ (b m * u_j)` when `u_j < 0`, with `χ` the standard bump (`seeleyCut`),
which is `1` near `0` and flat at `0`.

The evaluation of `v` at a point of the *closed* polydisc uses an abstract linear functional
(`polarEval`) which agrees with the evaluation at that point on functions continuous up to
`pd n ρ 3`, and depends only on the restriction to `pd n ρ 1`; this is what makes the construction
interior-determined and is essential for the second conjunct of the statement.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.exists_moment_data
import Submission.Work.NN.Final.SeeleyDefs

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter
open Classical

namespace Work.NN.Final

variable {n : ℕ} {ρ : Fin n → ℝ}

/-! ## The closure of the polydisc and evaluation at the boundary -/

/-- The closure of the open polydisc `pd n ρ 1` is the closed polydisc. -/
theorem closure_pd (n : ℕ) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    closure (pd n ρ 1) = {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ ρ j} := by
  apply Subset.antisymm
  · intro z hz j
    have hclosed : IsClosed {w : Fin n → ℂ | ‖w j‖ ≤ ρ j} :=
      isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
    exact closure_minimal (fun w hw => le_of_lt (by rw [mem_pd] at hw; simpa using hw j))
      hclosed hz
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hzn : (0:ℝ) ≤ ‖z‖ := norm_nonneg _
    obtain ⟨t, htpos, ht1, htε⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * ‖z‖ < ε := by
      refine ⟨min (ε / (‖z‖ + 1)) (1/2), lt_min (div_pos hε (by linarith)) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
      calc min (ε / (‖z‖ + 1)) (1/2) * ‖z‖ ≤ (ε / (‖z‖ + 1)) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hzn
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < ‖z‖ + 1)]
            nlinarith
    refine ⟨(1 - t) • z, ?_, ?_⟩
    · rw [mem_pd]
      intro j
      have h1 : ‖((1 - t : ℝ) : ℂ) * z j‖ = |1 - t| * ‖z j‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2 : |1 - t| = 1 - t := abs_of_pos (by linarith)
      rw [Pi.smul_apply, Complex.real_smul, h1, h2]
      calc (1 - t) * ‖z j‖ ≤ (1 - t) * ρ j :=
            mul_le_mul_of_nonneg_left (by simpa using hz j) (by linarith)
        _ < 1 * ρ j := mul_lt_mul_of_pos_right (by linarith) (hρ j)
    · rw [dist_eq_norm]
      have hsub : z - (1 - t) • z = t • z := by
        ext j; simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]; push_cast; ring
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htε

/-- A function continuous on `pd n ρ 3` that vanishes on `pd n ρ 1` vanishes at every point of
the closed polydisc `pd n ρ 1`. -/
theorem eq_zero_of_continuousOn_of_eq_zero {v : (Fin n → ℂ) → ℂ} (hρ : ∀ j, 0 < ρ j)
    (hv : ContinuousOn v (pd n ρ 3)) (hv0 : ∀ z ∈ pd n ρ 1, v z = 0)
    {ζ : Fin n → ℂ} (hζ : ∀ j, ‖ζ j‖ ≤ ρ j) : v ζ = 0 := by
  have hζ3 : ζ ∈ pd n ρ 3 := by
    rw [mem_pd]; intro j
    nlinarith [hζ j, hρ j]
  have hmem : ζ ∈ closure (pd n ρ 1) := by rw [closure_pd n hρ]; exact hζ
  haveI : (𝓝[pd n ρ 1] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hcont : ContinuousAt v ζ := hv.continuousAt ((isOpen_pd ρ 3).mem_nhds hζ3)
  have h1 : Filter.Tendsto v (𝓝[pd n ρ 1] ζ) (𝓝 (v ζ)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto v (𝓝[pd n ρ 1] ζ) (𝓝 (0:ℂ)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hv0 z hz).symm
  exact tendsto_nhds_unique h1 h2

/-! ## Linear functionals computing the value at a point of the closed polydisc -/

/-- Functions on the open polydisc, as a vector space over `ℝ`. -/
abbrev Pd1Fun (n : ℕ) (ρ : Fin n → ℝ) := ({z : Fin n → ℂ // z ∈ pd n ρ 1} → ℂ)

/-- The restriction of a function on `ℂⁿ` to the open polydisc. -/
def restrLM (n : ℕ) (ρ : Fin n → ℝ) : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] Pd1Fun n ρ where
  toFun v := fun z => v z.1
  map_add' _ _ := by ext z; rfl
  map_smul' _ _ := by ext z; rfl

/-- The subspace of functions continuous on `pd n ρ 3`. -/
def contSub (n : ℕ) (ρ : Fin n → ℝ) : Submodule ℝ ((Fin n → ℂ) → ℂ) where
  carrier := {v | ContinuousOn v (pd n ρ 3)}
  add_mem' := fun {_ _} ha hb => ha.add hb
  zero_mem' := continuousOn_const
  smul_mem' := fun c {_ } hx => ContinuousOn.const_smul hx c

/-- The restriction map on functions continuous up to `pd n ρ 3`. -/
def restrCont (n : ℕ) (ρ : Fin n → ℝ) : (contSub n ρ) →ₗ[ℝ] Pd1Fun n ρ :=
  (restrLM n ρ).comp (contSub n ρ).subtype

/-- Every linear functional on a submodule extends to the whole module. -/
theorem exists_linearMap_extend {M : Type*} [AddCommGroup M] [Module ℝ M] (p : Submodule ℝ M)
    (f : p →ₗ[ℝ] ℂ) : ∃ g : M →ₗ[ℝ] ℂ, ∀ x : p, g x = f x := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let e := p.prodEquivOfIsCompl q hq
  have key : ∀ x : p, e.symm (x : M) = (x, 0) := fun x =>
    Submodule.prodEquivOfIsCompl_symm_apply_left p q hq x
  refine ⟨f.comp ((LinearMap.fst ℝ p q).comp e.symm.toLinearMap), fun x => ?_⟩
  show f ((LinearMap.fst ℝ p q) (e.symm.toLinearMap (x : M))) = f x
  have h2 : (LinearMap.fst ℝ p q) (e.symm.toLinearMap (x : M)) = x := by
    rw [show e.symm.toLinearMap (x : M) = e.symm (x : M) from rfl, key x]
    rfl
  rw [h2]

/-- For `ζ` in the closed polydisc there is a linear functional on functions which agrees with the
evaluation at `ζ` on functions continuous up to `pd n ρ 3`, and depends only on the restriction to
the open polydisc. -/
theorem exists_evalFunctional (hρ : ∀ j, 0 < ρ j) (ζ : Fin n → ℂ)
    (hζ : ∀ j, ‖ζ j‖ ≤ ρ j) :
    ∃ Λ : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ℂ,
      (∀ v, ContinuousOn v (pd n ρ 3) → Λ v = v ζ) ∧
      (∀ v w, (∀ z ∈ pd n ρ 1, v z = w z) → Λ v = Λ w) := by
  let g : (contSub n ρ) →ₗ[ℝ] ℂ :=
    { toFun := fun v => v.1 ζ
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp }
  have hker : (restrCont n ρ).ker ≤ g.ker := by
    intro v hv
    have hv0 : ∀ z ∈ pd n ρ 1, v.1 z = 0 := by
      intro z hz
      have hv' := LinearMap.mem_ker.mp hv
      have h := congrFun hv' ⟨z, hz⟩
      simpa [restrCont, restrLM] using h
    have hz : v.1 ζ = 0 := eq_zero_of_continuousOn_of_eq_zero hρ v.2 hv0 hζ
    simpa [g] using hz
  let hfun : ((contSub n ρ) ⧸ (restrCont n ρ).ker) →ₗ[ℝ] ℂ :=
    Submodule.liftQ _ g hker
  let hWV : (restrCont n ρ).range →ₗ[ℝ] ℂ :=
    hfun.comp (restrCont n ρ).quotKerEquivRange.symm.toLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_linearMap_extend (restrCont n ρ).range hWV
  refine ⟨Φ.comp (restrLM n ρ), ?_, ?_⟩
  · intro v hv
    have hvmem : v ∈ contSub n ρ := hv
    have h1 : Φ (restrLM n ρ v)
        = hWV ⟨restrLM n ρ v, ⟨⟨v, hvmem⟩, rfl⟩⟩ := hΦ ⟨restrLM n ρ v, ⟨⟨v, hvmem⟩, rfl⟩⟩
    have h2 : hWV ⟨restrLM n ρ v, ⟨⟨v, hvmem⟩, rfl⟩⟩ = g ⟨v, hvmem⟩ := by
      show hfun ((restrCont n ρ).quotKerEquivRange.symm ⟨restrLM n ρ v, _⟩) = g ⟨v, hvmem⟩
      have h3 : (restrCont n ρ).quotKerEquivRange (Submodule.Quotient.mk ⟨v, hvmem⟩)
          = ⟨restrLM n ρ v, ⟨⟨v, hvmem⟩, rfl⟩⟩ := by
        apply Subtype.ext
        rw [LinearMap.quotKerEquivRange_apply_mk]
        rfl
      rw [← h3, LinearEquiv.symm_apply_apply]
      rfl
    show Φ (restrLM n ρ v) = v ζ
    rw [h1, h2]
    rfl
  · intro v w hvw
    have h1 : restrLM n ρ v = restrLM n ρ w := by
      funext z; exact hvw z.1 z.2
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1]


/-! ## The construction -/

section Construction

variable {a b : ℕ → ℝ}

/-- A fixed choice of the linear functional computing the value at a point `ζ` of the closed
polydisc. -/
noncomputable def polarEvalChoice (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (ζ : Fin n → ℂ)
    (hζ : ∀ j, ‖ζ j‖ ≤ ρ j) : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ℂ :=
  Classical.choose (exists_evalFunctional hρ ζ hζ)

lemma polarEvalChoice_apply {n : ℕ} {ρ : Fin n → ℝ} {hρ : ∀ j, 0 < ρ j} {ζ : Fin n → ℂ}
    {hζ : ∀ j, ‖ζ j‖ ≤ ρ j} {v : (Fin n → ℂ) → ℂ} (hv : ContinuousOn v (pd n ρ 3)) :
    polarEvalChoice n ρ hρ ζ hζ v = v ζ :=
  (Classical.choose_spec (exists_evalFunctional hρ ζ hζ)).1 v hv

lemma polarEvalChoice_congr {n : ℕ} {ρ : Fin n → ℝ} {hρ : ∀ j, 0 < ρ j} {ζ : Fin n → ℂ}
    {hζ : ∀ j, ‖ζ j‖ ≤ ρ j} {v w : (Fin n → ℂ) → ℂ} (h : ∀ z ∈ pd n ρ 1, v z = w z) :
    polarEvalChoice n ρ hρ ζ hζ v = polarEvalChoice n ρ hρ ζ hζ w :=
  (Classical.choose_spec (exists_evalFunctional hρ ζ hζ)).2 v w h

/-- The linear functional computing the value at a point `ζ` of the closed polydisc: for
`ζ` outside it is `0`. -/
noncomputable def polarEval (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (ζ : Fin n → ℂ) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ℂ :=
  if hζ : ∀ j, ‖ζ j‖ ≤ ρ j then polarEvalChoice n ρ hρ ζ hζ else 0

lemma polarEval_eq (hρ : ∀ j, 0 < ρ j) {ζ : Fin n → ℂ} (hζ : ∀ j, ‖ζ j‖ ≤ ρ j) :
    polarEval n ρ hρ ζ = polarEvalChoice n ρ hρ ζ hζ :=
  dif_pos hζ

/-- On functions continuous up to `pd n ρ 3` the functional is the evaluation. -/
theorem polarEval_apply_of_continuousOn (hρ : ∀ j, 0 < ρ j) {ζ : Fin n → ℂ}
    (hζ : ∀ j, ‖ζ j‖ ≤ ρ j) {v : (Fin n → ℂ) → ℂ} (hv : ContinuousOn v (pd n ρ 3)) :
    polarEval n ρ hρ ζ v = v ζ := by
  rw [polarEval_eq hρ hζ]
  exact polarEvalChoice_apply hv

/-- The functional depends only on the restriction to the open polydisc. -/
theorem polarEval_congr (hρ : ∀ j, 0 < ρ j) {ζ : Fin n → ℂ} (hζ : ∀ j, ‖ζ j‖ ≤ ρ j)
    {v w : (Fin n → ℂ) → ℂ} (h : ∀ z ∈ pd n ρ 1, v z = w z) :
    polarEval n ρ hρ ζ v = polarEval n ρ hρ ζ w := by
  rw [polarEval_eq hρ hζ]
  exact polarEvalChoice_congr h

/-- The cutoff factor in the `j`-th coordinate. -/
noncomputable def polarChi (n : ℕ) (ρ : Fin n → ℝ) (b : ℕ → ℝ) (m : ℕ) (j : Fin n)
    (z : Fin n → ℂ) : ℝ :=
  if ‖z j‖ < ρ j then 1 else seeleyCut (b m * Real.log (ρ j / ‖z j‖))

/-- The reflected `j`-th coordinate. -/
noncomputable def polarRefl (n : ℕ) (ρ : Fin n → ℝ) (b : ℕ → ℝ) (m : ℕ) (j : Fin n)
    (z : Fin n → ℂ) : ℂ :=
  if ‖z j‖ < ρ j then z j else z j * (((ρ j / ‖z j‖) ^ (b m + 1) : ℝ) : ℂ)

/-- The reflected point. -/
noncomputable def polarTau (n : ℕ) (ρ : Fin n → ℝ) (b : ℕ → ℝ) (m : ℕ) (z : Fin n → ℂ) :
    Fin n → ℂ := fun j => polarRefl n ρ b m j z

@[simp] lemma polarChi_of_lt (m : ℕ) (j : Fin n) {z : Fin n → ℂ} (hz : ‖z j‖ < ρ j) :
    polarChi n ρ b m j z = 1 := by
  simp [polarChi, hz]

@[simp] lemma polarChi_of_not_lt (m : ℕ) (j : Fin n) {z : Fin n → ℂ} (hz : ¬ ‖z j‖ < ρ j) :
    polarChi n ρ b m j z = seeleyCut (b m * Real.log (ρ j / ‖z j‖)) := by
  simp [polarChi, hz]

lemma polarChi_nonneg (m : ℕ) (j : Fin n) (z : Fin n → ℂ) : 0 ≤ polarChi n ρ b m j z := by
  rw [polarChi]; split_ifs with h
  · norm_num
  · exact seeleyCut_nonneg _

lemma polarChi_le_one (m : ℕ) (j : Fin n) (z : Fin n → ℂ) : polarChi n ρ b m j z ≤ 1 := by
  rw [polarChi]; split_ifs with h
  · norm_num
  · exact seeleyCut_le_one _

@[simp] lemma polarRefl_of_lt (m : ℕ) (j : Fin n) {z : Fin n → ℂ} (hz : ‖z j‖ < ρ j) :
    polarRefl n ρ b m j z = z j := by
  simp [polarRefl, hz]

@[simp] lemma polarRefl_of_not_lt (m : ℕ) (j : Fin n) {z : Fin n → ℂ} (hz : ¬ ‖z j‖ < ρ j) :
    polarRefl n ρ b m j z = z j * (((ρ j / ‖z j‖) ^ (b m + 1) : ℝ) : ℂ) := by
  simp [polarRefl, hz]

@[simp] lemma polarTau_apply (m : ℕ) (j : Fin n) (z : Fin n → ℂ) :
    polarTau n ρ b m z j = polarRefl n ρ b m j z := rfl

/-- The reflected coordinate lies in the closed disc of radius `ρ j`. -/
lemma norm_polarRefl_le (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m) (m : ℕ) (j : Fin n)
    (z : Fin n → ℂ) : ‖polarRefl n ρ b m j z‖ ≤ ρ j := by
  rw [polarRefl]
  split_ifs with hz
  · exact le_of_lt hz
  · push_neg at hz
    have hzp : 0 < ‖z j‖ := lt_of_lt_of_le (hρ j) hz
    have hnn : (0:ℝ) ≤ ρ j / ‖z j‖ := div_nonneg (le_of_lt (hρ j)) (le_of_lt hzp)
    have hle1 : ρ j / ‖z j‖ ≤ 1 := by rw [div_le_one hzp]; exact hz
    have hb1 : (1:ℝ) ≤ b m + 1 := by linarith [hb m]
    have h := Real.rpow_le_self_of_le_one hnn hle1 hb1
    have hnorm : ‖z j * (((ρ j / ‖z j‖) ^ (b m + 1) : ℝ) : ℂ)‖
        = ‖z j‖ * ((ρ j / ‖z j‖) ^ (b m + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnn _)]
    rw [hnorm]
    calc ‖z j‖ * ((ρ j / ‖z j‖) ^ (b m + 1)) ≤ ‖z j‖ * (ρ j / ‖z j‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = ρ j := by rw [mul_div_cancel₀]; exact ne_of_gt hzp

/-- The reflected point lies in the closed polydisc. -/
lemma polarTau_mem_closed (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m) (m : ℕ)
    (z : Fin n → ℂ) : ∀ j, ‖polarTau n ρ b m z j‖ ≤ ρ j :=
  fun j => norm_polarRefl_le hρ hb m j z

/-- At a point of the boundary faces the reflection is trivial. -/
lemma polarTau_eq_of_boundary (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hzc : ∀ j, ‖z j‖ ≤ ρ j) (hb : ∀ m, (0:ℝ) ≤ b m) (m : ℕ) : polarTau n ρ b m z = z := by
  funext j
  by_cases h : ‖z j‖ < ρ j
  · rw [polarTau_apply, polarRefl_of_lt m j h]
  · push_neg at h
    rw [polarTau_apply, polarRefl_of_not_lt m j (not_lt.mpr h)]
    have hjeq : ‖z j‖ = ρ j := le_antisymm (hzc j) h
    have hρpos : 0 < ρ j := hρ j
    have : (ρ j / ‖z j‖) ^ (b m + 1) = 1 := by
      rw [hjeq, div_self (ne_of_gt hρpos), Real.one_rpow]
    rw [this]; simp

/-- At a point of the boundary faces all cutoffs are one. -/
lemma polarChi_eq_one_of_boundary (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hzc : ∀ j, ‖z j‖ ≤ ρ j) (m : ℕ) (j : Fin n) : polarChi n ρ b m j z = 1 := by
  by_cases h : ‖z j‖ < ρ j
  · rw [polarChi_of_lt m j h]
  · push_neg at h
    have hjeq : ‖z j‖ = ρ j := le_antisymm (hzc j) h
    rw [polarChi_of_not_lt m j (not_lt.mpr h), hjeq, div_self (ne_of_gt (hρ j)),
      Real.log_one, mul_zero]
    exact seeleyCut_eq_one (by norm_num)

/-- The `m`-th term of the polar Seeley sum. -/
noncomputable def polarTerm (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : ℕ → ℝ) (m : ℕ)
    (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (a m : ℂ) * ((∏ j, (polarChi n ρ b m j z : ℂ)) * polarEval n ρ hρ (polarTau n ρ b m z) v)

lemma polarTerm_add (hρ : ∀ j, 0 < ρ j) (m : ℕ) (v w : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    polarTerm n ρ hρ a b m (v + w) z = polarTerm n ρ hρ a b m v z
      + polarTerm n ρ hρ a b m w z := by
  simp only [polarTerm, Pi.add_apply, map_add, mul_add]

lemma polarTerm_smul (hρ : ∀ j, 0 < ρ j) (m : ℕ) (c : ℝ) (v : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    polarTerm n ρ hρ a b m (c • v) z = c • polarTerm n ρ hρ a b m v z := by
  simp only [polarTerm, Pi.smul_apply, map_smul]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- The `j`-th cutoff vanishes when `‖z j‖ ≥ ρ j` and `b m * log (ρ j / ‖z j‖) ≤ -2`. -/
lemma polarChi_eq_zero (m : ℕ) (j : Fin n) {z : Fin n → ℂ} (hz : ¬ ‖z j‖ < ρ j)
    (h : b m * Real.log (ρ j / ‖z j‖) ≤ -2) : polarChi n ρ b m j z = 0 := by
  rw [polarChi_of_not_lt m j hz, seeleyCut_eq_zero (by rw [abs_of_nonpos (le_trans h (by norm_num))]; linarith)]

/-- The polar Seeley extension as a function. -/
noncomputable def polarExtFun (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : ℕ → ℝ)
    (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  if z ∈ pd n ρ 1 then v z else ∑' m, polarTerm n ρ hρ a b m v z

@[simp] lemma polarExtFun_of_mem (hρ : ∀ j, 0 < ρ j) (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hz : z ∈ pd n ρ 1) : polarExtFun n ρ hρ a b v z = v z := ite_eq_left hz

@[simp] lemma polarExtFun_of_not_mem (hρ : ∀ j, 0 < ρ j) (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hz : z ∉ pd n ρ 1) : polarExtFun n ρ hρ a b v z = ∑' m, polarTerm n ρ hρ a b m v z :=
  ite_eq_right hz

/-- Outside the polydisc with all coordinates in the closed polydisc, all reflection is trivial. -/
lemma polarTau_eq_of_not_mem (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : z ∉ pd n ρ 1)
    (hzc : ∀ j, ‖z j‖ ≤ ρ j) (hb : ∀ m, (0:ℝ) ≤ b m) (m : ℕ) : polarTau n ρ b m z = z :=
  polarTau_eq_of_boundary hρ hzc hb m

/-- In that case all cutoffs are one. -/
lemma polarChi_eq_one_of_not_mem (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hzc : ∀ j, ‖z j‖ ≤ ρ j) (m : ℕ) (j : Fin n) : polarChi n ρ b m j z = 1 :=
  polarChi_eq_one_of_boundary hρ hzc m j

lemma polarTerm_of_not_mem (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hz : z ∉ pd n ρ 1)
    (hzc : ∀ j, ‖z j‖ ≤ ρ j) (hb : ∀ m, (0:ℝ) ≤ b m) (m : ℕ) (v : (Fin n → ℂ) → ℂ) :
    polarTerm n ρ hρ a b m v z = (a m : ℂ) * polarEval n ρ hρ z v := by
  have hprod : (∏ j, (polarChi n ρ b m j z : ℂ)) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [polarChi_eq_one_of_not_mem hρ hzc m j]
    norm_num
  simp only [polarTerm, polarTau_eq_of_not_mem hρ hz hzc hb m, hprod, one_mul]

/-- For a point outside the polydisc with a strictly exterior coordinate all but finitely many
terms vanish. -/
lemma exists_finset_polarTerm_eq_zero {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hb : ∀ m, (1:ℝ) ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (v : (Fin n → ℂ) → ℂ) {z : Fin n → ℂ} (hz : ∃ j, ρ j < ‖z j‖) :
    ∃ s : Finset ℕ, ∀ m ∉ s, polarTerm n ρ hρ a b m v z = 0 := by
  obtain ⟨j, hj⟩ := hz
  have hL : Real.log (ρ j / ‖z j‖) < 0 := by
    apply Real.log_neg
    · exact div_pos (hρ j) (lt_of_lt_of_le (hρ j) hj.le)
    · rw [div_lt_one (lt_of_lt_of_le (hρ j) hj.le)]; exact hj
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hbT.eventually (Filter.eventually_ge_atTop (-2 / Real.log (ρ j / ‖z j‖))))
  refine ⟨Finset.range M, fun m hm => ?_⟩
  simp only [Finset.mem_range, not_lt] at hm
  have h1 : -2 / Real.log (ρ j / ‖z j‖) ≤ b m := hM m hm
  have h2 : b m * Real.log (ρ j / ‖z j‖) ≤ -2 := by
    have h3 := mul_le_mul_of_nonpos_right h1 hL.le
    rwa [div_mul_cancel₀ (-2) (ne_of_lt hL)] at h3
  have h3 : polarChi n ρ b m j z = 0 := polarChi_eq_zero m j (not_lt.mpr hj.le) h2
  have h4 : (∏ j, (polarChi n ρ b m j z : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [h3]; norm_num
  simp only [polarTerm, h4, zero_mul, mul_zero]


/-- The reflection is trivial on the closed polydisc. -/
lemma polarTau_eq_of_closed (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hzc : ∀ j, ‖z j‖ ≤ ρ j)
    (hb : ∀ m, (0:ℝ) ≤ b m) (m : ℕ) : polarTau n ρ b m z = z :=
  polarTau_eq_of_boundary hρ hzc hb m

/-- On the closed polydisc the term is a constant multiple of the evaluation functional. -/
lemma polarTerm_of_closed (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} (hzc : ∀ j, ‖z j‖ ≤ ρ j)
    (hb : ∀ m, (0:ℝ) ≤ b m) (m : ℕ) (v : (Fin n → ℂ) → ℂ) :
    polarTerm n ρ hρ a b m v z = (a m : ℂ) * polarEval n ρ hρ z v := by
  have hprod : (∏ j, (polarChi n ρ b m j z : ℂ)) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [polarChi_eq_one_of_boundary hρ hzc m j]
    norm_num
  simp only [polarTerm, polarTau_eq_of_closed hρ hzc hb m, hprod, one_mul]

/-- Each term of the polar Seeley sum is summable, when `∑ |a m|` converges. -/
lemma summable_polarTerm (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {a : ℕ → ℝ}
    (hsum : Summable fun m => |a m|) (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Summable fun m => polarTerm n ρ hρ a b m v z := by
  by_cases hz : ∃ j, ρ j < ‖z j‖
  · obtain ⟨s, hs⟩ := exists_finset_polarTerm_eq_zero hρ hb hbT v hz
    exact summable_of_ne_finset_zero hs
  · push_neg at hz
    have hterm : ∀ m, polarTerm n ρ hρ a b m v z = (a m : ℂ) * polarEval n ρ hρ z v :=
      fun m => polarTerm_of_closed hρ hz (fun m => le_trans zero_le_one (hb m)) m v
    rw [show (fun m => polarTerm n ρ hρ a b m v z)
        = (fun m => (a m : ℂ) * polarEval n ρ hρ z v) from funext hterm]
    have hsumC : Summable fun m => ((a m : ℝ) : ℂ) := by
      apply Summable.of_norm
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hsum
    exact Summable.mul_right (polarEval n ρ hρ z v) hsumC


/-- The polar Seeley extension is additive in the function, pointwise. -/
lemma polarExtFun_add (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (hsum : Summable fun m => |a m|)
    (v w : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    polarExtFun n ρ hρ a b (v + w) z = polarExtFun n ρ hρ a b v z + polarExtFun n ρ hρ a b w z := by
  by_cases hz : z ∈ pd n ρ 1
  · rw [polarExtFun_of_mem hρ (v+w) z hz, polarExtFun_of_mem hρ v z hz,
      polarExtFun_of_mem hρ w z hz, Pi.add_apply]
  · rw [polarExtFun_of_not_mem hρ (v+w) z hz, polarExtFun_of_not_mem hρ v z hz,
      polarExtFun_of_not_mem hρ w z hz]
    have hsv : Summable fun m => polarTerm n ρ hρ a b m v z :=
      summable_polarTerm hρ hb hbT hsum v z
    have hsw : Summable fun m => polarTerm n ρ hρ a b m w z :=
      summable_polarTerm hρ hb hbT hsum w z
    rw [← Summable.tsum_add hsv hsw]
    exact tsum_congr fun m => polarTerm_add hρ m v w z

/-- The polar Seeley extension is homogeneous in the function, pointwise. -/
lemma polarExtFun_smul (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (hsum : Summable fun m => |a m|)
    (c : ℝ) (v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    polarExtFun n ρ hρ a b (c • v) z = c • polarExtFun n ρ hρ a b v z := by
  by_cases hz : z ∈ pd n ρ 1
  · rw [polarExtFun_of_mem hρ (c • v) z hz, polarExtFun_of_mem hρ v z hz, Pi.smul_apply]
  · rw [polarExtFun_of_not_mem hρ (c • v) z hz, polarExtFun_of_not_mem hρ v z hz]
    have hsv : Summable fun m => polarTerm n ρ hρ a b m v z :=
      summable_polarTerm hρ hb hbT hsum v z
    rw [show (fun m => polarTerm n ρ hρ a b m (c • v) z)
        = (fun m => c • polarTerm n ρ hρ a b m v z) from
      funext fun m => polarTerm_smul hρ m c v z]
    exact Summable.tsum_const_smul c hsv

/-- The polar Seeley extension, as a linear map. -/
noncomputable def polarExtLin (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : ℕ → ℝ)
    (hb : ∀ m, (1:ℝ) ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hsum : Summable fun m => |a m|) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := polarExtFun n ρ hρ a b
  map_add' v w := funext fun z => polarExtFun_add hρ hb hbT hsum v w z
  map_smul' c v := funext fun z => polarExtFun_smul hρ hb hbT hsum c v z

lemma polarExtLin_apply (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (hsum : Summable fun m => |a m|)
    (v : (Fin n → ℂ) → ℂ) :
    polarExtLin n ρ hρ a b hb hbT hsum v = polarExtFun n ρ hρ a b v := rfl

/-- On the open polydisc the extension reproduces the input. -/
theorem polarExtLin_of_mem (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (hsum : Summable fun m => |a m|)
    (v : (Fin n → ℂ) → ℂ) {z : Fin n → ℂ} (hz : z ∈ pd n ρ 1) :
    polarExtLin n ρ hρ a b hb hbT hsum v z = v z :=
  polarExtFun_of_mem hρ v z hz

/-- The extension depends only on the restriction to the open polydisc. -/
theorem polarExtLin_congr (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (hsum : Summable fun m => |a m|)
    {v w : (Fin n → ℂ) → ℂ} (h : ∀ z ∈ pd n ρ 1, v z = w z) :
    polarExtLin n ρ hρ a b hb hbT hsum v = polarExtLin n ρ hρ a b hb hbT hsum w := by
  funext z
  by_cases hz : z ∈ pd n ρ 1
  · rw [polarExtLin_of_mem hρ hb hbT hsum v hz, polarExtLin_of_mem hρ hb hbT hsum w hz,
      h z hz]
  · show polarExtFun n ρ hρ a b v z = polarExtFun n ρ hρ a b w z
    rw [polarExtFun_of_not_mem hρ v z hz, polarExtFun_of_not_mem hρ w z hz]
    refine tsum_congr fun m => ?_
    simp only [polarTerm]
    rw [polarEval_congr hρ (polarTau_mem_closed hρ hb m z) h]


/-! ## The iterated (product) construction

The correct multi-coordinate construction is the *iteration* of the one-dimensional radial
extension, one coordinate at a time.  This is what makes the jets match across the faces: at a
face of one coordinate, the inner extension is applied uniformly on both sides, so the moment
identity `∑ a m (-(b m)) = 1` suffices. -/

/-- The regularised input: the honest evaluation on the open polydisc and the chosen functional on
the boundary faces. -/
noncomputable def polarReg (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (v : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun ζ => if ζ ∈ pd n ρ 1 then v ζ else polarEval n ρ hρ ζ v

@[simp] lemma polarReg_of_mem (hρ : ∀ j, 0 < ρ j) (v : (Fin n → ℂ) → ℂ) {ζ : Fin n → ℂ}
    (hζ : ζ ∈ pd n ρ 1) : polarReg n ρ hρ v ζ = v ζ := ite_eq_left hζ

@[simp] lemma polarReg_of_not_mem (hρ : ∀ j, 0 < ρ j) (v : (Fin n → ℂ) → ℂ) {ζ : Fin n → ℂ}
    (hζ : ζ ∉ pd n ρ 1) : polarReg n ρ hρ v ζ = polarEval n ρ hρ ζ v := ite_eq_right hζ

lemma polarReg_add (hρ : ∀ j, 0 < ρ j) (v w : (Fin n → ℂ) → ℂ) :
    polarReg n ρ hρ (v + w) = polarReg n ρ hρ v + polarReg n ρ hρ w := by
  funext ζ
  by_cases hz : ζ ∈ pd n ρ 1
  · simp only [polarReg_of_mem hρ (v+w) hz, Pi.add_apply, polarReg_of_mem hρ v hz,
      polarReg_of_mem hρ w hz]
  · simp only [polarReg_of_not_mem hρ (v+w) hz, Pi.add_apply, polarReg_of_not_mem hρ v hz,
      polarReg_of_not_mem hρ w hz, map_add]

lemma polarReg_smul (hρ : ∀ j, 0 < ρ j) (c : ℝ) (v : (Fin n → ℂ) → ℂ) :
    polarReg n ρ hρ (c • v) = c • polarReg n ρ hρ v := by
  funext ζ
  by_cases hz : ζ ∈ pd n ρ 1
  · simp only [polarReg_of_mem hρ (c • v) hz, Pi.smul_apply, polarReg_of_mem hρ v hz]
  · simp only [polarReg_of_not_mem hρ (c • v) hz, Pi.smul_apply, polarReg_of_not_mem hρ v hz,
      map_smul]

/-- The regularised input, as a linear map. -/
noncomputable def polarRegLin (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := polarReg n ρ hρ
  map_add' := polarReg_add hρ
  map_smul' := polarReg_smul hρ

lemma polarReg_congr (hρ : ∀ j, 0 < ρ j) {v w : (Fin n → ℂ) → ℂ}
    (h : ∀ z ∈ pd n ρ 1, v z = w z) : polarReg n ρ hρ v = polarReg n ρ hρ w := by
  funext ζ
  by_cases hz : ζ ∈ pd n ρ 1
  · rw [polarReg_of_mem hρ v hz, polarReg_of_mem hρ w hz, h ζ hz]
  · rw [polarReg_of_not_mem hρ v hz, polarReg_of_not_mem hρ w hz]
    by_cases hcl : ∀ j, ‖ζ j‖ ≤ ρ j
    · exact polarEval_congr hρ hcl h
    · unfold polarEval
      rw [dif_neg hcl]
      rfl

/-- The one-dimensional (radial) term in the `j`-th coordinate. -/
noncomputable def radialTerm (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (j : Fin n) (m : ℕ)
    (G : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (a m : ℂ) * ((polarChi n ρ b m j z : ℂ) * G (Function.update z j (polarRefl n ρ b m j z)))

/-- The one-dimensional (radial) extension in the `j`-th coordinate. -/
noncomputable def radialExt (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (j : Fin n)
    (G : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z => if ‖z j‖ ≤ ρ j then G z else ∑' m, radialTerm n ρ a b j m G z

@[simp] lemma radialExt_of_le {j : Fin n} {G : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : ‖z j‖ ≤ ρ j) : radialExt n ρ a b j G z = G z := ite_eq_left hz

lemma radialExt_of_gt {j : Fin n} {G : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : ρ j < ‖z j‖) : radialExt n ρ a b j G z = ∑' m, radialTerm n ρ a b j m G z :=
  ite_eq_right (not_le.mpr hz)

lemma radialTerm_add (j : Fin n) (m : ℕ) (G H : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    radialTerm n ρ a b j m (G + H) z
      = radialTerm n ρ a b j m G z + radialTerm n ρ a b j m H z := by
  simp only [radialTerm, Pi.add_apply, mul_add]

lemma radialTerm_smul (j : Fin n) (m : ℕ) (c : ℝ) (G : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    radialTerm n ρ a b j m (c • G) z = c • radialTerm n ρ a b j m G z := by
  simp only [radialTerm, Pi.smul_apply]
  rw [Complex.real_smul, Complex.real_smul]
  ring

lemma exists_finset_radialTerm_eq_zero (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (j : Fin n) (G : (Fin n → ℂ) → ℂ)
    {z : Fin n → ℂ} (hz : ρ j < ‖z j‖) :
    ∃ s : Finset ℕ, ∀ m ∉ s, radialTerm n ρ a b j m G z = 0 := by
  have hL : Real.log (ρ j / ‖z j‖) < 0 := by
    apply Real.log_neg
    · exact div_pos (hρ j) (lt_of_lt_of_le (hρ j) hz.le)
    · rw [div_lt_one (lt_of_lt_of_le (hρ j) hz.le)]; exact hz
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hbT.eventually (Filter.eventually_ge_atTop (-2 / Real.log (ρ j / ‖z j‖))))
  refine ⟨Finset.range M, fun m hm => ?_⟩
  simp only [Finset.mem_range, not_lt] at hm
  have h1 : -2 / Real.log (ρ j / ‖z j‖) ≤ b m := hM m hm
  have h2 : b m * Real.log (ρ j / ‖z j‖) ≤ -2 := by
    have h3 := mul_le_mul_of_nonpos_right h1 hL.le
    rwa [div_mul_cancel₀ (-2) (ne_of_lt hL)] at h3
  have h3 : polarChi n ρ b m j z = 0 := polarChi_eq_zero m j (not_lt.mpr hz.le) h2
  simp only [radialTerm, h3, Complex.ofReal_zero, zero_mul, mul_zero]

lemma summable_radialTerm (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (j : Fin n) (G : (Fin n → ℂ) → ℂ)
    {z : Fin n → ℂ} (hz : ρ j < ‖z j‖) : Summable fun m => radialTerm n ρ a b j m G z := by
  obtain ⟨s, hs⟩ := exists_finset_radialTerm_eq_zero hρ hb hbT j G hz
  exact summable_of_ne_finset_zero hs

lemma radialExt_add (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (j : Fin n)
    (G H : (Fin n → ℂ) → ℂ) :
    radialExt n ρ a b j (G + H) = radialExt n ρ a b j G + radialExt n ρ a b j H := by
  funext z
  rw [Pi.add_apply]
  by_cases hz : ‖z j‖ ≤ ρ j
  · simp only [radialExt_of_le hz, Pi.add_apply]
  · rw [radialExt_of_gt (lt_of_not_ge hz), radialExt_of_gt (lt_of_not_ge hz),
      radialExt_of_gt (lt_of_not_ge hz)]
    rw [← Summable.tsum_add (summable_radialTerm hρ hb hbT j G (lt_of_not_ge hz))
      (summable_radialTerm hρ hb hbT j H (lt_of_not_ge hz))]
    exact tsum_congr fun m => radialTerm_add j m G H z

lemma radialExt_smul (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (j : Fin n) (c : ℝ)
    (G : (Fin n → ℂ) → ℂ) :
    radialExt n ρ a b j (c • G) = c • radialExt n ρ a b j G := by
  funext z
  rw [Pi.smul_apply]
  by_cases hz : ‖z j‖ ≤ ρ j
  · simp only [radialExt_of_le hz, Pi.smul_apply]
  · rw [radialExt_of_gt (lt_of_not_ge hz), radialExt_of_gt (lt_of_not_ge hz)]
    rw [show (fun m => radialTerm n ρ a b j m (c • G) z)
        = (fun m => c • radialTerm n ρ a b j m G z) from
      funext fun m => radialTerm_smul j m c G z]
    exact Summable.tsum_const_smul c (summable_radialTerm hρ hb hbT j G (lt_of_not_ge hz))

/-- The one-dimensional radial extension, as a linear map. -/
noncomputable def radialExtLin (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hb : ∀ m, (1:ℝ) ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (j : Fin n) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := radialExt n ρ a b j
  map_add' := radialExt_add hρ hb hbT j
  map_smul' := radialExt_smul hρ hb hbT j


/-- The iterated polar Seeley extension: the composition of the one-dimensional radial extensions
in every coordinate, the first coordinate outermost. -/
noncomputable def iterExt (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (v : (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun j G => radialExt n ρ a b j G) v

private lemma foldr_radialExt_add (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (l : List (Fin n))
    (v w : (Fin n → ℂ) → ℂ) :
    l.foldr (fun j G => radialExt n ρ a b j G) (v + w)
      = l.foldr (fun j G => radialExt n ρ a b j G) v
        + l.foldr (fun j G => radialExt n ρ a b j G) w := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact radialExt_add hρ hb hbT j _ _

private lemma foldr_radialExt_smul (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (l : List (Fin n)) (c : ℝ)
    (v : (Fin n → ℂ) → ℂ) :
    l.foldr (fun j G => radialExt n ρ a b j G) (c • v)
      = c • l.foldr (fun j G => radialExt n ρ a b j G) v := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact radialExt_smul hρ hb hbT j c _

/-- The iterated extension, as a linear map. -/
noncomputable def iterExtLin (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hb : ∀ m, (1:ℝ) ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := iterExt n ρ a b
  map_add' v w := foldr_radialExt_add hρ hb hbT (List.finRange n) v w
  map_smul' c v := foldr_radialExt_smul hρ hb hbT (List.finRange n) c v

lemma iterExtLin_apply (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (v : (Fin n → ℂ) → ℂ) :
    iterExtLin n ρ a b hρ hb hbT v = iterExt n ρ a b v := rfl

private lemma foldr_radialExt_eval_of_mem {z : Fin n → ℂ} (hz : z ∈ pd n ρ 1)
    (l : List (Fin n)) (G : (Fin n → ℂ) → ℂ) :
    l.foldr (fun j G => radialExt n ρ a b j G) G z = G z := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, radialExt_of_le (le_of_lt (by rw [mem_pd] at hz; simpa using hz j))]
    exact ih

/-- On the open polydisc the iterated extension reproduces the input. -/
theorem iterExt_of_mem (v : (Fin n → ℂ) → ℂ) {z : Fin n → ℂ} (hz : z ∈ pd n ρ 1) :
    iterExt n ρ a b v z = v z :=
  foldr_radialExt_eval_of_mem hz (List.finRange n) v

/-- The iterated extension of equal functions (on the open polydisc) is equal. -/
theorem iterExt_congr (hρ : ∀ j, 0 < ρ j) {v w : (Fin n → ℂ) → ℂ}
    (h : ∀ z ∈ pd n ρ 1, v z = w z) :
    iterExt n ρ a b (polarReg n ρ hρ v) = iterExt n ρ a b (polarReg n ρ hρ w) := by
  rw [polarReg_congr hρ h]

/-- **The polar (iterated) Seeley extension operator.** -/
noncomputable def polarExtension (n : ℕ) (ρ : Fin n → ℝ) (a b : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hb : ∀ m, (1:ℝ) ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  (iterExtLin n ρ a b hρ hb hbT).comp (polarRegLin n ρ hρ)

lemma polarExtension_apply (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (v : (Fin n → ℂ) → ℂ) :
    polarExtension n ρ a b hρ hb hbT v = iterExt n ρ a b (polarReg n ρ hρ v) := rfl

/-- The extension reproduces the input on the open polydisc. -/
theorem polarExtension_of_mem (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (v : (Fin n → ℂ) → ℂ)
    {z : Fin n → ℂ} (hz : z ∈ pd n ρ 1) :
    polarExtension n ρ a b hρ hb hbT v z = v z := by
  rw [polarExtension_apply, iterExt_of_mem _ hz, polarReg_of_mem hρ v hz]

/-- The extension depends only on the restriction of the input to the open polydisc. -/
theorem polarExtension_congr (hρ : ∀ j, 0 < ρ j) (hb : ∀ m, (1:ℝ) ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {v w : (Fin n → ℂ) → ℂ}
    (h : ∀ z ∈ pd n ρ 1, v z = w z) :
    polarExtension n ρ a b hρ hb hbT v = polarExtension n ρ a b hρ hb hbT w := by
  rw [polarExtension_apply, polarExtension_apply, iterExt_congr hρ h]

end Construction

end Work.NN.Final
