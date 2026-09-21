import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.E1_E2_contDiff
import Submission.Work.OddVolterra.Smooth.E1_E2_regularity

/-!
# Continuity of the odd-case inhomogeneities `E₁`, `E₂` on `[a,1]`

`E₁ n h s = ∫_t ∂_u^{n+1} (ψ(u,t)^n √(ψ(u,t)))|_{u=s}` and
`E₂ n h s = ∫_t ∂_u^n (ψ(u,t)^{n-1} √(ψ(u,t)) ∂_u L(u,t))|_{u=s}` are integrals over the
fixed interval `[-profileX 1, profileX 1]`, where `ψ(u,t) = semicircle t ^ 2 - (u t + h u) ^ 2`.

The integrands are smooth on the open set `{ψ > 0}`, where they agree with the derivatives
`G₁`, `G₂` of the parametric iterates; hence both functions are smooth on `(0,1)`.  At `s = 1`
the radicand `ψ(1,t) = 1 - 2t²` vanishes at the two endpoints `t = ±profileX 1`, so the
integrand has an integrable singularity which is *not* uniform in `s`; continuity there is a
genuine dominated-convergence statement after the substitution `t = profileX 1 sin θ`.

The only hypothesis on `h` is *smoothness* (`ContDiff ℝ ∞`), not analyticity, so the slice
bounds of `E1_E2_regularity` (which are stated for the analytic order `ω`) are redone below at
the smooth order.
-/

namespace Work.OddVolterra.Smooth

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section

open Commons.Geometry.Ulam

/-! ## The iterated derivatives of a section, at the smooth order

These two lemmas are the smooth-order (`C^∞`, as opposed to analytic `C^ω`) forms of
`Work.Analysis.Calculus.iteratedDeriv_section_eq_iteratedFDeriv` and
`Work.Analysis.Calculus.parametric_iteratedDeriv_bound`; the proofs are those of the
originals, with the analyticity hypothesis replaced by smoothness. -/

/-- A natural number is below the smooth order `∞` (as opposed to the analytic order `ω`). -/
lemma natCast_le_smooth (k : ℕ) : ((k : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤)

/-- `↑n + 1 ≤ ∞` in the smooth order. -/
lemma natCast_add_one_le_smooth (n : ℕ) : ((n : ℕ∞ω) + 1) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  have h : ((n : ℕ∞ω) + 1) = ((n + 1 : ℕ) : ℕ∞ω) := by push_cast; ring
  rw [h]; exact natCast_le_smooth (n + 1)

/-- The `k`-th derivative of the section `v ↦ φ (q.1, v)` is the `k`-th iterated Fréchet
derivative of `φ` at `q` evaluated on `(0,1)`. -/
lemma section_iteratedDeriv_eq_iteratedFDeriv_smooth {φ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) (k : ℕ) {q : ℝ × ℝ} (hq : q ∈ U) :
    iteratedDeriv k (fun v : ℝ => φ (q.1, v)) q.2 =
      (iteratedFDeriv ℝ k φ q) (fun _ => (0, 1)) := by
  set s : Set (ℝ × ℝ) := (fun z : ℝ × ℝ => z + (q.1, 0)) ⁻¹' U with hs_def
  have hs_open : IsOpen s := hU.preimage (by continuity)
  have hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => φ (z + (q.1, 0))) s :=
    hφ.comp ((contDiff_id.add contDiff_const).contDiffOn.mono (Set.subset_univ s))
      (fun z hz => hz)
  have hq_in : (ContinuousLinearMap.inr ℝ ℝ ℝ q.2) ∈ s := by
    rw [hs_def, Set.mem_preimage]
    have : (ContinuousLinearMap.inr ℝ ℝ ℝ q.2) + (q.1, 0) = q := by
      ext <;> simp [ContinuousLinearMap.inr]
    rw [this]; exact hq
  have hσ : (fun v : ℝ => φ (q.1, v)) =
      (fun z : ℝ × ℝ => φ (z + (q.1, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    funext v
    simp [ContinuousLinearMap.inr]
  have hinr_open : IsOpen ((ContinuousLinearMap.inr ℝ ℝ ℝ) ⁻¹' s) :=
    hs_open.preimage (by continuity)
  have hq2_in : q.2 ∈ (ContinuousLinearMap.inr ℝ ℝ ℝ) ⁻¹' s := hq_in
  have hk : ((k : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := natCast_le_smooth k
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hσ]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := (fun z : ℝ × ℝ => φ (z + (q.1, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ))
        k hinr_open hq2_in]
  rw [ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
        (g := ContinuousLinearMap.inr ℝ ℝ ℝ) (f := fun z : ℝ × ℝ => φ (z + (q.1, 0)))
        (s := s) hψ hs_open.uniqueDiffOn hinr_open.uniqueDiffOn hq_in (i := k) hk]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := fun z : ℝ × ℝ => φ (z + (q.1, 0))) k hs_open hq_in]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := φ) k (q.1, 0)
        (ContinuousLinearMap.inr ℝ ℝ ℝ q.2)]
  simp [ContinuousLinearMap.inr]

/-- Uniform bound for the iterated derivatives of the sections of a jointly smooth function
on a compact subset of its domain. -/
theorem parametric_iteratedDeriv_bound_smooth {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) U)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) :
    ∃ C : ℝ, ∀ q ∈ K, |iteratedDeriv k (fun u : ℝ => F q.1 u) q.2| ≤ C := by
  have hk : ((k : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := natCast_le_smooth k
  have hcont : ContinuousOn (iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2)) U :=
    ContinuousOn.continuousOn_iteratedFDeriv (f := fun q : ℝ × ℝ => F q.1 q.2) hF hU hk
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨C, fun q hq => ?_⟩
  have hqU : q ∈ U := hKU hq
  have hid := section_iteratedDeriv_eq_iteratedFDeriv_smooth hU hF k hqU
  rw [hid, ← Real.norm_eq_abs]
  calc ‖(iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q) (fun _ => (0, 1))‖
      ≤ ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q‖ *
          ∏ _i : Fin k, ‖((0:ℝ), 1)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q‖ := by simp
    _ ≤ C := hC q hq

/-! ## Positivity of the radicand -/

lemma psi_pos_of_hmid {h : ℝ → ℝ}
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t)
    {s t : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : |t| ≤ profileX 1) :
    0 < psi h semicircle s t :=
  hmid s hs t (abs_le.mp ht)

lemma abs_sin_lt_one_of_abs_lt_pi_div_two {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    |Real.sin θ| < 1 := by
  have hθ' : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Ioo, ← abs_lt]; exact hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ'
  have hsc := Real.sin_sq_add_cos_sq θ
  have hcos2 : 0 < Real.cos θ ^ 2 := pow_pos hcos 2
  have hsq : Real.sin θ ^ 2 < 1 := by linarith
  have habs : |Real.sin θ| ^ 2 = Real.sin θ ^ 2 := sq_abs _
  nlinarith [abs_nonneg (Real.sin θ), hsq, habs]

lemma cos_pos_of_abs_lt_pi_div_two {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo (by rw [Set.mem_Ioo, ← abs_lt]; exact hθ)

lemma abs_profileX_one_mul_sin_le (θ : ℝ) :
    |profileX 1 * Real.sin θ| ≤ profileX 1 := by
  rw [abs_mul, abs_of_pos profileX_one_pos]
  exact mul_le_of_le_one_right profileX_one_pos.le (abs_sin_le_one θ)

lemma abs_profileX_one_mul_sin_lt {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    |profileX 1 * Real.sin θ| < profileX 1 := by
  rw [abs_mul, abs_of_pos profileX_one_pos]
  exact mul_lt_of_lt_one_right profileX_one_pos (abs_sin_lt_one_of_abs_lt_pi_div_two hθ)

/-- Positivity of `ψ` on the right end in the `sin`-substitution. -/
lemma psi_sin_pos_of_window {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {s : ℝ}
    (hs0 : 9 / 10 < s) (hs1 : s ≤ 1) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    0 < psi h semicircle s (profileX 1 * Real.sin θ) := by
  rw [psi_sin_eq hsupp (s := s) (by rw [one_sub_tau_eq]; exact hs0)]
  have hcos := cos_pos_of_abs_lt_pi_div_two hθ
  have hcos2 : 0 < Real.cos θ ^ 2 := pow_pos hcos 2
  have hsin : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0]
  nlinarith

/-- Positivity of `ψ` at `s = 1` away from the two endpoints. -/
lemma psi_one_pos_of_abs_lt {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) {t : ℝ}
    (ht : |t| < profileX 1) : 0 < psi h semicircle 1 t := by
  have ht1 : |t| ≤ 1 := le_trans ht.le profileX_one_le_one
  rw [psi_eq_quad_of_gt hsupp (s := 1) (by rw [one_sub_tau_eq]; norm_num) ht1]
  have h2 : t ^ 2 < 1 / 2 := by
    have habs := abs_lt.mp ht
    nlinarith [habs.1, habs.2, profileX_one_sq]
  nlinarith

/-! ## The slice of `ψ`, at the smooth order -/

lemma contDiff_slice_smooth (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => psi h semicircle u t) := by
  have hfe : (fun u : ℝ => psi h semicircle u t)
      = fun u : ℝ => (Real.sqrt (1 - t ^ 2)) ^ 2 - (u * t + h u) ^ 2 := by
    funext u; rw [psi_eq_sq]
  rw [hfe]
  fun_prop

/-- Uniform bounds for all `u`-derivatives of order `≤ n+1` of the slices of `ψ`, on the box
`[-profileX 1, profileX 1] × [9/10, 1]`. -/
lemma psi_slice_deriv_bound_smooth (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ n + 1, ∀ s ∈ Set.Icc (9 / 10 : ℝ) 1, ∀ t : ℝ,
      |t| ≤ profileX 1 →
      |iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s| ≤ M := by
  set U : Set (ℝ × ℝ) := {q : ℝ × ℝ | |q.1| < 1} with hUdef
  have hUopen : IsOpen U := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => psi h semicircle q.2 q.1) U := by
    have hpoly : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => 1 - q.1 ^ 2 - (q.2 * q.1 + h q.2) ^ 2) := by
      fun_prop
    refine hpoly.contDiffOn.congr (fun q hq => ?_)
    have hq1 : |q.1| ≤ 1 := le_of_lt hq
    exact psi_eq_quad hq1
  set K : Set (ℝ × ℝ) := Set.Icc (-(profileX 1)) (profileX 1) ×ˢ Set.Icc (9 / 10 : ℝ) 1
    with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [hUdef, Set.mem_setOf_eq]
    have hx1 : |x| ≤ profileX 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    exact lt_of_le_of_lt hx1 profileX_one_lt_one
  choose Cj hCj using fun j =>
    parametric_iteratedDeriv_bound_smooth
      (F := fun a b : ℝ => psi h semicircle b a) hUopen hF hKc hKU j
  refine ⟨max 1 (∑ j ∈ Finset.range (n + 2), max (Cj j) 1), le_max_left _ _, ?_⟩
  intro j hj s hs t ht
  have hmem : (t, s) ∈ K := by
    refine ⟨?_, hs⟩
    rw [abs_le] at ht
    exact ht
  have hb := hCj j (t, s) hmem
  have h1 : Cj j ≤ max (Cj j) 1 := le_max_left _ _
  have h2 : max (Cj j) 1 ≤ ∑ i ∈ Finset.range (n + 2), max (Cj i) 1 := by
    refine Finset.single_le_sum (f := fun i => max (Cj i) 1)
      (fun i _ => le_trans zero_le_one (le_max_right (Cj i) 1)) ?_
    simp only [Finset.mem_range]
    omega
  have h3 : (∑ i ∈ Finset.range (n + 2), max (Cj i) 1)
      ≤ max 1 (∑ i ∈ Finset.range (n + 2), max (Cj i) 1) := le_max_right _ _
  have hb' : |iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s| ≤ Cj j := by
    simpa using hb
  linarith

/-! ## The Faà di Bruno slice bounds, with positivity as a hypothesis -/

/-- The Faà di Bruno bound for the first inhomogeneity, with positivity of `ψ(s,t)` as an
explicit hypothesis (in place of a window estimate). -/
lemma E1_slice_bound_of_pos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s, 9 / 10 < s → s ≤ 1 → ∀ t, |t| ≤ profileX 1 →
      0 < psi h semicircle s t →
      |iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) s|
        ≤ K * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
  obtain ⟨M, hM1, hM⟩ := psi_slice_deriv_bound_smooth n hh
  obtain ⟨K, hK0, hK⟩ := iteratedDeriv_rpow_comp_bound_uniform ((n : ℝ) + 1 / 2) (n + 1)
    (C := M) hM1
  refine ⟨K, hK0, ?_⟩
  intro s hs0 hs1 t ht hpos
  have hslice := contDiff_slice_smooth h hh t
  have hmem : {u : ℝ | 0 < psi h semicircle u t} ∈ 𝓝 s :=
    (hslice.continuous.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
  have hev : (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) =ᶠ[𝓝 s]
      (fun u : ℝ => psi h semicircle u t ^ ((n : ℝ) + 1 / 2)) := by
    filter_upwards [hmem] with u hu
    show psi h semicircle u t ^ n * Real.sqrt (psi h semicircle u t)
      = psi h semicircle u t ^ ((n : ℝ) + 1 / 2)
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_add hu]
  rw [Filter.EventuallyEq.iteratedDeriv_eq _ hev]
  have hshift : iteratedDeriv (n + 1)
        (fun u : ℝ => psi h semicircle u t ^ ((n : ℝ) + 1 / 2)) s
      = iteratedDeriv (n + 1)
        (fun z : ℝ => psi h semicircle (z + s) t ^ ((n : ℝ) + 1 / 2)) 0 := by
    have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) (n + 1)
      (fun y : ℝ => psi h semicircle y t ^ ((n : ℝ) + 1 / 2)) s) 0
    simpa using hcomp.symm
  rw [hshift]
  have hsI : s ∈ Set.Icc (9 / 10 : ℝ) 1 := ⟨le_of_lt hs0, hs1⟩
  have hderiv : ∀ j ≤ n + 1,
      |iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0| ≤ M := by
    intro j hj
    have hsj : iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0
        = iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s := by
      have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) j
        (fun y : ℝ => psi h semicircle y t) s) 0
      simpa using hcomp
    rw [hsj]
    exact hM j hj s hsI t ht
  have hsm : ContDiffAt ℝ (n + 1) (fun z : ℝ => psi h semicircle (z + s) t) 0 := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => z + s) := by fun_prop
    exact (hslice.comp h2).contDiffAt.of_le (natCast_add_one_le_smooth n)
  have hΦC : psi h semicircle (0 + s) t ≤ M := by
    simpa using le_trans (psi_le_one (le_trans ht profileX_one_le_one) hpos.le) hM1
  have hbd := hK (n + 1) (psi h semicircle s t) (fun z : ℝ => psi h semicircle (z + s) t)
    (le_refl _) hpos (psi_le_one (le_trans ht profileX_one_le_one) hpos.le) hsm
    (by simpa using hpos.le) hΦC hderiv
  have hexp : (n : ℝ) + 1 / 2 - ((n + 1 : ℕ) : ℝ) = -(1 / 2) := by push_cast; ring
  rwa [hexp] at hbd

/-- The Faà di Bruno bound for the second inhomogeneity, with positivity of `ψ(s,t)` as an
explicit hypothesis. -/
lemma E2_slice_bound_of_pos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s, 9 / 10 < s → s ≤ 1 → ∀ t, |t| ≤ profileX 1 →
      0 < psi h semicircle s t →
      |iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) s|
        ≤ K * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, zero_le_one, ?_⟩
    intro s hs0 hs1 t ht hpos
    have h1 : (1 : ℝ) ≤ 1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ) := by
      have := Real.rpow_nonneg hpos.le (-(1 / 2) : ℝ); linarith
    have hls : |lineSlope h s t| ≤ 1 := by
      have := lineSlope_slice_bound hsupp (s := s) (t := t)
        (by rw [one_sub_tau_eq]; exact hs0) ht 0
      rwa [iteratedDeriv_zero] at this
    have hsq : Real.sqrt (psi h semicircle s t) ≤ 1 :=
      sqrt_le_one_of_le_one hpos.le (psi_le_one (le_trans ht profileX_one_le_one) hpos.le)
    have hnn : 0 ≤ Real.sqrt (psi h semicircle s t) := Real.sqrt_nonneg _
    have hb : |iteratedDeriv 0
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH 0 h (u, t)) s| ≤ 1 := by
      rw [iteratedDeriv_zero]
      calc |Work.OddVolterra.Existence.PhiH 0 h (s, t)|
          = |Real.sqrt (psi h semicircle s t) * lineSlope h s t| := by
            simp [Work.OddVolterra.Existence.PhiH]
        _ = Real.sqrt (psi h semicircle s t) * |lineSlope h s t| := by
            rw [abs_mul, abs_of_nonneg hnn]
        _ ≤ 1 * 1 := mul_le_mul hsq hls (abs_nonneg _) zero_le_one
        _ = 1 := by ring
    calc |iteratedDeriv 0 (fun u : ℝ => Work.OddVolterra.Existence.PhiH 0 h (u, t)) s| ≤ 1 := hb
      _ ≤ 1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by rw [one_mul]; exact h1
  · obtain ⟨M, hM1, hM⟩ := psi_slice_deriv_bound_smooth (n - 1) hh
    obtain ⟨K1, hK10, hK1⟩ := iteratedDeriv_rpow_comp_bound_uniform
      (((n - 1 : ℕ) : ℝ) + 1 / 2) n (C := M) hM1
    refine ⟨max 1 (K1 * 2 ^ n), le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro s hs0 hs1 t ht hpos
    have hc1 : psi h semicircle s t ≤ 1 :=
      psi_le_one (le_trans ht profileX_one_le_one) hpos.le
    have hc0 : 0 ≤ psi h semicircle s t := hpos.le
    have hslice := contDiff_slice_smooth h hh t
    have hsI : s ∈ Set.Icc (9 / 10 : ℝ) 1 := ⟨le_of_lt hs0, hs1⟩
    have hmem : {u : ℝ | 0 < psi h semicircle u t} ∈ 𝓝 s :=
      (hslice.continuous.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    have hev : (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) =ᶠ[𝓝 s]
        (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
          * lineSlope h u t) := by
      filter_upwards [hmem] with u hu
      show psi h semicircle u t ^ (n - 1) * Real.sqrt (psi h semicircle u t) * lineSlope h u t
        = (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) * lineSlope h u t
      congr 1
      rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_add hu]
    rw [Filter.EventuallyEq.iteratedDeriv_eq _ hev]
    have hf : ContDiffAt ℝ n
        (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s := by
      have h2 : ContDiffAt ℝ n (fun y : ℝ => y ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
          (psi h semicircle s t) :=
        Real.contDiffAt_rpow_const (n := n) (Or.inl (ne_of_gt hpos))
      exact h2.comp s (hslice.contDiffAt.of_le (natCast_le_smooth n))
    have hg : ContDiffAt ℝ n (fun u : ℝ => lineSlope h u t) s :=
      (contDiff_lineSlope_slice hh t).contDiffAt.of_le (natCast_le_smooth n)
    have hleib := iteratedDerivWithin_mul (𝕜 := ℝ) (n := n) (x := s) (s := Set.univ)
      (f := fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
      (g := fun u : ℝ => lineSlope h u t) (Set.mem_univ s) uniqueDiffOn_univ
      hf.contDiffWithinAt hg.contDiffWithinAt
    have hmul : iteratedDeriv n
        (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) * lineSlope h u t) s
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
          * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s := by
      rw [show (fun u : ℝ => (psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
            * lineSlope h u t)
          = ((fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2))
            * fun u : ℝ => lineSlope h u t) from rfl]
      simpa [iteratedDerivWithin_univ] using hleib
    rw [hmul]
    have hexp : ∀ i ≤ n, -(1 / 2 : ℝ) ≤ (((n - 1 : ℕ) : ℝ) + 1 / 2) - (i : ℝ) := by
      intro i hi
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      have hile : (i : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi
      linarith
    have hderiv : ∀ j ≤ n,
        |iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0| ≤ M := by
      intro j hj
      have hsj : iteratedDeriv j (fun z : ℝ => psi h semicircle (z + s) t) 0
          = iteratedDeriv j (fun u : ℝ => psi h semicircle u t) s := by
        have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) j
          (fun y : ℝ => psi h semicircle y t) s) 0
        simpa using hcomp
      rw [hsj]
      exact hM j (by omega) s hsI t ht
    have hsm : ContDiffAt ℝ n (fun z : ℝ => psi h semicircle (z + s) t) 0 := by
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => z + s) := by fun_prop
      exact (hslice.comp h2).contDiffAt.of_le (natCast_le_smooth n)
    have hΦC : psi h semicircle (0 + s) t ≤ M := by
      simpa using le_trans hc1 hM1
    have hfi : ∀ i ≤ n,
        |iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s|
        ≤ K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
      intro i hi
      have hshift : iteratedDeriv i
            (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
          = iteratedDeriv i
            (fun z : ℝ => psi h semicircle (z + s) t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) 0 := by
        have hcomp := congr_fun (iteratedDeriv_comp_add_const (𝕜 := ℝ) (F := ℝ) i
          (fun y : ℝ => psi h semicircle y t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s) 0
        simpa using hcomp.symm
      rw [hshift]
      have hb := hK1 i (psi h semicircle s t) (fun z : ℝ => psi h semicircle (z + s) t)
        (by omega) hpos hc1 hsm (by simpa using hc0) hΦC hderiv
      have hmono : (psi h semicircle s t) ^ ((((n - 1 : ℕ) : ℝ) + 1 / 2) - (i : ℝ))
          ≤ (psi h semicircle s t) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hc1 (hexp i hi)
      refine le_trans hb ?_
      apply mul_le_mul_of_nonneg_left ?_ hK10
      linarith
    have hgl : ∀ m, |iteratedDeriv m (fun u : ℝ => lineSlope h u t) s| ≤ 1 :=
      fun m => lineSlope_slice_bound hsupp (s := s) (t := t)
        (by rw [one_sub_tau_eq]; exact hs0) ht m
    calc |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * iteratedDeriv i (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
            * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s|
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
            * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
          intro i hi
          rw [Finset.mem_range] at hi
          have hi' : i ≤ n := by omega
          calc |(n.choose i : ℝ)
                * iteratedDeriv i
                    (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s
                * iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s|
              = (n.choose i : ℝ)
                * |iteratedDeriv i
                    (fun u : ℝ => psi h semicircle u t ^ (((n - 1 : ℕ) : ℝ) + 1 / 2)) s|
                * |iteratedDeriv (n - i) (fun u : ℝ => lineSlope h u t) s| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
            _ ≤ (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1 := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hfi i hi') (Nat.cast_nonneg _))
                  (hgl (n - i)) (abs_nonneg _)
                  (mul_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg hK10 (by have := Real.rpow_nonneg hc0 (-(1 / 2) : ℝ); linarith)))
      _ = (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 2 ^ n := by
          have h1 : ∀ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 1
              = (n.choose i : ℝ) * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) := by
            intro i _; ring
          rw [Finset.sum_congr rfl h1]
          have h2 : ∑ x ∈ Finset.range (n + 1), (n.choose x : ℝ)
              * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)))
              = (∑ x ∈ Finset.range (n + 1), (n.choose x : ℝ))
                * (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) := (Finset.sum_mul ..).symm
          rw [h2, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
      _ ≤ max 1 (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by
          have hK1' : K1 * 2 ^ n ≤ max 1 (K1 * 2 ^ n) := le_max_right _ _
          have h1 : (0 : ℝ) ≤ 1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ) := by
            have := Real.rpow_nonneg hc0 (-(1 / 2) : ℝ); linarith
          calc (K1 * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ))) * 2 ^ n
              = (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) := by ring
            _ ≤ max 1 (K1 * 2 ^ n) * (1 + (psi h semicircle s t) ^ (-(1 / 2) : ℝ)) :=
                mul_le_mul_of_nonneg_right hK1' h1

/-! ## The `θ`-bounds -/

lemma E1_theta_bound_of_pos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 9 / 10 < s → s ≤ 1 → ∀ θ, |θ| < Real.pi / 2 →
      |G1 n h (s, profileX 1 * Real.sin θ)| * (profileX 1 * Real.cos θ) ≤ C := by
  obtain ⟨K, hK0, hK⟩ := E1_slice_bound_of_pos n hh
  have hX1 := profileX_one_pos
  refine ⟨max (2 * K * profileX 1) 0, le_max_right _ _, ?_⟩
  intro s hs0 hs1 θ hθ
  have hcos := cos_pos_of_abs_lt_pi_div_two hθ
  have ht : |profileX 1 * Real.sin θ| ≤ profileX 1 := abs_profileX_one_mul_sin_le θ
  have hpos : 0 < psi h semicircle s (profileX 1 * Real.sin θ) :=
    psi_sin_pos_of_window hsupp hs0 hs1 hθ
  have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h := hpos
  have hident : G1 n h (s, profileX 1 * Real.sin θ)
      = iteratedDeriv (n + 1)
        (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, profileX 1 * Real.sin θ)) s := by
    rw [G1, iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
      (Work.OddVolterra.Existence.contDiffOn_PhiF hh n) hmem (n + 1)]
  rw [hident]
  have hb := hK s hs0 hs1 (profileX 1 * Real.sin θ) ht hpos
  have hge := psi_sin_ge_cos_sq hsupp (s := s) (by rw [one_sub_tau_eq]; exact hs0) hs1 θ
  have hle : (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ) * Real.cos θ ≤ 1 :=
    rpow_neg_half_mul_le_one hpos hcos.le hge
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  refine le_trans ?_ (le_max_left _ _)
  calc |iteratedDeriv (n + 1)
          (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, profileX 1 * Real.sin θ)) s|
        * (profileX 1 * Real.cos θ)
      ≤ (K * (1 + (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)))
        * (profileX 1 * Real.cos θ) := by
        apply mul_le_mul_of_nonneg_right hb
        positivity
    _ = K * profileX 1 * Real.cos θ
          + (K * profileX 1) * ((psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)
            * Real.cos θ) := by ring
    _ ≤ K * profileX 1 * 1 + (K * profileX 1) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hK0 hX1.le)
        · exact mul_le_mul_of_nonneg_left hle (mul_nonneg hK0 hX1.le)
    _ = 2 * K * profileX 1 := by ring

lemma E2_theta_bound_of_pos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 9 / 10 < s → s ≤ 1 → ∀ θ, |θ| < Real.pi / 2 →
      |G2 n h (s, profileX 1 * Real.sin θ)| * (profileX 1 * Real.cos θ) ≤ C := by
  obtain ⟨K, hK0, hK⟩ := E2_slice_bound_of_pos n hh hsupp
  have hX1 := profileX_one_pos
  refine ⟨max (2 * K * profileX 1) 0, le_max_right _ _, ?_⟩
  intro s hs0 hs1 θ hθ
  have hcos := cos_pos_of_abs_lt_pi_div_two hθ
  have ht : |profileX 1 * Real.sin θ| ≤ profileX 1 := abs_profileX_one_mul_sin_le θ
  have hpos : 0 < psi h semicircle s (profileX 1 * Real.sin θ) :=
    psi_sin_pos_of_window hsupp hs0 hs1 hθ
  have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h := hpos
  have hident : G2 n h (s, profileX 1 * Real.sin θ)
      = iteratedDeriv n
        (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, profileX 1 * Real.sin θ)) s := by
    rw [G2, iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
      (Work.OddVolterra.Existence.contDiffOn_PhiH hh n) hmem n]
  rw [hident]
  have hb := hK s hs0 hs1 (profileX 1 * Real.sin θ) ht hpos
  have hge := psi_sin_ge_cos_sq hsupp (s := s) (by rw [one_sub_tau_eq]; exact hs0) hs1 θ
  have hle : (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ) * Real.cos θ ≤ 1 :=
    rpow_neg_half_mul_le_one hpos hcos.le hge
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  refine le_trans ?_ (le_max_left _ _)
  calc |iteratedDeriv n
          (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, profileX 1 * Real.sin θ)) s|
        * (profileX 1 * Real.cos θ)
      ≤ (K * (1 + (psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)))
        * (profileX 1 * Real.cos θ) := by
        apply mul_le_mul_of_nonneg_right hb
        positivity
    _ = K * profileX 1 * Real.cos θ
          + (K * profileX 1) * ((psi h semicircle s (profileX 1 * Real.sin θ)) ^ (-(1 / 2) : ℝ)
            * Real.cos θ) := by ring
    _ ≤ K * profileX 1 * 1 + (K * profileX 1) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hK0 hX1.le)
        · exact mul_le_mul_of_nonneg_left hle (mul_nonneg hK0 hX1.le)
    _ = 2 * K * profileX 1 := by ring

/-! ## The `E₁`, `E₂` integrands as `sin`-substituted `θ`-integrals -/

/-- The slice of the `E₁` integrand. -/
def E1slice (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv (n + 1)
    (fun u : ℝ => Work.OddVolterra.Existence.PhiF n h (u, t)) s

/-- The slice of the `E₂` integrand. -/
def E2slice (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv n
    (fun u : ℝ => Work.OddVolterra.Existence.PhiH n h (u, t)) s

lemma E1slice_eq_G1_of_mem {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s t : ℝ}
    (hmem : (s, t) ∈ Work.OddVolterra.Existence.psiPos h) :
    E1slice n h s t = G1 n h (s, t) := by
  rw [E1slice, iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
    (Work.OddVolterra.Existence.contDiffOn_PhiF hh n) hmem (n + 1)]
  rfl

lemma E2slice_eq_G2_of_mem {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s t : ℝ}
    (hmem : (s, t) ∈ Work.OddVolterra.Existence.psiPos h) :
    E2slice n h s t = G2 n h (s, t) := by
  rw [E2slice, iteratedDeriv_eq_pderiv1Iter (Work.OddVolterra.Existence.isOpen_psiPos hh)
    (Work.OddVolterra.Existence.contDiffOn_PhiH hh n) hmem n]
  rfl

lemma E1_eq_slice_integral (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    E1 n h s = ∫ t in (-(profileX 1))..(profileX 1), E1slice n h s t := rfl

lemma E2_eq_slice_integral (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    E2 n h s = ∫ t in (-(profileX 1))..(profileX 1), E2slice n h s t := rfl

/-- The `t`-integral defining `E₁` is a `θ`-integral over `(-π/2, π/2)`. -/
lemma hmid_E1_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t)
    {s : ℝ} (hs0 : 9 / 10 < s) (hs1 : s < 1) :
    E1 n h s = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E1 n h s
      = ∫ t in (-(profileX 1))..(profileX 1), G1 n h (s, t) := by
    rw [E1_eq_slice_integral]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    exact E1slice_eq_G1_of_mem hh (psi_pos_of_hmid hmid ⟨by linarith, hs1⟩ ht1)
  rw [hstep1]
  exact (integral_comp_sin (g := fun t => G1 n h (s, t))).symm

/-- The value of `E₁` at `s = 1` as a `θ`-integral. -/
lemma hmid_E1_one_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    E1 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E1 n h 1
      = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          E1slice n h 1 (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
    rw [E1_eq_slice_integral]
    exact (integral_comp_sin (g := E1slice n h 1)).symm
  rw [hstep1]
  refine intervalIntegral.integral_congr (fun θ hθ => ?_)
  by_cases htop : |θ| = Real.pi / 2
  · have hcos0 : Real.cos θ = 0 := by
      rcases (abs_eq (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)).mp htop with h | h
      · rw [h, Real.cos_pi_div_two]
      · rw [h, Real.cos_neg, Real.cos_pi_div_two]
    simp [hcos0]
  · have hθ' : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      exact ⟨hθ.1, hθ.2⟩
    have habs : |θ| < Real.pi / 2 := lt_of_le_of_ne (abs_le.mpr ⟨hθ'.1, hθ'.2⟩) htop
    have ht : |profileX 1 * Real.sin θ| < profileX 1 := abs_profileX_one_mul_sin_lt habs
    show E1slice n h 1 (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
      = G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
    rw [E1slice_eq_G1_of_mem hh (psi_one_pos_of_abs_lt hsupp ht)]

/-- The `t`-integral defining `E₂` is a `θ`-integral over `(-π/2, π/2)`. -/
lemma hmid_E2_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t)
    {s : ℝ} (hs0 : 9 / 10 < s) (hs1 : s < 1) :
    E2 n h s = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E2 n h s
      = ∫ t in (-(profileX 1))..(profileX 1), G2 n h (s, t) := by
    rw [E2_eq_slice_integral]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht1 : |t| ≤ profileX 1 := by
      rw [Set.uIcc_of_le (by linarith [profileX_one_pos])] at ht
      exact abs_le.mpr ht
    exact E2slice_eq_G2_of_mem hh (psi_pos_of_hmid hmid ⟨by linarith, hs1⟩ ht1)
  rw [hstep1]
  exact (integral_comp_sin (g := fun t => G2 n h (s, t))).symm

/-- The value of `E₂` at `s = 1` as a `θ`-integral. -/
lemma hmid_E2_one_eq_theta_integral (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    E2 n h 1 = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
  have hstep1 : E2 n h 1
      = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          E2slice n h 1 (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ) := by
    rw [E2_eq_slice_integral]
    exact (integral_comp_sin (g := E2slice n h 1)).symm
  rw [hstep1]
  refine intervalIntegral.integral_congr (fun θ hθ => ?_)
  by_cases htop : |θ| = Real.pi / 2
  · have hcos0 : Real.cos θ = 0 := by
      rcases (abs_eq (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)).mp htop with h | h
      · rw [h, Real.cos_pi_div_two]
      · rw [h, Real.cos_neg, Real.cos_pi_div_two]
    simp [hcos0]
  · have hθ' : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      exact ⟨hθ.1, hθ.2⟩
    have habs : |θ| < Real.pi / 2 := lt_of_le_of_ne (abs_le.mpr ⟨hθ'.1, hθ'.2⟩) htop
    have ht : |profileX 1 * Real.sin θ| < profileX 1 := abs_profileX_one_mul_sin_lt habs
    show E2slice n h 1 (profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
      = G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)
    rw [E2slice_eq_G2_of_mem hh (psi_one_pos_of_abs_lt hsupp ht)]

/-! ## Continuity of the two integrand families -/

lemma continuous_G1_mul_cos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (fun θ : ℝ =>
      G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)) := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (G1 n h) (Work.OddVolterra.Existence.psiPos h) :=
    contDiffOn_G1 n hh
  have h1 : Continuous (fun θ : ℝ => G1 n h (s, profileX 1 * Real.sin θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
      psi_pos_of_hmid hmid hs (abs_profileX_one_mul_sin_le θ)
    have hmap : ContinuousAt (fun θ : ℝ => (s, profileX 1 * Real.sin θ)) θ :=
      (continuous_const.prodMk (continuous_const.mul Real.continuous_sin)).continuousAt
    exact (hG.continuousOn.continuousAt
      ((Work.OddVolterra.Existence.isOpen_psiPos hh).mem_nhds hmem)).comp
      (x := θ) (f := fun θ : ℝ => (s, profileX 1 * Real.sin θ)) hmap
  have h2 : Continuous fun θ : ℝ => profileX 1 * Real.cos θ := by fun_prop
  exact h1.mul h2

lemma continuous_G2_mul_cos (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (fun θ : ℝ =>
      G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ)) := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (G2 n h) (Work.OddVolterra.Existence.psiPos h) :=
    contDiffOn_G2 n hh
  have h1 : Continuous (fun θ : ℝ => G2 n h (s, profileX 1 * Real.sin θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hmem : (s, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
      psi_pos_of_hmid hmid hs (abs_profileX_one_mul_sin_le θ)
    have hmap : ContinuousAt (fun θ : ℝ => (s, profileX 1 * Real.sin θ)) θ :=
      (continuous_const.prodMk (continuous_const.mul Real.continuous_sin)).continuousAt
    exact (hG.continuousOn.continuousAt
      ((Work.OddVolterra.Existence.isOpen_psiPos hh).mem_nhds hmem)).comp
      (x := θ) (f := fun θ : ℝ => (s, profileX 1 * Real.sin θ)) hmap
  have h2 : Continuous fun θ : ℝ => profileX 1 * Real.cos θ := by fun_prop
  exact h1.mul h2

/-- `(9/10, 1)` is a left-neighbourhood of `1`. -/
lemma Ioo_mem_nhdsLT_one : Set.Ioo (9 / 10 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
  have h1 : Set.Ioi (9 / 10 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_inf_of_left (Ioi_mem_nhds (by norm_num))
  have h2 : Set.Iio (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) := self_mem_nhdsWithin
  have h := inter_mem h1 h2
  convert h using 1
  ext x
  simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio]

/-- Almost-everywhere statements on `uIoc (-π/2) (π/2)` reduce to the open interval. -/
lemma ae_uIoc_imp {p : ℝ → Prop} (h : ∀ θ, |θ| < Real.pi / 2 → p θ) :
    ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (-(Real.pi / 2)) (Real.pi / 2) → p θ := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_singleton (Real.pi / 2))
  intro θ hθ
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact hθ (fun hm => h θ (by
    have hmem : θ ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) := by
      rwa [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hm
    exact abs_lt.mpr ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩))

/-! ## Dominated convergence for the `θ`-integrals -/

lemma tendsto_theta_integral_E1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t) :
    Tendsto (fun s : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G1 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))) := by
  obtain ⟨C, hC0, hC⟩ := E1_theta_bound_of_pos n hh hsupp
  exact intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun s θ => G1 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
    (x₀ := (1 : ℝ)) (bound := fun _ => C) (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (s := Set.Iio 1) (μ := volume)
    (by
      filter_upwards [Ioo_mem_nhdsLT_one] with s hs
      exact (continuous_G1_mul_cos n hh hmid ⟨by linarith [hs.1], hs.2⟩).aestronglyMeasurable)
    (by
      filter_upwards [Ioo_mem_nhdsLT_one] with s hs
      refine ae_uIoc_imp (fun θ hθ => ?_)
      have hcos := cos_pos_of_abs_lt_pi_div_two hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos profileX_one_pos hcos)]
      exact hC s hs.1 hs.2.le θ hθ)
    intervalIntegrable_const
    (by
      refine ae_uIoc_imp (fun θ hθ => ?_)
      have ht : |profileX 1 * Real.sin θ| < profileX 1 := abs_profileX_one_mul_sin_lt hθ
      have hmem : (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
        psi_one_pos_of_abs_lt hsupp ht
      have hGc : ContinuousAt (G1 n h) (1, profileX 1 * Real.sin θ) :=
        (contDiffOn_G1 n hh).continuousOn.continuousAt
          ((Work.OddVolterra.Existence.isOpen_psiPos hh).mem_nhds hmem)
      have hmap : ContinuousAt (fun s : ℝ => (s, profileX 1 * Real.sin θ)) 1 :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact ((hGc.comp (x := (1 : ℝ))
        (f := fun s : ℝ => (s, profileX 1 * Real.sin θ)) hmap).mul
        continuousAt_const).continuousWithinAt)

lemma tendsto_theta_integral_E2 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t) :
    Tendsto (fun s : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        G2 n h (1, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))) := by
  obtain ⟨C, hC0, hC⟩ := E2_theta_bound_of_pos n hh hsupp
  exact intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun s θ => G2 n h (s, profileX 1 * Real.sin θ) * (profileX 1 * Real.cos θ))
    (x₀ := (1 : ℝ)) (bound := fun _ => C) (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (s := Set.Iio 1) (μ := volume)
    (by
      filter_upwards [Ioo_mem_nhdsLT_one] with s hs
      exact (continuous_G2_mul_cos n hh hmid ⟨by linarith [hs.1], hs.2⟩).aestronglyMeasurable)
    (by
      filter_upwards [Ioo_mem_nhdsLT_one] with s hs
      refine ae_uIoc_imp (fun θ hθ => ?_)
      have hcos := cos_pos_of_abs_lt_pi_div_two hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos profileX_one_pos hcos)]
      exact hC s hs.1 hs.2.le θ hθ)
    intervalIntegrable_const
    (by
      refine ae_uIoc_imp (fun θ hθ => ?_)
      have ht : |profileX 1 * Real.sin θ| < profileX 1 := abs_profileX_one_mul_sin_lt hθ
      have hmem : (1, profileX 1 * Real.sin θ) ∈ Work.OddVolterra.Existence.psiPos h :=
        psi_one_pos_of_abs_lt hsupp ht
      have hGc : ContinuousAt (G2 n h) (1, profileX 1 * Real.sin θ) :=
        (contDiffOn_G2 n hh).continuousOn.continuousAt
          ((Work.OddVolterra.Existence.isOpen_psiPos hh).mem_nhds hmem)
      have hmap : ContinuousAt (fun s : ℝ => (s, profileX 1 * Real.sin θ)) 1 :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact ((hGc.comp (x := (1 : ℝ))
        (f := fun s : ℝ => (s, profileX 1 * Real.sin θ)) hmap).mul
        continuousAt_const).continuousWithinAt)

/-! ## The left limits of `E₁`, `E₂` at `1` -/

lemma tendsto_E1_left (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t) :
    Tendsto (E1 n h) (𝓝[<] (1 : ℝ)) (𝓝 (E1 n h 1)) := by
  have hmain := tendsto_theta_integral_E1 n hh hsupp hmid
  rw [(hmid_E1_one_eq_theta_integral n hh hsupp).symm] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [Ioo_mem_nhdsLT_one] with s hs
  exact (hmid_E1_eq_theta_integral n hh hmid hs.1 hs.2).symm

lemma tendsto_E2_left (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(profileX 1)) (profileX 1), 0 < psi h semicircle s t) :
    Tendsto (E2 n h) (𝓝[<] (1 : ℝ)) (𝓝 (E2 n h 1)) := by
  have hmain := tendsto_theta_integral_E2 n hh hsupp hmid
  rw [(hmid_E2_one_eq_theta_integral n hh hsupp).symm] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [Ioo_mem_nhdsLT_one] with s hs
  exact (hmid_E2_eq_theta_integral n hh hmid hs.1 hs.2).symm

/-! ## From the left limit to continuity within `[a,1]` -/

/-- A left limit at `1` is a continuity statement within `[a,1]`: adjoining the point `1`
costs nothing because `f 1 ∈ T` for every neighbourhood `T` of `f 1`. -/
lemma continuousWithinAt_Icc_one_of_tendsto_nhdsLT {f : ℝ → ℝ} {a : ℝ}
    (h : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (f 1))) :
    ContinuousWithinAt f (Set.Icc a 1) 1 := by
  have hunion : ContinuousWithinAt f (Set.Iio 1 ∪ {1}) 1 := by
    rw [ContinuousWithinAt, nhdsWithin_union, nhdsWithin_singleton]
    exact tendsto_sup.mpr ⟨h, tendsto_pure_nhds f 1⟩
  refine hunion.mono ?_
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · exact Or.inr (Set.mem_singleton_iff.mpr h1)
  · exact Or.inl h1

theorem E1_E2_continuousOn_Icc (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t)
    {a : ℝ} (ha : 0 < a) :
    ContinuousOn (Work.OddVolterra.E1 n h) (Set.Icc a 1) ∧
    ContinuousOn (Work.OddVolterra.E2 n h) (Set.Icc a 1) := by
  have hcd := Work.OddVolterra.Existence.E1_E2_contDiff n hn hh hmid
  constructor
  · intro x hx
    rcases lt_or_ge x 1 with hx1 | hx1
    · have hmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ha hx.1, hx1⟩
      exact (hcd.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hmem)).continuousWithinAt
    · have hx' : x = 1 := le_antisymm hx.2 hx1
      subst hx'
      exact continuousWithinAt_Icc_one_of_tendsto_nhdsLT (tendsto_E1_left n hh hsupp hmid)
  · intro x hx
    rcases lt_or_ge x 1 with hx1 | hx1
    · have hmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ha hx.1, hx1⟩
      exact (hcd.2.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hmem)).continuousWithinAt
    · have hx' : x = 1 := le_antisymm hx.2 hx1
      subst hx'
      exact continuousWithinAt_Icc_one_of_tendsto_nhdsLT (tendsto_E2_left n hh hsupp hmid)

end

end Work.OddVolterra.Smooth
