import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## Two elementary facts about radial (`z`-only) functions

Both are specialisations of the junk-free parts of the `D_θ`-calculus: `D_θ` carries the factor
`sin(2θ)`, so it kills every function of `z` alone, and `∂_z` kills the zero function. -/

/-- Every strictly positive iterate of `D_θ` of a `z`-only (radial) function vanishes. -/
theorem DthIter_succ_radial_eq_zero (R : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter (i + 1) (fun z _ => R z) = 0 := by
  induction i with
  | zero =>
      funext z θ
      simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
  | succ i ih =>
      have hstep : Work.Spaces.DthIter (i.succ + 1) (fun z _ => R z)
          = Work.Spaces.Dth (Work.Spaces.DthIter (i + 1) (fun z _ => R z)) :=
        Work.Spaces.DthIter_succ (i + 1) _
      rw [hstep, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- `∂_z^c` of the zero function vanishes. -/
theorem pzIter_zero_apply (c : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter c (0 : ℝ → ℝ → ℝ) z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  simpa using Work.Spaces.iteratedDeriv_zero_fun c z

/-- `∂_z^c D_θ^a` of a `z`-only (radial) function vanishes for `a ≥ 1`. -/
theorem pzIter_DthIter_radial_apply (R : ℝ → ℝ) (a c : ℕ) (ha : 1 ≤ a) (z θ : ℝ) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z _ => R z)) z θ = 0 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [DthIter_succ_radial_eq_zero R a']
  exact pzIter_zero_apply c z θ

/-! ## The pointwise bound

`Work.Spaces.pz_DthIter_mul_eq` expands `∂_z^k D_θ^j (φ·h)` binomially in both variables; the
`a ≥ 1` terms of the angular expansion are killed by the radiality of `φ`, and each of the
surviving `a = 0` terms is bounded by `Work.Spaces.WlInf_z_bound` (for `φ`) and
`Work.Spaces.factor_bound` (for `h`).  The resulting `2^k` summands are then summed with
`Nat.sum_range_choose`. -/

/-- **Pointwise `z`-Leibniz bound for the radial product.**  For `SmoothInt` factors `φ` (radial)
and `h`, both in `𝒲^{4,∞}`, and `k + j ≤ 4`,

`|(z+1)^k ∂_z^k D_θ^j (φ·h)| ≤ 2^k |φ|_𝒲 |h|_𝒲 Ψ_j(θ)` on the closed quadrant,
with `Ψ_0 = 1` and `Ψ_j = (α + sin 2θ) sin(2θ)^{α/5}` for `j ≥ 1`. -/
theorem pzIter_DthIter_radial_bound {α : ℝ} (hα : 0 < α) (φ : ℝ → ℝ) (h : ℝ → ℝ → ℝ)
    (hφS : Work.Spaces.SmoothInt (fun z _ => φ z)) (hhS : Work.Spaces.SmoothInt h)
    (hφm : Work.Spaces.WlInfMem α 4 (fun z _ => φ z)) (hhm : Work.Spaces.WlInfMem α 4 h)
    (j k : ℕ) (hk : k ≤ 4) (hkj : k + j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ|
        ≤ (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h)
          * (if j = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hWφnn : 0 ≤ Work.Spaces.WlInf α 4 (fun z _ => φ z) :=
    Work.Spaces.WlInf_nonneg α 4 _ hφm
  have hWhnn : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hΦnn : 0 ≤ (if j = 0 then (1 : ℝ)
      else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    by_cases hj : j = 0
    · rw [if_pos hj]; norm_num
    · rw [if_neg hj]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg hsin _)
  -- the Leibniz expansion, with the radial part of the angular sum collapsed onto `a = 0`
  have hleib := Work.Spaces.pz_DthIter_mul_eq k j (fun z _ => φ z) h hφS hhS z hz θ hθ
  have hcollapse : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ
      = ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) *
          (Work.Spaces.pzIter c (fun z _ => φ z) z θ
            * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ) := by
    rw [hleib]
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro a ha ha0
      refine Finset.sum_eq_zero fun c hc => ?_
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [pzIter_DthIter_radial_apply φ (a' + 1) c (by omega) z θ]
      ring
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h0
    · refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Work.Spaces.DthIter_zero,
        one_mul]
  -- the whole sum vanishes, `c = 0` included
  have hsum2 : (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) = (2 : ℝ) ^ k := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  -- pull the weight inside the collapsed sum
  have hfac : ∀ c ∈ Finset.range (k + 1),
      (z + 1) ^ k * ((k.choose c : ℝ) * (Work.Spaces.pzIter c (fun z _ => φ z) z θ
            * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ))
        = (k.choose c : ℝ) * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
            * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ) := by
    intro c hc
    have hck : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hpc : (z + 1) ^ c * (z + 1) ^ (k - c) = (z + 1) ^ k := by
      rw [← pow_add, Nat.add_sub_cancel' hck]
    calc (z + 1) ^ k * ((k.choose c : ℝ) * (Work.Spaces.pzIter c (fun z _ => φ z) z θ
            * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ))
        = (z + 1) ^ c * (z + 1) ^ (k - c) * (k.choose c : ℝ)
            * Work.Spaces.pzIter c (fun z _ => φ z) z θ
            * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ := by
          rw [hpc]; ring
      _ = (k.choose c : ℝ) * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
            * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ) := by
          ring
  -- the termwise bound
  have hterm : ∀ c ∈ Finset.range (k + 1),
      |(k.choose c : ℝ) * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
          * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)|
        ≤ (k.choose c : ℝ) * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
            * (Work.Spaces.WlInf α 4 h
              * (if j = 0 then (1 : ℝ)
                else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
    intro c hc
    have hcmem : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hc4 : c ≤ 4 := by omega
    have hkc4 : k - c ≤ 4 := by omega
    have hA := Work.Spaces.WlInf_z_bound α 4 (fun z _ => φ z) hφm c hc4 z θ hz hθ
    have hB := Work.Spaces.factor_bound α hα h hhm (k - c) j hkc4 (fun _ => by omega) z θ hz hθ
    have e1 : |(k.choose c : ℝ) * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
          * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)|
        = (k.choose c : ℝ)
          * (|(z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ|
            * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ|) := by
      rw [show (k.choose c : ℝ) * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
            * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)
          = (k.choose c : ℝ) * (((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
            * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ))
          from by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose c)), abs_mul]
    rw [e1]
    have hstep : |(z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ|
          * |(z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ|
        ≤ Work.Spaces.WlInf α 4 (fun z _ => φ z)
          * (Work.Spaces.WlInf α 4 h
            * (if j = 0 then (1 : ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      mul_le_mul hA hB (abs_nonneg _) hWφnn
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (k.choose c))
  -- assemble
  rw [hcollapse]
  have hrewrite : (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1), ((k.choose c : ℝ)
        * (Work.Spaces.pzIter c (fun z _ => φ z) z θ
          * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)))
      = ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
          * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
          * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hfac
  rw [hrewrite]
  calc |∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
          * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
          * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)|
      ≤ ∑ c ∈ Finset.range (k + 1), |(k.choose c : ℝ)
          * ((z + 1) ^ c * Work.Spaces.pzIter c (fun z _ => φ z) z θ)
          * ((z + 1) ^ (k - c) * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter j h) z θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)
          * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
            * (Work.Spaces.WlInf α 4 h
              * (if j = 0 then (1 : ℝ)
                else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
        Finset.sum_le_sum hterm
    _ = (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ))
          * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
            * (Work.Spaces.WlInf α 4 h
              * (if j = 0 then (1 : ℝ)
                else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h)
          * (if j = 0 then (1 : ℝ)
            else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        rw [hsum2]; ring

/-- **The `wrad` field of the repaired `N4Norm`, in the exact form of the interface.**

The interface (revision of 07:49) requires `Work.Spaces.SmoothInt (fun z _ => φ z)` and
`Work.Spaces.SmoothInt h`.  The *second* conjunct of `SmoothInt` — every `z`-slice
`z ↦ h z θ`, `θ ∈ Iθ`, is smooth on `(-1,∞)` — is what makes this version easier than
`N4Fields/wrad_field_smooth` (whose `SmoothQuad` hypotheses constrain `h` only on the *open*
quadrant, leaving the boundary lines `θ = 0, π/2` arbitrary and requiring a junk-derivative
analysis there).

Route (the sibling `wang_field_smoothInt` is proved and is the same argument).  `θ`-differentiation
does not touch a function of `z` alone, so
`DthIter j (fun z θ => φ z * h z θ) = fun z θ => φ z * DthIter j h z θ` (the `θ`-Leibniz rule
with a constant-in-`θ` factor; both sides vanish at `θ = 0, π/2` because of the `sin(2θ)`
factor), and the `z`-Leibniz rule (`Work.Spaces.pz_DthIter_mul_eq`, `pz_mixed_mul_le_4`, both
requiring exactly `SmoothInt` of the two factors) expands `pzIter k` of the product over the
`α`-uniform factor bounds `Work.Spaces.WlInf_z_bound` and
`Work.Spaces.factor_bound`/`WlInf_mixed_bound`.  Every summand of the resulting sums is
`≤ 2^k·|φ|_𝒲·|h|_𝒲`, so `Work.Spaces.WlInfMem`/`WlInf` of the product are bounded by
`B := 16·|φ|_𝒲·|h|_𝒲` pointwise on all of `Iz × Iθ`, and
`Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds` turns that into the two conclusions
(with `C := 30·16 = 480`). -/
theorem wrad_field_smoothInt {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Work.FTS.Galerkin.Fn),
      Work.Spaces.SmoothInt (fun z _ => φ z) → Work.Spaces.SmoothInt h →
      Work.Spaces.WlInfMem α 4 (fun z _ => φ z) → Work.Spaces.WlInfMem α 4 h →
      Work.Spaces.WlInfMem α 4 (fun z θ => φ z * h z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => φ z * h z θ)
        ≤ C * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by
  refine ⟨480, by norm_num, ?_⟩
  intro α hα φ h hφS hhS hφm hhm
  have hα0 : 0 < α := hα.1
  have hWφnn : 0 ≤ Work.Spaces.WlInf α 4 (fun z _ => φ z) :=
    Work.Spaces.WlInf_nonneg α 4 _ hφm
  have hWhnn : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
  have hWhnn' : 0 ≤ Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h :=
    mul_nonneg hWφnn hWhnn
  have hBnn : 0 ≤ 16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h :=
    mul_nonneg (mul_nonneg (by norm_num) hWφnn) hWhnn
  have hpow16 : ∀ k : ℕ, k ≤ 4 → (2 : ℝ) ^ k ≤ 16 := by
    intro k hk
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at h
    exact h
  -- the radial pointwise bound
  have hr : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => φ z * h z θ) z θ|
        ≤ 16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by
    intro k hk z hz θ hθ
    have hmain := pzIter_DthIter_radial_bound hα0 φ h hφS hhS hφm hhm 0 k hk (by omega) z hz θ hθ
    rw [if_pos rfl, mul_one] at hmain
    calc |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => φ z * h z θ) z θ|
        ≤ (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
            * Work.Spaces.WlInf α 4 h) := hmain
      _ ≤ 16 * (Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h) :=
          mul_le_mul_of_nonneg_right (hpow16 k hk) hWhnn'
      _ = 16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by ring
  -- the mixed pointwise bound
  have ht : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ 16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by
    intro j k hj hkj z hz θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hspos : 0 < α + Real.sin (2 * θ) := by linarith
    have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin _) hspos.le
    have hmain := pzIter_DthIter_radial_bound hα0 φ h hφS hhS hφm hhm j k (by omega) hkj
      z hz θ hθ
    rw [if_neg (by omega : ¬ j = 0)] at hmain
    have hΦw : ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 :=
      weight_mul_div_le_one hα0 hsin
    have hXw : |(z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        = |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin _), abs_of_pos hspos]
      ring
    rw [hXw]
    have h2knn : 0 ≤ (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
        * Work.Spaces.WlInf α 4 h) := mul_nonneg (pow_nonneg (by norm_num) k) hWhnn'
    calc |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => φ z * h z θ)) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ ((2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hmain hw0
      _ = ((2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
              * Work.Spaces.WlInf α 4 h))
          * (((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      _ ≤ ((2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
              * Work.Spaces.WlInf α 4 h)) * 1 := mul_le_mul_of_nonneg_left hΦw h2knn
      _ = (2 : ℝ) ^ k * (Work.Spaces.WlInf α 4 (fun z _ => φ z)
            * Work.Spaces.WlInf α 4 h) := by ring
      _ ≤ 16 * (Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h) :=
          mul_le_mul_of_nonneg_right (hpow16 k (by omega)) hWhnn'
      _ = 16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by ring
  obtain ⟨hmem, hle⟩ := wlInf_of_pointwise_bounds hBnn hr ht
  exact ⟨hmem, by
    calc Work.Spaces.WlInf α 4 (fun z θ => φ z * h z θ)
        ≤ 30 * (16 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h) := hle
      _ = 480 * Work.Spaces.WlInf α 4 (fun z _ => φ z) * Work.Spaces.WlInf α 4 h := by ring⟩

end Work.FTS.Nonlinear.N4Fields
