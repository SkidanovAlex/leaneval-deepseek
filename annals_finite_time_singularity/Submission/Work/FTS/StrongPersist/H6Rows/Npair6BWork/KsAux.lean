/-
# `KsAux` — the elementary calculus and bounds for the angular moment of `F_*`

The statement `ksDat` (`Submission/Work/FTS/StrongPersist/H6Rows/Npair6BWork/ksDat.lean`)
concerns the two explicit functions

  `KsFun α  = fun z _ => α · 2z/(1+z)²`   (= `FK (Fstar α)`, the angular moment of `F_*`)
  `KsTor α  = fun z θ => sin²θ · KsFun α z θ`

on the open quadrant, together with their `D`-derivatives.  This module collects the
calculus and the explicit pointwise bounds that the four conjuncts of `ksDat` need:

* the identification of the two functions with `FK (Fstar α)` and `sin²θ · FK (Fstar α)`
  (`KsFun_eq_FK`, `KsTor_eq_FK`, from `FstarPkg.FK_Fstar`);
* factors which do not depend on `z` (resp. on `θ`) pass through `pz`/`DzIter`/`DthIter`
  (`pzIter_const_mul`, `DzIter_const_mul_apply`, `DthIter_sep_apply`, …);
* the closed-form bounds on the radial derivatives of `KsFun`, in the two shapes needed:
  `|(z+1)^k ∂_z^k Ks| ≤ 2α·k!(k+1)` (the `𝒲^{6,∞}`-slots) and
  `|z^k ∂_z^k Ks| ≤ 2·5040·α·z/(1+z)` together with the Stirling expansion
  `|D_z^j Ks| ≤ 2·5040·203·α·z/(1+z)` (the pointwise `D_z`-slots);
* the vanishing of the angular derivatives of the radial function (`DthIter_KsFun_eq_zero`),
  the `θ`-factorisation of the `D_θ`-iterates of `KsTor` (`DthIter_KsTor`,
  `pzIter_DthIter_KsTor`), and the weighted endpoint bound for `D_θ^j(sin²)`
  (`dthU_sinSq_weighted`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.HkAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-! ## §1 The two functions and their identification with the angular moment -/

/-- The angular moment `FK (Fstar α)` of the fundamental profile, written out:
`z ↦ α · 2z/(1+z)²`, constant in `θ`. -/
def KsFun (α : ℝ) : ℝ → ℝ → ℝ := fun z _ => α * (2 * z / (1 + z) ^ 2)

/-- `sin²θ · FK (Fstar α)`. -/
def KsTor (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * KsFun α z θ

/-- `KsFun α` is `z ↦ FK (Fstar α) z` (`FstarPkg.FK_Fstar`). -/
theorem KsFun_eq_FK {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    KsFun α = fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z := by
  funext z θ
  simp only [KsFun]
  rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]

/-- `KsTor α` is `(z,θ) ↦ sin²θ · FK (Fstar α) z`. -/
theorem KsTor_eq_FK {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    KsTor α = fun z θ => Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z := by
  funext z θ
  simp only [KsTor, KsFun]
  rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]

/-! ## §2 Factors which are constant in one variable -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field (c θ)

/-- A factor which does not depend on `z` passes through `∂_z^j`. -/
theorem pzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
      have heq : Work.Spaces.pzIter j (fun z θ => c θ * K z θ)
          = fun z θ => c θ * Work.Spaces.pzIter j K z θ :=
        funext fun z => funext fun θ => ih z θ
      rw [heq, pz_const_mul]

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem DzIter_const_mul_apply (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
      have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
          = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
        funext fun z => funext fun θ => ih z θ
      rw [heq]
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field (c θ) (v := fun z' => Work.Spaces.DzIter j K z' θ)]
      ring

/-- The `θ`-factor passes through the `D_θ`-iterates of a product of a `θ`-only and a
`z`-only factor. -/
theorem DthIter_sep_apply (a : ℝ → ℝ) (K : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (fun z θ => a θ * K z) z θ = Work.Spaces.dthU^[j] a θ * K z := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ]
      have heq : Work.Spaces.DthIter j (fun z θ => a θ * K z)
          = fun z θ => Work.Spaces.dthU^[j] a θ * K z :=
        funext fun z => funext fun θ => ih z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq]
      rw [deriv_mul_const_field (K z) (u := Work.Spaces.dthU^[j] a)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.dthU]
      ring

/-! ## §3 The radial derivatives of `KsFun` -/

/-- `∂_z^k` of a constant multiple of `hKer = z/(1+z)²`. -/
theorem pzIter_zOnly_mul (c : ℝ) (K : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z (_ : ℝ) => c * K z) = fun z _ => c * deriv^[k] K z := by
  induction k with
  | zero => funext z θ; simp
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [deriv_const_mul_field c (v := deriv^[k] K), Function.iterate_succ_apply']

/-- `∂_z^k KsFun α = 2α · hKer^{(k)}`. -/
theorem pzIter_KsFun (α : ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (KsFun α) = fun z _ => α * 2 * deriv^[k] Work.Spaces.hKer z := by
  have h : KsFun α = fun z _ => (α * 2) * Work.Spaces.hKer z := by
    funext z θ
    simp only [KsFun, Work.Spaces.hKer_apply]
    ring
  rw [h, pzIter_zOnly_mul]

/-- The `𝒲^{6,∞}`-shape of the radial derivatives of `KsFun`:
`|(z+1)^k ∂_z^k Ks| ≤ 2α · k! · (k+1)` for `z ≥ 0`. -/
theorem ks_pz_bound (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) := by
  rw [pzIter_KsFun]
  have h := Work.Spaces.pzIter_hKer_bound k z hz
  have hEq : (z + 1) ^ k * (α * 2 * deriv^[k] Work.Spaces.hKer z)
      = (α * 2) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) := by ring
  rw [hEq, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ α * 2)]
  calc α * 2 * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ α * 2 * ((k.factorial : ℝ) * (k + 1)) := mul_le_mul_of_nonneg_left h (by linarith)
    _ = 2 * α * ((k.factorial : ℝ) * (k + 1)) := by ring

/-- The `z^k`-shape of the radial derivatives of `KsFun`:
`|z^k ∂_z^k Ks| ≤ 2α · k! · (k+1) · (z/(1+z))^k` for `z ≥ 0`. -/
theorem ks_zpow_pz_bound (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) :
    |z ^ k * Work.Spaces.pzIter k (KsFun α) z θ|
      ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k := by
  rw [pzIter_KsFun]
  have h := Work.Spaces.pzIter_hKer_bound k z hz
  have hz1 : (1 + z : ℝ) ≠ 0 := by positivity
  have hr : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hsplit : z ^ k = (z + 1) ^ k * (z / (1 + z)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  have hEq : z ^ k * (α * 2 * deriv^[k] Work.Spaces.hKer z)
      = (α * 2) * ((z / (1 + z)) ^ k * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)) := by
    rw [hsplit]; ring
  rw [hEq, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ α * 2), abs_mul,
    abs_of_nonneg (pow_nonneg hr k)]
  calc α * 2 * ((z / (1 + z)) ^ k * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|)
      ≤ α * 2 * ((z / (1 + z)) ^ k * ((k.factorial : ℝ) * (k + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (pow_nonneg hr k)) (by linarith)
    _ = 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k := by ring

/-- `k! · (k+1) ≤ 5040` for `k ≤ 6`. -/
theorem fact_mul_le_5040 (k : ℕ) (hk : k ≤ 6) : (k.factorial : ℝ) * (k + 1) ≤ 5040 := by
  interval_cases k <;> norm_num

/-- `r^k ≤ r` for `0 ≤ r ≤ 1` and `k ≥ 1`. -/
theorem pow_nat_le_self {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) {k : ℕ} (hk : 1 ≤ k) : r ^ k ≤ r := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  calc r ^ m * r ≤ 1 * r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr hr1) hr
    _ = r := one_mul r

/-- The uniform pointwise bound `|z^k ∂_z^k Ks| ≤ 2·5040·α·z/(1+z)` for `k ≤ 6`, `z ≥ 0`:
this is the shape consumed by the Stirling expansion of `D_z^j`. -/
theorem ks_zpow_pz_le (α : ℝ) (hα : 0 ≤ α) (k : ℕ) (hk : k ≤ 6) (z : ℝ) (hz : 0 ≤ z)
    (θ : ℝ) :
    |z ^ k * Work.Spaces.pzIter k (KsFun α) z θ| ≤ 2 * 5040 * α * (z / (1 + z)) := by
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hr : 0 ≤ z / (1 + z) := div_nonneg hz (le_of_lt hz1)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pzIter_KsFun]
    simp only [pow_zero, one_mul]
    have hid : (2 : ℝ) * z / (1 + z) ^ 2 = ((2 : ℝ) * (z / (1 + z))) / (1 + z) := by
      field_simp
    have hle : ((2 : ℝ) * (z / (1 + z))) / (1 + z) ≤ 2 * (z / (1 + z)) := by
      rw [div_le_iff₀ hz1]
      nlinarith [hr, hz, mul_nonneg hr hz]
    calc |α * 2 * deriv^[0] Work.Spaces.hKer z| = α * ((2 : ℝ) * z / (1 + z) ^ 2) := by
          rw [Function.iterate_zero, id_eq, Work.Spaces.hKer_apply]
          rw [abs_of_nonneg (by positivity)]
          ring
      _ = α * (((2 : ℝ) * (z / (1 + z))) / (1 + z)) := by rw [hid]
      _ ≤ α * (2 * (z / (1 + z))) := mul_le_mul_of_nonneg_left hle hα
      _ ≤ 2 * 5040 * α * (z / (1 + z)) := by
          have h : (0:ℝ) ≤ α * (z / (1 + z)) := mul_nonneg hα hr
          nlinarith [h]
  · have h1 := ks_zpow_pz_bound α hα k z hz θ
    have h2 := pow_nat_le_self hr ((div_le_one hz1).mpr (by linarith)) hkpos
    have h3 := fact_mul_le_5040 k hk
    have h5 : 2 * α * ((k.factorial : ℝ) * (k + 1)) * (z / (1 + z)) ^ k
        ≤ 2 * α * 5040 * (z / (1 + z)) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by linarith)) (pow_nonneg hr k)
    have h6 : 2 * α * 5040 * (z / (1 + z)) ^ k ≤ 2 * α * 5040 * (z / (1 + z)) :=
      mul_le_mul_of_nonneg_left h2 (by nlinarith)
    linarith [h1, h5, h6,
      show (2:ℝ) * 5040 * α * (z / (1 + z)) = 2 * α * 5040 * (z / (1 + z)) by ring]

/-- The Bell number of a row `n ≤ 6` is at most `203`. -/
theorem bell_le_203 (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 203 := by
  interval_cases n <;> decide

/-! ## §4 The pointwise bound for `D_z^j KsFun` -/

/-- The `z`-slices of `KsFun α` are analytic on `(-1,∞)`.  This is the smoothness
hypothesis of the Stirling expansion `Work.Spaces.DzIter_eq_sum_scoef`. -/
theorem analytic_zSlice_KsFun (α : ℝ) (θ : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => KsFun α z θ) (Set.Ioi (-1)) := by
  have hfun : (fun z : ℝ => KsFun α z θ) = fun z : ℝ => α * (2 * z / (1 + z) ^ 2) := by
    funext z; rfl
  rw [hfun]
  have hden : ∀ x : ℝ, x ∈ Set.Ioi (-1) → (1 + x) ^ 2 ≠ 0 := by
    intro x hx
    have h1 : (-1 : ℝ) < x := hx
    have h2 : (0 : ℝ) < 1 + x := by linarith
    positivity
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
    refine ContDiffOn.div ?_ ?_ hden
    · fun_prop
    · fun_prop
  have h2 := h.mul (contDiffOn_const (c := α) (s := Set.Ioi (-1)))
  have h3 : (fun x : ℝ => 2 * x / (1 + x) ^ 2 * α)
      = (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) := by
    funext p; ring
  rwa [h3] at h2

/-- **The pointwise `D_z`-bound for the radial function `KsFun α`**:
`|D_z^j Ks| ≤ 2·5040·203·α·z/(1+z)` for every `j ≤ 6`, `z ≥ 0`. -/
theorem ks_Dz_bound (α : ℝ) (hα : 0 ≤ α) (j : ℕ) (hj : j ≤ 6) (z : ℝ) (hz : 0 ≤ z) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DzIter j (KsFun α) z θ| ≤ 2 * 5040 * 203 * α * (z / (1 + z)) := by
  have hstir := Work.Spaces.DzIter_eq_sum_scoef (h := KsFun α)
    (fun θ _ => analytic_zSlice_KsFun α θ) j z
      (by simp only [Set.mem_Ioi]; linarith [hz]) θ hθ
  rw [hstir]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le j (2 * 5040 * α * (z / (1 + z)))
    (fun k => z ^ k * Work.Spaces.pzIter k (KsFun α) z θ)
    (fun k hk => ks_zpow_pz_le α hα k (le_trans hk hj) z hz θ)
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by exact_mod_cast bell_le_203 j hj
  have hM : 0 ≤ 2 * 5040 * α * (z / (1 + z)) := by
    have : 0 ≤ α * (z / (1 + z)) := mul_nonneg hα (div_nonneg hz (by linarith))
    nlinarith [this]
  calc |∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * Work.Spaces.pzIter k (KsFun α) z θ)|
      ≤ (Work.Spaces.bell j : ℝ) * (2 * 5040 * α * (z / (1 + z))) := hsum
    _ ≤ 203 * (2 * 5040 * α * (z / (1 + z))) := mul_le_mul_of_nonneg_right hbell hM
    _ = 2 * 5040 * 203 * α * (z / (1 + z)) := by ring

/-! ## §5 The angular derivatives -/

/-- A `D_θ`-iterate of a constant (for `j ≥ 1`) vanishes. -/
theorem dthU_iter_const_eq_zero (c : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] (fun _ : ℝ => c) = fun _ => 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  clear hj
  induction m with
  | zero =>
      funext θ
      show Real.sin (2 * θ) * deriv (fun _ : ℝ => c) θ = 0
      rw [deriv_const]
      ring
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_succ_apply', ih]
      funext θ
      show Real.sin (2 * θ) * deriv (fun _ : ℝ => (0:ℝ)) θ = 0
      rw [deriv_const]
      ring

/-- `KsFun α` is constant in `θ`, so all its `D_θ`-iterates of positive order vanish. -/
theorem DthIter_KsFun_eq_zero (α : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.DthIter j (KsFun α) = fun _ _ => 0 := by
  have hfun : KsFun α = fun z (_ : ℝ) => (1 : ℝ) * (fun z => KsFun α z 0) z := by
    funext z θ; simp [KsFun]
  rw [hfun]
  funext z θ
  rw [DthIter_sep_apply (a := fun _ : ℝ => (1 : ℝ)) (K := fun z => KsFun α z 0)]
  rw [dthU_iter_const_eq_zero (1 : ℝ) hj]
  simp

/-- The `D_θ`-iterates of `KsTor α` factor as `D_θ^j(sin²) · KsFun`. -/
theorem DthIter_KsTor (α : ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (KsTor α) z θ
      = Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ * KsFun α z θ := by
  have h : KsTor α = fun z θ => (fun t : ℝ => Real.sin t ^ 2) θ * (fun z => KsFun α z 0) z := by
    funext z θ; simp [KsTor, KsFun]
  rw [h, DthIter_sep_apply]
  simp only [KsFun]

/-- The mixed derivatives of `KsTor α` factor as `D_θ^j(sin²)(θ) · ∂_z^k KsFun α`. -/
theorem pzIter_DthIter_KsTor (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (KsTor α)) z θ
      = Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ
        * Work.Spaces.pzIter k (KsFun α) z θ := by
  have h : Work.Spaces.DthIter j (KsTor α)
      = fun z θ => (fun t : ℝ => Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) t) θ
          * KsFun α z θ := by
    funext z θ
    exact DthIter_KsTor α j z θ
  rw [h, pzIter_const_mul]

/-- The `∂_z^k`-iterates of `KsTor α` factor as `sin²θ · ∂_z^k KsFun`. -/
theorem pzIter_KsTor (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (KsTor α) z θ
      = Real.sin θ ^ 2 * Work.Spaces.pzIter k (KsFun α) z θ := by
  have h : KsTor α = fun z θ => (fun t : ℝ => Real.sin t ^ 2) θ * KsFun α z θ := rfl
  rw [h, pzIter_const_mul]

/-- The weighted endpoint bound for the `D_θ`-iterates of `sin²` (from
`Npair6SupAux.dthU_sinSq_weight`), in the form used by the pointwise estimates:
on the *open* angular interval,
`|D_θ^j(sin²)(θ)| ≤ C · (α + sin 2θ) · sin(2θ)^{α/5}`. -/
theorem dthU_sinSq_weighted : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ j : ℕ, 1 ≤ j → j ≤ 6 →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        ≤ C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight
  refine ⟨C, hCpos, fun α hαI j hj1 hj6 θ hθ => ?_⟩
  obtain ⟨hα, hα1⟩ := hαI
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hb := hC α hα hα1 j hj1 hj6 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfac : 0 < (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_pos hden (Real.rpow_pos_of_pos hs _)
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt hfac)
  have hid : |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by
    have h1 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    have h2 : (α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hden)
    rw [div_eq_mul_inv]
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) * (α + Real.sin (2 * θ))⁻¹
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
          * ((α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ))) := by ring
      _ = |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ| := by rw [h1, h2]; ring
  rw [hid] at hmul
  calc |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      ≤ C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hmul
    _ = C * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := rfl

/-! ## §6 Smoothness on the open quadrant -/

/-- `KsFun α` is `C^∞` on the open quadrant. -/
theorem SmoothOpen_KsFun (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (KsFun α) := by
  have hfun : Function.uncurry (KsFun α)
      = fun p : ℝ × ℝ => α * (2 * p.1 / (1 + p.1) ^ 2) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  have hden : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    positivity
  have h : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div ?_ ?_ hden
    · fun_prop
    · fun_prop
  have h2 := h.mul (contDiffOn_const (c := α) (s := Work.FTS.EllipticEst.Q0))
  refine h2.congr (fun p hp => ?_)
  simp only [div_eq_mul_inv]
  ring

/-- `sin²θ · KsFun α` is `C^∞` on the open quadrant. -/
theorem SmoothOpen_KsTor (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (KsTor α) := by
  have hun : Function.uncurry (KsTor α)
      = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * (α * (2 * p.1 / (1 + p.1) ^ 2)) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hun]
  have hden : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    positivity
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 := by
    fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (2 * p.1 / (1 + p.1) ^ 2)) Work.FTS.EllipticEst.Q0 := by
    have hdiv : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div ?_ ?_ hden
      · fun_prop
      · fun_prop
    have hmul := hdiv.mul (contDiffOn_const (c := α) (s := Work.FTS.EllipticEst.Q0))
    refine hmul.congr (fun p hp => ?_)
    simp only [div_eq_mul_inv]
    ring
  exact (h1.mul h2).congr (fun p hp => rfl)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
