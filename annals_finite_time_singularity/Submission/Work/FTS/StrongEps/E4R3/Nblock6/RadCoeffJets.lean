import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.StrongEps.H5.hKerConstWlInf_l

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6

open scoped ContDiff Topology
open Set Filter

/-! ## Auxiliary calculus lemmas for the two radial profiles

We prove the pointwise bounds on the `∂_z^k`-derivatives of the two profiles
`z ↦ c·(1+z)⁻¹` and `z ↦ c·hKer z = c·z/(1+z)²` on `[0,∞)`, and then pass to the
iterated `D_z = z∂_z` by the Stirling expansion `D_z^j = ∑_{k≤j} S(j,k) z^k ∂_z^k`
(`Work.Spaces.DzIter_eq_sum_scoef`) together with the coefficient-mass bound
`Work.Spaces.abs_sum_scoef_mul_le`. -/

/-- `∂_z^k` commutes with multiplication by a constant. -/
private theorem deriv_iterate_const_mul (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    deriv^[k] (fun z => c * f z) = fun z => c * deriv^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply' deriv k (fun z => c * f z), ih]
    funext z
    rw [congrFun (Function.iterate_succ_apply' deriv k f) z]
    exact deriv_const_mul_field (v := deriv^[k] f) c

/-- The Bell number of a row `j ≤ 6` is at most `203` (`bell 6 = 203`). -/
private lemma bell_le_203 {j : ℕ} (hj : j ≤ 6) : Work.Spaces.bell j ≤ 203 := by
  interval_cases j <;> decide

/-- `k! ≤ 5040` for `k ≤ 6`. -/
private lemma factorial_le_5040 {k : ℕ} (hk : k ≤ 6) : (k.factorial : ℝ) ≤ 5040 := by
  have h1 : k.factorial ≤ Nat.factorial 6 := Nat.factorial_le hk
  calc (k.factorial : ℝ) ≤ (Nat.factorial 6 : ℝ) := by exact_mod_cast h1
    _ = 720 := by norm_num
    _ ≤ 5040 := by norm_num

/-- `k!·(k+1) ≤ 5040` for `k ≤ 6` (`6!·7 = 5040`). -/
private lemma factorial_mul_succ_le_5040 {k : ℕ} (hk : k ≤ 6) :
    (k.factorial : ℝ) * (k + 1) ≤ 5040 := by
  have h1 : (k.factorial : ℝ) ≤ 720 := by
    have h := Nat.factorial_le hk
    calc (k.factorial : ℝ) ≤ (Nat.factorial 6 : ℝ) := by exact_mod_cast h
      _ = 720 := by norm_num
  have h2 : (k : ℝ) + 1 ≤ 7 := by
    have hk' : k + 1 ≤ 7 := by omega
    exact_mod_cast hk'
  calc (k.factorial : ℝ) * (k + 1) ≤ 720 * 7 :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = 5040 := by norm_num

/-! ### The profile `z ↦ (1+z)⁻¹` -/

/-- The closed form `(-1)^k k! (1+z)^{-(k+1)}` of the `k`-th derivative of `z ↦ (1+z)⁻¹`. -/
private noncomputable def invClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((1 + z)⁻¹) ^ (k + 1)

private lemma hasDerivAt_invClosed (k : ℕ) {z : ℝ} (hz : (1 + z) ≠ 0) :
    HasDerivAt (invClosed k) (invClosed (k + 1) z) z := by
  have hbase : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv := hh.inv hz
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have hp := hbase.pow (k + 1)
  have hc := hp.const_mul ((-1 : ℝ) ^ k * (k.factorial : ℝ))
  have hfun : (fun y => ((-1 : ℝ) ^ k * (k.factorial : ℝ))
        * ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 1)) y) = invClosed k := by
    funext y; simp only [Pi.pow_apply, invClosed]
  have hval : ((-1 : ℝ) ^ k * (k.factorial : ℝ))
        * ((↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ (k + 1 - 1) * (-((1 + z)⁻¹) ^ 2))
      = invClosed (k + 1) z := by
    have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
    have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [show k + 1 - 1 = k by omega]
    simp only [invClosed]
    rw [hsign, hfact, pow_add, pow_add, pow_one]
    ring
  rw [hfun, hval] at hc
  exact hc

private theorem iter_deriv_inv (k : ℕ) {z : ℝ} (hz : -1 < z) :
    deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z = invClosed k z := by
  induction k generalizing z with
  | zero => simp [invClosed]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hev : deriv^[k] (fun w : ℝ => (1 + w)⁻¹) =ᶠ[𝓝 z] invClosed k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_invClosed k (by intro h; linarith)).deriv

/-- The weighted derivative bound for `z ↦ (1+z)⁻¹`: `|z^k ∂_z^k (1+z)⁻¹| ≤ k!` for `z ≥ 0`. -/
private lemma inv_deriv_bound (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z| ≤ (k.factorial : ℝ) := by
  rw [iter_deriv_inv k (by linarith : -1 < z)]
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hb1 : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hb2 : z / (1 + z) ≤ 1 := (div_le_one hz1).mpr (by linarith)
  have hc1 : 0 ≤ (1 + z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hc2 : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hprod : |(z / (1 + z)) ^ k * (1 + z)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hb1 k) hc1)]
    calc (z / (1 + z)) ^ k * (1 + z)⁻¹ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hb1 hb2) hc2 hc1 (by norm_num)
      _ = 1 := by ring
  have hrew : z ^ k * invClosed k z
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((z / (1 + z)) ^ k * (1 + z)⁻¹) := by
    simp only [invClosed]
    rw [div_eq_mul_inv, mul_pow, pow_succ]
    ring
  rw [hrew, abs_mul, abs_mul]
  have h1 : |(-1 : ℝ) ^ k| = 1 := by rw [abs_pow]; norm_num
  rw [h1, one_mul, abs_of_nonneg (Nat.cast_nonneg k.factorial)]
  exact mul_le_of_le_one_right (Nat.cast_nonneg k.factorial) hprod

/-- The weighted derivative bound for `z ↦ c·(1+z)⁻¹`: `|z^k ∂_z^k| ≤ k!·|c|` for `z ≥ 0`. -/
private lemma inv_const_deriv_bound (c : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => c * (1 + w)⁻¹) z| ≤ (k.factorial : ℝ) * |c| := by
  rw [congrFun (deriv_iterate_const_mul c (fun w : ℝ => (1 + w)⁻¹) k) z]
  rw [show z ^ k * (c * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z)
      = c * (z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z) by ring]
  rw [abs_mul]
  calc |c| * |z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z|
      ≤ |c| * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left (inv_deriv_bound k hz) (abs_nonneg c)
    _ = (k.factorial : ℝ) * |c| := by ring

/-- Analytic smoothness of `z ↦ c·(1+z)⁻¹` on the set where `1+z ≠ 0`. -/
private lemma contDiffOn_inv_const (c : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => c * (1 + z)⁻¹) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by
    simpa [add_comm] using
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).add
        (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1)))
  have h2 := h1.inv (fun x hx => ne_of_gt (by simp only [Set.mem_Ioi] at hx; linarith))
  simpa using (contDiffOn_const (c := c) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).mul h2

/-! ### The profile `z ↦ c·hKer z = c·z/(1+z)²` -/

/-- The weighted derivative bound for `hKer`: `|z^k ∂_z^k hKer z| ≤ k!·(k+1)` for `z ≥ 0`
(this is `Work.Spaces.pzIter_hKer_bound` with the factor `(1+z)^k` traded for `z^k ≥ 0`). -/
private lemma hKer_deriv_bound (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) := by
  have hkey : |(1 + z) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) := by
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact Work.Spaces.pzIter_hKer_bound k z hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  have hb1 : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hb2 : z / (1 + z) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < 1 + z)).mpr (by linarith)
  have hrew : z ^ k * deriv^[k] Work.Spaces.hKer z
      = (z / (1 + z)) ^ k * ((1 + z) ^ k * deriv^[k] Work.Spaces.hKer z) := by
    rw [← mul_assoc, ← mul_pow, div_mul_cancel₀ z hz1]
  rw [hrew, abs_mul, abs_of_nonneg (pow_nonneg hb1 k)]
  calc (z / (1 + z)) ^ k * |(1 + z) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ 1 * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul (pow_le_one₀ hb1 hb2) hkey (abs_nonneg _) (by norm_num)
    _ = (k.factorial : ℝ) * (k + 1) := by ring

/-- The weighted derivative bound for `z ↦ c·hKer z`: `|z^k ∂_z^k| ≤ k!·(k+1)·|c|`. -/
private lemma hKer_const_deriv_bound (c : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => c * Work.Spaces.hKer w) z|
      ≤ (k.factorial : ℝ) * (k + 1) * |c| := by
  rw [congrFun (deriv_iterate_const_mul c Work.Spaces.hKer k) z]
  rw [show z ^ k * (c * deriv^[k] Work.Spaces.hKer z)
      = c * (z ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
  rw [abs_mul]
  calc |c| * |z ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ |c| * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul_of_nonneg_left (hKer_deriv_bound k hz) (abs_nonneg c)
    _ = (k.factorial : ℝ) * (k + 1) * |c| := by ring

/-- Analytic smoothness of `hKer = z/(1+z)²` on the set where `1+z ≠ 0`. -/
private lemma contDiffOn_hKer_Ioi :
    ContDiffOn ℝ (⊤ : ℕ∞ω) Work.Spaces.hKer (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by
    simpa [add_comm] using
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).add
        (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1)))
  exact (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1))).div (h1.pow 2)
    (fun x hx => by
      have hx' : (0 : ℝ) < 1 + x := by simp only [Set.mem_Ioi] at hx; linarith
      positivity)

/-- Analytic smoothness of `z ↦ c·hKer z` on `(-1,∞)`. -/
private lemma contDiffOn_hKer_const (c : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => c * Work.Spaces.hKer z) (Set.Ioi (-1)) := by
  simpa using
    (contDiffOn_const (c := c) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).mul contDiffOn_hKer_Ioi

/-! ### From `∂_z^k`-bounds to `D_z^j`-bounds -/

/-- **The Stirling passage.**  If the `z`-slices of `u` are analytic on `(-1,∞)` and
`|z^k ∂_z^k u z| ≤ M` on `[0,∞)` for every `k ≤ 6`, then `|D_z^j u z| ≤ bell j · M` for
`j ≤ 6` and `z > 0` (via `Work.Elliptic.DzIter_rad`, `Work.Spaces.DzIter_eq_sum_scoef` and
the coefficient-mass bound `Work.Spaces.abs_sum_scoef_mul_le`). -/
private theorem abs_DzdIter_le {u : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞ω) u (Set.Ioi (-1)))
    (hbound : ∀ k ≤ 6, ∀ z : ℝ, 0 ≤ z → |z ^ k * deriv^[k] u z| ≤ M)
    (j : ℕ) (hj : j ≤ 6) :
    ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j u z| ≤ (Work.Spaces.bell j : ℝ) * M := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  have hzIoi : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_refl 0, by positivity⟩
  rw [(Work.Elliptic.DzIter_rad u j z 0).symm]
  rw [Work.Spaces.DzIter_eq_sum_scoef (h := fun w _ : ℝ => u w)
    (fun θ _ => by simpa using hsmooth) j z hzIoi 0 h0I]
  have hterm : ∀ k : ℕ,
      z ^ k * Work.Spaces.pzIter k (fun w _ : ℝ => u w) z 0 = z ^ k * deriv^[k] u z := by
    intro k
    have hfun : (fun w _ : ℝ => u w) = (fun w θ : ℝ => (1 : ℝ) * u w) := by
      funext w θ; simp
    rw [hfun, Work.Spaces.pzIter_decomp k (fun _ : ℝ => (1 : ℝ)) u z 0, one_mul]
  have hcongr : (∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * Work.Spaces.pzIter k (fun w _ : ℝ => u w) z 0))
      = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) * (z ^ k * deriv^[k] u z) :=
    Finset.sum_congr rfl fun k _ => by rw [hterm k]
  rw [hcongr]
  exact Work.Spaces.abs_sum_scoef_mul_le j M (fun k => z ^ k * deriv^[k] u z)
    (fun k hk => hbound k (le_trans hk hj) z hz0)

/-- **Pointwise `D_z`-jet bounds for the two radial coefficients `c/(1+z)` and `c·hKer z`**
(namespace `Work.FTS.StrongEps.E4R3.Nblock6`), for orders `j ≤ 6`, with a constant relative to
`|c|` and the smoothness on `(0,∞)`.

Both profiles are rational with their only pole at `z = -1`, and every `D_z`-iterate is bounded
on `(0,∞)` by a multiple of `|c|`: for `r(z) = 1/(1+z)` one has
`z^k ∂_z^k r z = (-1)^k k! z^k/(1+z)^{k+1}` and `0 ≤ z/(1+z) ≤ 1`; for `hKer` use
`Work.Spaces.pzIter_hKer_bound` (`|(z+1)^k ∂_z^k hKer z| ≤ k!·(k+1)`).  The passage from
`∂_z^k`-bounds to `D_z^j`-bounds is `Work.Elliptic.DzdIter j r z = Σ_{k≤j} scoef j k · z^k ∂_z^k r z`
(the 1-D form of `Work.Spaces.DzIter_eq_sum_scoef`, via `Work.Spaces.DzIter_rad`) followed by the
triangle inequality, as in `Work.Spaces.DzIter_le_of_pzIter`. -/
theorem RadCoeffJets : ∃ C : ℝ, 0 < C ∧
    (∀ (c : ℝ) (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => c / (1 + z)) z| ≤ C * |c|) ∧
    (∀ (c : ℝ), ContDiffOn ℝ 6 (fun z => c / (1 + z)) (Set.Ioi 0)) ∧
    (∀ (c : ℝ) (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => c * Work.Spaces.hKer z) z| ≤ C * |c|) ∧
    (∀ (c : ℝ), ContDiffOn ℝ 6 (fun z => c * Work.Spaces.hKer z) (Set.Ioi 0)) := by
  refine ⟨2000000, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- `j ≤ 6`-jet bound for `c/(1+z)`
    intro c j hj z hz
    have hfun : (fun w : ℝ => c / (1 + w)) = fun w => c * (1 + w)⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [hfun]
    have h := abs_DzdIter_le (u := fun w : ℝ => c * (1 + w)⁻¹) (M := 5040 * |c|)
      (contDiffOn_inv_const c)
      (fun k hk z hz' => le_trans (inv_const_deriv_bound c k hz')
        (mul_le_mul_of_nonneg_right (factorial_le_5040 hk) (abs_nonneg c)))
      j hj z hz
    refine le_trans h ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by
      exact_mod_cast bell_le_203 hj
    have h1 : (Work.Spaces.bell j : ℝ) * (5040 * |c|) ≤ 203 * (5040 * |c|) :=
      mul_le_mul_of_nonneg_right hbell (by positivity)
    have h2 : (203 : ℝ) * (5040 * |c|) ≤ 2000000 * |c| := by
      nlinarith [abs_nonneg c]
    linarith
  · -- smoothness of `c/(1+z)` on `(0,∞)`
    intro c
    have h : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun w : ℝ => c / (1 + w)) (Set.Ioi (-1)) := by
      simpa only [div_eq_mul_inv] using contDiffOn_inv_const c
    exact (h.mono (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)).of_le le_top
  · -- `j ≤ 6`-jet bound for `c·hKer`
    intro c j hj z hz
    have h := abs_DzdIter_le (u := fun w : ℝ => c * Work.Spaces.hKer w) (M := 5040 * |c|)
      (contDiffOn_hKer_const c)
      (fun k hk z hz' => le_trans (hKer_const_deriv_bound c k hz')
        (by
          rw [show (k.factorial : ℝ) * (k + 1) * |c| = ((k.factorial : ℝ) * (k + 1)) * |c| by ring]
          exact mul_le_mul_of_nonneg_right (factorial_mul_succ_le_5040 hk) (abs_nonneg c)))
      j hj z hz
    refine le_trans h ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by
      exact_mod_cast bell_le_203 hj
    have h1 : (Work.Spaces.bell j : ℝ) * (5040 * |c|) ≤ 203 * (5040 * |c|) :=
      mul_le_mul_of_nonneg_right hbell (by positivity)
    have h2 : (203 : ℝ) * (5040 * |c|) ≤ 2000000 * |c| := by
      nlinarith [abs_nonneg c]
    linarith
  · -- smoothness of `c·hKer` on `(0,∞)`
    intro c
    exact ((contDiffOn_hKer_const c).mono
      (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)).of_le le_top

end Work.FTS.StrongEps.E4R3.Nblock6
