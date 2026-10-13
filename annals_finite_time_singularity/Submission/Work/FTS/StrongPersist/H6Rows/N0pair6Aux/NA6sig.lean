import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.c2m_L12Fstar_W6
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

-- The σ-decay hypothesis of `RowAdz`, verified for the actual coefficient
-- `A = c₂ₘ(θ)·L₁₂(F_*)(z)` of the `N₀`-row (this is `H6Pair6Aux.NA6 α` up to unfolding).
--
-- ROUTE.  `L₁₂(F_*) = 2α/(1+z)` on `(-1,∞)` (`Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH`),
-- so `A = c₂ₘ(θ)·(2α/(1+z))` up to that equality, and the function is separable:
-- `D_θ^i A = c₂ₘ^{(i)}(θ)·(2α/(1+z))` and `mixed j i A = D_z^j(D_θ^i A)
--  = c₂ₘ^{(i)}(θ)·(D_z^j(2α/(1+z)))`.
--   * Angular (`1 ≤ i ≤ 6`): `|D_θ^i c₂ₘ| ≤ 100000·sin(2θ)²` by
--     `Work.FTS.StrongPersist.dthU_c2m_bound6` (with `DthIter i c₂ₘ = dthU^[i] c₂ₘ`).
--   * Radial: `|(z+1)^k·pzIter k (c₂ₘ(θ)·2α/(1+z))| ≤ 4α k!` for `z ≥ 0`
--     (`Work.FTS.StrongPersist.c2mSix_inv_points`), so `|pzIter k (2α/(1+z))| ≤ 4α k!`;
--     `DzIter j` is a finite combination of `z^k ∂_z^k` (`DzIter_eq_sum_scoef_of_contDiffOn`,
--     or an induction from `Spaces.Dz`), and `z^k/(1+z)^k ≤ 1`.
--   * `i = 0`: `|mixed j 0 A| = |c₂ₘ θ|·|DzIter j L₁₂| ≤ 2·Cα` (using `FstarPkg.abs_c2m_le_two`).
--   * `i ≥ 1`: `|mixed j i A| ≤ 100000·sin(2θ)²·Cα ≤ Cα·sin(2θ)` since `sin(2θ) ≤ 1`.
--
-- IMPLEMENTATION.  The separability is formalised as the pointwise identity
-- `mixed_eq` below: for `z > 0`, `θ ∈ Iθ`,
-- `mixed j i A z θ = (dthU^[i] c2m θ) · ∑_{k≤j} S(j,k) z^k (L₁₂(F_*))^{(k)}(z)`,
-- obtained from `DthIter_decomp` (angular separation), the Stirling expansion of
-- `D_z^j` (`Spaces.DzIter_eq_sum_scoef`, which needs the `z`-slices to be `C^∞` on
-- `(-1,∞)` — supplied by transporting `eqOn_L12_invH` through `ContDiffOn.congr`)
-- and the radial separation `Spaces.pzIter_decomp`.  The radial sum is bounded by
-- `1440000·α` in `radial_sum_bound`, using `deriv_iter_eqOn` + `c2mInv_radial`
-- (`|(z+1)^k (2α/(1+z))^{(k)}| ≤ 2α k!`), `z^k ≤ (z+1)^k`, `k! ≤ 720` and the
-- Bell-number bound `bell j ≤ 1000` for `j ≤ 6`.
private lemma bell_le_thousand (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-- `z ↦ 2α/(1+z)` is `C^∞` on `(-1,∞)`. -/
private lemma contDiffOn_invH (α : ℝ) :
    ContDiffOn ℝ ⊤ (Work.FTS.Nonlinear.FstarPkg.invH α) (Set.Ioi (-1)) := by
  have h : Work.FTS.Nonlinear.FstarPkg.invH α = fun z : ℝ => (2 * α) * (1 + z)⁻¹ := by
    funext z; rw [Work.FTS.Nonlinear.FstarPkg.invH_apply, div_eq_mul_inv]
  rw [h]
  refine ContDiffOn.mul (contDiffOn_const (c := 2 * α) (s := Set.Ioi (-1)) (n := ⊤)) ?_
  refine ContDiffOn.inv ?_ ?_
  · simpa using (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := ⊤)).add
      (contDiffOn_id (s := Set.Ioi (-1)) (n := ⊤))
  · intro x hx
    have hx' : (-1 : ℝ) < x := hx
    exact ne_of_gt (by linarith)

/-- `z ↦ L₁₂(F_*)(z)` is `C^∞` on `(-1,∞)` (it agrees there with `2α/(1+z)`). -/
private lemma contDiffOn_L12Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ ⊤
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi (-1)) :=
  (contDiffOn_invH α).congr
    (fun z hz => Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz)

/-- For a radial function, `pzIter` is the plain iterate of `deriv`. -/
private lemma pzIter_radial (B : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => B z) z θ = deriv^[k] B z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ]
    simp only [Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter k (fun z _ => B z) z' θ)
          = fun z' => deriv^[k] B z' from by
      funext z'; exact ih z']
    exact congrFun (Function.iterate_succ_apply' deriv k B).symm z

/-- The Stirling-weighted `z`-jet of `L₁₂(F_*)` is `O(α)` at order `≤ 6`. -/
private lemma radial_sum_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
          * (z ^ k * deriv^[k]
              (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
        ≤ 1440000 * α := by
  intro j hj z hz
  have hz0 : (0 : ℝ) < z := hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hterm : ∀ k ≤ j,
      |z ^ k * deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
        ≤ 2 * α * 720 := by
    intro k hk
    have hk6 : k ≤ 6 := le_trans hk hj
    have hkB : deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
        = deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z :=
      Work.FTS.Nonlinear.FstarPkg.deriv_iter_eqOn
        (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1) k hz1
    rw [hkB]
    have h := Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z (le_of_lt hz)
    have hfact : (k.factorial : ℝ) ≤ 720 := by
      interval_cases k <;> norm_num
    calc |z ^ k * deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z|
        = z ^ k * |deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hz) k)]
      _ ≤ (z + 1) ^ k * |deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) k
      _ = |(z + 1) ^ k * deriv^[k] (Work.FTS.Nonlinear.FstarPkg.invH α) z| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
      _ ≤ 2 * α * (k.factorial : ℝ) := h
      _ ≤ 2 * α * 720 := by nlinarith [hα]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le j (2 * α * 720)
    (fun k => z ^ k * deriv^[k]
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z) hterm
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 1000 := by exact_mod_cast bell_le_thousand j hj
  calc |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
        * (z ^ k * deriv^[k] (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
      ≤ (Work.Spaces.bell j : ℝ) * (2 * α * 720) := hsum
    _ ≤ 1000 * (2 * α * 720) := mul_le_mul_of_nonneg_right hbell (by positivity)
    _ = 1440000 * α := by ring

/-- **Separation of variables for the `N₀`-coefficient.**  For `z > 0`, `θ ∈ Iθ`,
`mixed j i A z θ = (dthU^[i] c2m θ) · ∑_{k≤j} S(j,k) z^k (∂_z^k L₁₂(F_*))(z)`. -/
private lemma mixed_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (j i : ℕ) (z θ : ℝ) (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed j i (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
            * (z ^ k * deriv^[k]
                (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z) := by
  have hB := contDiffOn_L12Fstar α hα hα1
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    simp only [Set.mem_Ioi] at hz ⊢; linarith
  have hsmooth : ∀ θ' ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z' => (Work.Spaces.dthU^[i] Work.Construction.c2m) θ'
        * Work.Construction.L12 (Work.Construction.Fstar α) z') (Set.Ioi (-1)) :=
    fun θ' _ => (contDiffOn_const (c := (Work.Spaces.dthU^[i] Work.Construction.c2m) θ')
      (s := Set.Ioi (-1)) (n := ⊤)).mul hB
  have hDth : Work.Spaces.DthIter i (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z)
      = fun z θ => (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp i Work.Construction.c2m
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
  rw [Work.Spaces.mixed, hDth,
    Work.Spaces.DzIter_eq_sum_scoef hsmooth j z hz1 θ hθ]
  have hpt : ∀ k ∈ Finset.range (j + 1),
      (Work.Spaces.scoef j k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k (fun z θ =>
              (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
                * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ)
      = (Work.Spaces.dthU^[i] Work.Construction.c2m) θ
        * ((Work.Spaces.scoef j k : ℝ)
            * (z ^ k * deriv^[k]
                (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)) := by
    intro k hk
    rw [Work.Spaces.pzIter_decomp k (Work.Spaces.dthU^[i] Work.Construction.c2m)
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z θ]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.mul_sum]

theorem NA6sig : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i
          (fun z θ => Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z) z θ|
        ≤ C * α * (if i = 0 then 1 else Real.sin (2 * θ)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨max (2 * 1440000) (C0 * 1440000) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ max (2 * 1440000) (C0 * 1440000) :=
      le_max_of_le_left (by norm_num)
    linarith
  · intro α hαmem z θ hz hθ0 hθ1 j i hij
    obtain ⟨hαpos, hαle⟩ := hαmem
    have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) := by
      apply Real.sin_nonneg_of_mem_Icc
      rw [Set.mem_Icc]
      constructor <;> linarith [hθ0, hθ1, Real.pi_pos]
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hji : j ≤ 6 := by omega
    have hii : i ≤ 6 := by omega
    rw [mixed_eq α hαpos hαle j i z θ hzI hθI, abs_mul]
    have hsum := radial_sum_bound α hαpos hαle j hji z hzI
    by_cases hi0 : i = 0
    · rw [if_pos hi0, mul_one]
      have hC : |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ| ≤ 2 := by
        rw [hi0]
        simpa using Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two θ
      calc |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
            * |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
                * (z ^ k * deriv^[k]
                    (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
          ≤ 2 * (1440000 * α) := mul_le_mul hC hsum (abs_nonneg _) (by norm_num)
        _ = 2880000 * α := by ring
        _ ≤ (max (2 * 1440000) (C0 * 1440000) + 1) * α := by
            have h2 : (2880000 : ℝ) ≤ max (2 * 1440000) (C0 * 1440000) + 1 := by
              have := le_max_left (2 * 1440000) (C0 * 1440000); linarith
            nlinarith [hαpos]
    · rw [if_neg hi0]
      have hi1 : 1 ≤ i := by omega
      have hC : |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
          ≤ C0 * (Real.sin (2 * θ)) ^ 2 := hC0 i hi1 hii θ
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ Real.sin (2 * θ) := by
        nlinarith [hsin0, hsin1]
      have hcoe : C0 * 1440000 ≤ max (2 * 1440000) (C0 * 1440000) + 1 := by
        have := le_max_right (2 * 1440000) (C0 * 1440000); linarith
      have hnn : (0 : ℝ) ≤ C0 * 1440000 * α :=
        mul_nonneg (mul_nonneg hC0pos.le (by norm_num)) hαpos.le
      calc |(Work.Spaces.dthU^[i] Work.Construction.c2m) θ|
            * |∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ)
                * (z ^ k * deriv^[k]
                    (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z)|
          ≤ (C0 * (Real.sin (2 * θ)) ^ 2) * (1440000 * α) :=
            mul_le_mul hC hsum (abs_nonneg _) (by positivity)
        _ = C0 * 1440000 * α * (Real.sin (2 * θ)) ^ 2 := by ring
        _ ≤ C0 * 1440000 * α * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left hs2 hnn
        _ ≤ (max (2 * 1440000) (C0 * 1440000) + 1) * α * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoe hαpos.le) hsin0

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
