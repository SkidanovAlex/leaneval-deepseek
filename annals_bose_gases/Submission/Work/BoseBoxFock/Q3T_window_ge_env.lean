import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBoxFock.GrowthEnv
import Submission.Work.BoseBoxFock.exists_abs_bound_double
import Submission.Work.BoseBoxFock.qw_Q3T_window_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Q3T_window_ge_env` — the `ρ`-uniform window bound for the cubic word

FS `eq:kroelleQ3z`'s cubic word in the corrected `ã_s`-slot form `T.Q3T E` is bounded
below on FS's window `1_{[0,𝓜]}(n₊)` by a *single* constant times the growth envelope
`genv ρ = 1 + √ρ·ρ`, uniformly in the condensate density `ρ`.

## Why this is true, and why it is not a restatement of `qw_Q3T_window_ge`

`Q3T` depends on the environment `E` only through `E.z`, `E.ell`, `E.fL`, `E.W1` and
`F.PHset E`; the re-pointing `KzEnvAt E ρ` (`{E with z := √(ρℓ³), A := …, B := …}`)
therefore changes `Q3T` **only through the scalar** `z/ℓ³ = √(ρℓ³)/ℓ³`:

  `T.Q3T (KzEnvAt E ρ) = (√(ρℓ³)/ℓ³) • Q`, `Q = Σ_{s∈excited} Σ_{k∈PH} (f_L(s)Ŵ₁(k)) •
      (ã_s†a_{s−k}a_k + h.c.)`

with `Q` completely `ρ`-independent.  So a **two-sided** bound `|⟨g,Qg⟩| ≤ D‖g‖²`
(`D` independent of `ρ`, from the finite sum over modes of the single-pair bound) converts
into the `ρ`-uniform one-sided bound

  `⟨g, (Q3T (KzEnvAt E ρ))g⟩ ≥ -|√(ρℓ³)/ℓ³|·D·‖g‖² ≥ -(|D|(√|ℓ³|)⁻¹·genv ρ)·‖g‖²`,

the last step being `|√(ρL)/L| ≤ (√|L|)⁻¹√ρ` for `ρ ≥ 0` and `√ρ ≤ genv ρ`.  This is why
the `_env` form needs the *absolute* pair bound (`exists_abs_bound_double`) and not the
sign-sensitive `qw_Q3T_window_ge`, whose constant is allowed to depend on `ρ`.

All the Fock bookkeeping (`bp_nOp_sum_eq`, `bp_a_swap`, `normSq_aDag_eq`, the three `qw`
linearity lemmas) is re-derived here from `Defs` alone; the pair bound is the Fock-algebra
estimate of `NormSqA`, `NormSqTa`, `NormSqADag`, `NormSqA'` below.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. Fock-form bookkeeping -/

/-- `Σ_k ‖a_kf‖² = ⟨(Σ_ka_k†a_k)f, f⟩`. -/
private lemma bp_nOp_sum_eq (F : Work.BoseB7.FockData Mode) (f : F.H) :
    F.bp ((∑ k : Mode, F.nOp k) f) f = ∑ k : Mode, F.normSq (F.a k f) := by
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Work.BoseB7.FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint k (F.a k f) f,
      Work.BoseB7.FockData.normSq]

/-- `⟨a_ix, y⟩ = ⟨x, a_i†y⟩`. -/
private lemma bp_a_swap (F : Work.BoseB7.FockData Mode) (i : Mode) (x y : F.H) :
    F.bp (F.a i x) y = F.bp x (F.aDag i y) := by
  rw [F.bp_symm (F.a i x) y, ← F.aDag_adjoint i y x]
  exact F.bp_symm _ _

/-- `‖a_k†f‖² = ‖a_kf‖² + [a_k,a_k†]‖f‖²` (the CCR). -/
private lemma normSq_aDag_eq (F : Work.BoseB7.FockData Mode) (k : Mode) (f : F.H) :
    F.normSq (F.aDag k f) = F.normSq (F.a k f) + F.ccrK k k * F.normSq f := by
  have hpt : F.a k (F.aDag k f) = F.aDag k (F.a k f) + (F.ccrK k k) • f := by
    have h := congrArg (fun (S : F.H →ₗ[ℝ] F.H) => S f) (F.ccr k k)
    simpa using h
  rw [Work.BoseB7.FockData.normSq, F.aDag_adjoint k f (F.aDag k f),
    F.bp_symm f (F.a k (F.aDag k f)), hpt]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Work.BoseB7.FockData.normSq]
  rw [F.aDag_adjoint k (F.a k f) f]

/-- `qw` is additive in the operator. -/
private lemma qw_add (F : Work.BoseB7.FockData Mode) (g : F.H) (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw g (X + Y) = F.qw g X + F.qw g Y := by
  simp only [Work.BoseB7.FockData.qw, LinearMap.add_apply, map_add]

/-- `qw` is homogeneous in the operator. -/
private lemma qw_smul (F : Work.BoseB7.FockData Mode) (g : F.H) (c : ℝ)
    (X : F.H →ₗ[ℝ] F.H) : F.qw g (c • X) = c * F.qw g X := by
  simp only [Work.BoseB7.FockData.qw, LinearMap.smul_apply, map_smul, smul_eq_mul]

/-- The Fock form of a finite sum of operators is the sum of the forms. -/
private lemma qw_sum (F : Work.BoseB7.FockData Mode) (g : F.H) {ι : Type*}
    (s : Finset ι) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw g (∑ i ∈ s, X i) = ∑ i ∈ s, F.qw g (X i) := by
  have h1 : (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g := LinearMap.sum_apply s X g
  rw [Work.BoseB7.FockData.qw, h1, map_sum, LinearMap.sum_apply]
  simp only [Work.BoseB7.FockData.qw]

/-! ## 2. The single-mode window bounds -/

/-- The per-mode number bound on a window state: `‖a_kf‖² ≤ Cn·M‖f‖²` (Bessel + window). -/
private lemma normSq_a_le (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (Cn M : ℝ) (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (k : Mode) (f : F.H) (hf : T.NWindow M f) :
    F.normSq (F.a k f) ≤ Cn * M * F.normSq f := by
  have h1 : F.normSq (F.a k f) ≤ F.bp ((∑ j : Mode, F.nOp j) f) f := by
    rw [bp_nOp_sum_eq]
    exact Finset.single_le_sum (fun j _ => F.bp_nonneg (F.a j f)) (Finset.mem_univ k)
  have h2 : F.bp ((∑ j : Mode, F.nOp j) f) f ≤ Cn * F.bp (T.N f) f := hBessel f
  have h3 : F.bp (T.N f) f ≤ M * F.normSq f := Work.BoseB7A.NWindow_bp_N_le F T hM hf
  calc F.normSq (F.a k f) ≤ Cn * F.bp (T.N f) f := le_trans h1 h2
    _ ≤ Cn * (M * F.normSq f) := mul_le_mul_of_nonneg_left h3 hCn0
    _ = Cn * M * F.normSq f := by ring

/-- The `ã_s`-norm is dominated by the `n₊`-form (`ta_le_N` for a single mode). -/
private lemma normSq_ta_le (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    {s : Mode} (hs : s ≠ 0) (f : F.H) : F.normSq (T.ta s f) ≤ F.bp (T.N f) f := by
  have h := T.ta_le_N ({s} : Finset Mode)
    (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ hs) f
  rw [Finset.sum_singleton] at h
  have h2 : F.bp ((T.taDag s ∘ₗ T.ta s) f) f = F.normSq (T.ta s f) := by
    rw [LinearMap.comp_apply, Work.BoseB7.FockData.normSq]
    exact T.taDag_adjoint s (T.ta s f) f
  rwa [h2] at h

/-! ## 3. The per-pair bound for the cubic monomial -/

/-- **The cubic pair bound.**  For one summand `ã_s†a_{s−k}a_k + a_k†a_{s−k}†ã_s` of `3Q`
(any `s ≠ 0`, any `k`), the quadratic form on a window state is bounded in absolute value
by a constant times `‖g‖²`.

The two adjoint halves have the same form, `2⟨a_kg, a_{s−k}†ã_sg⟩`; Cauchy–Schwarz plus the
three window bounds (`‖a_kg‖² ≤ Cn·M‖g‖²`, `‖ã_sg‖² ≤ M‖g‖²`,
`‖a_{s−k}†ã_sg‖² ≤ (Cn·M + [a_{s−k},a_{s−k}†])‖ã_sg‖²`) close it. -/
private lemma q3_pair_abs_le (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (Cn M : ℝ) (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (s k : Mode) (hs : s ≠ 0) :
    ∃ C : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (T.qtermT s k + T.qtermDagT s k)| ≤ C * F.normSq g := by
  refine ⟨Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M, fun g hg => ?_⟩
  -- both halves have the same value `⟨a_kg, a_{s−k}†(ã_sg)⟩`
  have hval : F.qw g (T.qtermT s k + T.qtermDagT s k)
      = 2 * F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
    rw [qw_add]
    have h1 : F.qw g (T.qtermT s k) = F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
      rw [Work.BoseB7.FockData.qw, Work.BoseB7A.TildeData.qtermT, LinearMap.comp_apply,
        LinearMap.comp_apply, T.taDag_adjoint s (F.a (s - k) (F.a k g)) g]
      exact bp_a_swap F (s - k) (F.a k g) (T.ta s g)
    have h2 : F.qw g (T.qtermDagT s k) = F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
      rw [Work.BoseB7.FockData.qw, Work.BoseB7A.TildeData.qtermDagT, LinearMap.comp_apply,
        LinearMap.comp_apply, F.aDag_adjoint k (F.aDag (s - k) (T.ta s g)) g, F.bp_symm]
    rw [h1, h2, two_mul]
  rw [hval, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- the three window bounds
  have hA : F.normSq (F.a k g) ≤ Cn * M * F.normSq g :=
    normSq_a_le F T Cn M hCn0 hM hBessel k g hg
  have htag : F.normSq (T.ta s g) ≤ M * F.normSq g :=
    le_trans (normSq_ta_le F T hs g) (Work.BoseB7A.NWindow_bp_N_le F T hM hg)
  have htagwin : T.NWindow M (T.ta s g) := T.NWindow_ta s hg
  have hAu : F.normSq (F.a (s - k) (T.ta s g)) ≤ Cn * M * (M * F.normSq g) := by
    have h1 := normSq_a_le F T Cn M hCn0 hM hBessel (s - k) (T.ta s g) htagwin
    calc F.normSq (F.a (s - k) (T.ta s g)) ≤ Cn * M * F.normSq (T.ta s g) := h1
      _ ≤ Cn * M * (M * F.normSq g) := mul_le_mul_of_nonneg_left htag (mul_nonneg hCn0 hM)
  have hBu : F.normSq (F.aDag (s - k) (T.ta s g))
      ≤ (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g := by
    rw [normSq_aDag_eq]
    have h2 : F.ccrK (s - k) (s - k) * F.normSq (T.ta s g)
        ≤ |F.ccrK (s - k) (s - k)| * (M * F.normSq g) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (F.bp_nonneg _))
        (mul_le_mul_of_nonneg_left htag (abs_nonneg _))
    have hb : Cn * M * (M * F.normSq g) + |F.ccrK (s - k) (s - k)| * (M * F.normSq g)
        = (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g := by ring
    linarith [hAu, h2, hb]
  -- Cauchy–Schwarz
  have hx := Work.BoseB7.SumABound.bp_abs_le F (F.a k g) (F.aDag (s - k) (T.ta s g))
  have hA' : F.bp (F.a k g) (F.a k g) ≤ Cn * M * F.normSq g := by
    rw [← Work.BoseB7.FockData.normSq]; exact hA
  have hBu' : F.bp (F.aDag (s - k) (T.ta s g)) (F.aDag (s - k) (T.ta s g))
      ≤ (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g := by
    rw [← Work.BoseB7.FockData.normSq]; exact hBu
  have hb : Cn * M * F.normSq g + (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g
      = (Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M) * F.normSq g := by ring
  linarith [hx, hA', hBu', hb]

/-! ## 4. The summed two-sided bound (independent of `ρ`) -/

/-- **The `ρ`-free absolute bound on the cubic word `Q`.**  Summing the per-pair bounds over
the finite mode set with `exists_abs_bound_double`. -/
private theorem q3T_sum_abs_bound (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (Cn M : ℝ)
    (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ D : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
        (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))| ≤ D * F.normSq g :=
  exists_abs_bound_double F T M (Work.BoseB7.excited Mode) (F.PHset E)
    (fun s k => E.fL s * E.W1 k) (fun s k => T.qtermT s k + T.qtermDagT s k)
    (fun s hs k _ => q3_pair_abs_le F T Cn M hCn0 hM hBessel s k
      (by rw [Work.BoseB7.excited, Finset.mem_erase] at hs; exact hs.1))

/-! ## 5. The `ρ`-scaling of `z/ℓ³` -/

/-- For `ρ ≥ 0`: `|√(ρL)/L| ≤ (√|L|)⁻¹·√ρ`.  (`L > 0`: `√(ρL)/L = √ρ/√L`; `L ≤ 0`:
`√(ρL) = 0` and the right-hand side is nonnegative.) -/
private lemma sqrt_div_self_le (L ρ : ℝ) (hρ : 0 ≤ ρ) :
    |Real.sqrt (ρ * L) / L| ≤ (Real.sqrt |L|)⁻¹ * Real.sqrt ρ := by
  rcases lt_trichotomy L 0 with h | h | h
  · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hρ h.le), zero_div,
      abs_zero]
    positivity
  · subst h
    simp
  · have hL : 0 < L := h
    have hspos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
    have hval : Real.sqrt (ρ * L) / L = Real.sqrt ρ / Real.sqrt L := by
      rw [Real.sqrt_mul hρ L, div_eq_div_iff (ne_of_gt hL) (ne_of_gt hspos), mul_assoc,
        hsq]
    rw [hval, abs_of_pos hL,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), div_eq_inv_mul]

/-! ## 6. The target -/

theorem Q3T_window_ge_env {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (M Cn : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : F.H, T.NWindow M g →
      -(C * Work.BoseBoxFock.genv ρ) * F.normSq g
        ≤ F.qw g (T.Q3T (Work.BoseFixR.KzEnvAt E ρ)) := by
  classical
  obtain ⟨D, hD⟩ := q3T_sum_abs_bound F T E Cn M hM hCn0 hBessel
  refine ⟨|D| * (Real.sqrt |E.ell ^ 3|)⁻¹, by positivity, fun ρ hρ g hg => ?_⟩
  -- the `ρ`-independent pieces
  set Q3 : F.H →ₗ[ℝ] F.H := ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
    (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k) with hQ3_def
  set n : ℝ := F.normSq g with hn_def
  set A : ℝ := (Real.sqrt |E.ell ^ 3|)⁻¹ with hA_def
  set s : ℝ := Real.sqrt (ρ * E.ell ^ 3) / E.ell ^ 3 with hs_def
  set X : ℝ := |D| * A with hX_def
  have hn : 0 ≤ n := by rw [hn_def]; exact F.bp_nonneg g
  have hA0 : 0 ≤ A := by rw [hA_def]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hDn : 0 ≤ |D| := abs_nonneg D
  have hX0 : 0 ≤ X := by rw [hX_def]; exact mul_nonneg hDn hA0
  have hgenv : Real.sqrt ρ ≤ genv ρ := sqrt_le_genv hρ
  have hscale : |s| ≤ A * Real.sqrt ρ := by
    rw [hs_def, hA_def]
    exact sqrt_div_self_le _ _ hρ
  have hQ3T : T.Q3T (Work.BoseFixR.KzEnvAt E ρ) = s • Q3 := by
    rw [hQ3_def, hs_def]
    rfl
  have habs : |F.qw g Q3| ≤ |D| * n := by
    have h := hD g hg
    rw [← hn_def] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (le_abs_self D) (F.bp_nonneg g))
  rw [hQ3T, qw_smul]
  -- the three arithmetic steps
  have hstep1 : -(X * genv ρ) * n ≤ -(X * Real.sqrt ρ) * n := by
    have hle : X * Real.sqrt ρ ≤ X * genv ρ := mul_le_mul_of_nonneg_left hgenv hX0
    have hle2 : X * Real.sqrt ρ * n ≤ X * genv ρ * n := mul_le_mul_of_nonneg_right hle hn
    calc -(X * genv ρ) * n = -(X * genv ρ * n) := by rw [neg_mul]
      _ ≤ -(X * Real.sqrt ρ * n) := neg_le_neg hle2
      _ = -(X * Real.sqrt ρ) * n := by rw [neg_mul]
  have hstep2 : -(X * Real.sqrt ρ) * n ≤ -(|s| * |D| * n) := by
    have hle : |s| * |D| ≤ X * Real.sqrt ρ := by
      have h := mul_le_mul_of_nonneg_right hscale hDn
      calc |s| * |D| ≤ (A * Real.sqrt ρ) * |D| := h
        _ = X * Real.sqrt ρ := by rw [hX_def]; ring
    have hle2 : |s| * |D| * n ≤ X * Real.sqrt ρ * n := mul_le_mul_of_nonneg_right hle hn
    calc -(X * Real.sqrt ρ) * n = -(X * Real.sqrt ρ * n) := by rw [neg_mul]
      _ ≤ -(|s| * |D| * n) := neg_le_neg hle2
  have hstep3 : -(|s| * |D| * n) ≤ s * F.qw g Q3 := by
    have h1 : -( |s| * |F.qw g Q3|) ≤ s * F.qw g Q3 := by
      have h := neg_abs_le (s * F.qw g Q3)
      rwa [abs_mul] at h
    have h2 : |s| * |F.qw g Q3| ≤ |s| * (|D| * n) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg s)
    have h3 : |s| * (|D| * n) = |s| * |D| * n := by ring
    linarith [h1, h2, h3]
  linarith [hstep1, hstep2, hstep3]

end Work.BoseBoxFock
