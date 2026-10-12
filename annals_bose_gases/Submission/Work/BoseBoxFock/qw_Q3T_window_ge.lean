import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.qw_Q3T_window_ge`

The **window lower bound for the cubic word `3Q`** (FS `eq:kroelleQ3z`, in the corrected
`ã_s`-slot form `Work.BoseB7A.TildeData.Q3T`):

> on a window state `g` (`T.NWindow M g`) and under the Bessel/number hypothesis
> `Σ_k a_k†a_k ≤ Cn·n₊` with `Cn ≤ 16`, the cubic form is bounded below,
> `K‖g‖² ≤ ⟨g, (3Q)g⟩`.

## Where the bound comes from

`3Q = (z/ℓ³)Σ_{s ∈ excited}Σ_{k ∈ P_H}(f_L(s)Ŵ₁(k))(Ã_s†a_{s−k}a_k + h.c.)`.  The two
adjoint halves have the *same* quadratic form, so only

  `⟨Ã_s†a_{s−k}a_k g, g⟩ = ⟨a_k g, a_{s−k}†(Ã_s g)⟩`

has to be bounded.  The window plus Bessel gives, purely from the number grading and
positivity of `n₊` (no diagonalisation, no completeness: every bound below is the
`NWindow` bound `⟨n₊f,f⟩ ≤ M‖f‖²` of `Work.BoseB7A.NWindow_bp_N_le` applied to a vector
that the grading keeps inside the window — `a_kg`, `Ã_sg` — together with
`Σ_ka_k†a_k ≤ Cn·n₊`):

* `‖a_k g‖² ≤ Cn·M‖g‖²`             (`normSq_a_le`),
* `‖Ã_s g‖² ≤ M‖g‖²`                (`normSq_ta_le` + the window bound),
* `‖a_{s−k}†(Ã_sg)‖² = ‖a_{s−k}(Ã_sg)‖² + [a_{s−k},a_{s−k}†]‖Ã_sg‖²`
                                       (`normSq_aDag_eq` + the CCR),

so Cauchy–Schwarz `|⟨u,v⟩| ≤ (‖u‖²+‖v‖²)/2` bounds the pair by an explicit multiple of
`‖g‖²` depending only on `M`, `Cn`, `[a,a†]` and the componentwise data of `F`, `T`, `E`.
The result is summed over the finite mode set (`exists_abs_bound_double`), and the
overall constant is the finite sum of the coefficient magnitudes times the pair bound,
multiplied by `|z|/ℓ³`; the sign of `z/ℓ³` is handled by taking absolute values.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. Elementary Fock-form identities -/

/-- `Σ_k‖a_kf‖² = ⟨(Σ_ka_k†a_k)f, f⟩`. -/
private theorem bp_nOp_sum_eq (F : FockData Mode) (f : F.H) :
    F.bp ((∑ k : Mode, F.nOp k) f) f = ∑ k : Mode, F.normSq (F.a k f) := by
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint, FockData.normSq]

/-- `⟨a_ix, y⟩ = ⟨x, a_i†y⟩` (adjointness of `a_i†`). -/
private theorem bp_a_swap (F : FockData Mode) (i : Mode) (x y : F.H) :
    F.bp (F.a i x) y = F.bp x (F.aDag i y) := by
  rw [F.bp_symm (F.a i x) y, ← F.aDag_adjoint i y x]
  exact F.bp_symm _ _

/-- `‖a_k†f‖² = ‖a_kf‖² + [a_k,a_k†]‖f‖²` (the CCR). -/
private theorem normSq_aDag_eq (F : FockData Mode) (k : Mode) (f : F.H) :
    F.normSq (F.aDag k f) = F.normSq (F.a k f) + F.ccrK k k * F.normSq f := by
  have hpt : F.a k (F.aDag k f) = F.aDag k (F.a k f) + (F.ccrK k k) • f := by
    have h := congrArg (fun (S : F.H →ₗ[ℝ] F.H) => S f) (F.ccr k k)
    simpa using h
  rw [FockData.normSq, F.aDag_adjoint k f (F.aDag k f), F.bp_symm f (F.a k (F.aDag k f)),
    hpt]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    FockData.normSq]
  rw [F.aDag_adjoint k (F.a k f) f]

/-- The `ã_s`-norm is dominated by the `n₊`-form (`ta_le_N` for a single mode). -/
private theorem normSq_ta_le (F : FockData Mode) (T : Work.BoseB7A.TildeData F) {s : Mode}
    (hs : s ≠ 0) (f : F.H) : F.normSq (T.ta s f) ≤ F.bp (T.N f) f := by
  have h := T.ta_le_N ({s} : Finset Mode)
    (by intro t ht; rw [Finset.mem_singleton] at ht; exact ht ▸ hs) f
  rw [Finset.sum_singleton] at h
  have h2 : F.bp ((T.taDag s ∘ₗ T.ta s) f) f = F.normSq (T.ta s f) := by
    rw [LinearMap.comp_apply, FockData.normSq]
    exact T.taDag_adjoint s (T.ta s f) f
  rwa [h2] at h

/-- `qw` is additive in the operator. -/
private theorem qw_add (F : FockData Mode) (g : F.H) (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw g (X + Y) = F.qw g X + F.qw g Y := by
  simp only [FockData.qw, LinearMap.add_apply, map_add, LinearMap.add_apply]

/-- `qw` is homogeneous in the operator. -/
private theorem qw_smul (F : FockData Mode) (g : F.H) (c : ℝ) (X : F.H →ₗ[ℝ] F.H) :
    F.qw g (c • X) = c * F.qw g X := by
  simp only [FockData.qw, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- The per-mode number bound on a window state: `‖a_kf‖² ≤ Cn·M‖f‖²` (Bessel + window). -/
private theorem normSq_a_le (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (k : Mode) (f : F.H) (hf : T.NWindow M f) :
    F.normSq (F.a k f) ≤ Cn * M * F.normSq f := by
  have h1 : F.normSq (F.a k f) ≤ F.bp ((∑ j : Mode, F.nOp j) f) f := by
    rw [bp_nOp_sum_eq]
    exact Finset.single_le_sum (fun j _ => F.bp_nonneg (F.a j f)) (Finset.mem_univ k)
  have h2 : F.bp ((∑ j : Mode, F.nOp j) f) f ≤ Cn * F.bp (T.N f) f := hBessel f
  have h3 : F.bp (T.N f) f ≤ M * F.normSq f :=
    Work.BoseB7A.NWindow_bp_N_le F T hM hf
  calc F.normSq (F.a k f) ≤ Cn * F.bp (T.N f) f := le_trans h1 h2
    _ ≤ Cn * (M * F.normSq f) := mul_le_mul_of_nonneg_left h3 hCn0
    _ = Cn * M * F.normSq f := by ring

/-! ## 2. The pair bound for the cubic monomial -/

/-- **The cubic pair bound.**  For one summand `Ã_s†a_{s−k}a_k + a_k†a_{s−k}†Ã_s` of `3Q`
(any `s ≠ 0`, any `k`), the quadratic form on a window state is bounded in absolute value
by a constant times `‖g‖²`.

The two adjoint halves have the same form, `2⟨a_kg, a_{s−k}†Ã_sg⟩`; Cauchy–Schwarz plus the
three window bounds of §1 (`‖a_kg‖² ≤ Cn·M‖g‖²`, `‖Ã_sg‖² ≤ M‖g‖²`,
`‖a_{s−k}†Ã_sg‖² ≤ (Cn·M + [a_{s−k},a_{s−k}†])‖Ã_sg‖²`) close it by textbook bookkeeping. -/
private theorem q3_pair_abs_le (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn M : ℝ)
    (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (s k : Mode) (hs : s ≠ 0) :
    ∃ C : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (T.qtermT s k + T.qtermDagT s k)| ≤ C * F.normSq g := by
  refine ⟨Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M, fun g hg => ?_⟩
  -- both halves have the same value `⟨a_kg, a_{s−k}†(Ã_sg)⟩`
  have hval : F.qw g (T.qtermT s k + T.qtermDagT s k)
      = 2 * F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
    rw [qw_add]
    have h1 : F.qw g (T.qtermT s k) = F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
      rw [FockData.qw, Work.BoseB7A.TildeData.qtermT, LinearMap.comp_apply,
        LinearMap.comp_apply, T.taDag_adjoint s (F.a (s - k) (F.a k g)) g]
      exact bp_a_swap F (s - k) (F.a k g) (T.ta s g)
    have h2 : F.qw g (T.qtermDagT s k) = F.bp (F.a k g) (F.aDag (s - k) (T.ta s g)) := by
      rw [FockData.qw, Work.BoseB7A.TildeData.qtermDagT, LinearMap.comp_apply,
        LinearMap.comp_apply, F.aDag_adjoint k (F.aDag (s - k) (T.ta s g)) g,
        F.bp_symm]
    rw [h1, h2, two_mul]
  -- the three window bounds
  have hA : F.normSq (F.a k g) ≤ Cn * M * F.normSq g :=
    normSq_a_le F T Cn M hCn0 hM hBessel k g hg
  have htag : F.normSq (T.ta s g) ≤ M * F.normSq g :=
    le_trans (normSq_ta_le F T hs g) (Work.BoseB7A.NWindow_bp_N_le F T hM hg)
  have htagwin : T.NWindow M (T.ta s g) := T.NWindow_ta s hg
  have hAu : F.normSq (F.a (s - k) (T.ta s g)) ≤ Cn * M * (M * F.normSq g) :=
    le_trans (normSq_a_le F T Cn M hCn0 hM hBessel (s - k) (T.ta s g) htagwin)
      (mul_le_mul_of_nonneg_left htag (mul_nonneg hCn0 hM))
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
    rw [← FockData.normSq]; exact hA
  have hBu' : F.bp (F.aDag (s - k) (T.ta s g)) (F.aDag (s - k) (T.ta s g))
      ≤ (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g := by
    rw [← FockData.normSq]; exact hBu
  have hx' : 2 * |F.bp (F.a k g) (F.aDag (s - k) (T.ta s g))|
      ≤ (Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M) * F.normSq g := by
    have hb : F.bp (F.a k g) (F.a k g)
        + F.bp (F.aDag (s - k) (T.ta s g)) (F.aDag (s - k) (T.ta s g))
        ≤ (Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M) * F.normSq g := by
      have hbb : Cn * M * F.normSq g + (Cn * M + |F.ccrK (s - k) (s - k)|) * M * F.normSq g
          = (Cn * M + (Cn * M + |F.ccrK (s - k) (s - k)|) * M) * F.normSq g := by ring
      linarith [add_le_add hA' hBu', hbb]
    linarith [hx, hb]
  rw [hval, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact hx'

/-! ## 3. Summation over the mode set -/

/-- The Fock form of a finite sum of operators is the sum of the forms. -/
private theorem qw_sum (F : FockData Mode) (g : F.H) {ι : Type*} (s : Finset ι)
    (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw g (∑ i ∈ s, X i) = ∑ i ∈ s, F.qw g (X i) := by
  have h1 : (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g := LinearMap.sum_apply s X g
  rw [FockData.qw, h1, map_sum, LinearMap.sum_apply]
  simp only [FockData.qw]

/-- The Fock form of a finite sum of scaled operators is the corresponding sum of forms. -/
private theorem qw_sum_smul (F : FockData Mode) (g : F.H) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw g (∑ i ∈ s, c i • X i) = ∑ i ∈ s, c i * F.qw g (X i) := by
  rw [qw_sum]
  exact Finset.sum_congr rfl fun i _ => qw_smul F g (c i) (X i)

/-- **Finite summation of window bounds**: if every summand form is bounded by a constant
times `‖g‖²` on the window, then so is any finite linear combination of them. -/
private theorem exists_abs_bound_double (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (M : ℝ) {α β : Type*} (s : Finset α) (t : Finset β) (c : α → β → ℝ)
    (X : α → β → F.H →ₗ[ℝ] F.H)
    (hX : ∀ a ∈ s, ∀ b ∈ t, ∃ C : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (X a b)| ≤ C * F.normSq g) :
    ∃ D : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (∑ a ∈ s, ∑ b ∈ t, c a b • X a b)| ≤ D * F.normSq g := by
  classical
  set C : α → β → ℝ := fun a b => if h : a ∈ s ∧ b ∈ t then Classical.choose (hX a h.1 b h.2)
    else 0 with hC
  have hCbound : ∀ a ∈ s, ∀ b ∈ t, ∀ g : F.H, T.NWindow M g →
      |F.qw g (X a b)| ≤ C a b * F.normSq g := by
    intro a ha b hb g hg
    have h : C a b = Classical.choose (hX a ha b hb) := by
      rw [hC]; exact dif_pos ⟨ha, hb⟩
    rw [h]
    exact Classical.choose_spec (hX a ha b hb) g hg
  refine ⟨∑ a ∈ s, ∑ b ∈ t, |c a b| * C a b, fun g hg => ?_⟩
  have hnn : 0 ≤ F.normSq g := F.bp_nonneg g
  have hsplit : F.qw g (∑ a ∈ s, ∑ b ∈ t, c a b • X a b)
      = ∑ a ∈ s, ∑ b ∈ t, c a b * F.qw g (X a b) := by
    rw [qw_sum]
    exact Finset.sum_congr rfl fun a _ => qw_sum_smul F g t (fun b => c a b) (fun b => X a b)
  rw [hsplit]
  calc |∑ a ∈ s, ∑ b ∈ t, c a b * F.qw g (X a b)|
      ≤ ∑ a ∈ s, |∑ b ∈ t, c a b * F.qw g (X a b)| :=
        Finset.abs_sum_le_sum_abs _ s
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, |c a b * F.qw g (X a b)| :=
        Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ t
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, |c a b| * C a b * F.normSq g := by
        refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
        rw [abs_mul]
        have h2 : |F.qw g (X a b)| ≤ C a b * F.normSq g := hCbound a ha b hb g hg
        have h3 : |c a b| * |F.qw g (X a b)| ≤ |c a b| * (C a b * F.normSq g) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        calc |c a b| * |F.qw g (X a b)| ≤ |c a b| * (C a b * F.normSq g) := h3
          _ = |c a b| * C a b * F.normSq g := by ring
    _ = (∑ a ∈ s, ∑ b ∈ t, |c a b| * C a b) * F.normSq g := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.sum_mul]

/-! ## 4. The `3Q` lower bound on the window -/

/-- The absolute window bound for the whole cubic word. -/
private theorem q3T_window_abs_bound (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Q3Env Mode) (Cn M : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ D : ℝ, ∀ g : F.H, T.NWindow M g →
      |F.qw g (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
          (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))| ≤ D * F.normSq g :=
  exists_abs_bound_double F T M (Work.BoseB7.excited Mode) (F.PHset E)
    (fun s k => E.fL s * E.W1 k) (fun s k => T.qtermT s k + T.qtermDagT s k)
    (fun s hs k _ => q3_pair_abs_le F T Cn M hCn0 hM hBessel s k
      (by rw [Work.BoseB7.excited, Finset.mem_erase] at hs; exact hs.1))

/-- **The general window lower bound for `3Q`** (any `Q3Env`, any window parameter). -/
theorem q3T_window_ge_general (F : FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Q3Env Mode) (Cn M : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (T.Q3T E) := by
  obtain ⟨D, hD⟩ := q3T_window_abs_bound F T E Cn M hM hCn0 hBessel
  refine ⟨-(|E.z / E.ell ^ 3| * D), fun g hg => ?_⟩
  have hDg : |F.qw g (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
      (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))| ≤ D * F.normSq g := hD g hg
  have hq : F.qw g (T.Q3T E) = (E.z / E.ell ^ 3) * F.qw g (∑ s ∈ Work.BoseB7.excited Mode,
      ∑ k ∈ F.PHset E, (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k)) := by
    rw [Work.BoseB7A.TildeData.Q3T, qw_smul]
  rw [hq]
  rcases lt_or_ge 0 (E.z / E.ell ^ 3) with hc | hc
  · have h1 : (E.z / E.ell ^ 3) * (-(D * F.normSq g))
        ≤ (E.z / E.ell ^ 3) * F.qw g (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
            (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k)) :=
      mul_le_mul_of_nonneg_left (abs_le.mp hDg).1 (le_of_lt hc)
    rw [abs_of_pos hc]
    calc -((E.z / E.ell ^ 3) * D) * F.normSq g
        = (E.z / E.ell ^ 3) * (-(D * F.normSq g)) := by ring
      _ ≤ _ := h1
  · have h1 : (E.z / E.ell ^ 3) * (D * F.normSq g)
        ≤ (E.z / E.ell ^ 3) * F.qw g (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
            (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k)) :=
      mul_le_mul_of_nonpos_left (abs_le.mp hDg).2 hc
    rw [abs_of_nonpos hc]
    calc -(-(E.z / E.ell ^ 3) * D) * F.normSq g
        = (E.z / E.ell ^ 3) * (D * F.normSq g) := by ring
      _ ≤ _ := h1

/-! ## 5. The requested statement -/

theorem qw_Q3T_window_ge {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (M Cn ρ : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn) (hCn16 : Cn ≤ 16)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ F.qw g (T.Q3T (Work.BoseFixR.KzEnvAt E ρ)) := by
  exact q3T_window_ge_general F T (Work.BoseFixR.KzEnvAt E ρ) Cn M hM hCn0 hBessel

end Work.BoseBoxFock
