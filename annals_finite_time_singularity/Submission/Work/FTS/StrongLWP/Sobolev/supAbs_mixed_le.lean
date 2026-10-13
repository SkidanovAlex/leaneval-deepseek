/-
Copyright: work module for the Elgindi finite-time singularity project.

# `supAbs` of a mixed derivative of order `≤ 4` by the `ℋ⁶`-norm

This file proves `Work.FTS.StrongLWP.Sobolev.supAbs_mixed_le`:

  `|D_z^j D_θ^i f|_{L^∞([0,∞)×[0,π/2])} ≤ 100/√(γ-1) · |f|_{ℋ⁶}`    (`i + j ≤ 4`),

for `f ∈ C^∞` on a neighbourhood of the closed quadrant, vanishing on the two angular
boundaries, with `f ∈ ℋ⁶` and with the mixed derivative itself decaying in `z`.

Route (the `Linf_H2_of_decay` route of `Work.Spaces.sup_mixed_le_H4`, at order `6`):

* `HkMem α 6 f` implies `HkMem α 2 (mixed j i f)`: every summand of the `H²`-integrand of
  `mixed j i f` is a summand of the `ℋ⁶`-integrand of `f`, because one `D_θ` (resp. `D_z`)
  lowers the level by exactly one (`HkIntegrand_Dth_le`, resp. `HkIntegrand_Dz_le` of
  `Work.Coercivity.HkMem_dth`); iterating the two shifts gives
  `HkIntegrand α l (mixed b a f) ≤ HkIntegrand α (l+a+b) f`
  (`supAbsAux_HkIntegrand_mixed_le_idx`), and enlarging `l + a + b` to `n` only adds
  nonnegative summands.
* the membership transfer is `supAbsAux_HkMem_of_integrand_le`, the squared-norm transfer
  is `supAbsAux_HkSq_le_of_integrand_le`, and the `L^∞`-bound is
  `Work.Spaces.Linf_H2_of_decay` (which uses the decay hypothesis only through its
  `(0,0)`-instance).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongLWP.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Linf_H2_of_decay
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.HkMem_dth
import Submission.Work.Coercivity.HkSq_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-! ## `VanishTheta` is preserved by mixed `D`-derivatives -/

/-- `VanishTheta` is preserved by iterated `D_z`-derivatives: the slice `θ ↦ DzIter n f z θ`
is identically zero at the two angular boundaries as soon as `f` is. -/
lemma supAbsAux_DzIter_vanishTheta {f : ℝ → ℝ → ℝ} (h : Work.Spaces.VanishTheta f) (n : ℕ) :
    Work.Spaces.VanishTheta (Work.Spaces.DzIter n f) := by
  induction n with
  | zero => exact h
  | succ m ih =>
      constructor
      · intro z
        have hfun : (fun z' => Work.Spaces.DzIter m f z' 0) = fun _ => (0 : ℝ) := funext ih.1
        simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hfun]
      · intro z
        have hfun : (fun z' => Work.Spaces.DzIter m f z' (π / 2)) = fun _ => (0 : ℝ) :=
          funext ih.2
        simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, hfun]

/-- Any positive iterate of `D_θ` already vanishes on the two angular boundaries
(`D_θ` carries the factor `sin(2θ)`). -/
lemma supAbsAux_DthIter_vanishTheta_of_pos (f : ℝ → ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    Work.Spaces.VanishTheta (Work.Spaces.DthIter a f) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  constructor
  · intro z
    show Real.sin (2 * 0) * Work.Spaces.pth (Work.Spaces.DthIter a' f) z 0 = 0
    simp
  · intro z
    show Real.sin (2 * (π / 2)) * Work.Spaces.pth (Work.Spaces.DthIter a' f) z (π / 2) = 0
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- `VanishTheta` is preserved by mixed `D`-derivatives `D_z^b D_θ^a`. -/
lemma supAbsAux_VanishTheta_mixed {f : ℝ → ℝ → ℝ} (h : Work.Spaces.VanishTheta f) (b a : ℕ) :
    Work.Spaces.VanishTheta (Work.Spaces.mixed b a f) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa [Work.Spaces.mixed] using supAbsAux_DzIter_vanishTheta h b
  · have h1 : Work.Spaces.VanishTheta (Work.Spaces.DthIter a f) :=
      supAbsAux_DthIter_vanishTheta_of_pos f ha
    simpa [Work.Spaces.mixed] using supAbsAux_DzIter_vanishTheta h1 b

/-! ## The `H^k`-integrand of a mixed derivative at a lower level

The two shifts: adding one `∂_θ` (with the `D_θ`-weight) raises the level of the integrand
by one, and likewise for `∂_z` (with the `D_z`-weight, the reindexing being the commutation
`D_z D_θ = D_θ D_z`). -/

/-- **`D_θ`-shift.**  `HkIntegrand α l (DthIter a f) ≤ HkIntegrand α (l+a) f`, by iterating
`Work.Coercivity.HkIntegrand_Dth_le`. -/
lemma supAbsAux_HkIntegrand_DthIter_le (α : ℝ) (hα : 0 < α) (a l : ℕ) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α l (Work.Spaces.DthIter a f) z θ
      ≤ Work.Spaces.HkIntegrand α (l + a) f z θ := by
  have hmain : ∀ a l : ℕ, Work.Spaces.HkIntegrand α l (Work.Spaces.DthIter a f) z θ
      ≤ Work.Spaces.HkIntegrand α (l + a) f z θ := by
    intro a
    induction a with
    | zero => intro l; simp
    | succ a ih =>
        intro l
        have h1 := Work.Coercivity.HkIntegrand_Dth_le α hα l (Work.Spaces.DthIter a f)
          z θ hz hθ
        have h2 := ih (l + 1)
        calc Work.Spaces.HkIntegrand α l (Work.Spaces.DthIter (a + 1) f) z θ
            = Work.Spaces.HkIntegrand α l
                (Work.Spaces.Dth (Work.Spaces.DthIter a f)) z θ := rfl
          _ ≤ Work.Spaces.HkIntegrand α (l + 1) (Work.Spaces.DthIter a f) z θ := h1
          _ ≤ Work.Spaces.HkIntegrand α ((l + 1) + a) f z θ := h2
          _ = Work.Spaces.HkIntegrand α (l + (a + 1)) f z θ :=
              congrArg (fun k => Work.Spaces.HkIntegrand α k f z θ) (by omega)
  exact hmain a l

/-- **`D_z`-shift.**  `HkIntegrand α l (DzIter b f) ≤ HkIntegrand α (l+b) f`, by iterating
`Work.Coercivity.HkIntegrand_Dz_le` (which needs `SmoothNbhd f` for the commutation
`D_z D_θ = D_θ D_z`). -/
lemma supAbsAux_HkIntegrand_DzIter_le (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) (b l : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α l (Work.Spaces.DzIter b f) z θ
      ≤ Work.Spaces.HkIntegrand α (l + b) f z θ := by
  have hmain : ∀ b l : ℕ, Work.Spaces.HkIntegrand α l (Work.Spaces.DzIter b f) z θ
      ≤ Work.Spaces.HkIntegrand α (l + b) f z θ := by
    intro b
    induction b with
    | zero => intro l; simp
    | succ b ih =>
        intro l
        have hsmb : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter b f) :=
          Work.Spaces.SmoothNbhd.DzIter hsm b
        have h1 := Work.Coercivity.HkIntegrand_Dz_le α l hsmb z θ hz hθ
        have h2 := ih (l + 1)
        calc Work.Spaces.HkIntegrand α l (Work.Spaces.DzIter (b + 1) f) z θ
            = Work.Spaces.HkIntegrand α l
                (Work.Spaces.Dz (Work.Spaces.DzIter b f)) z θ := rfl
          _ ≤ Work.Spaces.HkIntegrand α (l + 1) (Work.Spaces.DzIter b f) z θ := h1
          _ ≤ Work.Spaces.HkIntegrand α ((l + 1) + b) f z θ := h2
          _ = Work.Spaces.HkIntegrand α (l + (b + 1)) f z θ :=
              congrArg (fun k => Work.Spaces.HkIntegrand α k f z θ) (by omega)
  exact hmain b l

/-- Mixed form: `HkIntegrand α l (mixed b a f) ≤ HkIntegrand α (l+a+b) f`. -/
lemma supAbsAux_HkIntegrand_mixed_le_idx (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) (l a b : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α l (Work.Spaces.mixed b a f) z θ
      ≤ Work.Spaces.HkIntegrand α (l + a + b) f z θ := by
  have hsmth : Work.Spaces.SmoothNbhd (Work.Spaces.DthIter a f) :=
    Work.Spaces.SmoothNbhd.DthIter hsm a
  have h1 := supAbsAux_HkIntegrand_DzIter_le (f := Work.Spaces.DthIter a f) α hsmth b l
    z θ hz hθ
  have h2 := supAbsAux_HkIntegrand_DthIter_le α hα a (l + b) f z θ hz hθ
  have h3 : (l + b) + a = l + a + b := by omega
  calc Work.Spaces.HkIntegrand α l (Work.Spaces.mixed b a f) z θ
      = Work.Spaces.HkIntegrand α l
          (Work.Spaces.DzIter b (Work.Spaces.DthIter a f)) z θ := rfl
    _ ≤ Work.Spaces.HkIntegrand α (l + b) (Work.Spaces.DthIter a f) z θ := h1
    _ ≤ Work.Spaces.HkIntegrand α ((l + b) + a) f z θ := h2
    _ = Work.Spaces.HkIntegrand α (l + a + b) f z θ := by rw [h3]

/-- Enlarging the level `l ≤ n` only adds nonnegative summands to the `H`-integrand. -/
lemma supAbsAux_HkIntegrand_le_of_le (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (l n : ℕ)
    (h : l ≤ n) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α n f z θ := by
  have hmain : ∀ d l : ℕ, Work.Spaces.HkIntegrand α l f z θ
      ≤ Work.Spaces.HkIntegrand α (l + d) f z θ := by
    intro d
    induction d with
    | zero => intro l; simp
    | succ d ih =>
        intro l
        refine le_trans (ih l) ?_
        show Work.Spaces.HkIntegrand α (l + d) f z θ
          ≤ Work.Spaces.HkIntegrand α (l + (d + 1)) f z θ
        rw [← Nat.add_assoc l d 1]
        exact Work.Spaces.HkIntegrand_mono α (l + d) f z θ
  have hl : l + (n - l) = n := Nat.add_sub_cancel' h
  simpa [hl] using hmain (n - l) l

/-- **The pointwise domination.**  If `l + a + b ≤ n` then every summand of the
`H^l`-integrand of `mixed b a f` is a summand of the `H^n`-integrand of `f`. -/
lemma supAbsAux_HkIntegrand_mixed_le_gen (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f) (l n a b : ℕ) (hln : l + a + b ≤ n) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α l (Work.Spaces.mixed b a f) z θ
      ≤ Work.Spaces.HkIntegrand α n f z θ :=
  le_trans (supAbsAux_HkIntegrand_mixed_le_idx α hα hsm l a b z θ hz hθ)
    (supAbsAux_HkIntegrand_le_of_le α f z θ (l + a + b) n hln)

/-! ## Integration of the pointwise domination -/

/-- The pointwise domination of the integrands integrates to an inequality of the squared
norms. -/
lemma supAbsAux_HkSq_le_of_integrand_le (α : ℝ) (l n : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α n f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α l g z θ ≤ Work.Spaces.HkIntegrand α n f z θ) :
    Work.Spaces.HkSq α l g ≤ Work.Spaces.HkSq α n f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  apply setIntegral_mono_of_nonneg
  · intro z _
    exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α l g z θ
  · intro z hz
    apply setIntegral_mono_of_nonneg
    · intro θ _
      exact Work.Spaces.HkIntegrand_nonneg α l g z θ
    · intro θ hθ
      exact hle z hz θ hθ
    · exact h.1 z hz
  · exact h.2

/-- The pointwise domination of the integrands transfers `HkMem` from `f` to `g`, using the
a.e. strong measurability of the `H^l`-integrand of a smooth `g`. -/
lemma supAbsAux_HkMem_of_integrand_le (α : ℝ) (l n : ℕ) {f g : ℝ → ℝ → ℝ}
    (hsmg : Work.Spaces.SmoothNbhd g) (h : Work.Spaces.HkMem α n f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α l g z θ ≤ Work.Spaces.HkIntegrand α n f z θ) :
    Work.Spaces.HkMem α l g := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice := Work.Coercivity.aesm_HkIntegrand_slice α l hsmg
  have hjoint := Work.Coercivity.aesm_uncurry_HkIntegrand α l hsmg
  constructor
  · intro z hz
    refine Integrable.mono' (h.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α l g z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' h.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α l g z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α l g z θ))
      (h.1 z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))

/-! ## The target lemma -/

theorem supAbs_mixed_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hji : i + j + 2 ≤ 6) (hsm : Work.Spaces.SmoothNbhd f) (hvt : Work.Spaces.VanishTheta f)
    (hdec : Work.Spaces.DecayInZ 2 (Work.Spaces.mixed j i f)) (hmem : Work.Spaces.HkMem α 6 f) :
    Work.Spaces.supAbs (Work.Spaces.mixed j i f)
      ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 6 f := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.mixed j i f) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j
  have hvt' : Work.Spaces.VanishTheta (Work.Spaces.mixed j i f) :=
    supAbsAux_VanishTheta_mixed hvt j i
  -- the `H²`-integrand of `mixed j i f` is dominated by the `H⁶`-integrand of `f`
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 (Work.Spaces.mixed j i f) z θ
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z hz θ hθ =>
      supAbsAux_HkIntegrand_mixed_le_gen α hα hsm 2 6 i j (by omega) z θ hz hθ
  have hmem' : Work.Spaces.HkMem α 2 (Work.Spaces.mixed j i f) :=
    supAbsAux_HkMem_of_integrand_le α 2 6 hsm' hmem hle
  -- the decay hypothesis is used only through its `(0,0)`-instance
  have hdec' : ∀ θ ∈ Work.Spaces.Iθ,
      Tendsto (fun z => Work.Spaces.mixed j i f z θ) atTop (𝓝 0) := by
    intro θ hθ
    simpa using hdec 0 0 (by omega) θ hθ
  have h1 := Work.Spaces.Linf_H2_of_decay α hα hα1 (Work.Spaces.mixed j i f) hsm' hvt'
    hdec' hmem'
  have h2 : Work.Spaces.HkNorm α 2 (Work.Spaces.mixed j i f) ≤ Work.Spaces.HkNorm α 6 f :=
    Real.sqrt_le_sqrt (supAbsAux_HkSq_le_of_integrand_le α 2 6 hmem hle)
  have hcoef : 0 ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc Work.Spaces.supAbs (Work.Spaces.mixed j i f)
      ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 2 (Work.Spaces.mixed j i f) := h1
    _ ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 6 f :=
        mul_le_mul_of_nonneg_left h2 hcoef

end Work.FTS.StrongLWP.Sobolev
