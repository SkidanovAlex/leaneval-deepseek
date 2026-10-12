import Mathlib
import Submission.Work.BoseB7A.Statements
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Q3Kernel_inhabited` — the kernel interface is inhabited

`Work.BoseB7A.Q3Kernel` (`Submission/Work/BoseB7A/Defs.lean`) is the *only*
hypothesis of the three estimates `estQ3oneA`, `estQ3twoThreeA`, `estQ3fourA`
and of the assembled `thm:Control3Q` of FS §10, besides the parameter point
`FSParamsView`.  All of those statements have the shape

`∀ Mode F T E (hv : FSParamsView E), … → Q3Kernel K₀ F T E → …`

so if `Q3Kernel` were uninhabited the whole chapter would be vacuously true.
This module *exhibits* an instance of the bundle for every `K₀ ≥ 0`, on the
degenerate one-mode lattice `Mode = ZMod 1`, showing that the interface is
consistent and non-vacuous.

The witness is the obvious "everything acts on the one-dimensional space"
model, where all the mode-indexed data live on the single mode `0`:

* `trivFock`: `H = ULift ℝ` (the universe of the Fock space is an implicit
  parameter of the statement, so the model is built in `ULift ℝ`), `kmom ≡ 0`,
  `a ≡ a† ≡ 0`, `ccrK ≡ 0`, and `bp x y = x.down * y.down` (the product on `ℝ`).
  On the one-point group `ZMod 1` the only mode is `0`, so
  `excited (ZMod 1) = ∅` and every mode sum of the chapter vanishes.
* `trivTilde`: all the θ-mode operators and both number operators are `0` (the
  only non-vacuous commutator field `ta_ccr` is guarded by `s ≠ 0`, impossible
  on `ZMod 1`).
* `trivEnv`: FS's parameter point at `t = 1` (`fsEnv 1`) with `χ̂` replaced by
  `0`.  The modification is forced: with `a ≡ a† ≡ 0` the field `ccr` of
  `FockData` forces `ccrK ≡ 0`, so `hasKernel` needs `χ̂² - χ̂·χ̂ ≡ 0` on the
  only mode, whereas `fsEnv`'s `χ̂ ≡ 1` would give `-1`.  Its `FSParamsView` is
  transferred field by field from `FSParamsView_fsEnv` (no field of
  `FSParamsView` mentions the kernels, so only the untouched scalars matter).
* `trivQ3Kernel`: the hypothesis `K₀ ≥ 0` is used only in the five fields that
  bound a sum or a count by `K₀ * (something ≥ 0)`; on `ZMod 1` the remaining
  fields are empty-sum identities or vacuous implications (guarded by `f_L ≡ 0`
  or by the empty region `P_H^q`, see `trivNotPHq`).

## Contents

* `trivFockBp`, `trivFock`, `trivTilde`, `trivEnv`, `trivEnv_view` — the witness.
* `excited_zmod1`, `trivNotPHq`, `trivKlKL_nonneg`, `trivKH_pos`, `trivRho_pos`
  — the elementary facts about it used by the kernel.
* `trivQ3Kernel` — the kernel at the witness.
* `Q3Kernel_inhabited` — the target.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

universe v

/-! ## 1. The degenerate Fock space on the one-mode lattice `ZMod 1` -/

/-- The Fock form of the witness: the product on `ULift ℝ`, as a bilinear form
(`H →ₗ[ℝ] H →ₗ[ℝ] ℝ`). -/
def trivFockBp : ULift.{v} ℝ →ₗ[ℝ] ULift.{v} ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y : ULift.{v} ℝ => x.down * y.down)
    (fun x₁ x₂ y => by rw [show (x₁ + x₂).down = x₁.down + x₂.down from rfl, add_mul])
    (fun c x y => by rw [show (c • x).down = c • x.down from rfl, smul_mul_assoc])
    (fun x y₁ y₂ => by rw [show (y₁ + y₂).down = y₁.down + y₂.down from rfl, mul_add])
    (fun c x y => by rw [show (c • y).down = c • y.down from rfl, mul_smul_comm])

/-- The trivial `Mode = ZMod 1` Fock model: the one-dimensional space
`H = ULift ℝ`, zero annihilation/creation operators, zero commutator kernel and
the product as Fock form.  (`ZMod 1` is a subsingleton, so its only mode is
`0`.) -/
def trivFock : FockData.{0, v} (ZMod 1) where
  H := ULift.{v} ℝ
  kmom := fun _ => 0
  kmom_neg := by intro i; simp
  a := fun _ => 0
  aDag := fun _ => 0
  ann_comm := by intro i j; simp
  cre_comm := by intro i j; simp
  ccrK := fun _ _ => 0
  ccr := by intro i j; simp
  bp := trivFockBp
  bp_symm := by intro f g; exact mul_comm f.down g.down
  bp_nonneg := by intro f; exact mul_self_nonneg f.down
  bp_def := by intro f h; exact ULift.ext (mul_self_eq_zero.mp h)
  aDag_adjoint := by intro i f g; simp

@[simp] lemma trivFock_a (i : ZMod 1) : trivFock.a i = 0 := rfl
@[simp] lemma trivFock_aDag (i : ZMod 1) : trivFock.aDag i = 0 := rfl
@[simp] lemma trivFock_ccrK (i j : ZMod 1) : trivFock.ccrK i j = 0 := rfl
@[simp] lemma trivFock_kmom (i : ZMod 1) : trivFock.kmom i = 0 := rfl
@[simp] lemma trivFock_bp (f g : ULift.{v} ℝ) : trivFock.bp f g = f.down * g.down := rfl

/-- `excited (ZMod 1) = ∅`: the one-mode lattice has no excited mode. -/
lemma excited_zmod1 : Work.BoseB7.excited (ZMod 1) = ∅ := by decide

/-! ## 2. The θ-modes, both zero -/

/-- The trivial `TildeData` over `trivFock`: all θ-mode operators and both
number operators are `0`.  The only field that is not a zero identity is
`ta_ccr` (asking for a canonical commutator `[ã_s,ã_t†] = δ_{st}`), and it is
guarded by `s ≠ 0` — impossible on `ZMod 1`. -/
def trivTilde : Work.BoseB7A.TildeData trivFock where
  ta := fun _ => 0
  taDag := fun _ => 0
  taDag_adjoint := by intro s f g; simp
  ta_comm := by intro s t; simp
  taDag_comm := by intro s t; simp
  ta_ccr := by intro s t hs ht; exact absurd (Subsingleton.elim s 0) hs
  ta_a_comm := by intro s k; simp
  ccrX := fun _ _ => 0
  ta_aDag := by intro s k; simp
  N := 0
  NH := 0
  N_symm := by intro f g; simp
  N_nonneg := by intro f; simp
  NH_nonneg := by intro f; simp
  N_a := by intro k; simp
  N_aDag := by intro k; simp
  N_ta := by intro s; simp
  N_taDag := by intro s; simp
  ta_le_N := by intro S hS f; simp

@[simp] lemma trivTilde_ta (s : ZMod 1) : trivTilde.ta s = 0 := rfl
@[simp] lemma trivTilde_taDag (s : ZMod 1) : trivTilde.taDag s = 0 := rfl
@[simp] lemma trivTilde_ccrX (s q : ZMod 1) : trivTilde.ccrX s q = 0 := rfl
@[simp] lemma trivTilde_N : trivTilde.N = 0 := rfl
@[simp] lemma trivTilde_NH : trivTilde.NH = 0 := rfl

/-! ## 3. FS's parameter point at `t = 1`, with `χ̂ ≡ 0` -/

/-- FS's parameter point at diluteness `t = 1` (`Work.BoseB7.fsEnv 1`), with the
single modification `χ̂ ≡ 0` (see the module docstring). -/
def trivEnv : Q3Env (ZMod 1) :=
  { fsEnv (Mode := ZMod 1) 1 with hatChi := fun _ => 0 }

@[simp] lemma trivEnv_fL (s : ZMod 1) : trivEnv.fL s = 0 := rfl
@[simp] lemma trivEnv_W1 (k : ZMod 1) : trivEnv.W1 k = 0 := rfl
@[simp] lemma trivEnv_W1omega (k : ZMod 1) : trivEnv.W1omega k = 0 := rfl
@[simp] lemma trivEnv_W1omega0 : trivEnv.W1omega0 = 0 := rfl
@[simp] lemma trivEnv_hatChi (k : ZMod 1) : trivEnv.hatChi k = 0 := rfl
@[simp] lemma trivEnv_hatChiSq (k : ZMod 1) : trivEnv.hatChiSq k = 0 := rfl
@[simp] lemma trivEnv_A (k : ZMod 1) : trivEnv.A k = 1 := rfl
@[simp] lemma trivEnv_B (k : ZMod 1) : trivEnv.B k = 0 := rfl

/-- The parameter point `FSParamsView` of `trivEnv`, transferred field by field
from the one of `fsEnv 1`: none of the fields of `FSParamsView` mentions the
kernels, so only the scalars, which the update leaves untouched, matter. -/
def trivEnv_view : Work.BoseB7.FSParamsView trivEnv :=
  let hv0 := FSParamsView_fsEnv (Mode := ZMod 1) (t := 1) one_pos le_rfl
    (paramsOK_fsParams_le_one one_pos le_rfl)
  { t := hv0.t, t_pos := hv0.t_pos, t_le_one := hv0.t_le_one, mu_eq := hv0.mu_eq,
    a_pos := hv0.a_pos, Kl_eq := hv0.Kl_eq, KH_eq := hv0.KH_eq, d_eq := hv0.d_eq,
    s_eq := hv0.s_eq, eT_eq := hv0.eT_eq, KL_eq := hv0.KL_eq, ell_eq := hv0.ell_eq,
    bigM_eq := hv0.bigM_eq, intM_eq := hv0.intM_eq, paramsOK := hv0.paramsOK,
    z_ne := hv0.z_ne, rho_close := hv0.rho_close, one_le_Kl := hv0.one_le_Kl,
    one_le_KL := hv0.one_le_KL, one_le_KH := hv0.one_le_KH, one_le_bigM := hv0.one_le_bigM,
    lille_le_delta := hv0.lille_le_delta, delta_le_one := hv0.delta_le_one }

/-! ## 4. Elementary facts about the witness -/

/-- On the one-mode lattice the high-momentum region `P_H^q` (and hence `P_H`)
is empty: it asks for `1/(4K_Ha) ≤ ‖kmom 0‖ = 0` while `1/(4K_Ha) > 0`.  This
kills the four `Q3Kernel` fields that are implications guarded by `P_H^q`. -/
lemma trivNotPHq (q : ZMod 1) : ¬ trivFock.PHq trivEnv.KH trivEnv.aScat q := by
  intro h
  have hKH : 0 < trivEnv.KH := lt_of_lt_of_le zero_lt_one trivEnv_view.one_le_KH
  have hpos : 0 < 1 / (4 * trivEnv.KH * trivEnv.aScat) := by
    apply one_div_pos.mpr
    have ha := trivEnv_view.a_pos
    nlinarith
  have hnorm : ‖trivFock.kmom q‖ = 0 := by simp
  rw [FockData.PHq, hnorm] at h
  linarith

lemma trivKlKL_nonneg : (0 : ℝ) ≤ trivEnv.Kl * trivEnv.KL :=
  mul_nonneg (le_trans zero_le_one trivEnv_view.one_le_Kl)
    (le_trans zero_le_one trivEnv_view.one_le_KL)

lemma trivKH_pos : 0 < trivEnv.KH := lt_of_lt_of_le zero_lt_one trivEnv_view.one_le_KH

/-- `ρ_z > 0` at the witness: `|ρ_z - μ| ≤ μ/2` (FS `eq:Close`) and `μ > 0`. -/
lemma trivRho_pos : 0 < trivEnv.rho := by
  have hmu : 0 < trivEnv.mu := by
    have h : 0 < trivEnv.mu * trivEnv.aScat ^ 3 := by
      rw [trivEnv_view.mu_eq]; exact trivEnv_view.t_pos
    exact pos_of_mul_pos_left h (le_of_lt (pow_pos trivEnv_view.a_pos 3))
  have h := (abs_le.mp trivEnv_view.rho_close).1
  linarith

/-! ## 5. The kernel at the witness -/

/-- `Q3Kernel K₀` holds at the degenerate witness for every `K₀ ≥ 0`: both sides
of the `K₀`-bounds are `0` (all sums run over the empty `excited (ZMod 1)`, and
all the kernels and the number operators vanish), and all the implications are
vacuous (guarded by `f_L ≡ 0` or by the empty `P_H^q`). -/
theorem trivQ3Kernel (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    Work.BoseB7A.Q3Kernel K₀ trivFock trivTilde trivEnv where
  W1_le := by
    intro k
    simp only [trivEnv_W1, abs_zero]
    exact mul_nonneg hK₀ (le_of_lt trivEnv_view.a_pos)
  W1_even := by intro k; simp
  A_even := by intro k; simp
  B_even := by intro k; simp
  B_eq := by intro k; simp
  AB := by intro k; simp
  A_ge := by intro q _; simp
  fL_nonneg := by intro s; simp
  fL_le_one := by intro s; simp
  fL_even := by intro s; simp
  fL_supp := by intro s h; exact absurd rfl h
  kmom_sub := by intro s k h hk; exact absurd rfl h
  hasKernel := by intro i j; simp
  hatChiSq_le := by intro s; simp
  hatChi_le := by intro s; simp
  hatChi_even := by intro s; simp
  hatChiSq_even := by intro s; simp
  hatChi_small := by intro q hq; exact absurd hq (trivNotPHq q)
  ccrX_small := by intro s q hs hq; exact absurd rfl hs
  hatChiSq_form := by
    intro S c v hS
    have hS0 : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact hS s hs (Subsingleton.elim s 0)
    subst hS0
    simp
  count_PL := by
    rw [excited_zmod1]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hK₀ (pow_nonneg trivKlKL_nonneg 3)
  sum_hatChiSq := by
    rw [excited_zmod1]
    simp only [Finset.sum_empty]
    exact hK₀
  tail_hatChiSq := by
    rw [excited_zmod1]
    simp only [Finset.sum_empty]
    exact mul_nonneg hK₀ (Real.rpow_nonneg trivKlKL_nonneg _)
  sum_W1sq := by
    rw [excited_zmod1]
    simp only [Finset.filter_empty, Finset.sum_empty, mul_zero]
    exact mul_nonneg hK₀ (le_of_lt trivEnv_view.a_pos)
  alpha_lip := by intro p q hp hq; exact absurd hp (trivNotPHq p)
  W1omega0_nonneg := by simp
  W1omega0_le := by
    simp only [trivEnv_W1omega0]
    exact mul_nonneg hK₀ (le_of_lt trivEnv_view.a_pos)
  intOne := by
    simp only [trivEnv_W1omega0, mul_zero, trivEnv_W1, zero_mul, Finset.sum_const_zero,
      sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK₀ (le_of_lt trivRho_pos))
      (le_of_lt trivEnv_view.a_pos)) (inv_nonneg.mpr (le_of_lt trivKH_pos))
  q2exLower := by
    intro Ψ
    have hQ : trivFock.Q2ex trivEnv = 0 := by
      rw [FockData.Q2ex, excited_zmod1]; simp
    have hG : trivTilde.gapOpT trivEnv = 0 := by
      rw [TildeData.gapOpT]; simp
    have hL : 2 * trivEnv.rho * trivEnv.W1omega0 *
        trivFock.qw Ψ (trivTilde.Gop trivEnv) = 0 := by simp
    have hq : trivFock.qw Ψ (0 : trivFock.H →ₗ[ℝ] trivFock.H) = 0 := by
      simp only [FockData.qw, LinearMap.zero_apply, map_zero]
    rw [hL, hQ, hG, hq]
    simp

/-! ## 6. The target -/

theorem Q3Kernel_inhabited (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ (F : Work.BoseB7.FockData (ZMod 1)) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env (ZMod 1)) (hv : Work.BoseB7.FSParamsView E),
      Work.BoseB7A.Q3Kernel K₀ F T E :=
  ⟨trivFock, trivTilde, trivEnv, trivEnv_view, trivQ3Kernel K₀ hK₀⟩

end Work.BoseB7A
