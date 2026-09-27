import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.EG.scal_defs
import Submission.Work.KT.Fund.kappa_mul

/-!
# `Work.KT.EG.kappa_twist_fund` — the twist by a power of the coordinate unit

Same statement and proof as `Submission/Work/KT/EG/kappa_twist.lean`, but importing the (now proved)
`Submission.Work.KT.Fund.kappa_mul` rather than the temporary local copy
`Submission.Work.KT.EG.kappa_mul_local`; the two cannot both be in one module's import closure, and
this version is the one compatible with the modules `Submission.Work.KT.EG.kappa_lin_gen` and
`Submission.Work.KT.EG.kappa_reduce` need.
-/

namespace Work.KT.EG

noncomputable section

set_option linter.unusedSectionVars false

/-- Multiplicativity of the reduced clutched class for commuting units. -/
lemma tf_redK_mul_comm (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {m : ℕ}
    (u v : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (huv : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
          * (v : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
        = (v : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
          * (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))) :
    redK X m (u * v) = redK X m u + redK X m v := by
  rw [redK, redK, redK, Work.KT.Fund.kappa_mul X m u v huv]
  abel

/-- The `m × m` scalar matrix unit has reduced class `m` times that of the `1 × 1` one. -/
lemma tf_redK_scalUnit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ) :
    redK X m (scalUnit X m c) = m • redK X 1 (scalUnit X 1 c) := by
  induction m with
  | zero =>
      have h : scalUnit X 0 c = 1 := Units.ext (Subsingleton.elim _ _)
      rw [h, redK_one, zero_smul]
  | succ m ih =>
      have key : redK X (m + 1) (scalUnit X (m + 1) c)
          = redK X m (scalUnit X m c) + redK X 1 (scalUnit X 1 c) :=
        redK_add X (scalUnit X (m + 1) c) (scalUnit X m c) (scalUnit X 1 c)
          (scalUnit_succ X m c)
      rw [key, ih, succ_nsmul]

/-- `1 × 1` matrices commute. -/
lemma tf_oneByOne_mul_comm {R : Type} [CommRing R] (u v : Matrix (Fin 1) (Fin 1) R) :
    u * v = v * u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]

/-- Multiplicativity of `redK` in the `1 × 1` case (there all units commute). -/
lemma tf_redK_oneByOne_mul (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (u v : (Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))ˣ) :
    redK X 1 (u * v) = redK X 1 u + redK X 1 v :=
  tf_redK_mul_comm X u v (tf_oneByOne_mul_comm _ _)

/-- `n • (-x) = -(n • x)` in an additive commutative group. -/
lemma tf_nsmul_neg_local {A : Type} [AddCommGroup A] (n : ℕ) (x : A) :
    n • (-x) = -(n • x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ih, succ_nsmul]; abel

/-- Powers in the `1 × 1` case: `redK (B^N) = N • redK B`. -/
lemma tf_redK_oneByOne_pow (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (B : (Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))ˣ) (N : ℕ) :
    redK X 1 (B ^ N) = N • redK X 1 B := by
  induction N with
  | zero => rw [pow_zero, redK_one, zero_smul]
  | succ N ih => rw [pow_succ, tf_redK_oneByOne_mul, ih, succ_nsmul]

/-- The Bott class in the `1 × 1` case: `redK X 1 (z^{-N}) = -N • bottZ X`. -/
lemma tf_redK_zUnitMat_zpow (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (N : ℕ) :
    redK X 1 ((Work.KT.Fund.zUnitMat X) ^ (-(N : ℤ))) = -((N : ℕ) • bottZ X) := by
  have hz : (Work.KT.Fund.zUnitMat X) ^ (-(N : ℤ))
      = ((Work.KT.Fund.zUnitMat X)⁻¹) ^ N := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
  rw [hz, tf_redK_oneByOne_pow]
  have h2 : redK X 1 ((Work.KT.Fund.zUnitMat X)⁻¹)
      = - redK X 1 (Work.KT.Fund.zUnitMat X) := by
    have h3 := tf_redK_oneByOne_mul X ((Work.KT.Fund.zUnitMat X)⁻¹) (Work.KT.Fund.zUnitMat X)
    first
    | rw [inv_mul_cancel, redK_one] at h3
    | rw [Units.inv_mul, redK_one] at h3
    exact eq_neg_iff_add_eq_zero.mpr h3.symm
  rw [h2, tf_nsmul_neg_local]
  first
  | rfl
  | rw [bottZ]

/-- **The twist by a power of the coordinate unit.** For a unit `W` of matrices over
`C(X × S¹, ℂ)` and a unit `V` whose values are `z^{-N} • W` (scalar multiplication by the `-N`-th
power of the coordinate unit `z`), the reduced clutched class changes by `N * m` copies of the
Bott class: `redK X m V = redK X m W - (N * m) • bottZ X`.

Route. `z^{-N} • 1_m` is a *scalar* matrix, so it commutes with `W`, and multiplicativity of the
clutched class (`Fund.kappa_mul`, for commuting units) gives
`redK (z^{-N} • 1_m * W) = redK (z^{-N} • 1_m) + redK W`; then
`redK X m (z^{-N} • 1_m) = m • redK X 1 (z^{-N})` by block additivity
(`Work.KT.EG.redK_add`, from `Fund.kappa_add`), and `redK X 1 (z^{-k}) = -k • bottZ X` by
multiplicativity for the single `1 × 1` unit `Fund.zUnitMat` together with `Work.KT.Fund.kappa_one`.

If `Submission/Work/KT/Fund/kappa_mul.lean` still contains a `sorry` when you work, prove the
multiplicativity you need yourself — for the scalar case `κ (c • W)` with `c` a `1 × 1` unit this
is a small special case of Whitehead's factorization for block matrices (route: `Fund.kappa_add`,
`Work.KT.whitehead_diag`, `Work.KT.elem_lift`, `Fund.kappa_const`, `Fund.kappa_homotopic`) — and
do not import any result that is still `sorry`-ed. -/
theorem kappa_twist_fund (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (m N : ℕ)
    (W V : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hV : (V : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
      = (((Work.KT.zUnit X) ^ (-(N : ℤ)) : (C(X × Sph ℂ, ℂ))ˣ) : C(X × Sph ℂ, ℂ))
          • (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))) :
    Work.KT.EG.redK X m V = Work.KT.EG.redK X m W - (N * m) • Work.KT.EG.bottZ X := by
  have hVeq : V = scalUnit X m ((Work.KT.zUnit X) ^ (-(N : ℤ))) * W := by
    refine Units.ext ?_
    rw [hV, scalUnit_mul_val]
  have h1 : redK X m V
      = redK X m (scalUnit X m ((Work.KT.zUnit X) ^ (-(N : ℤ)))) + redK X m W := by
    rw [hVeq]
    exact tf_redK_mul_comm X _ _ (scalUnit_comm X m ((Work.KT.zUnit X) ^ (-(N : ℤ))) W)
  have h2 : redK X m (scalUnit X m ((Work.KT.zUnit X) ^ (-(N : ℤ))))
      = -(((N * m : ℕ)) • bottZ X) := by
    rw [tf_redK_scalUnit, scalUnit_zpow, scalUnit_zUnit, tf_redK_zUnitMat_zpow]
    rw [tf_nsmul_neg_local, ← mul_nsmul', Nat.mul_comm m N]
  rw [h1, h2]
  abel


end

end Work.KT.EG
