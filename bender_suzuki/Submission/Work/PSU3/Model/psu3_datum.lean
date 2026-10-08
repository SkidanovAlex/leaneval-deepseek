/-
# `psu3_datum`: the model rank-one datum of `PSU(3,2ⁿ)` (design node D1)

The model `Y = PSU(3,2ⁿ)` (`LeanEval.GroupTheory.Defs.PSU3Model n`) carries a
`ModelRankOneDatum` with coordinates `C = SZ (GF(2^(2n)))` and `fC = fMapTot`:

* `H = psu3B n` (the Borel), `Q = psu3U n` (the unipotent radical), `t = psu3Weyl n`
  (the Weyl involution) — the split rank-one datum is `psu3_isSplitRankOne`;
* `Y` is simple (`isSimpleGroup_PSU3Model`);
* the coordination `c : SZ (E n) ≃* Ū` is the matrix model `pglHom`, which is an
  isomorphism onto the unipotent radical (`uEquivHom_bijective`);
* the `f`-relation is read off the matrix identity `weylConj_matFun`
  (`J·A(p)·J = weylFactor(p)·J·A(f p)`), after exhibiting `weylFactor(x,y)` for
  `y ≠ 0` as the product of the torus element `diag(σy, σy/y, y)` with the unipotent
  element `u(σy·x/y, σy)` — hence an element of the Borel `suB n = suU n ⊔ suT n`.

Everything here is a strengthening of the already delivered pieces D1a
(`psu3_isSplitRankOne`) and D1b (`psu3_uEquiv`); the only new mathematics is the
decomposition of `weylFactor` inside the Borel.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.PSU3.ModelGL
import Submission.Work.PSU3.ModelGL.Injectivity
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.Model.psu3_isSplitRankOne
import Submission.Work.PSU3.Model.psu3_uEquiv
import Submission.Work.PSU3.Model.weylConj_matFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Work.PSU3.Model

/-! ## 1.  Elementary `σ`-facts for `E n = GF(2^{2n})` -/

lemma pow_sigma (n : ℕ) (z : E n) : (σE z) ^ (2 ^ n) = z := by
  have h : σE (σE z) = z := σE_σE z
  rwa [show σE z = z ^ 2 ^ n from rfl] at h

lemma sigma_ne_zero {n : ℕ} {y : E n} (hy : y ≠ 0) : σE y ≠ 0 :=
  fun h => hy (by have h' := congrArg σE h; simpa using h')

lemma inv_sigma_pow (n : ℕ) (y : E n) (hy : y ≠ 0) :
    ((σE y) ^ (2 ^ n - 1))⁻¹ = σE y * y⁻¹ := by
  have hσy : σE y ≠ 0 := sigma_ne_zero hy
  have hn : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_sub₀ _ hσy hn, pow_one, pow_sigma, _root_.mul_inv_rev, inv_inv]

/-! ## 2.  The Weyl factor and its decomposition in the Borel -/

/-- The matrix `weylFactor x y`, exhibited as an element of `GL(3, E)`: it is the product
of the torus element `diag(σy, σy/y, y)` (namely `suTg n (σy)⁻¹`) with the unipotent
element `u(σy·x/y, σy)` (namely `suUg n _ _`). -/
noncomputable def weylFactorGL (n : ℕ) (x y : E n) (hy : y ≠ 0)
    (hherm : y + σE y = x * σE x) : GL (Fin 3) (E n) :=
  Submission.PSU3.suTg n (Units.mk0 (σE y) (sigma_ne_zero hy))⁻¹ *
    Submission.PSU3.suUg n (σE y * x / y) (σE y)

lemma weylFactorGL_coe (n : ℕ) (x y : E n) (hy : y ≠ 0) (hherm : y + σE y = x * σE x) :
    ((weylFactorGL n x y hy hherm : GL (Fin 3) (E n)) : Matrix (Fin 3) (Fin 3) (E n)) =
      Work.PSU3.weylFactor x y := by
  have hσy : σE y ≠ 0 := sigma_ne_zero hy
  have hpow : (σE y) ^ (2 ^ n) = y := pow_sigma n y
  have hyq : y ^ (2 ^ n) = σE y := (show σE y = y ^ 2 ^ n from rfl).symm
  have hxq : x ^ (2 ^ n) = σE x := (show σE x = x ^ 2 ^ n from rfl).symm
  rw [weylFactorGL, Matrix.GeneralLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.PSU3.suTg_coe, Submission.PSU3.suUg_coe, Submission.PSU3.suTmat,
      Submission.PSU3.suUmat, Work.PSU3.weylFactor, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal, mul_pow, div_pow, inv_pow, hpow, hyq, hxq, inv_sigma_pow n y hy,
      mul_inv_cancel₀ hσy, inv_mul_cancel₀ hσy]
  all_goals (field_simp; try ring)

/-- The unipotent factor `u(σy·x/y, σy)` lies in `suU`: the condition `c + c^q = b^{q+1}`
is exactly the Hermitian relation satisfied by `p = (x,y)`. -/
lemma suUg_weyl_mem_suU (n : ℕ) (x y : E n) (hy : y ≠ 0) (hherm : y + σE y = x * σE x) :
    Submission.PSU3.suUg n (σE y * x / y) (σE y) ∈ Submission.PSU3.suU n := by
  have hσy : σE y ≠ 0 := sigma_ne_zero hy
  have hpow : (σE y) ^ (2 ^ n) = y := pow_sigma n y
  have hyq : y ^ (2 ^ n) = σE y := (show σE y = y ^ 2 ^ n from rfl).symm
  have hxq : x ^ (2 ^ n) = σE x := (show σE x = x ^ 2 ^ n from rfl).symm
  refine ⟨σE y * x / y, σE y, ?_, rfl⟩
  have key : (σE y * x / y) ^ (2 ^ n + 1) = x * σE x := by
    rw [pow_succ, div_pow, mul_pow, hpow, hyq, hxq]
    field_simp
  rw [key, hpow]
  simpa [add_comm] using hherm

lemma weylFactorGL_mem_suB (n : ℕ) (x y : E n) (hy : y ≠ 0) (hherm : y + σE y = x * σE x) :
    weylFactorGL n x y hy hherm ∈ Submission.PSU3.suB n := by
  rw [Submission.PSU3.suB]
  show Submission.PSU3.suTg n (Units.mk0 (σE y) (sigma_ne_zero hy))⁻¹ *
      Submission.PSU3.suUg n (σE y * x / y) (σE y) ∈
        Submission.PSU3.suU n ⊔ Submission.PSU3.suT n
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨_, rfl⟩)
    (Subgroup.mem_sup_left (suUg_weyl_mem_suU n x y hy hherm))

lemma weylFactorGL_mem_SU3 (n : ℕ) (x y : E n) (hy : y ≠ 0) (hherm : y + σE y = x * σE x) :
    weylFactorGL n x y hy hherm ∈ Submission.PSU3.SU3 n :=
  Submission.PSU3.suB_le_SU3 n (weylFactorGL_mem_suB n x y hy hherm)

/-! ## 3.  The Weyl conjugation at the level of `GL(3,E)` -/

theorem suSg_mul_matGL_mul_suSg (n : ℕ) (p : SZ (E n)) (hp : p ≠ 1) :
    Submission.PSU3.suSg n * matGL p * Submission.PSU3.suSg n =
      weylFactorGL n p.x p.y (SZ.y_ne_zero_of_ne_one hp) p.herm * Submission.PSU3.suSg n *
        matGL (SZ.fMap p hp) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, matGL_coe, Submission.PSU3.suSg_coe,
    weylFactorGL_coe]
  exact weylConj_matFun p hp

/-! ## 4.  The Weyl conjugation in `PSU(3,2ⁿ)` -/

/-- The image in `PSU(3,2ⁿ)` of the matrix `weylFactor x y`. -/
noncomputable def weylFactorM (n : ℕ) (x y : E n) (hy : y ≠ 0)
    (hherm : y + σE y = x * σE x) : ↥(PSU3Model n) :=
  ⟨ProjGenLinGroup.mk (weylFactorGL n x y hy hherm), by
    rw [Submission.PSU3.PSU3Model_eq_map_SU3]
    exact Subgroup.mem_map.mpr ⟨weylFactorGL n x y hy hherm,
      weylFactorGL_mem_SU3 n x y hy hherm, rfl⟩⟩

lemma weylFactorM_mem_psu3B (n : ℕ) (x y : E n) (hy : y ≠ 0)
    (hherm : y + σE y = x * σE x) :
    weylFactorM n x y hy hherm ∈ Submission.PSU3.psu3B n := by
  rw [Submission.PSU3.psu3B]
  refine Subgroup.mem_map.mpr
    ⟨⟨weylFactorGL n x y hy hherm, weylFactorGL_mem_SU3 n x y hy hherm⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact weylFactorGL_mem_suB n x y hy hherm
  · exact Subtype.ext (Submission.PSU3.psu3Hom_apply n _)

/-- **The `f`-relation in the model**: `t · A(p) · t = weylFactor(p) · t · A(f p)` in
`PSU(3,2ⁿ)`, the projective form of `weylConj_matFun`. -/
theorem psu3_weylConj_pglHom (n : ℕ) (p : SZ (E n)) (hp : p ≠ 1) :
    Submission.PSU3.psu3Weyl n *
        (⟨pglHom p, pglHom_mem_PSU3Model n p⟩ : ↥(PSU3Model n)) *
        Submission.PSU3.psu3Weyl n =
      weylFactorM n p.x p.y (SZ.y_ne_zero_of_ne_one hp) p.herm *
        Submission.PSU3.psu3Weyl n *
        (⟨pglHom (SZ.fMap p hp), pglHom_mem_PSU3Model n (SZ.fMap p hp)⟩ :
          ↥(PSU3Model n)) := by
  apply Subtype.ext
  show ProjGenLinGroup.mk (Submission.PSU3.suSg n) * pglHom p *
      ProjGenLinGroup.mk (Submission.PSU3.suSg n) =
    ProjGenLinGroup.mk (weylFactorGL n p.x p.y (SZ.y_ne_zero_of_ne_one hp) p.herm) *
      ProjGenLinGroup.mk (Submission.PSU3.suSg n) * pglHom (SZ.fMap p hp)
  rw [pglHom_apply, pglHom_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg ProjGenLinGroup.mk (suSg_mul_matGL_mul_suSg n p hp)

/-! ## 5.  The model datum -/

/-- `uEquivHom n : SZ (E n) →* Ū` (the matrix model `pglHom`, restricted to `Ū`) is
bijective: injective by `pglHom_injective`, surjective by the explicit parametrisation
`u(b,c)` of the unipotent radical (`matGL_mk_eq_suUg`). -/
theorem uEquivHom_bijective (n : ℕ) (hn : 2 ≤ n) : Function.Bijective (uEquivHom n) := by
  refine ⟨?_, ?_⟩
  · intro p q hpq
    apply pglHom_injective
    rw [← uEquivHom_apply n p, ← uEquivHom_apply n q, hpq]
  · intro g
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨b, c, hcond, hyb⟩ := (Subgroup.mem_subgroupOf.mp hy :
      (y : GL (Fin 3) (Submission.PSU3.F n)) ∈ Submission.PSU3.suU n)
    have hh : c + σE c = b * σE b := by
      show c + c ^ 2 ^ n = b * b ^ 2 ^ n
      simpa [pow_succ'] using hcond
    refine ⟨⟨b, c, hh⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [uEquivHom_apply, pglHom_apply, matGL_mk_eq_suUg n b c hh]
    rw [← hyb, ← congrArg Subtype.val hys, Submission.PSU3.psu3Hom_apply]

/-- The isomorphism `SZ (E n) ≃* Ū` used as the coordination `c` of the model datum. -/
noncomputable def psu3UEquiv (n : ℕ) (hn : 2 ≤ n) :
    SZ (E n) ≃* ↥(Submission.PSU3.psu3U n) :=
  MulEquiv.ofBijective (uEquivHom n) (uEquivHom_bijective n hn)

lemma psu3UEquiv_apply (n : ℕ) (hn : 2 ≤ n) (p : SZ (E n)) :
    ((psu3UEquiv n hn p : ↥(Submission.PSU3.psu3U n)) : ↥(PSU3Model n)) =
      ⟨pglHom p, pglHom_mem_PSU3Model n p⟩ := rfl

/-- **Design node `psu3_datum`** (Stage D): `PSU3Model n` carries a `ModelRankOneDatum`
with coordinates `(SZ (E n), fMapTot)`. -/
theorem psu3_datum (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (Work.RankOneUniqueness.ModelRankOneDatum
      ↥(LeanEval.GroupTheory.Defs.PSU3Model n)
      (SZ (GaloisField 2 (2 * n))) Work.PSU3.fMapTot) := by
  refine ⟨{ H := Submission.PSU3.psu3B n
            Q := Submission.PSU3.psu3U n
            t := Submission.PSU3.psu3Weyl n
            split := psu3_isSplitRankOne n hn
            simple := Submission.PSU3.isSimpleGroup_PSU3Model n hn
            c := psu3UEquiv n hn
            frel := ?_ }⟩
  intro u hu
  refine ⟨weylFactorM n u.x u.y (SZ.y_ne_zero_of_ne_one hu) u.herm,
    weylFactorM_mem_psu3B n u.x u.y (SZ.y_ne_zero_of_ne_one hu) u.herm, ?_⟩
  rw [psu3UEquiv_apply, fMapTot_of_ne_one hu, psu3UEquiv_apply]
  exact psu3_weylConj_pglHom n u hu

end Work.PSU3.Model
