import Mathlib
import Submission.Work.StemsB.wangCollarDerivDefs
import Submission.Work.StemsB.wangTauS

/-!
# The twisted Wang transgression and its derivation property

The geometric transgression `θ = ρ ∘ Σ ∘ λ_G^*` of `wangCollarDerivDefs` satisfies
(`wangTheta_cup`)

`θ(a ⌣ b) = (-1)^{|a|} a ⌣ θ(b) + (-1)^{b(n'+1)} θ(a) ⌣ b`,

which differs from the derivation property of the Wang transgression,
`θ(a ⌣ b) = θ(a) ⌣ b + (-1)^{(b-1)|a|} a ⌣ θ(b)`, by a *degree-dependent* sign.  Since the
family `τS` is free in the statement of the Wang transgression, the fix is to twist by the scalar
family `c_n = (-1)^{b n}` (a genuine sign, `c_n² = 1`): the twisted transgression
`ω_n = c_n • θ_n` satisfies the derivation property in exactly the form required by
`Work.StemsB.WangCohShiftDerivation`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-! ## The twist scalar -/

/-- The twist scalar `c_n = ((-1)^b)^n = (-1)^{b n}`. -/
noncomputable def wangSgn (b n : ℕ) : ℤ := ((-1 : ℤ) ^ b) ^ n

theorem wangSgn_add (b m n : ℕ) : wangSgn b (m + n) = wangSgn b m * wangSgn b n :=
  pow_add _ _ _

theorem wangSgn_eq (b n : ℕ) : wangSgn b n = (-1 : ℤ) ^ (b * n) := by
  rw [wangSgn, pow_mul]

theorem wangSgn_sq (b n : ℕ) : wangSgn b n * wangSgn b n = 1 := by
  have h2 : ((-1 : ℤ) ^ b) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨b, by ring⟩
  rw [← wangSgn_add, show n + n = 2 * n from by ring, wangSgn, pow_mul, h2, one_pow]

theorem wangNegOnePow_mul_self (m : ℕ) : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
  rw [← pow_add, show m + m = 2 * m from by ring, pow_mul]
  have h2 : ((-1 : ℤ)) ^ 2 = 1 := by norm_num
  rw [h2, one_pow]

theorem neg_one_pow_pred_mul (b m : ℕ) (hb : 1 ≤ b) :
    (-1 : ℤ) ^ ((b - 1) * m) = (-1 : ℤ) ^ (b * m + m) := by
  have h : (b - 1) * m + m = b * m := by
    have h1 : (b - 1) * m + 1 * m = b * m := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hb]
    rwa [one_mul] at h1
  calc (-1 : ℤ) ^ ((b - 1) * m)
      = (-1) ^ ((b - 1) * m) * ((-1) ^ m * (-1) ^ m) := by
        rw [wangNegOnePow_mul_self, mul_one]
    _ = ((-1) ^ ((b - 1) * m) * (-1) ^ m) * (-1) ^ m := by ring
    _ = (-1) ^ (b * m) * (-1) ^ m := by rw [← pow_add, h]
    _ = (-1) ^ (b * m + m) := by rw [pow_add]

/-- **The first twist identity**: `c_{n+n'+b} · (-1)^{b(n'+1)} · c_n = 1`. -/
theorem wangSgn_mul_neg_one (b n n' : ℕ) :
    wangSgn b (n + n' + b) * (-1 : ℤ) ^ (b * (n' + 1)) * wangSgn b n = 1 := by
  have h1 : wangSgn b (n + n' + b) = wangSgn b n * wangSgn b n' * wangSgn b b := by
    rw [show n + n' + b = (n + n') + b from by ring, wangSgn_add, wangSgn_add]
  have h2 : (-1 : ℤ) ^ (b * (n' + 1)) = wangSgn b n' * (-1 : ℤ) ^ b := by
    rw [mul_add, mul_one, pow_add, ← wangSgn_eq]
  have h3 : wangSgn b b * (-1 : ℤ) ^ b = 1 := by
    have hstep : wangSgn b b * (-1 : ℤ) ^ b = ((-1 : ℤ) ^ b) ^ (b + 1) := by
      rw [wangSgn, pow_succ]
    rw [hstep, ← pow_mul]
    exact Even.neg_one_pow (Nat.even_mul_succ_self b)
  rw [h1, h2]
  calc (wangSgn b n * wangSgn b n' * wangSgn b b) * (wangSgn b n' * (-1 : ℤ) ^ b) * wangSgn b n
      = (wangSgn b n * wangSgn b n) * (wangSgn b n' * wangSgn b n')
          * (wangSgn b b * (-1 : ℤ) ^ b) := by ring
    _ = 1 := by rw [wangSgn_sq, wangSgn_sq, h3]; ring

/-- **The second twist identity**: `c_{n+n'+b} · (-1)^{n+b} · c_{n'} = (-1)^{(b-1)(n+b)}`. -/
theorem wangSgn_mul_neg_one' (b n n' : ℕ) (hb : 1 ≤ b) :
    wangSgn b (n + n' + b) * (-1 : ℤ) ^ (n + b) * wangSgn b n'
      = (-1 : ℤ) ^ ((b - 1) * (n + b)) := by
  have h1 : wangSgn b (n + n' + b) = wangSgn b n * wangSgn b n' * wangSgn b b := by
    rw [show n + n' + b = (n + n') + b from by ring, wangSgn_add, wangSgn_add]
  have h2 : wangSgn b n = (-1 : ℤ) ^ (b * n) := wangSgn_eq b n
  have h3 : wangSgn b b = (-1 : ℤ) ^ (b * b) := wangSgn_eq b b
  have h4 : wangSgn b n' * wangSgn b n' = 1 := wangSgn_sq b n'
  rw [neg_one_pow_pred_mul b (n + b) hb, h1, h2, h3]
  calc (-1 : ℤ) ^ (b * n) * wangSgn b n' * (-1 : ℤ) ^ (b * b) * (-1 : ℤ) ^ (n + b) * wangSgn b n'
      = (-1 : ℤ) ^ (b * n) * (-1 : ℤ) ^ (b * b) * (-1 : ℤ) ^ (n + b)
          * (wangSgn b n' * wangSgn b n') := by ring
    _ = (-1 : ℤ) ^ (b * n) * (-1 : ℤ) ^ (b * b) * (-1 : ℤ) ^ (n + b) := by rw [h4, mul_one]
    _ = (-1 : ℤ) ^ (b * n + b * b + (n + b)) := by rw [← pow_add, ← pow_add]
    _ = (-1 : ℤ) ^ (b * (n + b) + (n + b)) := by
        congr 1
        ring

/-! ## The twisted transgression -/

/-- The negation isomorphism of a `ℤ`-module, built from the preadditive structure alone. -/
noncomputable def wangNegIso (M : ModuleCat ℤ) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  inv_hom_id := by rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]

theorem wangNegIso_hom_apply (M : ModuleCat ℤ) (x : M) : (wangNegIso M).hom x = -x := by
  show (-𝟙 M).hom x = -x
  rw [ModuleCat.hom_neg]
  simp

theorem wangSgn_eq_one_or_neg (b n : ℕ) : wangSgn b n = 1 ∨ wangSgn b n = -1 := by
  have hb := neg_one_pow_eq_or (R := ℤ) b
  rcases hb with h | h
  · left; rw [wangSgn, h, one_pow]
  · rcases neg_one_pow_eq_or (R := ℤ) n with h' | h'
    · left; rw [wangSgn, h, h']
    · right; rw [wangSgn, h, h']

/-- The sign isomorphism of a `ℤ`-module: multiplication by `wangSgn b n = ±1`. -/
noncomputable def wangSignIso (b n : ℕ) (M : ModuleCat ℤ) : M ≅ M :=
  if wangSgn b n = 1 then Iso.refl M else wangNegIso M

theorem wangSignIso_hom_apply (b n : ℕ) (M : ModuleCat ℤ) (x : M) :
    (wangSignIso b n M).hom x = wangSgn b n • x := by
  unfold wangSignIso
  split_ifs with h
  · rw [h, one_smul]; rfl
  · have h' : wangSgn b n = -1 := (wangSgn_eq_one_or_neg b n).resolve_left h
    rw [wangNegIso_hom_apply, h', show (-1 : ℤ) = -(1 : ℤ) from rfl, neg_zsmul, one_smul]

/-- **The twisted Wang transgression** `ω_n = c_n • θ_n`, `c_n = (-1)^{b n}`. -/
noncomputable def wangThetaTw (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ (n + b) (wangCohFsp b p) →ₗ[ℤ]
      Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p) :=
  wangSgn b n • wangTheta b hb p d_G hT_G hT_O n

/-- The twisted target transport `τS'`: the untwisted `τS` followed by multiplication by `c_n`. -/
noncomputable def wangTauSTw (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of E) (wangA b p)).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p) :=
  wangTauS b hb E p hT_O d_G hT_G n ≪≫
    wangSignIso b n (Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p))

/-- **The value of the twisted transgression**: the Wang transgression built from the twisted
`τS'` is `ω = c • θ`. -/
theorem wangCohShiftθ_tw_apply (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ)
    (a : Work.Cohomology.singularCohomology ℤ (n + b) (wangCohFsp b p)) :
    (wangCohShiftθ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
      (wangGammaExplicit b p hT_O) (wangTauSTw b hb E p hT_O d_G hT_G) n).hom a
      = wangThetaTw b hb p d_G hT_G hT_O n a := by
  have hval := by
    simpa only [wangCohShiftθ, ModuleCat.hom_comp, LinearMap.comp_apply]
      using wangTauS_value b hb E p hT_O d_G hT_G n a
  show (wangSignIso b n (Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p))).hom
      ((wangTauS b hb E p hT_O d_G hT_G n).hom
        ((Work.Cohomology.pairδ ℤ (TopCat.of E) (wangA b p) (n + b)).hom
          ((wangGammaExplicit b p hT_O (n + b)).inv a)))
      = wangSgn b n • wangTheta b hb p d_G hT_G hT_O n a
  rw [wangSignIso_hom_apply]
  exact congrArg (fun y => wangSgn b n • y) hval

end

end Work.StemsB
