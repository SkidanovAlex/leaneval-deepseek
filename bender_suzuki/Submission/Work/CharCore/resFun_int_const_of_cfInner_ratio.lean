import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.Induction.isVChar_resFun
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-!
# `Work.CharCore.resFun_int_const_of_cfInner_ratio`

Let `V` be a virtual character of a finite group `G` and let `W = Res_Q^G V` be its
restriction to a subgroup `Q`.  If `z₀` is an irreducible character of `Q` of degree `1`
and the multiplicities of **all** non-trivial irreducible characters of `Q` in `W` are
proportional to their degrees with the single ratio `⟨z₀, W⟩`,

`⟨z, W⟩ = z(1) · ⟨z₀, W⟩   for every `z ∈ Irr Q`, `z ≠ 1`,

then `W` is constant on the non-identity elements of `Q`.

## Proof

Write `a = ⟨W, z₀⟩` and `b = ⟨W, 1⟩`; both are integers because `cfInner` of two virtual
characters is an integer (`Work.CharCore.cfInner_int_vchar`).  Since `z₀ 1 = 1`, the
hypothesis reads `⟨z, W⟩ = z(1) · a` for `z ≠ 1`; as `a` and `z(1)` are (real) integral,
conjugating with `Work.CharCore.cfInner_conj_symm` gives the same formula for the
coefficients `⟨W, z⟩` which occur in the Fourier expansion of `W`.  Therefore the class
function

`g = a · reg_Q + (b - a) · 1`

(where `reg_Q` is the regular character of `Q`, so `reg_Q = ∑_z z(1) · z`) has the same
inner product with every irreducible character of `Q` as `W`:  for `z = 1` both are `b`,
and for `z ≠ 1` both are `z(1) · a`.  A class function orthogonal to all irreducible
characters vanishes (`Work.CharCore.classFun_eq_zero_of_orthogonal`), so `W = g`.
Evaluating at `y ≠ 1` gives `W y = b - a`, an integer.
-/
theorem resFun_int_const_of_cfInner_ratio {G : Type} [Group G] [Fintype G] {Q : Subgroup G}
    [Fintype ↥Q] {V : G → ℂ} (hV : Work.CharCore.IsVChar V)
    (hVc : Work.CharCore.IsClassFun V)
    {z0 : ↥Q → ℂ} (hz0 : z0 ∈ Work.CharCore.Irr ↥Q) (hz01 : z0 ≠ 1) (hz0lin : z0 1 = 1)
    (horth : ∀ z ∈ Work.CharCore.Irr ↥Q, z ≠ 1 →
      (z0 1) * Work.CharCore.cfInner z (Work.Induction.resFun Q V)
        = (z 1) * Work.CharCore.cfInner z0 (Work.Induction.resFun Q V)) :
    ∃ c : ℤ, ∀ y : ↥Q, y ≠ 1 → Work.Induction.resFun Q V y = (c : ℂ) := by
  classical
  -- `W` is the restriction of `V` to `Q`.
  set W : ↥Q → ℂ := Work.Induction.resFun Q V with hW
  -- `W` is a virtual character of `Q`, hence a class function.
  have hWV : Work.CharCore.IsVChar W := by
    rw [hW]
    convert Work.Induction.isVChar_resFun (G := G) (H := Q) (φ := V) hV using 1
  have hWc : Work.CharCore.IsClassFun W := Work.CharCore.IsVChar.isClassFun hWV
  -- the trivial character of `Q` is irreducible
  have h1mem : (1 : ↥Q → ℂ) ∈ Work.CharCore.Irr ↥Q := Work.CharCore.principalChar_mem_Irr
  -- the two inner products `a = ⟨W, z₀⟩` and `b = ⟨W, 1⟩` are integers
  obtain ⟨a, ha⟩ := Work.CharCore.cfInner_int_vchar (G := ↥Q) hWV
    (Work.CharCore.IsVChar.of_mem_Irr hz0)
  obtain ⟨b, hb⟩ := Work.CharCore.cfInner_int_vchar (G := ↥Q) hWV
    (Work.CharCore.IsVChar.of_mem_Irr h1mem)
  -- `⟨z₀, W⟩ = a` as well (`cfInner` is conjugate symmetric and `a` is real)
  have hz0W : Work.CharCore.cfInner z0 W = (a : ℂ) := by
    rw [Work.CharCore.cfInner_conj_symm, ha]
    simp
  -- the Fourier coefficients of `W` at the non-trivial irreducible characters
  have hkey : ∀ z ∈ Work.CharCore.Irr ↥Q, z ≠ 1 →
      Work.CharCore.cfInner W z = (z 1) * (a : ℂ) := by
    intro z hz hzne
    have h := horth z hz hzne
    rw [hz0lin, one_mul] at h
    have hzW : Work.CharCore.cfInner z W = (z 1) * (a : ℂ) := by rw [h, hz0W]
    rw [Work.CharCore.cfInner_conj_symm, hzW, Work.CharCore.irrDeg_spec hz]
    simp
  -- the comparison class function `g = a · reg_Q + (b - a) · 1`
  set g : ↥Q → ℂ :=
    (a : ℂ) • Work.CharCore.regularChar ↥Q + ((b - a : ℤ) : ℂ) • (1 : ↥Q → ℂ) with hg
  have hgclass : Work.CharCore.IsClassFun g := by
    rw [hg]
    exact Work.CharCore.IsClassFun.add
      (Work.CharCore.IsClassFun.smul (a : ℂ) (Work.CharCore.isClassFun_regularChar ↥Q))
      (Work.CharCore.IsClassFun.smul ((b - a : ℤ) : ℂ)
        (Work.CharCore.isClassFun_of_mem_Irr h1mem))
  -- `⟨g, z⟩ = a · z(1) + (b - a) · [z = 1]`
  have hcf_g : ∀ z ∈ Work.CharCore.Irr ↥Q,
      Work.CharCore.cfInner g z =
        (a : ℂ) * (z 1) + ((b - a : ℤ) : ℂ) * (if (1 : ↥Q → ℂ) = z then 1 else 0) := by
    intro z hz
    rw [hg, Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_smul_left,
      Work.CharCore.cfInner_smul_left, Work.CharCore.cfInner_regularChar hz,
      Work.CharCore.irr_orthonormal (1 : ↥Q → ℂ) z h1mem hz,
      Work.CharCore.irrDeg_spec hz]
  -- `W` and `g` have the same inner product with every irreducible character, so `W = g`
  have hWg : W = g := by
    refine sub_eq_zero.mp (Work.CharCore.classFun_eq_zero_of_orthogonal (hWc.sub hgclass) ?_)
    intro z hz
    rw [Work.CharCore.cfInner_sub_left, hcf_g z hz]
    by_cases hz1 : z = 1
    · -- trivial character: both inner products are `b`
      rw [hz1, hb]
      norm_num
    · -- non-trivial character: both inner products are `z(1) · a`
      have hnot : (1 : ↥Q → ℂ) ≠ z := fun hc => hz1 hc.symm
      have hif : (if (1 : ↥Q → ℂ) = z then (1 : ℂ) else 0) = 0 := by simp [hnot]
      rw [hkey z hz hz1, hif]
      ring
  -- evaluate: `W` is the constant `b - a` off the identity
  refine ⟨b - a, fun y hy => ?_⟩
  rw [hWg, hg]
  have hreg : Work.CharCore.regularChar ↥Q y = 0 := by
    simp [Work.CharCore.regularChar, hy]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hreg, mul_zero, zero_add,
    Pi.one_apply, mul_one]

end Work.CharCore
