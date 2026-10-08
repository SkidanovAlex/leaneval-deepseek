import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.column_orthogonality_not_conj`

The non-conjugate case of the second orthogonality relation for complex characters of a
finite group: if `g` and `h` are not conjugate, then

`∑_{χ ∈ Irr G} χ g * conj (χ h) = 0`.

The proof uses the indicator `conjClassInd h` of the conjugacy class of `h`.  It is a class
function, so by `Work.CharCore.classFun_eq_sum_irr` it expands in the orthonormal basis of
irreducible characters,
`conjClassInd h = ∑_{χ ∈ Irr G} ⟨conjClassInd h, χ⟩ χ`,
and its Fourier coefficient is computed to be
`⟨conjClassInd h, χ⟩ = |G|⁻¹ * (∑_x conjClassInd h x) * conj (χ h)`, the first factor being
non-zero because `h` is conjugate to itself.  Evaluating the expansion at `g`, where
`conjClassInd h g = 0`, and cancelling the non-zero scalar gives the result.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

/-- The indicator function of the conjugacy class of `h`: it is `1` on the conjugates of `h`
and `0` elsewhere. -/
noncomputable def conjClassInd {G : Type*} [Group G] [Fintype G] (h : G) : G → ℂ :=
  fun x => if IsConj x h then 1 else 0

@[simp] theorem conjClassInd_apply {G : Type*} [Group G] [Fintype G] (h x : G) :
    conjClassInd h x = if IsConj x h then (1 : ℂ) else 0 := rfl

/-- A class function takes the same value at conjugate elements. -/
theorem IsClassFun.apply_eq_of_isConj {G : Type*} [Group G] {f : G → ℂ} (hf : IsClassFun f)
    {x y : G} (hxy : IsConj x y) : f x = f y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have h := hf x c
  rw [hc] at h
  exact h.symm

/-- `conjClassInd h` is a class function. -/
theorem isClassFun_conjClassInd {G : Type*} [Group G] [Fintype G] (h : G) :
    IsClassFun (conjClassInd h) := by
  intro x y
  simp only [conjClassInd_apply]
  have hy : IsConj (y * x * y⁻¹) x := (isConj_iff.mpr ⟨y, rfl⟩).symm
  have key : IsConj (y * x * y⁻¹) h ↔ IsConj x h :=
    ⟨fun hc => hy.symm.trans hc, fun hc => hy.trans hc⟩
  by_cases hx : IsConj x h
  · have hc : IsConj (y * x * y⁻¹) h := key.mpr hx
    rw [if_pos hc, if_pos hx]
  · have hc : ¬ IsConj (y * x * y⁻¹) h := fun h' => hx (key.mp h')
    rw [if_neg hc, if_neg hx]

/-- The sum against a class function `χ` of the conjugacy-class indicator, rewritten by
pulling the constant value `conj (χ h)` out of the sum. -/
theorem sum_conjClassInd_mul {G : Type*} [Group G] [Fintype G] (h : G) {χ : G → ℂ}
    (hχ : IsClassFun χ) :
    (∑ x : G, conjClassInd h x * starRingEnd ℂ (χ x))
      = (∑ x : G, conjClassInd h x) * starRingEnd ℂ (χ h) := by
  have h1 : (∑ x : G, conjClassInd h x * starRingEnd ℂ (χ x))
      = ∑ x : G, conjClassInd h x * starRingEnd ℂ (χ h) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [conjClassInd_apply]
    by_cases hx : IsConj x h
    · have hxh : χ x = χ h := hχ.apply_eq_of_isConj hx
      rw [if_pos hx, hxh]
    · rw [if_neg hx]
      ring
  rw [h1, Finset.sum_mul]

/-- The Fourier coefficient of the conjugacy-class indicator. -/
theorem cfInner_conjClassInd {G : Type*} [Group G] [Fintype G] (h : G) {χ : G → ℂ}
    (hχ : IsClassFun χ) :
    cfInner (conjClassInd h) χ
      = (Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) * starRingEnd ℂ (χ h) := by
  rw [cfInner_apply, sum_conjClassInd_mul h hχ]
  ring

/-- The total mass of the conjugacy-class indicator, as the cardinality of the conjugacy
class of `h`. -/
theorem sum_conjClassInd {G : Type*} [Group G] [Fintype G] (h : G) :
    (∑ x : G, conjClassInd h x)
      = ((Finset.univ.filter (fun x : G => IsConj x h)).card : ℂ) := by
  rw [show (∑ x : G, conjClassInd h x)
        = ∑ x : G, (if IsConj x h then (1 : ℂ) else 0) from
      Finset.sum_congr rfl fun x _ => conjClassInd_apply h x]
  rw [Finset.sum_boole]

/-- The conjugacy-class indicator has non-zero total mass (it takes the value `1` at `h`). -/
theorem sum_conjClassInd_ne_zero {G : Type*} [Group G] [Fintype G] (h : G) :
    (∑ x : G, conjClassInd h x) ≠ 0 := by
  rw [sum_conjClassInd h]
  have hmem : h ∈ Finset.univ.filter (fun x : G => IsConj x h) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ h, IsConj.refl h⟩
  exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨h, hmem⟩).ne'

theorem column_orthogonality_not_conj {G : Type*} [Group G] [Fintype G] {g h : G}
    (hh : ¬ IsConj g h) :
    ∑ χ ∈ Irr G, χ g * starRingEnd ℂ (χ h) = 0 := by
  have hf : IsClassFun (conjClassInd h) := isClassFun_conjClassInd h
  have hkey : ∀ χ ∈ Irr G, cfInner (conjClassInd h) χ
      = (Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) * starRingEnd ℂ (χ h) :=
    fun χ hχ => cfInner_conjClassInd h (isClassFun_of_mem_Irr hχ)
  have hval : conjClassInd h g
      = ∑ χ ∈ Irr G, cfInner (conjClassInd h) χ * χ g := by
    have h := congrFun (classFun_eq_sum_irr hf) g
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hzero : ∑ χ ∈ Irr G, cfInner (conjClassInd h) χ * χ g = 0 := by
    rw [← hval, conjClassInd_apply]
    exact if_neg hh
  have h2 : ∑ χ ∈ Irr G,
      ((Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) * starRingEnd ℂ (χ h)) * χ g
      = 0 := by
    rw [← hzero]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hkey χ hχ]
  have hconst_ne : (Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (sum_conjClassInd_ne_zero h)
  have hfac : ((Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x))
      * (∑ χ ∈ Irr G, χ g * starRingEnd ℂ (χ h)) = 0 := by
    rw [Finset.mul_sum]
    rw [show (∑ χ ∈ Irr G,
          (Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) * (χ g * starRingEnd ℂ (χ h)))
        = ∑ χ ∈ Irr G,
          ((Fintype.card G : ℂ)⁻¹ * (∑ x : G, conjClassInd h x) * starRingEnd ℂ (χ h)) * χ g
        from Finset.sum_congr rfl fun χ _ => by ring]
    exact h2
  exact (mul_eq_zero.mp hfac).resolve_left hconst_ne

end Work.CharCore
