import Mathlib
import Submission.Work.SSGRoute.exists_sign_mul_pow_eq_real
import Submission.Work.SSGRoute.exists_pow_eq_complex_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Every unit of an archimedean completion is a global unit times a `p`-th power.**

For a number field `K`, an archimedean place `w` (so `K_w = w.Completion` is `ℝ` or `ℂ`) and a prime
`p`, every `b ∈ w.Completionˣ` is `β · c ^ p` with `β ∈ Kˣ` and `c` a unit of the completion.

Route: at a complex place, `w.Completion ≃+* ℂ`
(`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`) and `ℂ` is algebraically closed
(`Complex.instIsAlgClosed`), so one may take `β = 1` and a `p`-th root of `b`
(`IsAlgClosed.exists_pow_nat_eq`, noting `b ≠ 0`).  At a real place, `w.Completion ≃+* ℝ`
(`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal`): if the image of `b` is positive take
`β = 1` and a real `p`-th root (`Real.rpow_inv_natCast_pow`); if it is negative and `p` is odd take
`β = 1` and the negative `p`-th root; if it is negative and `p = 2` take `β = -1` (then `-b > 0` is
a square).  `NumberField.InfinitePlace.isReal_or_isComplex` supplies the case distinction. -/
theorem infinitePlace_units_mul_pow (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (w : NumberField.InfinitePlace K) (b : w.Completionˣ) :
    ∃ (β : Kˣ) (c : w.Completionˣ),
      Units.map (algebraMap K w.Completion).toMonoidHom β * c ^ p = b := by
  rcases NumberField.InfinitePlace.isReal_or_isComplex w with hreal | hcomplex
  · -- real place: `w.Completion ≃+* ℝ`; a real unit is a sign times a `p`-th power.
    set ψ := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal with hψ
    set Ψ := Units.mapEquiv ψ.toMulEquiv with hΨ
    obtain ⟨s, y, hs, hsy⟩ := exists_sign_mul_pow_eq_real p (Ψ b)
    -- The sign `s ∈ {1, -1}` is the image of the global unit `β = 1` or `β = -1`.
    have main : ∀ (β : Kˣ),
        Ψ (Units.map (algebraMap K w.Completion).toMonoidHom β) = s →
        ∃ c : w.Completionˣ,
          Units.map (algebraMap K w.Completion).toMonoidHom β * c ^ p = b := by
      intro β hβ
      refine ⟨Ψ.symm y, Ψ.injective ?_⟩
      rw [map_mul, map_pow, hβ, MulEquiv.apply_symm_apply]
      exact hsy
    rcases hs with hs | hs
    · rw [hs] at main
      refine ⟨1, main 1 ?_⟩
      rw [hΨ]
      simp
    · rw [hs] at main
      refine ⟨-1, main (-1) ?_⟩
      rw [hΨ]
      ext
      simp
  · -- complex place: `w.Completion ≃+* ℂ` is algebraically closed, take `β = 1` and a `p`-th root.
    set φ := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex with hφ
    set Φ := Units.mapEquiv φ.toMulEquiv with hΦ
    obtain ⟨c', hc'⟩ := exists_pow_eq_complex_units p (Φ b)
    refine ⟨1, Φ.symm c', ?_⟩
    rw [map_one, one_mul]
    refine Φ.injective ?_
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact hc'

end Work.SSGRoute
