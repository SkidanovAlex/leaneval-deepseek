import Mathlib
import Submission.Work.Drive.chordUnitDirDefs
import Submission.Work.Drive.contDiffOn_chordUnitDir
import Submission.Work.Drive.exists_secant_dir_contDiff
import Submission.Work.Drive.curve_deriv_ne_zero

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

/-! ## Elementary complex arithmetic used below -/

/-- `z * (1 / ‖z‖) = z / ‖z‖`, i.e. division by the (real) norm read as a complex multiplication. -/
private lemma mul_one_div_norm_eq_div (z : ℂ) :
    z * (((1 : ℝ) / ‖z‖ : ℝ) : ℂ) = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [div_eq_mul_inv]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_inv, one_mul]

/-- `(z / ‖z‖) ^ 2 = z / conj z = z / star z` for `z ≠ 0`: the square of the unit vector in the
direction of `z` is the quotient of `z` by its conjugate. -/
private lemma div_norm_sq_eq_div_conj (z : ℂ) (hz : z ≠ 0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / star z := by
  have hnorm : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * star z := by
    have h1 : ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj z, starRingEnd_apply]
  have hstar : star z ≠ 0 := by rw [star_ne_zero]; exact hz
  rw [div_pow, hnorm]
  field_simp

/-- The quotient `z / conj z` is unchanged by a nonzero **real** scalar factor. -/
private lemma div_star_smul_ofReal (c : ℝ) (w : ℂ) (hc : c ≠ 0) (hw : w ≠ 0) :
    (((c : ℂ) * w) / star ((c : ℂ) * w)) = w / star w := by
  have hc' : ((c:ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hstar : star w ≠ 0 := by rw [star_ne_zero]; exact hw
  rw [star_mul, Complex.star_def, Complex.conj_ofReal, starRingEnd_apply]
  field_simp

open Manifold in
open scoped Manifold ContDiff Topology in
/-- **The squared unit chord direction extends smoothly to the diagonal.**

For a smooth embedded closed plane curve `γ` and a point `p₀` of the torus of parameters *on the
diagonal* (`p₀ 0 = p₀ 1`), the squared unit chord direction `(chordUnitDir γ p) ^ 2`, which is smooth
away from the diagonal (`Work.Drive.contDiffOn_chordUnitDir`), has a **smooth extension** `Z` to a
neighbourhood of the diagonal, with `‖Z p₀‖ = 1`.

This is the missing datum for a **smooth chart of the closed configuration strip** (the Möbius band
`M` including its boundary): the capping coordinate of the configuration piece is the *doubled* chord
direction, and the chart of the capping space is smooth as soon as `circleOf ∘ (doubled direction)` is
(`Work.Drive.contMDiffAt_confPiece_mk`).  Off the diagonal that function is `(chordUnitDir γ p) ^ 2`,
while on the diagonal its value is the squared *tangent* direction; the formula
`(chordC / ‖chordC‖) ^ 2` is *not* the extension (Lean's total division gives `0` at the diagonal,
whereas the limit is a unit complex number), so a genuine extension has to be constructed.

Route.  Let `A p := (⟨(γ (Circle.exp (p 0)) - γ (Circle.exp (p 1))).1,
(γ (Circle.exp (p 0)) - γ (Circle.exp (p 1))).2⟩ : ℂ)` be the complexified chord, smooth and
non-vanishing off the diagonal; there `(chordUnitDir γ (p 0, p 1)) ^ 2 = A p / conj (A p)`
(`Work.Drive.circleOf_arg_div_pi`).  Vanishing on the diagonal, `A` factorises as
`A p = ((p 1 - p 0 : ℝ) : ℂ) * h p` with `h` smooth near `p₀` (the derivative/integral identity for
the parametric function `s ↦ A (p with second coordinate := s)`),
and `h p₀ ≠ 0` because the transverse derivative of `A` on the diagonal is a non-zero multiple of `γ'`
(the immersion clause of `Manifold.IsSmoothEmbedding`).  Then `A p / conj (A p) = h p / conj (h p)`
near `p₀`, which is smooth with `h p₀ / conj (h p₀)` of modulus one; glueing that germ to a global
function gives `Z`.

Implementation.  The divided difference of the parametrised curve `curve γ = fun t => γ (Circle.exp t)`
is `secantW (curve γ)`, the *global* `C^∞` function
`secantW F (s,t) = ∫ w in 0..1, deriv F (t + w * (s - t))` of
`Submission/Work/Drive/exists_secant_dir_contDiff.lean`, with the Newton–Leibniz identity
`curve γ s - curve γ t = (s - t) • secantW (curve γ) (s,t)` and the diagonal value
`secantW (curve γ) (t,t) = deriv (curve γ) t ≠ 0` (the curve is an immersion).  Writing
`wC q := toC (secantW (curve γ) q)` (the complexification of the divided difference), the chord
complexifies to `chordC γ (s,t) = ((s - t : ℝ) : ℂ) * wC (s,t)`, so off the diagonal
`(chordC / ‖chordC‖) ^ 2 = wC / star (wC) = (wC / ‖wC‖) ^ 2`; the right-hand side is `C^∞` near `p₀`
(the denominator `‖wC‖` is bounded away from `0` there) and defines the required `Z`, whose value at
`p₀` lives on the unit circle. -/
theorem exists_contMDiffAt_chordDir_sq (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (p₀ : EuclideanSpace ℝ (Fin 2)) (hp₀ : p₀ 0 = p₀ 1) :
    ∃ Z : EuclideanSpace ℝ (Fin 2) → ℂ,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z p₀ ∧ ‖Z p₀‖ = 1 ∧
      ∀ᶠ p in 𝓝 p₀, Circle.exp (p 0) ≠ Circle.exp (p 1) →
        Z p = (Work.Drive.chordUnitDir γ (p 0, p 1)) ^ 2 := by
  have hγinj : Function.Injective γ := hγ.isEmbedding.injective
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    contMDiff_iff_contDiff.mp (hγ.contMDiff.comp (contMDiff_circleExp (m := ∞)))
  have hder : ∀ t, deriv (curve γ) t ≠ 0 := curve_deriv_ne_zero γ hγ
  -- the complexified divided difference
  let wC : ℝ × ℝ → ℂ := fun q => toC (secantW (curve γ) q)
  have htoC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toC := by
    unfold toC
    have h1 : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const
    exact h1.add h2
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wC := htoC.comp (contDiff_secantW hF)
  have hwCa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wC (p₀ 0, p₀ 1) := hws.contDiffAt
  -- at the base point the divided difference is the tangent, which does not vanish
  have hbase : wC (p₀ 0, p₀ 1) ≠ 0 := by
    intro h
    rw [← hp₀] at h
    have h2 : deriv (curve γ) (p₀ 0) = 0 := by
      rw [← secantW_self (curve γ) (p₀ 0)]
      exact toC_eq_zero_iff.mp h
    exact hder (p₀ 0) h2
  -- smoothness of the unit normalisation (division is performed in `ℝ`, not in `ℂ`)
  have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => ‖wC q‖) (p₀ 0, p₀ 1) :=
    ContDiffAt.norm ℂ hwCa hbase
  have hdivn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1:ℝ)/‖wC q‖) (p₀ 0, p₀ 1) :=
    ContDiffAt.div (f := fun _ : ℝ × ℝ => (1:ℝ)) (g := fun q : ℝ × ℝ => ‖wC q‖)
      contDiffAt_const hnorm (norm_ne_zero_iff.mpr hbase)
  have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => wC q * (((1:ℝ)/‖wC q‖ : ℝ) : ℂ)) (p₀ 0, p₀ 1) :=
    hwCa.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (p₀ 0, p₀ 1) hdivn)
  have hloc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (wC q * (((1:ℝ)/‖wC q‖ : ℝ) : ℂ))^2) (p₀ 0, p₀ 1) := hmul.pow 2
  refine ⟨fun p => (wC (p 0, p 1) * (((1:ℝ)/‖wC (p 0, p 1)‖ : ℝ) : ℂ))^2, ?_, ?_, ?_⟩
  · -- smoothness at `p₀`
    rw [contMDiffAt_iff_contDiffAt]
    have hpair : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin 2) => (p 0, p 1)) p₀ := by fun_prop
    exact ContDiffAt.comp (f := fun p : EuclideanSpace ℝ (Fin 2) => (p 0, p 1))
      (g := fun q : ℝ × ℝ => (wC q * (((1:ℝ)/‖wC q‖ : ℝ) : ℂ))^2) p₀ hloc hpair
  · -- the value at `p₀` has modulus one
    show ‖(wC (p₀ 0, p₀ 1) * (((1:ℝ)/‖wC (p₀ 0, p₀ 1)‖ : ℝ) : ℂ))^2‖ = 1
    rw [mul_one_div_norm_eq_div, norm_pow, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hbase), one_pow]
  · -- off the diagonal the extension is the squared unit chord direction
    filter_upwards with p hne
    have hst : p 0 ≠ p 1 := fun h => hne (by rw [h])
    have hA : chordC γ (p 0, p 1) = ((p 0 - p 1 : ℝ) : ℂ) * wC (p 0, p 1) := by
      have hsub : curve γ (p 0) - curve γ (p 1) = (p 0 - p 1) • secantW (curve γ) (p 0, p 1) :=
        sub_eq_smul_secantW (hF.of_le (by norm_num)) (p 0) (p 1)
      rw [chordC_eq_toC]
      change toC (curve γ (p 0) - curve γ (p 1)) = ((p 0 - p 1 : ℝ) : ℂ) * wC (p 0, p 1)
      rw [hsub, toC_smul]
    have hAne : chordC γ (p 0, p 1) ≠ 0 := by
      rw [chordC_eq_toC, toC_ne_zero_iff, sub_ne_zero]
      exact fun h => hne (hγinj h)
    have hcne : p 0 - p 1 ≠ 0 := sub_ne_zero.mpr hst
    have hwne : wC (p 0, p 1) ≠ 0 := by
      intro h
      exact hAne (by rw [hA, h, mul_zero])
    show (wC (p 0, p 1) * (((1:ℝ)/‖wC (p 0, p 1)‖ : ℝ) : ℂ))^2
      = (Work.Drive.chordUnitDir γ (p 0, p 1))^2
    rw [chordUnitDir]
    have key : (chordC γ (p 0, p 1) / ((‖chordC γ (p 0, p 1)‖ : ℝ) : ℂ)) ^ 2
        = (wC (p 0, p 1) * (((1:ℝ)/‖wC (p 0, p 1)‖ : ℝ) : ℂ))^2 := by
      rw [mul_one_div_norm_eq_div, div_norm_sq_eq_div_conj _ hAne, hA,
        div_norm_sq_eq_div_conj _ hwne]
      exact div_star_smul_ofReal (p 0 - p 1) (wC (p 0, p 1)) hcne hwne
    exact key.symm

end Work.Drive
