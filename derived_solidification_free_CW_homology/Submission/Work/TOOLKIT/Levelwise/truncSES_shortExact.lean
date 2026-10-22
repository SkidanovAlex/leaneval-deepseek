/-
AREA TOOLKIT/Levelwise — short exactness of the truncation short complexes.

For every `m : ℕ` and every complex `K`, the short complex
`0 → σ^{≥-m}K → σ^{≥-(m+1)}K → (K.X (-(m+1)))[m+1] → 0` of `Work.TOOLKIT.Levelwise.truncSES`
is short exact.

The statement is verified in the two steps that the `Cpx`-version of the truncation sequence
naturally comes with:

* `HomologicalComplex.shortExact_of_degreewise_shortExact` reduces short exactness in the
  category of cochain complexes to short exactness of all the degreewise short complexes
  in `LightCondAb`;
* in each degree `i` the resulting short complex of light condensed abelian groups is
  degenerate: if `i > -(m+1)` the first term is `K.X i`, the second is `K.X i` and the
  third is `0`; if `i = -(m+1)` the first term is `0`, the second is `K.X (-(m+1))`, the
  third is `K.X (-(m+1))`; and if `i < -(m+1)` all three terms are zero.  In the first
  case `f` is an isomorphism and `g = 0`, in the second `f = 0` and `g` is an
  isomorphism, and in the third everything vanishes.
-/
import Mathlib
import Submission.Work.TOOLKIT.Levelwise.Tower
import Submission.Work.TOOLKIT.Levelwise.Maps
import Submission.Work.TOOLKIT.Levelwise.Basic

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.TOOLKIT.Levelwise

section Degenerate

variable {C : Type*} [Category C] [Abelian C]

/-- A short complex whose first map is an isomorphism and whose third term is a zero object
is short exact. -/
theorem shortExact_of_isIso_f_of_isZero_third {S : ShortComplex C} (hf : IsIso S.f)
    (h3 : IsZero S.X₃) : S.ShortExact :=
  ShortComplex.ShortExact.mk'
    ((S.exact_iff_epi (h3.eq_zero_of_tgt S.g)).2 inferInstance) inferInstance (h3.epi S.g)

/-- A short complex whose first term is a zero object and whose second map is an isomorphism
is short exact. -/
theorem shortExact_of_isZero_first_of_isIso_g {S : ShortComplex C} (h1 : IsZero S.X₁)
    (hg : IsIso S.g) : S.ShortExact :=
  ShortComplex.ShortExact.mk'
    ((S.exact_iff_mono (h1.eq_zero_of_src S.f)).2 inferInstance) (h1.mono S.f) inferInstance

/-- A short complex all of whose three terms are zero objects is short exact. -/
theorem shortExact_of_all_isZero {S : ShortComplex C} (h1 : IsZero S.X₁) (h2 : IsZero S.X₂)
    (h3 : IsZero S.X₃) : S.ShortExact :=
  ShortComplex.ShortExact.mk'
    ((S.exact_iff_mono (h1.eq_zero_of_src S.f)).2 (h2.mono S.g)) (h1.mono S.f) (h3.epi S.g)

end Degenerate

theorem truncSES_shortExact (m : ℕ) (K : Work.TOOLKIT.Cpx) :
    (Work.TOOLKIT.Levelwise.truncSES m K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i => ?_)
  -- In degree `i` the short complex is the degree-`i` part of `truncSES m K`.
  rcases lt_trichotomy (-(m + 1 : ℤ)) i with h | h | h
  · -- `i > -(m+1)`: `K.X i ⟶ K.X i` (an isomorphism) followed by `0`.
    refine shortExact_of_isIso_f_of_isZero_third ?_
      (isZero_sng_obj_X (by omega : i ≠ -(m + 1 : ℤ)) (K.X (-(m + 1 : ℤ))))
    show IsIso ((truncIncl (show -(m + 1 : ℤ) ≤ -(m : ℤ) by omega) K).f i)
    rw [truncIncl_f_of_le _ (by omega : -(m : ℤ) ≤ i) K]
    infer_instance
  · -- `i = -(m+1)`: `0 ⟶ K.X i` followed by an isomorphism.
    subst h
    refine shortExact_of_isZero_first_of_isIso_g
      (trunc_isZero_X (by omega : ¬ -(m : ℤ) ≤ -(m + 1 : ℤ)) K) ?_
    show IsIso ((truncProj K (-(m + 1 : ℤ))).f (-(m + 1 : ℤ)))
    rw [truncProj_f_self]
    infer_instance
  · -- `i < -(m+1)`: all three terms are zero.
    exact shortExact_of_all_isZero
      (trunc_isZero_X (by omega : ¬ -(m : ℤ) ≤ i) K)
      (trunc_isZero_X (by omega : ¬ -(m + 1 : ℤ) ≤ i) K)
      (isZero_sng_obj_X (by omega : i ≠ -(m + 1 : ℤ)) (K.X (-(m + 1 : ℤ))))

end Work.TOOLKIT.Levelwise
