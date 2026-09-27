import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLProd.aDiag_nsmul
import Submission.Work.EKLC6Core.box_iInter_conjBox
import Submission.Work.EKLC6Core.contracting_entry_eq_zero
import Submission.Work.EKLC6Core.conjBy_mem_Box1

/-!
# `EKLC6Core.box_conjBox_subset` — the conjugated box is trapped in `B₁^U`

For a horospherical subgroup `U ≤ SL₃(ℝ)` (`IsHoro U`: closed, normalised by the diagonal flow,
and contracted by some `aDiag t₀`) and an exponent vector `t` that contracts *all* of `U`,

`(aDiag t)ⁿ · u · (aDiag t)⁻ⁿ → 1`   for every `u ∈ U`   (`hcontr`),

the boxes `conjBox U t = aDiag t · B₁^U · (aDiag t)⁻¹` and `B₁^U` are sandwiched:

`conjBox U t ⊆ B₁^U ⊆ conjBox U (-t)`.

This is the elementary "one-sided" input to the entropy contribution of Pisa 7.6/7.18: it says
that along the contracting direction the contracted box `conjBox U t` sits inside the normalising
box, while the *expanding* box `conjBox U (-t)` still contains the normalising box.  In particular
no factor of `conjBox U t` can be a genuine expansion along the orbit of `aDiag t`.

The proof is entrywise.  Conjugation by a diagonal matrix scales entries,

`(aDiag t · g · (aDiag t)⁻¹)ᵢⱼ = e^{tᵢ - tⱼ} gᵢⱼ`   (`boxi_conj_apply`),

so the two inclusions hinge on the following consequence of `hcontr`
(`Work.EKLC6Core.contracting_entry_eq_zero`): in every *expanding* direction the entries of `U`
vanish,

`i ≠ j`, `t j < t i`  ⟹  `u i j = 0`  for every `u ∈ U`

(indeed the `(i,j)`-entry of `(aDiag t)ⁿ u (aDiag t)⁻ⁿ = e^{n(tᵢ-tⱼ)} uᵢⱼ` converges to `0`,
while the exponential factor is bounded below by `1`).  With that, `Work.EKLC6Core.conjBy_mem_Box1`
gives, for any `g ∈ B₁^U`,

* membership in `U` from the `A`-normalisation clause of `IsHoro`;
* `|(aDiag t · g · (aDiag t)⁻¹)ᵢⱼ - δᵢⱼ| ≤ 1`: unchanged on the diagonal, shrunk for `t i ≤ t j`,
  and `0` for `t j < t i`;

i.e. `aDiag t · g · (aDiag t)⁻¹ ∈ B₁^U`.  The first inclusion is this statement at `g ∈ B₁^U`
unwrapped from the image, and the second composes it with the identity
`aDiag (-t) · (aDiag t · g · (aDiag t)⁻¹) · (aDiag (-t))⁻¹ = g`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

theorem box_conjBox_subset {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    (Work.EKLC6Core.conjBox U t ⊆ Work.EKLContract.Box1 U) ∧
    (Work.EKLContract.Box1 U ⊆ Work.EKLC6Core.conjBox U (-t)) := by
  -- In every expanding direction the entries of `U` vanish.
  have hzero : ∀ u ∈ U, ∀ i j : Fin 3, i ≠ j → t j < t i → u i j = 0 :=
    fun u hu i j hij hlt => Work.EKLC6Core.contracting_entry_eq_zero hcontr hu hij hlt
  constructor
  · -- `conjBox U t ⊆ B₁^U`: unwrap the image and apply the box estimate
    rintro g ⟨h, hh, rfl⟩
    exact Work.EKLC6Core.conjBy_mem_Box1 hU hzero hh
  · -- `B₁^U ⊆ conjBox U (-t)`: `g` is the conjugate of `aDiag t · g · (aDiag t)⁻¹ ∈ B₁^U`
    intro g hg
    rw [Work.EKLC6Core.conjBox, Work.EKLC6Core.conjBy, Set.mem_image]
    refine ⟨Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹,
      Work.EKLC6Core.conjBy_mem_Box1 hU hzero hg, ?_⟩
    have h1 : (Work.EKLContract.aDiag t)⁻¹ = Work.EKLContract.aDiag (-t) :=
      Work.EKLC6Core.aDiag_inv_eq_neg t
    rw [← h1]
    group

end Work.EKLC6Core
