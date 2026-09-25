import Mathlib

/-!
# `Work.ShafarevichKoch.CohomologyAction` -- conjugation in the kernel of a homomorphism

The first ingredient of the **Hochschild--Serre five-term exact sequence** (the machinery the
classical proof of the Shafarevich--Koch relation bound uses, and which Mathlib is missing for
`H²`) is that the quotient `Q = G ⧸ N` acts on the cohomology of the normal subgroup `N ⊴ G` by
conjugation.  This file provides the underlying group-theoretic operation: for `π : G →* Q`
(thought of as `G ↠ Q` with `N = ker π`), conjugation by `g : G` restricts to an automorphism of
`ker π`, giving a left action of `G` on `ker π`.

Nothing here is arithmetic; it is shared infrastructure that this chapter's unramified relation
count, the sibling tame route, and the Gaschütz relation-rank dictionary `r = dim H²` all need.

## Main results

* `conjKer π g n` -- the conjugate `g * n * g⁻¹` of `n ∈ ker π`;
* `conjKer_coe`, `conjKer_one`, `conjKer_mul` -- its elementary API;
* `conjAction π : G →* MulAut (ker π)` -- the conjugation action, together with
  `conjAction_apply`.
-/

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch

variable {G Q : Type*} [Group G] [Group Q]

/-- **Conjugation inside the kernel.**  For `π : G →* Q` and `g : G`, the conjugate
`g * n * g⁻¹` of `n ∈ ker π` again lies in `ker π`. -/
def conjKer (π : G →* Q) (g : G) (n : MonoidHom.ker π) : MonoidHom.ker π :=
  ⟨g * (n : G) * g⁻¹, by
    have hn : π (n : G) = 1 := MonoidHom.mem_ker.mp n.2
    simp [map_mul, hn]⟩

@[simp] theorem conjKer_coe (π : G →* Q) (g : G) (n : MonoidHom.ker π) :
    ((conjKer π g n : MonoidHom.ker π) : G) = g * (n : G) * g⁻¹ := rfl

@[simp] theorem conjKer_one (π : G →* Q) (g : G) : conjKer π g 1 = 1 := by
  ext
  simp

theorem conjKer_mul (π : G →* Q) (g : G) (m n : MonoidHom.ker π) :
    conjKer π g (m * n) = conjKer π g m * conjKer π g n := by
  ext
  simp [mul_assoc]

/-- Two conjugations compose: `h (g n g⁻¹) h⁻¹ = (hg) n (hg)⁻¹`. -/
theorem conjKer_conjKer (π : G →* Q) (g h : G) (n : MonoidHom.ker π) :
    conjKer π h (conjKer π g n) = conjKer π (h * g) n := by
  ext
  simp only [conjKer_coe]
  group

/-- **The conjugation action of `G` on `ker π`**, as a homomorphism into the multiplicative
automorphism group of `ker π`. -/
def conjAction (π : G →* Q) : G →* MulAut (MonoidHom.ker π) where
  toFun g :=
    { toFun := conjKer π g
      invFun := conjKer π g⁻¹
      left_inv := fun n => by
        rw [conjKer_conjKer, inv_mul_cancel]
        exact Subtype.ext (by simp [conjKer_coe])
      right_inv := fun n => by
        rw [conjKer_conjKer, mul_inv_cancel]
        exact Subtype.ext (by simp [conjKer_coe])
      map_mul' := conjKer_mul π g }
  map_one' := MulEquiv.ext (fun n => Subtype.ext (by simp [conjKer_coe]))
  map_mul' := fun g h => MulEquiv.ext (fun n => (conjKer_conjKer π h g n).symm)

@[simp] theorem conjAction_apply (π : G →* Q) (g : G) (n : MonoidHom.ker π) :
    conjAction π g n = conjKer π g n := rfl

end Work.ShafarevichKoch
