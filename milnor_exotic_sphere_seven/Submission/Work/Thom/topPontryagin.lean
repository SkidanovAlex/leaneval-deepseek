import Mathlib
import Submission.Work.Thom.complexOrientation
import Submission.Work.Thom.complexification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The top Pontryagin class of a real bundle of rank `2n`

For a real vector bundle `E` of rank `2n`, Milnor–Stasheff's definition
`p_i(E) = (-1)^i c_{2i}(E ⊗_ℝ ℂ)` has, at `i = n`, the *top* complex rank: `E ⊗_ℝ ℂ` has complex
rank `2n`, so `c_{2n}` is the top Chern class, i.e. the Euler class of the realification — exactly
what `Work.Thom.nonempty_thomClass_of_complex_cover` supplies for a complex bundle over a two-piece
cover.  Hence

  `p_n(E) = (-1)^n · e((E ⊗_ℝ ℂ)_ℝ) ∈ H^{4n}(B;ℤ)`

is available for a general real bundle `E` of rank `2n` over a two-piece cover, with **no**
orientation hypothesis (a complex bundle is canonically oriented,
`Work.Thom.isOrientedOver_of_complex`).  This is the first Pontryagin class of a general real bundle
that the workspace can construct; the *lower* ones need the splitting principle
(README ADDENDUM 17.3).
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The Thom class of the realification of `E ⊗_ℝ ℂ`** for a real bundle `E` of rank `2n` over a
two-piece open cover.  Its Euler class is `c_{2n}(E ⊗_ℝ ℂ)`, so `(-1)^n` times it is the top
Pontryagin class `p_n(E)`. -/
theorem nonempty_thomClass_of_complexification (n : ℕ) (hn : 1 ≤ n)
    (E : RealBundle B (EuclideanSpace ℝ (Fin (2 * n))) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {i j : ι} (hUi : U ⊆ E.baseSet i) (hVj : V ⊆ E.baseSet j) :
    Nonempty (ThomClass (realification (complexificationCore E)) (2 * (2 * n))) :=
  nonempty_thomClass_of_complex_cover (2 * n) (by omega) (complexificationCore E)
    hU hV hcov hUi hVj

/-- **The top Pontryagin class `p_n(E) = (-1)^n c_{2n}(E ⊗_ℝ ℂ) ∈ H^{4n}(B;ℤ)`** of a real bundle
of rank `2n` over a two-piece open cover, as the Euler class of the realification of the
complexification (with the canonical complex orientation supplied by
`Work.Thom.nonempty_thomClass_of_complex_cover`). -/
noncomputable def pontryaginTop (n : ℕ) (hn : 1 ≤ n)
    (E : RealBundle B (EuclideanSpace ℝ (Fin (2 * n))) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {i j : ι} (hUi : U ⊆ E.baseSet i) (hVj : V ⊆ E.baseSet j) :
    Coh ℤ (2 * (2 * n)) B :=
  ((-1 : ℤ) ^ n) • (Classical.choice
    (nonempty_thomClass_of_complexification n hn E hU hV hcov hUi hVj)).eulerClass

/-- The defining property of `Work.Thom.pontryaginTop`: it is `(-1)^n` times the Euler class of the
Thom class of the realification of the complexification, in particular it *is* a characteristic
class of `E ⊗_ℝ ℂ`, not free data. -/
theorem pontryaginTop_spec (n : ℕ) (hn : 1 ≤ n)
    (E : RealBundle B (EuclideanSpace ℝ (Fin (2 * n))) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {i j : ι} (hUi : U ⊆ E.baseSet i) (hVj : V ⊆ E.baseSet j) :
    ∃ T : ThomClass (realification (complexificationCore E)) (2 * (2 * n)),
      pontryaginTop n hn E hU hV hcov hUi hVj = ((-1 : ℤ) ^ n) • T.eulerClass :=
  ⟨Classical.choice (nonempty_thomClass_of_complexification n hn E hU hV hcov hUi hVj), rfl⟩

end

end Work.Thom
