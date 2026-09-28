import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.Sig2.span_intCast_eq_span_range
import Submission.Work.HP.Sig2.gramOf_isUnit_inv
import Submission.Work.HP.Sig2.perpCompB_mem_orth
import Submission.Work.HP.Sig2.perpCompB_linear

/-!
# The perpendicular component `perpComp Λ w` of `w` with respect to `span_ℝ(Λ)`

`perpComp Λ w` (`Submission/Work/HP/Sig2/GamTwoDefs.lean`) is `w` minus the orthogonal projection
of `w` onto the real span of `Λ ⊆ ℤ^ι`, computed with the inverse Gram matrix of the canonical
`ℤ`-basis `canB Λ = (Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2` of `Λ`.  This file records its
geometry: the subtracted term is a finite sum of realified basis vectors, the remainder is
orthogonal to `Λ`, it vanishes on `span_ℝ(Λ)`, it only depends on `w` modulo `span_ℝ(Λ)`, it is
`1`-Lipschitz for the Euclidean `ℓ²` norm, and it is linear.

The analytic ingredients (the Gram matrix of a `ℤ`-basis is invertible over `ℝ`; `perpCompB` lies
in / is orthogonal to the span of the realified basis; `perpCompB` is linear) are proved in
`Submission/Work/HP/Sig2/{gramOf_isUnit_inv,perpCompB_mem_orth,perpCompB_linear}.lean`; here we
transport them from a general `ℤ`-basis `b` to the canonical basis used in the definition of
`perpComp`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Sig2
namespace PerpCompAux

open Work.HP Finset

/-! ## Generalities on an arbitrary `ℤ`-basis -/

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {Λ : Submodule ℤ (ι → ℤ)}

/-- The projection sum entering the definition of `perpCompB`: it is the subtracted term. -/
def projB (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) : ι → ℝ :=
  ∑ i : κ, (∑ j : κ, (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
    • intCastPi (((b i : Λ) : ι → ℤ))

/-- The real span of the realifications of the vectors of a `ℤ`-basis `b` of `Λ`. -/
def bSpan (b : Module.Basis κ ℤ Λ) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (Set.range fun i : κ => intCastPi (((b i : Λ) : ι → ℤ)))

lemma perpCompB_eq (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) :
    perpCompB b w = w - projB b w := rfl

/-- The projection sum is a linear combination of the basis vectors. -/
lemma projB_mem (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) : projB b w ∈ bSpan b := by
  rw [bSpan, Submodule.mem_span_range_iff_exists_fun ℝ]
  exact ⟨Matrix.mulVec (gramOf b)⁻¹ (fun j => dotR w (intCastPi (((b j : Λ) : ι → ℤ)))), rfl⟩

/-- Pythagoras: if `perpCompB b` is orthogonal to `bSpan b` then `perpCompB b` does not increase
the Euclidean norm. -/
lemma rNorm_perpCompB_le (b : Module.Basis κ ℤ Λ)
    (horth : ∀ w : ι → ℝ, ∀ z ∈ bSpan b, dotR (perpCompB b w) z = 0) (w : ι → ℝ) :
    rNorm (perpCompB b w) ≤ rNorm w := by
  have hP : projB b w ∈ bSpan b := projB_mem b w
  have h1 : dotR (perpCompB b w) (projB b w) = 0 := horth w (projB b w) hP
  have h2 : w = perpCompB b w + projB b w := by rw [perpCompB_eq b w]; abel
  have h3 : rNorm w ^ 2 = rNorm (perpCompB b w) ^ 2 + rNorm (projB b w) ^ 2 := by
    conv_lhs => rw [h2]
    rw [Transf.rNorm_add_sq_of_orthogonal h1]
  have h4 : rNorm (perpCompB b w) ^ 2 ≤ rNorm w ^ 2 := by
    rw [h3]; exact le_add_of_nonneg_right (sq_nonneg _)
  have h5 := sq_le_sq.mp h4
  rwa [abs_of_nonneg (Transf.rNorm_nonneg _), abs_of_nonneg (Transf.rNorm_nonneg _)] at h5

/-- If `w` is orthogonal to the realified basis then it is its own perpendicular component. -/
lemma perpCompB_eq_self_of_orthogonal (b : Module.Basis κ ℤ Λ) (w : ι → ℝ)
    (h : ∀ j : κ, dotR w (intCastPi (((b j : Λ) : ι → ℤ))) = 0) : perpCompB b w = w := by
  have h0 : ∀ i : κ,
      (∑ j : κ, (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ)))) = 0 :=
    fun i => Finset.sum_eq_zero fun j _ => by rw [h j, mul_zero]
  rw [perpCompB]
  rw [Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]]
  exact sub_zero w

end General

/-! ## The canonical basis of `Λ` and the perpendicular component -/

section Inst

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real span `span_ℝ(Λ)` of the lattice `Λ ⊆ ℤ^ι`. -/
abbrev spanR (Λ : Submodule ℤ (ι → ℤ)) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ)))

/-- The canonical `ℤ`-basis of `Λ` used in the definition of `perpComp`. -/
abbrev canB (Λ : Submodule ℤ (ι → ℤ)) := (Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2

lemma perpComp_eq_perpCompB (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ) :
    perpComp Λ w = perpCompB (canB Λ) w := rfl

omit [DecidableEq ι] in
/-- `span_ℝ(Λ)` is the real span of the realified vectors of the canonical basis. -/
lemma spanR_eq_bSpan (Λ : Submodule ℤ (ι → ℤ)) : spanR Λ = bSpan (canB Λ) :=
  span_intCast_eq_span_range (canB Λ)

omit [DecidableEq ι] in
lemma gramOf_canB_mul_inv (Λ : Submodule ℤ (ι → ℤ)) :
    gramOf (canB Λ) * (gramOf (canB Λ))⁻¹ = 1 :=
  (gramOf_isUnit_inv (canB Λ)).2.2

/-- `perpComp Λ w` is the orthogonal projection onto the complement of `span_ℝ(Λ)`: the subtracted
term lies in `span_ℝ(Λ)` and the remainder is orthogonal to it. -/
lemma perpComp_mem_orth (Λ : Submodule ℤ (ι → ℤ)) :
    (∀ w : ι → ℝ, w - perpComp Λ w ∈ spanR Λ) ∧
      (∀ w : ι → ℝ, ∀ z ∈ spanR Λ, dotR (perpComp Λ w) z = 0) := by
  obtain ⟨h1, h2⟩ := perpCompB_mem_orth (canB Λ) (gramOf_canB_mul_inv Λ)
  constructor
  · intro w
    rw [perpComp_eq_perpCompB, spanR_eq_bSpan]
    exact h1 w
  · intro w z hz
    rw [perpComp_eq_perpCompB]
    exact h2 w z (by rwa [spanR_eq_bSpan] at hz)

/-- (1) `w - perpComp Λ w ∈ span_ℝ(Λ)`. -/
lemma perpComp_mem (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ) : w - perpComp Λ w ∈ spanR Λ :=
  (perpComp_mem_orth Λ).1 w

/-- (2) `perpComp Λ w` is orthogonal to `Λ`. -/
lemma perpComp_orth (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ) :
    ∀ q ∈ Λ, dotR (perpComp Λ w) (toR q) = 0 := by
  intro q hq
  have hmem : intCastPi q ∈ spanR Λ := Submodule.subset_span ⟨q, hq, rfl⟩
  have h := (perpComp_mem_orth Λ).2 w (intCastPi q) hmem
  rwa [toR_eq_intCastPi]

/-- (3) If `w` is orthogonal to `Λ` then `perpComp Λ w = w`. -/
lemma perpComp_eq_self_of_orthogonal (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ)
    (h : ∀ q ∈ Λ, dotR w (toR q) = 0) : perpComp Λ w = w := by
  rw [perpComp_eq_perpCompB]
  refine perpCompB_eq_self_of_orthogonal (canB Λ) w fun j => ?_
  have hj := h (((canB Λ j : Λ) : ι → ℤ)) (canB Λ j).2
  rwa [toR_eq_intCastPi] at hj

/-- (4) `perpComp Λ` vanishes on `span_ℝ(Λ)`. -/
lemma perpComp_eq_zero_of_mem (Λ : Submodule ℤ (ι → ℤ)) {u : ι → ℝ} (hu : u ∈ spanR Λ) :
    perpComp Λ u = 0 := by
  have h1 : u - perpComp Λ u ∈ spanR Λ := perpComp_mem Λ u
  have h2 : perpComp Λ u ∈ spanR Λ := by
    have hm := Submodule.sub_mem (spanR Λ) hu h1
    rwa [show u - (u - perpComp Λ u) = perpComp Λ u from by abel] at hm
  have h3 : dotR (perpComp Λ u) (perpComp Λ u) = 0 := (perpComp_mem_orth Λ).2 u _ h2
  exact Transf.dotR_self_eq_zero.mp h3

/-- (5) `perpComp Λ` only depends on `w` modulo `span_ℝ(Λ)`. -/
lemma perpComp_eq_of_sub_mem (Λ : Submodule ℤ (ι → ℤ)) {w w' : ι → ℝ}
    (h : w - w' ∈ spanR Λ) : perpComp Λ w = perpComp Λ w' := by
  have hz : perpComp Λ (w - w') = 0 := perpComp_eq_zero_of_mem Λ h
  rw [perpComp_eq_perpCompB] at hz
  have hlin : perpCompB (canB Λ) (w - w')
      = perpCompB (canB Λ) w - perpCompB (canB Λ) w' := (perpCompB_linear (canB Λ)).2.2 w w'
  have h0 : perpCompB (canB Λ) w - perpCompB (canB Λ) w' = 0 := by rw [← hlin]; exact hz
  have h1 : perpCompB (canB Λ) w = perpCompB (canB Λ) w' := sub_eq_zero.mp h0
  rw [perpComp_eq_perpCompB, perpComp_eq_perpCompB]
  exact h1

/-- (6) The perpendicular component does not increase the Euclidean norm. -/
lemma rNorm_perpComp_le (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ) :
    rNorm (perpComp Λ w) ≤ rNorm w := by
  rw [perpComp_eq_perpCompB]
  refine rNorm_perpCompB_le (canB Λ) (fun u z hz => ?_) w
  rw [← perpComp_eq_perpCompB]
  exact (perpComp_mem_orth Λ).2 u z (by rw [spanR_eq_bSpan]; exact hz)

/-- (7) `perpComp Λ` is homogeneous. -/
lemma perpComp_smul (Λ : Submodule ℤ (ι → ℤ)) (a : ℝ) (u : ι → ℝ) :
    perpComp Λ (a • u) = a • perpComp Λ u := by
  rw [perpComp_eq_perpCompB, perpComp_eq_perpCompB]
  exact (perpCompB_linear (canB Λ)).1 a u

/-- (8) `perpComp Λ` is additive. -/
lemma perpComp_add (Λ : Submodule ℤ (ι → ℤ)) (u u' : ι → ℝ) :
    perpComp Λ (u + u') = perpComp Λ u + perpComp Λ u' := by
  rw [perpComp_eq_perpCompB, perpComp_eq_perpCompB, perpComp_eq_perpCompB]
  exact (perpCompB_linear (canB Λ)).2.1 u u'

end Inst

end PerpCompAux

/-- The "perpendicular component" `perpComp Λ w` of `w ∈ ℝ^ι` with respect to the real span of
`Λ ⊆ ℤ^ι` (defined in `Submission/Work/HP/Sig2/GamTwoDefs.lean` as `w` minus the projection
computed with the inverse Gram matrix of a `ℤ`-basis of `Λ`) has the expected properties.

(The file `Submission/Work/HP/Sig2/PerpCompGeom.lean` bundles a FALSE variant of the third
conjunct — it puts the hypothesis `∀ q ∈ Λ, dotR w (toR q) = 0` after the quantifier `∀ q ∈ Λ`.
Its eight auxiliary lemmas in namespace `Work.HP.Sig2.PerpAux` are correct; do NOT import that
module: copy the needed proofs, or redo them.  Note the module clashes with `Submission.Work.HP.Vero`
(`Work.HP.orthLat`), so do not import `numaux.Defs`, `DetLOrth`, `det_gam`, `det_gam_gen`, `EElow`,
`MDEstimates`.)

Route: `perpComp Λ w = perpCompB b w` with `b := (Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2` and
`perpCompB b w = w - ∑ᵢ (∑ⱼ (gramOf b)⁻¹ᵢⱼ * dotR w (bⱼ)) • bᵢ`.
(1) `w - perpComp Λ w ∈ span_ℝ(Λ)` is a finite sum of basis vectors.  (2) orthogonality:
`dotR (perpComp Λ w) (b k) = dotR w (b k) - ∑ j (∑ i (gramOf b)⁻¹ i j * (gramOf b) i k) dotR w (b j)
= 0` using `(gramOf b)⁻¹ * gramOf b = 1` (true since the Gram matrix of a `ℤ`-basis is invertible
over `ℝ`: a `ℤ`-basis is `ℝ`-linearly independent); extend by linearity to all of `Λ`.
(3) if `dotR w (toR q) = 0` for all `q ∈ Λ` then all `dotR w (b j) = 0` and the sum defining
`perpCompB b w` vanishes.
(4) if `u ∈ span_ℝ(Λ)` then `perpComp Λ u = 0`: write `u` in the basis and use `G⁻¹G t = t`.
(5)(6) are the same computation; (7)(8) are bilinearity of the formula.
Note `ι → ℝ` carries no `InnerProductSpace` instance (the default norm is the sup norm), so all
inner products are the explicit `dotR`; `rNorm` is the Euclidean `ℓ²` norm. -/
theorem PerpCompLemmas {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (w w' : ι → ℝ) (h : w - w' ∈ Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ)))) :
    (w - perpComp Λ w ∈ Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ)))) ∧
      (∀ q ∈ Λ, dotR (perpComp Λ w) (toR q) = 0) ∧
      ((∀ q ∈ Λ, dotR w (toR q) = 0) → perpComp Λ w = w) ∧
      (∀ u ∈ Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ))), perpComp Λ u = 0) ∧
      (perpComp Λ w = perpComp Λ w') ∧
      (rNorm (perpComp Λ w) ≤ rNorm w) ∧
      (∀ (a : ℝ) (u : ι → ℝ), perpComp Λ (a • u) = a • perpComp Λ u) ∧
      (∀ u u' : ι → ℝ, perpComp Λ (u + u') = perpComp Λ u + perpComp Λ u') :=
  ⟨PerpCompAux.perpComp_mem Λ w, PerpCompAux.perpComp_orth Λ w,
    fun horth => PerpCompAux.perpComp_eq_self_of_orthogonal Λ w horth,
    fun _ hu => PerpCompAux.perpComp_eq_zero_of_mem Λ hu,
    PerpCompAux.perpComp_eq_of_sub_mem Λ h, PerpCompAux.rNorm_perpComp_le Λ w,
    PerpCompAux.perpComp_smul Λ, PerpCompAux.perpComp_add Λ⟩

end Work.HP.Sig2
