import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTreeTree
import Submission.Work.ORLocInd.FKSKernel.pushoutStarTree_isTree
import Submission.Work.ORLocInd.FKSKernel.pushoutStarTree_stabilizers
import Submission.Work.ORLocInd.CohenLyndon.coprod_malnormal
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver
open Work.ORLocInd.FKSKernel

/-- The action of the pushout group on a leaf of the star tree, in `Quotient.mk''`-form. -/
theorem starTree_smul_lf_mk {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (i : ι) (x g : Psh φ) :
    x • lf φ i (Quotient.mk'' g) = lf φ i (Quotient.mk'' (x * g)) := by
  show smulVtx φ x (lf φ i (Quotient.mk'' g)) = lf φ i (Quotient.mk'' (x * g))
  rw [smulVtx_lf, smulCtr_mk]

/-- Two leaves of the star tree whose labels are `Quotient.mk''`-classes coincide exactly when the
corresponding cosets of the vertex group `ofSub φ i` coincide. -/
theorem starTree_lf_mk_eq_iff {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (i : ι) (a b : Psh φ) :
    lf φ i (Quotient.mk'' a) = lf φ i (Quotient.mk'' b) ↔
      (Quotient.mk'' a : Psh φ ⧸ ofSub φ i) = Quotient.mk'' b := by
  simp only [lf, cosetMap_mk]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
  · intro h
    rw [h]

/-- The underlying action function `smulVtx` is associative, phrased so that it does not go
through the (definitionally equal but syntactically different) `SMul` instance of `Vtx φ`. -/
theorem starTree_smulVtx_mul {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (g h : Psh φ) (X : Vtx φ) :
    smulVtx φ (g * h) X = smulVtx φ g (smulVtx φ h X) := by
  rcases X with c | ⟨i, c⟩
  · simp only [smulVtx_apply_inl, smulCtr_mul]
  · simp only [smulVtx_apply_inr, smulLf_mul]

/-- The underlying action function `smulVtx` fixes points at the identity. -/
theorem starTree_smulVtx_one {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (X : Vtx φ) : smulVtx φ 1 X = X := by
  rcases X with c | ⟨i, c⟩
  · simp only [smulVtx_apply_inl, smulCtr_one]
  · simp only [smulVtx_apply_inr, smulLf_one]

/-- **Bass--Serre descent on the star tree of a pushout of groups.**

Let `P = Monoid.PushoutI φ` be the pushout of a family of groups `G i` over `H`, and let `i₀ : ι`.
If `y` lies in the image of `G i₀` and `ζ ∉ im(G i₀)` conjugates `y` back into `im(G i₀)`, then
`y` is conjugate *within* `im(G i₀)` into the image of `H`.

Geometrically: `y` fixes the leaf `v₀ = lf i₀ (1 · baseSub)` and (because `ζ y ζ⁻¹` fixes it too)
the vertex `ζ⁻¹ • v₀`, which differs from `v₀` since `ζ ∉ im(G i₀)`.  An element of a group
acting on a tree which fixes two distinct vertices fixes a neighbour of one of them.  That
neighbour `x = ctr φ c` of the leaf `v₀` is a centre, `y` lies in its stabiliser
`g (baseSub) g⁻¹` (with `g = repC φ c`), and the fact that `v₀` is the leaf of the `i₀`-th vertex
group at the base coset forces `g ∈ im(G i₀)`.  Conjugating by `g⁻¹ ∈ im(G i₀)` gives the
claim. -/
theorem pushoutStarTreeDescent {ι : Type u} [Nonempty ι] {H : Type u} {G : ι → Type u}
    [Group H] [∀ i, Group (G i)] (φ : ∀ i, H →* G i) (i₀ : ι) {y ζ : Monoid.PushoutI φ}
    (hy : y ∈ (Monoid.PushoutI.of (φ := φ) i₀).range)
    (hconj : ζ * y * ζ⁻¹ ∈ (Monoid.PushoutI.of (φ := φ) i₀).range)
    (hζ : ζ ∉ (Monoid.PushoutI.of (φ := φ) i₀).range) :
    ∃ k : G i₀,
      (Monoid.PushoutI.of (φ := φ) i₀ k) * y * (Monoid.PushoutI.of (φ := φ) i₀ k)⁻¹ ∈
        (Monoid.PushoutI.base φ).range := by
  classical
  have hT : Work.ORBassSerre.IsTree (Vtx φ) := pushoutStarTree_isTree φ
  have hyS : y ∈ ofSub φ i₀ := hy
  have hconjS : ζ * y * ζ⁻¹ ∈ ofSub φ i₀ := hconj
  have hζS : ζ ∉ ofSub φ i₀ := hζ
  -- the leaf of the `i₀`-th vertex group at the base coset
  let v₀ : Vtx φ := lf φ i₀ (Quotient.mk'' (1 : Psh φ))
  have hyv₀ : y • v₀ = v₀ := by
    show smulVtx φ y (lf φ i₀ (Quotient.mk'' (1 : Psh φ))) =
      lf φ i₀ (Quotient.mk'' (1 : Psh φ))
    rw [smulVtx_lf, smulCtr_mk, mul_one, starTree_lf_mk_eq_iff, QuotientGroup.eq]
    simpa using (ofSub φ i₀).inv_mem hyS
  -- `ζ y ζ⁻¹` also fixes `v₀`
  have hfixV : smulVtx φ (ζ * y * ζ⁻¹) v₀ = v₀ := by
    show smulVtx φ (ζ * y * ζ⁻¹) (lf φ i₀ (Quotient.mk'' (1 : Psh φ))) =
      lf φ i₀ (Quotient.mk'' (1 : Psh φ))
    rw [smulVtx_lf, smulCtr_mk, mul_one, starTree_lf_mk_eq_iff, QuotientGroup.eq]
    simpa using (ofSub φ i₀).inv_mem hconjS
  -- the vertex `ζ⁻¹ • v₀`, also fixed by `y`
  let w : Vtx φ := smulVtx φ ζ⁻¹ v₀
  have hw_ne : w ≠ v₀ := by
    intro h
    apply hζS
    have h' : smulVtx φ ζ⁻¹ (lf φ i₀ (Quotient.mk'' (1 : Psh φ))) =
        lf φ i₀ (Quotient.mk'' (1 : Psh φ)) := h
    rw [smulVtx_lf, smulCtr_mk, mul_one] at h'
    have h3 : (Quotient.mk'' ζ⁻¹ : Psh φ ⧸ ofSub φ i₀) = Quotient.mk'' (1 : Psh φ) :=
      (starTree_lf_mk_eq_iff φ i₀ ζ⁻¹ 1).mp h'
    have h4 : (ζ⁻¹)⁻¹ * 1 ∈ ofSub φ i₀ := QuotientGroup.eq.mp h3
    simpa using h4
  have hyw : y • w = w := by
    show smulVtx φ y w = w
    calc smulVtx φ y w
        = smulVtx φ y (smulVtx φ ζ⁻¹ v₀) := rfl
      _ = smulVtx φ (y * ζ⁻¹) v₀ := (starTree_smulVtx_mul φ y ζ⁻¹ v₀).symm
      _ = smulVtx φ (ζ⁻¹ * (ζ * y * ζ⁻¹)) v₀ := by
            congr 1
            group
      _ = smulVtx φ ζ⁻¹ (smulVtx φ (ζ * y * ζ⁻¹) v₀) :=
            starTree_smulVtx_mul φ ζ⁻¹ (ζ * y * ζ⁻¹) v₀
      _ = smulVtx φ ζ⁻¹ v₀ := by rw [hfixV]
      _ = w := rfl
  -- a neighbour of `v₀` fixed by `y`: the source of the last arrow of the geodesic `w ↝ v₀`
  have hlen : 0 < (hT.geodesic w v₀).length := by
    rcases Nat.eq_zero_or_pos (hT.geodesic w v₀).length with h0 | hpos
    · exact absurd (Quiver.Path.eq_of_length_zero (hT.geodesic w v₀) h0) hw_ne
    · exact hpos
  obtain ⟨x, e, hx, -⟩ := exists_fixed_arrow_of_fixes_two hT hyw hyv₀
    (hT.geodesic_isReduced w v₀) hlen
  obtain ⟨-, he_lbl, he_x⟩ := arrow_lf_right (φ := φ) e
  have hxfix : y • ctr φ e.lbl = ctr φ e.lbl := by
    rw [← he_x]
    exact hx
  -- its stabiliser is a conjugate of the base subgroup
  let g : Psh φ := repC φ e.lbl
  have hgmk : (Quotient.mk'' g : Psh φ ⧸ baseSub φ) = e.lbl := repC_mk φ e.lbl
  have hstab : MulAction.stabilizer (Psh φ) (ctr φ (Quotient.mk'' g)) =
      (baseSub φ).map (MulEquiv.toMonoidHom (MulAut.conj g)) :=
    (pushoutStarTree_stabilizers φ).1 g
  have hmem2 : y ∈ (baseSub φ).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
    rw [← hstab, hgmk]
    exact MulAction.mem_stabilizer_iff.mpr hxfix
  obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hmem2
  have hconjh : g⁻¹ * y * g = h := by
    have hstep : (MulEquiv.toMonoidHom (MulAut.conj g)) h = g * h * g⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hhy, hstep]
    group
  -- `g` belongs to the `i₀`-th vertex group, because `v₀` is its leaf at the base coset
  have hg_ofSub : g ∈ ofSub φ i₀ := by
    have h1 : lf φ i₀ (Quotient.mk'' g) = lf φ i₀ (Quotient.mk'' (1 : Psh φ)) := by
      rw [hgmk]
      exact he_lbl
    have h2 : (Quotient.mk'' g : Psh φ ⧸ ofSub φ i₀) = Quotient.mk'' (1 : Psh φ) :=
      (starTree_lf_mk_eq_iff φ i₀ g 1).mp h1
    have h3 : g⁻¹ * 1 ∈ ofSub φ i₀ := QuotientGroup.eq.mp h2
    simpa using h3
  have hginv : g⁻¹ ∈ ofSub φ i₀ := (ofSub φ i₀).inv_mem hg_ofSub
  obtain ⟨k, hk⟩ : ∃ k : G i₀, Monoid.PushoutI.of (φ := φ) i₀ k = g⁻¹ := hginv
  refine ⟨k, ?_⟩
  have hkey : Monoid.PushoutI.of (φ := φ) i₀ k * y *
      (Monoid.PushoutI.of (φ := φ) i₀ k)⁻¹ = h := by
    rw [hk, inv_inv]
    exact hconjh
  rw [hkey]
  exact hh

end Work.ORLocInd.CohenLyndon
