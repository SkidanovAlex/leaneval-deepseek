import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Affine reparametrisation of the domain of a curve

The arrival of one stage of the routing (`arrivalGlue.lean`) produces the *glued* map
`G t = if t ≤ 1 then α t else c.symm (c (α 1) + (t - 1) • w)`, which is straight in the chart `c`
past the junction.  The seed of the next stage is a point `σ' = c.symm (c (α 1) + s • w)` of that
straight line, reached at parameter `1 + s`; the piece handed to `ray_of_pieces_with_germs` must
have its endpoint at parameter `1`, so it is the *affine reparametrisation*

    P t = G ((1 + s) * t).

This module contains the three transports this requires — `C^∞`, the pointwise immersion, and
`InjOn` on the unit interval — plus the rewriting of the straight chart germ under the
reparametrisation (the scalar identity `(a - 1) + (t - 1) * a = a * t - 1`).

* `contMDiff_comp_affine`;
* `injective_mfderiv_affine` (the derivative of the reparametrisation itself), used to transport the
  immersion through `mfderiv_comp` in `injective_mfderiv_comp_affine`;
* `injOn_comp_affine_Icc`;
* `affine_germ_rewrite`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M]

/-- **`C^∞` transport.**  Composing with an affine reparametrisation of the domain of `ℝ` keeps a
curve `C^∞`. -/
theorem contMDiff_comp_affine {F : ℝ → M} (hF : ContMDiff MCreal (MC n) smoothOrder F)
    (a b : ℝ) : ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => F (a * t + b)) := by
  have hφ : ContMDiff MCreal MCreal smoothOrder (fun t : ℝ => a * t + b) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  exact hF.comp hφ

/-- **The derivative of the reparametrisation.**  `t ↦ a * t + b` has injective derivative at every
point as soon as `a ≠ 0`.

The derivative is *not* computed in coordinates: the affine map `φ` has the smooth inverse
`ψ y = (y - b) / a`, so `ψ ∘ φ = id` and the chain rule exhibits `mfderiv ψ (φ t)` as a left inverse
of `mfderiv φ t`, which is therefore injective.  (This avoids the instance difficulties of the
`ℝ`-self-model `TangentSpace`, which make the coordinate form awkward to use.) -/
theorem injective_mfderiv_affine {a b t : ℝ} (ha : a ≠ 0) :
    Function.Injective (mfderiv MCreal MCreal (fun s : ℝ => a * s + b) t) := by
  have hne : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  set φ : ℝ → ℝ := fun s => a * s + b with hφdef
  set ψ : ℝ → ℝ := fun y => (y - b) / a with hψdef
  have hφsm : ContMDiff MCreal MCreal smoothOrder φ := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hψsm : ContMDiff MCreal MCreal smoothOrder ψ := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hcomp : ψ ∘ φ = id := by
    funext y
    simp only [Function.comp_apply, hφdef, hψdef, id_eq]
    field_simp
    ring
  have hchain := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MCreal) t
    (g := ψ) (f := φ) (hψsm.contMDiffAt.mdifferentiableAt hne)
    (hφsm.contMDiffAt.mdifferentiableAt hne)
  have hid : (mfderiv MCreal MCreal (ψ ∘ φ) t)
      = ContinuousLinearMap.id ℝ (TangentSpace MCreal t) := by
    rw [hcomp, mfderiv_id]
  intro u v huv
  have h1 : ∀ w : TangentSpace MCreal t,
      (mfderiv MCreal MCreal ψ (φ t)) ((mfderiv MCreal MCreal φ t) w) = w := by
    intro w
    have h2 : (mfderiv MCreal MCreal (ψ ∘ φ) t) w = w := by
      rw [hid]
      exact ContinuousLinearMap.id_apply w
    rw [hchain] at h2
    exact h2
  rw [← h1 u, huv, h1 v]

/-- **Immersion transport.**  The immersion property at every point is preserved by an affine
reparametrisation with `a ≠ 0` (the chain rule, the derivative of the reparametrisation being
injective). -/
theorem injective_mfderiv_comp_affine {F : ℝ → M} (hF : ContMDiff MCreal (MC n) smoothOrder F)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) F t))
    {a b : ℝ} (ha : a ≠ 0) :
    ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => F (a * s + b)) t) := by
  intro t
  have hne : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hφ : ContMDiff MCreal MCreal smoothOrder (fun s : ℝ => a * s + b) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hchain := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n) t
    (g := F) (f := fun s : ℝ => a * s + b)
    (hF.contMDiffAt.mdifferentiableAt hne) (hφ.contMDiffAt.mdifferentiableAt hne)
  have hfun : (fun s : ℝ => F (a * s + b))
      = F ∘ (fun s : ℝ => a * s + b) := rfl
  rw [hfun, hchain]
  exact (himm (a * t + b)).comp (injective_mfderiv_affine (b := b) ha)

/-- **`InjOn` transport.**  If `F` is injective on the interval `[b, a + b]` (`a > 0`), then the
reparametrised curve is injective on `[0, 1]`. -/
theorem injOn_comp_affine_Icc {F : ℝ → M} {a b : ℝ} (ha : 0 < a)
    (hF : Set.InjOn F (Set.Icc b (a + b))) :
    Set.InjOn (fun t : ℝ => F (a * t + b)) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx' : a * x + b ∈ Set.Icc b (a + b) :=
    ⟨by nlinarith [hx.1, ha], by nlinarith [hx.2, ha]⟩
  have hy' : a * y + b ∈ Set.Icc b (a + b) :=
    ⟨by nlinarith [hy.1, ha], by nlinarith [hy.2, ha]⟩
  have h := hF hx' hy' hxy
  have h2 : a * x = a * y := by linarith
  exact mul_left_cancel₀ (ne_of_gt ha) h2

/-- **The straight chart germ under the reparametrisation.**  With `σ = c.symm (c p + (a - 1) • w)`
(the seed reached at parameter `1 + s`, i.e. `a = 1 + s`), the chart line through `p` in the
direction `w`, reparametrised by `t ↦ a * t`, is the chart line *ending* at `σ`, in the direction
`a • w`. -/
theorem affine_germ_rewrite {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {p : M} {w : EuclideanSpace ℝ (Fin n)} {a : ℝ}
    (htgt : c p + (a - 1) • w ∈ c.target) (t : ℝ) :
    c.symm (c p + (a * t - 1) • w)
      = c.symm (c (c.symm (c p + (a - 1) • w)) + (t - 1) • (a • w)) := by
  rw [c.right_inv htgt]
  congr 1
  have hs : (a - 1) + (t - 1) * a = a * t - 1 := by ring
  have h1 : (a - 1) • w + (t - 1) • (a • w) = (a * t - 1) • w := by
    rw [smul_smul, ← hs, add_smul]
  rw [← h1, add_assoc]


/-- **Immersion transport, local form.**  The global `injective_mfderiv_comp_affine` asks the curve to
be an immersion *everywhere*, which fails for the cut glued map: its tail is eventually constant (that
is what makes it `C^∞`), so its `mfderiv` vanishes there.  The piece only traverses `[0, 1+s]`, so the
usable form is pointwise: an immersion at the *image* point `a * t + b` gives one at `t`. -/
theorem injective_mfderiv_comp_affine_at {F : ℝ → M} (hF : ContMDiff MCreal (MC n) smoothOrder F)
    {a b : ℝ} (ha : a ≠ 0) {t : ℝ}
    (h : Function.Injective (mfderiv MCreal (MC n) F (a * t + b))) :
    Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => F (a * s + b)) t) := by
  have hne : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hφ : ContMDiff MCreal MCreal smoothOrder (fun s : ℝ => a * s + b) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hchain := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n) t
    (g := F) (f := fun s : ℝ => a * s + b)
    (hF.contMDiffAt.mdifferentiableAt hne) (hφ.contMDiffAt.mdifferentiableAt hne)
  have hfun : (fun s : ℝ => F (a * s + b)) = F ∘ (fun s : ℝ => a * s + b) := rfl
  rw [hfun, hchain]
  exact h.comp (injective_mfderiv_affine (b := b) ha)

/-- **Immersion transport along `s ↦ a * s`, without the constant term.**  Same as
`injective_mfderiv_comp_affine_at`, but for the `b`-free reparametrisation: the variant to wire when
the transport's `b = 0` residue would otherwise have to be cancelled inside an `if`.  The inner map's
injective `mfderiv` is proved by the *inverse* argument (inverse `s ↦ s / a`), not by reusing
`injective_mfderiv_affine`, precisely so that no `+ 0` reappears. -/
theorem injective_mfderiv_comp_smul_at {F : ℝ → M} (hF : ContMDiff MCreal (MC n) smoothOrder F)
    {a : ℝ} (ha : a ≠ 0) {t : ℝ}
    (h : Function.Injective (mfderiv MCreal (MC n) F (a * t))) :
    Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => F (a * s)) t) := by
  have hne : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hinner : ContMDiff MCreal MCreal smoothOrder (fun s : ℝ => a * s) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hchain := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MC n) t
    (g := F) (f := fun s : ℝ => a * s)
    (hF.contMDiffAt.mdifferentiableAt hne) (hinner.contMDiffAt.mdifferentiableAt hne)
  have hfun : (fun s : ℝ => F (a * s)) = F ∘ (fun s : ℝ => a * s) := rfl
  rw [hfun, hchain]
  refine h.comp ?_
  set phi : ℝ → ℝ := fun s => a * s with hphidef
  set psi : ℝ → ℝ := fun y => y / a with hpsidef
  have hpsi : ContMDiff MCreal MCreal smoothOrder psi := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hcomp : psi ∘ phi = id := by
    funext y
    simp only [Function.comp_apply, hphidef, hpsidef, id_eq]
    field_simp
  have hphi : ContMDiff MCreal MCreal smoothOrder phi := by
    rw [hphidef]; exact hinner
  have hchain2 := mfderiv_comp (I := MCreal) (I' := MCreal) (I'' := MCreal) t
    (g := psi) (f := phi) (hpsi.contMDiffAt.mdifferentiableAt hne)
    (hphi.contMDiffAt.mdifferentiableAt hne)
  have hid : (mfderiv MCreal MCreal (psi ∘ phi) t)
      = ContinuousLinearMap.id ℝ (TangentSpace MCreal t) := by
    rw [hcomp, mfderiv_id]
  have hkey : ∀ w : TangentSpace MCreal t,
      (mfderiv MCreal MCreal psi (phi t)) ((mfderiv MCreal MCreal phi t) w) = w := by
    intro w
    have h2 : (mfderiv MCreal MCreal (psi ∘ phi) t) w = w := by
      rw [hid]
      exact ContinuousLinearMap.id_apply w
    rw [hchain2] at h2
    exact h2
  intro u v huv
  exact (hkey u).symm.trans
    ((congrArg (fun w => (mfderiv MCreal MCreal psi (phi t)) w) huv).trans (hkey v))

/-- **`InjOn` transport along `s ↦ a * s`, without the constant term** — the sibling of
`injOn_comp_affine_Icc` used for the piece `P = G ∘ ((1+s) ·)`.  (`injOn_comp_affine_Icc` would ask for
`G (a * t + 0)`, reintroducing the `b = 0` residue; see the house rule about not asking Lean to align
terms that are only provably equal.) -/
theorem injOn_comp_smul_Icc {F : ℝ → M} {a : ℝ} (ha : 0 < a)
    (hF : Set.InjOn F (Set.Icc (0:ℝ) a)) :
    Set.InjOn (fun t : ℝ => F (a * t)) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx' : a * x ∈ Set.Icc (0:ℝ) a := ⟨mul_nonneg ha.le hx.1, by nlinarith [hx.2, ha]⟩
  have hy' : a * y ∈ Set.Icc (0:ℝ) a := ⟨mul_nonneg ha.le hy.1, by nlinarith [hy.2, ha]⟩
  have h := hF hx' hy' hxy
  exact mul_left_cancel₀ (ne_of_gt ha) h

end

end Work.Noncompact.CompressionTube
