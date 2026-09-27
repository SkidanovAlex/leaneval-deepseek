import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensThetaRows
import Submission.Work.Drive.PushDisc.milnorLens

/-!
# Injectivity of `fderiv θ` on the lens (`Work.Drive.PushDisc.thetaDiscInjective`)

`Work.Drive.PushDisc.thetaMap Δ U W S₂ c r` is the explicit map of the framing assembly

    θ (x,y,u,v) = Δ (x,y) + Σᵢ uᵢ • Uᵢ (x,y) + Σⱼ (r vⱼ) • Wⱼ (x,y)
                   + [ S₂ (x, r • v) - Δ (x, c x) - (fderiv ℝ (fun w => S₂ (x,w)) 0) (r • v) ]

(`thetaMapDefs.lean`).  The **derivative row** of `θ` on the plane `{u = 0, v = 0}` is the framing

    fderiv ℝ θ (x,y,0,0) (a,b,u',v') = (fderiv ℝ Δ (x,y)) (a,b) + Σᵢ u'ᵢ • Uᵢ (x,y) + Σⱼ (r v'ⱼ) • Wⱼ (x,y),

so that `fderiv ℝ θ (x,y,0,0)` is injective as soon as the frame `[∂ₓΔ, ∂_yΔ, U, W]` is independent
at `(x,y)` and `r ≠ 0`.  `lensThetaRows` already proves this (conjunct 5) from the *global* rows
`S₂ (x,0) = Δ (x, c x)` for all `x`; the present lemma is the same statement with the rows only on
a window `|x| ≤ X` with `1 < X`.

The point is that the derivative row only ever uses the rows at the base point `x = p.1`, and the
lens satisfies `|p.1| ≤ 1 < X`.  Rather than re-deriving the (delicate) bracket derivative, we
replace the offending term `Δ (x, c x)` by `S₂ (x, 0)`: the *standard* bracket

    bracketStd S₂ r ξ = S₂ (ξ.1, r • ξ.2.2.2) - S₂ (ξ.1, 0)
                          - (fderiv ℝ (fun w => S₂ (ξ.1, w)) 0) (r • ξ.2.2.2)

has vanishing derivative on the plane `{u = 0, v = 0}` **unconditionally** (the two `S₂`-terms
cancel against the `v`-slot derivative), the modified map `thetaLoc`

    θ' (x,y,u,v) = Δ (x,y) + Σᵢ uᵢ • Uᵢ (x,y) + Σⱼ (r vⱼ) • Wⱼ (x,y) + bracketStd S₂ r (x,y,u,v)

agrees with `θ` on the window `|x| ≤ X`, and `fderiv` is a local operation.

The second half is the linear-algebra kernel argument of `lensThetaRows` (conjunct 5), reproduced
here in the vocabulary of the local derivative row.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff Topology
open Filter

variable {k : ℕ}

/-- The bracket of `θ` with the top-edge term `Δ (x, c x)` replaced by `S₂ (x, 0)` — i.e. the
bracket of the map whose rows are known on a window only.  Its derivative on the plane
`{u = 0, v = 0}` vanishes identically (see `hasFDerivAt_bracketStd`). -/
noncomputable def bracketStd (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (r : ℝ) (ξ : Work.Drive.Whitney.Mdl k) : Work.Drive.Whitney.Mdl k :=
  S₂ (ξ.1, r • ξ.2.2.2) - S₂ (ξ.1, 0)
    - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0) (r • ξ.2.2.2)

/-- The map `θ` with the top-edge term `Δ (x, c x)` of its bracket replaced by `S₂ (x, 0)`.  It
agrees with `thetaMap Δ U W S₂ c r` on the window where the top-edge row holds
(`thetaMap_eq_thetaLoc`) and its derivative on the plane `{u = 0, v = 0}` is the framing
`[∂ₓΔ, ∂_yΔ, U, W]` — this is the content of the proof of `thetaDiscInjective`. -/
noncomputable def thetaLoc (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (r : ℝ)
    (ξ : Work.Drive.Whitney.Mdl k) : Work.Drive.Whitney.Mdl k :=
  Δ (ξ.1, ξ.2.1)
    + (∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
    + (∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j)
    + bracketStd S₂ r ξ

/-- **The standard bracket has zero derivative on the plane `{u = 0, v = 0}`.**  This needs no row
on `S₂` at all: the `ξ ↦ S₂ (ξ.1, r • ξ.2.2.2)` term contributes `(fderiv ℝ S₂ (x,0)) ∘ kapV r`,
the `ξ ↦ S₂ (ξ.1, 0)` term contributes `- (fderiv ℝ S₂ (x,0)) ∘ inl ∘ prX` and the
`sndDeriv`-term contributes `- (fderiv ℝ S₂ (x,0)) ∘ inr ∘ (r • prV)`; since
`kapV r = inl ∘ prX + inr ∘ (r • prV)` the sum vanishes. -/
theorem hasFDerivAt_bracketStd (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂) (r x y : ℝ) :
    HasFDerivAt (bracketStd S₂ r) (0 : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k)
      (x, y, 0, 0) := by
  have hB1 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => S₂ (ξ.1, r • ξ.2.2.2))
      ((fderiv ℝ S₂ (x,0)).comp (kapV r)) (x,y,0,0) := by
    have hpt : (kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) = (x, 0) := by simp [kapV_apply]
    have hd : HasFDerivAt S₂ (fderiv ℝ S₂ ((kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k)))
        ((kapV r) ((x,y,0,0) : Work.Drive.Whitney.Mdl k)) := by
      rw [hpt]
      exact (hS₂.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have hcomp := hd.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k)
      (ContinuousLinearMap.hasFDerivAt (kapV r))
    rw [hpt] at hcomp
    exact hcomp
  have hB2 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => S₂ (ξ.1, (0 : EuclideanSpace ℝ (Fin k))))
      (((fderiv ℝ S₂ (x,0)).comp (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k)))).comp prX)
      (x,y,0,0) := by
    have hd : HasFDerivAt S₂ (fderiv ℝ S₂ (x, 0)) (x, 0) :=
      (hS₂.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    have h1 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => (ξ.1, (0 : EuclideanSpace ℝ (Fin k))))
        ((ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp prX) (x,y,0,0) := by
      have h2 := (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (0 : EuclideanSpace ℝ (Fin k))).comp
        ((x,y,0,0) : Work.Drive.Whitney.Mdl k) (ContinuousLinearMap.hasFDerivAt prX)
      exact h2
    have h3 := hd.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k) h1
    rw [← ContinuousLinearMap.comp_assoc] at h3
    exact h3
  have hB3 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
        (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0) (r • ξ.2.2.2))
      ((sndDeriv S₂ x).comp (r • prV)) (x,y,0,0) := by
    have hΛ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sndDeriv S₂) := contDiff_sndDeriv S₂ hS₂
    have hdΛ : DifferentiableAt ℝ (sndDeriv S₂) x :=
      (hΛ.differentiable (by simp)).differentiableAt
    have hcl : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => sndDeriv S₂ ξ.1)
        ((fderiv ℝ (sndDeriv S₂) x).comp prX) (x,y,0,0) := by
      have hcomp : HasFDerivAt (sndDeriv S₂ ∘ prX)
          ((fderiv ℝ (sndDeriv S₂) x) ∘SL prX) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
        hdΛ.hasFDerivAt.comp ((x,y,0,0) : Work.Drive.Whitney.Mdl k)
          (ContinuousLinearMap.hasFDerivAt prX)
      exact hcomp
    have hu : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k => r • ξ.2.2.2)
        (r • prV) (x,y,0,0) := by
      have hcomp : HasFDerivAt (r • prV) (r • prV) ((x,y,0,0) : Work.Drive.Whitney.Mdl k) :=
        ContinuousLinearMap.hasFDerivAt (r • prV)
      exact hcomp
    have h3 : HasFDerivAt (fun ξ : Work.Drive.Whitney.Mdl k =>
          sndDeriv S₂ ξ.1 (r • prV ξ)) ((sndDeriv S₂ x).comp (r • prV)) (x,y,0,0) := by
      have h := hcl.clm_apply hu
      have hderiv : (sndDeriv S₂ x) ∘SL (r • prV)
          + ((fderiv ℝ (sndDeriv S₂) x).comp prX).flip
              ((r • prV) ((x,y,0,0) : Work.Drive.Whitney.Mdl k))
          = (sndDeriv S₂ x).comp (r • prV) := by
        simp
      exact h.congr_fderiv hderiv
    exact h3
  have hD := (hB1.sub hB2).sub hB3
  have hzero : ((fderiv ℝ S₂ (x,0)).comp (kapV r))
      - (((fderiv ℝ S₂ (x,0)).comp
          (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k)))).comp prX)
      - ((sndDeriv S₂ x).comp (r • prV))
      = (0 : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) := by
    have hk : kapV r = (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp prX
        + (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k))).comp (r • prV) := by
      apply ContinuousLinearMap.ext
      intro ξ
      simp only [add_apply, ContinuousLinearMap.comp_apply, kapV_apply,
        smul_apply, prV_apply, prX_apply]
      ext <;> simp
    rw [hk, sndDeriv_eq_comp_inr S₂ hS₂ x, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    abel
  exact hD.congr_fderiv hzero

/-- `θ` and its local model `thetaLoc` agree on the window `|x| ≤ X`, where the top-edge row
`S₂ (x,0) = Δ (x, c x)` holds. -/
theorem thetaMap_eq_thetaLoc (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ) (r X : ℝ)
    (hS₂0 : ∀ x : ℝ, |x| ≤ X → S₂ (x, 0) = Δ (x, c x))
    (ξ : Work.Drive.Whitney.Mdl k) (hξ : |ξ.1| ≤ X) :
    thetaMap Δ U W S₂ c r ξ = thetaLoc Δ U W S₂ r ξ := by
  have hrow : S₂ (ξ.1, 0) = Δ (ξ.1, c ξ.1) := hS₂0 ξ.1 hξ
  simp only [thetaMap, thetaLoc, bracketStd]
  rw [hrow]

/-- **The derivative row of `θ` on the plane `{u = 0, v = 0}`, on a window.**  Only the rows at the
base point `x` are used (`|x| ≤ X`), and `r` may be any real.  This is the local form of conjunct 4
of `lensThetaRows`. -/
theorem hasFDerivAt_thetaMap_plane (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ) (r X : ℝ)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hS₂0 : ∀ x : ℝ, |x| ≤ X → S₂ (x, 0) = Δ (x, c x))
    (x y : ℝ) (hx : |x| < X) :
    fderiv ℝ (thetaMap Δ U W S₂ c r) (x, y, 0, 0)
      = ((fderiv ℝ Δ (x, y)).comp piXY)
        + (∑ i : Fin k, (coU i).smulRight (U (x, y) i))
        + (∑ j : Fin k, (r • coV j).smulRight (W (x, y) j)) := by
  have hA := hasFDerivAt_delta Δ hΔ x y
  have hB := hasFDerivAt_usum U hU x y
  have hC := hasFDerivAt_vsum W hW r x y
  have hBr := hasFDerivAt_bracketStd S₂ hS₂ r x y
  have hsum := ((hA.add hB).add hC).add hBr
  have hfun : thetaLoc Δ U W S₂ r
      = ((fun ξ : Work.Drive.Whitney.Mdl k => Δ (ξ.1, ξ.2.1))
          + (fun ξ : Work.Drive.Whitney.Mdl k =>
              ∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
          + (fun ξ : Work.Drive.Whitney.Mdl k =>
              ∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j))
          + (bracketStd S₂ r) := by
    funext ξ
    rfl
  have hsum' : HasFDerivAt (thetaLoc Δ U W S₂ r)
      ((((fderiv ℝ Δ (x, y)).comp piXY)
        + (∑ i : Fin k, (coU i).smulRight (U (x, y) i))
        + (∑ j : Fin k, (r • coV j).smulRight (W (x, y) j))) + 0)
      (x, y, 0, 0) := hfun.symm ▸ hsum
  rw [add_zero] at hsum'
  have hnb : ∀ᶠ ξ : Work.Drive.Whitney.Mdl k in 𝓝 ((x, y, 0, 0) : Work.Drive.Whitney.Mdl k),
      |ξ.1| < X :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).mem_nhds (by simpa using hx)
  have heq : thetaMap Δ U W S₂ c r
      =ᶠ[𝓝 ((x, y, 0, 0) : Work.Drive.Whitney.Mdl k)] thetaLoc Δ U W S₂ r := by
    filter_upwards [hnb] with ξ hξ
    exact thetaMap_eq_thetaLoc Δ U W S₂ c r X hS₂0 ξ (le_of_lt hξ)
  exact (hsum'.congr_of_eventuallyEq heq).fderiv

/-- **Injectivity of the derivative of `θ` on the lens.**  On the lens the base point `p.1` satisfies
`|p.1| ≤ 1 < X`, so the local derivative row applies; the frame `[∂ₓΔ, ∂_yΔ, U, W]` is independent
there and `r ≠ 0`, so the derivative is injective (kernel argument, as in `lensThetaRows`). -/
theorem thetaDiscInjective {k : ℕ}
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ) (r X : ℝ) (hr : 0 < r) (hX : 1 < X)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hS₂0 : ∀ x : ℝ, |x| ≤ X → S₂ (x, 0) = Δ (x, c x))
    (hWc : ∀ x : ℝ, |x| ≤ X → W (x, c x) = V x)
    (hV : ∀ x : ℝ, |x| ≤ X → ∀ w : EuclideanSpace ℝ (Fin k),
      (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S₂ (x, w')) 0) w
        = ∑ j : Fin k, w j • V x j)
    (hframe : ∀ p ∈ Work.Drive.PushDisc.lensK, LinearIndependent ℝ (Fin.append (Fin.append
      (Work.Drive.PushDisc.planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
        (fun q => fderiv ℝ Δ q (0, 1)) p) (U p)) (W p))) :
    ∀ p ∈ Work.Drive.PushDisc.lensK,
      Function.Injective
        (fderiv ℝ (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) (p.1, p.2, 0, 0)) := by
  intro p hp
  have hx : |p.1| < X := lt_of_le_of_lt hp.1 hX
  set L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k :=
    ((fderiv ℝ Δ (p.1, p.2)).comp piXY)
      + (∑ i : Fin k, (coU i).smulRight (U (p.1, p.2) i))
      + (∑ j : Fin k, (r • coV j).smulRight (W (p.1, p.2) j)) with hLdef
  have hL : fderiv ℝ (thetaMap Δ U W S₂ c r) (p.1, p.2, 0, 0) = L := by
    rw [hLdef]
    exact hasFDerivAt_thetaMap_plane Δ U W S₂ c r X hΔ hU hW hS₂ hS₂0 p.1 p.2 hx
  rw [hL]
  have happ : ∀ h : Work.Drive.Whitney.Mdl k,
      L h = (fderiv ℝ Δ (p.1, p.2)) (h.1, h.2.1)
        + (∑ i : Fin k, h.2.2.1 i • U (p.1, p.2) i)
        + (∑ j : Fin k, (r * h.2.2.2 j) • W (p.1, p.2) j) := by
    intro h
    rw [hLdef]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, sum_apply, smul_apply, piXY_apply, coU_apply,
      coV_apply, smul_eq_mul]
  set F : Fin (2 + k + k) → Work.Drive.Whitney.Mdl k :=
    Fin.append (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
      (fun q => fderiv ℝ Δ q (0, 1)) p) (U p)) (W p) with hFdef
  have hF : LinearIndependent ℝ F := hFdef.symm ▸ hframe p hp
  have hker : ∀ h : Work.Drive.Whitney.Mdl k, L h = 0 → h = 0 := by
    intro h hh
    rw [happ h] at hh
    set g : Fin (2 + k + k) → ℝ :=
      Fin.append (Fin.append (![h.1, h.2.1] : Fin 2 → ℝ) h.2.2.1) (fun j => r * h.2.2.2 j)
      with hgdef
    have hsum_eq : ∑ i : Fin (2 + k + k), g i • F i
        = (fderiv ℝ Δ (p.1, p.2)) (h.1, h.2.1)
          + (∑ i : Fin k, h.2.2.1 i • U (p.1, p.2) i)
          + (∑ j : Fin k, (r * h.2.2.2 j) • W (p.1, p.2) j) := by
      rw [hgdef, hFdef, sum_fin_append_smul, sum_fin_append_smul, Fin.sum_univ_two]
      simp only [planeFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hlin : h.1 • (fderiv ℝ Δ p (1, 0)) + h.2.1 • (fderiv ℝ Δ p (0, 1))
          = (fderiv ℝ Δ p) (h.1, h.2.1) := by
        have hp' : (h.1, h.2.1) = h.1 • (1, 0) + h.2.1 • (0, 1) := by
          ext <;> simp
        rw [hp', map_add, map_smul, map_smul]
      rw [hlin]
    have hzero : ∑ i : Fin (2 + k + k), g i • F i = 0 := by
      rw [hsum_eq]; exact hh
    have hg : ∀ i, g i = 0 := (Fintype.linearIndependent_iff.mp hF) g hzero
    have hc1 : h.1 = 0 := by
      have h0 := hg (Fin.castAdd k (Fin.castAdd k (0 : Fin 2)))
      rwa [show g (Fin.castAdd k (Fin.castAdd k (0 : Fin 2))) = h.1 from by
        simp [hgdef, Fin.append_left]] at h0
    have hc2 : h.2.1 = 0 := by
      have h0 := hg (Fin.castAdd k (Fin.castAdd k (1 : Fin 2)))
      rwa [show g (Fin.castAdd k (Fin.castAdd k (1 : Fin 2))) = h.2.1 from by
        simp [hgdef, Fin.append_left]] at h0
    have hcu : h.2.2.1 = 0 := by
      ext i
      have h0 := hg (Fin.castAdd k (Fin.natAdd 2 i))
      rwa [show g (Fin.castAdd k (Fin.natAdd 2 i)) = h.2.2.1 i from by
        simp [hgdef, Fin.append_left, Fin.append_right]] at h0
    have hcv : h.2.2.2 = 0 := by
      ext j
      have h0 := hg (Fin.natAdd (2 + k) j)
      have h0' : g (Fin.natAdd (2 + k) j) = r * h.2.2.2 j := by
        simp [hgdef, Fin.append_right]
      rw [h0', mul_eq_zero] at h0
      exact h0.resolve_left (ne_of_gt hr)
    ext <;> simp_all
  intro h₁ h₂ hh
  have hsub : h₁ - h₂ = 0 := hker (h₁ - h₂) (by rw [map_sub, hh, sub_self])
  exact sub_eq_zero.mp hsub

end Work.Drive.PushDisc
