import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.Proj
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds
import Submission.Work.NN.Final.holderNorm_zero_clm_apply_le
import Submission.Work.NN.Final.HolderCongr
import Submission.Work.NN.Newton.newtonCorrDefs

/-
# Self-contained bundle for `Work.NN.Newton.coordDefectData`

The lemmas that `Work.NN.Newton.coordDefectData` is assembled from are collected in this module, with
their declarations prefixed by `z`.  Their originals live in the sibling modules `cddRel`,
`cddDefect`, `cddProj02`, `cddEexpr`, `cddQuadBound` and their helpers, which import
`Submission.Work.NN.Newton.coordDefectData` itself and therefore cannot be imported back into it.
The definitions `cdLam`, `cdEvec`, `cdIevec`, `cdD`, `cdL`, `cdDefA`, `cdE`, `cdQuad`, `cdRel` are
also declared here and are re-exported by `Submission.Work.NN.Newton.coordDefectData`.
-/

namespace Work.NN.Newton

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set


/-- The `l`-th coordinate functional `w ↦ w l` on `ℂⁿ`, as a real-linear map. -/
def cdLam {n : ℕ} (l : Fin n) : Work.NN.Core.Cn n →L[ℝ] ℂ := ContinuousLinearMap.proj l

@[simp] lemma cdLam_apply {n : ℕ} (l : Fin n) (w : Work.NN.Core.Cn n) : cdLam l w = w l := rfl

/-- The unit vector `e_j`. -/
def cdEvec {n : ℕ} (j : Fin n) : Work.NN.Core.Cn n := Pi.single j (1 : ℂ)

/-- The vector `i·e_j`. -/
def cdIevec {n : ℕ} (j : Fin n) : Work.NN.Core.Cn n := Pi.single j (Complex.I : ℂ)

/-- `(DA_z X)(Y)`, the directional derivative of the perturbation array `A`. -/
def cdD {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (X Y : Work.NN.Core.Cn n) : Work.NN.Core.Cn n :=
  (fderiv ℝ A z X) Y

/-- `λ_l((DA_z X)(Y))`, the `l`-th coordinate of `(DA_z X)(Y)`. -/
def cdL {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y : Work.NN.Core.Cn n) : ℂ :=
  cdLam l (cdD A z X Y)

/-- The "linear", Nijenhuis-type expression `X = λ(DA[e_j]e_k) − λ(DA[e_k]e_j)
+ i λ(DA[ie_j]e_k) − i λ(DA[ie_k]e_j)`: `(4/i)·(∂̄_j F_k − ∂̄_k F_j)` for the coordinate datum
`F = coordDatum A l`. -/
def cdDefA {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  cdL A z l (cdEvec j) (cdEvec k) - cdL A z l (cdEvec k) (cdEvec j)
    + Complex.I * cdL A z l (cdIevec j) (cdEvec k) - Complex.I * cdL A z l (cdIevec k) (cdEvec j)

/-- The `(0,2)`-form-level expansion `Eexpr` of `(8/i)·proj02 J (dOne (∂̄_J z_l)) z e_j e_k`. -/
def cdE {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  cdL A z l (cdEvec j) (cdEvec k) - cdL A z l (cdEvec k) (cdEvec j)
    + Complex.I * cdL A z l ((Work.NN.Core.JstdCn n + A) z (cdEvec j)) (cdEvec k)
    - Complex.I * cdL A z l (cdEvec k) ((Work.NN.Core.JstdCn n + A) z (cdEvec j))
    + Complex.I * cdL A z l (cdEvec j) ((Work.NN.Core.JstdCn n + A) z (cdEvec k))
    - Complex.I * cdL A z l ((Work.NN.Core.JstdCn n + A) z (cdEvec k)) (cdEvec j)
    - cdL A z l ((Work.NN.Core.JstdCn n + A) z (cdEvec j)) ((Work.NN.Core.JstdCn n + A) z (cdEvec k))
    + cdL A z l ((Work.NN.Core.JstdCn n + A) z (cdEvec k)) ((Work.NN.Core.JstdCn n + A) z (cdEvec j))

/-- The ten "quadratic" terms of `Eexpr − 2·cdDefA`: every term is a product of an entry of `A`
with an entry of `DA`, hence of size `a²`. -/
def cdQuad {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) : ℂ :=
  Complex.I * cdL A z l (A z (cdEvec j)) (cdEvec k)
    + Complex.I * cdLam l (A z (cdD A z (cdEvec k) (cdEvec j)))
    - Complex.I * cdLam l (A z (cdD A z (cdEvec j) (cdEvec k)))
    - Complex.I * cdL A z l (A z (cdEvec k)) (cdEvec j)
    + cdLam l (A z (cdD A z (cdIevec j) (cdEvec k)))
    - cdL A z l (A z (cdEvec j)) (cdIevec k)
    - cdL A z l (A z (cdEvec j)) (A z (cdEvec k))
    - cdLam l (A z (cdD A z (cdIevec k) (cdEvec j)))
    + cdL A z l (A z (cdEvec k)) (cdIevec j)
    + cdL A z l (A z (cdEvec k)) (A z (cdEvec j))

/-- The pointwise differentiated almost-complexity relation
`i·m(X,w) + m(X,iw) + m(X, A z w) + λ(A z (m(X,w))) = 0`, where `m(X,w) = λ_l((DA_z X)(w))`.
It is the derivative of `(Jstd + A)² = −1`. -/
def cdRel {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) : Prop :=
  ∀ X w : Work.NN.Core.Cn n,
    Complex.I * cdL A z l X w + cdL A z l X (Complex.I • w) + cdL A z l X (A z w)
      + cdLam l (A z (cdD A z X w)) = 0

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddRel` -/

namespace Work.NN.Newton

open scoped ContDiff
open Set Filter

/-- `z' ↦ (Jstd + A) z'` has derivative `fderiv ℝ A z` at `z`, since `Jstd` is constant. -/
private lemma hasFDerivAt_Jstd_add {n : ℕ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {z : Work.NN.Core.Cn n} (hAdiff : DifferentiableAt ℝ A z) :
    HasFDerivAt (fun z' : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) z')
      (fderiv ℝ A z) z := by
  have key : (fun z' : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) z')
      = (fun _ : Work.NN.Core.Cn n =>
          Complex.I • (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)) + A := rfl
  rw [key]
  simpa only [zero_add] using (hasFDerivAt_const (x := z)
    (c := Complex.I • (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n))).add hAdiff.hasFDerivAt

/-- **The differentiated almost-complexity relation.**

Let `A` be smooth on the polydisc `P_r` and suppose that `J = Jstd + A` is almost complex there,
`(Jstd+A) z' ((Jstd+A) z' v) = -v` for all `z' ∈ P_r`, `v`.  Then at every `z ∈ P_r` the identity
`(Jstd+A)² = -1` may be differentiated: for all `X, w ∈ ℂⁿ`

`i·m(X,w) + m(X, i·w) + m(X, A z w) + λ_l(A z (m(X,w))) = 0`,

where `m(X,w) = λ_l((DA_z X)(w))`; this is exactly the predicate `cdRel A z l`
(`Work.NN.Newton.cdRel`, defined in `Submission.Work.NN.Newton.coordDefectData`).

Proof: differentiate `g_v(z') = (Jstd+A) z' ((Jstd+A) z' v)` at `z`; it is locally constant equal
to `-v` on the open polydisc, so its `fderiv` vanishes, and the product rule computes it as
`(DA_{z} X)((Jstd+A) z v) + (Jstd+A) z ((DA_z X) v)`.  Take `λ_l` and put `w = v`. -/
theorem zcddRel {n : ℕ} {r : ℝ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)))
    (hac : ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
      ∀ v : Work.NN.Core.Cn n,
        (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v)
    {z : Work.NN.Core.Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    (l : Fin n) : Work.NN.Newton.cdRel A z l := by
  -- the polydisc is open and contains `z`, hence is a neighbourhood of `z`
  have hP : Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) ∈ nhds z :=
    (Work.CR.Flat.isOpen_polydisc _ _).mem_nhds hz
  -- `A` is differentiable at `z` (it is smooth of every order on `P_r`)
  have hAdiff : DifferentiableAt ℝ A z :=
    ((hA 1).contDiffAt hP).differentiableAt (by norm_num)
  have hT := hasFDerivAt_Jstd_add (A := A) hAdiff
  -- the standard structure is multiplication by `i`
  have hJz : ∀ u : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z u = Complex.I • u + A z u := by
    intro u; simp [Work.NN.Core.JstdCn]
  intro X w
  -- product rule for `g_w`
  have hU : HasFDerivAt (fun z' : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) z' w)
      ((fderiv ℝ A z).flip w) z := by
    have h := HasFDerivAt.clm_apply hT (hasFDerivAt_const (x := z) (c := w))
    simpa using h
  have hF := HasFDerivAt.clm_apply hT hU
  -- `g_w` is constantly `-w` near `z`
  have hconst : (fun z' : Work.NN.Core.Cn n =>
        (Work.NN.Core.JstdCn n + A) z' ((Work.NN.Core.JstdCn n + A) z' w))
      =ᶠ[nhds z] fun _ => -w := by
    filter_upwards [hP] with z' hz'
    exact hac z' hz' w
  have hzero : fderiv ℝ (fun z' : Work.NN.Core.Cn n =>
      (Work.NN.Core.JstdCn n + A) z' ((Work.NN.Core.JstdCn n + A) z' w)) z = 0 := by
    rw [hconst.fderiv_eq]
    simp
  -- hence the explicit derivative vanishes
  have hL : ((Work.NN.Core.JstdCn n + A) z ∘SL (fderiv ℝ A z).flip w
      + (fderiv ℝ A z).flip ((Work.NN.Core.JstdCn n + A) z w)) = 0 := by
    rw [← hF.fderiv]; exact hzero
  have hX : (((Work.NN.Core.JstdCn n + A) z ∘SL (fderiv ℝ A z).flip w
      + (fderiv ℝ A z).flip ((Work.NN.Core.JstdCn n + A) z w)) X) l = 0 := by
    rw [hL, zero_apply, Pi.zero_apply]
  -- expand in coordinates
  have expand : ((((Work.NN.Core.JstdCn n + A) z ∘SL (fderiv ℝ A z).flip w
        + (fderiv ℝ A z).flip ((Work.NN.Core.JstdCn n + A) z w)) X) l)
      = Complex.I * Work.NN.Newton.cdL A z l X w + Work.NN.Newton.cdL A z l X (Complex.I • w)
        + Work.NN.Newton.cdL A z l X (A z w)
        + (Work.NN.Newton.cdLam l) (A z (Work.NN.Newton.cdD A z X w)) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      add_apply, smul_apply, one_apply_eq_self,
      Work.NN.Core.JstdCn, map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Work.NN.Newton.cdL, Work.NN.Newton.cdD, Work.NN.Newton.cdLam_apply]
    ring
  rw [← expand]
  exact hX

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddDefect` -/

namespace Work.NN.Newton

noncomputable section

open Set

/-- **The derivative of the coordinate datum.**  Since `coordDatum A l q z = (i/2)·(A z e_q)_l`,
the chain rule gives, for every vector `X`,

`D_z (coordDatum A l q) X = (i/2)·((DA_z X)(e_q))_l`. -/
lemma zfderiv_coordDatum {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (hA : DifferentiableAt ℝ A z)
    (l q : Fin n) (X : Work.NN.Core.Cn n) :
    fderiv ℝ (coordDatum A l q) z X
      = (Complex.I / 2)
          * ((fderiv ℝ A z X) (Pi.single q (1 : ℂ))) l := by
  have h1 : HasFDerivAt (fun z' : Work.NN.Core.Cn n => A z' (Pi.single q (1 : ℂ)))
      ((fderiv ℝ A z).flip (Pi.single q (1 : ℂ))) z := by
    simpa using hA.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single q (1 : ℂ)) z)
  have h2 : HasFDerivAt (fun z' : Work.NN.Core.Cn n => (A z' (Pi.single q (1 : ℂ))) l)
      ((ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ).comp
        ((fderiv ℝ A z).flip (Pi.single q (1 : ℂ)))) z := by
    have h := (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ)).comp z h1
    simpa [Function.comp_def] using h
  have h3 : HasFDerivAt
      (fun z' : Work.NN.Core.Cn n => (Complex.I / 2) * (A z' (Pi.single q (1 : ℂ))) l)
      ((Complex.I / 2) • ((ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ).comp
        ((fderiv ℝ A z).flip (Pi.single q (1 : ℂ))))) z :=
    h2.const_mul (Complex.I / 2)
  have h4 : HasFDerivAt (coordDatum A l q)
      ((Complex.I / 2) • ((ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ).comp
        ((fderiv ℝ A z).flip (Pi.single q (1 : ℂ))))) z := by
    rw [coordDatum_eq_fun]
    exact h3
  rw [h4.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

/-- **The flat `∂̄`-defect of the coordinate datum is `(i/4)·cdDefA`.**

The coordinate datum of `z_l` is `F^{(l)}_k z = Lcoef A (· l) k z = (i/2)(A z e_k)_l`, so for
`X` a vector and `w` a fixed vector, `fderiv ℝ (fun z' => (A z' w)_l) z X = λ_l((DA_z X)(w))`.
Hence with `∂̄_j F = (1/2)(D_{e_j}F + i D_{i e_j}F)`,

`∂̄_j F^{(l)}_k z - ∂̄_k F^{(l)}_j z = (i/4)·( λ_l(DA_z e_j e_k) - λ_l(DA_z e_k e_j)
    + i λ_l(DA_z (i e_j) e_k) - i λ_l(DA_z (i e_k) e_j) ) = (i/4)·cdDefA A z l j k`

(`cdDefA`, `cdL`, `cdD`, `cdEvec`, `cdIevec` are defined in
`Submission.Work.NN.Newton.coordDefectData`; `coordDefect` is
`Work.NN.Newton.coordDefect A l j k z = ddbar Jstd (coordDatum A l) j k z = ∂̄_j F_k - ∂̄_k F_j`,
from `Submission.Work.NN.Newton.newtonCorrDefs`). -/
theorem zcddDefect {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) (hA : DifferentiableAt ℝ A z) :
    Work.NN.Newton.coordDefect A l j k z
      = (Complex.I / 4) * Work.NN.Newton.cdDefA A z l j k := by
  have hjk := zfderiv_coordDatum A z hA l k (Pi.single j (1 : ℂ))
  have hji := zfderiv_coordDatum A z hA l k (Pi.single j (Complex.I : ℂ))
  have hkj := zfderiv_coordDatum A z hA l j (Pi.single k (1 : ℂ))
  have hki := zfderiv_coordDatum A z hA l j (Pi.single k (Complex.I : ℂ))
  rw [coordDefect_apply, Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hjk, hji, hkj, hki]
  simp only [cdDefA, cdL, cdD, cdLam_apply, cdEvec, cdIevec]
  ring

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddProj02` -/

namespace Work.NN.Newton

noncomputable section

open Work.NN.Core

variable {n : ℕ}

/-! ## Computational preliminaries

The three lemmas below expand `proj02 J (dOne (∂̄_J λ_l))` on the coordinate functional
`λ_l = cdLam l`.  They are the only computations in this file; the identity requested by
`zcddProj02` is then a literal expansion of `proj02` and `cdE`.
-/

/-- **The coordinate functional is real-linear, so `∂̄_J λ_l` is an affine function of `z`.**
For every `z'` and every vector `W`,
`∂̄_{Jstd + A} λ_l (z')(W) = (1/2)·(W_l + i·(((Jstd + A) z') W)_l)`. -/
lemma zdbarCn_cdLam_apply (A : Cn n → Cn n →L[ℝ] Cn n) (z' : Cn n) (l : Fin n) (W : Cn n) :
    dbarCn (JstdCn n + A) (cdLam l) z' W
      = (1 / 2 : ℂ) * (W l + Complex.I * ((JstdCn n + A) z' W) l) := by
  rw [dbarCn_apply, ContinuousLinearMap.fderiv]
  simp

/-- The coordinate expansion of the perturbed structure:
`((Jstd + A) z' W)_l = i·W_l + (A z' W)_l`. -/
lemma zJstd_add_apply_coord (A : Cn n → Cn n →L[ℝ] Cn n) (z' : Cn n) (l : Fin n) (W : Cn n) :
    ((JstdCn n + A) z' W) l = Complex.I * W l + (A z' W) l := by
  simp [Pi.add_apply, add_apply, JstdCn_apply, smul_eq_mul]

/-- **The derivative of `z' ↦ ∂̄_J λ_l (z')(W)`.**  Since `Jstd z` is the constant multiplication by
`i`, only the perturbation `A` contributes:
`d_{z,V} (∂̄_J λ_l (·)(W)) = (i/2)·λ_l((DA_z V)(W)) = (i/2)·cdL A z l V W`. -/
lemma zfderiv_dbarCn_cdLam (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) (l : Fin n)
    (hA : DifferentiableAt ℝ A z) (W V : Cn n) :
    fderiv ℝ (fun z' => dbarCn (JstdCn n + A) (cdLam l) z' W) z V
      = (Complex.I / 2) * cdL A z l V W := by
  -- `z' ↦ (A z' W) l` is `λ_l ∘ (ev_W ∘ A)`, hence has derivative `λ_l ∘ (ev_W ∘ DA_z)`.
  have hG : HasFDerivAt (fun z' => (A z' W) l)
      ((cdLam l).comp ((ContinuousLinearMap.apply ℝ (Cn n) W).comp (fderiv ℝ A z))) z := by
    have h2 : HasFDerivAt (fun z' => A z' W)
        ((ContinuousLinearMap.apply ℝ (Cn n) W).comp (fderiv ℝ A z)) z :=
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ (Cn n) W)).comp z
        hA.hasFDerivAt
    exact (ContinuousLinearMap.hasFDerivAt (cdLam l)).comp z h2
  -- `∂̄_J λ_l (z')(W) = c + (i/2)·(A z' W)_l` with `c = (1/2)(W_l + i·i·W_l)` independent of `z'`.
  have hF : HasFDerivAt
      (fun z' => ((1 / 2 : ℂ) * (W l + Complex.I * (Complex.I * W l)))
        + ((1 / 2 : ℂ) * Complex.I) * (A z' W) l)
      (((1 / 2 : ℂ) * Complex.I)
        • ((cdLam l).comp ((ContinuousLinearMap.apply ℝ (Cn n) W).comp (fderiv ℝ A z)))) z :=
    (hG.const_mul ((1 / 2 : ℂ) * Complex.I)).const_add
      ((1 / 2 : ℂ) * (W l + Complex.I * (Complex.I * W l)))
  have hfun : (fun z' => dbarCn (JstdCn n + A) (cdLam l) z' W)
      = fun z' => ((1 / 2 : ℂ) * (W l + Complex.I * (Complex.I * W l)))
        + ((1 / 2 : ℂ) * Complex.I) * (A z' W) l := by
    funext z'
    rw [dbarCn_apply, ContinuousLinearMap.fderiv]
    simp only [cdLam_apply]
    rw [zJstd_add_apply_coord]
    ring
  rw [hfun, hF.fderiv]
  show (((1 / 2 : ℂ) * Complex.I)
      • ((cdLam l).comp ((ContinuousLinearMap.apply ℝ (Cn n) W).comp (fderiv ℝ A z)))) V
      = (Complex.I / 2) * cdL A z l V W
  rw [show (((1 / 2 : ℂ) * Complex.I)
        • ((cdLam l).comp ((ContinuousLinearMap.apply ℝ (Cn n) W).comp (fderiv ℝ A z)))) V
      = ((1 / 2 : ℂ) * Complex.I) * (cdL A z l V W) from rfl]
  ring

/-- **The form-level expansion.**  The exterior derivative of the `(0,1)`-form `∂̄_J λ_l` is
`d(∂̄_J λ_l)_z(V,W) = (i/2)·(λ_l((DA_z V)(W)) − λ_l((DA_z W)(V)))`, i.e. `(i/2)` times the
antisymmetrisation of the bilinear form `(X,Y) ↦ λ_l((DA_z X)(Y))`. -/
lemma zdOne_dbarCn_cdLam (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) (l : Fin n)
    (hA : DifferentiableAt ℝ A z) (V W : Cn n) :
    Work.NN.Final.dOne (fun z' => dbarCn (JstdCn n + A) (cdLam l) z') z V W
      = (Complex.I / 2) * (cdL A z l V W - cdL A z l W V) := by
  simp only [Work.NN.Final.dOne]
  simp only [zfderiv_dbarCn_cdLam A z l hA]
  ring

/-- **The form-level expansion of `proj02 J (dOne (∂̄_J z_l))` on the coordinate functions.**

With `J = Jstd + A` and `u = z_l` (the `l`-th coordinate function, real-linear, so
`dbarCn J u z v = (1/2)(v l + i·((J z v) l))`), one has, for every `V, W`,

`dOne (fun z'' => dbarCn J u z'') z V W = (i/2)·( λ_l(DA_z V W) - λ_l(DA_z W V) )`,

and therefore, for the basis vectors `e_j`, `e_k`,

`proj02 J (fun z' => dOne (fun z'' => dbarCn J u z'') z') z e_j e_k = (i/8)·cdE A z l j k`,

where `cdE` is the eight-term expansion defined in
`Submission.Work.NN.Newton.coordDefectData`.  (This is a purely computational identity: expand
`(Jstd + A) z V = i·V + A z V`, use the real bilinearity of `(X,Y) ↦ λ_l((DA_z X)(Y))` in both
slots, and collect.  Numerically verified: the identity holds to `10^{-11}`, and
`(8/i)·proj02 = cdE` exactly.) -/
theorem zcddProj02 {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) (hA : DifferentiableAt ℝ A z) :
    Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne
          (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
            (Work.NN.Newton.cdLam l) z'') z')
        z (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k)
      = (Complex.I / 8) * Work.NN.Newton.cdE A z l j k := by
  simp only [Work.NN.Final.proj02, zdOne_dbarCn_cdLam A z l hA, cdE]
  ring

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddEexpr` -/

namespace Work.NN.Newton

noncomputable section

open scoped ContDiff

/-! ### Elementary facts about `cdL`

`cdL A z l X Y = λ_l((DA_z X)(Y))` is the `l`-th coordinate of the directional derivative of the
perturbation array `A` at `z`, applied to `(X, Y)`; it is real-bilinear in `(X, Y)`
(`zcdL_add_left`, `zcdL_add_right`, `zcdL_smul_left`, `zcdL_smul_right`).  These are the expansion
rules used to turn the eight-term expression `cdE` into its `18`-term polynomial form.
-/

/-- `cdIevec j = i • cdEvec j`: the basic vector `i·e_j` is `i` times the basic vector `e_j`. -/
lemma zcdIevec_eq_smul {n : ℕ} (j : Fin n) : cdIevec j = Complex.I • cdEvec j := by
  simp [cdIevec, cdEvec, Work.NN.Core.smul_single_I]

/-- `cdL` is additive in its first slot. -/
lemma zcdL_add_left {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X₁ X₂ Y : Work.NN.Core.Cn n) :
    cdL A z l (X₁ + X₂) Y = cdL A z l X₁ Y + cdL A z l X₂ Y := by
  simp [cdL, cdD, cdLam, map_add]

/-- `cdL` is additive in its second slot. -/
lemma zcdL_add_right {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y₁ Y₂ : Work.NN.Core.Cn n) :
    cdL A z l X (Y₁ + Y₂) = cdL A z l X Y₁ + cdL A z l X Y₂ := by
  simp [cdL, cdD, cdLam, map_add]

/-- `cdL` is real-homogeneous in its first slot. -/
lemma zcdL_smul_left {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y : Work.NN.Core.Cn n) (c : ℝ) :
    cdL A z l (c • X) Y = c * cdL A z l X Y := by
  simp [cdL, cdD, cdLam, Complex.real_smul]

/-- `cdL` is real-homogeneous in its second slot. -/
lemma zcdL_smul_right {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y : Work.NN.Core.Cn n) (c : ℝ) :
    cdL A z l X (c • Y) = c * cdL A z l X Y := by
  simp [cdL, cdD, cdLam, Complex.real_smul]

/-- **The differentiated almost-complexity relation, solved for `cdL X (i•w)`.**

The relation `cdRel A z l` reads `i·m(X,w) + m(X,i•w) + m(X,A z w) + λ_l(A z (m(X,w))) = 0`;
solving it for the second term gives, for all `X, w`,

`cdL A z l X (i•w) = −(i·cdL A z l X w) − cdL A z l X (A z w) − λ_l(A z ((DA_z X)(w)))`.

This is the substitution applied to the four terms of `cdE` whose second slot is `i•(…)`. -/
lemma zcdRel_i_smul {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (h : cdRel A z l) (X w : Work.NN.Core.Cn n) :
    cdL A z l X (Complex.I • w)
      = -(Complex.I * cdL A z l X w) - cdL A z l X (A z w)
          - cdLam l (A z (cdD A z X w)) := by
  have hh := h X w
  linear_combination hh

/-- **The algebraic decomposition `cdE = 2·cdDefA + cdQuad`.**

Under the pointwise differentiated almost-complexity relation `cdRel A z l`, i.e.
`i·m(X,w) + m(X,i•w) + m(X,A z w) + λ_l(A z (m(X,w))) = 0` for all `X,w`
(where `m(X,w) = cdL A z l X w = λ_l((DA_z X)(w))`), the eight-term expansion `cdE` of
`(8/i)·proj02 J (dOne ∂̄_J z_l) z e_j e_k` splits as

`cdE A z l j k = 2·cdDefA A z l j k + cdQuad A z l j k`,

where `cdQuad` is the sum of the ten terms that contain at least one factor of `A`.

Proof: expand `cdE` using the real bilinearity of `cdL` in both slots and
`(Jstd+A) z V = i•V + A z V`; substitute the relation in the four places where the second slot
is `i•(something)`; the twelve resulting linear terms collect into `2·cdDefA` and the rest is,
term by term, `cdQuad`.  Numerically verified on genuinely almost-complex data (so that `cdRel`
holds) to `5·10^{-10}`.  All names are defined in
`Submission.Work.NN.Newton.coordDefectData`. -/
theorem zcddEexpr {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l j k : Fin n) (h : Work.NN.Newton.cdRel A z l) :
    Work.NN.Newton.cdE A z l j k
      = 2 * Work.NN.Newton.cdDefA A z l j k + Work.NN.Newton.cdQuad A z l j k := by
  -- 1. unfold the three defined expressions;
  -- 2. write both `cdIevec`'s as `i • cdEvec`;
  -- 3. expand `(Jstd + A) z V = i • V + A z V`;
  -- 4. expand `cdL` in both slots (real bilinearity);
  simp only [cdE, cdDefA, cdQuad, zcdIevec_eq_smul, Pi.add_apply, add_apply,
    Work.NN.Core.JstdCn_apply, zcdL_add_left, zcdL_add_right]
  -- 5. the four substitutions; each rewrites exactly one term, the one whose second slot is
  --    `i•something` with the appropriate first slot, and leaves `cdL (A z u) (i•v)` and
  --    `cdL (A z v) (i•u)` — the terms of `cdQuad` — alone.
  rw [zcdRel_i_smul A z l h (cdEvec k) (cdEvec j),
    zcdRel_i_smul A z l h (cdEvec j) (cdEvec k),
    zcdRel_i_smul A z l h (Complex.I • cdEvec j) (cdEvec k),
    zcdRel_i_smul A z l h (Complex.I • cdEvec k) (cdEvec j)]
  -- 6. collect, using `i² = −1` for the two sign flips.
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddEstL_pairing_le` -/

namespace Work.NN.Newton

open ContinuousLinearMap

/-- Norm bound for the pairing `λ_l((DA_z (A z V))(W))`: it is bounded by the operator norm of
`DA_z`, the operator norm of the perturbation `A z` and the norms of `V` and `W`. -/
theorem zcddEstL_pairing_le {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n)
    {V W : Work.NN.Core.Cn n} (z : Work.NN.Core.Cn n) :
    ‖Work.NN.Newton.cdL A z l (A z V) W‖
      ≤ ‖fderiv ℝ A z‖ * (‖A z‖ * ‖V‖) * ‖W‖ := by
  calc ‖Work.NN.Newton.cdL A z l (A z V) W‖
      = ‖(((fderiv ℝ A z) (A z V)) W) l‖ := rfl
    _ ≤ ‖((fderiv ℝ A z) (A z V)) W‖ := norm_le_pi_norm _ l
    _ ≤ ‖(fderiv ℝ A z) (A z V)‖ * ‖W‖ := le_opNorm _ _
    _ ≤ (‖fderiv ℝ A z‖ * ‖A z V‖) * ‖W‖ :=
        mul_le_mul_of_nonneg_right (le_opNorm (fderiv ℝ A z) (A z V)) (norm_nonneg W)
    _ ≤ (‖fderiv ℝ A z‖ * (‖A z‖ * ‖V‖)) * ‖W‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_opNorm (A z) V) (norm_nonneg (fderiv ℝ A z)))
          (norm_nonneg W)

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddEstD_pairing_sub_le` -/

namespace Work.NN.Newton

/-- The `l`-coordinate of `(DA_z X)(Y)` unfolds to the `l`-th coordinate of the value of the
second derivative of `A` at `z` evaluated on `X` and then on `Y`. -/
lemma zcdL_apply_eq {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (z : Work.NN.Core.Cn n) (l : Fin n) (X Y : Work.NN.Core.Cn n) :
    cdL A z l X Y = (((fderiv ℝ A z) X) Y) l := rfl

/-- Perturbing both the base point (`x → y`) and the direction (`A x V → A y V`) of the pairing
`cdL A z l X Y` costs `‖Dx − Dy‖·‖A x V‖·‖W‖ + ‖Dy‖·‖(A x − A y) V‖·‖W‖`: the first term
accounts for the change of the derivative, the second for the change of the direction. -/
theorem zcddEstD_pairing_sub_le {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l : Fin n)
    {V W : Work.NN.Core.Cn n} (x y : Work.NN.Core.Cn n) :
    ‖Work.NN.Newton.cdL A x l (A x V) W - Work.NN.Newton.cdL A y l (A y V) W‖
      ≤ ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ * ‖W‖
        + ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ * ‖W‖ := by
  have hsub : Work.NN.Newton.cdL A x l (A x V) W - Work.NN.Newton.cdL A y l (A y V) W
      = (((fderiv ℝ A x) (A x V)) W - ((fderiv ℝ A y) (A y V)) W) l := by
    simp [Work.NN.Newton.cdL, Work.NN.Newton.cdD, Work.NN.Newton.cdLam]
  rw [hsub]
  calc ‖(((fderiv ℝ A x) (A x V)) W - ((fderiv ℝ A y) (A y V)) W) l‖
      ≤ ‖((fderiv ℝ A x) (A x V)) W - ((fderiv ℝ A y) (A y V)) W‖ := norm_le_pi_norm _ l
    _ = ‖((fderiv ℝ A x - fderiv ℝ A y) (A x V)) W + ((fderiv ℝ A y) ((A x - A y) V)) W‖ := by
        congr 1
        simp [map_sub]
    _ ≤ ‖((fderiv ℝ A x - fderiv ℝ A y) (A x V)) W‖
          + ‖((fderiv ℝ A y) ((A x - A y) V)) W‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ * ‖W‖
          + ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ * ‖W‖ := by
        apply add_le_add
        · calc ‖((fderiv ℝ A x - fderiv ℝ A y) (A x V)) W‖
              ≤ ‖(fderiv ℝ A x - fderiv ℝ A y) (A x V)‖ * ‖W‖ :=
                ContinuousLinearMap.le_opNorm _ W
            _ ≤ (‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖) * ‖W‖ := by
                gcongr
                exact ContinuousLinearMap.le_opNorm _ (A x V)
            _ = ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ * ‖W‖ := by ring
        · calc ‖((fderiv ℝ A y) ((A x - A y) V)) W‖
              ≤ ‖(fderiv ℝ A y) ((A x - A y) V)‖ * ‖W‖ :=
                ContinuousLinearMap.le_opNorm _ W
            _ ≤ (‖fderiv ℝ A y‖ * ‖(A x - A y) V‖) * ‖W‖ := by
                gcongr
                exact ContinuousLinearMap.le_opNorm _ ((A x - A y) V)
            _ = ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ * ‖W‖ := by ring

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddShapeA` -/

namespace Work.NN.Newton

noncomputable section

open scoped NNReal ENNReal
open Set

/-- **`C^{0,α}` bound for the quadratic perturbation term.**  With
`fs z = λ_l((DA_z (A z V))(W))`:

* `‖fs z‖ ≤ a²`, because `fs` is a product of `DA` (bounded by `a`), `A` (bounded by `a`) and the
  two unit vectors `V`, `W`;
* `‖fs x - fs y‖ ≤ 2a²‖x - y‖^α`, by telescoping
  `DA_x(A x V) - DA_y(A y V) = (DA_x - DA_y)(A x V) + DA_y((A x - A y)V)` and using the two
  `α`-Hölder hypotheses on `A` and on `DA`;

so the `C^{0,α}`-norm on the polydisc is at most `ofReal (a²) + ofReal (2a²) = ofReal (3a²)` (the
`holderNorm 0` of a function is the sum of its sup bound and its Hölder seminorm), which is
`≤ ofReal (4a²)`. -/
theorem zcddShapeA {n : ℕ} {r a α : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A z‖ ≤ a)
    (hPα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α)
    (hK : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a)
    (hKα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ a * ‖x - y‖ ^ α)
    (l : Fin n) {V W : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.cdL A z l (A z V) W)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  set P : Set (Work.NN.Core.Cn n) :=
    Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) with hPdef
  set fs : Work.NN.Core.Cn n → ℂ := fun z => cdL A z l (A z V) W with hfs
  -- Supremum bound: `‖fs z‖ ≤ a²`.
  have hsup : ∀ z ∈ P, ‖fs z‖ ≤ a ^ 2 := by
    intro z hz
    calc ‖fs z‖ = ‖cdL A z l (A z V) W‖ := rfl
      _ ≤ ‖fderiv ℝ A z‖ * (‖A z‖ * ‖V‖) * ‖W‖ := zcddEstL_pairing_le A l z
      _ ≤ a * (a * 1) * 1 :=
          mul_le_mul
            (mul_le_mul (hK z hz)
              (mul_le_mul (hP z hz) hV (norm_nonneg _) ha)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ha)
            hW (norm_nonneg _) (mul_nonneg ha (mul_nonneg ha zero_le_one))
      _ = a ^ 2 := by ring
  -- Hölder bound: `‖fs x - fs y‖ ≤ 2a²‖x - y‖^α`.
  have hhold : ∀ x ∈ P, ∀ y ∈ P, ‖fs x - fs y‖ ≤ 2 * a ^ 2 * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hAxV : ‖A x V‖ ≤ a * 1 := by
      calc ‖A x V‖ ≤ ‖A x‖ * ‖V‖ := ContinuousLinearMap.le_opNorm (A x) V
        _ ≤ a * 1 := mul_le_mul (hP x hx) hV (norm_nonneg _) ha
    have hAxAyV : ‖(A x - A y) V‖ ≤ (a * ‖x - y‖ ^ α) * 1 := by
      calc ‖(A x - A y) V‖ ≤ ‖A x - A y‖ * ‖V‖ := ContinuousLinearMap.le_opNorm (A x - A y) V
        _ ≤ (a * ‖x - y‖ ^ α) * 1 :=
            mul_le_mul (hPα x hx y hy) hV (norm_nonneg _) (mul_nonneg ha hr)
    have h1 : ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ * ‖W‖
        ≤ (a * ‖x - y‖ ^ α) * (a * 1) * 1 := by
      have hD : ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ ≤ (a * ‖x - y‖ ^ α) * (a * 1) :=
        mul_le_mul (hKα x hx y hy) hAxV (norm_nonneg _) (mul_nonneg ha hr)
      exact mul_le_mul hD hW (norm_nonneg _)
        (mul_nonneg (mul_nonneg ha hr) (mul_nonneg ha zero_le_one))
    have h2 : ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ * ‖W‖
        ≤ a * ((a * ‖x - y‖ ^ α) * 1) * 1 := by
      have hD : ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ ≤ a * ((a * ‖x - y‖ ^ α) * 1) :=
        mul_le_mul (hK y hy) hAxAyV (norm_nonneg _) ha
      exact mul_le_mul hD hW (norm_nonneg _)
        (mul_nonneg ha (mul_nonneg (mul_nonneg ha hr) zero_le_one))
    calc ‖fs x - fs y‖ = ‖cdL A x l (A x V) W - cdL A y l (A y V) W‖ := rfl
      _ ≤ ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A x V‖ * ‖W‖
            + ‖fderiv ℝ A y‖ * ‖(A x - A y) V‖ * ‖W‖ := zcddEstD_pairing_sub_le A l x y
      _ ≤ (a * ‖x - y‖ ^ α) * (a * 1) * 1 + a * ((a * ‖x - y‖ ^ α) * 1) * 1 :=
          add_le_add h1 h2
      _ = 2 * a ^ 2 * ‖x - y‖ ^ α := by ring
  calc Work.CR.Flat.holderNorm 0 α fs P
      ≤ ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (2 * a ^ 2) :=
        Work.NN.Final.holderNorm_zero_le_ofReal_add_of_bounds (α := α) (Ω := P) (f := fs)
          (A := a ^ 2) (B := 2 * a ^ 2) (by positivity) (by positivity) hsup hhold
    _ = ENNReal.ofReal (a ^ 2 + 2 * a ^ 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (4 * a ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a, ha1])

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddShapeB` -/

/-!
# The `C^{0,α}`-estimate `zcddShapeB`

Magnitude estimate for the coefficient `z ↦ cdL A z l (A z V) (A z W)`
(= `λ_l((DA_z (A z V))(A z W))`) on the polydisc `P_r ⊂ ℂⁿ`, where `A` is a
matrix-valued perturbation whose values and derivative are bounded by `a ≤ 1`
and α-Hölder with constant `a`.

Both the pointwise bound (`≤ a³`) and the α-Hölder bound (`≤ 3·a³`) are obtained
by elementary telescoping; since `a ≤ 1` they are `≤ a²` and `≤ 3·a²`
respectively, giving `C^{0,α}`-norm at most `4·a²`.
-/

namespace Work.NN.Newton

noncomputable section

open scoped ENNReal

/-- Norm bound: if `‖A z‖ ≤ a` on `P_r` and `‖V‖ ≤ 1` then `‖A z V‖ ≤ a`. -/
private lemma cddShapeB_apply_le {n : ℕ} {r a : ℝ} (ha : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r), ‖A z‖ ≤ a)
    {z : Work.NN.Core.Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {V : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) : ‖A z V‖ ≤ a := by
  calc ‖A z V‖ ≤ ‖A z‖ * ‖V‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ a * 1 := mul_le_mul (hP z hz) hV (norm_nonneg _) ha
    _ = a := by ring

/-- α-Hölder bound: `‖A x V - A y V‖ ≤ a·‖x-y‖^α`. -/
private lemma cddShapeB_sub_apply_le {n : ℕ} {r a α : ℝ} (ha : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hPα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α)
    {x : Work.NN.Core.Cn n}
    (hx : x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {y : Work.NN.Core.Cn n}
    (hy : y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {V : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) :
    ‖A x V - A y V‖ ≤ a * ‖x - y‖ ^ α := by
  have hr : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  calc ‖A x V - A y V‖ = ‖(A x - A y) V‖ := by rw [sub_apply]
    _ ≤ ‖A x - A y‖ * ‖V‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (a * ‖x - y‖ ^ α) * 1 :=
        mul_le_mul (hPα x hx y hy) hV (norm_nonneg _) (mul_nonneg ha hr)
    _ = a * ‖x - y‖ ^ α := by ring

/-- Pointwise bound for the "inner" derivative factor `z ↦ (DA_z (A z V))`. -/
private lemma cddShapeB_fderiv_apply_le {n : ℕ} {r a : ℝ} (ha : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r), ‖A z‖ ≤ a)
    (hK : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a)
    {z : Work.NN.Core.Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {V : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) :
    ‖fderiv ℝ A z (A z V)‖ ≤ a ^ 2 := by
  calc ‖fderiv ℝ A z (A z V)‖ ≤ ‖fderiv ℝ A z‖ * ‖A z V‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ a * a := mul_le_mul (hK z hz) (cddShapeB_apply_le ha hP hz hV) (norm_nonneg _) ha
    _ = a ^ 2 := by ring

/-- α-Hölder bound for `z ↦ (DA_z (A z V))`. -/
private lemma cddShapeB_fderiv_apply_sub_le {n : ℕ} {r a α : ℝ} (ha : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r), ‖A z‖ ≤ a)
    (hPα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α)
    (hK : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a)
    (hKα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ a * ‖x - y‖ ^ α)
    {x : Work.NN.Core.Cn n}
    (hx : x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {y : Work.NN.Core.Cn n}
    (hy : y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    {V : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) :
    ‖fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)‖ ≤ 2 * a ^ 2 * ‖x - y‖ ^ α := by
  have hr : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hsubV := cddShapeB_sub_apply_le (r := r) ha hPα hx hy hV
  have hAVy : ‖A y V‖ ≤ a := cddShapeB_apply_le ha hP hy hV
  have hid : fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)
      = fderiv ℝ A x (A x V - A y V) + (fderiv ℝ A x - fderiv ℝ A y) (A y V) := by
    rw [map_sub, sub_apply]; abel
  rw [hid]
  calc ‖fderiv ℝ A x (A x V - A y V) + (fderiv ℝ A x - fderiv ℝ A y) (A y V)‖
      ≤ ‖fderiv ℝ A x (A x V - A y V)‖ + ‖(fderiv ℝ A x - fderiv ℝ A y) (A y V)‖ :=
        norm_add_le _ _
    _ ≤ ‖fderiv ℝ A x‖ * ‖A x V - A y V‖ + ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖A y V‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ a * (a * ‖x - y‖ ^ α) + (a * ‖x - y‖ ^ α) * a := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul (hK x hx) hsubV (by positivity) ha
        · exact mul_le_mul (hKα x hx y hy) hAVy (norm_nonneg _) (mul_nonneg ha hr)
    _ = 2 * a ^ 2 * ‖x - y‖ ^ α := by ring

theorem zcddShapeB {n : ℕ} {r a α : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A z‖ ≤ a)
    (hPα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α)
    (hK : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a)
    (hKα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ a * ‖x - y‖ ^ α)
    (l : Fin n) {V W : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.cdL A z l (A z V) (A z W))
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  have ha3 : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
  have h3a2 : (0 : ℝ) ≤ 3 * a ^ 2 := by positivity
  have hcube : a ^ 3 ≤ a ^ 2 := by
    calc a ^ 3 = a ^ 2 * a := by ring
      _ ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
      _ = a ^ 2 := by ring
  refine (Work.NN.Final.holderNorm_zero_le_ofReal_add_of_bounds
      (α := α) (Ω := Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      (f := fun z => Work.NN.Newton.cdL A z l (A z V) (A z W))
      (A := a ^ 3) (B := 3 * a ^ 2) ha3 h3a2 ?_ ?_).trans ?_
  · -- pointwise bound `‖F z‖ ≤ a³`
    intro z hz
    have hDAV := cddShapeB_fderiv_apply_le (r := r) ha hP hK hz hV
    have hAW : ‖A z W‖ ≤ a := cddShapeB_apply_le ha hP hz hW
    have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    calc ‖Work.NN.Newton.cdL A z l (A z V) (A z W)‖
        = ‖((fderiv ℝ A z (A z V)) (A z W)) l‖ := by
          simp [Work.NN.Newton.cdL, Work.NN.Newton.cdD, Work.NN.Newton.cdLam]
      _ ≤ ‖(fderiv ℝ A z (A z V)) (A z W)‖ := norm_le_pi_norm _ l
      _ ≤ ‖fderiv ℝ A z (A z V)‖ * ‖A z W‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ a ^ 2 * a := mul_le_mul hDAV hAW (norm_nonneg _) ha2
      _ = a ^ 3 := by ring
  · -- Hölder bound `‖F x - F y‖ ≤ 3a²·‖x-y‖^α`
    intro x hx y hy
    have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    have hr : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hsubW := cddShapeB_sub_apply_le (r := r) ha hPα hx hy hW
    have hAWy : ‖A y W‖ ≤ a := cddShapeB_apply_le ha hP hy hW
    have hDAVx : ‖fderiv ℝ A x (A x V)‖ ≤ a ^ 2 :=
      cddShapeB_fderiv_apply_le (r := r) ha hP hK hx hV
    have hsubP := cddShapeB_fderiv_apply_sub_le (r := r) ha hP hPα hK hKα hx hy hV
    have hone : Work.NN.Newton.cdL A x l (A x V) (A x W)
        = ((fderiv ℝ A x (A x V)) (A x W)) l := by
      simp [Work.NN.Newton.cdL, Work.NN.Newton.cdD, Work.NN.Newton.cdLam]
    have htwo : Work.NN.Newton.cdL A y l (A y V) (A y W)
        = ((fderiv ℝ A y (A y V)) (A y W)) l := by
      simp [Work.NN.Newton.cdL, Work.NN.Newton.cdD, Work.NN.Newton.cdLam]
    rw [hone, htwo, ← Pi.sub_apply]
    refine (norm_le_pi_norm _ l).trans ?_
    have hdec : (fderiv ℝ A x (A x V)) (A x W) - (fderiv ℝ A y (A y V)) (A y W)
        = (fderiv ℝ A x (A x V)) (A x W - A y W)
          + (fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)) (A y W) := by
      rw [map_sub, sub_apply]; abel
    rw [hdec]
    calc ‖(fderiv ℝ A x (A x V)) (A x W - A y W)
          + (fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)) (A y W)‖
        ≤ ‖(fderiv ℝ A x (A x V)) (A x W - A y W)‖
          + ‖(fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)) (A y W)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ A x (A x V)‖ * ‖A x W - A y W‖
          + ‖fderiv ℝ A x (A x V) - fderiv ℝ A y (A y V)‖ * ‖A y W‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ a ^ 2 * (a * ‖x - y‖ ^ α) + (2 * a ^ 2 * ‖x - y‖ ^ α) * a := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hDAVx hsubW (norm_nonneg _) ha2
            · exact mul_le_mul hsubP hAWy (norm_nonneg _) (by positivity)
      _ = 3 * a ^ 3 * ‖x - y‖ ^ α := by ring
      _ ≤ 3 * a ^ 2 * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcube (by norm_num)) hr
  · -- arithmetic: `a³ + 3a² ≤ 4a²`
    rw [← ENNReal.ofReal_add ha3 h3a2]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddShapeC` -/

set_option linter.unusedVariables false

namespace Work.NN.Newton

open scoped NNReal ENNReal
open Set

theorem zcddShapeC {n : ℕ} {r a α : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hP : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A z‖ ≤ a)
    (hPα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α)
    (hK : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a)
    (hKα : ∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ a * ‖x - y‖ ^ α)
    (l : Fin n) {V W : Work.NN.Core.Cn n} (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.cdLam l (A z (Work.NN.Newton.cdD A z V W)))
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  -- `cdLam l = ContinuousLinearMap.proj l` is a contraction, so it can be pushed inside.
  have hproj : ‖cdLam l‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    rw [cdLam_apply, one_mul]
    exact norm_le_pi_norm w l
  set P : Set (Work.NN.Core.Cn n) :=
    Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) with hPdef
  -- The `ℝ`-linear map `z ↦ (cdLam l).comp (A z) : ℂⁿ →L[ℝ] ℂ` is bounded and Hölder.
  have hbdry : ∀ z ∈ P, ‖(cdLam l).comp (A z)‖ ≤ a := by
    intro z hz
    calc ‖(cdLam l).comp (A z)‖ ≤ ‖cdLam l‖ * ‖A z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * a := mul_le_mul hproj (hP z hz) (norm_nonneg _) zero_le_one
      _ = a := one_mul a
  have hheld : ∀ x ∈ P, ∀ y ∈ P, ‖(cdLam l).comp (A x) - (cdLam l).comp (A y)‖
      ≤ a * ‖x - y‖ ^ α := by
    intro x hx y hy
    rw [show (cdLam l).comp (A x) - (cdLam l).comp (A y) = (cdLam l).comp (A x - A y) from by
      ext v; simp [ContinuousLinearMap.comp_apply]]
    calc ‖(cdLam l).comp (A x - A y)‖ ≤ ‖cdLam l‖ * ‖A x - A y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (a * ‖x - y‖ ^ α) :=
          mul_le_mul hproj (hPα x hx y hy) (norm_nonneg _) zero_le_one
      _ = a * ‖x - y‖ ^ α := one_mul _
  -- The vector field `z ↦ (fderiv ℝ A z V) W` is bounded and Hölder.
  have hu0 : ∀ z ∈ P, ‖(fderiv ℝ A z V) W‖ ≤ a := by
    intro z hz
    have h1 : ‖fderiv ℝ A z V‖ ≤ a := by
      calc ‖fderiv ℝ A z V‖ ≤ ‖fderiv ℝ A z‖ * ‖V‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ a * 1 := mul_le_mul (hK z hz) hV (norm_nonneg _) ha
        _ = a := mul_one a
    calc ‖(fderiv ℝ A z V) W‖ ≤ ‖fderiv ℝ A z V‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ a * 1 := mul_le_mul h1 hW (norm_nonneg _) ha
      _ = a := mul_one a
  have huα : ∀ x ∈ P, ∀ y ∈ P, ‖(fderiv ℝ A x V) W - (fderiv ℝ A y V) W‖
      ≤ a * ‖x - y‖ ^ α := by
    intro x hx y hy
    have h1 : ‖(fderiv ℝ A x - fderiv ℝ A y) V‖ ≤ a * ‖x - y‖ ^ α := by
      calc ‖(fderiv ℝ A x - fderiv ℝ A y) V‖
            ≤ ‖fderiv ℝ A x - fderiv ℝ A y‖ * ‖V‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (a * ‖x - y‖ ^ α) * 1 :=
            mul_le_mul (hKα x hx y hy) hV (norm_nonneg _)
              (mul_nonneg ha (Real.rpow_nonneg (norm_nonneg _) α))
        _ = a * ‖x - y‖ ^ α := mul_one _
    rw [show (fderiv ℝ A x V) W - (fderiv ℝ A y V) W
        = ((fderiv ℝ A x - fderiv ℝ A y) V) W from by simp [sub_apply]]
    calc ‖((fderiv ℝ A x - fderiv ℝ A y) V) W‖
          ≤ ‖(fderiv ℝ A x - fderiv ℝ A y) V‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (a * ‖x - y‖ ^ α) * 1 :=
          mul_le_mul h1 hW (norm_nonneg _)
            (mul_nonneg ha (Real.rpow_nonneg (norm_nonneg _) α))
      _ = a * ‖x - y‖ ^ α := mul_one _
  -- Leibniz pairing estimate: bound `a`, Hölder constant `a` on both factors.
  have hmain := Work.NN.Final.holderNorm_zero_clm_apply_le (X := Work.NN.Core.Cn n)
    (E := Work.NN.Core.Cn n) (α := α) (ε := a) (M := a) ha ha
    (fun z => (cdLam l).comp (A z)) (fun z => (fderiv ℝ A z V) W) P hbdry hheld hu0 huα
  refine hmain.trans ?_
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg a]

end Work.NN.Newton

/-! ## inlined from `Submission.Work.NN.Newton.cddQuadBound` -/

namespace Work.NN.Newton

open scoped NNReal ENNReal
open Set

noncomputable section

/-! ## Elementary zero-order facts about the `C^{0,α}` norm

At order `0` the iterated derivative is the function itself, so `iterDerivNorm 0` and
`holderSeminorm 0 α` are subadditive on sums of *arbitrary* complex valued functions, with no
differentiability hypothesis.  This lets us add up the ten summands of `cdQuad` without
proving that each one is `C^0`. -/

private lemma iterDerivNorm_zero_add {n : ℕ} (f g : Work.NN.Core.Cn n → ℂ)
    (Ω : Set (Work.NN.Core.Cn n)) :
    Work.CR.Flat.iterDerivNorm 0 (f + g) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.iterDerivNorm 0 g Ω := by
  simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero, Pi.add_apply]
  refine iSup₂_le fun z hz => ?_
  calc ENNReal.ofReal ‖f z + g z‖
      ≤ ENNReal.ofReal (‖f z‖ + ‖g z‖) := ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖f z‖ + ENNReal.ofReal ‖g z‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ z ∈ Ω, ENNReal.ofReal ‖f z‖) + ⨆ z ∈ Ω, ENNReal.ofReal ‖g z‖ :=
        add_le_add (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)

private lemma iterDerivNorm_zero_sub {n : ℕ} (f g : Work.NN.Core.Cn n → ℂ)
    (Ω : Set (Work.NN.Core.Cn n)) :
    Work.CR.Flat.iterDerivNorm 0 (f - g) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.iterDerivNorm 0 g Ω := by
  simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero, Pi.sub_apply]
  refine iSup₂_le fun z hz => ?_
  calc ENNReal.ofReal ‖f z - g z‖
      ≤ ENNReal.ofReal (‖f z‖ + ‖g z‖) := ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
    _ = ENNReal.ofReal ‖f z‖ + ENNReal.ofReal ‖g z‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ z ∈ Ω, ENNReal.ofReal ‖f z‖) + ⨆ z ∈ Ω, ENNReal.ofReal ‖g z‖ :=
        add_le_add (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)

private lemma holderSeminorm_zero_add {n : ℕ} (α : ℝ) (f g : Work.NN.Core.Cn n → ℂ)
    (Ω : Set (Work.NN.Core.Cn n)) :
    Work.CR.Flat.holderSeminorm 0 α (f + g) Ω
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hkey : ‖(f + g) x - (f + g) y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
    rw [show (f + g) x - (f + g) y = (f x - f y) + (g x - g y) by
      simp only [Pi.add_apply]; abel]
    exact norm_add_le _ _
  calc ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ 0 (f + g) Ω x - iteratedFDerivWithin ℝ 0 (f + g) Ω y‖
          / ‖x - y‖ ^ α)
      = ENNReal.ofReal (‖(f + g) x - (f + g) y‖ / ‖x - y‖ ^ α) := by
        rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
    _ ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hkey hd)
    _ = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
        rw [add_div, ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd)
          (div_nonneg (norm_nonneg _) hd)]
    _ ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
        rw [← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub f Ω x y,
          ← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub g Ω x y]
        exact add_le_add (Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy)
          (Work.CR.Flat.le_holderSeminorm 0 α g Ω hx hy hxy)

private lemma holderSeminorm_zero_sub {n : ℕ} (α : ℝ) (f g : Work.NN.Core.Cn n → ℂ)
    (Ω : Set (Work.NN.Core.Cn n)) :
    Work.CR.Flat.holderSeminorm 0 α (f - g) Ω
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hkey : ‖(f - g) x - (f - g) y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
    rw [show (f - g) x - (f - g) y = (f x - f y) - (g x - g y) by
      simp only [Pi.sub_apply]; abel]
    exact norm_sub_le _ _
  calc ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ 0 (f - g) Ω x - iteratedFDerivWithin ℝ 0 (f - g) Ω y‖
          / ‖x - y‖ ^ α)
      = ENNReal.ofReal (‖(f - g) x - (f - g) y‖ / ‖x - y‖ ^ α) := by
        rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
    _ ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hkey hd)
    _ = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
          + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
        rw [add_div, ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd)
          (div_nonneg (norm_nonneg _) hd)]
    _ ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
        rw [← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub f Ω x y,
          ← Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub g Ω x y]
        exact add_le_add (Work.CR.Flat.le_holderSeminorm 0 α f Ω hx hy hxy)
          (Work.CR.Flat.le_holderSeminorm 0 α g Ω hx hy hxy)

private lemma holderNorm_zero_add_le {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (f g : Work.NN.Core.Cn n → ℂ) :
    Work.CR.Flat.holderNorm 0 α (f + g) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  have h1 := iterDerivNorm_zero_add f g Ω
  have h2 := holderSeminorm_zero_add α f g Ω
  simp only [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact (add_le_add h1 h2).trans (le_of_eq (add_add_add_comm _ _ _ _))

private lemma holderNorm_zero_sub_le {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (f g : Work.NN.Core.Cn n → ℂ) :
    Work.CR.Flat.holderNorm 0 α (f - g) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  have h1 := iterDerivNorm_zero_sub f g Ω
  have h2 := holderSeminorm_zero_sub α f g Ω
  simp only [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact (add_le_add h1 h2).trans (le_of_eq (add_add_add_comm _ _ _ _))

/-- Scaling a `C^{0,α}` bound by a complex constant of norm at most `1/8`. -/
private lemma holderNorm_zero_scale {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (hΩ : UniqueDiffOn ℝ Ω) (c : ℂ) (hc : ‖c‖ ≤ 1 / 8) {f : Work.NN.Core.Cn n → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal B) :
    Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω ≤ ENNReal.ofReal B := by
  calc Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 0 α f Ω :=
        Work.NN.Core.holderNorm_const_mul_le hΩ c f
    _ ≤ ENNReal.ofReal (1 / 8) * ENNReal.ofReal B :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc) hf
    _ = ENNReal.ofReal ((1 / 8) * B) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by nlinarith)

set_option maxHeartbeats 1000000 in
/-- The ten summands of `cdQuad`, peeled apart with the zero-order triangle inequalities. -/
private lemma holderNorm_zero_sum10 {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : Work.NN.Core.Cn n → ℂ) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => f1 z + f2 z - f3 z - f4 z + f5 z - f6 z - f7 z - f8 z + f9 z + f10 z) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f1 Ω + Work.CR.Flat.holderNorm 0 α f2 Ω
        + Work.CR.Flat.holderNorm 0 α f3 Ω + Work.CR.Flat.holderNorm 0 α f4 Ω
        + Work.CR.Flat.holderNorm 0 α f5 Ω + Work.CR.Flat.holderNorm 0 α f6 Ω
        + Work.CR.Flat.holderNorm 0 α f7 Ω + Work.CR.Flat.holderNorm 0 α f8 Ω
        + Work.CR.Flat.holderNorm 0 α f9 Ω + Work.CR.Flat.holderNorm 0 α f10 Ω := by
  have hfun : (fun z => f1 z + f2 z - f3 z - f4 z + f5 z - f6 z - f7 z - f8 z + f9 z + f10 z)
      = (((((((((f1 + f2) - f3) - f4) + f5) - f6) - f7) - f8) + f9) + f10) := by
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
  rw [hfun]
  let E2 : Work.NN.Core.Cn n → ℂ := f1 + f2
  let E3 : Work.NN.Core.Cn n → ℂ := E2 - f3
  let E4 : Work.NN.Core.Cn n → ℂ := E3 - f4
  let E5 : Work.NN.Core.Cn n → ℂ := E4 + f5
  let E6 : Work.NN.Core.Cn n → ℂ := E5 - f6
  let E7 : Work.NN.Core.Cn n → ℂ := E6 - f7
  let E8 : Work.NN.Core.Cn n → ℂ := E7 - f8
  let E9 : Work.NN.Core.Cn n → ℂ := E8 + f9
  let E10 : Work.NN.Core.Cn n → ℂ := E9 + f10
  let S2 : ℝ≥0∞ := Work.CR.Flat.holderNorm 0 α f1 Ω + Work.CR.Flat.holderNorm 0 α f2 Ω
  let S3 : ℝ≥0∞ := S2 + Work.CR.Flat.holderNorm 0 α f3 Ω
  let S4 : ℝ≥0∞ := S3 + Work.CR.Flat.holderNorm 0 α f4 Ω
  let S5 : ℝ≥0∞ := S4 + Work.CR.Flat.holderNorm 0 α f5 Ω
  let S6 : ℝ≥0∞ := S5 + Work.CR.Flat.holderNorm 0 α f6 Ω
  let S7 : ℝ≥0∞ := S6 + Work.CR.Flat.holderNorm 0 α f7 Ω
  let S8 : ℝ≥0∞ := S7 + Work.CR.Flat.holderNorm 0 α f8 Ω
  let S9 : ℝ≥0∞ := S8 + Work.CR.Flat.holderNorm 0 α f9 Ω
  let S10 : ℝ≥0∞ := S9 + Work.CR.Flat.holderNorm 0 α f10 Ω
  have hh2 : Work.CR.Flat.holderNorm 0 α E2 Ω ≤ S2 := holderNorm_zero_add_le f1 f2
  have hh3 : Work.CR.Flat.holderNorm 0 α E3 Ω ≤ S3 :=
    (holderNorm_zero_sub_le E2 f3).trans (add_le_add hh2 le_rfl)
  have hh4 : Work.CR.Flat.holderNorm 0 α E4 Ω ≤ S4 :=
    (holderNorm_zero_sub_le E3 f4).trans (add_le_add hh3 le_rfl)
  have hh5 : Work.CR.Flat.holderNorm 0 α E5 Ω ≤ S5 :=
    (holderNorm_zero_add_le E4 f5).trans (add_le_add hh4 le_rfl)
  have hh6 : Work.CR.Flat.holderNorm 0 α E6 Ω ≤ S6 :=
    (holderNorm_zero_sub_le E5 f6).trans (add_le_add hh5 le_rfl)
  have hh7 : Work.CR.Flat.holderNorm 0 α E7 Ω ≤ S7 :=
    (holderNorm_zero_sub_le E6 f7).trans (add_le_add hh6 le_rfl)
  have hh8 : Work.CR.Flat.holderNorm 0 α E8 Ω ≤ S8 :=
    (holderNorm_zero_sub_le E7 f8).trans (add_le_add hh7 le_rfl)
  have hh9 : Work.CR.Flat.holderNorm 0 α E9 Ω ≤ S9 :=
    (holderNorm_zero_add_le E8 f9).trans (add_le_add hh8 le_rfl)
  have hh10 : Work.CR.Flat.holderNorm 0 α E10 Ω ≤ S10 :=
    (holderNorm_zero_add_le E9 f10).trans (add_le_add hh9 le_rfl)
  exact hh10

/-! ## Pointwise consequences of a `holderNorm` bound -/

private lemma norm_le_of_holderNorm_zero_le {n : ℕ} {α A : ℝ} (hA : 0 ≤ A)
    {Ω : Set (Work.NN.Core.Cn n)} {g : Work.NN.Core.Cn n → ℂ}
    (h : Work.CR.Flat.holderNorm 0 α g Ω ≤ ENNReal.ofReal A) :
    ∀ z ∈ Ω, ‖g z‖ ≤ A := by
  intro z hz
  refine (ENNReal.ofReal_le_ofReal_iff hA).mp ?_
  calc ENNReal.ofReal ‖g z‖
      = ENNReal.ofReal ‖iteratedFDerivWithin ℝ 0 g Ω z‖ := by
        rw [norm_iteratedFDerivWithin_zero]
    _ ≤ Work.CR.Flat.iterDerivNorm 0 g Ω := Work.CR.Flat.le_iterDerivNorm 0 g Ω hz
    _ ≤ Work.CR.Flat.holderNorm 0 α g Ω :=
        Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α g Ω (le_refl 0)
    _ ≤ ENNReal.ofReal A := h

private lemma norm_sub_le_of_holderNorm_zero_le {n : ℕ} {α A : ℝ} (hA : 0 ≤ A)
    {Ω : Set (Work.NN.Core.Cn n)} {g : Work.NN.Core.Cn n → ℂ}
    (h : Work.CR.Flat.holderNorm 0 α g Ω ≤ ENNReal.ofReal A) :
    ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖g z - g z'‖ ≤ A * ‖z - z'‖ ^ α := by
  intro z hz z' hz'
  by_cases hzz : z = z'
  · subst hzz
    rw [sub_self, norm_zero]
    exact mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) α)
  · have h1 : ENNReal.ofReal (‖g z - g z'‖ / ‖z - z'‖ ^ α) ≤ ENNReal.ofReal A := by
      calc ENNReal.ofReal (‖g z - g z'‖ / ‖z - z'‖ ^ α)
          = ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 g Ω z
              - iteratedFDerivWithin ℝ 0 g Ω z'‖ / ‖z - z'‖ ^ α) := by
            rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
        _ ≤ Work.CR.Flat.holderSeminorm 0 α g Ω :=
            Work.CR.Flat.le_holderSeminorm 0 α g Ω hz hz' hzz
        _ ≤ Work.CR.Flat.holderNorm 0 α g Ω :=
            Work.CR.Flat.holderSeminorm_le_holderNorm 0 α g Ω (le_refl 0)
        _ ≤ ENNReal.ofReal A := h
    have h2 := (ENNReal.ofReal_le_ofReal_iff hA).mp h1
    have hpos : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
    exact (div_le_iff₀ hpos).mp h2

/-! ## The differential of `A` in terms of the coefficient functions -/

private lemma fderiv_coeff_eq {n : ℕ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {z : Work.NN.Core.Cn n} (hz : DifferentiableAt ℝ A z) (w : Work.NN.Core.Cn n) (l : Fin n) :
    fderiv ℝ (fun z' => A z' w l) z
      = (Work.NN.Newton.cdLam l).comp
          ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).comp (fderiv ℝ A z)) := by
  have h1 : HasFDerivAt (fun z' => A z' w)
      ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).comp (fderiv ℝ A z)) z :=
    (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w).hasFDerivAt.comp z hz.hasFDerivAt
  have hfun : (fun z' => A z' w l)
      = (⇑(Work.NN.Newton.cdLam l) ∘ fun z' => A z' w) := by
    funext z'
    exact (Work.NN.Newton.cdLam_apply l (A z' w)).symm
  rw [hfun]
  exact ((Work.NN.Newton.cdLam l).hasFDerivAt.comp z h1).fderiv

private lemma fderiv_coeff_apply {n : ℕ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {z : Work.NN.Core.Cn n} (hz : DifferentiableAt ℝ A z)
    (w v : Work.NN.Core.Cn n) (l : Fin n) :
    fderiv ℝ (fun z' => A z' w l) z v = ((fderiv ℝ A z) v) w l := by
  rw [fderiv_coeff_eq hz w l]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    Work.NN.Newton.cdLam_apply]

/-! ## The pointwise bounds on `A` and on `fderiv A` implied by the coefficient hypothesis -/

private lemma cddOpNormBounds {n : ℕ} {α a r : ℝ} (ha0 : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hcoef : ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ENNReal.ofReal a) :
    (∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r), ‖A z‖ ≤ a) ∧
    (∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α) := by
  set P : Set (Work.NN.Core.Cn n) :=
    Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) with hPdef
  have h0 : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α (fun z => A z w j) P ≤ ENNReal.ofReal a := by
    intro w j hw
    exact le_trans (Work.CR.Flat.holderNorm_mono_k (Nat.zero_le 1) α _ P) (hcoef w hw j)
  have hcoord : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ z ∈ P, ‖A z w j‖ ≤ a := by
    intro w j hw z hz
    exact norm_le_of_holderNorm_zero_le ha0 (h0 w j hw) z hz
  have hholder : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ x ∈ P, ∀ y ∈ P,
      ‖A x w j - A y w j‖ ≤ a * ‖x - y‖ ^ α := by
    intro w j hw x hx y hy
    exact norm_sub_le_of_holderNorm_zero_le ha0 (h0 w j hw) x hx y hy
  have hnormal : ∀ v : Work.NN.Core.Cn n, v ≠ 0 →
      ‖(‖v‖)⁻¹ • v‖ = 1 ∧ ‖v‖ • ((‖v‖)⁻¹ • v) = v := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr hv
    · exact smul_inv_smul₀ (ne_of_gt (norm_pos_iff.mpr hv)) v
  constructor
  · intro z hz
    have hcz : ∀ (v : Work.NN.Core.Cn n) (j : Fin n), ‖(A z v) j‖ ≤ a * ‖v‖ := by
      intro v j
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · obtain ⟨hwnorm, hvdecomp⟩ := hnormal v hv
        have hcw : ‖A z ((‖v‖)⁻¹ • v) j‖ ≤ a := hcoord _ j hwnorm.le z hz
        have hmain : (A z v) j = ‖v‖ • (A z ((‖v‖)⁻¹ • v)) j := by
          conv_lhs => rw [← hvdecomp]
          simp only [map_smul, Pi.smul_apply]
        rw [hmain, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(A z ((‖v‖)⁻¹ • v)) j‖ ≤ ‖v‖ * a :=
              mul_le_mul_of_nonneg_left hcw (norm_nonneg v)
          _ = a * ‖v‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff ha0]
    intro v
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg ha0 (norm_nonneg v))]
    intro j
    exact hcz v j
  · intro x hx y hy
    have hc : 0 ≤ a * ‖x - y‖ ^ α := mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
    have hcz : ∀ (v : Work.NN.Core.Cn n) (j : Fin n),
        ‖((A x - A y) v) j‖ ≤ (a * ‖x - y‖ ^ α) * ‖v‖ := by
      intro v j
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · obtain ⟨hwnorm, hvdecomp⟩ := hnormal v hv
        have hcw : ‖A x ((‖v‖)⁻¹ • v) j - A y ((‖v‖)⁻¹ • v) j‖ ≤ a * ‖x - y‖ ^ α :=
          hholder _ j hwnorm.le x hx y hy
        have hmain : ((A x - A y) v) j
            = ‖v‖ • ((A x ((‖v‖)⁻¹ • v)) j - (A y ((‖v‖)⁻¹ • v)) j) := by
          conv_lhs => rw [← hvdecomp]
          simp only [sub_apply, map_smul, Pi.sub_apply, Pi.smul_apply, smul_sub]
        rw [hmain, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(A x ((‖v‖)⁻¹ • v)) j - (A y ((‖v‖)⁻¹ • v)) j‖
              ≤ ‖v‖ * (a * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left hcw (norm_nonneg v)
          _ = (a * ‖x - y‖ ^ α) * ‖v‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff hc]
    intro v
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg v))]
    intro j
    exact hcz v j

private lemma cddFderivBounds {n : ℕ} {α a r : ℝ} (hα0 : 0 < α) (ha0 : 0 ≤ a)
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)))
    (hcoef : ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ENNReal.ofReal a) :
    (∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A z‖ ≤ a) ∧
    (∀ x ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
        ‖fderiv ℝ A x - fderiv ℝ A y‖ ≤ a * ‖x - y‖ ^ α) := by
  set P : Set (Work.NN.Core.Cn n) :=
    Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) with hPdef
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 _
  have hdiff : ∀ z ∈ P, DifferentiableAt ℝ A z := fun z hz =>
    ((hA 1).contDiffAt (hPopen.mem_nhds hz)).differentiableAt (by norm_num)
  constructor
  · intro z hz
    -- unit-ball bound for the `(w,j)` entry of `fderiv A z`
    have hunit : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ v : Work.NN.Core.Cn n,
        ‖((fderiv ℝ A z) v) w j‖ ≤ a * ‖v‖ := by
      intro w j hw v
      have hb : ENNReal.ofReal ‖fderiv ℝ (fun z' => A z' w j) z‖ ≤ ENNReal.ofReal a := by
        have h1 : ENNReal.ofReal
            ‖fderivWithin ℝ (fun z' => A z' w j) P z‖ ≤ ENNReal.ofReal a := by
          rw [← norm_iteratedFDerivWithin_one _ (hPopen.uniqueDiffOn z hz)]
          exact (Work.CR.Flat.le_iterDerivNorm 1 _ _ hz).trans
            ((Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α _ _ le_rfl).trans (hcoef w hw j))
        rwa [fderivWithin_of_isOpen hPopen hz] at h1
      rw [← fderiv_coeff_apply (hdiff z hz) w v j]
      exact ((fderiv ℝ (fun z' => A z' w j) z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((ENNReal.ofReal_le_ofReal_iff ha0).mp hb) (norm_nonneg v))
    -- scaling in `w`
    have hscale : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ∀ v : Work.NN.Core.Cn n,
        ‖((fderiv ℝ A z) v) w j‖ ≤ a * ‖v‖ * ‖w‖ := by
      intro w j v
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
        have hwn : ‖(‖w‖)⁻¹ • w‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
            inv_mul_cancel₀ (ne_of_gt hpos)]
        have hb := hunit ((‖w‖)⁻¹ • w) j hwn v
        have hdec : ((fderiv ℝ A z) v) w j
            = ‖w‖ • (((fderiv ℝ A z) v) ((‖w‖)⁻¹ • w) j) := by
          conv_lhs => rw [← smul_inv_smul₀ (ne_of_gt hpos) w]
          simp only [map_smul, Pi.smul_apply]
        rw [hdec, norm_smul, Real.norm_of_nonneg (norm_nonneg w)]
        calc ‖w‖ * ‖((fderiv ℝ A z) v) ((‖w‖)⁻¹ • w) j‖ ≤ ‖w‖ * (a * ‖v‖) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg w)
          _ = a * ‖v‖ * ‖w‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff ha0]
    intro v
    rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg ha0 (norm_nonneg v))]
    intro w
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg ha0 (norm_nonneg v)) (norm_nonneg w))]
    intro j
    exact hscale w j v
  · intro x hx y hy
    have hC : 0 ≤ a * ‖x - y‖ ^ α := mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
    have hcol : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ v : Work.NN.Core.Cn n,
        ‖((fderiv ℝ A x - fderiv ℝ A y) v) w j‖ ≤ a * ‖x - y‖ ^ α * ‖v‖ := by
      intro w j hw v
      have hkey : ((fderiv ℝ A x - fderiv ℝ A y) v) w j
          = fderiv ℝ (fun z' => A z' w j) x v - fderiv ℝ (fun z' => A z' w j) y v := by
        rw [fderiv_coeff_apply (hdiff x hx) w v j,
          fderiv_coeff_apply (hdiff y hy) w v j]
        simp only [sub_apply, Pi.sub_apply]
      rw [hkey]
      have hb : ‖fderiv ℝ (fun z' => A z' w j) x - fderiv ℝ (fun z' => A z' w j) y‖
          ≤ a * ‖x - y‖ ^ α := by
        by_cases hxy : x = y
        · subst hxy
          rw [sub_self, norm_zero]
          exact mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
        · have hsn : Work.CR.Flat.holderSeminorm 1 α (fun z' => A z' w j) P
              ≤ ENNReal.ofReal a :=
            le_trans (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α _ P le_rfl) (hcoef w hw j)
          have h1 := Work.CR.Flat.le_holderSeminorm 1 α (fun z' => A z' w j) P hx hy hxy
          have h2 : ‖iteratedFDerivWithin ℝ 1 (fun z' => A z' w j) P x
              - iteratedFDerivWithin ℝ 1 (fun z' => A z' w j) P y‖ / ‖x - y‖ ^ α ≤ a :=
            (ENNReal.ofReal_le_ofReal_iff ha0).mp (le_trans h1 hsn)
          have hdpos : 0 < ‖x - y‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
          have h3 : ‖iteratedFDerivWithin ℝ 1 (fun z' => A z' w j) P x
              - iteratedFDerivWithin ℝ 1 (fun z' => A z' w j) P y‖ ≤ a * ‖x - y‖ ^ α :=
            (div_le_iff₀ hdpos).mp h2
          rwa [Work.NN.Core.Lev.norm_iteratedFDerivWithin_one_sub_eq hPopen _ hx hy] at h3
      calc ‖fderiv ℝ (fun z' => A z' w j) x v - fderiv ℝ (fun z' => A z' w j) y v‖
          = ‖(fderiv ℝ (fun z' => A z' w j) x - fderiv ℝ (fun z' => A z' w j) y) v‖ := by
            rw [sub_apply]
        _ ≤ ‖fderiv ℝ (fun z' => A z' w j) x - fderiv ℝ (fun z' => A z' w j) y‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ v
        _ ≤ (a * ‖x - y‖ ^ α) * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
        _ = a * ‖x - y‖ ^ α * ‖v‖ := by ring
    have hscaled : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ∀ v : Work.NN.Core.Cn n,
        ‖((fderiv ℝ A x - fderiv ℝ A y) v) w j‖ ≤ (a * ‖x - y‖ ^ α) * ‖v‖ * ‖w‖ := by
      intro w j v
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
        have hwn : ‖(‖w‖)⁻¹ • w‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
            inv_mul_cancel₀ (ne_of_gt hpos)]
        have hb := hcol ((‖w‖)⁻¹ • w) j hwn v
        have hdec : ((fderiv ℝ A x - fderiv ℝ A y) v) w j
            = ‖w‖ • (((fderiv ℝ A x - fderiv ℝ A y) v) ((‖w‖)⁻¹ • w) j) := by
          conv_lhs => rw [← smul_inv_smul₀ (ne_of_gt hpos) w]
          simp only [map_smul, Pi.smul_apply]
        rw [hdec, norm_smul, Real.norm_of_nonneg (norm_nonneg w)]
        calc ‖w‖ * ‖((fderiv ℝ A x - fderiv ℝ A y) v) ((‖w‖)⁻¹ • w) j‖
              ≤ ‖w‖ * (a * ‖x - y‖ ^ α * ‖v‖) :=
                mul_le_mul_of_nonneg_left hb (norm_nonneg w)
          _ = (a * ‖x - y‖ ^ α) * ‖v‖ * ‖w‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff hC]
    intro v
    rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg hC (norm_nonneg v))]
    intro w
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg v)) (norm_nonneg w))]
    intro j
    exact hscaled w j v

/-- **The quadratic remainder `cdQuad` is `O(a²)` in `C^{0,α}`.**

Let `A` be smooth on the polydisc `P_r` (`1 ≤ r ≤ 4`) and let `a ∈ [0,1]` bound the `C^{1,α}`-norm
of every coefficient `z ↦ A z w j` with `‖w‖ ≤ 1`.  Then every component of `cdQuad A · l j k`
(after the harmless factor `-(i/8)`) has `C^{0,α}`-norm on `P_r` at most `C·a²`, with `C` depending
only on `n, α`. -/
theorem zcddQuadBound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → r ≤ 4 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        ∀ l j k : Fin n,
          Work.CR.Flat.holderNorm 0 α (fun z => -(Complex.I / 8) * Work.NN.Newton.cdQuad A z l j k)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal (C * a ^ 2) := by
  refine ⟨41, by norm_num, ?_⟩
  intro r hr1 hr4 A hA a ha0 ha1 hcoef l j k
  obtain ⟨hPz, hPα⟩ := cddOpNormBounds (n := n) (α := α) (a := a) (r := r) ha0 hcoef
  obtain ⟨hKz, hKα⟩ := cddFderivBounds (n := n) (α := α) (a := a) (r := r) hα0 ha0 hA hcoef
  have hΩd : UniqueDiffOn ℝ
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    (Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)).uniqueDiffOn
  have hEj : ‖Work.NN.Newton.cdEvec j‖ ≤ 1 := by
    simp [Work.NN.Newton.cdEvec, Pi.norm_single]
  have hEk : ‖Work.NN.Newton.cdEvec k‖ ≤ 1 := by
    simp [Work.NN.Newton.cdEvec, Pi.norm_single]
  have hIEj : ‖Work.NN.Newton.cdIevec j‖ ≤ 1 := by
    simp [Work.NN.Newton.cdIevec, Pi.norm_single, Complex.norm_I]
  have hIEk : ‖Work.NN.Newton.cdIevec k‖ ≤ 1 := by
    simp [Work.NN.Newton.cdIevec, Pi.norm_single, Complex.norm_I]
  have hSA : ∀ (V W : Work.NN.Core.Cn n), ‖V‖ ≤ 1 → ‖W‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.cdL A z l (A z V) W)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ENNReal.ofReal (4 * a ^ 2) :=
    fun V W hV hW => Work.NN.Newton.zcddShapeA (r := r) (a := a) (α := α) (V := V) (W := W)
      ha0 ha1 hPz hPα hKz hKα l hV hW
  have hSB : ∀ (V W : Work.NN.Core.Cn n), ‖V‖ ≤ 1 → ‖W‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.cdL A z l (A z V) (A z W))
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ENNReal.ofReal (4 * a ^ 2) :=
    fun V W hV hW => Work.NN.Newton.zcddShapeB (r := r) (a := a) (α := α) (V := V) (W := W)
      ha0 ha1 hPz hPα hKz hKα l hV hW
  have hSC : ∀ (V W : Work.NN.Core.Cn n), ‖V‖ ≤ 1 → ‖W‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α
          (fun z => Work.NN.Newton.cdLam l (A z (Work.NN.Newton.cdD A z V W)))
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
        ≤ ENNReal.ofReal (4 * a ^ 2) :=
    fun V W hV hW => Work.NN.Newton.zcddShapeC (r := r) (a := a) (α := α) (V := V) (W := W)
      ha0 ha1 hPz hPα hKz hKα l hV hW
  have hc8 : ‖(-(Complex.I / 8) : ℂ)‖ = 1 / 8 := by
    rw [norm_neg, norm_div, Complex.norm_I]; norm_num
  -- ### the ten literal summands of `cdQuad`, with the factor `-(i/8)` taken out in front
  have hF1 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (Work.NN.Newton.cdEvec k))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
    refine (Work.NN.Core.holderNorm_const_mul_le hΩd Complex.I _).trans ?_
    rw [Complex.norm_I, ENNReal.ofReal_one, one_mul]
    exact hSA (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k) hEj hEk
  have hF2 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdEvec j))))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
    refine (Work.NN.Core.holderNorm_const_mul_le hΩd Complex.I _).trans ?_
    rw [Complex.norm_I, ENNReal.ofReal_one, one_mul]
    exact hSC (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdEvec j) hEk hEj
  have hF3 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k))))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
    refine (Work.NN.Core.holderNorm_const_mul_le hΩd Complex.I _).trans ?_
    rw [Complex.norm_I, ENNReal.ofReal_one, one_mul]
    exact hSC (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k) hEj hEk
  have hF4 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (Work.NN.Newton.cdEvec j))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
    refine (Work.NN.Core.holderNorm_const_mul_le hΩd Complex.I _).trans ?_
    rw [Complex.norm_I, ENNReal.ofReal_one, one_mul]
    exact hSA (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdEvec j) hEk hEj
  have hF5 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdIevec j) (Work.NN.Newton.cdEvec k))))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSC (Work.NN.Newton.cdIevec j) (Work.NN.Newton.cdEvec k) hIEj hEk
  have hF6 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (Work.NN.Newton.cdIevec k))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSA (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdIevec k) hEj hIEk
  have hF7 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (A z (Work.NN.Newton.cdEvec k)))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSB (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k) hEj hEk
  have hF8 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdIevec k) (Work.NN.Newton.cdEvec j))))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSC (Work.NN.Newton.cdIevec k) (Work.NN.Newton.cdEvec j) hIEk hEj
  have hF9 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (Work.NN.Newton.cdIevec j))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSA (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdIevec j) hEk hIEj
  have hF10 : Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (A z (Work.NN.Newton.cdEvec j)))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    hSB (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdEvec j) hEk hEj
  -- ### sum the ten terms
  have hq : Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.cdQuad A z l j k)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal (40 * a ^ 2) := by
    refine (holderNorm_zero_sum10
      (fun z => Complex.I * Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (Work.NN.Newton.cdEvec k))
      (fun z => Complex.I * Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdEvec k) (Work.NN.Newton.cdEvec j))))
      (fun z => Complex.I * Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdEvec j) (Work.NN.Newton.cdEvec k))))
      (fun z => Complex.I * Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (Work.NN.Newton.cdEvec j))
      (fun z => Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdIevec j) (Work.NN.Newton.cdEvec k))))
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (Work.NN.Newton.cdIevec k))
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec j))
        (A z (Work.NN.Newton.cdEvec k)))
      (fun z => Work.NN.Newton.cdLam l
        (A z (Work.NN.Newton.cdD A z (Work.NN.Newton.cdIevec k) (Work.NN.Newton.cdEvec j))))
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (Work.NN.Newton.cdIevec j))
      (fun z => Work.NN.Newton.cdL A z l (A z (Work.NN.Newton.cdEvec k))
        (A z (Work.NN.Newton.cdEvec j)))).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (add_le_add hF1 hF2) hF3) hF4) hF5) hF6) hF7) hF8) hF9) hF10).trans ?_
    refine le_trans (b := ENNReal.ofReal (40 * a ^ 2)) ?_
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a]))
    refine le_of_eq ?_
    repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- ### put the factor `-(i/8)` back in
  calc Work.CR.Flat.holderNorm 0 α
        (fun z => -(Complex.I / 8) * Work.NN.Newton.cdQuad A z l j k)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      ≤ ENNReal.ofReal ‖(-(Complex.I / 8) : ℂ)‖
          * Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.cdQuad A z l j k)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
        Work.NN.Core.holderNorm_const_mul_le hΩd _ _
    _ = ENNReal.ofReal (1 / 8)
          * Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.cdQuad A z l j k)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by rw [hc8]
    _ ≤ ENNReal.ofReal (1 / 8) * ENNReal.ofReal (40 * a ^ 2) := mul_le_mul' le_rfl hq
    _ = ENNReal.ofReal ((1 / 8) * (40 * a ^ 2)) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal (41 * a ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a])

end

end Work.NN.Newton
