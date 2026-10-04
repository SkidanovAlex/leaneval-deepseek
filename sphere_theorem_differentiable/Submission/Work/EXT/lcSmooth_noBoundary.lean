import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.T.FrameExt
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. `lcOf g` is Mathlib's `leviCivitaConnection` (Koszul, via duality). Torsion-free and Mathlib-compatible are in Mathlib
(`torsion_leviCivitaConnection_eq_zero`, `isMetricCompatible_leviCivitaConnection`). Convert the latter to the challenge's
`IsMetricCompatible` (mvfderiv of the inner product).
Smoothness: in a chart, ∇_X Y = X(Y) + Γ(X, Y), with Christoffel symbols given by the Koszul formula in coordinates. They are
smooth because g and g⁻¹ are smooth. The seeded library has chart Christoffel machinery for the instance metric
(ChartConnection.lean, ChartCurv.lean: chrB, gammaEntry) that you can reuse with the letI instance.
`ContMDiffCovariantDerivative` asks: for a C^k field X and a C^{k+1} section σ, ∇_X σ is C^k. Check its exact definition in
Mathlib (Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean).

ACTUAL PROOF (this file; boundary-free copy of `Submission/Work/Diff/T/lc_smooth`, whose `[I.Boundaryless]` hypotheses are unused).  `ContMDiffCovariantDerivative (lcOf g) ∞` is obtained as follows.

* `lc_koszul_pairing` : for globally smooth `σ X Z`, `q ↦ ⟪∇_X σ q, Z q⟫` is smooth.  This is the Koszul formula
  (`leviCivitaConnection_apply_inner`) together with `mvfderiv_apply_contMDiff` (derivative of a smooth function along a
  smooth field is smooth) and smoothness of `mlieBracket` of smooth fields.
* `section_of_inner_cmdiff` (separate file) : if all pairings `⟪V, Z⟫` (Z globally smooth) are smooth, then `V` is a smooth
  section.  The proof inverts the Gram matrix of the coordinate frame (`Matrix.posDef_gram_of_linearIndependent`).
* `lc_hom_section` : if for every globally smooth `Z` the field `A (Z)` is smooth, then `q ↦ ⟨q, A q⟩` is a smooth section
  of the bundle of endomorphisms of `TM`.  Proved with the endomorphism-bundle trivialization `hom_trivializationAt`.
* `lc_metric_identity` : the Leibniz rule `X⟪Y,Z⟫ = ⟪∇_X Y, Z⟫ + ⟪Y, ∇_X Z⟫` for the Levi-Civita connection, from the Koszul
  formula; it yields the challenge's `IsMetricCompatible` (with `FiberBundle.extend` to realise an arbitrary tangent vector).
-/

namespace Work.EXT

open Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- **Koszul pairing.**  For globally smooth `σ X Z`, the function `q ↦ ⟪∇_X σ q, Z q⟫` is smooth. -/
theorem lc_koszul_pairing [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {σ X Z : Π x : M, TangentSpace I x}
    (hσ : CMDiff ∞ (T% σ)) (hX : CMDiff ∞ (T% X)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (fun q : M =>
      inner ℝ ((CovariantDerivative.leviCivitaConnection I M) σ q (X q)) (Z q)) := by
  have hmσ : ∀ q : M, MDiffAt (T% σ) q := fun q => hσ.contMDiffAt.mdifferentiableAt (by simp)
  have hmX : ∀ q : M, MDiffAt (T% X) q := fun q => hX.contMDiffAt.mdifferentiableAt (by simp)
  have hmZ : ∀ q : M, MDiffAt (T% Z) q := fun q => hZ.contMDiffAt.mdifferentiableAt (by simp)
  have mb : ∀ {A B : Π x : M, TangentSpace I x}, CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      CMDiff ∞ (T% (mlieBracket I A B)) := by
    intro A B hA hB
    haveI : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
      have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
      rw [h]; infer_instance
    intro y
    exact (hA y).mlieBracket_vectorField (hB y) (by simp)
  have hbr1 : CMDiff ∞ (T% (mlieBracket I X Z)) := mb hX hZ
  have hbr2 : CMDiff ∞ (T% (mlieBracket I σ X)) := mb hσ hX
  have hbr3 : CMDiff ∞ (T% (mlieBracket I Z σ)) := mb hZ hσ
  have hA : CMDiff ∞ (fun q : M => (d% (fun y : M => inner ℝ (σ y) (Z y)) q) (X q)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
      (f := fun y : M => inner ℝ (σ y) (Z y)) (X := X)
      (ContMDiff.inner_bundle hσ hZ) hX
  have hB : CMDiff ∞ (fun q : M => (d% (fun y : M => inner ℝ (Z y) (X y)) q) (σ q)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
      (f := fun y : M => inner ℝ (Z y) (X y)) (X := σ)
      (ContMDiff.inner_bundle hZ hX) hσ
  have hC : CMDiff ∞ (fun q : M => (d% (fun y : M => inner ℝ (X y) (σ y)) q) (Z q)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
      (f := fun y : M => inner ℝ (X y) (σ y)) (X := Z)
      (ContMDiff.inner_bundle hX hσ) hZ
  have hD : CMDiff ∞ (fun q : M => inner ℝ (σ q) (mlieBracket I X Z q)) :=
    ContMDiff.inner_bundle hσ hbr1
  have hE : CMDiff ∞ (fun q : M => inner ℝ (Z q) (mlieBracket I σ X q)) :=
    ContMDiff.inner_bundle hZ hbr2
  have hF : CMDiff ∞ (fun q : M => inner ℝ (X q) (mlieBracket I Z σ q)) :=
    ContMDiff.inner_bundle hX hbr3
  have hsum0 : CMDiff ∞ (fun q : M =>
      ((d% (fun y : M => inner ℝ (σ y) (Z y)) q) (X q)
        + (d% (fun y : M => inner ℝ (Z y) (X y)) q) (σ q)
        - (d% (fun y : M => inner ℝ (X y) (σ y)) q) (Z q)
        - inner ℝ (σ q) (mlieBracket I X Z q)
        - inner ℝ (Z q) (mlieBracket I σ X q)
        + inner ℝ (X q) (mlieBracket I Z σ q))) :=
    ((hA.add hB).sub hC).sub hD |>.sub hE |>.add hF
  have hsum : CMDiff ∞ (fun q : M =>
      ((d% (fun y : M => inner ℝ (σ y) (Z y)) q) (X q)
        + (d% (fun y : M => inner ℝ (Z y) (X y)) q) (σ q)
        - (d% (fun y : M => inner ℝ (X y) (σ y)) q) (Z q)
        - inner ℝ (σ q) (mlieBracket I X Z q)
        - inner ℝ (Z q) (mlieBracket I σ X q)
        + inner ℝ (X q) (mlieBracket I Z σ q)) / 2) := by
    simpa only [Pi.div_apply] using hsum0.div_const 2
  refine hsum.congr (fun q => ?_)
  exact (CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (X := X) (Y := σ) (Z := Z)
    (hmX q) (hmσ q) (hmZ q))

/-- **Sections of the endomorphism bundle.**  If applying `A` to every globally smooth vector field
gives a smooth field, then `q ↦ ⟨q, A q⟩` is a smooth section of the bundle of endomorphisms. -/
theorem lc_hom_section [T2Space M]
    {A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (h : ∀ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) →
        CMDiff ∞ (T% (fun q : M => A q (Z q)))) :
    CMDiff ∞ (fun q : M => (⟨q, A q⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  intro p
  set triv := trivializationAt E (TangentSpace I) p with htriv
  have hp : p ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p
  have hb : p ∈ (trivializationAt (E →L[ℝ] E)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hp, hp⟩
  refine (Trivialization.contMDiffAt_section_iff
    (trivializationAt (E →L[ℝ] E)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p) hb).mpr ?_
  simp only [hom_trivializationAt_apply]
  set P : M → (E →L[ℝ] E) :=
    fun x => ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) p x p x (A x)
    with hP
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, E) ∞ (fun q : M => P q ((Module.finBasis ℝ E) i)) p := by
    intro i
    obtain ⟨Z, hZ, hZeq⟩ :=
      exists_global_eventuallyEq_symmL (I := I) p ((Module.finBasis ℝ E) i)
        (mem_chart_source H p)
    have hW : CMDiff ∞ (T% (fun q : M => A q (Z q))) := h Z hZ
    have hcoord : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun q : M => triv.continuousLinearMapAt ℝ q (A q (Z q))) p := by
      have h1 := (Trivialization.contMDiffAt_section_iff triv hp).mp hW.contMDiffAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [triv.open_baseSet.mem_nhds hp] with q hq
      exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hq (A q (Z q))
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [hZeq] with q hq
    show P q ((Module.finBasis ℝ E) i) = triv.continuousLinearMapAt ℝ q (A q (Z q))
    rw [hP]
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [show Z q = (trivializationAt E (TangentSpace I) p).symmL ℝ q ((Module.finBasis ℝ E) i)
      from hq]
  have hpi : ContMDiffAt I 𝓘(ℝ, Fin (Module.finrank ℝ E) → E) ∞
      (fun q : M => fun i => P q ((Module.finBasis ℝ E) i)) p :=
    contMDiffAt_pi_space.mpr hcomp
  have hterm : ∀ i : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun q : M => (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
        (P q ((Module.finBasis ℝ E) i))) p := by
    intro i
    have hL : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
        ((((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight)
        (P p ((Module.finBasis ℝ E) i)) :=
      (((ContinuousLinearMap.smulRightL ℝ E E)
        (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).contDiff).contMDiff.contMDiffAt
    exact hL.comp p (hcomp i)
  have hsum : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun q : M =>
      ∑ i, (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
        (P q ((Module.finBasis ℝ E) i))) p :=
    ContMDiffAt.sum (t := Finset.univ) (fun i _ => hterm i)
  have hident : ∀ q : M, P q = ∑ i, (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
        (P q ((Module.finBasis ℝ E) i)) := by
    intro q
    ext v
    rw [sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, Module.Basis.coord_apply,
      LinearMap.coe_toContinuousLinearMap']
    conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => hident q))

/-- **Leibniz rule for the Levi-Civita connection** (metric compatibility, pointwise form). -/
theorem lc_metric_identity [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    (d% (fun y : M => inner ℝ (Y y) (Z y)) x) (X x) =
      inner ℝ ((CovariantDerivative.leviCivitaConnection I M) Y x (X x)) (Z x) +
      inner ℝ (Y x) ((CovariantDerivative.leviCivitaConnection I M) Z x (X x)) := by
  have k1 := CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (X := X) (Y := Y)
    (Z := Z) hX hY hZ
  have k2 := CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (X := X) (Y := Z)
    (Z := Y) hX hZ hY
  have hcomm : inner ℝ (Y x) (((CovariantDerivative.leviCivitaConnection I M) Z x) (X x))
      = inner ℝ (((CovariantDerivative.leviCivitaConnection I M) Z x) (X x)) (Y x) :=
    real_inner_comm _ _
  rw [hcomm, k1, k2]
  have e1 : (fun y : M => inner ℝ (X y) (Y y)) = (fun y : M => inner ℝ (Y y) (X y)) := by
    funext y; exact real_inner_comm _ _
  have e2 : (fun y : M => inner ℝ (X y) (Z y)) = (fun y : M => inner ℝ (Z y) (X y)) := by
    funext y; exact real_inner_comm _ _
  have e3 : (fun y : M => inner ℝ (Z y) (Y y)) = (fun y : M => inner ℝ (Y y) (Z y)) := by
    funext y; exact real_inner_comm _ _
  have e4 : (fun y : M => inner ℝ (Y y) (X y)) = (fun y : M => inner ℝ (X y) (Y y)) := by
    funext y; exact real_inner_comm _ _
  have b1 : mlieBracket I X Z = - mlieBracket I Z X := VectorField.mlieBracket_swap
  have b2 : mlieBracket I Z Y = - mlieBracket I Y Z := VectorField.mlieBracket_swap
  have b3 : mlieBracket I Y Z = - mlieBracket I Z Y := VectorField.mlieBracket_swap
  have b4 : mlieBracket I Y X = - mlieBracket I X Y := VectorField.mlieBracket_swap
  rw [e1, e2, e3, e4, b1, b2, b3, b4]
  simp only [Pi.neg_apply, inner_neg_right]
  ring_nf

theorem lc_section_of_inner [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {V : Π x : M, TangentSpace I x}
    (h : ∀ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) →
        CMDiff ∞ (fun q : M => inner ℝ (V q) (Z q))) :
    CMDiff ∞ (T% V) := by
  intro p
  set triv := trivializationAt E (TangentSpace I) p with htriv
  have hp : p ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p
  choose Z hZ hZeq using fun i : Fin (Module.finrank ℝ E) =>
    exists_global_eventuallyEq_symmL (I := I) p ((Module.finBasis ℝ E) i) (mem_chart_source H p)
  have hP : ∀ j : Fin (Module.finrank ℝ E), CMDiff ∞ (fun q : M => inner ℝ (V q) (Z j q)) :=
    fun j => h (Z j) (hZ j)
  set Gm : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => Matrix.gram ℝ (fun i => Z i q) with hGm
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => Gm q i j) p := by
    intro i j
    have h1 : CMDiff ∞ (fun q : M => inner ℝ (Z i q) (Z j q)) :=
      ContMDiff.inner_bundle (hZ i) (hZ j)
    simpa only [hGm, Matrix.gram_apply] using h1.contMDiffAt
  have det_smooth : ∀ (A : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ),
      (∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => A q i j) p) →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (A q).det) p := by
    intro A hA
    have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i) p :=
      ContMDiffAt.sum (t := Finset.univ) fun σ _ =>
        ContMDiffAt.mul (contMDiffAt_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ)))
          (ContMDiffAt.prod (t := Finset.univ) (f := fun i q => A q (σ i) i)
            (fun i _ => hA (σ i) i))
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    show (A q).det = ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [Units.smul_def, zsmul_eq_mul]
  have hdetGm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (Gm q).det) p := det_smooth Gm hentry
  have hadj : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (Gm q).adjugate a b) p := by
    intro a b
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun q : M => ((fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ))) q).det) p :=
      det_smooth (fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ))) (fun i j => ?_)
    · simpa only [Matrix.adjugate_apply] using h1
    · by_cases hij : i = b
      · subst hij
        have hself : (fun q : M => (Gm q).updateRow i (Pi.single a (1 : ℝ)) i j)
            = fun _ : M => (Pi.single a (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) j := by
          funext q
          exact congrFun (Matrix.updateRow_self (M := Gm q) (i := i) (b := Pi.single a (1 : ℝ))) j
        rw [hself]
        exact contMDiffAt_const
      · have hne : (fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ)) i j)
            = fun q : M => Gm q i j := by
          funext q
          exact congrFun (Matrix.updateRow_ne (M := Gm q) (i := b)
            (b := Pi.single a (1 : ℝ)) hij) j
        rw [hne]
        exact hentry i j
  have hdetp_ne : (Gm p).det ≠ 0 := by
    have hframe : LinearIndependent ℝ
        (fun i => triv.symmL ℝ p ((Module.finBasis ℝ E) i)) := by
      have hker : LinearMap.ker
          ((triv.symmL ℝ p : E →L[ℝ] TangentSpace I p) : E →ₗ[ℝ] TangentSpace I p) = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro y hy
        have h2 : (triv.symmL ℝ p) y = 0 := by simpa using hy
        have h1 := Trivialization.continuousLinearMapAt_symmL (e := triv) (R := ℝ) hp y
        rw [h2, map_zero] at h1
        exact h1.symm
      have h1 := (Module.finBasis ℝ E).linearIndependent.map'
        ((triv.symmL ℝ p : E →L[ℝ] TangentSpace I p) : E →ₗ[ℝ] TangentSpace I p) hker
      convert h1 using 1
      ext i
      rfl
    have hLI : LinearIndependent ℝ (fun i => Z i p) := by
      rw [show (fun i => Z i p)
        = fun i => triv.symmL ℝ p ((Module.finBasis ℝ E) i) from
        funext fun i => (hZeq i).eq_of_nhds]
      exact hframe
    have hpos : (Gm p).PosDef := by
      rw [hGm]
      exact Matrix.posDef_gram_of_linearIndependent hLI
    exact (hpos.det_pos).ne'
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ)⁻¹ a b) p := by
    intro a b
    have hdetT : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ).det) p := by
      simpa only [Matrix.det_transpose] using hdetGm
    have hadjT : ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ).adjugate i j) p := by
      intro i j
      simpa only [← Matrix.adjugate_transpose, Matrix.transpose_apply] using hadj j i
    have hdetT_ne : ((Gm p)ᵀ).det ≠ 0 := by
      simpa only [Matrix.det_transpose] using hdetp_ne
    have hfun : (fun q : M => ((Gm q)ᵀ)⁻¹ a b)
        = fun q => (((Gm q)ᵀ).det)⁻¹ * ((Gm q)ᵀ).adjugate a b := by
      funext q
      rw [Matrix.inv_def]
      simp
    rw [hfun]
    have hinv1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (((Gm q)ᵀ).det)⁻¹) p :=
      ((ContDiffAt.inv contDiffAt_id hdetT_ne).contMDiffAt).comp p hdetT
    exact ContMDiffAt.mul hinv1 (hadjT a b)
  set x : M → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun q => ((Gm q)ᵀ)⁻¹ *ᵥ (fun j => inner ℝ (V q) (Z j q)) with hx
  have hx_smooth : ∀ a, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => x q a) p := by
    intro a
    have hfun : (fun q : M => x q a)
        = fun q => ∑ j, ((Gm q)ᵀ)⁻¹ a j * inner ℝ (V q) (Z j q) := by
      funext q
      rw [hx]
      exact Matrix.mulVec_apply _ _ _
    rw [hfun]
    exact ContMDiffAt.sum (t := Finset.univ) fun j _ =>
      ContMDiffAt.mul (hinv a j) ((hP j).contMDiffAt)
  set W : Π q : M, TangentSpace I q := fun q => ∑ i, (x q) i • Z i q with hWdef
  have hW : ContMDiffAt I I.tangent ∞ (T% W) p := by
    have h1 := ContMDiffAt.sum_section (I := I) (s := Finset.univ)
      (t := fun i (q : M) => (x q) i • Z i q)
      (fun i _ => ContMDiffAt.smul_section (hx_smooth i) ((hZ i).contMDiffAt))
    convert h1 using 1
  have hgood : ∀ᶠ q in 𝓝 p,
      q ∈ triv.baseSet ∧ (∀ i, Z i q = triv.symmL ℝ q ((Module.finBasis ℝ E) i)) ∧
        ((Gm q).det ≠ 0) := by
    have h1 : ∀ᶠ q in 𝓝 p, ∀ i, Z i q = triv.symmL ℝ q ((Module.finBasis ℝ E) i) :=
      Filter.eventually_all.2 hZeq
    have h2 : ∀ᶠ q in 𝓝 p, (Gm q).det ≠ 0 :=
      hdetGm.continuousAt.eventually_ne hdetp_ne
    filter_upwards [triv.open_baseSet.mem_nhds hp, h1, h2] with q hq1 hq2 hq3
    exact ⟨hq1, hq2, hq3⟩
  have hVW : V =ᶠ[𝓝 p] W := by
    filter_upwards [hgood] with q hq
    obtain ⟨hqb, hqZ, hqdet⟩ := hq
    have hunit : IsUnit ((Gm q)ᵀ).det := by
      refine isUnit_iff_ne_zero.mpr ?_
      simpa only [Matrix.det_transpose] using hqdet
    have hrepr : (∑ i, ((Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q)))
          • (Module.finBasis ℝ E) i) = triv.continuousLinearMapAt ℝ q (V q) := by
      simpa only [Module.Basis.coord_apply] using
        (Module.Basis.sum_repr (Module.finBasis ℝ E) (triv.continuousLinearMapAt ℝ q (V q)))
    have hexp : V q
        = ∑ i, ((Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q))) • Z i q := by
      conv_lhs => rw [← Trivialization.symmL_continuousLinearMapAt (e := triv) (R := ℝ) hqb (V q)]
      conv_lhs => rw [← hrepr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      exact congrArg (fun w => ((Module.finBasis ℝ E).coord i
        (triv.continuousLinearMapAt ℝ q (V q))) • w) (hqZ i).symm
    have hsys : ((Gm q)ᵀ) *ᵥ (fun i =>
          (Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q)))
        = fun j => inner ℝ (V q) (Z j q) := by
      funext j
      rw [Matrix.mulVec_apply_eq_sum]
      conv_rhs => rw [hexp, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.transpose_apply, hGm, Matrix.gram_apply, real_inner_smul_left]
      ring
    have hxq : x q = fun i =>
        (Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q)) := by
      have h2 := congrArg (fun w => ((Gm q)ᵀ)⁻¹ *ᵥ w) hsys
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at h2
      rw [hx]
      exact h2.symm
    show V q = ∑ i, (x q) i • Z i q
    simp only [hxq]
    exact hexp
  refine hW.congr_of_eventuallyEq ?_
  filter_upwards [hVW] with q hq
  exact congrArg (fun v : TangentSpace I q => (⟨q, v⟩ : TangentBundle I M)) hq

theorem lcSmooth_noBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] :
    LCSmooth I M := by
  intro g
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun {σ} hσ => ?_⟩⟩⟩
    rw [contMDiffOn_univ]
    have hσ' : CMDiff ∞ (T% σ) := contMDiffOn_univ.mp hσ
    refine lc_hom_section (A := fun q : M => (lcOf g) σ q) ?_
    intro Z hZ
    exact lc_section_of_inner (V := fun q : M => (lcOf g) σ q (Z q))
      (fun Z' hZ' => lc_koszul_pairing hσ' hZ hZ')
  · exact CovariantDerivative.torsion_leviCivitaConnection_eq_zero I
  · show ∀ (Y Z : Π x : M, TangentSpace I x),
      CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
      ∀ (x : M) (v : TangentSpace I x),
        mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
          inner ℝ (lcOf g Y x v) (Z x) + inner ℝ (Y x) (lcOf g Z x v)
    intro Y Z hY hZ x v
    have hX : MDiffAt (T% (FiberBundle.extend E v)) x :=
      FiberBundle.mdifferentiableAt_extend I E v
    have key := lc_metric_identity (X := FiberBundle.extend E v) (Y := Y) (Z := Z) (x := x) hX
      (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
    rw [FiberBundle.extend_apply_self] at key
    exact key

end Work.EXT
