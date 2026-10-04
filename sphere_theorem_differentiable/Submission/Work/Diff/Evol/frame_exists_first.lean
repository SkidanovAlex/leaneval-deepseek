import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.smooth_skew_jet1
import Submission.Work.Diff.Evol.FrameExp
import Submission.Work.Diff.Evol.exp_chain_rule
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.Evol.onframe_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A smooth orthonormal frame, parallel to first order at a point

`Work.Diff.Evol.frame_exists_first`: given a smooth metric `g` on a compact boundaryless smooth
manifold `M`, a point `x` and a `g x`-orthonormal frame `e` of `T_xM`, there is a family `Ef` of
*globally* smooth tangent fields with `Ef i x = e i`, which is `g`-orthonormal near `x` and whose
covariant derivative at `x` vanishes in every direction: `∇_v (Ef i) = 0` for all `v ∈ T_xM`.

Ingredients:

* a `g`-orthonormal family `F` of fields which is `C^∞` on the chart at `x` and satisfies
  `F i x = e i` (`Work.Diff.Evol.onframe_chart`, Gram–Schmidt of the chart coordinate frame);
* a bump `ψ` with `tsupport ψ ⊆ (chartAt H x).source` killing the fields outside the chart, so that
  `u i := ψ • F i` is `C^∞` on all of `M` (`ContMDiffOn.smul_section_of_tsupport`) while still being
  `g`-orthonormal near `x` and equal to `e i` at `x`;
* the exponential correction: for the skew-valued `1`-jet `L(v)_{jk} = -g(∇_v u_k, e_j)` (the
  `g`-orthonormality of `u` near `x` makes `L(v)` skew-symmetric, by the Leibniz rule for the
  Levi-Civita connection), `Work.Diff.Evol.smooth_skew_jet1` produces a smooth skew-valued family
  `B` with `B x = 0` and `dB_x = L`, and `Ef k := ∑_j (exp (B y))_{jk} • u_j y` is smooth,
  orthonormal near `x` (an exponential of a skew matrix is orthogonal, `exp_transpose_mul_exp`) and
  satisfies `∇_v (Ef k)(x) = ∑_j L(v)_{jk} e_j + ∇_v u_k(x) = 0`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix Matrix.Norms.Operator BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

namespace FrameFirst

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- `mvfderiv` of `ℝ`-valued functions respects eventual equality. -/
lemma mvfderiv_congr {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- The matrix exponential, written with the matrix algebra structure explicit. -/
noncomputable abbrev matExp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp A

/-- The linear functional "the `(j,k)`-entry" on matrices. -/
noncomputable def matEntryCLM (n : ℕ) (j k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ where
  toFun A := A j k
  map_add' A B := rfl
  map_smul' c A := rfl

@[simp] lemma matEntryCLM_apply {n : ℕ} (j k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    matEntryCLM n j k A = A j k := rfl

/-- The chain rule for a continuous linear functional applied to the exponential of a smooth family:
the derivative is the functional applied to the derivative of the exponential.  Stated for a general
complete normed algebra so that all its instance arguments are those of a *variable* type. -/
lemma mvfderiv_clm_exp {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (φ : 𝔸 →L[ℝ] ℝ) {B : M → 𝔸} (hB : SmoothMap I M B) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => φ (NormedSpace.exp (B y))) x v
      = φ (mvfderiv I (fun y : M => NormedSpace.exp (B y)) x v) := by
  have hExpSm : SmoothMap I M (fun y : M => NormedSpace.exp (B y)) :=
    exp_contDiff.comp_contMDiff hB
  have hExpd := (hExpSm.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hgd := (ContinuousLinearMap.differentiableAt φ (x := NormedSpace.exp (B x))).mdifferentiableAt
  have hcomp := mvfderiv_comp_apply (I := 𝓘(ℝ, 𝔸))
    (I' := I) (M' := M) (M := 𝔸) (F := ℝ)
    (f := fun y : M => NormedSpace.exp (B y)) (g := φ) x hgd hExpd v
  show mvfderiv I (φ ∘ (fun y : M => NormedSpace.exp (B y))) x v = _
  rw [hcomp]
  have hclm : mvfderiv 𝓘(ℝ, 𝔸) φ (NormedSpace.exp (B x)) = φ := by
    rw [mvfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt φ).fderiv
  rw [hclm]
  rfl

/-- The chain rule for the `(j,k)`-entry of the exponential of a smooth matrix-valued family,
written with the entry functional. -/
lemma mvfderiv_entry_exp {n : ℕ} {B : M → Matrix (Fin n) (Fin n) ℝ}
    (hB : SmoothMap I M B) (x : M) (j k : Fin n) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => matEntryCLM n j k (matExp (B y))) x v
      = matEntryCLM n j k (mvfderiv I (fun y : M => matExp (B y)) x v) :=
  mvfderiv_clm_exp (𝔸 := Matrix (Fin n) (Fin n) ℝ) (matEntryCLM n j k) hB x v

/-- The `(j,k)`-entry of the exponential of a smooth matrix-valued family: `mvfderiv` of the entry
function is the entry of the `mvfderiv`. -/
lemma mvfderiv_entry_exp' {n : ℕ} {B : M → Matrix (Fin n) (Fin n) ℝ}
    (hB : SmoothMap I M B) (x : M) (j k : Fin n) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => (matExp (B y)) j k) x v
      = (mvfderiv I (fun y : M => matExp (B y)) x v) j k := by
  have hfun : (fun y : M => (matExp (B y)) j k)
      = (fun y : M => matEntryCLM n j k (matExp (B y))) := by
    funext y
    exact (matEntryCLM_apply j k (matExp (B y))).symm
  rw [hfun, mvfderiv_entry_exp (B := B) hB x j k v, matEntryCLM_apply]

/-- Bilinearity of `g.inner` with respect to two finite sums. -/
lemma inner_sum_sum (g : SMet I M) (y : M) {n : ℕ} (c d : Fin n → ℝ)
    (v : Fin n → TangentSpace I y) :
    g.inner y (∑ k, c k • v k) (∑ l, d l • v l)
      = ∑ k, ∑ l, (c k * d l) * g.inner y (v k) (v l) := by
  have h1 : g.inner y (∑ k, c k • v k) (∑ l, d l • v l)
      = ∑ l, d l * (∑ k, c k * g.inner y (v k) (v l)) := by
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma smooth_skew_jet1_matrix {n : ℕ} (x : M)
    (L : TangentSpace I x → Matrix (Fin n) (Fin n) ℝ)
    (hLlin : ∀ (r s : ℝ) (v w : TangentSpace I x), L (r • v + s • w) = r • L v + s • L w)
    (hLsk : ∀ (v : TangentSpace I x) (p i : Fin n), L v i p = -(L v p i)) :
    ∃ B : M → Matrix (Fin n) (Fin n) ℝ,
      SmoothMap I M B ∧ B x = 0 ∧
      (∀ y : M, Matrix.transpose (B y) = -(B y)) ∧
      (∀ v : TangentSpace I x, mvfderiv I B x v = L v) := by
  classical
  have hL0 : L 0 = 0 := by
    have h := hLlin 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
    simpa using h
  have hLadd : ∀ v w : TangentSpace I x, L (v + w) = L v + L w := by
    intro v w
    have h := hLlin 1 1 v w
    simpa using h
  have hLsmul : ∀ (r : ℝ) (v : TangentSpace I x), L (r • v) = r • L v := by
    intro r v
    have h := hLlin r 0 v (0 : TangentSpace I x)
    simpa [hL0] using h
  let Lin : TangentSpace I x →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := L, map_add' := hLadd, map_smul' := hLsmul }
  let Φ : E →L[ℝ] Matrix (Fin n) (Fin n) ℝ := LinearMap.toContinuousLinearMap Lin
  have hΦ : ∀ v : TangentSpace I x, Φ v = L v :=
    fun v => congrFun (LinearMap.coe_toContinuousLinearMap' Lin) v
  obtain ⟨ψ, -, hψsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  set G : M → E := fun y => (extChartAt I x) y - (extChartAt I x) x with hG
  have hGOn : ContMDiffOn I 𝓘(ℝ,E) ∞ G (chartAt H x).source :=
    (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
  have hΦOn := (ContinuousLinearMap.contMDiff (n := ∞) Φ).comp_contMDiffOn (f := G) hGOn
  refine ⟨fun y : M => (ψ : M → ℝ) y • Φ (G y), ?_, ?_, ?_, ?_⟩
  · exact ψ.contMDiff_smul hΦOn
  · show (ψ : M → ℝ) x • Φ (G x) = 0
    simp [hG]
  · intro y
    show Matrix.transpose ((ψ : M → ℝ) y • Φ (G y)) = -((ψ : M → ℝ) y • Φ (G y))
    have hsk : Matrix.transpose (Φ (G y)) = -(Φ (G y)) := by
      ext p i
      simpa [Matrix.transpose_apply, hΦ (G y)] using hLsk (G y) p i
    calc Matrix.transpose ((ψ : M → ℝ) y • (Φ (G y)))
        = (ψ : M → ℝ) y • Matrix.transpose (Φ (G y)) := Matrix.transpose_smul _ _
      _ = (ψ : M → ℝ) y • (-(Φ (G y))) := by rw [hsk]
      _ = -((ψ : M → ℝ) y • (Φ (G y))) := by rw [smul_neg]
  · intro v
    have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
      ψ.contMDiff.mdifferentiableAt (by simp)
    have hΦd := ((hΦOn x (mem_chart_source H x)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
    have hmul := mvfderiv_smul hψd hΦd
    have hchart : mvfderiv I (Φ ∘ G) x v = Φ v := by
      have hfun : (Φ ∘ G)
          = (fun y : M => Φ ((extChartAt I x) y - (extChartAt I x) x)) := by
        funext y
        rw [Function.comp_apply, hG]
      rw [hfun]
      exact mvfderiv_clm_comp_chart (I := I) x Φ v
    have hsmul_eq : (fun y : M => (ψ : M → ℝ) y • Φ (G y))
        = (fun y : M => (ψ : M → ℝ) y) • (Φ ∘ G) := rfl
    rw [hsmul_eq]
    have hψx : (ψ : M → ℝ) x = 1 := SmoothBumpFunction.eq_one ψ
    have hGx : G x = 0 := by simp [hG]
    have hmulv := congrArg (fun (L' : TangentSpace I x →L[ℝ] Matrix (Fin n) (Fin n) ℝ) => L' v) hmul
    refine hmulv.trans ?_
    have hψ0 : mvfderiv I (fun y : M => (ψ : M → ℝ) y) x = 0 := by
      rw [mvfderiv_congr ψ.eventuallyEq_one]
      exact mvfderiv_const (1 : ℝ)
    have hzero : (mvfderiv I (fun y : M => (ψ : M → ℝ) y) x).smulRight ((Φ ∘ G) x) v = 0 := by
      rw [hψ0]
      simp
    show (ψ : M → ℝ) x • (mvfderiv I (Φ ∘ G) x v)
        + (mvfderiv I (fun y : M => (ψ : M → ℝ) y) x).smulRight ((Φ ∘ G) x) v = L v
    rw [hzero, add_zero, hψx, one_smul, hchart]
    exact hΦ v

/-- **The main construction.**  Given a `g`-orthonormal frame `F` on the chart at `x` with
`F i x = e i` (which is `Work.Diff.Evol.onframe_chart`), build the corrected frame by the
exponential of the skew correction of the connection matrix. -/
lemma frame_exists_aux
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e)
    (hFrame : ∃ F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, F i x = e i) ∧
      (∀ i, ContMDiffOn I I.tangent ∞ (T% (F i)) (chartAt H x).source) ∧
      (∀ y ∈ (chartAt H x).source, IsONFrame g y (fun i => F i y))) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, SmoothField I M (Ef i)) ∧
      ONFrameNear I M g x Ef ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
        Submission.Diff.lcOf g (Ef i) x v = 0) := by
  classical
  obtain ⟨F, hFx, hFsmooth, hFON⟩ := hFrame
  -- a bump function supported in the chart at `x`
  obtain ⟨ψ, -, hψsupp⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  -- the bumped frame
  set u : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => (ψ : M → ℝ) • F i with hu
  have husm : ∀ i, SmoothField I M (u i) := fun i => by
    show CMDiff ∞ (T% ((ψ : M → ℝ) • F i))
    exact ContMDiffOn.smul_section_of_tsupport (hψ := ψ.contMDiff.contMDiffOn)
      (chartAt H x).open_source hψsupp (hFsmooth i)
  have hux : ∀ i, u i x = e i := fun i => by
    show (ψ : M → ℝ) x • F i x = e i
    rw [SmoothBumpFunction.eq_one ψ, one_smul, hFx i]
  have huON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => u i y) := by
    filter_upwards [ψ.eventuallyEq_one,
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hψy hy
    show IsONFrame g y (fun i => (ψ : M → ℝ) y • F i y)
    rw [hψy]
    simpa using hFON y hy
  -- the skew `1`-jet of the correction
  set L : TangentSpace I x → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun v j k => - g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j) with hL
  have hLlin : ∀ (r s : ℝ) (v w : TangentSpace I x), L (r • v + s • w) = r • L v + s • L w := by
    intro r s v w
    funext j k
    show - g.inner x (((Submission.Diff.lcOf g) (u k) x) (r • v + s • w)) (e j)
        = r * (- g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j))
          + s * (- g.inner x (((Submission.Diff.lcOf g) (u k) x) w) (e j))
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hskew : ∀ (v : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)),
      g.inner x (((Submission.Diff.lcOf g) (u p) x) v) (e i)
        + g.inner x (((Submission.Diff.lcOf g) (u i) x) v) (e p) = 0 := by
    intro v p i
    have hprod := Work.Diff.GE.kato_mvfderiv_inner_lc g x v (husm p) (husm i)
    have hzero : mvfderiv I (fun y : M => g.inner y (u p y) (u i y)) x v = 0 := by
      have hev : (fun y : M => g.inner y (u p y) (u i y))
          =ᶠ[𝓝 x] (fun _ : M => (if p = i then (1 : ℝ) else 0)) := by
        filter_upwards [huON] with y hy
        exact hy p i
      rw [mvfderiv_congr hev, mvfderiv_const]
      rfl
    rw [hzero, hux p, hux i,
      g.symm x (e p) (((Submission.Diff.lcOf g) (u i) x) v)] at hprod
    linarith
  have hLsk : ∀ (v : TangentSpace I x) (p i : Fin (Module.finrank ℝ E)), L v i p = - L v p i := by
    intro v p i
    show - g.inner x (((Submission.Diff.lcOf g) (u p) x) v) (e i)
        = - - g.inner x (((Submission.Diff.lcOf g) (u i) x) v) (e p)
    rw [neg_neg]
    have h := hskew v p i
    linarith
  obtain ⟨B, hBsm, hBx0, hBsk, hBderiv⟩ :=
    smooth_skew_jet1_matrix (I := I) (M := M) (n := Module.finrank ℝ E) x L hLlin hLsk
  -- the corrected frame
  set Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun k y => ∑ j, (matExp (B y)) j k • u j y with hEf
  -- (1) the value at `x`
  have hEfx : ∀ k, Ef k x = e k := by
    intro k
    show (∑ j, (matExp (B x)) j k • u j x) = e k
    have hMx : matExp (B x) = 1 := by
      rw [hBx0]
      exact NormedSpace.exp_zero
    rw [Finset.sum_eq_single k]
    · rw [hMx, Matrix.one_apply_eq, one_smul, hux k]
    · intro j _ hj
      rw [hMx, Matrix.one_apply_ne hj, zero_smul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  -- (2) smoothness of the corrected frame
  have hExpSm : SmoothMap I M (fun y : M => matExp (B y)) :=
    exp_contDiff.comp_contMDiff hBsm
  have hcoeff : ∀ j k : Fin (Module.finrank ℝ E),
      CMDiff ∞ (fun y : M => (matExp (B y)) j k) := by
    intro j k
    have h := (ContinuousLinearMap.contMDiff (matEntryCLM _ j k)).comp hExpSm
    have hfun : (fun y : M => (matExp (B y)) j k)
        = (fun y : M => matEntryCLM (Module.finrank ℝ E) j k (matExp (B y))) := by
      funext y
      exact (matEntryCLM_apply j k (matExp (B y))).symm
    rw [hfun]
    exact h
  have hEfsm : ∀ k, SmoothField I M (Ef k) := by
    intro k
    have h := ContMDiff.sum_section (s := Finset.univ)
      (t := fun j y => (matExp (B y)) j k • u j y)
      (fun j _ => (hcoeff j k).smul_section (husm j))
    simpa [hEf] using h
  -- (3) orthonormality near `x`
  have hEfON : ONFrameNear I M g x Ef := by
    filter_upwards [huON] with y hyON
    intro i j
    show g.inner y (∑ k, (matExp (B y)) k i • u k y)
        (∑ l, (matExp (B y)) l j • u l y) = if i = j then (1 : ℝ) else 0
    have hM : Matrix.transpose (matExp (B y)) * matExp (B y) = 1 := by
      simpa [matExp] using exp_transpose_mul_exp (B y) (hBsk y)
    have hinner : ∀ k, (∑ l, ((matExp (B y)) k i * (matExp (B y)) l j)
        * g.inner y (u k y) (u l y))
        = (matExp (B y)) k i * (matExp (B y)) k j := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [hyON k k, if_pos rfl, mul_one]
      · intro l _ hl
        rw [hyON k l, if_neg (fun h : k = l => hl h.symm), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hsum : (∑ k, (matExp (B y)) k i * (matExp (B y)) k j)
        = (Matrix.transpose (matExp (B y)) * matExp (B y)) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])
    rw [inner_sum_sum g y (fun k => (matExp (B y)) k i)
        (fun l => (matExp (B y)) l j) (fun k => u k y),
      Finset.sum_congr rfl (fun k _ => hinner k), hsum, hM, Matrix.one_apply]
  -- (4) the covariant derivative vanishes at `x`
  have hEfderiv : ∀ (k : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
      Submission.Diff.lcOf g (Ef k) x v = 0 := by
    intro k v
    have hZ : CMDiffAt ∞ (T% (Ef k)) x := (hEfsm k).contMDiffAt
    have hσ : ∀ j, CMDiffAt ∞ (T% (u j)) x := fun j => (husm j).contMDiffAt
    have hf : ∀ j, CMDiffAt ∞ (fun y : M => (matExp (B y)) j k) x :=
      fun j => (hcoeff j k).contMDiffAt
    have heq : Ef k =ᶠ[𝓝 x] (fun y : M => ∑ j, (matExp (B y)) j k • u j y) :=
      Filter.EventuallyEq.rfl
    have hmain : Submission.Diff.lcOf g (Ef k) x v
        = ∑ j ∈ Finset.univ, (matExp (B x)) j k • ((Submission.Diff.lcOf g) (u j) x) v
          + ∑ j ∈ Finset.univ,
              (mvfderiv I (fun y : M => (matExp (B y)) j k) x v) • u j x :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
        (cov := Submission.Diff.lcOf g) (s := Finset.univ)
        (f := fun j y => (matExp (B y)) j k) (σ := u) (Z := Ef k)
        hZ hσ hf heq (x := x) (v := v)
    have hMx : matExp (B x) = 1 := by
      rw [hBx0]
      exact NormedSpace.exp_zero
    have hsum1 : (∑ j ∈ Finset.univ,
          (matExp (B x)) j k • ((Submission.Diff.lcOf g) (u j) x) v)
        = ((Submission.Diff.lcOf g) (u k) x) v := by
      rw [Finset.sum_eq_single k]
      · rw [hMx, Matrix.one_apply_eq, one_smul]
      · intro j _ hj
        rw [hMx, Matrix.one_apply_ne hj, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    have hcoef : ∀ j, mvfderiv I (fun y : M => (matExp (B y)) j k) x v
        = - g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j) := by
      intro j
      have hchain : mvfderiv I (fun y : M => matExp (B y)) x v = mvfderiv I B x v :=
        (Work.Diff.Evol.exp_chain_rule B hBsm x hBx0).1 v
      rw [mvfderiv_entry_exp' (I := I) (B := B) hBsm x j k v, hchain, hBderiv v]
    have hsum2 : (∑ j ∈ Finset.univ,
          (mvfderiv I (fun y : M => (matExp (B y)) j k) x v) • u j x)
        = - ((Submission.Diff.lcOf g) (u k) x) v := by
      rw [show (∑ j ∈ Finset.univ,
              (mvfderiv I (fun y : M => (matExp (B y)) j k) x v) • u j x)
            = ∑ j, (- g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j)) • u j x from by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hcoef j]]
      rw [show (∑ j, (- g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j)) • u j x)
            = -(∑ j, g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j) • u j x) from by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by rw [neg_smul])]
      rw [show (∑ j, g.inner x (((Submission.Diff.lcOf g) (u k) x) v) (e j) • u j x)
            = ((Submission.Diff.lcOf g) (u k) x) v from by
          simp_rw [hux]
          exact Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x e he
            (((Submission.Diff.lcOf g) (u k) x) v)]
    rw [hmain, hsum1, hsum2, add_neg_cancel]
  exact ⟨Ef, hEfx, hEfsm, hEfON, hEfderiv⟩

end FrameFirst

theorem frame_exists_first
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, Work.Diff.Evol.SmoothField I M (Ef i)) ∧
      Work.Diff.Evol.ONFrameNear I M g x Ef ∧
      (∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I x),
        Submission.Diff.lcOf g (Ef i) x v = 0) := by
  obtain ⟨F, h1, h2, h3⟩ := Work.Diff.Evol.onframe_chart (I := I) (M := M) g x e he
  exact FrameFirst.frame_exists_aux g x e he ⟨F, h1, h2, h3⟩

end Work.Diff.Evol
