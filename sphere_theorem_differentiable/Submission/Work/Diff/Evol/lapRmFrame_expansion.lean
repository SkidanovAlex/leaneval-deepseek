import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.Evol.ricci_identity_rm
import Submission.Work.Diff.GE.ricAt_eq_sum_frame
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.react.dbKit
import Submission.Work.Diff.GE.react.dRSecCov_bianchi
import Submission.Work.Diff.Evol.diffBianchiA
import Submission.Work.Diff.Evol.covRm_pair
import Submission.Work.Diff.Evol.covRm_skew12
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin
import Submission.Work.Diff.Evol.diffBianchi2
import Submission.Work.Diff.Evol.Qhat_curvAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]


/-! ## The contracted (twice) Bianchi identity

`∑_m (∇_{e_m} Rm)(e_m, a, b, c) = (∇_b Ric)(a,c) - (∇_c Ric)(a,b)`, proved from the differential
Bianchi identity `Work.Diff.Evol.diffBianchiA`, the pair symmetry and the first-slot antisymmetry of
`∇Rm`, and the trace identity `Work.Diff.Evol.covRic_eq_sum_covRm_fin` for `∇Ric`.  In the "array"
notation `S v x y z w := covRm g x (e v) (e x) (e y) (e z) (e w)` (so `v` is the differentiation
slot and the four curvature slots are `x y z w`), the derivation is

`∑_m S m m a b c = ∑_m S m b c m a`  (pair symmetry, termwise)
`∑_m S b m a m c = ∑_m S b m c m a`  (pair symmetry, termwise)
`∑_m S c m a m b = ∑_m S c m b m a`  (pair symmetry, termwise)

and, for each `m`, the differential Bianchi identity with `(v,a,b,c,d) = (e_m, e_b, e_c, e_m, e_a)`
`S m b c m a + S b c m m a + S c m b m a = 0`, together with `S b c m m a = - S b m c m a` (first-slot
antisymmetry), gives `S m b c m a = S b m c m a - S c m b m a` for each `m`.  Summing and using the two
trace identities for `covRic` finishes. -/
theorem contracted_bianchi_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (a b c : TangentSpace I x) :
    (∑ m, covRm g x (e m) (e m) a b c) = covRic g x b a c - covRic g x c a b := by
  classical
  have hRic1 : covRic g x b a c = ∑ m, covRm g x b (e m) c (e m) a := by
    rw [covRic_eq_sum_covRm_fin hLC g x e he b a c]
    exact Finset.sum_congr rfl (fun m _ => covRm_pair hLC g x b (e m) a (e m) c)
  have hRic2 : covRic g x c a b = ∑ m, covRm g x c (e m) b (e m) a := by
    rw [covRic_eq_sum_covRm_fin hLC g x e he c a b]
    exact Finset.sum_congr rfl (fun m _ => covRm_pair hLC g x c (e m) a (e m) b)
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      covRm g x (e m) (e m) a b c
        = covRm g x b (e m) c (e m) a - covRm g x c (e m) b (e m) a := by
    intro m
    have hpair : covRm g x (e m) (e m) a b c = covRm g x (e m) b c (e m) a :=
      covRm_pair hLC g x (e m) (e m) a b c
    have hbianchi := diffBianchiA hLC g x (e m) b c (e m) a
    have hskew : covRm g x b c (e m) (e m) a = - covRm g x b (e m) c (e m) a :=
      covRm_skew12 hLC g x b c (e m) (e m) a
    rw [hpair]
    linarith
  rw [hRic1, hRic2]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_sub_distrib]


/-! ## Auxiliary lemmas for the second-order expansion

`covRm` is the component `(∇_v Rm)(a,b,c,d)` of `∇Rm`, `cov2Rm` the component
`(∇_v∇_w Rm)(a,b,c,d)` of `∇²Rm`, and `covRic`/`cov2Ric` the corresponding components of `∇Ric` and
`∇²Ric`.  The two identities proved below are

`∑_m ∇²_{e_i,e_m}Rm(e_j,e_m,e_k,e_l) = ∇²_{e_i,e_l}Ric(e_j,e_k) - ∇²_{e_i,e_k}Ric(e_j,e_l)`
`∑_m ∇²_{e_j,e_m}Rm(e_m,e_i,e_k,e_l) = ∇²_{e_j,e_k}Ric(e_i,e_l) - ∇²_{e_j,e_l}Ric(e_i,e_k)`

for a `g`-orthonormal frame `e` at `x`.  The proof of the first one: let `W` be a smooth frame field,
orthonormal near `x`, with `W p x = e p`, and put
`Φ y := ∑_p covRm g y (W p y) (J y) (W p y) (K y) (L y)` with `J,K,L` the chosen extensions of
`e_j,e_k,e_l`.  By the contracted Bianchi identity, applied at every `y` near `x` with the orthonormal
frame `W·y`, and the first-slot antisymmetry of `covRm`, `Φ` agrees near `x` with
`y ↦ covRic g y (L y) (J y) (K y) - covRic g y (K y) (J y) (L y)`.  Differentiating at `x` in the
direction `e_i` and expanding both sides with the definitions of `cov2Rm` (`= cov2RmExt` on the chosen
extensions) and of `cov2Ric` gives the identity: the connection corrections on the two sides match,
and the corrections coming from the motion of the frame cancel by skew-adjointness
(`covRic_frame_skew`).  The second identity is the same computation with `(i,j)` interchanged. -/

/-- Linearity of `covRm` in its second argument (the first curvature slot). -/
theorem covRm_linear_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (v : TangentSpace I x) (r s : ℝ) (a₁ a₂ b c d : TangentSpace I x),
      covRm g x v (r • a₁ + s • a₂) b c d
        = r * covRm g x v a₁ b c d + s * covRm g x v a₂ b c d := by
  intro v r s a₁ a₂ b c d
  have h1 : covRm g x v (r • a₁ + s • a₂) b c d
      = - covRm g x v b (r • a₁ + s • a₂) c d :=
    Work.Diff.Evol.covRm_skew12 hLC g x v (r • a₁ + s • a₂) b c d
  have h2 : covRm g x v b (r • a₁ + s • a₂) c d
      = r * covRm g x v b a₁ c d + s * covRm g x v b a₂ c d :=
    Work.Diff.GE.covRm_linear_thd hLC g x v b r s a₁ a₂ c d
  have h3 : covRm g x v b a₁ c d = - covRm g x v a₁ b c d :=
    Work.Diff.Evol.covRm_skew12 hLC g x v b a₁ c d
  have h4 : covRm g x v b a₂ c d = - covRm g x v a₂ b c d :=
    Work.Diff.Evol.covRm_skew12 hLC g x v b a₂ c d
  rw [h1, h2, h3, h4]; ring

/-- `covRm` vanishes when its differentiation slot is `0`. -/
theorem covRm_zero_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    covRm g x 0 a b c d = 0 := by
  have h := Work.Diff.GE.covRm_linear_fst hLC g x 0 0 (0 : TangentSpace I x)
    (0 : TangentSpace I x) a b c d
  simpa using h

/-- Sum-linearity of `covRm` in its first (differentiation) argument. -/
theorem covRm_sum_fst {ι : Type*} (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I x) (a b c' d : TangentSpace I x) :
    covRm g x (∑ q ∈ s, c q • v q) a b c' d = ∑ q ∈ s, c q * covRm g x (v q) a b c' d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using covRm_zero_fst hLC g x a b c' d
  | insert p s hp ih =>
      have h := Work.Diff.GE.covRm_linear_fst hLC g x (c p) 1 (v p)
        (∑ q ∈ s, c q • v q) a b c' d
      rw [Finset.sum_insert hp, Finset.sum_insert hp]
      simp only [one_smul] at h ⊢
      rw [h, ih]; ring

/-- Sum-linearity of `covRm` in its second argument (the first curvature slot). -/
theorem covRm_sum_snd {ι : Type*} (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I x) (a b c' d : TangentSpace I x) :
    covRm g x a (∑ q ∈ s, c q • v q) b c' d = ∑ q ∈ s, c q * covRm g x a (v q) b c' d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := covRm_linear_snd hLC g x a 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x) b c' d
      simpa using h
  | insert p s hp ih =>
      have h := covRm_linear_snd hLC g x a (c p) 1 (v p) (∑ q ∈ s, c q • v q) b c' d
      rw [Finset.sum_insert hp, Finset.sum_insert hp]
      simp only [one_smul] at h ⊢
      rw [h, ih]; ring

/-- Sum-linearity of `covRm` in its third argument (the second curvature slot). -/
theorem covRm_sum_thd {ι : Type*} (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I x) (a b c' d : TangentSpace I x) :
    covRm g x a b (∑ q ∈ s, c q • v q) c' d = ∑ q ∈ s, c q * covRm g x a b (v q) c' d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := Work.Diff.GE.covRm_linear_thd hLC g x a b 0 0 (0 : TangentSpace I x)
        (0 : TangentSpace I x) c' d
      simpa using h
  | insert p s hp ih =>
      have h := Work.Diff.GE.covRm_linear_thd hLC g x a b (c p) 1 (v p)
        (∑ q ∈ s, c q • v q) c' d
      rw [Finset.sum_insert hp, Finset.sum_insert hp]
      simp only [one_smul] at h ⊢
      rw [h, ih]; ring

/-- For a skew-symmetric matrix `c` and any `F`, `∑_{p,q} c_{pq}(F_{qp} + F_{pq}) = 0`. -/
theorem skew_double_sum_zero {ι : Type*} [Fintype ι] (c F : ι → ι → ℝ)
    (hskew : ∀ p q, c p q = - c q p) :
    (∑ p, ∑ q, c p q * F q p) + (∑ p, ∑ q, c p q * F p q) = 0 := by
  have h : (∑ p, ∑ q, c p q * F q p) = - (∑ p, ∑ q, c p q * F p q) := by
    rw [Finset.sum_comm]
    rw [show (∑ q, ∑ p, c p q * F q p) = ∑ p, ∑ q, c q p * F p q from rfl]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hskew p q]; ring
  linarith

/-- **Skew-adjointness cancellation, first pattern.**  For a smooth frame field `W` orthonormal near
`x`, a direction `v` and fixed vectors `X, Y, Z`,
`∑_p [ Rm(∇_vW_p, X, e_p, Y, Z) + Rm(e_p, X, ∇_vW_p, Y, Z) ] = 0`: the two corrections of
`cov2RmExt` in which the moving frame field `W_p` is differentiated cancel. -/
theorem frame_correction_zero_one
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ p, CMDiff ∞ (T% (W p)))
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun p => W p y))
    (X Y Z : TangentSpace I x) :
    (∑ p, covRm g x (lcOf g (W p) x v) X (W p x) Y Z)
      + (∑ p, covRm g x (W p x) X (lcOf g (W p) x v) Y Z) = 0 := by
  classical
  by_cases hm : 0 < Module.finrank ℝ E
  · have hONx : IsONFrame g x (fun p => W p x) := hWON.self_of_nhds
    have hexp : ∀ p, lcOf g (W p) x v
        = ∑ q, g.inner x (lcOf g (W p) x v) (W q x) • W q x :=
      fun p => (Work.Diff.GE.sum_smul_inner_eq_self g x hm (fun q => W q x) hONx
        (lcOf g (W p) x v)).symm
    have hskew : ∀ p q, g.inner x (lcOf g (W p) x v) (W q x)
        = - g.inner x (lcOf g (W q) x v) (W p x) := by
      intro p q
      have h := Work.Diff.GE.covRic_frame_skew hLC g x v W hWs hWON p q
      rw [g.symm x (W p x) (lcOf g (W q) x v)] at h
      linarith
    have h1 : (∑ p, covRm g x (lcOf g (W p) x v) X (W p x) Y Z)
        = ∑ p, ∑ q, g.inner x (lcOf g (W p) x v) (W q x)
            * covRm g x (W q x) X (W p x) Y Z := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      conv_lhs => rw [hexp p]
      exact covRm_sum_fst hLC g x Finset.univ
        (fun q => g.inner x (lcOf g (W p) x v) (W q x)) (fun q => W q x) X (W p x) Y Z
    have h2 : (∑ p, covRm g x (W p x) X (lcOf g (W p) x v) Y Z)
        = ∑ p, ∑ q, g.inner x (lcOf g (W p) x v) (W q x)
            * covRm g x (W p x) X (W q x) Y Z := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      conv_lhs => rw [hexp p]
      exact covRm_sum_thd hLC g x Finset.univ
        (fun q => g.inner x (lcOf g (W p) x v) (W q x)) (fun q => W q x) (W p x) X Y Z
    rw [h1, h2]
    exact skew_double_sum_zero (fun p q => g.inner x (lcOf g (W p) x v) (W q x))
      (fun u w => covRm g x (W u x) X (W w x) Y Z) (fun p q => hskew p q)
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hm
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Finset.univ_eq_empty]

/-- **Skew-adjointness cancellation, second pattern.**  For a smooth frame field `W` orthonormal near
`x`, a direction `v` and fixed vectors `X, Y, Z`,
`∑_p [ Rm(∇_vW_p, e_p, X, Y, Z) + Rm(e_p, ∇_vW_p, X, Y, Z) ] = 0`. -/
theorem frame_correction_zero_two
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ p, CMDiff ∞ (T% (W p)))
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun p => W p y))
    (X Y Z : TangentSpace I x) :
    (∑ p, covRm g x (lcOf g (W p) x v) (W p x) X Y Z)
      + (∑ p, covRm g x (W p x) (lcOf g (W p) x v) X Y Z) = 0 := by
  classical
  by_cases hm : 0 < Module.finrank ℝ E
  · have hONx : IsONFrame g x (fun p => W p x) := hWON.self_of_nhds
    have hexp : ∀ p, lcOf g (W p) x v
        = ∑ q, g.inner x (lcOf g (W p) x v) (W q x) • W q x :=
      fun p => (Work.Diff.GE.sum_smul_inner_eq_self g x hm (fun q => W q x) hONx
        (lcOf g (W p) x v)).symm
    have hskew : ∀ p q, g.inner x (lcOf g (W p) x v) (W q x)
        = - g.inner x (lcOf g (W q) x v) (W p x) := by
      intro p q
      have h := Work.Diff.GE.covRic_frame_skew hLC g x v W hWs hWON p q
      rw [g.symm x (W p x) (lcOf g (W q) x v)] at h
      linarith
    have h1 : (∑ p, covRm g x (lcOf g (W p) x v) (W p x) X Y Z)
        = ∑ p, ∑ q, g.inner x (lcOf g (W p) x v) (W q x)
            * covRm g x (W q x) (W p x) X Y Z := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      conv_lhs => rw [hexp p]
      exact covRm_sum_fst hLC g x Finset.univ
        (fun q => g.inner x (lcOf g (W p) x v) (W q x)) (fun q => W q x) (W p x) X Y Z
    have h2 : (∑ p, covRm g x (W p x) (lcOf g (W p) x v) X Y Z)
        = ∑ p, ∑ q, g.inner x (lcOf g (W p) x v) (W q x)
            * covRm g x (W p x) (W q x) X Y Z := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      conv_lhs => rw [hexp p]
      exact covRm_sum_snd hLC g x Finset.univ
        (fun q => g.inner x (lcOf g (W p) x v) (W q x)) (fun q => W q x) (W p x) X Y Z
    rw [h1, h2]
    exact skew_double_sum_zero (fun p q => g.inner x (lcOf g (W p) x v) (W q x))
      (fun u w => covRm g x (W u x) (W w x) X Y Z) (fun p q => hskew p q)
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hm
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Finset.univ_eq_empty]

/-- Existence of a smooth frame field which is `g`-orthonormal near `x` with `W p x = e p`. -/
theorem exists_frame_field
    (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    ∃ W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y),
      (∀ p, CMDiff ∞ (T% (W p))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun p => W p y)) ∧
      (∀ p, W p x = e p) := by
  classical
  have hVs : ∀ p : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (smoothExt x (e p))) :=
    fun p => Work.Diff.GE.smoothExt_cmdiff x (e p)
  have hVON : IsONFrame g x (fun p : Work.Diff.GE.katoIdx E => smoothExt x (e p) x) := by
    have h : (fun p : Work.Diff.GE.katoIdx E => smoothExt x (e p) x) = e :=
      funext fun p => Work.Diff.GE.smoothExt_apply x (e p)
    rw [h]; exact he
  obtain ⟨h1, h2, h3⟩ := Work.Diff.GE.covRic_onFrame_family (I := I) (M := M) g x
    (fun p : Work.Diff.GE.katoIdx E => smoothExt x (e p)) hVs hVON
  refine ⟨fun p => Work.Diff.GE.katoFrame g x
    (fun q : Work.Diff.GE.katoIdx E => smoothExt x (e q)) p, h1, h2, ?_⟩
  intro p
  show Work.Diff.GE.katoFrame g x
    (fun q : Work.Diff.GE.katoIdx E => smoothExt x (e q)) p x = e p
  rw [h3 p, Work.Diff.GE.smoothExt_apply]


/-- The frozen `Submission.Diff.cov2Rm` is `Work.Diff.GE.cov2RmExt` on the chosen extensions. -/
theorem cov2Rm_frozen_eq_ext (g : SMet I M) (x : M) (u v a b c d : TangentSpace I x) :
    cov2Rm g x u v a b c d
      = Work.Diff.GE.cov2RmExt g x u (smoothExt x v) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d) := by
  simp only [Submission.Diff.cov2Rm, Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]

/-- `cov2Rm` with a frame field in place of the chosen extensions: if `W` is smooth, orthonormal near
`x` with `W p x = e p`, then the `cov2RmExt` expression with the fields `W p` in the direction slots
(the second and fourth arguments of the frozen `cov2Rm`) and the chosen extensions in the curvature
slots is the frozen `cov2Rm` component. -/
theorem cov2Rm_eq_ext_of_frame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ p, CMDiff ∞ (T% (W p))) (hWx : ∀ p, W p x = e p)
    (u : TangentSpace I x) (p a c d : Fin (Module.finrank ℝ E)) :
    cov2Rm g x u (e p) (e a) (e p) (e c) (e d)
      = Work.Diff.GE.cov2RmExt g x u (W p) (smoothExt x (e a)) (W p) (smoothExt x (e c))
          (smoothExt x (e d)) := by
  rw [cov2Rm_frozen_eq_ext]
  have h1 : (W p) x = (smoothExt x (e p)) x := by
    rw [hWx p, Work.Diff.GE.smoothExt_apply]
  rw [← Work.Diff.GE.cov2RmExt_bind_V hLC g x u (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e p))
    (Work.Diff.GE.smoothExt_cmdiff x (e a)) (Work.Diff.GE.smoothExt_cmdiff x (e p))
    (Work.Diff.GE.smoothExt_cmdiff x (e c)) (Work.Diff.GE.smoothExt_cmdiff x (e d)) h1]
  rw [← Work.Diff.GE.cov2RmExt_bind_B hLC g x u (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e a))
    (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e p)) (Work.Diff.GE.smoothExt_cmdiff x (e c))
    (Work.Diff.GE.smoothExt_cmdiff x (e d)) h1]

/-- Variant of `cov2Rm_eq_ext_of_frame` with the frame field in the second curvature slot. -/
theorem cov2Rm_eq_ext_of_frame_a (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ p, CMDiff ∞ (T% (W p))) (hWx : ∀ p, W p x = e p)
    (u : TangentSpace I x) (p a c d : Fin (Module.finrank ℝ E)) :
    cov2Rm g x u (e p) (e p) (e a) (e c) (e d)
      = Work.Diff.GE.cov2RmExt g x u (W p) (W p) (smoothExt x (e a)) (smoothExt x (e c))
          (smoothExt x (e d)) := by
  rw [cov2Rm_frozen_eq_ext]
  have h1 : (W p) x = (smoothExt x (e p)) x := by
    rw [hWx p, Work.Diff.GE.smoothExt_apply]
  rw [← Work.Diff.GE.cov2RmExt_bind_V hLC g x u (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e p))
    (Work.Diff.GE.smoothExt_cmdiff x (e p)) (Work.Diff.GE.smoothExt_cmdiff x (e a))
    (Work.Diff.GE.smoothExt_cmdiff x (e c)) (Work.Diff.GE.smoothExt_cmdiff x (e d)) h1]
  exact Work.Diff.GE.cov2RmExt_bind_A hLC g x u (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e p))
    (hWs p) (Work.Diff.GE.smoothExt_cmdiff x (e a)) (Work.Diff.GE.smoothExt_cmdiff x (e c))
    (Work.Diff.GE.smoothExt_cmdiff x (e d)) h1.symm

/-- **Differentiability of a `covRic` component along smooth fields.**  If `W` is a smooth frame field
orthonormal near `x`, then `y ↦ covRic g y (A y) (B y) (C y)` is differentiable at `x`: near `x` it
coincides with the frame sum `∑ p, covRm g y (A y) (W p y) (B y) (W p y) (C y)` (the trace identity
`covRic_eq_sum_covRm_fin`, applied at every point of a neighbourhood), which is a finite sum of smooth
functions. -/
theorem covRic_component_mdiffAt (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ p, CMDiff ∞ (T% (W p)))
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun p => W p y))
    {A B C : Π y : M, TangentSpace I y} (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) :
    MDiffAt (fun y : M => covRic g y (A y) (B y) (C y)) x := by
  have hsum : CMDiff ∞ (fun y : M => ∑ p, covRm g y (A y) (W p y) (B y) (W p y) (C y)) :=
    ContMDiff.sum (fun p _ => Work.Diff.GE.covRm_fields_smooth hLC hA (hWs p) hB (hWs p) hC)
  have hcongr : (fun y : M => covRic g y (A y) (B y) (C y))
      =ᶠ[𝓝 x] fun y : M => ∑ p, covRm g y (A y) (W p y) (B y) (W p y) (C y) := by
    filter_upwards [hWON] with y hy
    exact covRic_eq_sum_covRm_fin hLC g y (fun p => W p y) hy (A y) (B y) (C y)
  exact (hsum.mdifferentiableAt (by simp)).congr_of_eventuallyEq hcongr


/-- **First trace-expansion identity.**  For a `g`-orthonormal frame `e` at `x`,

`∑_m (∇_{e_i}∇_{e_m}Rm)(e_j, e_m, e_k, e_l) = (∇_{e_i}∇_{e_l}Ric)(e_j,e_k) - (∇_{e_i}∇_{e_k}Ric)(e_j,e_l)`.

Proof: with a smooth frame field `W`, orthonormal near `x`, with `W p x = e p`, and the chosen
extensions `J, K, L` of `e_j, e_k, e_l`, put
`Φ y := ∑_p covRm g y (W p y) (J y) (W p y) (K y) (L y)`.  The contracted Bianchi identity at `y`
(with the orthonormal frame `W·y`) together with the first-slot antisymmetry of `covRm` gives
`Φ y = covRic g y (L y) (J y) (K y) - covRic g y (K y) (J y) (L y)` for `y` near `x`, so the
derivative of `Φ` at `x` in direction `e_i` can be computed in two ways: expanding `Φ` as a finite sum
of `covRm` components (with the fields `W p`) and expanding the `covRic` terms by the definition of
`cov2Ric`.  The connection corrections of the two expansions match: the two corrections in which the
frame field `W p` is differentiated cancel by skew-adjointness (`frame_correction_zero_one`), and the
remaining ones are evaluated by the contracted Bianchi identity with the prescribed frame `e`
(`contracted_bianchi_expansion`). -/
theorem cov2Rm_trace_I
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (∑ m, cov2Rm g x (e i) (e m) (e j) (e m) (e k) (e l))
      = cov2Ric g x (e i) (e l) (e j) (e k) - cov2Ric g x (e i) (e k) (e j) (e l) := by
  classical
  obtain ⟨W, hWs, hWON, hWx⟩ := exists_frame_field (I := I) (M := M) g x e he
  have hJs : CMDiff ∞ (T% (smoothExt x (e j))) := Work.Diff.GE.smoothExt_cmdiff x (e j)
  have hKs : CMDiff ∞ (T% (smoothExt x (e k))) := Work.Diff.GE.smoothExt_cmdiff x (e k)
  have hLs : CMDiff ∞ (T% (smoothExt x (e l))) := Work.Diff.GE.smoothExt_cmdiff x (e l)
  set Φ : M → ℝ := fun y => ∑ p, covRm g y (W p y) (smoothExt x (e j) y) (W p y)
      (smoothExt x (e k) y) (smoothExt x (e l) y) with hΦ
  set Ψ₁ : M → ℝ := fun y => covRic g y (smoothExt x (e l) y) (smoothExt x (e j) y)
      (smoothExt x (e k) y) with hΨ₁
  set Ψ₂ : M → ℝ := fun y => covRic g y (smoothExt x (e k) y) (smoothExt x (e j) y)
      (smoothExt x (e l) y) with hΨ₂
  -- ## Step 1: the pointwise identity
  have hident : Φ =ᶠ[𝓝 x] fun y : M => Ψ₁ y - Ψ₂ y := by
    filter_upwards [hWON] with y hy
    simp only [hΦ, hΨ₁, hΨ₂]
    have hskew : (∑ p, covRm g y (W p y) (smoothExt x (e j) y) (W p y)
          (smoothExt x (e k) y) (smoothExt x (e l) y))
        = - ∑ p, covRm g y (W p y) (W p y) (smoothExt x (e j) y) (smoothExt x (e k) y)
            (smoothExt x (e l) y) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => covRm_skew12 hLC g y (W p y)
        (smoothExt x (e j) y) (W p y) (smoothExt x (e k) y) (smoothExt x (e l) y))
    rw [hskew, contracted_bianchi_expansion hLC g y (fun p => W p y) hy
      (smoothExt x (e j) y) (smoothExt x (e k) y) (smoothExt x (e l) y)]
    ring
  -- ## Step 2: derivative of `Phi` as the difference of the two `covRic` components
  have hdiff : mvfderiv I Φ x (e i) = mvfderiv I Ψ₁ x (e i) - mvfderiv I Ψ₂ x (e i) := by
    have hcongr := Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hident
    rw [hcongr, hΨ₁, hΨ₂]
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (e i))
      (mvfderiv_sub (covRic_component_mdiffAt hLC g x W hWs hWON hLs hJs hKs)
        (covRic_component_mdiffAt hLC g x W hWs hWON hKs hJs hLs))
  -- ## Step 3: expanding the derivative of `Phi` in the frame
  have hA : mvfderiv I Φ x (e i) = ∑ p,
      (Work.Diff.GE.cov2RmExt g x (e i) (W p) (smoothExt x (e j)) (W p) (smoothExt x (e k))
          (smoothExt x (e l))
        + (covRm g x (lcOf g (W p) x (e i)) (e j) (W p x) (e k) (e l)
          + covRm g x (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (W p x) (e k) (e l)
          + covRm g x (W p x) (e j) (lcOf g (W p) x (e i)) (e k) (e l)
          + covRm g x (W p x) (e j) (W p x) (lcOf g (smoothExt x (e k)) x (e i)) (e l)
          + covRm g x (W p x) (e j) (W p x) (e k) (lcOf g (smoothExt x (e l)) x (e i)))) := by
    rw [hΦ]
    rw [show (fun y : M => ∑ p, covRm g y (W p y) (smoothExt x (e j) y) (W p y)
          (smoothExt x (e k) y) (smoothExt x (e l) y))
        = fun y : M => ∑ p ∈ Finset.univ, covRm g y (W p y) (smoothExt x (e j) y) (W p y)
            (smoothExt x (e k) y) (smoothExt x (e l) y) from rfl]
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun p y => covRm g y (W p y) (smoothExt x (e j) y) (W p y) (smoothExt x (e k) y)
        (smoothExt x (e l) y))
      (fun p => Work.Diff.GE.covRm_fields_smooth hLC (hWs p) hJs (hWs p) hKs hLs) x (e i)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]
    ring
  -- ## Step 4: expanding the two `covRic` components by the definition of `cov2Ric`
  have hB1 : mvfderiv I Ψ₁ x (e i)
      = cov2Ric g x (e i) (e l) (e j) (e k)
        + (covRic g x (lcOf g (smoothExt x (e l)) x (e i)) (e j) (e k)
          + covRic g x (e l) (lcOf g (smoothExt x (e j)) x (e i)) (e k)
          + covRic g x (e l) (e j) (lcOf g (smoothExt x (e k)) x (e i))) := by
    rw [hΨ₁]
    simp only [Work.Diff.Evol.cov2Ric]
    ring
  have hB2 : mvfderiv I Ψ₂ x (e i)
      = cov2Ric g x (e i) (e k) (e j) (e l)
        + (covRic g x (lcOf g (smoothExt x (e k)) x (e i)) (e j) (e l)
          + covRic g x (e k) (lcOf g (smoothExt x (e j)) x (e i)) (e l)
          + covRic g x (e k) (e j) (lcOf g (smoothExt x (e l)) x (e i))) := by
    rw [hΨ₂]
    simp only [Work.Diff.Evol.cov2Ric]
    ring
  -- ## Step 5: evaluating the connection corrections
  have hframe : (∑ p, covRm g x (lcOf g (W p) x (e i)) (e j) (W p x) (e k) (e l))
      + (∑ p, covRm g x (W p x) (e j) (lcOf g (W p) x (e i)) (e k) (e l)) = 0 :=
    frame_correction_zero_one hLC g x (e i) W hWs hWON (e j) (e k) (e l)
  have hskewJ : (∑ p, covRm g x (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (W p x) (e k) (e l))
      = - ∑ p, covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (e k) (e l) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => covRm_skew12 hLC g x (W p x)
      (lcOf g (smoothExt x (e j)) x (e i)) (W p x) (e k) (e l))
  have hcbJ : (∑ p, covRm g x (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (W p x) (e k) (e l))
      = covRic g x (e l) (lcOf g (smoothExt x (e j)) x (e i)) (e k)
        - covRic g x (e k) (lcOf g (smoothExt x (e j)) x (e i)) (e l) := by
    rw [hskewJ]
    have hinner : (∑ p, covRm g x (e p) (e p) (lcOf g (smoothExt x (e j)) x (e i)) (e k) (e l))
        = covRic g x (e k) (lcOf g (smoothExt x (e j)) x (e i)) (e l)
          - covRic g x (e l) (lcOf g (smoothExt x (e j)) x (e i)) (e k) :=
      contracted_bianchi_expansion hLC g x e he _ (e k) (e l)
    rw [show (∑ p, covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (e k) (e l))
        = ∑ p, covRm g x (e p) (e p) (lcOf g (smoothExt x (e j)) x (e i)) (e k) (e l) by
      simp only [hWx]]
    rw [hinner]
    ring
  have hskewK : (∑ p, covRm g x (W p x) (e j) (W p x) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
      = - ∑ p, covRm g x (W p x) (W p x) (e j) (lcOf g (smoothExt x (e k)) x (e i)) (e l) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => covRm_skew12 hLC g x (W p x)
      (e j) (W p x) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
  have hcbK : (∑ p, covRm g x (W p x) (e j) (W p x) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
      = covRic g x (e l) (e j) (lcOf g (smoothExt x (e k)) x (e i))
        - covRic g x (lcOf g (smoothExt x (e k)) x (e i)) (e j) (e l) := by
    rw [hskewK]
    have hinner : (∑ p, covRm g x (e p) (e p) (e j) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
        = covRic g x (lcOf g (smoothExt x (e k)) x (e i)) (e j) (e l)
          - covRic g x (e l) (e j) (lcOf g (smoothExt x (e k)) x (e i)) :=
      contracted_bianchi_expansion hLC g x e he (e j) _ (e l)
    rw [show (∑ p, covRm g x (W p x) (W p x) (e j) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
        = ∑ p, covRm g x (e p) (e p) (e j) (lcOf g (smoothExt x (e k)) x (e i)) (e l) by
      simp only [hWx]]
    rw [hinner]
    ring
  have hskewL : (∑ p, covRm g x (W p x) (e j) (W p x) (e k) (lcOf g (smoothExt x (e l)) x (e i)))
      = - ∑ p, covRm g x (W p x) (W p x) (e j) (e k) (lcOf g (smoothExt x (e l)) x (e i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => covRm_skew12 hLC g x (W p x)
      (e j) (W p x) (e k) (lcOf g (smoothExt x (e l)) x (e i)))
  have hcbL : (∑ p, covRm g x (W p x) (e j) (W p x) (e k) (lcOf g (smoothExt x (e l)) x (e i)))
      = covRic g x (lcOf g (smoothExt x (e l)) x (e i)) (e j) (e k)
        - covRic g x (e k) (e j) (lcOf g (smoothExt x (e l)) x (e i)) := by
    rw [hskewL]
    have hinner : (∑ p, covRm g x (e p) (e p) (e j) (e k) (lcOf g (smoothExt x (e l)) x (e i)))
        = covRic g x (e k) (e j) (lcOf g (smoothExt x (e l)) x (e i))
          - covRic g x (lcOf g (smoothExt x (e l)) x (e i)) (e j) (e k) :=
      contracted_bianchi_expansion hLC g x e he (e j) (e k) _
    rw [show (∑ p, covRm g x (W p x) (W p x) (e j) (e k) (lcOf g (smoothExt x (e l)) x (e i)))
        = ∑ p, covRm g x (e p) (e p) (e j) (e k) (lcOf g (smoothExt x (e l)) x (e i)) by
      simp only [hWx]]
    rw [hinner]
    ring
  -- ## Step 6: assemble
  have hα' : mvfderiv I Φ x (e i)
      = (∑ p, cov2Rm g x (e i) (e p) (e j) (e p) (e k) (e l))
        + ((∑ p, covRm g x (lcOf g (W p) x (e i)) (e j) (W p x) (e k) (e l))
          + (∑ p, covRm g x (W p x) (lcOf g (smoothExt x (e j)) x (e i)) (W p x) (e k) (e l))
          + (∑ p, covRm g x (W p x) (e j) (lcOf g (W p) x (e i)) (e k) (e l))
          + (∑ p, covRm g x (W p x) (e j) (W p x) (lcOf g (smoothExt x (e k)) x (e i)) (e l))
          + (∑ p, covRm g x (W p x) (e j) (W p x) (e k)
              (lcOf g (smoothExt x (e l)) x (e i)))) := by
    rw [hA]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun p _ => (cov2Rm_eq_ext_of_frame hLC g x e W hWs hWx
      (e i) p j k l).symm)]
  have hα : mvfderiv I Φ x (e i)
      = (∑ p, cov2Rm g x (e i) (e p) (e j) (e p) (e k) (e l))
        + ((covRic g x (lcOf g (smoothExt x (e l)) x (e i)) (e j) (e k)
            + covRic g x (e l) (lcOf g (smoothExt x (e j)) x (e i)) (e k)
            + covRic g x (e l) (e j) (lcOf g (smoothExt x (e k)) x (e i)))
          - (covRic g x (lcOf g (smoothExt x (e k)) x (e i)) (e j) (e l)
            + covRic g x (e k) (lcOf g (smoothExt x (e j)) x (e i)) (e l)
            + covRic g x (e k) (e j) (lcOf g (smoothExt x (e l)) x (e i)))) := by
    rw [hα']
    linarith [hframe, hcbJ, hcbK, hcbL]
  have hβ : mvfderiv I Φ x (e i)
      = (cov2Ric g x (e i) (e l) (e j) (e k) - cov2Ric g x (e i) (e k) (e j) (e l))
        + ((covRic g x (lcOf g (smoothExt x (e l)) x (e i)) (e j) (e k)
            + covRic g x (e l) (lcOf g (smoothExt x (e j)) x (e i)) (e k)
            + covRic g x (e l) (e j) (lcOf g (smoothExt x (e k)) x (e i)))
          - (covRic g x (lcOf g (smoothExt x (e k)) x (e i)) (e j) (e l)
            + covRic g x (e k) (lcOf g (smoothExt x (e j)) x (e i)) (e l)
            + covRic g x (e k) (e j) (lcOf g (smoothExt x (e l)) x (e i)))) := by
    rw [hdiff, hB1, hB2]
    ring
  linarith [hα, hβ]


/-- **Second trace-expansion identity.**  For a `g`-orthonormal frame `e` at `x`,

`∑_m (∇_{e_j}∇_{e_m}Rm)(e_m, e_i, e_k, e_l) = (∇_{e_j}∇_{e_k}Ric)(e_i,e_l) - (∇_{e_j}∇_{e_l}Ric)(e_i,e_k)`.

The proof is the same computation as `cov2Rm_trace_I` with the roles of the first slot and the inner
differentiation slot exchanged: with `W` a frame field orthonormal near `x` and `I, K, L` the chosen
extensions of `e_i, e_k, e_l`, put `Ξ y := ∑_p covRm g y (W p y) (W p y) (I y) (K y) (L y)`; the
contracted Bianchi identity at `y` (with the orthonormal frame `W·y`) gives
`Ξ y = covRic g y (K y) (I y) (L y) - covRic g y (L y) (I y) (K y)` near `x`, and the derivatives of
the two sides match, the frame-derivative corrections cancelling by `frame_correction_zero_two`. -/
theorem cov2Rm_trace_II
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (∑ m, cov2Rm g x (e j) (e m) (e m) (e i) (e k) (e l))
      = cov2Ric g x (e j) (e k) (e i) (e l) - cov2Ric g x (e j) (e l) (e i) (e k) := by
  classical
  obtain ⟨W, hWs, hWON, hWx⟩ := exists_frame_field (I := I) (M := M) g x e he
  have hIs : CMDiff ∞ (T% (smoothExt x (e i))) := Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hKs : CMDiff ∞ (T% (smoothExt x (e k))) := Work.Diff.GE.smoothExt_cmdiff x (e k)
  have hLs : CMDiff ∞ (T% (smoothExt x (e l))) := Work.Diff.GE.smoothExt_cmdiff x (e l)
  set Ξ : M → ℝ := fun y => ∑ p, covRm g y (W p y) (W p y) (smoothExt x (e i) y)
      (smoothExt x (e k) y) (smoothExt x (e l) y) with hΞ
  set Ψ₁ : M → ℝ := fun y => covRic g y (smoothExt x (e k) y) (smoothExt x (e i) y)
      (smoothExt x (e l) y) with hΨ₁
  set Ψ₂ : M → ℝ := fun y => covRic g y (smoothExt x (e l) y) (smoothExt x (e i) y)
      (smoothExt x (e k) y) with hΨ₂
  -- ## Step 1: the pointwise identity
  have hident : Ξ =ᶠ[𝓝 x] fun y : M => Ψ₁ y - Ψ₂ y := by
    filter_upwards [hWON] with y hy
    simp only [hΞ, hΨ₁, hΨ₂]
    rw [contracted_bianchi_expansion hLC g y (fun p => W p y) hy
      (smoothExt x (e i) y) (smoothExt x (e k) y) (smoothExt x (e l) y)]
  -- ## Step 2: derivative of `Xi` as the difference of the two `covRic` components
  have hdiff : mvfderiv I Ξ x (e j) = mvfderiv I Ψ₁ x (e j) - mvfderiv I Ψ₂ x (e j) := by
    have hcongr := Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hident
    rw [hcongr, hΨ₁, hΨ₂]
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (e j))
      (mvfderiv_sub (covRic_component_mdiffAt hLC g x W hWs hWON hKs hIs hLs)
        (covRic_component_mdiffAt hLC g x W hWs hWON hLs hIs hKs))
  -- ## Step 3: expanding the derivative of `Xi` in the frame
  have hA : mvfderiv I Ξ x (e j) = ∑ p,
      (Work.Diff.GE.cov2RmExt g x (e j) (W p) (W p) (smoothExt x (e i)) (smoothExt x (e k))
          (smoothExt x (e l))
        + (covRm g x (lcOf g (W p) x (e j)) (W p x) (e i) (e k) (e l)
          + covRm g x (W p x) (lcOf g (W p) x (e j)) (e i) (e k) (e l)
          + covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e i)) x (e j)) (e k) (e l)
          + covRm g x (W p x) (W p x) (e i) (lcOf g (smoothExt x (e k)) x (e j)) (e l)
          + covRm g x (W p x) (W p x) (e i) (e k) (lcOf g (smoothExt x (e l)) x (e j)))) := by
    rw [hΞ]
    rw [show (fun y : M => ∑ p, covRm g y (W p y) (W p y) (smoothExt x (e i) y)
          (smoothExt x (e k) y) (smoothExt x (e l) y))
        = fun y : M => ∑ p ∈ Finset.univ, covRm g y (W p y) (W p y) (smoothExt x (e i) y)
            (smoothExt x (e k) y) (smoothExt x (e l) y) from rfl]
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun p y => covRm g y (W p y) (W p y) (smoothExt x (e i) y) (smoothExt x (e k) y)
        (smoothExt x (e l) y))
      (fun p => Work.Diff.GE.covRm_fields_smooth hLC (hWs p) (hWs p) hIs hKs hLs) x (e j)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Work.Diff.GE.cov2RmExt, Work.Diff.GE.smoothExt_apply]
    ring
  -- ## Step 4: expanding the two `covRic` components by the definition of `cov2Ric`
  have hB1 : mvfderiv I Ψ₁ x (e j)
      = cov2Ric g x (e j) (e k) (e i) (e l)
        + (covRic g x (lcOf g (smoothExt x (e k)) x (e j)) (e i) (e l)
          + covRic g x (e k) (lcOf g (smoothExt x (e i)) x (e j)) (e l)
          + covRic g x (e k) (e i) (lcOf g (smoothExt x (e l)) x (e j))) := by
    rw [hΨ₁]
    simp only [Work.Diff.Evol.cov2Ric]
    ring
  have hB2 : mvfderiv I Ψ₂ x (e j)
      = cov2Ric g x (e j) (e l) (e i) (e k)
        + (covRic g x (lcOf g (smoothExt x (e l)) x (e j)) (e i) (e k)
          + covRic g x (e l) (lcOf g (smoothExt x (e i)) x (e j)) (e k)
          + covRic g x (e l) (e i) (lcOf g (smoothExt x (e k)) x (e j))) := by
    rw [hΨ₂]
    simp only [Work.Diff.Evol.cov2Ric]
    ring
  -- ## Step 5: evaluating the connection corrections
  have hframe : (∑ p, covRm g x (lcOf g (W p) x (e j)) (W p x) (e i) (e k) (e l))
      + (∑ p, covRm g x (W p x) (lcOf g (W p) x (e j)) (e i) (e k) (e l)) = 0 :=
    frame_correction_zero_two hLC g x (e j) W hWs hWON (e i) (e k) (e l)
  have hcbI : (∑ p, covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e i)) x (e j)) (e k) (e l))
      = covRic g x (e k) (lcOf g (smoothExt x (e i)) x (e j)) (e l)
        - covRic g x (e l) (lcOf g (smoothExt x (e i)) x (e j)) (e k) := by
    rw [show (∑ p, covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e i)) x (e j)) (e k) (e l))
        = ∑ p, covRm g x (e p) (e p) (lcOf g (smoothExt x (e i)) x (e j)) (e k) (e l) by
      simp only [hWx]]
    exact contracted_bianchi_expansion hLC g x e he _ (e k) (e l)
  have hcbK : (∑ p, covRm g x (W p x) (W p x) (e i) (lcOf g (smoothExt x (e k)) x (e j)) (e l))
      = covRic g x (lcOf g (smoothExt x (e k)) x (e j)) (e i) (e l)
        - covRic g x (e l) (e i) (lcOf g (smoothExt x (e k)) x (e j)) := by
    rw [show (∑ p, covRm g x (W p x) (W p x) (e i) (lcOf g (smoothExt x (e k)) x (e j)) (e l))
        = ∑ p, covRm g x (e p) (e p) (e i) (lcOf g (smoothExt x (e k)) x (e j)) (e l) by
      simp only [hWx]]
    exact contracted_bianchi_expansion hLC g x e he (e i) _ (e l)
  have hcbL : (∑ p, covRm g x (W p x) (W p x) (e i) (e k) (lcOf g (smoothExt x (e l)) x (e j)))
      = covRic g x (e k) (e i) (lcOf g (smoothExt x (e l)) x (e j))
        - covRic g x (lcOf g (smoothExt x (e l)) x (e j)) (e i) (e k) := by
    rw [show (∑ p, covRm g x (W p x) (W p x) (e i) (e k) (lcOf g (smoothExt x (e l)) x (e j)))
        = ∑ p, covRm g x (e p) (e p) (e i) (e k) (lcOf g (smoothExt x (e l)) x (e j)) by
      simp only [hWx]]
    exact contracted_bianchi_expansion hLC g x e he (e i) (e k) _
  -- ## Step 6: assemble
  have hα' : mvfderiv I Ξ x (e j)
      = (∑ p, cov2Rm g x (e j) (e p) (e p) (e i) (e k) (e l))
        + ((∑ p, covRm g x (lcOf g (W p) x (e j)) (W p x) (e i) (e k) (e l))
          + (∑ p, covRm g x (W p x) (lcOf g (W p) x (e j)) (e i) (e k) (e l))
          + (∑ p, covRm g x (W p x) (W p x) (lcOf g (smoothExt x (e i)) x (e j)) (e k) (e l))
          + (∑ p, covRm g x (W p x) (W p x) (e i) (lcOf g (smoothExt x (e k)) x (e j)) (e l))
          + (∑ p, covRm g x (W p x) (W p x) (e i) (e k)
              (lcOf g (smoothExt x (e l)) x (e j)))) := by
    rw [hA]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun p _ => (cov2Rm_eq_ext_of_frame_a hLC g x e W hWs hWx
      (e j) p i k l).symm)]
  have hα : mvfderiv I Ξ x (e j)
      = (∑ p, cov2Rm g x (e j) (e p) (e p) (e i) (e k) (e l))
        + ((covRic g x (lcOf g (smoothExt x (e k)) x (e j)) (e i) (e l)
            + covRic g x (e k) (lcOf g (smoothExt x (e i)) x (e j)) (e l)
            + covRic g x (e k) (e i) (lcOf g (smoothExt x (e l)) x (e j)))
          - (covRic g x (lcOf g (smoothExt x (e l)) x (e j)) (e i) (e k)
            + covRic g x (e l) (lcOf g (smoothExt x (e i)) x (e j)) (e k)
            + covRic g x (e l) (e i) (lcOf g (smoothExt x (e k)) x (e j)))) := by
    rw [hα']
    linarith [hframe, hcbI, hcbK, hcbL]
  have hβ : mvfderiv I Ξ x (e j)
      = (cov2Ric g x (e j) (e k) (e i) (e l) - cov2Ric g x (e j) (e l) (e i) (e k))
        + ((covRic g x (lcOf g (smoothExt x (e k)) x (e j)) (e i) (e l)
            + covRic g x (e k) (lcOf g (smoothExt x (e i)) x (e j)) (e l)
            + covRic g x (e k) (e i) (lcOf g (smoothExt x (e l)) x (e j)))
          - (covRic g x (lcOf g (smoothExt x (e l)) x (e j)) (e i) (e k)
            + covRic g x (e l) (lcOf g (smoothExt x (e i)) x (e j)) (e k)
            + covRic g x (e l) (e i) (lcOf g (smoothExt x (e k)) x (e j)))) := by
    rw [hdiff, hB1, hB2]
    ring
  linarith [hα, hβ]

/-- **Hamilton's expansion of the rough Laplacian of the curvature.** -/
theorem lapRmFrame_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (i j k l : Fin (Module.finrank ℝ E)) :
    lapRmFrame g x e i j k l
      = cov2Ric g x (e i) (e k) (e j) (e l) - cov2Ric g x (e i) (e l) (e j) (e k)
        + cov2Ric g x (e j) (e l) (e i) (e k) - cov2Ric g x (e j) (e k) (e i) (e l)
        + Qhat (rmFrame g x e) i j k l := by
  classical
  -- the differentiated Bianchi identity (at every point)
  have h1 : ∀ (y : M) (v a b c d : TangentSpace I y),
      covRm g y v a b c d + covRm g y a b v c d + covRm g y b v a c d = 0 :=
    fun y v a b c d => diffBianchiA hLC g y v a b c d
  -- `lapRmFrame` is the trace of `∇²Rm`
  have hLap : lapRmFrame g x e i j k l
      = ∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l) := rfl
  rw [hLap]
  -- the differentiated Bianchi identity, summed over the frame
  have hDB : ∀ m : Fin (Module.finrank ℝ E),
      cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)
        = - cov2Rm g x (e m) (e i) (e j) (e m) (e k) (e l)
          - cov2Rm g x (e m) (e j) (e m) (e i) (e k) (e l) := by
    intro m
    have h := diffBianchi2 hLC g h1 x (e m) (e i) (e j) (e k) (e l)
    linarith
  -- the Ricci identity, exchanging the two differentiation slots
  have hRic1 : ∀ m : Fin (Module.finrank ℝ E),
      cov2Rm g x (e m) (e i) (e j) (e m) (e k) (e l)
        = cov2Rm g x (e i) (e m) (e j) (e m) (e k) (e l)
          - rmP g x (rmVec (lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)
          - rmP g x (e j) (rmVec (lcOf g) x (e m) (e i) (e m)) (e k) (e l)
          - rmP g x (e j) (e m) (rmVec (lcOf g) x (e m) (e i) (e k)) (e l)
          - rmP g x (e j) (e m) (e k) (rmVec (lcOf g) x (e m) (e i) (e l)) := by
    intro m
    have h := ricci_identity_rm hLC g x (e m) (e i) (e j) (e m) (e k) (e l)
    linarith
  have hRic2 : ∀ m : Fin (Module.finrank ℝ E),
      cov2Rm g x (e m) (e j) (e m) (e i) (e k) (e l)
        = cov2Rm g x (e j) (e m) (e m) (e i) (e k) (e l)
          - rmP g x (rmVec (lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l)
          - rmP g x (e m) (rmVec (lcOf g) x (e m) (e j) (e i)) (e k) (e l)
          - rmP g x (e m) (e i) (rmVec (lcOf g) x (e m) (e j) (e k)) (e l)
          - rmP g x (e m) (e i) (e k) (rmVec (lcOf g) x (e m) (e j) (e l)) := by
    intro m
    have h := ricci_identity_rm hLC g x (e m) (e j) (e m) (e i) (e k) (e l)
    linarith
  -- the two trace-expansion identities
  have hI := cov2Rm_trace_I hLC g x e he i j k l
  have hII := cov2Rm_trace_II hLC g x e he i j k l
  -- the quadratic terms form `Qhat`
  -- the quadratic terms form `Qhat`
  have hQ := Qhat_curvAction hLC g x e he i j k l
  have hQ' : Qhat (rmFrame g x e) i j k l
      = (∑ m, rmP g x (rmVec (lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l))
        + (∑ m, rmP g x (e j) (rmVec (lcOf g) x (e m) (e i) (e m)) (e k) (e l))
        + (∑ m, rmP g x (e j) (e m) (rmVec (lcOf g) x (e m) (e i) (e k)) (e l))
        + (∑ m, rmP g x (e j) (e m) (e k) (rmVec (lcOf g) x (e m) (e i) (e l)))
        + (∑ m, rmP g x (rmVec (lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l))
        + (∑ m, rmP g x (e m) (rmVec (lcOf g) x (e m) (e j) (e i)) (e k) (e l))
        + (∑ m, rmP g x (e m) (e i) (rmVec (lcOf g) x (e m) (e j) (e k)) (e l))
        + (∑ m, rmP g x (e m) (e i) (e k) (rmVec (lcOf g) x (e m) (e j) (e l))) := by
    rw [hQ]
    simp only [Finset.sum_add_distrib]
    ring
  -- the pointwise combination
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)
        = - cov2Rm g x (e i) (e m) (e j) (e m) (e k) (e l)
          - cov2Rm g x (e j) (e m) (e m) (e i) (e k) (e l)
          + (rmP g x (rmVec (lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)
            + rmP g x (e j) (rmVec (lcOf g) x (e m) (e i) (e m)) (e k) (e l)
            + rmP g x (e j) (e m) (rmVec (lcOf g) x (e m) (e i) (e k)) (e l)
            + rmP g x (e j) (e m) (e k) (rmVec (lcOf g) x (e m) (e i) (e l))
            + rmP g x (rmVec (lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l)
            + rmP g x (e m) (rmVec (lcOf g) x (e m) (e j) (e i)) (e k) (e l)
            + rmP g x (e m) (e i) (rmVec (lcOf g) x (e m) (e j) (e k)) (e l)
            + rmP g x (e m) (e i) (e k) (rmVec (lcOf g) x (e m) (e j) (e l))) := by
    intro m
    rw [hDB m, hRic1 m, hRic2 m]
    ring
  have key : (∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l))
      = - (∑ m, cov2Rm g x (e i) (e m) (e j) (e m) (e k) (e l))
        - (∑ m, cov2Rm g x (e j) (e m) (e m) (e i) (e k) (e l))
        + ((∑ m, rmP g x (rmVec (lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l))
          + (∑ m, rmP g x (e j) (rmVec (lcOf g) x (e m) (e i) (e m)) (e k) (e l))
          + (∑ m, rmP g x (e j) (e m) (rmVec (lcOf g) x (e m) (e i) (e k)) (e l))
          + (∑ m, rmP g x (e j) (e m) (e k) (rmVec (lcOf g) x (e m) (e i) (e l)))
          + (∑ m, rmP g x (rmVec (lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l))
          + (∑ m, rmP g x (e m) (rmVec (lcOf g) x (e m) (e j) (e i)) (e k) (e l))
          + (∑ m, rmP g x (e m) (e i) (rmVec (lcOf g) x (e m) (e j) (e k)) (e l))
          + (∑ m, rmP g x (e m) (e i) (e k) (rmVec (lcOf g) x (e m) (e j) (e l)))) := by
    rw [Finset.sum_congr rfl (fun m _ => hterm m)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith [key, hI, hII, hQ']

end Work.Diff.Evol
