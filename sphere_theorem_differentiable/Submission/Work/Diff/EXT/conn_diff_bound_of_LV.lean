import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.EXT.ConnDefs
import Submission.Work.Diff.EXT.SmConnVar
import Submission.Work.Diff.EXT.metric_equiv_of_curvBound
import Submission.Work.Diff.EXT.ric_bound_of_curvBound
import Submission.Work.EXT.ricAt_eq_sum_frame
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.Diff.EXT.CovRicAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The connection-difference estimate for a Ricci flow with bounded `|∇Rm|`

If `G` is a smooth Ricci flow on `[0,T)` with bounded curvature and bounded `|∇Rm|`, then the
Levi-Civita connections of the metrics `G t` and `G 0` differ by at most `C₂ |u| |w|`:

`√(⟪∇^{g_t}_u W_u − ∇^{g_0}_u W_u, ∇^{g_t}_u W_u − ∇^{g_0}_u W_u⟫_{g_t}) ≤ C₂ |u|_{g_t} |w|_{g_t}`

for `W_u` a smooth extension of `w`.  This is the `Shi`-type input used by the continuation
argument of the Brendle–Schoen proof.

The proof is the `∂ₜ Γ` argument: contract the first-variation formula of the Levi-Civita
connection (`LCVariation`) against `∂ₜ g = -2 Ric`, use the trace identity
`∇Ric = tr ∇Rm` (so that `∂ₜ Γ` is controlled by `|∇Rm|`), integrate in time, and convert between
the metrics at times `0` and `t` by the standard metric-comparison estimate.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Elementary tools -/

/-- The reparametrisation trick: a family which is jointly smooth on the half-open interval `[0,T)`
is jointly smooth on the open interval `(-ρ,ρ)` after the substitution `t = τ ^ 2`, provided
`ρ ^ 2 ≤ T`. -/
theorem jointSmooth_sqFlow' (G : ℝ → SMet I M) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρT : ρ ^ 2 ≤ T) (h : JointSmooth G (Set.Ico 0 T)) :
    JointSmooth (fun τ : ℝ => G (τ ^ 2)) (Set.Ioo (-ρ) ρ) := by
  unfold Submission.Diff.JointSmooth
  have hsq : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M => (p.1) ^ 2) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := by
    have h1 : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => p.1)
        (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := contMDiffOn_fst
    simpa using h1.pow 2
  have hΛ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : ℝ × M => (p.1 ^ 2, p.2)) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) :=
    hsq.prodMk contMDiffOn_snd
  have hsub : (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M))
      ⊆ (fun p : ℝ × M => (p.1 ^ 2, p.2)) ⁻¹' (Set.Ico 0 T ×ˢ (univ : Set M)) := by
    intro p hp
    obtain ⟨hp1, -⟩ := hp
    obtain ⟨hlo, hhi⟩ := hp1
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · nlinarith [sq_nonneg p.1]
    · have h1 : 0 < ρ - p.1 := by linarith
      have h2 : 0 < ρ + p.1 := by linarith
      have hmul : 0 < (ρ - p.1) * (ρ + p.1) := mul_pos h1 h2
      nlinarith [hmul]
  exact ContMDiffOn.comp h hΛ hsub

/-- Cauchy–Schwarz for a single Riemannian metric. -/
theorem smet_cauchy' (g : SMet I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have h1 : g.inner x v w = Inner.inner ℝ v w := rfl
  have h2 : g.inner x v v = Inner.inner ℝ v v := rfl
  have h3 : g.inner x w w = Inner.inner ℝ w w := rfl
  rw [h1, h2, h3]
  have hcs : |Inner.inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
  have hv : Real.sqrt (Inner.inner ℝ v v) = ‖v‖ := by
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
  have hw : Real.sqrt (Inner.inner ℝ w w) = ‖w‖ := by
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg w)]
  rw [hv, hw]
  exact hcs

/-- A metric inequality gives a norm inequality. -/
theorem sqrt_le_of_inner_le {g g' : SMet I M} {x : M} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : TangentSpace I x, g'.inner x v v ≤ c * (g.inner x v v)) (v : TangentSpace I x) :
    Real.sqrt (g'.inner x v v) ≤ Real.sqrt c * Real.sqrt (g.inner x v v) := by
  rw [← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt (h v)

/-- Mean value inequality wrapper: if `f'` bounds the derivative of `f` on `(a,b)` and `f'` is
bounded by `C` there, then `|f b - f a| ≤ C (b - a)`. -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (f' x) (Set.Icc a b) x)
    (hbd : ∀ x ∈ Set.Ico a b, |f' x| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (a := a) (b := b)
    (C := C) hf (fun x hx => by simpa [Real.norm_eq_abs] using hbd x hx)
  have hb := h b (Set.right_mem_Icc.mpr hab)
  simpa [Real.norm_eq_abs] using hb

/-- The covariant derivative of the zero bilinear form vanishes. -/
@[simp] theorem covDerivSym2_zero
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (U V W : Π y : M, TangentSpace I y) (x : M) :
    Submission.Diff.covDerivSym2 cov (fun _ _ _ => (0 : ℝ)) U V W x = 0 := by
  rw [Submission.Diff.covDerivSym2]
  simp [mvfderiv_const]

/-- The pointwise Ricci trace identity in an orthonormal frame, at the smooth level. -/
theorem ricTrace_sm [T2Space M] (hLC : LCSmooth I M) :
    ∀ (g : SMet I M) (y : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
      IsONFrame g y e → ∀ u v : TangentSpace I y,
        ricAt (lcOf g) y u v = ∑ m, rmP g y (e m) u (e m) v := by
  intro g y e he u v
  have hcov := (hLC g).1.some
  have h := Work.EXT.ricAt_eq_sum_frame (I := I) (M := M) g hcov y e he u v
  simpa only [Submission.Diff.rmP] using h

/-! ## The estimate -/

/-- The connection-difference estimate, from the first-variation formula and the bound on `∇Ric`. -/
theorem conn_diff_bound_of_LV_aux
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (hbnd : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (g : SMet I M) (x : M) (v a b : TangentSpace I x),
      |Work.Diff.Evol.covRic g x v a b| ≤ Cb * Real.sqrt (dRmNormSq g x)
        * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
        * Real.sqrt (g.inner x b b))
    (G : ℝ → SMet I M) (T C C₁ : ℝ) (hT : 0 < T)
    (hflow : IsRicciFlow G T)
    (hCurv : ∀ t ∈ Ico 0 T, CurvBound (G t) C)
    (hdRm : ∀ t ∈ Ico 0 T, ∀ x : M, dRmNormSq (G t) x ≤ C₁) :
    ∃ C₂ : ℝ, ∀ t ∈ Ico 0 T, ∀ x : M, ∀ u w : TangentSpace I x,
      Real.sqrt ((G t).inner x
          (lcOf (G t) (smoothExt x w) x u - lcOf (G 0) (smoothExt x w) x u)
          (lcOf (G t) (smoothExt x w) x u - lcOf (G 0) (smoothExt x w) x u))
        ≤ C₂ * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) := by
  classical
  -- ### the first-variation bound of `connVar_bound`
  obtain ⟨Cv, hCv0, hCv⟩ := Work.Diff.GE.Sm.connVar_bound_aux (I := I) (M := M) hLC hLV
    (Work.Diff.GE.Sm.dRicPhi_eq_sum_covRm_sm (I := I) (M := M) hLC (ricTrace_sm hLC))
    (Work.Diff.GE.Sm.covRic_eq_sum_covRm_sm (I := I) (M := M) hLC (ricTrace_sm hLC))
    hbnd
  -- ### comparison of the metrics at the times `0`, `s`, `t`
  set Cp : ℝ := max C 0 with hCpdef
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  have hCurv' : ∀ t ∈ Ico 0 T, CurvBound (G t) Cp :=
    fun t ht x e he i j k l => le_trans (hCurv t ht x e he i j k l) hCCp
  have hmet :=
    Work.Diff.EXT.metric_equiv_of_curvBound (I := I) (M := M) G T Cp hT hCp0 hflow hCurv'
  set K : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * Cp) * T) with hKdef
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hnc0 : 0 ≤ (Module.finrank ℝ E : ℝ) * Cp := mul_nonneg hn0 hCp0
  have h2nc0 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * Cp) := by linarith
  have hK1 : 1 ≤ K := by
    rw [hKdef, ← Real.exp_zero, Real.exp_le_exp]
    exact mul_nonneg h2nc0 hT.le
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hcmp0 : ∀ x : M, ∀ s ∈ Ico 0 T, ∀ v : TangentSpace I x,
      (G 0).inner x v v ≤ K * (G s).inner x v v := by
    intro x s hs v
    have h1 : (G 0).inner x v v
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * Cp) * s) * (G s).inner x v v :=
      (hmet s hs x v).2
    have h2 : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * Cp) * s) ≤ K := by
      rw [hKdef, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hs.2.le h2nc0
    have h3 : 0 ≤ (G s).inner x v v := Work.Diff.GE.Sm.smet_inner_self_nonneg (G s) x v
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h3)
  have hcmp1 : ∀ x : M, ∀ s ∈ Ico 0 T, ∀ v : TangentSpace I x,
      (G s).inner x v v ≤ K * (G 0).inner x v v := by
    intro x s hs v
    have h1 : (G s).inner x v v
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * Cp) * s) * (G 0).inner x v v :=
      (hmet s hs x v).1
    have h2 : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * Cp) * s) ≤ K := by
      rw [hKdef, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left hs.2.le h2nc0
    have h3 : 0 ≤ (G 0).inner x v v := Work.Diff.GE.Sm.smet_inner_self_nonneg (G 0) x v
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 h3)
  -- ### the per-point argument
  refine ⟨2 * T * K ^ 7 * Real.sqrt (max (Cv * C₁) 0), ?_⟩
  intro t ht x u w
  by_cases hC₁ : 0 ≤ C₁
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G 0).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    set V : Π y : M, TangentSpace I y := smoothExt x u with hVdef
    set W : Π y : M, TangentSpace I y := smoothExt x w with hWdef
    have hVsm : Work.Diff.GE.SmoothField M V := by
      rw [hVdef]; exact Work.Diff.GE.smoothExt_cmdiff x u
    have hWsm : Work.Diff.GE.SmoothField M W := by
      rw [hWdef]; exact Work.Diff.GE.smoothExt_cmdiff x w
    have hVx : V x = u := by rw [hVdef]; exact Work.Diff.GE.smoothExt_apply x u
    have hWx : W x = w := by rw [hWdef]; exact Work.Diff.GE.smoothExt_apply x w
    set r : ℝ := Real.sqrt t with hrdef
    have hr2 : r ^ 2 = t := by rw [hrdef]; exact Real.sq_sqrt ht.1
    have hr0 : 0 ≤ r := by rw [hrdef]; exact Real.sqrt_nonneg t
    -- the connection field along the (reparametrised) flow
    set f : ℝ → TangentSpace I x := fun τ => lcOf (G (τ ^ 2)) W x (V x) with hfdef
    have hfr : f r = lcOf (G t) W x (V x) := by
      rw [hfdef]; simp only; rw [hr2]
    have hf0 : f 0 = lcOf (G 0) W x (V x) := by
      rw [hfdef]; norm_num
    -- ### the first variation vector, as a function of the (reparametrised) time
    have hJs : JointSmooth G (Ioo 0 T) :=
      hflow.1.mono (Set.prod_mono Ioo_subset_Ico_self (Subset.refl _))
    have hex : ∀ τ : ℝ, ∃ A : TangentSpace I x,
        τ ^ 2 ∈ Ioo 0 T → HasDerivAt (fun s : ℝ => lcOf (G s) W x (V x)) A (τ ^ 2) := by
      intro τ
      by_cases h : τ ^ 2 ∈ Ioo 0 T
      · obtain ⟨A, hA, -⟩ := hLV G (Ioo 0 T) isOpen_Ioo hJs (τ ^ 2) h V W hVsm hWsm x
        exact ⟨A, fun _ => hA⟩
      · exact ⟨0, fun hh => absurd hh h⟩
    set A : ℝ → TangentSpace I x := fun τ => Classical.choose (hex τ) with hAdef
    have hAspec : ∀ τ : ℝ, τ ^ 2 ∈ Ioo 0 T →
        HasDerivAt (fun s : ℝ => lcOf (G s) W x (V x)) (A τ) (τ ^ 2) :=
      fun τ h => Classical.choose_spec (hex τ) h
    -- ### differentiability of `τ ↦ ⟪f τ, ζ⟫` on `(0, r]`
    have hder : ∀ (ζ : TangentSpace I x) (τ : ℝ), 0 < τ → τ ≤ r →
        HasDerivAt (fun τ' : ℝ => (G 0).inner x (f τ') ζ) ((G 0).inner x (A τ) ζ * (2 * τ)) τ := by
      intro ζ τ hτ0 hτr
      have hs : τ ^ 2 ∈ Ioo 0 T := by
        refine ⟨pow_pos hτ0 2, ?_⟩
        exact lt_of_le_of_lt (pow_le_pow_left₀ hτ0.le hτr 2) (by rw [hr2]; exact ht.2)
      have hζ : HasDerivAt (fun _ : ℝ => ζ) (0 : TangentSpace I x) (τ ^ 2) :=
        hasDerivAt_const (c := ζ) (x := τ ^ 2)
      have hInner : HasDerivAt (fun τ' : ℝ => Inner.inner ℝ (lcOf (G (τ' ^ 2)) W x (V x)) ζ)
          (Inner.inner ℝ (A τ) ζ * (2 * τ)) τ := by
        have hL : HasDerivAt (fun s : ℝ => Inner.inner ℝ (lcOf (G s) W x (V x)) ζ)
            (Inner.inner ℝ (A τ) ζ) (τ ^ 2) := by
          have h := HasDerivAt.inner ℝ (hAspec τ hs) hζ
          simpa using h
        have h2 : HasDerivAt (fun τ' : ℝ => τ' ^ 2) (2 * τ) τ := by
          simpa using hasDerivAt_pow 2 τ
        have h3 := HasDerivAt.comp (h := fun τ' : ℝ => τ' ^ 2) (x := τ) hL h2
        simpa [Function.comp_def] using h3
      exact hInner
    -- ### the bound on the derivative
    have hbd : ∀ (ζ : TangentSpace I x) (τ : ℝ), τ ∈ Ioo 0 r →
        |(G 0).inner x (A τ) ζ * (2 * τ)| ≤
          2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
            * Real.sqrt ((G t).inner x w w) * Real.sqrt ((G 0).inner x ζ ζ) := by
      intro ζ τ hτ
      have hs : τ ^ 2 ∈ Ioo 0 T := by
        refine ⟨pow_pos hτ.1 2, ?_⟩
        exact lt_of_le_of_lt (pow_le_pow_left₀ hτ.1.le hτ.2.le 2) (by rw [hr2]; exact ht.2)
      have hsIco : τ ^ 2 ∈ Ico 0 T := ⟨le_of_lt hs.1, hs.2⟩
      have htIco : t ∈ Ico 0 T := ht
      -- the bound on the first variation vector
      have h1 : (G 0).inner x (A τ) (A τ) ≤ K * (G (τ ^ 2)).inner x (A τ) (A τ) :=
        hcmp0 x (τ ^ 2) hsIco (A τ)
      have h2 := hCv G T hflow (τ ^ 2) hs x V W hVsm hWsm (A τ) (hAspec τ hs)
      have hVb : (G (τ ^ 2)).inner x (V x) (V x) ≤ K * K * (G t).inner x (V x) (V x) := by
        have ha := hcmp1 x (τ ^ 2) hsIco (V x)
        have hb := hcmp0 x t htIco (V x)
        have hnn : 0 ≤ (G t).inner x (V x) (V x) :=
          Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x (V x)
        calc (G (τ ^ 2)).inner x (V x) (V x) ≤ K * (G 0).inner x (V x) (V x) := ha
          _ ≤ K * (K * (G t).inner x (V x) (V x)) := mul_le_mul_of_nonneg_left hb hKpos.le
          _ = K * K * (G t).inner x (V x) (V x) := by ring
      have hWb : (G (τ ^ 2)).inner x (W x) (W x) ≤ K * K * (G t).inner x (W x) (W x) := by
        have ha := hcmp1 x (τ ^ 2) hsIco (W x)
        have hb := hcmp0 x t htIco (W x)
        have hnn : 0 ≤ (G t).inner x (W x) (W x) :=
          Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x (W x)
        calc (G (τ ^ 2)).inner x (W x) (W x) ≤ K * (G 0).inner x (W x) (W x) := ha
          _ ≤ K * (K * (G t).inner x (W x) (W x)) := mul_le_mul_of_nonneg_left hb hKpos.le
          _ = K * K * (G t).inner x (W x) (W x) := by ring
      have hdRmτ : dRmNormSq (G (τ ^ 2)) x ≤ C₁ := hdRm (τ ^ 2) hsIco x
      have huu : 0 ≤ (G t).inner x u u := Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x u
      have hww : 0 ≤ (G t).inner x w w := Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x w
      -- combine into a bound with `K ^ 5`
      have hA0 : (G 0).inner x (A τ) (A τ)
          ≤ Cv * C₁ * K ^ 5 * ((G t).inner x u u * (G t).inner x w w) := by
        have hstep : (G (τ ^ 2)).inner x (A τ) (A τ)
            ≤ Cv * C₁ * (K * K * (G t).inner x u u) * (K * K * (G t).inner x w w) := by
          refine le_trans h2 ?_
          have hA' : Cv * dRmNormSq (G (τ ^ 2)) x ≤ Cv * C₁ :=
            mul_le_mul_of_nonneg_left hdRmτ hCv0
          have hA'' : 0 ≤ Cv * dRmNormSq (G (τ ^ 2)) x :=
            mul_nonneg hCv0 (Work.Diff.GE.Gest.dRmNormSq_nonneg (I := I) (M := M) _ _)
          have hRV : 0 ≤ K * K * (G t).inner x (V x) (V x) :=
            mul_nonneg (mul_nonneg hKpos.le hKpos.le)
              (Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x (V x))
          have hRW : 0 ≤ K * K * (G t).inner x (W x) (W x) :=
            mul_nonneg (mul_nonneg hKpos.le hKpos.le)
              (Work.Diff.GE.Sm.smet_inner_self_nonneg (G t) x (W x))
          have hVn : 0 ≤ (G (τ ^ 2)).inner x (V x) (V x) :=
            Work.Diff.GE.Sm.smet_inner_self_nonneg (G (τ ^ 2)) x (V x)
          have hWn : 0 ≤ (G (τ ^ 2)).inner x (W x) (W x) :=
            Work.Diff.GE.Sm.smet_inner_self_nonneg (G (τ ^ 2)) x (W x)
          calc Cv * dRmNormSq (G (τ ^ 2)) x * (G (τ ^ 2)).inner x (V x) (V x)
                * (G (τ ^ 2)).inner x (W x) (W x)
              ≤ (Cv * C₁) * (K * K * (G t).inner x (V x) (V x))
                * (K * K * (G t).inner x (W x) (W x)) :=
                mul_le_mul (mul_le_mul hA' hVb hVn (mul_nonneg hCv0 hC₁)) hWb hWn
                  (mul_nonneg (mul_nonneg hCv0 hC₁) hRV)
            _ = Cv * C₁ * (K * K * (G t).inner x u u) * (K * K * (G t).inner x w w) := by
                rw [hVx, hWx]
        calc (G 0).inner x (A τ) (A τ) ≤ K * (G (τ ^ 2)).inner x (A τ) (A τ) := h1
          _ ≤ K * (Cv * C₁ * (K * K * (G t).inner x u u) * (K * K * (G t).inner x w w)) :=
                mul_le_mul_of_nonneg_left hstep hKpos.le
          _ = Cv * C₁ * K ^ 5 * ((G t).inner x u u * (G t).inner x w w) := by ring
      -- Cauchy–Schwarz, with the square-root factor absorbed into `K ^ 6`
      have h6 : Real.sqrt ((G 0).inner x (A τ) (A τ))
          ≤ Real.sqrt (Cv * C₁) * K ^ 6
            * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)) := by
        have hRHS : 0 ≤ Real.sqrt (Cv * C₁) * K ^ 6
            * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)) := by positivity
        have hsq : (Real.sqrt (Cv * C₁) * K ^ 6
            * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w))) ^ 2
            = Cv * C₁ * K ^ 12 * ((G t).inner x u u * (G t).inner x w w) := by
          simp only [mul_pow, Real.sq_sqrt (mul_nonneg hCv0 hC₁), Real.sq_sqrt huu,
            Real.sq_sqrt hww]
          ring
        have hKpow : K ^ 5 ≤ K ^ 12 := pow_le_pow_right₀ hK1 (by norm_num)
        have hmid : Cv * C₁ * K ^ 5 * ((G t).inner x u u * (G t).inner x w w)
            ≤ Cv * C₁ * K ^ 12 * ((G t).inner x u u * (G t).inner x w w) := by
          have h1 : Cv * C₁ * K ^ 5 ≤ Cv * C₁ * K ^ 12 := by
            have h := mul_le_mul_of_nonneg_left hKpow (mul_nonneg hCv0 hC₁)
            simpa [mul_assoc] using h
          exact mul_le_mul_of_nonneg_right h1 (mul_nonneg huu hww)
        calc Real.sqrt ((G 0).inner x (A τ) (A τ))
            ≤ Real.sqrt (Cv * C₁ * K ^ 5 * ((G t).inner x u u * (G t).inner x w w)) :=
              Real.sqrt_le_sqrt hA0
          _ ≤ Real.sqrt ((Real.sqrt (Cv * C₁) * K ^ 6
                * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w))) ^ 2) :=
              Real.sqrt_le_sqrt (by rw [hsq]; exact hmid)
          _ = Real.sqrt (Cv * C₁) * K ^ 6
                * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)) :=
              Real.sqrt_sq hRHS
      have h7 : |(G 0).inner x (A τ) ζ|
          ≤ (Real.sqrt (Cv * C₁) * K ^ 6
              * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)))
            * Real.sqrt ((G 0).inner x ζ ζ) :=
        le_trans (smet_cauchy' (G 0) x (A τ) ζ)
          (mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg _))
      have h8 : 0 ≤ 2 * τ := by linarith [hτ.1]
      have h9 : 2 * τ ≤ 2 * r := by linarith [hτ.2]
      have h10 : 0 ≤ (Real.sqrt (Cv * C₁) * K ^ 6
          * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)))
          * Real.sqrt ((G 0).inner x ζ ζ) := by positivity
      rw [abs_mul, abs_of_nonneg h8]
      calc |(G 0).inner x (A τ) ζ| * (2 * τ)
          ≤ ((Real.sqrt (Cv * C₁) * K ^ 6
              * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)))
            * Real.sqrt ((G 0).inner x ζ ζ)) * (2 * τ) :=
            mul_le_mul_of_nonneg_right h7 h8
        _ ≤ ((Real.sqrt (Cv * C₁) * K ^ 6
              * (Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w)))
            * Real.sqrt ((G 0).inner x ζ ζ)) * (2 * r) :=
            mul_le_mul_of_nonneg_left h9 h10
        _ = 2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
              * Real.sqrt ((G t).inner x w w) * Real.sqrt ((G 0).inner x ζ ζ) := by ring
    -- ### the variation vector at time `0` vanishes
    have hρsq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
    have hρpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    have hsqFlow : JointSmooth (fun σ : ℝ => G (σ ^ 2)) (Ioo (-(Real.sqrt T)) (Real.sqrt T)) :=
      jointSmooth_sqFlow' G hρpos hρsq.le hflow.1
    obtain ⟨A₀, hA₀, hform₀⟩ := hLV (fun σ : ℝ => G (σ ^ 2))
      (Ioo (-(Real.sqrt T)) (Real.sqrt T)) isOpen_Ioo hsqFlow 0
      ⟨by linarith [hρpos], hρpos⟩ V W hVsm hWsm x
    have hG0 : G ((0 : ℝ) ^ 2) = G 0 := by norm_num
    have hdt0 : Submission.Diff.dtMet (fun σ : ℝ => G (σ ^ 2)) 0 = fun _ _ _ => (0 : ℝ) := by
      funext y a b
      rw [Submission.Diff.dtMet]
      have hu : HasDerivWithinAt (fun s : ℝ => (G s).inner y a b)
          (-2 * ricAt (lcOf (G 0)) y a b) (Ico 0 T) 0 :=
        hflow.2 0 ⟨le_refl 0, hT⟩ y a b
      have hv : HasDerivWithinAt (fun σ : ℝ => σ ^ 2) (0 : ℝ)
          (Ioo (-(Real.sqrt T)) (Real.sqrt T)) 0 := by
        have h : HasDerivAt (fun σ : ℝ => σ ^ 2) 0 0 := by
          simpa using hasDerivAt_pow 2 (0 : ℝ)
        exact h.hasDerivWithinAt
      have hmaps : MapsTo (fun σ : ℝ => σ ^ 2)
          (Ioo (-(Real.sqrt T)) (Real.sqrt T)) (Ico 0 T) := by
        intro σ hσ
        obtain ⟨h1, h2⟩ := hσ
        refine ⟨?_, ?_⟩
        · nlinarith [sq_nonneg σ]
        · have hp1 : 0 < Real.sqrt T - σ := by linarith
          have hp2 : 0 < Real.sqrt T + σ := by linarith
          have hmul : 0 < (Real.sqrt T - σ) * (Real.sqrt T + σ) := mul_pos hp1 hp2
          nlinarith [hmul, hρsq]
      have hu' : HasDerivWithinAt (fun s : ℝ => (G s).inner y a b)
          (-2 * ricAt (lcOf (G 0)) y a b) (Ico 0 T) ((0 : ℝ) ^ 2) := by
        simpa using hu
      have hcomp : HasDerivWithinAt
          ((fun s : ℝ => (G s).inner y a b) ∘ (fun σ : ℝ => σ ^ 2))
          ((-2 * ricAt (lcOf (G 0)) y a b) * 0) (Ioo (-(Real.sqrt T)) (Real.sqrt T)) 0 :=
        HasDerivWithinAt.comp (h := fun σ : ℝ => σ ^ 2) (x := 0) hu' hv hmaps
      rw [mul_zero] at hcomp
      have hcomp' : HasDerivWithinAt (fun σ : ℝ => (G (σ ^ 2)).inner y a b)
          (0 : ℝ) (Ioo (-(Real.sqrt T)) (Real.sqrt T)) 0 := by
        simpa [Function.comp_def] using hcomp
      have hd : HasDerivAt (fun σ : ℝ => (G (σ ^ 2)).inner y a b) 0 0 :=
        hcomp'.hasDerivAt (isOpen_Ioo.mem_nhds ⟨by linarith [hρpos], hρpos⟩)
      exact hd.deriv
    have hA₀zero : ∀ ζ : TangentSpace I x, (G 0).inner x A₀ ζ = 0 := by
      intro ζ
      have hsm : CMDiff ∞ (T% (smoothExt x ζ)) := Work.Diff.GE.smoothExt_cmdiff x ζ
      have h := hform₀ (smoothExt x ζ) hsm
      rw [hG0, hdt0, Work.Diff.GE.smoothExt_apply] at h
      simp only [covDerivSym2_zero, add_zero, sub_zero, mul_zero] at h
      exact h
    -- ### the mean value argument
    have hA₀' : HasDerivAt (fun t : ℝ => lcOf ((fun σ : ℝ => G (σ ^ 2)) t) W x (V x)) A₀ 0 := by
      simpa using hA₀
    have hψ0 : ∀ ζ : TangentSpace I x,
        HasDerivAt (fun τ : ℝ => (G 0).inner x (f τ) ζ) (0 : ℝ) 0 := by
      intro ζ
      have hζ : HasDerivAt (fun _ : ℝ => ζ) (0 : TangentSpace I x) 0 :=
        hasDerivAt_const (c := ζ) (x := 0)
      have hz : Inner.inner ℝ A₀ ζ = 0 := hA₀zero ζ
      have hInner : HasDerivAt (fun σ : ℝ => Inner.inner ℝ (lcOf (G (σ ^ 2)) W x (V x)) ζ)
          (0 : ℝ) 0 := by
        have h := HasDerivAt.inner ℝ hA₀' hζ
        simpa [hz] using h
      exact hInner
    have key : ∀ ζ : TangentSpace I x,
        |(G 0).inner x (f r) ζ - (G 0).inner x (f 0) ζ|
        ≤ (2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
            * Real.sqrt ((G t).inner x w w) * Real.sqrt ((G 0).inner x ζ ζ)) * r := by
      intro ζ
      have h := abs_sub_le_of_deriv_bound
        (f := fun τ' : ℝ => (G 0).inner x (f τ') ζ)
        (f' := fun τ' : ℝ => (G 0).inner x (A τ') ζ * (2 * τ'))
        (C := 2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
            * Real.sqrt ((G t).inner x w w) * Real.sqrt ((G 0).inner x ζ ζ)) hr0 ?_ ?_
      · simpa using h
      · intro τ hτ
        rcases eq_or_lt_of_le hτ.1 with h0 | h0
        · subst h0
          have hz : (G 0).inner x (A 0) ζ * (2 * 0) = 0 := by ring
          rw [hz]
          exact (hψ0 ζ).hasDerivWithinAt
        · exact (hder ζ τ h0 hτ.2).hasDerivWithinAt
      · intro τ hτ
        rcases eq_or_lt_of_le hτ.1 with h0 | h0
        · subst h0
          have hz : (G 0).inner x (A 0) ζ * (2 * 0) = 0 := by ring
          rw [hz, abs_zero]
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · exact hbd ζ τ ⟨h0, hτ.2⟩
    -- ### conclusion
    set D : TangentSpace I x := f r - f 0 with hDdef
    have hDsub : (G 0).inner x (f r) D - (G 0).inner x (f 0) D
        = (G 0).inner x D D := by
      have h1 : (G 0).inner x (f r) D - (G 0).inner x (f 0) D
          = ((G 0).inner x (f r) - (G 0).inner x (f 0)) D := by rw [sub_apply]
      have h2 : (G 0).inner x (f r) - (G 0).inner x (f 0) = (G 0).inner x (f r - f 0) := by
        rw [map_sub]
      rw [h1, h2]
    have hD : (G 0).inner x D D
        ≤ (2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
            * Real.sqrt ((G t).inner x w w) * r)
          * Real.sqrt ((G 0).inner x D D) := by
      have h := key D
      rw [hDdef, hDsub, abs_of_nonneg (Work.Diff.GE.Sm.smet_inner_self_nonneg (G 0) x D)] at h
      nlinarith [h]
    have hsqrt0 : Real.sqrt ((G 0).inner x D D)
        ≤ 2 * r * (Real.sqrt (Cv * C₁) * K ^ 6) * Real.sqrt ((G t).inner x u u)
            * Real.sqrt ((G t).inner x w w) * r :=
      Work.Diff.GE.Sm.sqrt_le_of_le_mul_sqrt
        (Work.Diff.GE.Sm.smet_inner_self_nonneg (G 0) x D)
        (by positivity) hD
    have hcmpD : ∀ v : TangentSpace I x, (G t).inner x v v ≤ K * (G 0).inner x v v :=
      fun v => hcmp1 x t ht v
    have hK7 : Real.sqrt K * (Real.sqrt (Cv * C₁) * K ^ 6)
        ≤ K ^ 7 * Real.sqrt (max (Cv * C₁) 0) := by
      have hsqrtK : Real.sqrt K ≤ K := by
        have hKsq : K ≤ K ^ 2 := by nlinarith [hK1]
        have h := Real.sqrt_le_sqrt hKsq
        rwa [Real.sqrt_sq hKpos.le] at h
      have hsqrtCv : Real.sqrt (Cv * C₁) ≤ Real.sqrt (max (Cv * C₁) 0) :=
        Real.sqrt_le_sqrt (le_max_left _ _)
      calc Real.sqrt K * (Real.sqrt (Cv * C₁) * K ^ 6)
          = (Real.sqrt K * Real.sqrt (Cv * C₁)) * K ^ 6 := by ring
        _ ≤ (K * Real.sqrt (max (Cv * C₁) 0)) * K ^ 6 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hsqrtK hsqrtCv (Real.sqrt_nonneg _) hKpos.le) (pow_nonneg hKpos.le 6)
        _ = K ^ 7 * Real.sqrt (max (Cv * C₁) 0) := by ring
    have hrt : 2 * t * (Real.sqrt K * (Real.sqrt (Cv * C₁) * K ^ 6))
        ≤ 2 * T * K ^ 7 * Real.sqrt (max (Cv * C₁) 0) := by
      calc 2 * t * (Real.sqrt K * (Real.sqrt (Cv * C₁) * K ^ 6))
          ≤ 2 * T * (K ^ 7 * Real.sqrt (max (Cv * C₁) 0)) := by
            exact mul_le_mul (by linarith [ht.2] : 2 * t ≤ 2 * T) hK7
              (by positivity) (by linarith [ht.1] : 0 ≤ 2 * T)
        _ = 2 * T * K ^ 7 * Real.sqrt (max (Cv * C₁) 0) := by ring
    have hfin : Real.sqrt ((G t).inner x D D)
        ≤ 2 * T * K ^ 7 * Real.sqrt (max (Cv * C₁) 0)
          * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) := by
      calc Real.sqrt ((G t).inner x D D)
          ≤ Real.sqrt K * Real.sqrt ((G 0).inner x D D) :=
            sqrt_le_of_inner_le (g := G 0) (g' := G t) (x := x) (c := K) hKpos.le hcmpD D
        _ ≤ Real.sqrt K * (2 * r * (Real.sqrt (Cv * C₁) * K ^ 6)
              * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) * r) :=
            mul_le_mul_of_nonneg_left hsqrt0 (Real.sqrt_nonneg K)
        _ = 2 * t * (Real.sqrt K * (Real.sqrt (Cv * C₁) * K ^ 6))
              * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) := by
            rw [← hr2]; ring
        _ ≤ 2 * T * K ^ 7 * Real.sqrt (max (Cv * C₁) 0)
              * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hrt (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hWD : lcOf (G t) (smoothExt x w) x u - lcOf (G 0) (smoothExt x w) x u = D := by
      rw [hDdef, hfr, hf0, hWdef, hVx]
    rw [hWD]
    exact hfin
  · exfalso
    have h1 := hdRm 0 ⟨le_refl 0, hT⟩ x
    have h2 := Work.Diff.GE.Gest.dRmNormSq_nonneg (I := I) (M := M) (G 0) x
    linarith

/-- **The connection-difference estimate.**  If `G` is a smooth Ricci flow on `[0,T)` with bounded
curvature and bounded `|∇Rm|`, then the Levi-Civita connections of the metrics `G t` and `G 0`
differ by at most `C₂ |u| |w|` (in the metric `G t`). -/
theorem conn_diff_bound_of_LV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T C C₁ : ℝ) (hT : 0 < T)
    (hLV : Submission.Diff.LCVariation I M)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hdRm : ∀ t ∈ Set.Ico 0 T, ∀ x : M, Submission.Diff.dRmNormSq (G t) x ≤ C₁) :
    ∃ C₂ : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u w : TangentSpace I x,
      Real.sqrt ((G t).inner x
          (Submission.Diff.lcOf (G t) (Submission.Diff.smoothExt x w) x u
            - Submission.Diff.lcOf (G 0) (Submission.Diff.smoothExt x w) x u)
          (Submission.Diff.lcOf (G t) (Submission.Diff.smoothExt x w) x u
            - Submission.Diff.lcOf (G 0) (Submission.Diff.smoothExt x w) x u))
        ≤ C₂ * Real.sqrt ((G t).inner x u u) * Real.sqrt ((G t).inner x w w) := by
  have hLC : LCSmooth I M := Work.EXT.lcSmooth_noBoundary
  have hsum := Work.Diff.GE.Sm.covRic_eq_sum_covRm_sm (I := I) (M := M) hLC (ricTrace_sm hLC)
  exact conn_diff_bound_of_LV_aux (I := I) (M := M) hLC hLV
    (covRic_bound_of_trace (I := I) (M := M) hLC hsum)
    G T C C₁ hT hflow hbound hdRm

end Work.Diff.EXT
