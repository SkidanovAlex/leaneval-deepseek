import Mathlib
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.ENormB_eq_BPair_Qk
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.lapPow_comp_eq_varLapPow
import Submission.Work.Diff.STE.B3.VarCoef.lapPow_apply_eq_of_eventuallyEq
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.mat_eq_inv_zeta_sum
import Submission.Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_dens_comp
import Submission.Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_dens_inv_comp
import Submission.Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_tMapFun_gen
import Submission.Work.Diff.STE.B3.VarCoef.contDiffOn_mat_of_goodSet
import Submission.Work.Diff.STE.B3.MatGlob.mat_expansion
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.coeffFun_transfer_Rper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

open scoped Topology BigOperators

noncomputable section

/-- **Periodisation of a smooth real-valued function supported in the open unit cube.**

For a smooth `F` whose support lies in the open cube `(-1/2,1/2)^n` the function
`x ↦ ∑_m F (x + m)` is smooth, `1`-periodic, and agrees with `F` on the whole open cube.
(A one-line reduction of `Work.Diff.STE.periodization_contDiff_periodic` to real values.) -/
theorem periodic_of_compact {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ∃ G : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ Work.Diff.STE.Periodic1 G ∧
      ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) → G x = F x := by
  obtain ⟨hGsm, hGper, hGeq⟩ :=
    Work.Diff.STE.periodization_contDiff_periodic (ι := Fin n)
      (fun x : Fin n → ℝ => ((F x : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp hF)
      (fun x hx => hsupp (by
        intro h
        exact hx (by simp [h])))
  refine ⟨fun x => (∑' m : Fin n → ℤ,
      ((F (x + fun i => (m i : ℝ)) : ℝ) : ℂ)).re, ?_, ?_, ?_⟩
  · exact Complex.reCLM.contDiff.comp hGsm
  · intro i x
    exact congrArg Complex.re (hGper i x)
  · intro x hx
    show (∑' m : Fin n → ℤ, ((F (x + fun i => (m i : ℝ)) : ℝ) : ℂ)).re = F x
    rw [hGeq x hx, Complex.ofReal_re]

/-! ## Auxiliary lemmas -/

section Aux

/-- A point of the open unit cube, from a norm bound. -/
private lemma mem_Ioo_of_norm_lt {n : ℕ} {s : ℝ} (hs : s ≤ 1 / 2) {z : Fin n → ℝ}
    (hz : ‖z‖ < s) (j : Fin n) : z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  have hj : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j
  exact Set.mem_Ioo.mpr (abs_lt.mp (lt_of_le_of_lt hj (lt_of_lt_of_le hz hs)))

private lemma openCube_of_norm_lt {n : ℕ} {s : ℝ} (hs : s ≤ 1 / 2) {z : Fin n → ℝ}
    (hz : ‖z‖ < s) :
    z ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun j _ => mem_Ioo_of_norm_lt hs hz j

/-- The product of a smooth bump with a function which is `C^∞` on an open set containing the
topological support of the bump is globally `C^∞`.  (Real-valued version of
`Work.Diff.STE.B3.SymCalcStep8.contDiff_mul_of_contDiffOn`.) -/
private lemma contDiff_mul_of_contDiffOn_real {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {φ f : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hsub : tsupport φ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hsub hx)))
  · have h0 : ∀ᶠ y in nhds x, φ y = 0 := by
      have hc : (tsupport φ)ᶜ ∈ nhds x := (isClosed_tsupport φ).isOpen_compl.mem_nhds hx
      filter_upwards [hc] with y hy
      by_contra hne
      exact hy (subset_closure (Function.mem_support.mpr hne))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

/-- A coordinate of a smooth map into `Fin n → ℝ` is smooth. -/
private lemma contDiff_coord_apply {ι : Type*} [Fintype ι] (σ : (ι → ℝ) → (ι → ℝ))
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (a : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => σ z a) :=
  (ContinuousLinearMap.contDiff
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) a)).comp hσ

/-- The real partial derivative of a smooth real function is smooth. -/
private lemma contDiff_pdR' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdR i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => fderiv ℝ f x (Pi.single i (1 : ℝ)))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- `Periodic1`-invariance is preserved by precomposition. -/
private lemma periodic1_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    {F : (ι → ℝ) → β} {T : (ι → ℝ) → (ι → ℝ)} (hT : Work.Diff.STE.Periodic1 T) :
    Work.Diff.STE.Periodic1 (fun x => F (T x)) := by
  intro i x
  exact congrArg F (hT i x)

/-- `Periodic1`-invariance is preserved by products. -/
private lemma periodic1_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (fun x => f x * g x) := by
  intro i x
  show f (x + Pi.single i 1) * g (x + Pi.single i 1) = f x * g x
  rw [hf i x, hg i x]

/-- `Periodic1`-invariance is preserved by finite sums. -/
private lemma periodic1_finset_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    [AddCommMonoid β] {α : Type*} {s : Finset α} {f : α → (ι → ℝ) → β}
    (h : ∀ a ∈ s, Work.Diff.STE.Periodic1 (f a)) :
    Work.Diff.STE.Periodic1 (fun x => ∑ a ∈ s, f a x) := by
  intro i x
  show (∑ a ∈ s, f a (x + Pi.single i 1)) = ∑ a ∈ s, f a x
  exact Finset.sum_congr rfl (fun a ha => h a ha i x)

/-- `fderiv` of a real-valued function, coerced to `ℂ`, in an arbitrary finite dimension. -/
private lemma fderiv_ofReal_comp' {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (z v : ι → ℝ) :
    fderiv ℝ (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) z v = ((fderiv ℝ f z v : ℝ) : ℂ) := by
  by_cases hf : DifferentiableAt ℝ f z
  · have h1 : HasFDerivAt (fun y : ι → ℝ => ((f y : ℝ) : ℂ))
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ f z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
    rw [h1.fderiv]
    rfl
  · have h2 : fderiv ℝ f z = 0 := fderiv_zero_of_not_differentiableAt hf
    rw [h2]
    have h3 : ¬ DifferentiableAt ℝ (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) z := by
      intro hc
      refine hf ?_
      have h4 : DifferentiableAt ℝ (fun y : ι → ℝ => Complex.re (((f y : ℝ) : ℂ))) z :=
        Complex.reCLM.differentiableAt.comp z hc
      simpa using h4
    rw [fderiv_zero_of_not_differentiableAt h3]
    simp

/-- The partial derivative of a complexified real function. -/
private lemma pd_ofReal_comp' {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (f : (ι → ℝ) → ℝ) (z : ι → ℝ) :
    Work.Diff.STE.pd i (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) z
      = ((Work.Diff.STE.pdR i f z : ℝ) : ℂ) :=
  fderiv_ofReal_comp' f z (Pi.single i 1)

/-- The real variable-coefficient second-order operator underlying `varLap`. -/
private noncomputable def varLapR {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (g : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun x => -((∑ a, ∑ b, A a b x * Work.Diff.STE.pdR a (Work.Diff.STE.pdR b g) x)
    + ∑ a, B a x * Work.Diff.STE.pdR a g x)

private lemma varLap_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (g : (ι → ℝ) → ℝ) :
    varLap A B (fun y => ((g y : ℝ) : ℂ)) = fun x => ((varLapR A B g x : ℝ) : ℂ) := by
  funext x
  have hb : ∀ b : ι, Work.Diff.STE.pd b (fun y => ((g y : ℝ) : ℂ)) x
      = ((Work.Diff.STE.pdR b g x : ℝ) : ℂ) := fun b => pd_ofReal_comp' b g x
  have hb'' : ∀ b : ι, Work.Diff.STE.pd b (fun z => ((g z : ℝ) : ℂ))
      = fun y => ((Work.Diff.STE.pdR b g y : ℝ) : ℂ) :=
    fun b => funext (fun y => pd_ofReal_comp' b g y)
  have ha : ∀ a b : ι, Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => ((g y : ℝ) : ℂ))) x
      = ((Work.Diff.STE.pdR a (Work.Diff.STE.pdR b g) x : ℝ) : ℂ) := by
    intro a b
    rw [hb'' b]
    exact pd_ofReal_comp' a (Work.Diff.STE.pdR b g) x
  have e1 : (∑ a, ∑ b, ((A a b x : ℝ) : ℂ)
        * Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun y => ((g y : ℝ) : ℂ))) x)
      = ∑ a, ∑ b, ((A a b x * Work.Diff.STE.pdR a (Work.Diff.STE.pdR b g) x : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [ha a b, Complex.ofReal_mul]
  have e2 : (∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a (fun y => ((g y : ℝ) : ℂ)) x)
      = ∑ a, ((B a x * Work.Diff.STE.pdR a g x : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hb a, Complex.ofReal_mul]
  simp only [varLap, varLapR]
  rw [e1, e2]
  simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]

private lemma iterate_varLap_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (g : (ι → ℝ) → ℝ) :
    ∀ k : ℕ, (varLap A B)^[k] (fun y => ((g y : ℝ) : ℂ))
      = fun x => ((((varLapR A B)^[k] g) x : ℝ) : ℂ) := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact varLap_ofReal A B ((varLapR A B)^[j] g)

/-- `varLapPow` of a complexified real function is the complexification of the real operator. -/
private lemma varLapPow_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (g : (ι → ℝ) → ℝ) :
    varLapPow k A B (fun y => ((g y : ℝ) : ℂ))
      = fun x => ((((varLapR A B)^[k] g) x : ℝ) : ℂ) :=
  iterate_varLap_ofReal A B g k

/-- `varLap` only depends on the germ. -/
private lemma varLap_germ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {g g' : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (h : g =ᶠ[nhds x] g') : varLap A B g x = varLap A B g' x := by
  have h1 : ∀ i : ι, Work.Diff.STE.pd i g =ᶠ[nhds x] Work.Diff.STE.pd i g' := by
    intro i
    have hf : fderiv ℝ g =ᶠ[nhds x] fderiv ℝ g' := h.fderiv
    exact hf.fun_comp (fun T : (ι → ℝ) →L[ℝ] ℂ => T (Pi.single i 1))
  have h2 : ∀ a b : ι, Work.Diff.STE.pd a (Work.Diff.STE.pd b g)
      =ᶠ[nhds x] Work.Diff.STE.pd a (Work.Diff.STE.pd b g') := by
    intro a b
    have hf : fderiv ℝ (Work.Diff.STE.pd b g) =ᶠ[nhds x]
        fderiv ℝ (Work.Diff.STE.pd b g') := (h1 b).fderiv
    exact hf.fun_comp (fun T : (ι → ℝ) →L[ℝ] ℂ => T (Pi.single a 1))
  have e1 : (∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g) x)
      = ∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b g') x := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [(h2 a b).eq_of_nhds]
  have e2 : (∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a g x)
      = ∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a g' x := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(h1 a).eq_of_nhds]
  simp only [varLap]
  rw [e1, e2]

/-- `varLapPow` only depends on the germ (on an open set). -/
private lemma varLapPow_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → ι → (ι → ℝ) → ℝ} {B : ι → (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} (hU : IsOpen U)
    {g g' : (ι → ℝ) → ℂ} (h : ∀ x ∈ U, g x = g' x) :
    ∀ k : ℕ, ∀ x ∈ U, varLapPow k A B g x = varLapPow k A B g' x := by
  intro k
  induction k with
  | zero => intro x hx; simpa only [varLapPow, Function.iterate_zero_apply] using h x hx
  | succ j ih =>
    intro x hx
    rw [show varLapPow (j+1) A B g = varLap A B (varLapPow j A B g) from
        Function.iterate_succ_apply' (varLap A B) j g,
      show varLapPow (j+1) A B g' = varLap A B (varLapPow j A B g') from
        Function.iterate_succ_apply' (varLap A B) j g']
    refine varLap_germ (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy)

/-- The chain rule for `lapPow` under a change of variables, in the form needed here: only
`IsOpen (τ '' W)` is required (the openness of `W` is not used in the proof). -/
private theorem lapPow_comp_eq_varLapPow' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (τ σ : (ι → ℝ) → (ι → ℝ))
    (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (W : Set (ι → ℝ)) (hτW : IsOpen (τ '' W))
    (hστ : ∀ y ∈ W, σ (τ y) = y)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a))
    (hAW : ∀ y ∈ W, ∀ a b, A a b y = ∑ r, Work.Diff.STE.pdR r (fun z => σ z a) (τ y)
        * Work.Diff.STE.pdR r (fun z => σ z b) (τ y))
    (hBW : ∀ y ∈ W, ∀ a,
      B a y = ∑ r, Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σ z a)) (τ y))
    (w G : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwp : Work.Diff.STE.Periodic1 w)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hwG : ∀ z ∈ τ '' W, w z = G (σ z)) :
    ∀ y ∈ W, Work.Diff.STE.B3.SymCalcStep5.lapPow k w (τ y)
      = Work.Diff.STE.B3.VarCoef.varLapPow k A B G y := by
  have key : ∀ j : ℕ, ∀ z ∈ τ '' W, (negLap^[j] w) z = varLapPow j A B G (σ z) := by
    intro j
    induction j with
    | zero =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Function.iterate_zero_apply]
      show w (τ y) = varLapPow 0 A B G (σ (τ y))
      rw [show varLapPow 0 A B G = G from Function.iterate_zero_apply (varLap A B) G]
      exact hwG (τ y) ⟨y, hy, rfl⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hstep : (negLap^[j + 1] w) (τ y)
          = - Work.Diff.STE.B3.SymCalc.lapC (negLap^[j] w) (τ y) := by
        rw [Function.iterate_succ_apply']
        simp only [negLap]
      rw [hstep]
      have hloc : (negLap^[j] w) =ᶠ[nhds (τ y)]
          (fun z' => varLapPow j A B G (σ z')) :=
        Filter.eventually_of_mem (hτW.mem_nhds ⟨y, hy, rfl⟩) (fun z' hz' => ih z' hz')
      rw [lapC_congr hloc,
        chain_step hσ hAW hBW hστ (varLapPow j A B G) (varLapPow_contDiff hA hB j hG) y hy,
        hστ y hy]
      simp only [varLapPow, Function.iterate_succ_apply']
  intro y hy
  rw [lapPow_eq_iterate k w hw hwp (τ y), key k (τ y) ⟨y, hy, rfl⟩, hστ y hy]

/-- The cross-chart expansion of the `i`-component of `Qk`, pointwise. -/
private theorem R_Qk_pointwise_expansion'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R i (Work.Diff.STE.B3.Qk D k h) a b z
      = ∑ l : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coeffFun (I := I) (M := M) D l i a b c d z
            * Work.Diff.STE.B3.lamSection D k h l c d
                (Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i z) := by
  have hlin : D.R i (Work.Diff.STE.B3.Qk D k h) a b z
      = ∑ l : ι₀, D.R i (D.Rstar l (Work.Diff.STE.B3.lamSection D k h l)) a b z := by
    simp only [Work.Diff.STE.B3.Qk_eq_sum_Rstar, Work.Diff.STE.B3Data.R,
      Work.Diff.STE.B3Data.mat, Finset.sum_apply, ContinuousLinearMap.sum_apply, Finset.mul_sum]
  rw [hlin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Work.Diff.STE.B3.R_Rstar_expansion_pointwise_noT2]

/-- `Omega` (the set where the reconstruction genuinely contributes) is open. -/
private theorem isOpen_Omega'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (Work.Diff.STE.D.Omega (I := I) (M := M) D i j) := by
  have hsupp : IsOpen (Function.support (D.psi j)) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hlt : ‖z‖ < D.σ j := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) D hz
    have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z
      (Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D j z (le_of_lt hlt))
    have hζ : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ j (D.pt j w)) z :=
      contMDiffAt_iff_contDiffAt.mp (((D.hζsm j).contMDiffAt).comp z hpt)
    have hcont : ContinuousAt (D.psi j) z := by
      show ContinuousAt (fun w => D.χ j w * D.ζ j (D.pt j w)) z
      exact (D.hχsm j).contDiffAt.continuousAt.mul hζ.continuousAt
    exact hcont.eventually_ne hz
  have hover : IsOpen (Work.Diff.STE.B3.overlapSet (I := I) (M := M) D j i) :=
    Work.Diff.STE.B3.isOpen_overlapSet (I := I) (M := M) D (i := j) (j := i)
  have hset : Work.Diff.STE.D.Omega (I := I) (M := M) D i j
      = Function.support (D.psi j) ∩ Work.Diff.STE.B3.overlapSet (I := I) (M := M) D j i := by
    ext z
    simp only [Work.Diff.STE.D.Omega, Set.mem_setOf_eq, Set.mem_inter_iff, Function.mem_support,
      Work.Diff.STE.B3.overlapSet]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) D h1, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  rw [hset]
  exact hsupp.inter hover

/-- `ζ i ∘ pt j` is `C^∞` on any set of flat coordinates lying in the interior of the chart-`j`
target. -/
private theorem contDiffOn_zeta_pt_of_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀)
    {U : Set (Fin (Module.finrank ℝ E) → ℝ)}
    (hU : ∀ z ∈ U, Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
      interior ((extChartAt I (D.x₀ l)).target)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => D.ζ i (D.pt l z)) U := by
  intro z hz
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D l z (hU z hz)
  exact (contMDiffAt_iff_contDiffAt.mp (((D.hζsm i).contMDiffAt).comp z hpt)).contDiffWithinAt

/-- The metric pairing of two smooth fields, composed with `pt l`, is `C^∞` on any set of flat
coordinates lying in the interior of the chart-`l` target. -/
private theorem contDiffOn_pairing_pt_of_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) (p q : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    {U : Set (Fin (Module.finrank ℝ E) → ℝ)}
    (hU : ∀ z ∈ U, Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
      interior ((extChartAt I (D.x₀ l)).target)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => g₀.inner (D.pt l z) (D.e p a (D.pt l z)) (D.e q b (D.pt l z))) U := by
  intro z hz
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D l z (hU z hz)
  have hpair := Work.EXT.ONF.pairing g₀ (D.pt l z)
    ((D.hesm p a).contMDiffAt) ((D.hesm q b).contMDiffAt)
  exact (contMDiffAt_iff_contDiffAt.mp (hpair.comp z hpt)).contDiffWithinAt

end Aux

end

/-! ## The chart expansion, assembled -/

theorem R_Qk_chartExpr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀) :
    ∃ (A : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (B : ι₀ → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (ci co : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ),
      (∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b)) ∧
      (∀ i a b, Work.Diff.STE.Periodic1 (A i a b)) ∧
      (∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a)) ∧
      (∀ i a, Work.Diff.STE.Periodic1 (B i a)) ∧
      (∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d')) ∧
      (∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d')) ∧
      (∀ i a b c d, ContDiff ℝ (⊤ : ℕ∞) (co i a b c d)) ∧
      (∀ i a b c d, Work.Diff.STE.Periodic1 (co i a b c d)) ∧
      (∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)),
        (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
        ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          ((D.R l (Work.Diff.STE.B3.Qk D k h) a b z : ℝ) : ℂ) =
            ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                ((co i a b c d z : ℝ) : ℂ) *
                  Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
                    (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                      ((ci i c d c' d' w : ℝ) : ℂ) *
                        ((D.mat l h c' d' w : ℝ) : ℂ)) z)) := by
  classical
  haveI hT2 : T2Space M := Work.Diff.STE.B3.t2Space_of_B3Data (I := I) (M := M) D
  -- ## the bump on the flat coordinates of the chart `l`
  let Ul : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {z | Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target)}
      ∩ {z | ‖z‖ < 2 * D.σ l}
  have hUl : IsOpen Ul :=
    (isOpen_interior.preimage
        (Work.Diff.STE.D.contDiff_flatToE (I := I) (M := M) (D.x₀ l)).continuous).inter
      (isOpen_lt continuous_norm continuous_const)
  have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l) ⊆ Ul := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact ⟨Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z hz,
      lt_of_le_of_lt hz (by have := D.hσ l; linarith)⟩
  obtain ⟨χl, hχlsm, hχlone, hχltsup, -⟩ :=
    Work.Diff.STE.D.bump_smul_smooth
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ l)) Ul
      (isCompact_closedBall _ _) hUl hKU
      (fun _ : Fin (Module.finrank ℝ E) → ℝ => (1 : ℝ)) contDiffOn_const
  have hχltsup' : tsupport χl ⊆ {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ < 2 * D.σ l} :=
    fun z hz => (hχltsup hz).2
  have hUl_int : ∀ z ∈ Ul, Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
      interior ((extChartAt I (D.x₀ l)).target) := fun z hz => hz.1
  have hχlone' : ∀ z, ‖z‖ ≤ D.σ l → χl z = 1 :=
    fun z hz => hχlone z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
  have hσl2 : D.σ l ≤ 1 / 2 := by have := D.hσ2 l; linarith
  have h2σl : 2 * D.σ l ≤ 1 / 2 := by have := D.hσ2 l; linarith
  -- ## the per-chart bumps
  have hχbext : ∀ i : ι₀, ∃ χb : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χb ∧ (∀ z, ‖z‖ ≤ D.σ i → χb z = 1) ∧
      tsupport χb ⊆ {z | Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
          interior ((extChartAt I (D.x₀ i)).target)} ∩ {z | ‖z‖ < 2 * D.σ i} := by
    intro i
    have hUi : IsOpen ({z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
          interior ((extChartAt I (D.x₀ i)).target)} ∩ {z | ‖z‖ < 2 * D.σ i}) :=
      (isOpen_interior.preimage
          (Work.Diff.STE.D.contDiff_flatToE (I := I) (M := M) (D.x₀ i)).continuous).inter
        (isOpen_lt continuous_norm continuous_const)
    have hKi : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) ⊆
        ({z : Fin (Module.finrank ℝ E) → ℝ |
            Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
              interior ((extChartAt I (D.x₀ i)).target)} ∩ {z | ‖z‖ < 2 * D.σ i}) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact ⟨Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D i z hz,
        lt_of_le_of_lt hz (by have := D.hσ i; linarith)⟩
    obtain ⟨χb, h1, h2, h3, -⟩ :=
      Work.Diff.STE.D.bump_smul_smooth
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i))
        ({z : Fin (Module.finrank ℝ E) → ℝ |
            Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈
              interior ((extChartAt I (D.x₀ i)).target)} ∩ {z | ‖z‖ < 2 * D.σ i})
        (isCompact_closedBall _ _) hUi hKi
        (fun _ : Fin (Module.finrank ℝ E) → ℝ => (1 : ℝ)) contDiffOn_const
    exact ⟨χb, h1, fun z hz => h2 z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz), h3⟩
  choose χb hχbsm hχbone hχbtsup using hχbext
  -- ## global smooth extensions of the transition maps and of the density factors
  have hΘext : ∀ i : ι₀, ∃ G : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) G ∧ ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi l y ≠ 0 → D.ζ i (D.pt l y) ≠ 0 →
        G y = Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))) :=
    fun i => exists_contDiff_eqOn_dens_comp (I := I) (M := M) D l i
  choose Θ hΘsm hΘeq using hΘext
  have hΘinvext : ∀ i : ι₀, ∃ G : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) G ∧ ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi l y ≠ 0 → D.ζ i (D.pt l y) ≠ 0 →
        G y = (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))))⁻¹ :=
    fun i => exists_contDiff_eqOn_dens_inv_comp (I := I) (M := M) D l i
  choose Θinv hΘinvsm hΘinveq using hΘinvext
  have hτ0ext : ∀ i : ι₀, ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧ ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi l y ≠ 0 → D.ζ i (D.pt l y) ≠ 0 →
        T y = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l y :=
    fun i => exists_contDiff_eqOn_tMapFun_gen (I := I) (M := M) D i l
  choose τ₀ hτ₀sm hτ₀eq using hτ0ext
  have hσ0ext : ∀ i : ι₀, ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧ ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi i y ≠ 0 → D.ζ l (D.pt i y) ≠ 0 →
        T y = Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i y :=
    fun i => exists_contDiff_eqOn_tMapFun_gen (I := I) (M := M) D l i
  choose σ₀ hσ₀sm hσ₀eq using hσ0ext
  -- ## periodisations
  have hτext : ∀ i : ι₀, ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧ Work.Diff.STE.Periodic1 T ∧
      ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        T y = fun j => χl y * τ₀ i y j := by
    intro i
    have hcomp : ∀ j : Fin (Module.finrank ℝ E), ∃ F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) F ∧ Work.Diff.STE.Periodic1 F ∧
        ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          (∀ k : Fin (Module.finrank ℝ E), y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          F y = χl y * τ₀ i y j := by
      intro j
      refine periodic_of_compact (F := fun y => χl y * (τ₀ i y j))
        (hχlsm.mul (contDiff_coord_apply (τ₀ i) (hτ₀sm i) j)) ?_
      intro z hz
      exact openCube_of_norm_lt h2σl (hχltsup' (subset_closure (Function.mem_support.mpr
        (fun (h0 : χl z = 0) => hz (by simp only [h0, zero_mul])))))
    choose F hFsm hFper hFeq using hcomp
    exact ⟨fun y j => F j y, contDiff_pi.mpr hFsm, fun j x => funext (fun k => hFper k j x),
      fun y hy => funext (fun k => hFeq k y hy)⟩
  choose τe hτesm hτeper hτeeq using hτext
  have hσext : ∀ i : ι₀, ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧ Work.Diff.STE.Periodic1 T ∧
      ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        T y = fun j => χb i y * σ₀ i y j := by
    intro i
    have hcomp : ∀ j : Fin (Module.finrank ℝ E), ∃ F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) F ∧ Work.Diff.STE.Periodic1 F ∧
        ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          (∀ k : Fin (Module.finrank ℝ E), y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          F y = χb i y * σ₀ i y j := by
      intro j
      refine periodic_of_compact (F := fun y => χb i y * (σ₀ i y j))
        ((hχbsm i).mul (contDiff_coord_apply (σ₀ i) (hσ₀sm i) j)) ?_
      intro z hz
      exact openCube_of_norm_lt (by have := D.hσ2 i; linarith)
        ((hχbtsup i (subset_closure (Function.mem_support.mpr
          (fun (h0 : χb i z = 0) => hz (by simp only [h0, zero_mul]))))).2)
    choose F hFsm hFper hFeq using hcomp
    exact ⟨fun y j => F j y, contDiff_pi.mpr hFsm, fun j x => funext (fun k => hFper k j x),
      fun y hy => funext (fun k => hFeq k y hy)⟩
  choose σe hσesm hσeper hσeeq using hσext
  -- ## the coefficients `A` and `B`
  let A : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun i a b y =>
    ∑ r : Fin (Module.finrank ℝ E), Work.Diff.STE.pdR r (fun z => σe i z a) (τe i y)
      * Work.Diff.STE.pdR r (fun z => σe i z b) (τe i y)
  let B : ι₀ → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun i a y =>
    ∑ r : Fin (Module.finrank ℝ E),
      Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σe i z a)) (τe i y)
  have hAsm : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b) := by
    intro i a b
    refine ContDiff.sum fun r _ => ?_
    exact ((contDiff_pdR' (fun z => σe i z a) (contDiff_coord_apply (σe i) (hσesm i) a) r).comp
        (hτesm i)).mul
      ((contDiff_pdR' (fun z => σe i z b) (contDiff_coord_apply (σe i) (hσesm i) b) r).comp
        (hτesm i))
  have hAper : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b) := by
    intro i a b
    refine periodic1_finset_sum (s := Finset.univ) (f := fun r y =>
      Work.Diff.STE.pdR r (fun z => σe i z a) (τe i y)
        * Work.Diff.STE.pdR r (fun z => σe i z b) (τe i y)) fun r _ => ?_
    exact periodic1_mul
      (periodic1_comp (T := τe i)
        (F := fun z => Work.Diff.STE.pdR r (fun z' => σe i z' a) z) (hτeper i))
      (periodic1_comp (T := τe i)
        (F := fun z => Work.Diff.STE.pdR r (fun z' => σe i z' b) z) (hτeper i))
  have hBsm : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a) := by
    intro i a
    refine ContDiff.sum fun r _ => ?_
    exact (contDiff_pdR' (Work.Diff.STE.pdR r (fun z => σe i z a))
      (contDiff_pdR' (fun z => σe i z a) (contDiff_coord_apply (σe i) (hσesm i) a) r) r).comp
      (hτesm i)
  have hBper : ∀ i a, Work.Diff.STE.Periodic1 (B i a) := by
    intro i a
    refine periodic1_finset_sum (s := Finset.univ) (f := fun r y =>
      Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σe i z a)) (τe i y)) fun r _ => ?_
    exact periodic1_comp (T := τe i)
      (F := fun z => Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z' => σe i z' a)) z) (hτeper i)
  -- ## the coefficient `ci`
  have hci_ext : ∀ (i : ι₀) (c d c' d' : Fin (Module.finrank ℝ E)),
      ∃ F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      Work.Diff.STE.Periodic1 F ∧
      ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        (∀ j, y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        F y = χl y * ((χl y * D.ζ i (D.pt l y)) * (χl y * D.χ i (τ₀ i y))
          * (χl y * Θ i y)
          * (χl y * g₀.inner (D.pt l y) (D.e i c (D.pt l y)) (D.e l c' (D.pt l y)))
          * (χl y * g₀.inner (D.pt l y) (D.e i d (D.pt l y)) (D.e l d' (D.pt l y)))) := by
    intro i c d c' d'
    refine periodic_of_compact (F := fun y => χl y * ((χl y * D.ζ i (D.pt l y))
        * (χl y * D.χ i (τ₀ i y)) * (χl y * Θ i y)
        * (χl y * g₀.inner (D.pt l y) (D.e i c (D.pt l y)) (D.e l c' (D.pt l y)))
        * (χl y * g₀.inner (D.pt l y) (D.e i d (D.pt l y)) (D.e l d' (D.pt l y))))) ?_ ?_
    · have hA1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * D.ζ i (D.pt l y)) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_zeta_pt_of_interior (I := I) (M := M) D l i hUl_int) hχltsup
      have hA2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * D.χ i (τ₀ i y)) :=
        hχlsm.mul ((D.hχsm i).comp (hτ₀sm i))
      have hA3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * Θ i y) := hχlsm.mul (hΘsm i)
      have hA4 : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => χl y * g₀.inner (D.pt l y) (D.e i c (D.pt l y)) (D.e l c' (D.pt l y))) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_pairing_pt_of_interior (I := I) (M := M) D l i l c c' hUl_int) hχltsup
      have hA5 : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => χl y * g₀.inner (D.pt l y) (D.e i d (D.pt l y)) (D.e l d' (D.pt l y))) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_pairing_pt_of_interior (I := I) (M := M) D l i l d d' hUl_int) hχltsup
      exact hχlsm.mul ((((hA1.mul hA2).mul hA3).mul hA4).mul hA5)
    · intro z hz
      exact openCube_of_norm_lt h2σl (hχltsup' (subset_closure (Function.mem_support.mpr
        (fun (h0 : χl z = 0) => hz (by simp only [h0, zero_mul, mul_zero])))))
  choose ci hcism hciper hcieq using hci_ext
  -- ## the coefficient `co`
  have hco_ext : ∀ (i : ι₀) (a b c d : Fin (Module.finrank ℝ E)),
      ∃ F : (Fin (Module.finrank ℝ E) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      Work.Diff.STE.Periodic1 F ∧
      ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        (∀ j, y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        F y = χl y * ((χl y * D.ζ i (D.pt l y)) * (χl y * D.χ i (τ₀ i y))
          * (χl y * Θinv i y)
          * (χl y * g₀.inner (D.pt l y) (D.e l a (D.pt l y)) (D.e i c (D.pt l y)))
          * (χl y * g₀.inner (D.pt l y) (D.e l b (D.pt l y)) (D.e i d (D.pt l y)))) := by
    intro i a b c d
    refine periodic_of_compact (F := fun y => χl y * ((χl y * D.ζ i (D.pt l y))
        * (χl y * D.χ i (τ₀ i y)) * (χl y * Θinv i y)
        * (χl y * g₀.inner (D.pt l y) (D.e l a (D.pt l y)) (D.e i c (D.pt l y)))
        * (χl y * g₀.inner (D.pt l y) (D.e l b (D.pt l y)) (D.e i d (D.pt l y))))) ?_ ?_
    · have hA1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * D.ζ i (D.pt l y)) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_zeta_pt_of_interior (I := I) (M := M) D l i hUl_int) hχltsup
      have hA2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * D.χ i (τ₀ i y)) :=
        hχlsm.mul ((D.hχsm i).comp (hτ₀sm i))
      have hA3 : ContDiff ℝ (⊤ : ℕ∞) (fun y => χl y * Θinv i y) := hχlsm.mul (hΘinvsm i)
      have hA4 : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => χl y * g₀.inner (D.pt l y) (D.e l a (D.pt l y)) (D.e i c (D.pt l y))) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_pairing_pt_of_interior (I := I) (M := M) D l l i a c hUl_int) hχltsup
      have hA5 : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => χl y * g₀.inner (D.pt l y) (D.e l b (D.pt l y)) (D.e i d (D.pt l y))) :=
        contDiff_mul_of_contDiffOn_real hUl hχlsm
          (contDiffOn_pairing_pt_of_interior (I := I) (M := M) D l l i b d hUl_int) hχltsup
      exact hχlsm.mul ((((hA1.mul hA2).mul hA3).mul hA4).mul hA5)
    · intro z hz
      exact openCube_of_norm_lt h2σl (hχltsup' (subset_closure (Function.mem_support.mpr
        (fun (h0 : χl z = 0) => hz (by simp only [h0, zero_mul, mul_zero])))))
  choose co hcosm hcoper hcoeq using hco_ext
  refine ⟨A, B, ci, co, hAsm, hAper, hBsm, hBper, hcism, hciper, hcosm, hcoper, ?_⟩
  intro h a b hsm z
  have hsm2 : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R j h a' b') := fun j a' b' => hsm j a' b'
  have hpoint : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i l a b c d z
          * Work.Diff.STE.B3.lamSection D k h i c d
            (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z) : ℝ) : ℂ)
        = ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) *
          (((co i a b c d z : ℝ) : ℂ) *
            varLapPow k (A i) (B i)
              (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ)) z) := by
    intro i c d
    by_cases hψ : D.psi l z = 0
    · have hcf : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i l a b c d z = 0 := by
        simp only [Work.Diff.STE.D.coeffFun, hψ, zero_mul]
      simp only [hcf, hψ, zero_mul, Complex.ofReal_zero]
    · by_cases hζ : D.ζ i (D.pt l z) = 0
      · have hltl : ‖z‖ < D.σ l := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) D hψ
        have hcz : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
          fun j => mem_Ioo_of_norm_lt hσl2 hltl j
        have hco0 : co i a b c d z = 0 := by
          rw [hcoeq i a b c d z hcz]
          simp only [hζ, mul_zero, zero_mul]
        have hcf : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i l a b c d z = 0 := by
          simp only [Work.Diff.STE.D.coeffFun, hζ, mul_zero, zero_mul]
        simp only [hcf, hco0, zero_mul, mul_zero, Complex.ofReal_zero]
      · have hltl : ‖z‖ < D.σ l := Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) D hψ
        have hcz : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
          fun j => mem_Ioo_of_norm_lt hσl2 hltl j
        have hχlz : χl z = 1 := hχlone' z (le_of_lt hltl)
        have hζl : D.ζ l (D.pt l z) ≠ 0 :=
          fun h0 => hψ (by simp only [Work.Diff.STE.B3Data.psi, h0, mul_zero])
        have hsrc_l : D.pt l z ∈ (extChartAt I (D.x₀ l)).source := (D.hζsupp l _ hζl).1
        have hτ₀z : τ₀ i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z :=
          hτ₀eq i z hψ hζ
        have htau : τe i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z := by
          rw [hτeeq i z hcz]
          funext j
          rw [hχlz, one_mul, hτ₀z]
        set z₀ : Fin (Module.finrank ℝ E) → ℝ := τe i z with hz₀def
        have hz₀τ : z₀ = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z :=
          hz₀def.trans htau
        have hτz : τe i z = z₀ := hz₀def.symm
        have hz₀_norm : ‖z₀‖ < D.σ i := by
          rw [hz₀τ]; exact (D.hζsupp i _ hζ).2
        have hpt_i_z₀ : D.pt i z₀ = D.pt l z := by
          rw [hz₀τ]; exact D.pt_coord i (D.hζsupp i _ hζ).1
        have hχi_z₀ : D.χ i z₀ = 1 := D.hχ1 i z₀ (le_of_lt hz₀_norm)
        have hpsi_i_z₀ : D.psi i z₀ = D.ζ i (D.pt l z) := by
          rw [Work.Diff.STE.B3Data.psi, hχi_z₀, hpt_i_z₀, one_mul]
        have hz₀_Om : z₀ ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D l i :=
          ⟨by rw [hpsi_i_z₀]; exact hζ, by rw [hpt_i_z₀]; exact hζl⟩
        have hszi : D.σ i ≤ 1 / 2 := by have := D.hσ2 i; linarith
        have hσez₀ : σe i z₀ = z := by
          rw [hσeeq i z₀ (fun j => mem_Ioo_of_norm_lt hszi hz₀_norm j),
            hχbone i z₀ (le_of_lt hz₀_norm)]
          funext j
          rw [one_mul]
          exact (congrFun (hσ₀eq i z₀ hz₀_Om.1 hz₀_Om.2) j).trans (by
            show Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i z₀) j = z j
            rw [hpt_i_z₀]
            exact congrFun (D.coord_pt l (by have := D.hσ l; linarith)) j)
        have hz_good : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D l l := by
          refine ⟨?_, hsrc_l, ?_⟩
          · exact Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z
              (le_of_lt hltl)
          · rw [show (extChartAt I (D.x₀ l)) (D.pt l z)
                  = Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
                from (extChartAt I (D.x₀ l)).right_inv (interior_subset
                  (Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z
                    (le_of_lt hltl)))]
            exact Work.Diff.STE.D.flatToE_mem_interior_target (I := I) (M := M) D l z
              (le_of_lt hltl)
        have hgood_open : IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D l l) :=
          Work.Diff.STE.D.isOpen_goodSet (I := I) (M := M) D l l
        obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hgood_open.mem_nhds hz_good)
        have hβext : ∀ c' d' : Fin (Module.finrank ℝ E),
            ∃ β : (Fin (Module.finrank ℝ E) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧
              (∀ w, w ∈ Metric.closedBall z (ε / 2) → β w = 1) ∧
              tsupport β ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D l l := by
          intro c' d'
          obtain ⟨β, h1, h2, h3, -⟩ := Work.Diff.STE.D.bump_smul_smooth
            (Metric.closedBall z (ε / 2)) (Work.Diff.STE.D.goodSet (I := I) (M := M) D l l)
            (isCompact_closedBall _ _) hgood_open
            (fun w hw => hεsub (Metric.closedBall_subset_ball (by linarith) hw))
            (fun w => D.mat l h c' d' w)
            (contDiffOn_mat_of_goodSet (I := I) (M := M) D l h c' d' hsm2)
          exact ⟨β, h1, h2, h3⟩
        choose β hβsm hβone hβtsup using hβext
        let φR : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun w =>
          ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
            ci i c d c' d' w * (β c' d' w * D.mat l h c' d' w)
        let Φ : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun w => ((φR w : ℝ) : ℂ)
        let G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun w =>
          ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
            ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ)
        have hG_real : G = fun w => ((∑ c' : Fin (Module.finrank ℝ E),
            ∑ d' : Fin (Module.finrank ℝ E), ci i c d c' d' w * D.mat l h c' d' w : ℝ) : ℂ) := by
          funext w
          show (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ))
            = ((∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ci i c d c' d' w * D.mat l h c' d' w : ℝ) : ℂ)
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [Complex.ofReal_mul]
        have hφRsm : ContDiff ℝ (⊤ : ℕ∞) φR := by
          show ContDiff ℝ (⊤ : ℕ∞) (fun w => ∑ c' : Fin (Module.finrank ℝ E),
            ∑ d' : Fin (Module.finrank ℝ E),
              ci i c d c' d' w * (β c' d' w * D.mat l h c' d' w))
          refine ContDiff.sum fun c' _ => ContDiff.sum fun d' _ => ?_
          exact (hcism i c d c' d').mul (contDiff_mul_of_contDiffOn_real hgood_open
            (hβsm c' d') (contDiffOn_mat_of_goodSet (I := I) (M := M) D l h c' d' hsm2)
            (hβtsup c' d'))
        have hΦsm : ContDiff ℝ (⊤ : ℕ∞) Φ := Complex.ofRealCLM.contDiff.comp hφRsm
        have hΦeq : Φ =ᶠ[nhds z] G := by
          have hmem : Metric.closedBall z (ε / 2) ∈ nhds z :=
            Metric.closedBall_mem_nhds z (by linarith)
          filter_upwards [hmem] with w hw
          have hφw : φR w = ∑ c' : Fin (Module.finrank ℝ E),
              ∑ d' : Fin (Module.finrank ℝ E), ci i c d c' d' w * D.mat l h c' d' w := by
            show (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ci i c d c' d' w * (β c' d' w * D.mat l h c' d' w)) = _
            refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ => ?_
            rw [hβone c' d' w hw, one_mul]
          show ((φR w : ℝ) : ℂ) = G w
          rw [hG_real, hφw]
        have hΦreal : varLapPow k (A i) (B i) Φ z
            = ((varLapPow k (A i) (B i) Φ z).re : ℂ) := by
          rw [show varLapPow k (A i) (B i) Φ
                = varLapPow k (A i) (B i) (fun y => ((φR y : ℝ) : ℂ)) from rfl,
            varLapPow_ofReal k (A i) (B i) φR]
          simp only [Complex.ofReal_re]
        obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hΦeq
        have hΓ : varLapPow k (A i) (B i) G z = varLapPow k (A i) (B i) Φ z :=
          varLapPow_congr (A := A i) (B := B i) (U := Metric.ball z ρ) (g := G) (g' := Φ)
            Metric.isOpen_ball (fun x hx => (hρsub hx).symm) k z (Metric.mem_ball_self hρpos)
        obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ : ℝ, 0 < δ ∧ Metric.ball z₀ δ ⊆
            (Work.Diff.STE.D.Omega (I := I) (M := M) D l i)
            ∩ (Work.Diff.STE.B3.sigmaBall (I := I) (M := M) D i)
            ∩ (σe i ⁻¹' (Work.Diff.STE.D.Omega (I := I) (M := M) D i l))
            ∩ (σe i ⁻¹' (Metric.ball z ρ)) := by
          have h1 : Work.Diff.STE.D.Omega (I := I) (M := M) D l i ∈ nhds z₀ :=
            (isOpen_Omega' (I := I) (M := M) D l i).mem_nhds hz₀_Om
          have h2 : Work.Diff.STE.B3.sigmaBall (I := I) (M := M) D i ∈ nhds z₀ :=
            (Work.Diff.STE.B3.isOpen_sigmaBall (I := I) (M := M) D (i := i)).mem_nhds hz₀_norm
          have h3 : σe i ⁻¹' (Work.Diff.STE.D.Omega (I := I) (M := M) D i l) ∈ nhds z₀ := by
            refine (hσesm i).continuous.continuousAt.preimage_mem_nhds ?_
            rw [hσez₀]
            exact (isOpen_Omega' (I := I) (M := M) D i l).mem_nhds ⟨hψ, hζ⟩
          have h4 : σe i ⁻¹' (Metric.ball z ρ) ∈ nhds z₀ := by
            refine (hσesm i).continuous.continuousAt.preimage_mem_nhds ?_
            rw [hσez₀]
            exact Metric.ball_mem_nhds z hρpos
          exact Metric.mem_nhds_iff.mp
            (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem h1 h2) h3) h4)
        let Bd : Set (Fin (Module.finrank ℝ E) → ℝ) := Metric.ball z₀ δ
        have hBz₀ : z₀ ∈ Bd := Metric.mem_ball_self hδpos
        have hframe : ∀ u ∈ Bd, D.Rper i h c d u = G (σe i u) := by
          intro u hu
          have huOm : u ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D l i := (hδsub hu).1.1.1
          have huSig : ‖u‖ < D.σ i := (hδsub hu).1.1.2
          have hcubeu : ∀ j, u j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
            fun j => mem_Ioo_of_norm_lt hszi huSig j
          have hζlu : D.ζ l (D.pt i u) ≠ 0 := huOm.2
          have hsrc : D.pt i u ∈ (extChartAt I (D.x₀ l)).source := (D.hζsupp l _ hζlu).1
          have hnlu : ‖Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)‖ < D.σ l :=
            (D.hζsupp l _ hζlu).2
          have hv_cube : ∀ j, Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u) j
              ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun j => mem_Ioo_of_norm_lt hσl2 hnlu j
          have hσuT : σe i u = Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i u := by
            rw [hσeeq i u hcubeu]
            funext j
            rw [hχbone i u (le_of_lt huSig), one_mul, hσ₀eq i u huOm.1 huOm.2]
          have hσu : σe i u = Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u) := hσuT
          have hψi : D.psi i u = D.ζ i (D.pt i u) := by
            rw [Work.Diff.STE.B3Data.psi, D.hχ1 i u (le_of_lt huSig), one_mul]
          have hcu : Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt i u) = u :=
            D.coord_pt i (le_trans (le_of_lt huSig) (by have := D.hσ i; linarith))
          have hχlv : χl (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) = 1 :=
            hχlone' _ (le_of_lt hnlu)
          have hptlv : D.pt l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u))
              = D.pt i u := D.pt_coord l hsrc
          have hpsilv : D.psi l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) ≠ 0 := by
            rw [Work.Diff.STE.B3Data.psi, D.hχ1 l _ (le_of_lt hnlu), one_mul, hptlv]
            exact hζlu
          have hζilv : D.ζ i (D.pt l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u))) ≠ 0 := by
            rw [hptlv, ← hψi]
            exact huOm.1
          have hτ0v : τ₀ i (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) = u := by
            rw [hτ₀eq i _ hpsilv hζilv]
            show Work.Diff.STE.coord (I := I) (D.x₀ i)
                (D.pt l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u))) = u
            rw [hptlv]
            exact hcu
          have hci : ∀ c' d' : Fin (Module.finrank ℝ E),
              ci i c d c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u))
                = D.psi i u * Real.sqrt (D.dens i u) *
                  (g₀.inner (D.pt i u) (D.e i c (D.pt i u)) (D.e l c' (D.pt i u))) *
                  (g₀.inner (D.pt i u) (D.e i d (D.pt i u)) (D.e l d' (D.pt i u))) := by
            intro c' d'
            rw [hcieq i c d c' d' _ hv_cube]
            rw [hχlv]
            simp only [one_mul]
            rw [hΘeq i _ hpsilv hζilv, hτ0v, D.hχ1 i u (le_of_lt huSig), hptlv, hψi, hcu]
            ring
          rw [Work.Diff.STE.B3.Rper_eq_of_mem_cube (I := I) (M := M) D h i c d hcubeu]
          show (((D.psi i u * Real.sqrt (D.dens i u) * D.mat i h c d u : ℝ)) : ℂ) = G (σe i u)
          rw [hσu]
          show (((D.psi i u * Real.sqrt (D.dens i u) * D.mat i h c d u : ℝ)) : ℂ)
            = (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) : ℝ) : ℂ) *
                ((D.mat l h c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) : ℝ) : ℂ))
          rw [Work.Diff.STE.B3.MatGlob.mat_expansion (I := I) (M := M) D l i h c d u hsrc
            (le_trans (le_of_lt hnlu) (by have := D.hσ l; linarith))]
          have hreal : D.psi i u * Real.sqrt (D.dens i u) *
              (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                (g₀.inner (D.pt i u) (D.e i c (D.pt i u)) (D.e l c' (D.pt i u))) *
                (g₀.inner (D.pt i u) (D.e i d (D.pt i u)) (D.e l d' (D.pt i u))) *
                D.mat l h c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)))
              = ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ci i c d c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) *
                D.mat l h c' d' (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d' _ => ?_
            rw [hci c' d']
            ring
          rw [hreal, Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [Complex.ofReal_mul]
        have hτσ : ∀ u ∈ Bd, τe i (σe i u) = u := by
          intro u hu
          have huOm : u ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D l i := (hδsub hu).1.1.1
          have huSig : ‖u‖ < D.σ i := (hδsub hu).1.1.2
          have huOmil : σe i u ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D i l := (hδsub hu).1.2
          have hcubeu : ∀ j, u j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
            fun j => mem_Ioo_of_norm_lt hszi huSig j
          have hζlu : D.ζ l (D.pt i u) ≠ 0 := huOm.2
          have hsrc : D.pt i u ∈ (extChartAt I (D.x₀ l)).source := (D.hζsupp l _ hζlu).1
          have hnlu : ‖Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)‖ < D.σ l :=
            (D.hζsupp l _ hζlu).2
          have hσuT : σe i u = Work.Diff.STE.D.tMapFun (I := I) (M := M) D l i u := by
            rw [hσeeq i u hcubeu]
            funext j
            rw [hχbone i u (le_of_lt huSig), one_mul, hσ₀eq i u huOm.1 huOm.2]
          have hσu : σe i u = Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u) := hσuT
          rw [hσu]
          have hv_cube : ∀ j, Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u) j
              ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun j => mem_Ioo_of_norm_lt hσl2 hnlu j
          rw [hτeeq i _ hv_cube]
          funext j
          rw [hχlone' _ (le_of_lt hnlu), one_mul]
          have hyOmil : Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u)
              ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D i l := by
            rw [← hσu]; exact huOmil
          rw [hτ₀eq i _ hyOmil.1 hyOmil.2]
          show Work.Diff.STE.coord (I := I) (D.x₀ i)
              (D.pt l (Work.Diff.STE.coord (I := I) (D.x₀ l) (D.pt i u))) j = u j
          rw [D.pt_coord l hsrc]
          exact congrFun (D.coord_pt i (le_trans (le_of_lt huSig) (by have := D.hσ i; linarith))) j
        have hτσ' : ∀ y ∈ σe i '' Bd, σe i (τe i y) = y := by
          rintro y ⟨u, hu, rfl⟩
          rw [hτσ u hu]
        have himg : τe i '' (σe i '' Bd) = Bd := by
          rw [Set.image_image]
          rw [show (fun x => τe i (σe i x)) '' Bd = id '' Bd from
            Set.image_congr (fun u hu => hτσ u hu)]
          exact Set.image_id Bd
        have hW : IsOpen (τe i '' (σe i '' Bd)) := by
          rw [himg]; exact Metric.isOpen_ball
        have hAW : ∀ y ∈ σe i '' Bd, ∀ a b, A i a b y = ∑ r : Fin (Module.finrank ℝ E),
            Work.Diff.STE.pdR r (fun z => σe i z a) (τe i y)
              * Work.Diff.STE.pdR r (fun z => σe i z b) (τe i y) := fun y _ a b => rfl
        have hBW : ∀ y ∈ σe i '' Bd, ∀ a, B i a y = ∑ r : Fin (Module.finrank ℝ E),
            Work.Diff.STE.pdR r (Work.Diff.STE.pdR r (fun z => σe i z a)) (τe i y) :=
          fun y _ a => rfl
        have hwsm : ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h c d) :=
          (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h c d
            (hsm2 i c d)).1
        have hwper : Work.Diff.STE.Periodic1 (D.Rper i h c d) :=
          (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h c d
            (hsm2 i c d)).2
        have hwG : ∀ z' ∈ τe i '' (σe i '' Bd), D.Rper i h c d z' = Φ (σe i z') := by
          intro z' hz'
          have hz'B : z' ∈ Bd := by rwa [himg] at hz'
          rw [hframe z' hz'B, hρsub ((hδsub hz'B).2)]
        have hcr := lapPow_comp_eq_varLapPow' (ι := Fin (Module.finrank ℝ E)) k (τe i) (σe i)
          (hτesm i) (hσesm i) (σe i '' Bd) hW hτσ' (A i) (B i) (hAsm i) (hBsm i) hAW hBW
          (D.Rper i h c d) Φ hwsm hwper hΦsm hwG
        have hzW : z ∈ σe i '' Bd := ⟨z₀, hBz₀, hσez₀⟩
        have hchain : Work.Diff.STE.B3.SymCalcStep5.lapPow k (D.Rper i h c d) (τe i z)
            = varLapPow k (A i) (B i) Φ z := hcr z hzW
        have hlam : Work.Diff.STE.B3.lamSection D k h i c d
              (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z)
            = (varLapPow k (A i) (B i) Φ z).re := by
          rw [show Work.Diff.STE.B3.lamSection D k h i c d
                (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z)
              = (Work.Diff.STE.B3.SymCalcStep5.lapPow k (D.Rper i h c d)
                (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z)).re from rfl]
          rw [← htau, hchain]
        have hcoef : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i l a b c d z
            = (D.psi l z * Real.sqrt (D.dens l z)) * co i a b c d z := by
          rw [hcoeq i a b c d z hcz]
          simp only [Work.Diff.STE.D.coeffFun, hχlz, one_mul, hΘinveq i z hψ hζ, hτ₀z]
          rw [show Work.Diff.STE.D.tMapFun (I := I) (M := M) D i l z
                = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z) from rfl]
          ring
        rw [show (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ)) = G from rfl]
        rw [Complex.ofReal_mul, hcoef, Complex.ofReal_mul, hlam, hΦreal.symm, hΓ.symm]
        ring
  rw [R_Qk_pointwise_expansion' (I := I) (M := M) D k h l a b z, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact hpoint i c d


end Work.Diff.STE.B3.VarCoef
