import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.EXT.frobSqN_frame_indep
import Submission.Work.Diff.EXT.sum_fin_add_four

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 2000000

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

section Tensor

local macro "Tf" : term => `((y : M) → TangentSpace I y)

/-- The covariant derivative `∇_{v₀} X` of the field `X` in the direction of the field `v₀`,
as a field. -/
noncomputable def dirF (g : SMet I M) (X v0 : Tf) : Tf := fun y => lcOf g X y (v0 y)

/-- **The uniform recursion.**  `ckt g k F` is the `k`-th covariant derivative `∇^k Rm` of the
curvature evaluated on the tuple of fields `F : Fin (k+4) → Tf`: the first `k` entries are the
differentiation slots, the last four the curvature slots.  The recursion is the Leibniz rule
`(∇_{v₀}T)(args) = v₀(T args) − ∑_slots T (args with the slot replaced by ∇_{v₀}(slot))`. -/
noncomputable def ckt (g : SMet I M) : ∀ k : ℕ, (Fin (k + 4) → Tf) → M → ℝ
  | 0, F => fun y => rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
  | k + 1, F => fun y =>
      mvfderiv I (ckt g k (fun i : Fin (k + 4) => F i.succ)) y (F 0 y)
        - ∑ s : Fin (k + 4), ckt g k (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))) y

/-- The recursion, as an equality of functions. -/
lemma ckt_succ (g : SMet I M) (k : ℕ) (F : Fin (k + 5) → Tf) :
    ckt g (k + 1) F
      = (fun y : M => (mvfderiv I (ckt g k (fun i : Fin (k + 4) => F i.succ)) y) (F 0 y))
        - ∑ s : Fin (k + 4), ckt g k (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))) := by
  funext y
  simp only [ckt, Finset.sum_apply, Pi.sub_apply]

/-- A field is smooth. -/
def SmoothF (X : Tf) : Prop := CMDiff ∞ (T% X)

lemma smoothF_smul {f : M → ℝ} {X : Tf} (hf : CMDiff ∞ f) (hX : SmoothF X) :
    SmoothF (f • X) := hf.smul_section hX

lemma smoothF_add {X Y : Tf} (hX : SmoothF X) (hY : SmoothF Y) : SmoothF (X + Y) :=
  hX.add_section hY



/-! ## Updating the `succ`-shifted tuple -/

lemma update_comp_succ {k : ℕ} (F : Fin (k + 5) → Tf) (j : Fin (k + 4)) (W : Tf) :
    (fun i : Fin (k + 4) => (Function.update F j.succ W) i.succ)
      = Function.update (fun i : Fin (k + 4) => F i.succ) j W := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · have h' : i.succ ≠ j.succ := fun hh => h (Fin.succ_inj.mp hh)
    rw [Function.update_of_ne h' W F,
      Function.update_of_ne h W (fun i : Fin (k + 4) => F i.succ)]

lemma update_zero_comp_succ {k : ℕ} (F : Fin (k + 5) → Tf) (W : Tf) :
    (fun i : Fin (k + 4) => (Function.update F 0 W) i.succ)
      = fun i : Fin (k + 4) => F i.succ := by
  funext i
  rw [Function.update_of_ne (Fin.succ_ne_zero i) W F]

/-! ## The operation `dirF` -/

/-- `dirF` is additive and homogeneous in the *direction*. -/
lemma dirF_add_dir (g : SMet I M) (X : Tf) (X₁ X₂ : Tf) (f₁ f₂ : M → ℝ) :
    dirF g X (f₁ • X₁ + f₂ • X₂) = f₁ • dirF g X X₁ + f₂ • dirF g X X₂ := by
  funext y
  simp only [dirF, Pi.add_apply, Pi.smul_apply', map_add, map_smul]

/-- The Leibniz rule for `dirF` in the *field* argument. -/
lemma dirF_leibniz (g : SMet I M) {X₁ X₂ : Tf} {f₁ f₂ : M → ℝ} {v0 : Tf}
    (hX₁ : SmoothF X₁) (hX₂ : SmoothF X₂) (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dirF g (f₁ • X₁ + f₂ • X₂) v0
      = f₁ • dirF g X₁ v0 + (fun y => (mvfderiv I f₁ y) (v0 y)) • X₁
        + f₂ • dirF g X₂ v0 + (fun y => (mvfderiv I f₂ y) (v0 y)) • X₂ := by
  funext y
  have h1 : MDiffAt (T% (f₁ • X₁)) y := (hf₁.smul_section hX₁).mdifferentiableAt (by simp)
  have h2 : MDiffAt (T% (f₂ • X₂)) y := (hf₂.smul_section hX₂).mdifferentiableAt (by simp)
  have h3 : MDiffAt (T% X₁) y := hX₁.mdifferentiableAt (by simp)
  have h4 : MDiffAt (T% X₂) y := hX₂.mdifferentiableAt (by simp)
  have h5 : MDiffAt f₁ y := hf₁.mdifferentiableAt (by simp)
  have h6 : MDiffAt f₂ y := hf₂.mdifferentiableAt (by simp)
  have hadd := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ)
    (σ := f₁ • X₁) (σ' := f₂ • X₂) h1 h2
  have hl1 := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := X₁) (g := f₁) h3 h5
  have hl2 := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := X₂) (g := f₂) h4 h6
  simp only [dirF, Pi.add_apply, Pi.smul_apply']
  rw [hadd, hl1, hl2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, Pi.add_apply,
    Pi.smul_apply']
  abel

/-- `dirF` of a smooth field in a smooth direction is smooth. -/
lemma dirF_smooth (hLC : LCSmooth I M) (g : SMet I M) {X v0 : Tf}
    (hX : SmoothF X) (hv0 : SmoothF v0) : SmoothF (dirF g X v0) := by
  obtain ⟨hcov⟩ := (hLC g).1
  exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (lcOf g) hcov hX hv0

/-- `rmP` depends only on the *values* of its four field arguments at the base point. -/
lemma rmP_congr_apply (hLC : LCSmooth I M) (g : SMet I M) (y : M)
    {A A' B B' C C' D D' : Tf}
    (hA : SmoothF A) (hA' : SmoothF A') (hB : SmoothF B) (hB' : SmoothF B')
    (hC : SmoothF C) (hC' : SmoothF C') (hD : SmoothF D) (hD' : SmoothF D')
    (hAx : A y = A' y) (hBx : B y = B' y) (hCx : C y = C' y) (hDx : D y = D' y) :
    rmP g y (A y) (B y) (C y) (D y) = rmP g y (A' y) (B' y) (C' y) (D' y) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov⟩ := (hLC g).1
  have hbridge : ∀ (A₁ B₁ C₁ D₁ : Tf), SmoothF A₁ → SmoothF B₁ → SmoothF C₁ → SmoothF D₁ →
      rmP g y (A₁ y) (B₁ y) (C₁ y) (D₁ y) = inner ℝ (curv (lcOf g) A₁ B₁ D₁ y) (C₁ y) := by
    intro A₁ B₁ C₁ D₁ hA₁ hB₁ hC₁ hD₁
    show g.inner y (rmVec (lcOf g) y (A₁ y) (B₁ y) (D₁ y)) (C₁ y)
      = inner ℝ (curv (lcOf g) A₁ B₁ D₁ y) (C₁ y)
    rw [show inner ℝ (curv (lcOf g) A₁ B₁ D₁ y) (C₁ y)
        = g.inner y (curv (lcOf g) A₁ B₁ D₁ y) (C₁ y) from rfl]
    have hrv : rmVec (lcOf g) y (A₁ y) (B₁ y) (D₁ y) = curv (lcOf g) A₁ B₁ D₁ y := by
      rw [show rmVec (lcOf g) y (A₁ y) (B₁ y) (D₁ y)
          = curv (lcOf g) (smoothExt y (A₁ y)) (smoothExt y (B₁ y)) (smoothExt y (D₁ y)) y
          from rfl]
      exact Submission.Curvature.curv_eq_of_apply_eq (lcOf g) hcov
        (Work.Diff.GE.smoothExt_cmdiff y (A₁ y)) hA₁
        (Work.Diff.GE.smoothExt_cmdiff y (B₁ y)) hB₁
        (Work.Diff.GE.smoothExt_cmdiff y (D₁ y)) hD₁
        (Work.Diff.GE.smoothExt_apply y (A₁ y)) (Work.Diff.GE.smoothExt_apply y (B₁ y))
        (Work.Diff.GE.smoothExt_apply y (D₁ y))
    rw [hrv]
  rw [hbridge A B C D hA hB hC hD, hbridge A' B' C' D' hA' hB' hC' hD',
    Submission.Curvature.curv_eq_of_apply_eq (lcOf g) hcov hA hA' hB hB' hD hD' hAx hBx hDx,
    hCx]


/-! ## Elementary helpers for the induction step -/

/-- `Function.update` of a tuple at a slot, all fields smooth. -/
lemma smoothF_update {k : ℕ} {G : Fin k → Tf} (hG : ∀ i, SmoothF (G i)) {j : Fin k} {W : Tf}
    (hW : SmoothF W) : ∀ q, SmoothF ((Function.update G j W) q) := by
  intro q
  rcases eq_or_ne q j with h | h
  · subst h; rw [Function.update_self]; exact hW
  · rw [Function.update_of_ne h]; exact hG q

/-- `Fin.cons` of smooth fields is smooth. -/
lemma smoothF_cons {k : ℕ} {v0 : Tf} (hv0 : SmoothF v0) {G : Fin k → Tf}
    (hG : ∀ i, SmoothF (G i)) : ∀ q, SmoothF ((Fin.cons v0 G : Fin (k + 1) → Tf) q) := by
  intro q
  refine Fin.cases ?_ ?_ q
  · rw [Fin.cons_zero]; exact hv0
  · intro i; rw [Fin.cons_succ]; exact hG i

/-- Updating the first slot of a tuple is `Fin.cons`. -/
lemma update_zero_eq_cons {k : ℕ} (F : Fin (k + 5) → Tf) (W : Tf) :
    Function.update F 0 W = (Fin.cons W (fun i : Fin (k + 4) => F i.succ) : Fin (k + 5) → Tf) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 5) => Tf), Function.update_self]
  · intro j
    rw [Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf),
      Function.update_of_ne (Fin.succ_ne_zero j) W F]

/-- Updating a non-first slot of a tuple is `Fin.cons` over the shifted tuple. -/
lemma update_succ_eq_cons {k : ℕ} (F : Fin (k + 5) → Tf) (j : Fin (k + 4)) (W : Tf) :
    Function.update F j.succ W
      = (Fin.cons (F 0) (Function.update (fun i : Fin (k + 4) => F i.succ) j W)
          : Fin (k + 5) → Tf) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero (α := fun _ : Fin (k + 5) => Tf),
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)) W F]
  · intro j'
    rw [Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf)]
    rcases eq_or_ne j' j with h | h
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.succ_inj.mp hh)), Function.update_of_ne h]

/-- The product rule for a sum of two scalar multiples, evaluated in a direction. -/
lemma mvfderiv_two_smul_lambda (f₁ f₂ Φ₁ Φ₂ : M → ℝ) (x : M) (u : TangentSpace I x)
    (hf₁ : MDiffAt f₁ x) (hf₂ : MDiffAt f₂ x) (hΦ₁ : MDiffAt Φ₁ x) (hΦ₂ : MDiffAt Φ₂ x) :
    (mvfderiv I (fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y) x) u
      = f₁ x * ((mvfderiv I Φ₁ x) u) + ((mvfderiv I f₁ x) u) * Φ₁ x
        + f₂ x * ((mvfderiv I Φ₂ x) u) + ((mvfderiv I f₂ x) u) * Φ₂ x := by
  have hfun : (fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y) = f₁ • Φ₁ + f₂ • Φ₂ := rfl
  have hadd : mvfderiv I (f₁ • Φ₁ + f₂ • Φ₂) x
      = mvfderiv I (f₁ • Φ₁) x + mvfderiv I (f₂ • Φ₂) x :=
    mvfderiv_add (hf₁.smul hΦ₁) (hf₂.smul hΦ₂)
  have hs1 : mvfderiv I (f₁ • Φ₁) x = f₁ x • mvfderiv I Φ₁ x + (mvfderiv I f₁ x).smulRight (Φ₁ x) :=
    mvfderiv_smul hf₁ hΦ₁
  have hs2 : mvfderiv I (f₂ • Φ₂) x = f₂ x • mvfderiv I Φ₂ x + (mvfderiv I f₂ x).smulRight (Φ₂ x) :=
    mvfderiv_smul hf₂ hΦ₂
  rw [hfun, hadd, hs1, hs2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- The product rule for a sum of two scalar multiples (field form), evaluated in a direction. -/
lemma mvfderiv_two_smul (f₁ f₂ Φ₁ Φ₂ : M → ℝ) (x : M) (u : TangentSpace I x)
    (hf₁ : MDiffAt f₁ x) (hf₂ : MDiffAt f₂ x) (hΦ₁ : MDiffAt Φ₁ x) (hΦ₂ : MDiffAt Φ₂ x) :
    (mvfderiv I (f₁ • Φ₁ + f₂ • Φ₂) x) u
      = f₁ x * ((mvfderiv I Φ₁ x) u) + ((mvfderiv I f₁ x) u) * Φ₁ x
        + f₂ x * ((mvfderiv I Φ₂ x) u) + ((mvfderiv I f₂ x) u) * Φ₂ x := by
  have hfun : (f₁ • Φ₁ + f₂ • Φ₂) = fun y : M => f₁ y • Φ₁ y + f₂ y • Φ₂ y := rfl
  rw [hfun]
  exact mvfderiv_two_smul_lambda f₁ f₂ Φ₁ Φ₂ x u hf₁ hf₂ hΦ₁ hΦ₂

/-- An eventual equality near `x` is eventual near every nearby point. -/
lemma eventuallyEq_nhds_eventually {α : Type*} [TopologicalSpace α] {x : α} {p q : α → M}
    (h : p =ᶠ[𝓝 x] q) : ∀ᶠ y in 𝓝 x, p =ᶠ[𝓝 y] q := by
  obtain ⟨U, hU, hUU⟩ := Filter.eventually_iff_exists_mem.mp h
  have hx : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact Filter.eventually_iff_exists_mem.mpr
    ⟨interior U, isOpen_interior.mem_nhds hy, fun z hz => hUU z (interior_subset hz)⟩

/-- `dirF` is local in both arguments. -/
lemma dirF_eventuallyEq {g : SMet I M} {X X' v v' : Tf} {x : M}
    (hX : SmoothF X) (hX' : SmoothF X') (hXeq : X =ᶠ[𝓝 x] X') (hveq : v =ᶠ[𝓝 x] v') :
    dirF g X v =ᶠ[𝓝 x] dirF g X' v' := by
  have h1 : ∀ᶠ y in 𝓝 x, X =ᶠ[𝓝 y] X' := eventuallyEq_nhds_eventually hXeq
  have h2 : ∀ᶠ y in 𝓝 x, v =ᶠ[𝓝 y] v' := eventuallyEq_nhds_eventually hveq
  filter_upwards [h1, h2] with y hyX hyv
  rw [dirF, dirF]
  rw [Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq g (hX.mdifferentiableAt (by simp))
    (hX'.mdifferentiableAt (by simp)) hyX, hyv.eq_of_nhds]

/-- **The induction statement.**  For tuples of smooth fields, `∇^k Rm` is smooth, `C^∞`-linear in
every slot, and local. -/
def TensProp (g : SMet I M) (k : ℕ) : Prop :=
  ∀ F : Fin (k + 4) → Tf,
    (∀ s, SmoothF (F s)) →
    CMDiff ∞ (fun y : M => ckt g k F y) ∧
    (∀ (s : Fin (k + 4)) (X₁ X₂ : Tf) (f₁ f₂ : M → ℝ),
      SmoothF X₁ → SmoothF X₂ → CMDiff ∞ f₁ → CMDiff ∞ f₂ →
      ckt g k (Function.update F s (f₁ • X₁ + f₂ • X₂))
        = f₁ • ckt g k (Function.update F s X₁) + f₂ • ckt g k (Function.update F s X₂)) ∧
    (∀ (x : M) (F' : Fin (k + 4) → Tf), (∀ s, SmoothF (F' s)) →
      (∀ s, F s =ᶠ[𝓝 x] F' s) → ckt g k F =ᶠ[𝓝 x] ckt g k F')

/-- The base case `k = 0`. -/
lemma tensProp_zero (hLC : LCSmooth I M) (g : SMet I M) : TensProp g 0 := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · exact Work.Diff.GE.rmP_fields_smooth hLC g (hF 0) (hF 1) (hF 2) (hF 3)
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    fin_cases s <;>
      · funext y
        simp only [ckt]
        simp [Pi.add_apply, Pi.smul_apply', smul_eq_mul,
          Work.Diff.GE.rmP_add_fst g hLC y, Work.Diff.GE.rmP_add_snd g hLC y,
          Work.Diff.GE.rmP_add_thd g hLC y, Work.Diff.GE.rmP_add_fth g hLC y,
          Work.Diff.GE.rmP_smul_fst g hLC y, Work.Diff.GE.rmP_smul_snd g hLC y,
          Work.Diff.GE.rmP_smul_thd g hLC y, Work.Diff.GE.rmP_smul_fth g hLC y]
  · intro x F' hF' h
    filter_upwards [Filter.eventually_all.2 h] with y hy
    exact rmP_congr_apply hLC g y (hF 0) (hF' 0) (hF 1) (hF' 1) (hF 2) (hF' 2)
      (hF 3) (hF' 3) (hy 0) (hy 1) (hy 2) (hy 3)

/-! ## The induction step -/

/-- **Smoothness step.** -/
lemma ckt_smooth_step (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (hih : TensProp g k)
    {F : Fin (k + 5) → Tf} (hF : ∀ s, SmoothF (F s)) :
    CMDiff ∞ (fun y : M => ckt g (k + 1) F y) := by
  have hG : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => F i.succ) i) := fun i => hF i.succ
  have hΦ : CMDiff ∞ (fun y : M => ckt g k (fun i : Fin (k + 4) => F i.succ) y) :=
    (hih (fun i : Fin (k + 4) => F i.succ) hG).1
  have h1 : CMDiff ∞ (fun y : M =>
      (mvfderiv I (fun y : M => ckt g k (fun i : Fin (k + 4) => F i.succ) y) y) (F 0 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hΦ (hF 0)
  have h2 : ∀ s : Fin (k + 4), CMDiff ∞ (fun y : M => ckt g k
      (Function.update (fun i : Fin (k + 4) => F i.succ) s
        (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))) y) := by
    intro s
    exact (hih _ (smoothF_update hG (dirF_smooth hLC g (hG s) (hF 0)))).1
  have h3' : CMDiff ∞ (fun y : M => ∑ s : Fin (k + 4), ckt g k
      (Function.update (fun i : Fin (k + 4) => F i.succ) s
        (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))) y) :=
    ContMDiff.sum (t := Finset.univ) (fun s _ => h2 s)
  have h3 : CMDiff ∞ (∑ s : Fin (k + 4), ckt g k
      (Function.update (fun i : Fin (k + 4) => F i.succ) s
        (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0)))) := by
    have hfun : (∑ s : Fin (k + 4), ckt g k
        (Function.update (fun i : Fin (k + 4) => F i.succ) s
          (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))))
        = fun y : M => ∑ s : Fin (k + 4), ckt g k
          (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (dirF g ((fun i : Fin (k + 4) => F i.succ) s) (F 0))) y := by
      funext y; rw [Finset.sum_apply]
    rw [hfun]; exact h3'
  rw [ckt_succ]
  exact h1.sub h3

/-- **Locality step.** -/
lemma ckt_loc_step (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (hih : TensProp g k)
    {F F' : Fin (k + 5) → Tf} (hF : ∀ s, SmoothF (F s)) (hF' : ∀ s, SmoothF (F' s))
    {x : M} (h : ∀ s, F s =ᶠ[𝓝 x] F' s) :
    ckt g (k + 1) F =ᶠ[𝓝 x] ckt g (k + 1) F' := by
  have hGs : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => F i.succ) i) := fun i => hF i.succ
  have hG's : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => F' i.succ) i) := fun i => hF' i.succ
  have hGloc : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 4),
      (fun i : Fin (k + 4) => F i.succ) i =ᶠ[𝓝 y] (fun i : Fin (k + 4) => F' i.succ) i := by
    rw [Filter.eventually_all]
    exact fun i => eventuallyEq_nhds_eventually (h i.succ)
  have h0loc : ∀ᶠ y in 𝓝 x, F 0 =ᶠ[𝓝 y] F' 0 := eventuallyEq_nhds_eventually (h 0)
  have hder : (fun z : M =>
        (mvfderiv I (fun z : M => ckt g k (fun i : Fin (k + 4) => F i.succ) z) z) (F 0 z))
      =ᶠ[𝓝 x] (fun z : M =>
        (mvfderiv I (fun z : M => ckt g k (fun i : Fin (k + 4) => F' i.succ) z) z) (F' 0 z)) := by
    filter_upwards [hGloc, h0loc] with y hyG hy0
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq
        ((hih (fun i : Fin (k + 4) => F i.succ) hGs).2.2 y
          (fun i : Fin (k + 4) => F' i.succ) hG's hyG), hy0.eq_of_nhds]
  have hsum : (∑ q : Fin (k + 4), ckt g k (Function.update (fun i : Fin (k + 4) => F i.succ) q
        (dirF g ((fun i : Fin (k + 4) => F i.succ) q) (F 0))))
      =ᶠ[𝓝 x] (∑ q : Fin (k + 4), ckt g k
        (Function.update (fun i : Fin (k + 4) => F' i.succ) q
          (dirF g ((fun i : Fin (k + 4) => F' i.succ) q) (F' 0)))) := by
    filter_upwards [hGloc, h0loc] with y hyG hy0
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hdq : dirF g ((fun i : Fin (k + 4) => F i.succ) q) (F 0)
        =ᶠ[𝓝 y] dirF g ((fun i : Fin (k + 4) => F' i.succ) q) (F' 0) :=
      dirF_eventuallyEq (g := g) (hGs q) (hG's q) (hyG q) hy0
    have hgerm : ∀ s : Fin (k + 4),
        (Function.update (fun i : Fin (k + 4) => F i.succ) q
          (dirF g ((fun i : Fin (k + 4) => F i.succ) q) (F 0))) s
        =ᶠ[𝓝 y] (Function.update (fun i : Fin (k + 4) => F' i.succ) q
          (dirF g ((fun i : Fin (k + 4) => F' i.succ) q) (F' 0))) s := by
      intro s
      rcases eq_or_ne s q with hs | hs
      · subst hs; rw [Function.update_self, Function.update_self]; exact hdq
      · rw [Function.update_of_ne hs, Function.update_of_ne hs]; exact hyG s
    exact ((hih (Function.update (fun i : Fin (k + 4) => F i.succ) q
          (dirF g ((fun i : Fin (k + 4) => F i.succ) q) (F 0)))
        (smoothF_update hGs (dirF_smooth hLC g (hGs q) (hF 0)))).2.2 y
      (Function.update (fun i : Fin (k + 4) => F' i.succ) q
          (dirF g ((fun i : Fin (k + 4) => F' i.succ) q) (F' 0)))
        (smoothF_update hG's (dirF_smooth hLC g (hG's q) (hF' 0))) hgerm).eq_of_nhds
  rw [ckt_succ, ckt_succ]
  exact hder.sub hsum



/-- **Linearity in the differentiation slot.** -/
lemma ckt_lin_dir (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (hih : TensProp g k)
    {G : Fin (k + 4) → Tf} (hG : ∀ i, SmoothF (G i))
    {X₁ X₂ : Tf} (hX₁ : SmoothF X₁) (hX₂ : SmoothF X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    ckt g (k + 1) (Fin.cons (f₁ • X₁ + f₂ • X₂) G)
      = f₁ • ckt g (k + 1) (Fin.cons X₁ G) + f₂ • ckt g (k + 1) (Fin.cons X₂ G) := by
  have hconsF : ∀ (W : Tf),
      (fun i : Fin (k + 4) => (Fin.cons W G : Fin (k + 5) → Tf) i.succ) = G := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf) W G i
  have hconsP : ∀ (W : Tf) (i : Fin (k + 4)),
      (Fin.cons W G : Fin (k + 5) → Tf) i.succ = G i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf) W G i
  have hzero : ∀ (W : Tf), (Fin.cons W G : Fin (k + 5) → Tf) 0 = W :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 5) => Tf) W G
  rw [ckt_succ, ckt_succ, ckt_succ]
  simp only [hconsF, hconsP, hzero]
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have ht1 : (mvfderiv I (ckt g k G) y) (f₁ y • X₁ y + f₂ y • X₂ y)
      = f₁ y • ((mvfderiv I (ckt g k G) y) (X₁ y))
        + f₂ y • ((mvfderiv I (ckt g k G) y) (X₂ y)) := by
    simp only [map_add, map_smul]
  have hs : (∑ q : Fin (k + 4), ckt g k
        (Function.update G q (dirF g (G q) (f₁ • X₁ + f₂ • X₂))) y)
      = f₁ y • (∑ q : Fin (k + 4), ckt g k (Function.update G q (dirF g (G q) X₁)) y)
        + f₂ y • (∑ q : Fin (k + 4), ckt g k (Function.update G q (dirF g (G q) X₂)) y) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [dirF_add_dir]
    have hq := (hih G hG).2.1 q (dirF g (G q) X₁) (dirF g (G q) X₂) f₁ f₂
      (dirF_smooth hLC g (hG q) hX₁) (dirF_smooth hLC g (hG q) hX₂) hf₁ hf₂
    rw [hq]
    simp only [Pi.add_apply, Pi.smul_apply']
  rw [ht1, hs]
  simp only [smul_sub, smul_eq_mul]
  ring

/-- **Linearity in a differentiation slot of the tail.** -/
lemma ckt_lin_tail (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (hih : TensProp g k)
    {G : Fin (k + 4) → Tf} (hG : ∀ i, SmoothF (G i))
    {v0 X₁ X₂ : Tf} (hv0 : SmoothF v0) (hX₁ : SmoothF X₁) (hX₂ : SmoothF X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) (j : Fin (k + 4)) :
    ckt g (k + 1) (Fin.cons v0 (Function.update G j (f₁ • X₁ + f₂ • X₂)))
      = f₁ • ckt g (k + 1) (Fin.cons v0 (Function.update G j X₁))
        + f₂ • ckt g (k + 1) (Fin.cons v0 (Function.update G j X₂)) := by
  have hconsF : ∀ (W : Fin (k + 4) → Tf),
      (fun i : Fin (k + 4) => (Fin.cons v0 W : Fin (k + 5) → Tf) i.succ) = W := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf) v0 W i
  have hconsP : ∀ (W : Fin (k + 4) → Tf) (i : Fin (k + 4)),
      (Fin.cons v0 W : Fin (k + 5) → Tf) i.succ = W i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 5) => Tf) v0 W i
  have hzero : ∀ (W : Fin (k + 4) → Tf), (Fin.cons v0 W : Fin (k + 5) → Tf) 0 = v0 :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 5) => Tf) v0 W
  rw [ckt_succ, ckt_succ, ckt_succ]
  simp only [hconsF, hconsP, hzero]
  have hAW : ckt g k (Function.update G j (f₁ • X₁ + f₂ • X₂))
      = f₁ • ckt g k (Function.update G j X₁) + f₂ • ckt g k (Function.update G j X₂) :=
    (hih G hG).2.1 j X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
  have hadd : ∀ {A B : Tf}, SmoothF A → SmoothF B →
      ckt g k (Function.update G j (A + B))
        = ckt g k (Function.update G j A) + ckt g k (Function.update G j B) := by
    intro A B hA hB
    have h := (hih G hG).2.1 j A B (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hA hB
      (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have hAB : (fun _ : M => (1 : ℝ)) • A + (fun _ : M => (1 : ℝ)) • B = A + B := by
      funext z; simp
    have hA' : (fun _ : M => (1 : ℝ)) • ckt g k (Function.update G j A)
        = ckt g k (Function.update G j A) := by funext z; simp
    have hB' : (fun _ : M => (1 : ℝ)) • ckt g k (Function.update G j B)
        = ckt g k (Function.update G j B) := by funext z; simp
    rw [hAB, hA', hB'] at h
    exact h
  have hS1 : CMDiff ∞ (ckt g k (Function.update G j X₁)) :=
    (hih _ (smoothF_update hG hX₁)).1
  have hS2 : CMDiff ∞ (ckt g k (Function.update G j X₂)) :=
    (hih _ (smoothF_update hG hX₂)).1
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have hT : (mvfderiv I (ckt g k (Function.update G j (f₁ • X₁ + f₂ • X₂))) y) (v0 y)
      = f₁ y • ((mvfderiv I (ckt g k (Function.update G j X₁)) y) (v0 y))
        + ((mvfderiv I f₁ y) (v0 y)) • (ckt g k (Function.update G j X₁) y)
        + f₂ y • ((mvfderiv I (ckt g k (Function.update G j X₂)) y) (v0 y))
        + ((mvfderiv I f₂ y) (v0 y)) • (ckt g k (Function.update G j X₂) y) := by
    rw [hAW]
    rw [mvfderiv_two_smul f₁ f₂ (ckt g k (Function.update G j X₁))
      (ckt g k (Function.update G j X₂)) y (v0 y)
      (hf₁.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
      (hS1.mdifferentiableAt (by simp)) (hS2.mdifferentiableAt (by simp))]
    simp only [smul_eq_mul]
  have hstep : ∀ q : Fin (k + 4), q ≠ j →
      ckt g k (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
        (dirF g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0))
      = f₁ • ckt g k (Function.update (Function.update G j X₁) q
            (dirF g ((Function.update G j X₁) q) v0))
        + f₂ • ckt g k (Function.update (Function.update G j X₂) q
            (dirF g ((Function.update G j X₂) q) v0)) := by
    intro q hqj
    have h1 : Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
        (dirF g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)
        = Function.update (Function.update G q (dirF g (G q) v0)) j (f₁ • X₁ + f₂ • X₂) := by
      rw [Function.update_of_ne hqj (f₁ • X₁ + f₂ • X₂) G]
      exact (Function.update_comm hqj (dirF g (G q) v0) (f₁ • X₁ + f₂ • X₂) G).symm
    have h2 : Function.update (Function.update G q (dirF g (G q) v0)) j X₁
        = Function.update (Function.update G j X₁) q (dirF g ((Function.update G j X₁) q) v0) := by
      rw [Function.update_of_ne hqj X₁ G]
      exact Function.update_comm hqj (dirF g (G q) v0) X₁ G
    have h3 : Function.update (Function.update G q (dirF g (G q) v0)) j X₂
        = Function.update (Function.update G j X₂) q (dirF g ((Function.update G j X₂) q) v0) := by
      rw [Function.update_of_ne hqj X₂ G]
      exact Function.update_comm hqj (dirF g (G q) v0) X₂ G
    rw [h1]
    have hlin := (hih (Function.update G q (dirF g (G q) v0))
      (smoothF_update hG (dirF_smooth hLC g (hG q) hv0))).2.1 j X₁ X₂ f₁ f₂
      hX₁ hX₂ hf₁ hf₂
    rw [hlin, h2, h3]
  have hjterm : ckt g k (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) j
        (dirF g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) j) v0)) y
      = f₁ y • (ckt g k (Function.update (Function.update G j X₁) j
            (dirF g ((Function.update G j X₁) j) v0)) y)
        + f₂ y • (ckt g k (Function.update (Function.update G j X₂) j
            (dirF g ((Function.update G j X₂) j) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (ckt g k (Function.update G j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (ckt g k (Function.update G j X₂) y) := by
    have hidem : Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) j
        (dirF g (Function.update G j (f₁ • X₁ + f₂ • X₂) j) v0)
        = Function.update G j (dirF g (f₁ • X₁ + f₂ • X₂) v0) := by
      rw [Function.update_self]
      exact Function.update_idem (f₁ • X₁ + f₂ • X₂) (dirF g (f₁ • X₁ + f₂ • X₂) v0) G
    rw [hidem, dirF_leibniz (g := g) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
      (v0 := v0) hX₁ hX₂ hf₁ hf₂]
    have hE1 : CMDiff ∞ (fun z : M => (mvfderiv I f₁ z) (v0 z)) :=
      mvfderiv_apply_contMDiff hf₁ hv0
    have hE2 : CMDiff ∞ (fun z : M => (mvfderiv I f₂ z) (v0 z)) :=
      mvfderiv_apply_contMDiff hf₂ hv0
    rw [add_assoc (f₁ • dirF g X₁ v0 + (fun z : M => (mvfderiv I f₁ z) (v0 z)) • X₁)
        (f₂ • dirF g X₂ v0) ((fun z : M => (mvfderiv I f₂ z) (v0 z)) • X₂)]
    rw [hadd (smoothF_add (smoothF_smul hf₁ (dirF_smooth hLC g hX₁ hv0)) (smoothF_smul hE1 hX₁))
        (smoothF_add (smoothF_smul hf₂ (dirF_smooth hLC g hX₂ hv0)) (smoothF_smul hE2 hX₂))]
    rw [(hih G hG).2.1 j (dirF g X₁ v0) X₁ f₁ (fun z : M => (mvfderiv I f₁ z) (v0 z))
        (dirF_smooth hLC g hX₁ hv0) hX₁ hf₁ hE1]
    rw [(hih G hG).2.1 j (dirF g X₂ v0) X₂ f₂ (fun z : M => (mvfderiv I f₂ z) (v0 z))
        (dirF_smooth hLC g hX₂ hv0) hX₂ hf₂ hE2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply', Function.update_idem,
      Function.update_self, smul_eq_mul]
    ring
  have hne : (∑ q ∈ Finset.univ.erase j, ckt g k
        (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
          (dirF g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y * (∑ q ∈ Finset.univ.erase j, ckt g k
            (Function.update (Function.update G j X₁) q (dirF g ((Function.update G j X₁) q) v0)) y)
        + f₂ y * (∑ q ∈ Finset.univ.erase j, ckt g k
            (Function.update (Function.update G j X₂) q (dirF g ((Function.update G j X₂) q) v0)) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqj : q ≠ j := (Finset.mem_erase.mp hq).1
    rw [hstep q hqj]
    simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  have hS : (∑ q : Fin (k + 4), ckt g k
        (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
          (dirF g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y • (∑ q : Fin (k + 4), ckt g k
            (Function.update (Function.update G j X₁) q (dirF g ((Function.update G j X₁) q) v0)) y)
        + f₂ y • (∑ q : Fin (k + 4), ckt g k
            (Function.update (Function.update G j X₂) q (dirF g ((Function.update G j X₂) q) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (ckt g k (Function.update G j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (ckt g k (Function.update G j X₂) y) := by
    rw [← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j)]
    rw [hjterm, hne]
    simp only [smul_add, smul_eq_mul]
    ring
  rw [hT, hS]
  simp only [smul_sub, smul_add, smul_eq_mul]
  ring

/-! ## The bridge to `covKRmExt` -/

/-- Assemble a `Fin (k+4)`-tuple of fields from a `k`-tuple of differentiation slots and a
4-tuple of curvature slots. -/
noncomputable def mkT {k : ℕ} (w : Fin k → Tf) (B : Fin 4 → Tf) : Fin (k + 4) → Tf :=
  Fin.addCases (motive := fun _ => Tf) (fun i => w i) (fun p => B p)

lemma mkT_castAdd {k : ℕ} (w : Fin k → Tf) (B : Fin 4 → Tf) (i : Fin k) :
    mkT w B (Fin.castAdd 4 i) = w i := Fin.addCases_left i

lemma mkT_natAdd {k : ℕ} (w : Fin k → Tf) (B : Fin 4 → Tf) (p : Fin 4) :
    mkT w B (Fin.natAdd k p) = B p := Fin.addCases_right p

lemma succ_castAdd_four {k : ℕ} (i : Fin k) :
    (Fin.castAdd 4 i).succ = Fin.castAdd 4 i.succ := by
  ext; simp

lemma succ_natAdd_four {k : ℕ} (p : Fin 4) :
    (Fin.natAdd k p).succ = Fin.natAdd (k + 1) p := by
  ext; simp only [Fin.val_succ, Fin.val_natAdd]; omega

lemma natAdd_ne_castAdd_four {k : ℕ} (p : Fin 4) (i : Fin k) :
    Fin.natAdd k p ≠ Fin.castAdd 4 i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

lemma update_castAdd_mkT {k : ℕ} (w : Fin k → Tf) (B : Fin 4 → Tf) (i : Fin k) (X : Tf) :
    Function.update (mkT w B) (Fin.castAdd 4 i) X = mkT (Function.update w i X) B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro j
    rw [mkT_castAdd (Function.update w i X) B j]
    rcases eq_or_ne j i with h | h
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.castAdd_inj.mp hh)) X (mkT w B),
        Function.update_of_ne h X w, mkT_castAdd]
  · intro p
    rw [mkT_natAdd (Function.update w i X) B p,
      Function.update_of_ne (natAdd_ne_castAdd_four p i) X (mkT w B), mkT_natAdd]

lemma update_natAdd_mkT {k : ℕ} (w : Fin k → Tf) (B : Fin 4 → Tf) (p : Fin 4) (X : Tf) :
    Function.update (mkT w B) (Fin.natAdd k p) X = mkT w (Function.update B p X) := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [mkT_castAdd w (Function.update B p X) i,
      Function.update_of_ne (Ne.symm (natAdd_ne_castAdd_four p i)) X (mkT w B), mkT_castAdd]
  · intro q
    rw [mkT_natAdd w (Function.update B p X) q]
    rcases eq_or_ne q p with h | h
    · subst h
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h ((Fin.natAdd_inj k).mp hh)) X (mkT w B),
        Function.update_of_ne h X B, mkT_natAdd]

lemma mkT_comp_succ {k : ℕ} (w : Fin (k + 1) → Tf) (B : Fin 4 → Tf) :
    (fun i : Fin (k + 4) => mkT w B i.succ) = mkT (fun i : Fin k => w i.succ) B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [mkT_castAdd (fun i : Fin k => w i.succ) B i, succ_castAdd_four, mkT_castAdd]
  · intro p
    rw [mkT_natAdd (fun i : Fin k => w i.succ) B p, succ_natAdd_four, mkT_natAdd]

lemma mkT_succ_val {k : ℕ} (w : Fin (k + 1) → Tf) (B : Fin 4 → Tf) (i : Fin (k + 4)) :
    mkT w B (Fin.succ i) = mkT (fun j : Fin k => w j.succ) B i := by
  rw [← mkT_comp_succ]

/-- The recursion `ckt` computes `covKRmExt` on the corresponding split tuple. -/
lemma ckt_mkT_eq (g : SMet I M) : ∀ (k : ℕ) (w : Fin k → Tf) (B : Fin 4 → Tf) (y : M),
    ckt g k (mkT w B) y = covKRmExt g k w (B 0) (B 1) (B 2) (B 3) y := by
  intro k
  induction k with
  | zero =>
      intro w B y
      rfl
  | succ k ih =>
      intro v A y
      have h0 : mkT v A 0 = v 0 := by
        rw [show (0 : Fin (k + 5)) = Fin.castAdd 4 (0 : Fin (k + 1)) from rfl, mkT_castAdd]
      have htail : (fun i : Fin (k + 4) => mkT v A i.succ)
          = mkT (fun i : Fin k => v i.succ) A := mkT_comp_succ v A
      have hder : ckt g k (mkT (fun i : Fin k => v i.succ) A)
          = covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2) (A 3) :=
        funext (fun z => ih (fun i : Fin k => v i.succ) A z)
      have hsumk : (∑ i : Fin k, ckt g k (Function.update (mkT (fun i : Fin k => v i.succ) A)
            (Fin.castAdd 4 i)
            (dirF g ((mkT (fun i : Fin k => v i.succ) A) (Fin.castAdd 4 i)) (v 0))) y)
          = ∑ i : Fin k, covKRmExt g k (Function.update (fun i : Fin k => v i.succ) i
              (dirF g (v i.succ) (v 0))) (A 0) (A 1) (A 2) (A 3) y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [update_castAdd_mkT, mkT_castAdd]
        exact ih (Function.update (fun i : Fin k => v i.succ) i (dirF g (v i.succ) (v 0))) A y
      have hsum4 : (∑ p : Fin 4, ckt g k (Function.update (mkT (fun i : Fin k => v i.succ) A)
            (Fin.natAdd k p)
            (dirF g ((mkT (fun i : Fin k => v i.succ) A) (Fin.natAdd k p)) (v 0))) y)
          = ∑ p : Fin 4, covKRmExt g k (fun i : Fin k => v i.succ)
              ((Function.update A p (dirF g (A p) (v 0))) 0)
              ((Function.update A p (dirF g (A p) (v 0))) 1)
              ((Function.update A p (dirF g (A p) (v 0))) 2)
              ((Function.update A p (dirF g (A p) (v 0))) 3) y := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_natAdd_mkT, mkT_natAdd]
        exact ih (fun i : Fin k => v i.succ) (Function.update A p (dirF g (A p) (v 0))) y
      have hfour : (∑ p : Fin 4, covKRmExt g k (fun i : Fin k => v i.succ)
            ((Function.update A p (dirF g (A p) (v 0))) 0)
            ((Function.update A p (dirF g (A p) (v 0))) 1)
            ((Function.update A p (dirF g (A p) (v 0))) 2)
            ((Function.update A p (dirF g (A p) (v 0))) 3) y)
          = covKRmExt g k (fun i : Fin k => v i.succ) (dirF g (A 0) (v 0)) (A 1) (A 2) (A 3) y
            + covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (dirF g (A 1) (v 0)) (A 2) (A 3) y
            + covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1) (dirF g (A 2) (v 0)) (A 3) y
            + covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2) (dirF g (A 3) (v 0)) y := by
        rw [Fin.sum_univ_four]
        simp only [Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
          Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)]
      rw [ckt_succ]
      rw [Pi.sub_apply, Finset.sum_apply]
      rw [htail, h0, hder, Fin.sum_univ_add, hsumk, hsum4, hfour]
      rw [show covKRmExt g (k + 1) v (A 0) (A 1) (A 2) (A 3) y
          = mvfderiv I (covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2) (A 3)) y
              (v 0 y)
            - (∑ i : Fin k, covKRmExt g k (Function.update (fun j : Fin k => v j.succ) i
                  (dirF g (v i.succ) (v 0))) (A 0) (A 1) (A 2) (A 3) y)
            - covKRmExt g k (fun i : Fin k => v i.succ)
                (dirF g (A 0) (v 0)) (A 1) (A 2) (A 3) y
            - covKRmExt g k (fun i : Fin k => v i.succ) (A 0)
                (dirF g (A 1) (v 0)) (A 2) (A 3) y
            - covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1)
                (dirF g (A 2) (v 0)) (A 3) y
            - covKRmExt g k (fun i : Fin k => v i.succ) (A 0) (A 1) (A 2)
                (dirF g (A 3) (v 0)) y from rfl]
      ring

/-- The general bridge: `ckt` computes `covKRmExt` on the corresponding split tuple. -/
lemma ckt_eq_covKRmExt (g : SMet I M) (k : ℕ) (F : Fin (k + 4) → Tf) (y : M) :
    ckt g k F y = covKRmExt g k (fun i : Fin k => F (Fin.castAdd 4 i))
      (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2)) (F (Fin.natAdd k 3)) y := by
  have hsplit : F = mkT (fun i : Fin k => F (Fin.castAdd 4 i))
      (fun p : Fin 4 => F (Fin.natAdd k p)) := by
    funext s
    refine Fin.addCases ?_ ?_ s
    · intro i; rw [mkT_castAdd]
    · intro p; rw [mkT_natAdd]
  rw [hsplit, ckt_mkT_eq]
  simp only [mkT_castAdd, mkT_natAdd]

/-! ## Smoothness, locality and linearity of the iteration -/

theorem tensProp_succ (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (hih : TensProp g k) :
    TensProp g (k + 1) := by
  intro F hF
  refine ⟨ckt_smooth_step hLC g k hih hF, ?_, ?_⟩
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    refine Fin.cases ?_ ?_ s
    · rw [update_zero_eq_cons, update_zero_eq_cons, update_zero_eq_cons]
      exact ckt_lin_dir hLC g k hih (fun i => hF i.succ) hX₁ hX₂ hf₁ hf₂
    · intro j
      rw [update_succ_eq_cons, update_succ_eq_cons, update_succ_eq_cons]
      exact ckt_lin_tail hLC g k hih (fun i => hF i.succ) (hF 0) hX₁ hX₂ hf₁ hf₂ j
  · intro x F' hF' h
    exact ckt_loc_step hLC g k hih hF hF' h

theorem tensProp_all (hLC : LCSmooth I M) (g : SMet I M) : ∀ k, TensProp g k := by
  intro k
  induction k with
  | zero => exact tensProp_zero hLC g
  | succ k ih => exact tensProp_succ hLC g k ih

lemma TensProp_add (hLC : LCSmooth I M) (g : SMet I M) {k : ℕ} (h : TensProp g k)
    {F : Fin (k + 4) → Tf} (hF : ∀ s, SmoothF (F s)) (s : Fin (k + 4))
    {X Y : Tf} (hX : SmoothF X) (hY : SmoothF Y) :
    ckt g k (Function.update F s (X + Y))
      = ckt g k (Function.update F s X) + ckt g k (Function.update F s Y) := by
  have h1 := (h F hF).2.1 s X Y (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hX hY
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  have e1 : (fun _ : M => (1 : ℝ)) • X + (fun _ : M => (1 : ℝ)) • Y = X + Y := by
    funext z; simp
  have e2 : (fun _ : M => (1 : ℝ)) • ckt g k (Function.update F s X)
      = ckt g k (Function.update F s X) := by funext z; simp
  have e3 : (fun _ : M => (1 : ℝ)) • ckt g k (Function.update F s Y)
      = ckt g k (Function.update F s Y) := by funext z; simp
  rw [e1, e2, e3] at h1
  exact h1

lemma TensProp_smul (hLC : LCSmooth I M) (g : SMet I M) {k : ℕ} (h : TensProp g k)
    {F : Fin (k + 4) → Tf} (hF : ∀ s, SmoothF (F s)) (s : Fin (k + 4)) (c : ℝ)
    {X : Tf} (hX : SmoothF X) :
    ckt g k (Function.update F s ((fun _ : M => c) • X))
      = (fun _ : M => c) • ckt g k (Function.update F s X) := by
  have h1 := (h F hF).2.1 s X X (fun _ : M => c) (fun _ : M => (0 : ℝ)) hX hX
    (contMDiff_const (c := c)) (contMDiff_const (c := (0 : ℝ)))
  have e1 : (fun _ : M => c) • X + (fun _ : M => (0 : ℝ)) • X = (fun _ : M => c) • X := by
    funext z; simp
  have e2 : (fun _ : M => c) • ckt g k (Function.update F s X)
      + (fun _ : M => (0 : ℝ)) • ckt g k (Function.update F s X)
      = (fun _ : M => c) • ckt g k (Function.update F s X) := by funext z; simp
  rw [e1, e2] at h1
  exact h1

/-- Single-slot value dependence of the iteration. -/
lemma ckt_val_dep (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {FS : Fin (k + 4) → Tf} (hFS : ∀ s, SmoothF (FS s)) (s : Fin (k + 4))
    {X X' : Tf} (hX : SmoothF X) (hX' : SmoothF X') (h : X x = X' x) :
    ckt g k (Function.update FS s X) x = ckt g k (Function.update FS s X') x := by
  have h1 : ∀ (X₁ X₂ : Tf) (f₁ f₂ : M → ℝ), SmoothF X₁ → SmoothF X₂ → CMDiff ∞ f₁ →
      CMDiff ∞ f₂ →
      ckt g k (Function.update FS s (f₁ • X₁ + f₂ • X₂)) x
        = f₁ x * ckt g k (Function.update FS s X₁) x
          + f₂ x * ckt g k (Function.update FS s X₂) x := by
    intro X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    have h2 := congrFun ((tensProp_all hLC g k FS hFS).2.1 s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂) x
    simpa only [Pi.add_apply, Pi.mul_apply, smul_eq_mul] using h2
  have h3 : ∀ (X Y : Tf), SmoothF X → SmoothF Y → X =ᶠ[𝓝 x] Y →
      ckt g k (Function.update FS s X) x = ckt g k (Function.update FS s Y) x := by
    intro X Y hX hY heq
    have h4 : ∀ q, (Function.update FS s X) q =ᶠ[𝓝 x] (Function.update FS s Y) q := by
      intro q
      rcases eq_or_ne q s with hq | hq
      · subst hq; rw [Function.update_self, Function.update_self]; exact heq
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]; try rfl
    exact (((tensProp_all hLC g k (Function.update FS s X) (smoothF_update hFS hX)).2.2 x
      (Function.update FS s Y) (smoothF_update hFS hY) h4)).eq_of_nhds
  exact Work.Diff.GE.field_value_dep_of_linear x h1 h3 hX hX' h

/-! ## The point-level evaluation and its multilinearity -/

/-- `∇^k Rm` evaluated at `x` on the tuple of tangent vectors `w`. -/
noncomputable def Kpt (g : SMet I M) (x : M) (k : ℕ)
    (w : Fin (k + 4) → TangentSpace I x) : ℝ :=
  ckt g k (fun s => smoothExt x (w s)) x

lemma Kpt_add (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    (w : Fin (k + 4) → TangentSpace I x) (s : Fin (k + 4)) (u v : TangentSpace I x) :
    Kpt g x k (Function.update w s (u + v))
      = Kpt g x k (Function.update w s u) + Kpt g x k (Function.update w s v) := by
  have hFS : ∀ q, SmoothF ((fun s => smoothExt x (w s)) q) :=
    fun q => Work.Diff.GE.smoothExt_cmdiff x (w q)
  have htupeq : ∀ (y : TangentSpace I x),
      (fun q : Fin (k + 4) => smoothExt x ((Function.update w s y) q))
        = Function.update (fun q => smoothExt x (w q)) s (smoothExt x y) := by
    intro y; funext q
    rcases eq_or_ne q s with hq | hq
    · subst hq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
  have hv : (smoothExt x (u + v)) x = (smoothExt x u + smoothExt x v) x := by
    simp only [Work.Diff.GE.smoothExt_apply, Pi.add_apply]
  have h1 : Kpt g x k (Function.update w s (u + v))
      = ckt g k (Function.update (fun q => smoothExt x (w q)) s (smoothExt x (u + v))) x := by
    rw [Kpt, htupeq]
  have h2 := ckt_val_dep hLC g k x hFS s (Work.Diff.GE.smoothExt_cmdiff x (u + v))
    (smoothF_add (Work.Diff.GE.smoothExt_cmdiff x u) (Work.Diff.GE.smoothExt_cmdiff x v)) hv
  have h3 := TensProp_add hLC g (tensProp_all hLC g k) hFS s
    (Work.Diff.GE.smoothExt_cmdiff x u) (Work.Diff.GE.smoothExt_cmdiff x v)
  have h4 : Kpt g x k (Function.update w s u)
      = ckt g k (Function.update (fun q => smoothExt x (w q)) s (smoothExt x u)) x := by
    rw [Kpt, htupeq]
  have h5 : Kpt g x k (Function.update w s v)
      = ckt g k (Function.update (fun q => smoothExt x (w q)) s (smoothExt x v)) x := by
    rw [Kpt, htupeq]
  rw [h1, h2, h3, h4, h5]
  simp only [Pi.add_apply]

lemma Kpt_smul (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    (w : Fin (k + 4) → TangentSpace I x) (s : Fin (k + 4)) (c : ℝ) (u : TangentSpace I x) :
    Kpt g x k (Function.update w s (c • u)) = c • Kpt g x k (Function.update w s u) := by
  have hFS : ∀ q, SmoothF ((fun s => smoothExt x (w s)) q) :=
    fun q => Work.Diff.GE.smoothExt_cmdiff x (w q)
  have htupeq : ∀ (y : TangentSpace I x),
      (fun q : Fin (k + 4) => smoothExt x ((Function.update w s y) q))
        = Function.update (fun q => smoothExt x (w q)) s (smoothExt x y) := by
    intro y; funext q
    rcases eq_or_ne q s with hq | hq
    · subst hq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
  have hv : (smoothExt x (c • u)) x = ((fun _ : M => c) • smoothExt x u) x := by
    simp only [Work.Diff.GE.smoothExt_apply, Pi.smul_apply']
  have h1 : Kpt g x k (Function.update w s (c • u))
      = ckt g k (Function.update (fun q => smoothExt x (w q)) s (smoothExt x (c • u))) x := by
    rw [Kpt, htupeq]
  have h2 := ckt_val_dep hLC g k x hFS s (Work.Diff.GE.smoothExt_cmdiff x (c • u))
    (smoothF_smul (contMDiff_const (c := c)) (Work.Diff.GE.smoothExt_cmdiff x u)) hv
  have h3 := TensProp_smul hLC g (tensProp_all hLC g k) hFS s c
    (Work.Diff.GE.smoothExt_cmdiff x u)
  have h4 : Kpt g x k (Function.update w s u)
      = ckt g k (Function.update (fun q => smoothExt x (w q)) s (smoothExt x u)) x := by
    rw [Kpt, htupeq]
  rw [h1, h2, h3, h4]
  simp only [Pi.smul_apply']

/-- `Function.update` does not depend on which `DecidableEq` instance is used. -/
lemma update_inst_congr {α : Type*} {β : α → Sort*} (i₁ i₂ : DecidableEq α)
    (f : (a : α) → β a) (a' : α) (v : β a') :
    @Function.update α β i₁ f a' v = @Function.update α β i₂ f a' v := by
  funext x
  by_cases h : x = a'
  · subst h
    rw [@Function.update_self α β i₁ x v f, @Function.update_self α β i₂ x v f]
  · rw [@Function.update_of_ne α β i₁ x a' h v f, @Function.update_of_ne α β i₂ x a' h v f]

/-- **The multilinear map whose Frobenius norm is `|∇^k Rm|²`.** -/
noncomputable def KptLin (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin (k + 4) => TangentSpace I x) ℝ where
  toFun := Kpt g x k
  map_update_add' := by
    intro _ m s u v
    simp only [update_inst_congr (i₂ := instDecidableEqFin (k + 4))]
    exact Kpt_add hLC g x k m s u v
  map_update_smul' := by
    intro _ m s c u
    simp only [update_inst_congr (i₂ := instDecidableEqFin (k + 4))]
    exact Kpt_smul hLC g x k m s c u

end Tensor

theorem curvNormK_frame_indep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) {g : Submission.Diff.SMet I M} (x : M) (k : ℕ)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) :
    Work.Diff.EXT.curvNormK g x k =
      ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (Work.Diff.EXT.covKRmC g x e k ι i j l m) ^ 2 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hone : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
    exact he i j
  have honf : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show inner ℝ (onFrame g x i) (onFrame g x j)
        = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame g x i j
  have hpt : ∀ (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)),
      covKRmC g x f k ι i j l m = Kpt g x k (fun s => f (Fin.append ι ![i, j, l, m] s)) := by
    intro f ι i j l m
    show covKRmC g x f k ι i j l m
      = ckt g k (fun s' => smoothExt x ((fun s => f (Fin.append ι ![i, j, l, m] s)) s')) x
    rw [covKRmC, ckt_eq_covKRmExt]
    have h1 : (fun s : Fin k => (fun s' : Fin (k + 4) =>
          smoothExt x (f (Fin.append ι ![i, j, l, m] s'))) (Fin.castAdd 4 s))
        = fun s => smoothExt x (f (ι s)) := by
      funext s
      show smoothExt x (f (Fin.append ι ![i, j, l, m] (Fin.castAdd 4 s)))
        = smoothExt x (f (ι s))
      rw [Fin.append_left]
    have h2 : smoothExt x ((fun s => f (Fin.append ι ![i, j, l, m] s)) (Fin.natAdd k 0))
        = smoothExt x (f i) := by
      show smoothExt x (f (Fin.append ι ![i, j, l, m] (Fin.natAdd k 0))) = smoothExt x (f i)
      rw [Fin.append_right]; rfl
    have h3 : smoothExt x ((fun s => f (Fin.append ι ![i, j, l, m] s)) (Fin.natAdd k 1))
        = smoothExt x (f j) := by
      show smoothExt x (f (Fin.append ι ![i, j, l, m] (Fin.natAdd k 1))) = smoothExt x (f j)
      rw [Fin.append_right]; rfl
    have h4 : smoothExt x ((fun s => f (Fin.append ι ![i, j, l, m] s)) (Fin.natAdd k 2))
        = smoothExt x (f l) := by
      show smoothExt x (f (Fin.append ι ![i, j, l, m] (Fin.natAdd k 2))) = smoothExt x (f l)
      rw [Fin.append_right]; rfl
    have h5 : smoothExt x ((fun s => f (Fin.append ι ![i, j, l, m] s)) (Fin.natAdd k 3))
        = smoothExt x (f m) := by
      show smoothExt x (f (Fin.append ι ![i, j, l, m] (Fin.natAdd k 3))) = smoothExt x (f m)
      rw [Fin.append_right]; rfl
    rw [h1, h2, h3, h4, h5]
  have hsum : ∀ (f : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC g x f k ι i j l m) ^ 2)
        = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
            (Kpt g x k (fun s => f (w s))) ^ 2 := by
    intro f
    rw [sum_fin_add_four (fun w : Fin (k + 4) → Fin (Module.finrank ℝ E) =>
      (Kpt g x k (fun s => f (w s))) ^ 2)]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hpt f ι i j l m]
  have hL : curvNormK g x k
      = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
          (Kpt g x k (fun s => onFrame g x (w s))) ^ 2 := by
    simp only [curvNormK]
    exact hsum (onFrame g x)
  have hR : (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC g x e k ι i j l m) ^ 2)
      = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
          (Kpt g x k (fun s => e (w s))) ^ 2 := hsum e
  rw [hL, hR]
  exact (frobSqN_frame_indep (k + 4) (KptLin hLC g x k) e (onFrame g x) hone honf).symm

end Work.Diff.EXT
