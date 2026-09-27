import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.projChartIndexOf
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.planePt
import Submission.Work.Drive.confProjVecOf_data_span
import Submission.Work.Drive.fderiv_smul_real_eq_zero_of_norm_eq_one
import Submission.Work.Drive.inf_map_eq_bot_iff

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# When is a projectivised map an immersion?

The counting chapter of the chain route has to decide whether the *class map* of a plane — the map
`z ↦ [V z] ∈ ℝP³` obtained by projectivising a smooth nowhere-vanishing vector field `V` — is an
**immersion** (`Work.Drive.planeClassDeriv_injective_iff`, the `hc` hypothesis of
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion`).  Mathlib has the
smoothness half of this dictionary (`Work.Drive.contMDiffAt_projMk`: smoothness of `z ↦ [V z]` is
smoothness of the ratios `(V z)_j / (V z)_i`), but not the differential half.

This file supplies it:

* `Work.Drive.projImmCoordL`, `Work.Drive.projCoordFunDeriv` — the derivative of the projective coordinates
  `projCoordFun i v = ((v_j/v_i))_{j ≠ i}`, namely `w ↦ ((w_j v_i - v_j w_i)/v_i²)_j`
  (`Work.Drive.hasFDerivAt_projCoordFun_pi`, `..._coord`);
* `Work.Drive.projCoordFunDeriv_eq_zero_iff` — **the kernel of that derivative is the line `ℝ∙v`**,
  which is the geometric content: the projective coordinates move only in the directions transverse to
  the line of `v`;
* `Work.Drive.mfderiv_chartAt_comp'` / `Work.Drive.fderiv_projChartMap_of_chartAt_eq'` — the chart
  bridge (a Mathlib gap) identifying `mfderiv` into `(ℝPⁿ, projCharted n)` with the Fréchet derivative
  of the composite with the concrete chart `projChartMap i`, for an arbitrary normed domain;
* **`Work.Drive.injective_mfderiv_projMk_iff`** — the criterion: for `V : E → ℝ^{n+1}` smooth at `z`
  with `V z ≠ 0`,

  > `z ↦ [V z]` is an immersion at `z`  ⟺  `∀ w, dV(z) w ∈ ℝ∙(V z) → w = 0`
  >  ⟺  `dV(z)` injective and `range dV(z) ⊓ ℝ∙(V z) = ⊥`.

  (For `E` two-dimensional the first form is the useful one: the derivative of `V` has no component
  along the line of `V`.)

This is the tool that turns the immersion hypothesis `hc` of the counting chapter into a *concrete
linear-algebra computation about the vector lift `V`* — no charts, no change-of-coordinates.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The projective coordinate function and its derivative -/

variable {n : ℕ}

/-- The `l`-th coordinate functional on `Eucl n = ℝ^{n+1}`. -/
def projImmCoordL (l : Fin (n + 1)) : Eucl n →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) l

@[simp] lemma projImmCoordL_apply (l : Fin (n + 1)) (v : Eucl n) : projImmCoordL l v = v.ofLp l := rfl

/-- The derivative of the projective coordinates `projCoordFun i` at `v`, as a linear map into the
coordinate space `Fin n → ℝ`: it is `w ↦ ((v_i · w_j − v_j · w_i)/v_i²)_j`. -/
def projCoordFunDeriv (i : Fin (n + 1)) (v : Eucl n) : Eucl n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin n =>
    (v.ofLp i)⁻¹ ^ 2 •
      ((v.ofLp i) • projImmCoordL (i.succAbove j) - (v.ofLp (i.succAbove j)) • projImmCoordL i))

lemma projCoordFunDeriv_apply (i : Fin (n + 1)) (v w : Eucl n) (j : Fin n) :
    projCoordFunDeriv i v w j
      = (v.ofLp i)⁻¹ ^ 2 * ((v.ofLp i) * w.ofLp (i.succAbove j)
          - (v.ofLp (i.succAbove j)) * w.ofLp i) := by
  simp [projCoordFunDeriv]

/-- **The derivative of one coordinate of the projective chart.** -/
lemma hasFDerivAt_projCoordFun_coord {i : Fin (n + 1)} {v : Eucl n} (hv : v.ofLp i ≠ 0)
    (j : Fin n) :
    HasFDerivAt (fun u : Eucl n => u.ofLp (i.succAbove j) / u.ofLp i)
      ((v.ofLp i)⁻¹ ^ 2 •
        ((v.ofLp i) • projImmCoordL (i.succAbove j) - (v.ofLp (i.succAbove j)) • projImmCoordL i)) v := by
  have h1 : HasFDerivAt (fun u : Eucl n => u.ofLp (i.succAbove j)) (projImmCoordL (i.succAbove j)) v :=
    (projImmCoordL (i.succAbove j)).hasFDerivAt
  have h2 : HasFDerivAt (fun u : Eucl n => (u.ofLp i)⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(v.ofLp i ^ 2)⁻¹) ∘SL projImmCoordL i) v :=
    (hasFDerivAt_inv hv).comp v (projImmCoordL i).hasFDerivAt
  have h := h1.mul h2
  have hdiv : HasFDerivAt (fun u : Eucl n => u.ofLp (i.succAbove j) / u.ofLp i) _ v :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => (div_eq_mul_inv _ _).symm))
  refine hdiv.congr_fderiv ?_
  ext w
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, projImmCoordL_apply, smul_eq_mul, sub_apply]
  field_simp
  ring

/-- **The derivative of the projective coordinate function** `projCoordFun i`, in the form of the
coordinate space `Fin n → ℝ`. -/
lemma hasFDerivAt_projCoordFun_pi {i : Fin (n + 1)} {v : Eucl n} (hv : v.ofLp i ≠ 0) :
    HasFDerivAt (fun u : Eucl n => fun j : Fin n => u.ofLp (i.succAbove j) / u.ofLp i)
      (projCoordFunDeriv i v) v := by
  refine (hasFDerivAt_pi (𝕜 := ℝ) (x := v)
    (φ := fun (j : Fin n) (u : Eucl n) => u.ofLp (i.succAbove j) / u.ofLp i)
    (φ' := fun (j : Fin n) => (v.ofLp i)⁻¹ ^ 2 •
      ((v.ofLp i) • projImmCoordL (i.succAbove j) - (v.ofLp (i.succAbove j)) • projImmCoordL i))).mpr ?_
  intro j
  exact hasFDerivAt_projCoordFun_coord hv j

/-- The derivative of `projCoordFun i` at `v` as a linear map into `EuclideanSpace ℝ (Fin n)`. -/
def projCoordFunDerivE (i : Fin (n + 1)) (v : Eucl n) :
    Eucl n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
      (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (projCoordFunDeriv i v)

/-- **The derivative of the projective coordinate function** `projCoordFun i`. -/
lemma hasFDerivAt_projCoordFun {i : Fin (n + 1)} {v : Eucl n} (hv : v.ofLp i ≠ 0) :
    HasFDerivAt (projCoordFun i) (projCoordFunDerivE i v) v := by
  have hiso : HasFDerivAt
      (⇑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm)
      (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
        (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (fun j : Fin n => v.ofLp (i.succAbove j) / v.ofLp i) :=
    ContinuousLinearEquiv.hasFDerivAt _
  have h := hiso.comp v (hasFDerivAt_projCoordFun_pi hv)
  have hfun : (fun u : Eucl n => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
      (fun j : Fin n => u.ofLp (i.succAbove j) / u.ofLp i)) = projCoordFun i := by
    funext u
    rw [PiLp.continuousLinearEquiv_symm_apply]
    rfl
  have h' : HasFDerivAt (fun u : Eucl n =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
        (fun j : Fin n => u.ofLp (i.succAbove j) / u.ofLp i)) (projCoordFunDerivE i v) v := h
  rwa [hfun] at h'

/-- **The kernel of the projective derivative is the line of `v`.**  The projective coordinates move
in exactly the directions transverse to `ℝ∙v`. -/
lemma projCoordFunDeriv_eq_zero_iff {i : Fin (n + 1)} {v : Eucl n} (hv : v.ofLp i ≠ 0)
    (w : Eucl n) :
    projCoordFunDeriv i v w = 0 ↔ w ∈ Submodule.span ℝ ({v} : Set (Eucl n)) := by
  constructor
  · intro h
    have hcomp : ∀ j : Fin n,
        v.ofLp i * w.ofLp (i.succAbove j) = v.ofLp (i.succAbove j) * w.ofLp i := by
      intro j
      have hj := congrFun h j
      rw [projCoordFunDeriv_apply] at hj
      have hne : (v.ofLp i)⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hv)
      have h0 := (mul_eq_zero.mp hj).resolve_left hne
      linarith [h0]
    have key : ∀ l : Fin (n + 1), w.ofLp l = (w.ofLp i / v.ofLp i) * v.ofLp l := by
      intro l
      rcases Fin.eq_self_or_eq_succAbove i l with h | ⟨j, hj⟩
      · rw [h, div_mul_cancel₀ _ hv]
      · rw [hj]
        have hj' := hcomp j
        field_simp
        linarith [hj']
    refine Submodule.mem_span_singleton.mpr ⟨w.ofLp i / v.ofLp i, ?_⟩
    refine WithLp.ofLp_injective 2 ?_
    funext l
    rw [PiLp.smul_apply, smul_eq_mul]
    exact (key l).symm
  · intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    rw [← hc]
    funext j
    rw [projCoordFunDeriv_apply]
    simp only [PiLp.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-! ## 2. The chart bridge in a charted manifold, and the immersion criterion -/

section Criterion

attribute [local instance] Work.Drive.projCharted

variable {k : ℕ}

/-- **The chart bridge in a charted `m`-manifold**, for an arbitrary normed domain: the derivative of
`chartAt p ∘ f` is the manifold derivative of `f` composed with the change-of-coordinates map. -/
theorem mfderiv_chartAt_comp' {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : EuclideanSpace ℝ (Fin k) → M) {s : EuclideanSpace ℝ (Fin k)}
    (hf : ContMDiffAt (𝓡 k) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞) f s) (p : M)
    (hs : f s ∈ (chartAt (EuclideanSpace ℝ (Fin m)) p).source) :
    mfderiv (𝓡 k) (𝓡 m) (fun u => chartAt (EuclideanSpace ℝ (Fin m)) p (f u)) s
      = (tangentCoordChange (𝓡 m) (f s) p (f s)).comp (mfderiv (𝓡 k) (𝓡 m) f s) := by
  have hφ : MDifferentiableAt (𝓡 m) (𝓡 m) (chartAt (EuclideanSpace ℝ (Fin m)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓡 k) (𝓡 m) f s := hf.mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- **The derivative of the composite with a projective chart.**  When `projChart i` is the chart of
the transparent projective structure at the value `g z`, the Fréchet derivative of
`projChartMap i ∘ g` *is* the manifold derivative of `g` (the change of coordinates at the own chart
point is the identity). -/
theorem fderiv_projChartMap_of_chartAt_eq' {n : ℕ}
    (g : EuclideanSpace ℝ (Fin k) → Projectivization ℝ (Eucl n))
    (z : EuclideanSpace ℝ (Fin k))
    (hg : ContMDiffAt (𝓡 k) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) g z) (i : Fin (n + 1))
    (hchart : (@chartAt (EuclideanSpace ℝ (Fin n)) _ (Projectivization ℝ (Eucl n)) _
        (Work.Drive.projCharted n) (g z) :
        OpenPartialHomeomorph (Projectivization ℝ (Eucl n)) (EuclideanSpace ℝ (Fin n)))
      = Work.Drive.projChart i) :
    fderiv ℝ (fun y => Work.Drive.projChartMap i (g y)) z =
      mfderiv (𝓡 k) (𝓡 n) g z := by
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl n)) :=
    Work.Drive.isManifold_projCharted n
  have hs : g z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (g z)).source := mem_chart_source _ _
  have h1 := mfderiv_chartAt_comp' g hg (g z) hs
  have h3 : (fun y : EuclideanSpace ℝ (Fin k) => Work.Drive.projChartMap i (g y)) =
      fun y => chartAt (EuclideanSpace ℝ (Fin n)) (g z) (g y) := by
    funext y
    simp only [hchart, Work.Drive.projChart_apply]
  rw [h3, ← mfderiv_eq_fderiv, h1]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply]
  exact tangentCoordChange_self (I := 𝓡 n) (x := g z) (z := g z)
    (v := (mfderiv (𝓡 k) (𝓡 n) g z) v) (mem_extChartAt_source (g z))

/-- The defining computation rule of `projCoordFunDerivE`. -/
@[simp] lemma projCoordFunDerivE_apply (i : Fin (n + 1)) (v w : Eucl n) :
    projCoordFunDerivE i v w
      = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
          (projCoordFunDeriv i v w) := rfl

/-- **The kernel of `projCoordFunDerivE` is the line of `v`.** -/
lemma projCoordFunDerivE_eq_zero_iff {i : Fin (n + 1)} {v : Eucl n} (hv : v.ofLp i ≠ 0)
    (w : Eucl n) :
    projCoordFunDerivE i v w = 0 ↔ w ∈ Submodule.span ℝ ({v} : Set (Eucl n)) := by
  have key : (projCoordFunDerivE i v w = 0) ↔ (projCoordFunDeriv i v w = 0) := by
    rw [projCoordFunDerivE_apply]
    refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.injective (by
      rw [h, map_zero])
  rw [key, projCoordFunDeriv_eq_zero_iff hv w]

/-- **Injectivity of a composition of continuous linear maps.** -/
lemma injective_comp_iff {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (M : E →L[ℝ] F) :
    Function.Injective (L.comp M) ↔ ∀ w : E, L (M w) = 0 → w = 0 := by
  constructor
  · intro h w hw
    refine h ?_
    show (L.comp M) w = (L.comp M) 0
    simp only [ContinuousLinearMap.comp_apply, map_zero, hw]
  · intro h w w' hww
    have hsub : L (M (w - w')) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact hww
    exact sub_eq_zero.mp (h (w - w') hsub)

/-- **THE IMMERSION CRITERION.**  For a smooth nowhere-vanishing vector field `V : ℝᵏ → ℝ^{n+1}`, the
projectivisation `z ↦ [V z]` is an immersion at `z` if and only if the derivative of `V` at `z` has
no component along the line of `V z`. -/
theorem injective_mfderiv_projMk_iff {n : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl n)
    (hV : ∀ x, V x ≠ 0) (z : EuclideanSpace ℝ (Fin k))
    (hVs : ContMDiffAt (𝓡 k) (𝓘(ℝ, Eucl n)) ((⊤ : ℕ∞) : WithTop ℕ∞) V z) :
    Function.Injective (mfderiv (𝓡 k) (𝓡 n)
        (fun x => Projectivization.mk ℝ (V x) (hV x)) z)
      ↔ ∀ w : EuclideanSpace ℝ (Fin k),
          fderiv ℝ V z w ∈ Submodule.span ℝ ({V z} : Set (Eucl n)) → w = 0 := by
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl n)) :=
    Work.Drive.isManifold_projCharted n
  have hpcd : ContMDiffAt (𝓡 k) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Projectivization.mk ℝ (V x) (hV x)) z :=
    Work.Drive.contMDiffAt_projMk V hV z hVs
  set i : Fin (n + 1) := Work.Drive.projChartIndexOf (Projectivization.mk ℝ (V z) (hV z))
  have hvi : (V z).ofLp i ≠ 0 :=
    (Work.Drive.mem_projChartSource_iff' (hV z)).mp
      (Work.Drive.projChartIndexOf_spec (Projectivization.mk ℝ (V z) (hV z)))
  have hchart : (@chartAt (EuclideanSpace ℝ (Fin n)) _ (Projectivization ℝ (Eucl n)) _
      (Work.Drive.projCharted n) (Projectivization.mk ℝ (V z) (hV z)) :
      OpenPartialHomeomorph (Projectivization ℝ (Eucl n)) (EuclideanSpace ℝ (Fin n)))
      = Work.Drive.projChart i :=
    Work.Drive.projCharted_chartAt_eq_projChart _
  have hmf : mfderiv (𝓡 k) (𝓡 n)
        (fun x => Projectivization.mk ℝ (V x) (hV x)) z
      = fderiv ℝ (fun u => Work.Drive.projCoordFun i (V u)) z :=
    (fderiv_projChartMap_of_chartAt_eq' (fun x => Projectivization.mk ℝ (V x) (hV x)) z
      hpcd i hchart).symm
  have hVd : DifferentiableAt ℝ V z :=
    (contMDiffAt_iff_contDiffAt.mp hVs).differentiableAt (by norm_num)
  have hchain : fderiv ℝ (fun u => Work.Drive.projCoordFun i (V u)) z
      = (projCoordFunDerivE i (V z)).comp (fderiv ℝ V z) :=
    ((hasFDerivAt_projCoordFun hvi).comp z hVd.hasFDerivAt).fderiv
  have key : Function.Injective ((projCoordFunDerivE i (V z)).comp (fderiv ℝ V z))
      ↔ ∀ w : EuclideanSpace ℝ (Fin k),
          fderiv ℝ V z w ∈ Submodule.span ℝ ({V z} : Set (Eucl n)) → w = 0 := by
    refine (injective_comp_iff (projCoordFunDerivE i (V z)) (fderiv ℝ V z)).trans ?_
    constructor
    · intro h w hw
      exact h w ((projCoordFunDerivE_eq_zero_iff hvi (fderiv ℝ V z w)).mpr hw)
    · intro h w hw
      exact h w ((projCoordFunDerivE_eq_zero_iff hvi (fderiv ℝ V z w)).mp hw)
  rw [hmf, hchain]
  exact key

/-- **The immersion criterion, in range form.** -/
theorem injective_mfderiv_projMk_iff' {n : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl n)
    (hV : ∀ x, V x ≠ 0) (z : EuclideanSpace ℝ (Fin k))
    (hVs : ContMDiffAt (𝓡 k) (𝓘(ℝ, Eucl n)) ((⊤ : ℕ∞) : WithTop ℕ∞) V z) :
    Function.Injective (mfderiv (𝓡 k) (𝓡 n)
        (fun x => Projectivization.mk ℝ (V x) (hV x)) z)
      ↔ Function.Injective (fderiv ℝ V z) ∧
        (fderiv ℝ V z).range ⊓ Submodule.span ℝ ({V z} : Set (Eucl n)) = ⊥ := by
  rw [injective_mfderiv_projMk_iff V hV z hVs]
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, ?_⟩
    · have hz : fderiv ℝ V z (a - b) = 0 := by rw [map_sub, hab, sub_self]
      exact sub_eq_zero.mp (h (a - b) (by rw [hz]; exact Submodule.zero_mem _))
    · refine (Submodule.eq_bot_iff _).mpr ?_
      rintro x ⟨hxr, hxs⟩
      obtain ⟨w, rfl⟩ := hxr
      rw [h w hxs, map_zero]
  · rintro ⟨hinj, hbot⟩ w hw
    have hmem : fderiv ℝ V z w ∈
        (fderiv ℝ V z).range ⊓ Submodule.span ℝ ({V z} : Set (Eucl n)) :=
      ⟨⟨w, rfl⟩, hw⟩
    rw [hbot] at hmem
    exact hinj (by rw [(Submodule.mem_bot ℝ).mp hmem, map_zero])

end Criterion


/-! ## 3. The disk coordinate of the plane as a point of `ℝ²`

The concrete class maps of the capped plane are functions of a complex *disk coordinate* `d`; to feed
them to the criterion of §2 (whose domain is `ℝᵏ`) we identify `ℂ` with `ℝ²` by
`Work.Drive.cplxOf`. -/

section DiskCoord

/-- The complex disk coordinate of a point of `ℝ²`. -/
def cplxOf (x : EuclideanSpace ℝ (Fin 2)) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

@[simp] lemma cplxOf_apply (x : EuclideanSpace ℝ (Fin 2)) : cplxOf x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := rfl

@[simp] lemma cplxOf_re (x : EuclideanSpace ℝ (Fin 2)) : (cplxOf x).re = x 0 := by
  simp [cplxOf]

@[simp] lemma cplxOf_im (x : EuclideanSpace ℝ (Fin 2)) : (cplxOf x).im = x 1 := by
  simp [cplxOf]

lemma cplxOf_injective : Function.Injective cplxOf := by
  intro x y h
  have h1 : x 0 = y 0 := by rw [← cplxOf_re x, ← cplxOf_re y, h]
  have h2 : x 1 = y 1 := by rw [← cplxOf_im x, ← cplxOf_im y, h]
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  · exact h1
  · exact h2

lemma contDiff_cplxOf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cplxOf := by
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin 2) => (y 0 : ℝ)) :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 |>.contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin 2) => (y 1 : ℝ)) :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 |>.contDiff
  have h : cplxOf = fun y : EuclideanSpace ℝ (Fin 2) =>
      ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
    funext y; rfl
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp h0).add
    ((Complex.ofRealCLM.contDiff.comp h1).mul contDiff_const)

lemma continuous_cplxOf : Continuous cplxOf := contDiff_cplxOf.continuous

end DiskCoord


/-! ## 5. The end-to-end interface for `hc`

Combining the criterion of §2 with the data form of the plane's class lift
(`Work.Drive.confProjVecOf_data_span`): **the class map of a plane presented through the unified point
`Work.Drive.planePt` with data `(u, r, d)` is an immersion as soon as the *data* map
`z ↦ (u z, d z)` has no non-zero direction in which `u` moves only radially while `d` stands still.**
No chart and no projective geometry is left in the statement. -/

section EndToEnd

attribute [local instance] Work.Drive.projCharted

/-- **`hc` from the data of the plane presentation.**  For a `C^∞` data pair `(U, D)` with `U` valued
in the unit circle and `D` in the disk `‖D‖ < √2`, if the only direction in which `U` moves radially
(`dU(x) w ∈ ℝ∙U x`) while `D` stands still (`dD(x) w = 0`) is the zero direction, then the
projectivised class lift `x ↦ [confProjVecOf (U x) (D x)]` is an immersion at every `x`. -/
theorem injective_mfderiv_projMk_confProjVecOf_data {U D : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hU : ∀ x, ‖U x‖ = 1) (hD : ∀ x, 0 < 1 - ‖D x‖ ^ 2 / 2)
    (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hDd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hι : ∀ x w, (∃ l : ℝ, fderiv ℝ U x w = l • U x) → fderiv ℝ D x w = 0 → w = 0)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y => Projectivization.mk ℝ (Work.Drive.confProjVecOf (U y) (D y))
        (Work.Drive.confProjVecOf_ne_zero_of_norm_eq_one (hU y) (D y))) x) := by
  refine (injective_mfderiv_projMk_iff (fun y => Work.Drive.confProjVecOf (U y) (D y))
    (fun y => Work.Drive.confProjVecOf_ne_zero_of_norm_eq_one (hU y) (D y)) x ?_).mpr
    (fun w hw => Work.Drive.confProjVecOf_data_span hU hD hUd hDd hι x hw)
  rw [contMDiffAt_iff_contDiffAt]
  exact Work.Drive.contDiffAt_confProjVecOf' hUd.contDiffAt hDd.contDiffAt (ne_of_gt (hD x))

/-- **The hypothesis of the interface, in the form the route verifies it.**  For a circle-valued `U`
the antecedent `dU(x) w ∈ ℝ∙U x` already forces `dU(x) w = 0`
(`Work.Drive.fderiv_smul_real_eq_zero_of_norm_eq_one`), so the condition `hι` of the interface is
exactly *the joint kernel of the two data differentials is zero*, i.e. the data map is immersive. -/
theorem data_span_hι_of_joint_kernel {U D : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hU : ∀ x, ‖U x‖ = 1) (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U) (x : EuclideanSpace ℝ (Fin 2))
    (h : ∀ w, fderiv ℝ U x w = 0 → fderiv ℝ D x w = 0 → w = 0) :
    ∀ w, (∃ l : ℝ, fderiv ℝ U x w = l • U x) → fderiv ℝ D x w = 0 → w = 0 := by
  rintro w ⟨l, hl⟩ hw
  have hl0 : l = 0 := Work.Drive.fderiv_smul_real_eq_zero_of_norm_eq_one hU
    (hUd.contDiffAt.differentiableAt (by norm_num)) hl
  rw [hl0, zero_smul] at hl
  exact h w hl hw

end EndToEnd


/-! ## 6. The range of the class derivative, and the `hV` reduction

The companion of the criterion for the **general-position** hypothesis `hV` of the counting chapter:
the range of the class derivative `mfderiv (mk ∘ V) z` is the image, under the projective quotient
`projCoordFunDerivE i (V z)` (whose kernel is the line `ℝ∙(V z)`, §1), of the range of the lift's
derivative.  With `Work.Drive.inf_map_eq_bot_iff` this turns `hV` into a statement about the *lift*:
three `2`-planes of `ℝ⁴` through the common line `ℝv` meet in exactly that line. -/

section Range

attribute [local instance] Work.Drive.projCharted

/-- **The range of the class derivative is the projective quotient of the lift's derivative range.** -/
theorem range_mfderiv_projMk {n k : ℕ} (V : EuclideanSpace ℝ (Fin k) → Eucl n)
    (hV : ∀ x, V x ≠ 0) (z : EuclideanSpace ℝ (Fin k))
    (hVs : ContMDiffAt (𝓡 k) (𝓘(ℝ, Eucl n)) ((⊤ : ℕ∞) : WithTop ℕ∞) V z) :
    LinearMap.range (mfderiv (𝓡 k) (𝓡 n)
        (fun x => Projectivization.mk ℝ (V x) (hV x)) z).toLinearMap
      = Submodule.map (projCoordFunDerivE
            (Work.Drive.projChartIndexOf (Projectivization.mk ℝ (V z) (hV z))) (V z)).toLinearMap
          (LinearMap.range (fderiv ℝ V z).toLinearMap) := by
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl n)) :=
    Work.Drive.isManifold_projCharted n
  have hpcd : ContMDiffAt (𝓡 k) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Projectivization.mk ℝ (V x) (hV x)) z :=
    Work.Drive.contMDiffAt_projMk V hV z hVs
  set i : Fin (n + 1) := Work.Drive.projChartIndexOf (Projectivization.mk ℝ (V z) (hV z))
  have hvi : (V z).ofLp i ≠ 0 :=
    (Work.Drive.mem_projChartSource_iff' (hV z)).mp
      (Work.Drive.projChartIndexOf_spec (Projectivization.mk ℝ (V z) (hV z)))
  have hchart : (@chartAt (EuclideanSpace ℝ (Fin n)) _ (Projectivization ℝ (Eucl n)) _
      (Work.Drive.projCharted n) (Projectivization.mk ℝ (V z) (hV z)) :
      OpenPartialHomeomorph (Projectivization ℝ (Eucl n)) (EuclideanSpace ℝ (Fin n)))
      = Work.Drive.projChart i :=
    Work.Drive.projCharted_chartAt_eq_projChart _
  have hmf : mfderiv (𝓡 k) (𝓡 n) (fun x => Projectivization.mk ℝ (V x) (hV x)) z
      = fderiv ℝ (fun u => Work.Drive.projCoordFun i (V u)) z :=
    (fderiv_projChartMap_of_chartAt_eq' (fun x => Projectivization.mk ℝ (V x) (hV x)) z
      hpcd i hchart).symm
  have hchain : fderiv ℝ (fun u => Work.Drive.projCoordFun i (V u)) z
      = (projCoordFunDerivE i (V z)).comp (fderiv ℝ V z) :=
    ((hasFDerivAt_projCoordFun hvi).comp z
      (((contMDiffAt_iff_contDiffAt.mp hVs).differentiableAt (by norm_num)).hasFDerivAt)).fderiv
  rw [hmf, hchain]
  rw [show (projCoordFunDerivE i (V z) ∘SL fderiv ℝ V z).toLinearMap
      = (projCoordFunDerivE i (V z)).toLinearMap.comp (fderiv ℝ V z).toLinearMap from rfl]
  exact LinearMap.range_comp _ _

/-- **The `hV` criterion in the form the route uses.**  For a quotient map `π` with
`ker π = ℝ∙v` and three linear maps `M k`, the three projective images meet in `⊥` **iff** the three
ambient planes `range (M k) + ℝ∙v` meet in exactly the line `ℝ∙v`. -/
theorem inf_range_comp_eq_bot_iff {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (π : E →L[ℝ] E') {v : E}
    (hker : LinearMap.ker π.toLinearMap = Submodule.span ℝ ({v} : Set E))
    (M : Fin 3 → E →L[ℝ] E) :
    (LinearMap.range (π.comp (M 0)).toLinearMap ⊓ LinearMap.range (π.comp (M 1)).toLinearMap ⊓
        LinearMap.range (π.comp (M 2)).toLinearMap = ⊥)
      ↔ (LinearMap.range (M 0).toLinearMap ⊔ Submodule.span ℝ ({v} : Set E)) ⊓
          (LinearMap.range (M 1).toLinearMap ⊔ Submodule.span ℝ ({v} : Set E)) ⊓
          (LinearMap.range (M 2).toLinearMap ⊔ Submodule.span ℝ ({v} : Set E))
        = Submodule.span ℝ ({v} : Set E) := by
  have hv0 : π v = 0 :=
    LinearMap.mem_ker.mp (by rw [hker]; exact Submodule.mem_span_singleton_self v)
  have hv : (↑π : E → E') v = 0 := hv0
  have hW : ∀ k : Fin 3, Submodule.span ℝ ({v} : Set E) ≤
      (LinearMap.range (M k).toLinearMap ⊔ Submodule.span ℝ ({v} : Set E)) :=
    fun k => le_sup_right
  have hmap : ∀ k : Fin 3,
      Submodule.map π.toLinearMap
          (LinearMap.range (M k).toLinearMap ⊔ Submodule.span ℝ ({v} : Set E))
        = LinearMap.range (π.comp (M k)).toLinearMap := by
    intro k
    simp only [Submodule.map_sup, Submodule.map_span, Set.image_singleton,
      ContinuousLinearMap.coe_coe, hv0, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp]
    simp
  have h := inf_map_eq_bot_iff π hker (fun k => LinearMap.range (M k).toLinearMap ⊔
    Submodule.span ℝ ({v} : Set E)) hW
  rw [hmap 0, hmap 1, hmap 2] at h
  exact h

end Range

end

end Work.Drive
