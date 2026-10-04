import Mathlib
import Submission.Work.Diff.ODE.Basic

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Global existence of the flow of a jointly smooth time-dependent vector field

The contract this file establishes is `Work.Diff.ODE.exists_isXCurve`: on a compact manifold every
jointly smooth time-dependent vector field `X` has, through every point `(a, y)`, an integral curve
defined for all (elapsed) times.

The hypotheses of the target are *local*: `hBox` provides a local flow box around every `(a, y)` and
`hUniq` provides uniqueness of solutions with the same initial data.  Neither is enough on its own;
the proof glues the local pieces along the time axis.

## Layout

All work is done in **absolute time**: `IsXSolOn X γ s` says that `γ` solves `γ' = X t (γ t)` for
`t ∈ s` (whereas the elapsed-time notion `IsXCurveOn X a y T γ` of `Basic.lean` reads
`γ' τ = X (a + τ) (γ τ)` for `|τ| < T`).  The two are converted into one another by the chain-rule
lemmas below.

The field `X` is then replaced by its *shift* `shiftX X a = fun τ => X (a + τ)`, for which an
elapsed solution with base time `a` is literally an absolute-time solution.  For `shiftX X a`:
* `exists_uniform_local` (proved from `hBox` and compactness of `M`) gives a uniform local existence
  time on every compact set of base times;
* `isXSolOn_piecewise` glues two solutions over overlapping intervals (using `hUniq` for the local
  uniqueness);
* `agreeOnIntervals_of_localUniq` propagates agreement of two solutions from one common point to
  their whole common interval;
* `exists_isXSolOn_extend` extends one solution a little to the right;
* `exists_isXSolOn_right` (the main argument of this file, a maximality argument) produces a
  solution valid on `Ioo L T` for every `T` for some `L < a`, and its time-reverse produces one
  valid on `Ioo T R` for every `T` for some `R > a`; the two are glued at the initial point.

## Tags

integral curve, ODE, flow box, existence
-/

noncomputable section

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Set Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Solution predicates in absolute time -/

/-- `IsXSolOn X γ s`: the curve `γ` solves the ODE of the time-dependent field `X` in absolute time,
i.e. `γ' t = X t (γ t)` for all `t ∈ s`. -/
def IsXSolOn (X : ℝ → Π x : M, TangentSpace I x) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt 𝓘(ℝ,ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))

/-- `IsXSol X γ`: the curve `γ` solves the ODE of `X` in absolute time for all times. -/
def IsXSol (X : ℝ → Π x : M, TangentSpace I x) (γ : ℝ → M) : Prop :=
  ∀ t, HasMFDerivAt 𝓘(ℝ,ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))

/-- Local uniqueness of solutions of the absolute-time ODE of `X`, at every initial condition. -/
def LocalUniq (X : ℝ → Π x : M, TangentSpace I x) : Prop :=
  ∀ {σ T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
    IsXSolOn X γ (Ioo (σ - T) (σ + T)) → IsXSolOn X γ' (Ioo (σ - T) (σ + T)) →
    γ σ = γ' σ → EqOn γ γ' (Ioo (σ - T) (σ + T))

/-- Two solutions of `X` that agree at an interior common point agree on their whole common
interval. -/
def AgreeOnIntervals (X : ℝ → Π x : M, TangentSpace I x) : Prop :=
  ∀ {γ γ' : ℝ → M} {A B A' B' t₀ : ℝ}, IsXSolOn X γ (Ioo A B) → IsXSolOn X γ' (Ioo A' B') →
    t₀ ∈ Ioo A B ∩ Ioo A' B' → γ t₀ = γ' t₀ → EqOn γ γ' (Ioo (max A A') (min B B'))

/-- Uniform local existence in absolute time: on every compact set of initial times there is a
positive common existence time around every initial point. -/
def UnifLocalAbs (X : ℝ → Π x : M, TangentSpace I x) : Prop :=
  ∀ K : Set ℝ, IsCompact K → ∃ d : ℝ, 0 < d ∧
    ∀ σ ∈ K, ∀ z : M, ∃ Γ : ℝ → M, Γ σ = z ∧ IsXSolOn X Γ (Ioo (σ - d) (σ + d))

/-- The field `X` shifted in time by `a`.  Elapsed solutions of `X` with base time `a + σ` are
exactly absolute solutions of `shiftX X a` around `σ`. -/
def shiftX (X : ℝ → Π x : M, TangentSpace I x) (a : ℝ) : ℝ → Π x : M, TangentSpace I x :=
  fun τ => X (a + τ)

/-- The time-reversal of the field `X`: solutions of `revX X` are time-reversed solutions of `X`. -/
def revX (X : ℝ → Π x : M, TangentSpace I x) : ℝ → Π x : M, TangentSpace I x :=
  fun t => -X (-t)

/-! ## Chain rules for translating the time parameter -/

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule: differentiating `t ↦ f (σ + t)` at `τ`. -/
lemma hasMFDerivAt_comp_const_add {f : ℝ → M} {σ τ : ℝ}
    {F : TangentSpace 𝓘(ℝ,ℝ) (σ + τ) →L[ℝ] TangentSpace I (f (σ + τ))}
    (h : HasMFDerivAt 𝓘(ℝ,ℝ) I f (σ + τ) F) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => f (σ + u)) τ F := by
  rw [← ContinuousLinearMap.comp_id F]
  have hinner : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => σ + u) τ
      (ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hasFDerivAt_id τ).const_add σ
  exact h.comp τ hinner

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule: differentiating `t ↦ f (t + σ)` at `τ`. -/
lemma hasMFDerivAt_comp_add_const {f : ℝ → M} {σ τ : ℝ}
    {F : TangentSpace 𝓘(ℝ,ℝ) (τ + σ) →L[ℝ] TangentSpace I (f (τ + σ))}
    (h : HasMFDerivAt 𝓘(ℝ,ℝ) I f (τ + σ) F) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => f (u + σ)) τ F := by
  rw [← ContinuousLinearMap.comp_id F]
  have hinner : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => u + σ) τ
      (ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hasFDerivAt_id τ).add_const σ
  exact h.comp τ hinner

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule: differentiating `t ↦ f (t - σ)` at `τ`. -/
lemma hasMFDerivAt_comp_sub_const {f : ℝ → M} {σ τ : ℝ}
    {F : TangentSpace 𝓘(ℝ,ℝ) (τ - σ) →L[ℝ] TangentSpace I (f (τ - σ))}
    (h : HasMFDerivAt 𝓘(ℝ,ℝ) I f (τ - σ) F) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => f (u - σ)) τ F := by
  rw [← ContinuousLinearMap.comp_id F]
  have hinner : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => u - σ) τ
      (ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hasFDerivAt_id τ).sub_const σ
  exact h.comp τ hinner

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule for time reversal: a solution at time `t` gives a solution of the negated field at
time `-t`. -/
lemma hasMFDerivAt_comp_neg {f : ℝ → M} {t : ℝ} {w : TangentSpace I (f t)}
    (h : HasMFDerivAt 𝓘(ℝ,ℝ) I f t ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => f (-u)) (-t) ((1 : ℝ →L[ℝ] ℝ).smulRight (-w)) := by
  have h' : HasMFDerivAt 𝓘(ℝ,ℝ) I f (-(-t)) ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    rw [neg_neg]; exact h
  have hinner : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => -u) (-t) (-1 : ℝ →L[ℝ] ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hasFDerivAt_id (-t)).neg
  have hcomp := h'.comp (-t) hinner
  have hderiv : ((1 : ℝ →L[ℝ] ℝ).smulRight w) ∘SL (-1 : ℝ →L[ℝ] ℝ)
      = (1 : ℝ →L[ℝ] ℝ).smulRight (-w) := by
    ext v
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hderiv] at hcomp
  exact hcomp

/-! ## Conversions between elapsed and absolute time -/

/-- An elapsed solution of `X` with base time `σ` is an absolute solution of `X` (after the
translation `t ↦ t - σ`). -/
lemma isXSolOn_comp_sub_of_isXCurveOn {X : ℝ → Π x : M, TangentSpace I x} {σ T : ℝ} {z : M}
    {η : ℝ → M} (h : IsXCurveOn X σ z T η) :
    IsXSolOn X (fun t => η (t - σ)) (Ioo (σ - T) (σ + T)) := by
  intro t ht
  have hτ : |t - σ| < T := by
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := hasMFDerivAt_comp_sub_const (σ := σ) (τ := t) (h.2 (t - σ) hτ)
  have heq : σ + (t - σ) = t := by ring
  simpa [heq] using hd

/-- An absolute solution of `X` around `σ` is an elapsed solution of `X` with base time `σ`. -/
lemma isXCurveOn_of_isXSolOn {X : ℝ → Π x : M, TangentSpace I x} {Γ : ℝ → M} {σ T : ℝ} {z : M}
    (h : IsXSolOn X Γ (Ioo (σ - T) (σ + T))) (h0 : Γ σ = z) :
    IsXCurveOn X σ z T (fun u => Γ (σ + u)) := by
  refine ⟨?_, fun τ hτ => ?_⟩
  · simpa using h0
  · have hτ' := abs_lt.mp hτ
    have hmem : σ + τ ∈ Ioo (σ - T) (σ + T) :=
      ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
    exact hasMFDerivAt_comp_const_add (σ := σ) (τ := τ) (h (σ + τ) hmem)

/-- The elapsed solution produced by a local box. -/
lemma isXCurveOn_of_localBox {X : ℝ → Π x : M, TangentSpace I x} {B : LocalBox X} {a : ℝ}
    {y : M} (h : (a, y) ∈ B.U) :
    IsXCurveOn X a y (2 * B.δ) (fun τ => B.FL τ a y) :=
  ⟨B.hzero a y h, fun τ hτ => B.hode a y h τ (le_of_lt hτ)⟩

/-- Elapsed solutions of `shiftX X a` with base time `σ` are elapsed solutions of `X` with base time
`a + σ`. -/
lemma isXCurveOn_shiftX_iff {X : ℝ → Π x : M, TangentSpace I x} {a σ T : ℝ} {z : M}
    {η : ℝ → M} :
    IsXCurveOn (shiftX X a) σ z T η ↔ IsXCurveOn X (a + σ) z T η := by
  simp only [IsXCurveOn, shiftX, add_assoc]

/-- `IsXCurve` of the shifted field at base time `0` is `IsXCurve` of `X` at base time `a`. -/
lemma isXCurve_shiftX_iff {X : ℝ → Π x : M, TangentSpace I x} {a : ℝ} {y : M} {γ : ℝ → M} :
    IsXCurve (shiftX X a) 0 y γ ↔ IsXCurve X a y γ := by
  simp only [IsXCurve, shiftX, zero_add]

/-- `IsXCurve` at base time `0` is `IsXSol`. -/
lemma isXCurve_iff_isXSol {Y : ℝ → Π x : M, TangentSpace I x} {y : M} {γ : ℝ → M} :
    IsXCurve Y 0 y γ ↔ γ 0 = y ∧ IsXSol Y γ := by
  simp only [IsXCurve, IsXSol, zero_add]

/-- Solutions of `X` pull back to solutions of `shiftX X a` along `t ↦ a + t` (on intervals). -/
lemma isXSolOn_shiftX_of_isXSolOn_Ioo {X : ℝ → Π x : M, TangentSpace I x} {Γ : ℝ → M}
    {c e : ℝ} {a : ℝ} (h : IsXSolOn X Γ (Ioo c e)) :
    IsXSolOn (shiftX X a) (fun t => Γ (a + t)) (Ioo (c - a) (e - a)) := by
  intro t ht
  have hmem : a + t ∈ Ioo c e := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact hasMFDerivAt_comp_const_add (σ := a) (τ := t) (h (a + t) hmem)

/-- An elapsed solution of `X` with base time `a + σ` gives an absolute solution of `shiftX X a`
around `σ`. -/
lemma isXSolOn_shiftX_of_isXCurveOn {X : ℝ → Π x : M, TangentSpace I x} {a σ d : ℝ} {z : M}
    {η : ℝ → M} (h : IsXCurveOn X (a + σ) z d η) :
    IsXSolOn (shiftX X a) (fun t => η (t - σ)) (Ioo (σ - d) (σ + d)) := by
  intro t ht
  have hτ : |t - σ| < d := by
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hd := hasMFDerivAt_comp_sub_const (σ := σ) (τ := t) (h.2 (t - σ) hτ)
  have heq : (a + σ) + (t - σ) = a + t := by ring
  simpa [shiftX, heq] using hd

/-- The shifted field inherits uniformity of local existence. -/
lemma unifLocalAbs_shiftX {X : ℝ → Π x : M, TangentSpace I x} (h : UnifLocalAbs X) (a : ℝ) :
    UnifLocalAbs (shiftX X a) := by
  intro K hK
  obtain ⟨d, hd, hd'⟩ := h ((fun σ => a + σ) '' K) (hK.image (continuous_const_add a))
  refine ⟨d, hd, fun σ hσ z => ?_⟩
  obtain ⟨Γ, hΓ0, hΓ⟩ := hd' (a + σ) (mem_image_of_mem _ hσ) z
  refine ⟨fun t => Γ (a + t), by simpa using hΓ0, ?_⟩
  have := isXSolOn_shiftX_of_isXSolOn_Ioo (a := a) (c := a + σ - d) (e := a + σ + d) hΓ
  convert this using 2 <;> ring

/-- The shifted field inherits local uniqueness, granted uniqueness of elapsed solutions of `X`. -/
lemma localUniq_shiftX_of_hUniq {X : ℝ → Π x : M, TangentSpace I x}
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T))
    (a : ℝ) : LocalUniq (shiftX X a) := by
  intro σ T hT γ γ' hγ hγ' h0
  have h1 : IsXCurveOn X (a + σ) (γ σ) T (fun u => γ (σ + u)) :=
    (isXCurveOn_shiftX_iff).mp (isXCurveOn_of_isXSolOn hγ rfl)
  have h2 : IsXCurveOn X (a + σ) (γ σ) T (fun u => γ' (σ + u)) :=
    (isXCurveOn_shiftX_iff).mp (isXCurveOn_of_isXSolOn hγ' h0.symm)
  have h3 := hUniq hT h1 h2
  intro t ht
  have hu : t - σ ∈ Ioo (-T) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h4 := h3 hu
  simpa only [show σ + (t - σ) = t from by ring] using h4

/-! ## Auxiliary lemmas

The team proved general versions of the following lemmas in the sibling files
`exists_uniform_local.lean`, `agreeOnIntervals_of_localUniq.lean`, `isXSolOn_piecewise.lean`,
`isXSolOn_revX.lean`, `localUniq_revX.lean` and `unifLocalAbs_revX.lean`.  As those files import
*this* one (for the definitions they are stated with), they cannot be imported here; the proofs are
therefore reproduced below, under different names, so that this file is self-contained. -/

/-- **Uniform local existence in absolute time.**  From local flow boxes around every point of
`ℝ × M` we get a uniform existence time on every compact set of initial times (compactness of
`K × M` and the minimum of finitely many box radii). -/
theorem unifLocalAbs_of_boxes [CompactSpace M] {X : ℝ → Π x : M, TangentSpace I x}
    (hBox : ∀ a y, ∃ B : LocalBox X, (a, y) ∈ B.U) : UnifLocalAbs X := by
  classical
  intro K hK
  choose B hB using fun p : ℝ × M => hBox p.1 p.2
  have hKc : IsCompact (K ×ˢ (Set.univ : Set M)) := hK.prod isCompact_univ
  obtain ⟨t, ht⟩ : ∃ t : Finset (ℝ × M), K ×ˢ (Set.univ : Set M) ⊆ ⋃ p ∈ t, (B p).U :=
    hKc.elim_finite_subcover (fun p => (B p).U) (fun p => (B p).hU)
      (fun q _ => Set.mem_iUnion.mpr ⟨q, hB q⟩)
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, one_pos, fun σ hσ z => ?_⟩
    exact absurd (ht (show (σ, z) ∈ K ×ˢ (Set.univ : Set M) from ⟨hσ, Set.mem_univ z⟩))
      (by simp)
  · refine ⟨t.inf' hne (fun p => (B p).δ), ?_, fun σ hσ z => ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro p _
      exact (B p).hδ
    · obtain ⟨p, hpt, hpU⟩ : ∃ p : ℝ × M, p ∈ t ∧ (σ, z) ∈ (B p).U := by
        have h1 := ht (show (σ, z) ∈ K ×ˢ (Set.univ : Set M) from ⟨hσ, Set.mem_univ z⟩)
        rw [Set.mem_iUnion] at h1
        obtain ⟨p, hp⟩ := h1
        rw [Set.mem_iUnion] at hp
        obtain ⟨hpt, hpU⟩ := hp
        exact ⟨p, hpt, hpU⟩
      have hsol := isXSolOn_comp_sub_of_isXCurveOn (isXCurveOn_of_localBox (X := X) hpU)
      refine ⟨fun r => (B p).FL (r - σ) σ z, ?_, fun r hr => hsol r ?_⟩
      · change (B p).FL (σ - σ) σ z = z
        rw [sub_self]
        exact (B p).hzero σ z hpU
      · have hδ := (B p).hδ
        have hdle : t.inf' hne (fun p => (B p).δ) ≤ (B p).δ :=
          Finset.inf'_le (fun p => (B p).δ) hpt
        have hlt : t.inf' hne (fun p => (B p).δ) < 2 * (B p).δ := by linarith
        exact ⟨by linarith [hr.1, hlt], by linarith [hr.2, hlt]⟩

private theorem mem_closure_image_of_continuousAt_aux {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} {s : Set α} {x : α} (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) := by
  rw [mem_closure_iff] at hx ⊢
  intro U hU hxU
  obtain ⟨V, hV, hVopen, hxV⟩ := mem_nhds_iff.mp (hf.preimage_mem_nhds (hU.mem_nhds hxU))
  obtain ⟨y, hyV, hyS⟩ := hx V hVopen hxV
  exact ⟨f y, hV hyV, y, hyS, rfl⟩

/-- **Agreement propagates.**  Two solutions of the same ODE that agree at one interior common
point agree on their whole common interval (connectedness argument: the agreement set is open by
local uniqueness and closed by continuity in a Hausdorff space). -/
theorem agreeOnIntervals_of_localUniq_core [T2Space M] {X : ℝ → Π x : M, TangentSpace I x}
    (h : LocalUniq X) : AgreeOnIntervals X := by
  intro γ γ' A B A' B' t₀ hγ hγ' ht₀ hagree
  set s : Set ℝ := Ioo (max A A') (min B B') with hs
  set S : Set ℝ := {t | γ t = γ' t} ∩ s with hS
  have ht₀s : t₀ ∈ s :=
    mem_Ioo.mpr ⟨max_lt_iff.mpr ⟨ht₀.1.1, ht₀.2.1⟩, lt_min_iff.mpr ⟨ht₀.1.2, ht₀.2.2⟩⟩
  have hne : (s ∩ S).Nonempty := by
    refine ⟨t₀, ht₀s, ?_⟩
    rw [hS]
    exact ⟨hagree, ht₀s⟩
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨hag, htint⟩ := ht
    have hA : A < t := lt_of_le_of_lt (le_max_left A A') htint.1
    have hB : t < B := lt_of_lt_of_le htint.2 (min_le_left B B')
    have hA' : A' < t := lt_of_le_of_lt (le_max_right A A') htint.1
    have hB' : t < B' := lt_of_lt_of_le htint.2 (min_le_right B B')
    set T : ℝ := min (min ((t - A) / 2) ((B - t) / 2)) (min ((t - A') / 2) ((B' - t) / 2))
      with hT
    have hTpos : 0 < T := by
      rw [hT]
      exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
    have hTleA : T ≤ (t - A) / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hTleB : T ≤ (B - t) / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hTleA' : T ≤ (t - A') / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hTleB' : T ≤ (B' - t) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hsubAB : Ioo (t - T) (t + T) ⊆ Ioo A B := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsubA'B' : Ioo (t - T) (t + T) ⊆ Ioo A' B' := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hloc : EqOn γ γ' (Ioo (t - T) (t + T)) :=
      h (σ := t) (T := T) hTpos (fun u hu => hγ u (hsubAB hu))
        (fun u hu => hγ' u (hsubA'B' hu)) hag
    have hsubS : Ioo (t - T) (t + T) ⊆ S := by
      intro u hu
      rw [hS]
      refine ⟨hloc hu, mem_Ioo.mpr ⟨?_, ?_⟩⟩
      · exact max_lt_iff.mpr ⟨(hsubAB hu).1, (hsubA'B' hu).1⟩
      · exact lt_min_iff.mpr ⟨(hsubAB hu).2, (hsubA'B' hu).2⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hsubS
  have hcl : closure S ∩ s ⊆ S := by
    rintro t ⟨htcl, htint⟩
    have htAB : t ∈ Ioo A B :=
      ⟨lt_of_le_of_lt (le_max_left A A') htint.1, lt_of_lt_of_le htint.2 (min_le_left B B')⟩
    have htA'B' : t ∈ Ioo A' B' :=
      ⟨lt_of_le_of_lt (le_max_right A A') htint.1, lt_of_lt_of_le htint.2 (min_le_right B B')⟩
    have hcontγ : ContinuousAt γ t := (hγ t htAB).continuousAt
    have hcontγ' : ContinuousAt γ' t := (hγ' t htA'B').continuousAt
    have hfc : ContinuousAt (fun u : ℝ => (γ u, γ' u)) t := hcontγ.prodMk hcontγ'
    have hmem : (γ t, γ' t) ∈ closure ((fun u : ℝ => (γ u, γ' u)) '' S) :=
      mem_closure_image_of_continuousAt_aux hfc htcl
    have hsub : (fun u : ℝ => (γ u, γ' u)) '' S ⊆ {p : M × M | p.1 = p.2} := by
      rintro p ⟨u, hu, rfl⟩
      rw [hS] at hu
      exact hu.1
    have hclosed : IsClosed {p : M × M | p.1 = p.2} := isClosed_eq continuous_fst continuous_snd
    rw [hS]
    exact ⟨closure_minimal hsub hclosed hmem, htint⟩
  have hsub : s ⊆ S :=
    (isPreconnected_Ioo (a := max A A') (b := min B B')).subset_of_closure_inter_subset
      (u := S) hopen hne hcl
  intro t ht
  exact (hsub ht).1

private lemma exists_Ioo_symm_subset_of_mem_nhds_aux {s : Set ℝ} {u : ℝ} (hs : s ∈ 𝓝 u) :
    ∃ T : ℝ, 0 < T ∧ Ioo (u - T) (u + T) ⊆ s := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε, hε, fun σ hσ => hεsub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩

/-- **Patching two solutions.**  Two solutions defined on overlapping open intervals and agreeing at
a common point glue into a solution on the union (which agrees with each of them on its own
interval). -/
theorem isXSolOn_piecewise_core {X : ℝ → Π x : M, TangentSpace I x} (huniq : LocalUniq X)
    {γ γ' : ℝ → M} {A B A' B' t₀ : ℝ}
    (hγ : IsXSolOn X γ (Ioo A B)) (hγ' : IsXSolOn X γ' (Ioo A' B'))
    (ht₀ : t₀ ∈ Ioo A B ∩ Ioo A' B') (h : γ t₀ = γ' t₀) :
    IsXSolOn X (Set.piecewise (Ioo A B) γ γ') (Ioo A B ∪ Ioo A' B') ∧
    EqOn (Set.piecewise (Ioo A B) γ γ') γ (Ioo A B) ∧
    EqOn (Set.piecewise (Ioo A B) γ γ') γ' (Ioo A' B') := by
  classical
  have hILR : Ioo A B ∩ Ioo A' B' = Ioo (max A A') (min B B') := Ioo_inter_Ioo
  have ht₀' : t₀ ∈ Ioo (max A A') (min B B') := hILR ▸ ht₀
  have hsubAB : Ioo (max A A') (min B B') ⊆ Ioo A B :=
    Ioo_subset_Ioo (le_max_left A A') (min_le_left B B')
  have hsubAB' : Ioo (max A A') (min B B') ⊆ Ioo A' B' :=
    Ioo_subset_Ioo (le_max_right A A') (min_le_right B B')
  have key : ∀ t ∈ Ioo (max A A') (min B B'), γ t = γ' t := by
    set S : Set ℝ := {t | γ t = γ' t} ∩ Ioo (max A A') (min B B') with hS
    have hSopen : IsOpen S := by
      rw [hS, isOpen_iff_mem_nhds]
      rintro u ⟨hu1, hu2⟩
      obtain ⟨T, hT, hTsub⟩ := exists_Ioo_symm_subset_of_mem_nhds_aux (isOpen_Ioo.mem_nhds hu2)
      have hloc := huniq hT (fun s hs => hγ s (hsubAB (hTsub hs)))
        (fun s hs => hγ' s (hsubAB' (hTsub hs))) hu1
      refine Filter.mem_of_superset
        (show Ioo (u - T) (u + T) ∈ 𝓝 u from Ioo_mem_nhds (by linarith) (by linarith)) ?_
      intro σ hσ
      exact ⟨hloc hσ, hTsub hσ⟩
    have hcl : closure S ∩ Ioo (max A A') (min B B') ⊆ S := by
      rw [hS]
      rintro t ⟨htcl, htLR⟩
      refine ⟨?_, htLR⟩
      by_contra hne
      obtain ⟨η, hη, hηsub⟩ := exists_Ioo_symm_subset_of_mem_nhds_aux (isOpen_Ioo.mem_nhds htLR)
      obtain ⟨u, huη, huagree, -⟩ := mem_closure_iff.mp htcl (Ioo (t - η / 4) (t + η / 4))
        isOpen_Ioo ⟨by linarith, by linarith⟩
      obtain ⟨hu1, hu2⟩ := huη
      have hut : |u - t| < η / 4 := abs_lt.mpr ⟨by linarith, by linarith⟩
      have hune : u ≠ t := fun h' => hne (h' ▸ huagree)
      set T : ℝ := η / 2 + |u - t| with hT
      have hTpos : 0 < T := by rw [hT]; positivity
      have hTsub : Ioo (u - T) (u + T) ⊆ Ioo (max A A') (min B B') := by
        intro σ hσ
        rw [hT] at hσ
        obtain ⟨hσ1, hσ2⟩ := hσ
        exact hηsub ⟨by linarith, by linarith⟩
      have htmem : t ∈ Ioo (u - T) (u + T) := by
        have h1 : u - t ≤ |u - t| := le_abs_self _
        have h2 : t - u ≤ |u - t| := by
          have hh := le_abs_self (t - u)
          rw [abs_sub_comm] at hh
          exact hh
        rw [hT]
        exact ⟨by linarith, by linarith⟩
      exact hne (huniq hTpos (fun s hs => hγ s (hsubAB (hTsub hs)))
        (fun s hs => hγ' s (hsubAB' (hTsub hs))) huagree htmem)
    have hne : (Ioo (max A A') (min B B') ∩ S).Nonempty :=
      ⟨t₀, ht₀', by rw [hS]; exact ⟨h, ht₀'⟩⟩
    have hsub : Ioo (max A A') (min B B') ⊆ S :=
      (isPreconnected_Ioo (a := max A A') (b := min B B')).subset_of_closure_inter_subset
        hSopen hne hcl
    intro t ht
    have h1 := hsub ht
    rw [hS] at h1
    exact h1.1
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [Set.mem_union] at ht
    rcases ht with ht | ht
    · have hp : Set.piecewise (Ioo A B) γ γ' =ᶠ[𝓝 t] γ := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with σ hσ
        exact Set.piecewise_eq_of_mem (Ioo A B) γ γ' hσ
      have hpt : Set.piecewise (Ioo A B) γ γ' t = γ t :=
        Set.piecewise_eq_of_mem (Ioo A B) γ γ' ht
      rw [hpt]
      exact (hγ t ht).congr_of_eventuallyEq_abuse hp
    · have hp : Set.piecewise (Ioo A B) γ γ' =ᶠ[𝓝 t] γ' := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with σ hσ
        by_cases hσAB : σ ∈ Ioo A B
        · rw [Set.piecewise_eq_of_mem (Ioo A B) γ γ' hσAB]
          exact key σ (hILR ▸ ⟨hσAB, hσ⟩)
        · exact Set.piecewise_eq_of_notMem (Ioo A B) γ γ' hσAB
      have hpt : Set.piecewise (Ioo A B) γ γ' t = γ' t := by
        by_cases htAB : t ∈ Ioo A B
        · rw [Set.piecewise_eq_of_mem (Ioo A B) γ γ' htAB]
          exact key t (hILR ▸ ⟨htAB, ht⟩)
        · exact Set.piecewise_eq_of_notMem (Ioo A B) γ γ' htAB
      rw [hpt]
      exact (hγ' t ht).congr_of_eventuallyEq_abuse hp
  · intro t ht
    exact Set.piecewise_eq_of_mem (Ioo A B) γ γ' ht
  · intro t ht
    by_cases htAB : t ∈ Ioo A B
    · rw [Set.piecewise_eq_of_mem (Ioo A B) γ γ' htAB]
      exact key t (hILR ▸ ⟨htAB, ht⟩)
    · exact Set.piecewise_eq_of_notMem (Ioo A B) γ γ' htAB

/-- Time reversal of solutions. -/
theorem isXSolOn_revX_core {X : ℝ → Π x : M, TangentSpace I x} {γ : ℝ → M} {s : Set ℝ}
    (h : IsXSolOn (revX X) γ s) : IsXSolOn X (fun t => γ (-t)) {t | -t ∈ s} := by
  intro t ht
  have h' : HasMFDerivAt 𝓘(ℝ,ℝ) I γ (-t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X (-(-t)) (γ (-t))))) := by
    simpa [revX] using h (-t) ht
  have hc := hasMFDerivAt_comp_neg (f := γ) (t := -t) (w := -(X (-(-t)) (γ (-t)))) h'
  rw [neg_neg t] at hc
  simpa using hc

/-- The reversed field inherits local uniqueness. -/
theorem localUniq_revX_core {X : ℝ → Π x : M, TangentSpace I x} (h : LocalUniq X) :
    LocalUniq (revX X) := by
  intro σ T hT γ γ' hγ hγ' h0
  have hset : {t : ℝ | -t ∈ Ioo (σ - T) (σ + T)} = Ioo (-σ - T) (-σ + T) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor <;> intro hh <;> constructor <;> linarith
  have h1 : IsXSolOn X (fun t => γ (-t)) (Ioo (-σ - T) (-σ + T)) := by
    have := isXSolOn_revX_core (X := X) (γ := γ) (s := Ioo (σ - T) (σ + T)) hγ
    rwa [hset] at this
  have h2 : IsXSolOn X (fun t => γ' (-t)) (Ioo (-σ - T) (-σ + T)) := by
    have := isXSolOn_revX_core (X := X) (γ := γ') (s := Ioo (σ - T) (σ + T)) hγ'
    rwa [hset] at this
  have h0' : (fun t => γ (-t)) (-σ) = (fun t => γ' (-t)) (-σ) := by
    simpa using h0
  have h3 := h hT h1 h2 h0'
  intro t ht
  have ht' : -t ∈ Ioo (-σ - T) (-σ + T) := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h4 := h3 ht'
  simpa using h4

/-- A solution of `X` gives, after reversal, a solution of `revX X`. -/
theorem isXSolOn_revX_conv {X : ℝ → Π x : M, TangentSpace I x} {Γ : ℝ → M} {s : Set ℝ}
    (h : IsXSolOn X Γ s) : IsXSolOn (revX X) (fun t => Γ (-t)) {t | -t ∈ s} := by
  intro t ht
  have h' : HasMFDerivAt 𝓘(ℝ,ℝ) I Γ (-t) ((1 : ℝ →L[ℝ] ℝ).smulRight (X (-t) (Γ (-t)))) :=
    h (-t) ht
  have hc := hasMFDerivAt_comp_neg (f := Γ) (t := -t) (w := X (-t) (Γ (-t))) h'
  rw [neg_neg t] at hc
  simpa [revX] using hc

/-- The reversed field inherits uniform local existence. -/
theorem unifLocalAbs_revX_core {X : ℝ → Π x : M, TangentSpace I x} (h : UnifLocalAbs X) :
    UnifLocalAbs (revX X) := by
  intro K hK
  obtain ⟨d, hd, hd'⟩ := h ((fun σ => -σ) '' K) (hK.image continuous_neg)
  refine ⟨d, hd, fun σ hσ z => ?_⟩
  obtain ⟨Γ, hΓ0, hΓ⟩ := hd' (-σ) (mem_image_of_mem _ hσ) z
  refine ⟨fun t => Γ (-t), ?_, ?_⟩
  · simpa using hΓ0
  · have hset : {t : ℝ | -t ∈ Ioo (-σ - d) (-σ + d)} = Ioo (σ - d) (σ + d) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor <;> intro hh <;> constructor <;> linarith
    have := isXSolOn_revX_conv (X := X) (Γ := Γ) (s := Ioo (-σ - d) (-σ + d)) hΓ
    rwa [hset] at this

/-! ## The maximality argument -/

/-- A single solution can be extended a little to the right. -/
lemma exists_isXSolOn_extend {Y : ℝ → Π x : M, TangentSpace I x} {d : ℝ} (hd : 0 < d)
    {L t : ℝ} (hLt : L < t) {Γ : ℝ → M} (hΓ : IsXSolOn Y Γ (Ioo L t))
    (hloc : ∀ σ ∈ Icc L t, ∀ z : M, ∃ Φ : ℝ → M, Φ σ = z ∧ IsXSolOn Y Φ (Ioo (σ - d) (σ + d)))
    (hLu : LocalUniq Y) {a : ℝ} {z : M} (haL : L < a) (hat : a < t) (hΓa : Γ a = z) :
    ∃ Γ' : ℝ → M, Γ' a = z ∧ IsXSolOn Y Γ' (Ioo L (t + d / 2)) := by
  classical
  set m : ℝ := min (d / 2) ((t - L) / 2) with hm
  have hmpos : 0 < m := lt_min (by linarith) (by linarith)
  have hmle : m ≤ d / 2 := min_le_left _ _
  set t₀ : ℝ := t - m with ht₀
  have ht₀lt : t₀ < t := by rw [ht₀]; linarith
  have ht₀gt : L < t₀ := by
    rw [ht₀]
    have h2 : m ≤ (t - L) / 2 := min_le_right _ _
    linarith
  obtain ⟨Φ, hΦ0, hΦ⟩ := hloc t₀ ⟨le_of_lt ht₀gt, le_of_lt ht₀lt⟩ (Γ t₀)
  have hglue := isXSolOn_piecewise_core (X := Y) hLu hΓ hΦ
    (show t₀ ∈ Ioo L t ∩ Ioo (t₀ - d) (t₀ + d) from
      ⟨⟨ht₀gt, ht₀lt⟩, ⟨by linarith, by linarith⟩⟩) hΦ0.symm
  refine ⟨Set.piecewise (Ioo L t) Γ Φ, ?_, ?_⟩
  · rw [Set.piecewise_eq_of_mem (Ioo L t) Γ Φ ⟨haL, hat⟩]
    exact hΓa
  · intro u hu
    refine hglue.1 u ?_
    have hmain : t + d / 2 ≤ t₀ + d := by rw [ht₀]; linarith
    have hu' : u < t₀ + d := lt_of_lt_of_le hu.2 hmain
    rcases lt_or_ge u t with hlt | hge
    · exact Or.inl ⟨hu.1, hlt⟩
    · exact Or.inr ⟨by linarith, hu'⟩

/-- **Gluing a compatible family of solutions** through one initial point into a single one. -/
theorem exists_isXSolOn_Ioi_core {Y : ℝ → Π x : M, TangentSpace I x} (hAg : AgreeOnIntervals Y)
    {L a : ℝ} (hLa : L < a) {z : M}
    (h : ∀ T : ℝ, ∃ Γ : ℝ → M, Γ a = z ∧ IsXSolOn Y Γ (Ioo L T)) :
    ∃ Γ : ℝ → M, Γ a = z ∧ ∀ T : ℝ, IsXSolOn Y Γ (Ioo L T) := by
  classical
  have ht1 : ∀ t : ℝ, t < max (t + 1) (a + 1) :=
    fun t => lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ha1 : ∀ t : ℝ, a < max (t + 1) (a + 1) :=
    fun t => lt_of_lt_of_le (by linarith) (le_max_right _ _)
  let Γ : ℝ → M := fun t => if L < t then (Classical.choose (h (max (t + 1) (a + 1)))) t else z
  have hspec : ∀ t, (Classical.choose (h (max (t + 1) (a + 1)))) a = z ∧
      IsXSolOn Y (Classical.choose (h (max (t + 1) (a + 1)))) (Ioo L (max (t + 1) (a + 1))) :=
    fun t => Classical.choose_spec (h (max (t + 1) (a + 1)))
  have hΓa : Γ a = z := by
    show (if L < a then (Classical.choose (h (max (a + 1) (a + 1)))) a else z) = z
    rw [if_pos hLa]
    exact (hspec a).1
  refine ⟨Γ, hΓa, fun T t ht => ?_⟩
  have hLt : L < t := ht.1
  have hev : Γ =ᶠ[𝓝 t] (Classical.choose (h (max (t + 1) (a + 1)))) := by
    have hε1 : min 1 ((t - L) / 2) ≤ 1 := min_le_left _ _
    have hε2 : min 1 ((t - L) / 2) ≤ (t - L) / 2 := min_le_right _ _
    have hεpos : 0 < min 1 ((t - L) / 2) := lt_min one_pos (by linarith)
    have hnbhd : Ioo (t - min 1 ((t - L) / 2)) (t + min 1 ((t - L) / 2)) ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds (Set.mem_Ioo.mpr ⟨by linarith [hεpos], by linarith [hεpos]⟩)
    filter_upwards [hnbhd] with u hu
    have hLu : L < u := by linarith [hu.1, hε2]
    have hu1 : u < t + 1 := by linarith [hu.2, hε1]
    show (if L < u then (Classical.choose (h (max (u + 1) (a + 1)))) u else z)
      = (Classical.choose (h (max (t + 1) (a + 1)))) u
    rw [if_pos hLu]
    have hcmp := hAg (γ := Classical.choose (h (max (u + 1) (a + 1))))
      (γ' := Classical.choose (h (max (t + 1) (a + 1))))
      (A := L) (B := max (u + 1) (a + 1)) (A' := L) (B' := max (t + 1) (a + 1)) (t₀ := a)
      (hspec u).2 (hspec t).2
      (by rw [Set.mem_inter_iff]
          exact ⟨Set.mem_Ioo.mpr ⟨hLa, ha1 u⟩, Set.mem_Ioo.mpr ⟨hLa, ha1 t⟩⟩)
      ((hspec u).1.trans (hspec t).1.symm)
    exact hcmp (Set.mem_Ioo.mpr ⟨by simpa using hLu,
      lt_min (lt_of_lt_of_le (by linarith : u < u + 1) (le_max_left (u + 1) (a + 1)))
        (lt_of_lt_of_le hu1 (le_max_left (t + 1) (a + 1)))⟩)
  have hpt : Γ t = (Classical.choose (h (max (t + 1) (a + 1)))) t := by
    show (if L < t then (Classical.choose (h (max (t + 1) (a + 1)))) t else z) = _
    rw [if_pos hLt]
  rw [hpt]
  exact ((hspec t).2 t (Set.mem_Ioo.mpr ⟨hLt, ht1 t⟩)).congr_of_eventuallyEq_abuse hev

/-- **Right extension.**  With uniform local existence and local uniqueness, there is a solution
through `(a, z)` valid on `Ioo L T` for every `T`, for some `L < a`. -/
theorem exists_isXSolOn_right {Y : ℝ → Π x : M, TangentSpace I x} (hU : UnifLocalAbs Y)
    (hLu : LocalUniq Y) (hAg : AgreeOnIntervals Y) (a : ℝ) (z : M) :
    ∃ L : ℝ, L < a ∧ ∃ Γ : ℝ → M, Γ a = z ∧ ∀ T : ℝ, IsXSolOn Y Γ (Ioo L T) := by
  classical
  obtain ⟨d, hd, hdl⟩ := hU {a} isCompact_singleton
  obtain ⟨Γ₀, hΓ₀a, hΓ₀⟩ := hdl a (mem_singleton a) z
  set L : ℝ := a - d with hL
  have hLa : L < a := by rw [hL]; linarith
  set S : Set ℝ := {t : ℝ | ∃ Γ : ℝ → M, Γ a = z ∧ IsXSolOn Y Γ (Ioo L t)} with hS
  have haS : a + d ∈ S := ⟨Γ₀, hΓ₀a, hΓ₀⟩
  have hSne : S.Nonempty := ⟨a + d, haS⟩
  have hunbounded : ∀ u : ℝ, ∃ t ∈ S, u < t := by
    intro u
    by_contra hcon
    have hcon' : ∀ t ∈ S, t ≤ u := fun t ht => le_of_not_gt (fun hlt => hcon ⟨t, ht, hlt⟩)
    have hbdd : BddAbove S := ⟨u, hcon'⟩
    set s : ℝ := sSup S with hs
    obtain ⟨e, he, hel⟩ := hU (Icc L s) isCompact_Icc
    have hsge : a + d ≤ s := le_csSup hbdd haS
    have hlt_s : max a (s - e / 3) < s := max_lt (by linarith) (by linarith)
    obtain ⟨t, htS, htgt⟩ := (lt_csSup_iff hbdd hSne).mp hlt_s
    have ht1 : a < t := lt_of_le_of_lt (le_max_left _ _) htgt
    have ht2 : s - e / 3 < t := lt_of_le_of_lt (le_max_right _ _) htgt
    have hts : t ≤ s := le_csSup hbdd htS
    obtain ⟨Γ, hΓa, hΓ⟩ := htS
    have hloc : ∀ σ ∈ Icc L t, ∀ z : M,
        ∃ Φ : ℝ → M, Φ σ = z ∧ IsXSolOn Y Φ (Ioo (σ - e) (σ + e)) :=
      fun σ hσ => hel σ ⟨hσ.1, le_trans hσ.2 hts⟩
    obtain ⟨Γ', hΓ'a, hΓ'⟩ :=
      exists_isXSolOn_extend he (lt_of_lt_of_le hLa (le_of_lt ht1)) hΓ hloc hLu hLa ht1 hΓa
    have ht'mem : t + e / 2 ∈ S := ⟨Γ', hΓ'a, hΓ'⟩
    have hle := le_csSup hbdd ht'mem
    linarith
  have hall : ∀ T : ℝ, ∃ Γ : ℝ → M, Γ a = z ∧ IsXSolOn Y Γ (Ioo L T) := by
    intro T
    obtain ⟨t, htS, ht⟩ := hunbounded T
    obtain ⟨Γ, hΓa, hΓ⟩ := htS
    exact ⟨Γ, hΓa, fun u hu => hΓ u ⟨hu.1, lt_trans hu.2 ht⟩⟩
  obtain ⟨Γ, hΓa, hΓ⟩ := exists_isXSolOn_Ioi_core hAg hLa hall
  exact ⟨L, hLa, Γ, hΓa, hΓ⟩

/-- **Left extension**, obtained from the right extension by time reversal. -/
theorem exists_isXSolOn_left {Y : ℝ → Π x : M, TangentSpace I x} (hU : UnifLocalAbs Y)
    (hLu : LocalUniq Y) [T2Space M] (a : ℝ) (z : M) :
    ∃ R : ℝ, a < R ∧ ∃ Γ : ℝ → M, Γ a = z ∧ ∀ T : ℝ, IsXSolOn Y Γ (Ioo T R) := by
  have hU' : UnifLocalAbs (revX Y) := unifLocalAbs_revX_core hU
  have hLu' : LocalUniq (revX Y) := localUniq_revX_core hLu
  have hAg' : AgreeOnIntervals (revX Y) := agreeOnIntervals_of_localUniq_core hLu'
  obtain ⟨L, hL, ΓL, hΓL0, hΓL⟩ := exists_isXSolOn_right hU' hLu' hAg' (-a) z
  refine ⟨-L, by linarith, fun t => ΓL (-t), ?_, ?_⟩
  · exact hΓL0
  · intro T
    have h := isXSolOn_revX_core (X := Y) (γ := ΓL) (s := Ioo L (-T)) (hΓL (-T))
    have hset : {t : ℝ | -t ∈ Ioo L (-T)} = Ioo T (-L) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ioo]
      constructor <;> intro hh <;> constructor <;> linarith
    rwa [hset] at h

/-- **Global solution.**  A local solution around the initial point, together with uniform local
existence and agreement of solutions, yields a global one. -/
theorem exists_isXSol_of_loc {Y : ℝ → Π x : M, TangentSpace I x} (hU : UnifLocalAbs Y)
    (hLu : LocalUniq Y) (hAg : AgreeOnIntervals Y) [T2Space M] {a : ℝ} {z : M}
    (hloc : ∃ Γ₀ : ℝ → M, Γ₀ a = z ∧ ∃ d : ℝ, 0 < d ∧ IsXSolOn Y Γ₀ (Ioo (a - d) (a + d))) :
    ∃ Γ : ℝ → M, Γ a = z ∧ IsXSol Y Γ := by
  classical
  obtain ⟨L, hL, Γ_R, hRa, hR⟩ := exists_isXSolOn_right hU hLu hAg a z
  obtain ⟨R, hR', Γ_L, hLa, hLsol⟩ := exists_isXSolOn_left hU hLu a z
  obtain ⟨Γ₀, hΓ₀a, d, hd, hΓ₀⟩ := hloc
  have hRmem : a ∈ Ioo (a - 1) R := Set.mem_Ioo.mpr ⟨by linarith, hR'⟩
  have hLmem : a ∈ Ioo L (a + 1) := Set.mem_Ioo.mpr ⟨hL, by linarith⟩
  -- the two one-sided solutions agree with the local one near the initial point
  have hAgR : EqOn Γ_R Γ₀ (Ioo (max L (a - d)) (min (a + 1) (a + d))) :=
    hAg (γ := Γ_R) (γ' := Γ₀) (A := L) (B := a + 1) (A' := a - d) (B' := a + d) (t₀ := a)
      (hR (a + 1)) hΓ₀
      (by rw [Set.mem_inter_iff]
          exact ⟨hLmem, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩)
      (hRa.trans hΓ₀a.symm)
  have hAgL : EqOn Γ_L Γ₀ (Ioo (max (a - 1) (a - d)) (min R (a + d))) :=
    hAg (γ := Γ_L) (γ' := Γ₀) (A := a - 1) (B := R) (A' := a - d) (B' := a + d) (t₀ := a)
      (hLsol (a - 1)) hΓ₀
      (by rw [Set.mem_inter_iff]
          exact ⟨hRmem, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩)
      (hLa.trans hΓ₀a.symm)
  have hmemR : a ∈ Ioo (max L (a - d)) (min (a + 1) (a + d)) :=
    Set.mem_Ioo.mpr ⟨max_lt hL (by linarith), lt_min (by linarith) (by linarith)⟩
  have hmemL : a ∈ Ioo (max (a - 1) (a - d)) (min R (a + d)) :=
    Set.mem_Ioo.mpr ⟨max_lt (by linarith) (by linarith), lt_min hR' (by linarith)⟩
  have hev : (fun t => if t < a then Γ_L t else Γ_R t) =ᶠ[𝓝 a] Γ₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hmemR, isOpen_Ioo.mem_nhds hmemL] with u huR huL
    rcases lt_or_ge u a with hlt | hge
    · show (if u < a then Γ_L u else Γ_R u) = Γ₀ u
      rw [if_pos hlt]
      exact hAgL huL
    · show (if u < a then Γ_L u else Γ_R u) = Γ₀ u
      rw [if_neg (not_lt.mpr hge)]
      exact hAgR huR
  refine ⟨fun t => if t < a then Γ_L t else Γ_R t, ?_, ?_⟩
  · show (if a < a then Γ_L a else Γ_R a) = z
    rw [if_neg (lt_irrefl a)]
    exact hRa
  · intro t
    rcases lt_trichotomy t a with hlt | heq | hgt
    · have hev' : (fun u => if u < a then Γ_L u else Γ_R u) =ᶠ[𝓝 t] Γ_L := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
        rw [if_pos (Set.mem_Iio.mp hu)]
      have hpt : (if t < a then Γ_L t else Γ_R t) = Γ_L t := if_pos hlt
      change HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => if u < a then Γ_L u else Γ_R u) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (if t < a then Γ_L t else Γ_R t)))
      rw [hpt]
      exact (hLsol (t - 1) t (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)).congr_of_eventuallyEq_abuse
        hev'
    · have hta : t = a := heq
      have hnot : ¬ (t < a) := by rw [hta]; exact lt_irrefl a
      have hpt : (if t < a then Γ_L t else Γ_R t) = Γ₀ t := by
        rw [if_neg hnot, hta]
        exact hRa.trans hΓ₀a.symm
      change HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => if u < a then Γ_L u else Γ_R u) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (if t < a then Γ_L t else Γ_R t)))
      rw [hpt, hta]
      exact (hΓ₀ a (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)).congr_of_eventuallyEq_abuse hev
    · have hev' : (fun u => if u < a then Γ_L u else Γ_R u) =ᶠ[𝓝 t] Γ_R := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
        rw [if_neg (not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hu)))]
      have hpt : (if t < a then Γ_L t else Γ_R t) = Γ_R t := if_neg (not_lt.mpr (le_of_lt hgt))
      change HasMFDerivAt 𝓘(ℝ,ℝ) I (fun u => if u < a then Γ_L u else Γ_R u) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (if t < a then Γ_L t else Γ_R t)))
      rw [hpt]
      exact (hR (t + 1) t (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)).congr_of_eventuallyEq_abuse
        hev'

theorem exists_isXCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hBox : ∀ a y, ∃ B : Work.Diff.ODE.LocalBox X, (a, y) ∈ B.U)
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      Work.Diff.ODE.IsXCurveOn X a y T γ → Work.Diff.ODE.IsXCurveOn X a y T γ' →
        EqOn γ γ' (Ioo (-T) T))
    (a : ℝ) (y : M) : ∃ γ : ℝ → M, Work.Diff.ODE.IsXCurve X a y γ := by
  classical
  have hU : UnifLocalAbs (shiftX X a) :=
    unifLocalAbs_shiftX (unifLocalAbs_of_boxes hBox) a
  have hLu : LocalUniq (shiftX X a) := localUniq_shiftX_of_hUniq hUniq a
  have hAg : AgreeOnIntervals (shiftX X a) := agreeOnIntervals_of_localUniq_core hLu
  obtain ⟨B, hB⟩ := hBox a y
  have hloc : ∃ Γ₀ : ℝ → M, Γ₀ 0 = y ∧
      ∃ d : ℝ, 0 < d ∧ IsXSolOn (shiftX X a) Γ₀ (Ioo (0 - d) (0 + d)) := by
    refine ⟨fun t => B.FL (t - 0) a y, ?_, 2 * B.δ, by linarith [B.hδ], ?_⟩
    · change B.FL (0 - 0) a y = y
      rw [sub_self]
      exact B.hzero a y hB
    · have hcur : IsXCurveOn X (a + 0) y (2 * B.δ) (fun τ => B.FL τ a y) := by
        simpa using isXCurveOn_of_localBox (X := X) hB
      exact isXSolOn_shiftX_of_isXCurveOn (a := a) (σ := 0) (d := 2 * B.δ) (z := y) hcur
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_isXSol_of_loc hU hLu hAg hloc
  refine ⟨Γ, (isXCurve_shiftX_iff (X := X) (a := a) (y := y) (γ := Γ)).mp ?_⟩
  exact (isXCurve_iff_isXSol (Y := shiftX X a) (y := y) (γ := Γ)).mpr ⟨hΓ0, hΓ⟩

end Work.Diff.ODE
