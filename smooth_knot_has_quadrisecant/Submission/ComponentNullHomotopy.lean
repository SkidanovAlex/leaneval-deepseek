import Mathlib
import ChallengeDeps
import Submission.TrappedWinding
import Submission.ComponentWindingData
import Submission.EmbeddedCircleWinding
import Submission.Commons.Topology.Homotopy.nullHomotopic_comp_left
import Submission.Commons.Analysis.Floor.interval_of_not_mem_zmultiples

open LeanEval.KnotTheory.Quadrisecant
open Filter

set_option linter.style.haveILetI false
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S280 — brick (d), first step: the class map of a circular component of
the trisecant set is NULL-HOMOTOPIC in the band (VERIFIED, sorry-free)
(Submission/ComponentNullHomotopy.lean)

S279 closed the winding measurement: a circular component of the trisecant
set has EVEN ordered lift with ZERO endpoint advances (`ka = kb = 0`), and
the odd branch is impossible.  This module turns that into the geometric
statement brick (d) consumes: **the component does not wind** — the class
map `AddCircle T → OpenMobius` of the component is null-homotopic.  The
null-homotopy is completely explicit:

* with `ka = kb = 0` the endpoint real lifts `a, b` are `T`-periodic
  (`a (u+T) = a u`, `b (u+T) = b u`), so the ordered pair `(a u, b u)`
  descends to a loop `σ : AddCircle T → OrderedPairs` of the ordered
  double cover over the class map;
* the difference `a − b` is continuous and never in `period · ℤ` (the
  endpoint classes are distinct), so on the connected `ℝ` its values lie
  in a single window `(k·period, (k+1)·period)` (commons
  `interval_of_not_mem_zmultiples`);
* the straight-line homotopy
  `(u, s) ↦ ((1−s)·a u + s·cc, (1−s)·b u + s·0)` with
  `cc = (k + 1/2)·period` keeps the difference
  `(1−s)(a u − b u) + s·cc` a convex combination of two points of the open
  window `(k·period, (k+1)·period)`, hence never hits the diagonal; it
  descends to a homotopy of `σ` to a constant;
* composing with the covering projection `mobiusCover` gives the
  null-homotopy of the class map.

Content:

1. **`componentCircleClassMap`** — the class map descended to the
   component circle, `C(AddCircle T, OpenMobius)`;
2. **`orderedRealModel` / `orderedLiftLoop`** — the ordered lift of the
   component loop through the double cover (from `T`-periodic endpoint
   lifts), with the value identity at coercions
   (`liftIco_zero_coe_apply_of_periodic`) and `mobiusCover_orderedLiftLoop`
   (its projection is the class map);
3. **`nullHomotopic_orderedLiftLoop`** — the explicit null-homotopy of the
   ordered loop in `OrderedPairs`;
4. **`circular_component_classMap_nullHomotopic`** — THE brick-(d) input:
   under the general-position and quadrisecant-free hypotheses the class
   map of every circular component of the trisecant set is null-homotopic
   in the band (no circular component of `O` winds — the dichotomy branch
   "winding circular component" is vacuous).

(Recorded next bridge, for brick (d) proper: transporting the null-homotopy
across the chart homeomorphism to the `Circle`-parametrised
`SimpleClosedCurve` vocabulary of `EmbeddedCircleWinding` — the class map
of the `Circle` chart is this class map precomposed with
`paramCircleHomeo : AddCircle period ≃ₜ Circle` (S253
`addCircleHomeo_of_circleHomeo`), and precomposition with a homeomorphism
preserves null-homotopy in both directions.)

Tree green (`lake build Challenge Submission Solution` rc=0); TWO
documented sorries (Challenge.lean:5 stub, Submission.lean final
placeholder); no children pending.
-/

/-! ## 1. The class map on the component circle -/

/-- **The class map of a circular component, descended to the component
circle (VERIFIED def)**: `u ↦ (χ u : OpenMobius)` as a continuous map
`C(AddCircle T, OpenMobius)`. -/
noncomputable def componentCircleClassMap {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) : C(AddCircle T, OpenMobius) :=
  ⟨fun u => ((χ u : TrisecantComponent r c₀) : OpenMobius),
    continuous_subtype_val.comp (continuous_subtype_val.comp χ.continuous)⟩

/-- The descended class map agrees with `componentClassMap` at coercions
(VERIFIED). -/
lemma componentCircleClassMap_coe {r : ℝ → Space} (c₀ : OSub r) {T : ℝ}
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) (u : ℝ) :
    componentCircleClassMap c₀ χ (u : AddCircle T) = componentClassMap c₀ χ u := rfl

/-! ## 2. The ordered lift loop through the double cover -/

/-- **The real model of the ordered loop (VERIFIED def)**: the ordered pair
of the two endpoint classes, `u ↦ ((a u), (b u))` in `OrderedPairs`
(distinctness from the data). -/
noncomputable def orderedRealModel (a b : ℝ → ℝ)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period)) :
    ℝ → OrderedPairs :=
  fun u => ⟨((a u : AddCircle period), (b u : AddCircle period)), hne u⟩

/-- Continuity of the real model (VERIFIED). -/
lemma continuous_orderedRealModel {a b : ℝ → ℝ} (haC : Continuous a)
    (hbC : Continuous b)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period)) :
    Continuous (orderedRealModel a b hne) := by
  refine Continuous.subtype_mk
    (p := fun q : AddCircle period × AddCircle period => q.1 ≠ q.2) ?_ hne
  exact ((AddCircle.continuous_mk' period).comp haC).prodMk
    ((AddCircle.continuous_mk' period).comp hbC)

/-- `T`-periodicity of the real model (VERIFIED). -/
lemma orderedRealModel_periodic {a b : ℝ → ℝ}
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    {T : ℝ} (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) :
    Function.Periodic (orderedRealModel a b hne) T := by
  intro u
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun t : ℝ => (t : AddCircle period)) (haT u)
  · exact congrArg (fun t : ℝ => (t : AddCircle period)) (hbT u)

/-- **Evaluation of a descended periodic map at an arbitrary real
parameter (VERIFIED)**: if `f` is `T`-periodic, `AddCircle.liftIco T 0 f`
agrees with `f` at every real `x` (the standard
`AddCircle.liftIco_zero_coe_apply` covers `x ∈ Ico 0 T`; periodicity
removes the restriction). -/
lemma liftIco_zero_coe_apply_of_periodic {T : ℝ} [Fact (0 < T)] {B : Type*} {f : ℝ → B}
    (hper : Function.Periodic f T) (x : ℝ) :
    AddCircle.liftIco T 0 f (x : AddCircle T) = f x := by
  rcases AddCircle.eq_coe_Ico (x : AddCircle T) with ⟨t, ht, htx⟩
  have hft : f t = f x := by
    have hmem : t - x ∈ AddSubgroup.zmultiples T := (QuotientAddGroup.eq_iff_sub_mem).mp htx
    rcases (AddSubgroup.mem_zmultiples_iff.mp hmem) with ⟨n, hn⟩
    have htx' : t = x + n • T := by
      rw [hn]
      abel
    rw [htx']
    exact hper.zsmul n x
  calc
    AddCircle.liftIco T 0 f (x : AddCircle T) =
        AddCircle.liftIco T 0 f (t : AddCircle T) := by rw [htx]
    _ = f t := AddCircle.liftIco_zero_coe_apply ht
    _ = f x := hft

/-- **The ordered lift loop (VERIFIED def)**: the loop of `OrderedPairs`
over the component circle from `T`-periodic real endpoint lifts `a, b` —
the descent of the real model `u ↦ ((a u), (b u))`. -/
noncomputable def orderedLiftLoop {r : ℝ → Space} (c₀ : OSub r) {T : ℝ} [Fact (0 < T)]
    (_χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {a b : ℝ → ℝ} (haC : Continuous a)
    (hbC : Continuous b)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) :
    C(AddCircle T, OrderedPairs) :=
  ⟨AddCircle.liftIco T 0 (orderedRealModel a b hne),
    AddCircle.liftIco_zero_continuous
      (by simpa using (orderedRealModel_periodic hne haT hbT 0).symm)
      (continuous_orderedRealModel haC hbC hne).continuousOn⟩

/-- The value of the ordered lift loop at coercions (VERIFIED). -/
lemma orderedLiftLoop_coe {r : ℝ → Space} (c₀ : OSub r) {T : ℝ} [Fact (0 < T)]
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {a b : ℝ → ℝ} (haC : Continuous a)
    (hbC : Continuous b)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) (u : ℝ) :
    orderedLiftLoop c₀ χ haC hbC hne haT hbT (u : AddCircle T) =
      orderedRealModel a b hne u :=
  liftIco_zero_coe_apply_of_periodic (orderedRealModel_periodic hne haT hbT) u

/-- **The ordered lift loop projects to the class map (VERIFIED)**: for
endpoint real lifts `a, b` of an ordered lift `sig` of the class map, the
covering projection of the ordered lift loop is the descended class map. -/
lemma mobiusCover_orderedLiftLoop {r : ℝ → Space} (c₀ : OSub r) {T : ℝ} [Fact (0 < T)]
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {sig : C(ℝ, OrderedPairs)}
    (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ) {a b : ℝ → ℝ}
    (haC : Continuous a) (hbC : Continuous b)
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) :
    mobiusCover ∘ orderedLiftLoop c₀ χ haC hbC hne haT hbT =
      componentCircleClassMap c₀ χ := by
  funext z
  rcases AddCircle.eq_coe_Ico z with ⟨u, -, huz⟩
  rw [← huz]
  simp only [Function.comp_apply, orderedLiftLoop_coe, componentCircleClassMap_coe]
  have h1 : mobiusCover (orderedRealModel a b hne u) = mobiusCover (sig u) := by
    apply Subtype.ext
    apply Quotient.sound
    refine Or.inl ?_
    exact Prod.ext (ha u) (hb u)
  rw [h1]
  exact congrFun hσl u

/-! ## 3. The explicit null-homotopy of the ordered loop -/

/-- **The homotopy difference avoids the diagonal (VERIFIED)**: if the
difference `a − b` lies in the open window `(k·period, (k+1)·period)` and
`cc = (k + 1/2)·period` is the window midpoint, then the straight-line
combination `(1−s)·a u + s·cc` versus `(1−s)·b u + s·0` still avoids the
diagonal: the difference `(1−s)(a u − b u) + s·cc` is a convex combination
of two points of the open window, hence lies strictly inside it. -/
lemma orderedHomotopy_diff_notMem (k : ℤ) {cc : ℝ}
    (hcc : cc = ((k : ℝ) + 1 / 2) * period) {a b : ℝ → ℝ}
    (hwin : ∀ u : ℝ, a u - b u ∈
      Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period))
    (u : ℝ) (s : I) :
    ((1 - (s : ℝ)) * a u + (s : ℝ) * cc) -
      ((1 - (s : ℝ)) * b u + (s : ℝ) * (0 : ℝ)) ∉
      AddSubgroup.zmultiples period := by
  intro hmem
  have hcomb : (1 - (s : ℝ)) * (a u - b u) + (s : ℝ) * cc =
      ((1 - (s : ℝ)) * a u + (s : ℝ) * cc) -
        ((1 - (s : ℝ)) * b u + (s : ℝ) * (0 : ℝ)) := by ring
  rw [← hcomb] at hmem
  have hmemIoo : (1 - (s : ℝ)) * (a u - b u) + (s : ℝ) * cc ∈
      Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period) := by
    have hconv : Convex ℝ (Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period)) :=
      convex_Ioo _ _
    have hm : cc ∈ Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period) := by
      rw [hcc]
      constructor <;> nlinarith [period_pos]
    have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by have := s.2.2; linarith
    have h2 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have h3 : (1 - (s : ℝ)) + (s : ℝ) = 1 := by ring
    simpa [smul_eq_mul] using hconv (hwin u) hm h1 h2 h3
  rcases (AddSubgroup.mem_zmultiples_iff.mp hmem) with ⟨n, hn⟩
  have hval : (1 - (s : ℝ)) * (a u - b u) + (s : ℝ) * cc = (n : ℝ) * period := by
    rw [zsmul_eq_mul] at hn
    exact hn.symm
  have hnlow : ((k : ℝ) * period) < (n : ℝ) * period := by rw [← hval]; exact hmemIoo.1
  have hnhigh : (n : ℝ) * period < ((k : ℝ) + 1) * period := by rw [← hval]; exact hmemIoo.2
  have hk : k < n := by
    have hreal : (k : ℝ) < (n : ℝ) := by nlinarith [hnlow, period_pos]
    exact_mod_cast hreal
  have hnk : n < k + 1 := by
    have hcast : ((k : ℝ) + 1) = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
    have hreal : (n : ℝ) < ((k + 1 : ℤ) : ℝ) := by rw [← hcast]; nlinarith [hnhigh, period_pos]
    exact_mod_cast hreal
  omega

/-- **The real level homotopy (VERIFIED def)**: the straight-line homotopy
of the ordered pair `(a u, b u)` to the constant pair `(cc, 0)`, staying
off the diagonal by `orderedHomotopy_diff_notMem`. -/
noncomputable def orderedHomotopyFun {a b : ℝ → ℝ} {cc : ℝ} {k : ℤ}
    (hcc : cc = ((k : ℝ) + 1 / 2) * period)
    (hwin : ∀ u : ℝ, a u - b u ∈
      Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period))
    (u : ℝ) (s : I) : OrderedPairs :=
  ⟨(((1 - (s : ℝ)) * a u + (s : ℝ) * cc),
      ((1 - (s : ℝ)) * b u + (s : ℝ) * (0 : ℝ))),
    fun hcon => orderedHomotopy_diff_notMem k hcc hwin u s
      ((QuotientAddGroup.eq_iff_sub_mem).mp hcon)⟩

/-- The real level homotopy is continuous (VERIFIED). -/
lemma continuous_orderedHomotopyFun {a b : ℝ → ℝ} (haC : Continuous a)
    (hbC : Continuous b) {cc : ℝ} {k : ℤ}
    (hcc : cc = ((k : ℝ) + 1 / 2) * period)
    (hwin : ∀ u : ℝ, a u - b u ∈
      Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period)) :
    Continuous (fun p : ℝ × I => orderedHomotopyFun hcc hwin p.1 p.2) := by
  have hs : Continuous (fun p : ℝ × I => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have h1 : Continuous (fun p : ℝ × I =>
      ((1 - (p.2 : ℝ)) * a p.1 + (p.2 : ℝ) * cc : AddCircle period)) :=
    (AddCircle.continuous_mk' period).comp
      (((continuous_const.sub hs).mul (haC.comp continuous_fst)).add
        (hs.mul continuous_const))
  have h2 : Continuous (fun p : ℝ × I =>
      ((1 - (p.2 : ℝ)) * b p.1 + (p.2 : ℝ) * (0 : ℝ) : AddCircle period)) :=
    (AddCircle.continuous_mk' period).comp
      (((continuous_const.sub hs).mul (hbC.comp continuous_fst)).add
        (hs.mul continuous_const))
  exact Continuous.subtype_mk
    (p := fun q : AddCircle period × AddCircle period => q.1 ≠ q.2)
    (h1.prodMk h2)
    (fun x hcon => orderedHomotopy_diff_notMem k hcc hwin x.1 x.2
      ((QuotientAddGroup.eq_iff_sub_mem).mp hcon))

/-- The real level homotopy is `T`-periodic in its first variable
(VERIFIED). -/
lemma orderedHomotopyFun_periodic {a b : ℝ → ℝ} {cc : ℝ} {k : ℤ} {T : ℝ}
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u)
    (hcc : cc = ((k : ℝ) + 1 / 2) * period)
    (hwin : ∀ u : ℝ, a u - b u ∈
      Set.Ioo ((k : ℝ) * period) (((k : ℝ) + 1) * period)) (s : I) :
    Function.Periodic (fun u : ℝ => orderedHomotopyFun hcc hwin u s) T := by
  intro u
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (((1 - (s : ℝ)) * a (u + T) + (s : ℝ) * cc : ℝ) : AddCircle period) =
      (((1 - (s : ℝ)) * a u + (s : ℝ) * cc : ℝ) : AddCircle period)
    rw [haT u]
  · show (((1 - (s : ℝ)) * b (u + T) + (s : ℝ) * (0 : ℝ) : ℝ) : AddCircle period) =
      (((1 - (s : ℝ)) * b u + (s : ℝ) * (0 : ℝ) : ℝ) : AddCircle period)
    rw [hbT u]

/-- **The ordered lift loop is null-homotopic in the double cover
(VERIFIED)**: any loop of `OrderedPairs` whose two coordinates are
`T`-periodic and never congruent is null-homotopic — the explicit
straight-line homotopy above descends to the component circle. -/
theorem nullHomotopic_orderedLiftLoop {r : ℝ → Space} (c₀ : OSub r) {T : ℝ} [Fact (0 < T)]
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) {a b : ℝ → ℝ} (haC : Continuous a)
    (hbC : Continuous b)
    (hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period))
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) :
    ∃ c : OrderedPairs,
      ContinuousMap.Homotopic (orderedLiftLoop c₀ χ haC hbC hne haT hbT)
        (ContinuousMap.const (AddCircle T) c) := by
  classical
  have hdiff_ne : ∀ u : ℝ, a u - b u ∉ AddSubgroup.zmultiples period := fun u hmem =>
    hne u ((QuotientAddGroup.eq_iff_sub_mem).mpr hmem)
  rcases Commons.Analysis.Floor.interval_of_not_mem_zmultiples (haC.sub hbC) period_pos hdiff_ne with ⟨k, hwin⟩
  set cc : ℝ := ((k : ℝ) + 1 / 2) * period with hcc
  have hcc_ne : ((cc : AddCircle period)) ≠ ((0 : ℝ) : AddCircle period) := by
    intro hcon
    have hmem : cc ∈ AddSubgroup.zmultiples period := by
      simpa using (QuotientAddGroup.eq_iff_sub_mem).mp hcon
    rcases (AddSubgroup.mem_zmultiples_iff.mp hmem) with ⟨n, hn⟩
    rw [zsmul_eq_mul] at hn
    have hhalf : ((k : ℝ) + 1 / 2) = (n : ℝ) := by
      have h1 : (n : ℝ) * period = ((k : ℝ) + 1 / 2) * period := by rw [hn, hcc]
      exact (mul_right_cancel₀ (ne_of_gt period_pos) h1).symm
    have h2 : 2 * (k : ℝ) + 1 = 2 * (n : ℝ) := by linarith
    have h2' : (2 * k + 1 : ℤ) = 2 * n := by exact_mod_cast h2
    omega
  let ck : OrderedPairs := ⟨((cc : AddCircle period), ((0 : ℝ) : AddCircle period)), hcc_ne⟩
  have hGcont : Continuous (fun p : ℝ × I => orderedHomotopyFun hcc hwin p.1 p.2) :=
    continuous_orderedHomotopyFun haC hbC hcc hwin
  -- the descended homotopy
  refine ⟨ck, ⟨⟨fun q : I × AddCircle T =>
    AddCircle.liftIco T 0 (fun u => orderedHomotopyFun hcc hwin u q.1) q.2, ?_⟩, ?_, ?_⟩⟩
  · -- continuity by descent through the open quotient map
    have hq : IsOpenQuotientMap (Prod.map (id : I → I)
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples T))) :=
      IsOpenQuotientMap.prodMap IsOpenQuotientMap.id QuotientAddGroup.isOpenQuotientMap_mk
    refine (IsOpenQuotientMap.continuous_comp_iff hq
      (g := fun q : I × AddCircle T =>
        AddCircle.liftIco T 0 (fun u => orderedHomotopyFun hcc hwin u q.1) q.2)).mp ?_
    have heq : (fun q : I × AddCircle T =>
        AddCircle.liftIco T 0 (fun u => orderedHomotopyFun hcc hwin u q.1) q.2) ∘
        (Prod.map (id : I → I) (QuotientAddGroup.mk' (AddSubgroup.zmultiples T))) =
        (fun p : I × ℝ => orderedHomotopyFun hcc hwin p.2 p.1) := by
      funext p
      exact liftIco_zero_coe_apply_of_periodic
        (orderedHomotopyFun_periodic haT hbT hcc hwin p.1) p.2
    rw [heq]
    exact hGcont.comp (continuous_snd.prodMk continuous_fst)
  · -- at `s = 0` the homotopy is the ordered lift loop
    intro z
    rcases AddCircle.eq_coe_Ico z with ⟨u, -, huz⟩
    rw [← huz]
    change AddCircle.liftIco T 0 (fun u' => orderedHomotopyFun hcc hwin u' (0 : I))
        (u : AddCircle T) =
      orderedLiftLoop c₀ χ haC hbC hne haT hbT (u : AddCircle T)
    rw [liftIco_zero_coe_apply_of_periodic
      (orderedHomotopyFun_periodic haT hbT hcc hwin (0 : I)) u]
    rw [orderedLiftLoop_coe]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · apply congrArg (fun t : ℝ => (t : AddCircle period))
      have hz0 : ((0 : I) : ℝ) = 0 := rfl
      rw [hz0]
      ring
    · apply congrArg (fun t : ℝ => (t : AddCircle period))
      have hz0 : ((0 : I) : ℝ) = 0 := rfl
      rw [hz0]
      ring
  · -- at `s = 1` the homotopy is the constant pair
    intro z
    rcases AddCircle.eq_coe_Ico z with ⟨u, -, huz⟩
    rw [← huz]
    change AddCircle.liftIco T 0 (fun u' => orderedHomotopyFun hcc hwin u' (1 : I))
        (u : AddCircle T) =
      (ContinuousMap.const (AddCircle T) ck) (u : AddCircle T)
    rw [liftIco_zero_coe_apply_of_periodic
      (orderedHomotopyFun_periodic haT hbT hcc hwin (1 : I)) u]
    change orderedHomotopyFun hcc hwin u (1 : I) = ck
    refine Subtype.ext (Prod.ext ?_ ?_)
    · apply congrArg (fun t : ℝ => (t : AddCircle period))
      have hz1 : ((1 : I) : ℝ) = 1 := rfl
      rw [hz1]
      ring
    · apply congrArg (fun t : ℝ => (t : AddCircle period))
      have hz1 : ((1 : I) : ℝ) = 1 := rfl
      rw [hz1]
      ring

/-! ## 4. The class map of a circular component is null-homotopic -/

/-- **Null-homotopy of the component's class map from the even-branch
periodic endpoint lifts (VERIFIED)**: given the even branch of a circular
component with `T`-periodic endpoint real lifts, the descending class map
is null-homotopic in the band (compose the ordered lift loop's
null-homotopy with the covering projection). -/
theorem componentClassMap_nullHomotopic_of_periodic_endpoints {r : ℝ → Space}
    (c₀ : OSub r) {T : ℝ} [Fact (0 < T)] (χ : AddCircle T ≃ₜ TrisecantComponent r c₀)
    {sig : C(ℝ, OrderedPairs)} (hσl : mobiusCover ∘ sig = componentClassMap c₀ χ)
    {a b : ℝ → ℝ} (haC : Continuous a) (hbC : Continuous b)
    (ha : ∀ u : ℝ, (a u : AddCircle period) = (sig u).1.1)
    (hb : ∀ u : ℝ, (b u : AddCircle period) = (sig u).1.2)
    (haT : ∀ u : ℝ, a (u + T) = a u) (hbT : ∀ u : ℝ, b (u + T) = b u) :
    ∃ c : OpenMobius,
      ContinuousMap.Homotopic (componentCircleClassMap c₀ χ)
        (ContinuousMap.const (AddCircle T) c) := by
  have hne : ∀ u : ℝ, (a u : AddCircle period) ≠ (b u : AddCircle period) :=
    component_endpoint_classes_ne c₀ χ ha hb
  rcases nullHomotopic_orderedLiftLoop c₀ χ haC hbC hne haT hbT with ⟨c, hc⟩
  rcases Commons.Topology.Homotopy.nullHomotopic_comp_left
    ⟨mobiusCover, continuous_mobiusCover⟩ (f := orderedLiftLoop c₀ χ haC hbC hne haT hbT)
    ⟨c, hc⟩ with ⟨cm, hm⟩
  refine ⟨cm, ?_⟩
  -- identify the composite `mobiusCover ∘ orderedLiftLoop` with the class map
  have heq : componentCircleClassMap c₀ χ =
      (⟨mobiusCover, continuous_mobiusCover⟩ : C(OrderedPairs, OpenMobius)).comp
        (orderedLiftLoop c₀ χ haC hbC hne haT hbT) := by
    refine ContinuousMap.ext (fun z => ?_)
    exact (congrFun (mobiusCover_orderedLiftLoop c₀ χ hσl haC hbC ha hb hne haT hbT) z).symm
  rw [heq]
  exact hm

/-- **THE brick-(d) input (VERIFIED)**: under the general-position and
quadrisecant-free hypotheses, the class map of every circular component of
the trisecant set is null-homotopic in the band — no circular component of
`O` winds.  (The winding measurement of S279 supplies the even branch with
`ka = kb = 0`, hence `T`-periodic endpoint real lifts; the odd branch is
impossible.) -/
theorem circular_component_classMap_nullHomotopic {r : ℝ → Space}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) {T : ℝ} (hT : 0 < T)
    (χ : AddCircle T ≃ₜ TrisecantComponent r c₀) :
    ∃ c : OpenMobius,
      ContinuousMap.Homotopic (componentCircleClassMap c₀ χ)
        (ContinuousMap.const (AddCircle T) c) := by
  classical
  haveI : Fact (0 < T) := ⟨hT⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p : OrderedPairs,
      mobiusCover p = (componentClassMap c₀ χ 0 : OpenMobius) := by
    rcases (((χ (0 : AddCircle T) : TrisecantComponent r c₀) : OSub r).2) with ⟨m, p, hp, hm⟩
    exact ⟨p, by simpa [componentClassMap] using hp⟩
  rcases component_ordered_lift_real c₀ χ p₀ hp₀ with ⟨sig, -, hσl, hevodd⟩
  rcases hevodd with heven | hodd
  · -- EVEN branch: the endpoint advances vanish (S279), so the lifts are periodic
    rcases component_endpoints_lift_even c₀ χ hσl heven with
      ⟨a, b, haC, hbC, ha, hb, ⟨ka, hAadv⟩, ⟨kb, hBadv⟩⟩
    have hzero : ka = 0 ∧ kb = 0 :=
      even_endpoint_advances_zero h hqf hgp c₀ hT χ hσl haC hbC ha hb hAadv hBadv
    have haT : ∀ u : ℝ, a (u + T) = a u := fun u => by
      rw [hAadv u, hzero.1]
      ring
    have hbT : ∀ u : ℝ, b (u + T) = b u := fun u => by
      rw [hBadv u, hzero.2]
      ring
    exact componentClassMap_nullHomotopic_of_periodic_endpoints c₀ χ hσl haC hbC ha hb haT hbT
  · -- ODD branch: impossible (S279 once data)
    exfalso
    rcases component_endpoints_lift c₀ χ hσl with ⟨a, b, haC, hbC, ha, hb⟩
    exact once_winding_data_false h hqf hgp c₀ hT χ ⟨sig, hσl, hodd, a, b, haC, hbC, ha, hb⟩


/-! ## S281 — brick (d): the `Circle`-chart transport — the embedded circle
of a circular component is null-homotopic (VERIFIED, sorry-free)
(Submission/ComponentNullHomotopy.lean)

S280 proved that the class map `AddCircle T → OpenMobius` of a circular
component of the trisecant set is null-homotopic.  The (D) dichotomy and
`EmbeddedCircleWinding` work with the `Circle`-parametrised
`SimpleClosedCurve` of the component (S250 `component_simpleClosedCurve_of_circleHomeo`),
so this section transports the nullity across the chart homeomorphism
`paramCircleHomeo : AddCircle period ≜ Circle` (S253
`addCircleHomeo_of_circleHomeo`):

* **`nullHomotopic_of_comp_paramCircleHomeo`** (VERIFIED) — precomposition
  with a homeomorphism of the circle preserves null-homotopy: if
  `f ∘ paramCircleHomeo` is homotopic to a constant then so is `f` (the
  homotopy is reparametrised by `paramCircleHomeo.symm`);
* **`circular_component_curve_nullHomotopic`** (VERIFIED) — the embedded
  circle of a circular component of `O` is `IsNullHomotopic` in the
  `SimpleClosedCurve` vocabulary, with its image still the component
  val-set (the S250 form): the dichotomy's essential-circle branch is
  vacuous at the level the `EmbeddedCircleWinding` vocabulary consumes. -/

/-- **Precomposition with the circle homeomorphism preserves
null-homotopy (VERIFIED)**: if the circle map `f` becomes null-homotopic
after reparametrising its domain by `paramCircleHomeo : AddCircle period ≃ₜ
Circle`, then `f` itself is null-homotopic (reparametrise the homotopy by
`paramCircleHomeo.symm`). -/
lemma nullHomotopic_of_comp_paramCircleHomeo {X : Type*} [TopologicalSpace X]
    {f : C(Circle, X)}
    (h : ∃ c : X, ContinuousMap.Homotopic (f.comp paramCircleHomeo)
      (ContinuousMap.const (AddCircle period) c)) :
    ∃ c : X, ContinuousMap.Homotopic f (ContinuousMap.const Circle c) := by
  rcases h with ⟨c, H⟩
  rcases H with ⟨H⟩
  refine ⟨c, ⟨⟨fun p : I × Circle => H (p.1, paramCircleHomeo.symm p.2), ?_⟩, ?_, ?_⟩⟩
  · exact H.continuous.comp
      (continuous_fst.prodMk (paramCircleHomeo.symm.continuous.comp continuous_snd))
  · intro z
    change H (0, paramCircleHomeo.symm z) = f z
    rw [ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply]
    exact congrArg f (paramCircleHomeo.apply_symm_apply z)
  · intro z
    change H (1, paramCircleHomeo.symm z) = c
    rw [ContinuousMap.Homotopy.apply_one]
    rfl

/-- **Brick (d), `Circle`-chart form (VERIFIED)**: for a circular component
of the trisecant set under the general-position and quadrisecant-free
hypotheses, the embedded simple closed curve of the component (the S250
`SimpleClosedCurve`, whose image is the component's val-set) is
NULL-HOMOTOPIC: `γ.IsNullHomotopic` in the `EmbeddedCircleWinding`
vocabulary.  No circular component of `O` is essential — the (D)
dichotomy's winding branch is vacuous at the level the winding layer
consumes. -/
theorem circular_component_curve_nullHomotopic {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r)
    (χ : Circle ≃ₜ TrisecantComponent r c₀) :
    ∃ γ : SimpleClosedCurve OpenMobius, γ.IsNullHomotopic ∧
      γ.image = (fun s : OSub r => (s : OpenMobius)) ''
        (connectedComponent c₀ : Set (OSub r)) := by
  let f : C(Circle, OpenMobius) :=
    ⟨fun z : Circle => (((χ z : TrisecantComponent r c₀) : OSub r) : OpenMobius),
      (continuous_subtype_val.comp continuous_subtype_val).comp χ.continuous⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    apply χ.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hzw
  have hnull : ∃ c : OpenMobius, ContinuousMap.Homotopic f (ContinuousMap.const Circle c) := by
    apply nullHomotopic_of_comp_paramCircleHomeo
    have hT := circular_component_classMap_nullHomotopic h hqf hgp c₀ period_pos
      (addCircleHomeo_of_circleHomeo χ)
    have heq : componentCircleClassMap c₀ (addCircleHomeo_of_circleHomeo χ) =
        f.comp paramCircleHomeo := by
      ext u
      rfl
    rcases hT with ⟨c, hc⟩
    exact ⟨c, by rwa [heq] at hc⟩
  refine ⟨⟨f, hinj⟩, hnull, ?_⟩
  unfold SimpleClosedCurve.image
  ext c
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(χ z : TrisecantComponent r c₀), (χ z : TrisecantComponent r c₀).2, rfl⟩
  · rintro ⟨s, hs, hc⟩
    refine ⟨χ.symm ⟨s, hs⟩, ?_⟩
    show (((χ (χ.symm ⟨s, hs⟩) : TrisecantComponent r c₀) : OSub r) : OpenMobius) = c
    rw [χ.apply_symm_apply]
    simpa using hc

end LeanEval.KnotTheory.Quadrisecant
