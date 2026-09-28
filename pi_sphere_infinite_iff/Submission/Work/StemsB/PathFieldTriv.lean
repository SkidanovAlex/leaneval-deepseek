import Mathlib
import Submission.Work.StemsB.EvalOnePreimage
import Submission.Work.Bordism.HomotopyHomology

/-!
# The trivialisation of the path–loop fibration over a parameter space with a path field

Let `X` be a topological space, `x₀ : X`, `D ⊆ X`, and let `s : ↥D × I → X` be a *path field*:
`s (d, 0) = x₀` and `s (d, 1) = d` for all `d ∈ D`.  Then the preimage
`p⁻¹D = evalOnePreimage D` of the path–loop fibration `p = evalOne X x₀` over `D` should be
homotopy equivalent to the product `↥D × Ω`, `Ω = Path x₀ x₀`:

* `Work.StemsB.trivPathCM` — the loop `q * rev σ_{q(1)}` (the trivialisation, as a path);
* `Work.StemsB.sectPathCM` — the path `δ * σ_d` (the section, as a path).

## Status and plan (for the next stretch of work)

The concatenation `catCM`/`cat3Fun` and the path-level constructions above are done.  What remains
is the *packaging* of these as `ContinuousMap`s and the two homotopies:

* `Work.StemsB.trivCM D s h0 h1 : C(evalOnePreimage D, ↥D × Path x₀ x₀)`, `q ↦ (dOf D q, ⟨trivPathCM …⟩)`.
  Packaging recipe that is known to work (tested separately): prove the *uncurried* function
  `trivRaw : evalOnePreimage D × I → X` continuous by `Continuous.if_le` (see
  `bundlePullback_homotopyEquiv.lean` for the same pattern), then
  `continuous_induced_rng.mpr ((ContinuousMap.curry ⟨trivRaw, hcont⟩).continuous)` for the second
  component (this avoids the higher-order unification failure of `Path.continuous_uncurry_iff.mpr`).
* `Work.StemsB.sectCM D s h0 h1 : C(↥D × Path x₀ x₀, evalOnePreimage D)`, likewise.
* The two homotopies `sectCM ∘ trivCM ≃ id` and `trivCM ∘ sectCM ≃ id`, with the explicit
  "fold-squeezing" formulas described in `SPHLOOP_STEP1_NOTES.md`.
* `IsIso (homologyMap (chainMap ℤ (TopCat.of (evalOnePreimage D)) (TopCat.of (↥D × Path x₀ x₀))
  (TopCat.ofHom (trivCM …))) k)` via `Work.Cohomology.homologyEquiv ℤ …` and then the pair version
  via `Work.Cohomology.relChainsMapOf_homologyMap_isIso` applied to `D` and to `D' ⊆ D`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## Concatenation of paths -/

/-- Concatenation `α * β` of two paths, as an explicit function: `α` on the first half of the
interval and `β` on the second. -/
def catFun (α β : C(I, X)) (h : α 1 = β 0) (t : I) : X :=
  if (2 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (2 * (t : ℝ))) else β (clampI (2 * (t : ℝ) - 1))

theorem continuous_catFun (α β : C(I, X)) (h : α 1 = β 0) : Continuous (catFun α β h) := by
  rw [show catFun α β h = fun t : I =>
      if (2 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (2 * (t : ℝ)))
      else β (clampI (2 * (t : ℝ) - 1)) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · exact α.continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact β.continuous.comp (continuous_clampI.comp (by fun_prop))
  · fun_prop
  · fun_prop
  · intro t ht
    have ht1 : (2 : ℝ) * (t : ℝ) = 1 := by
      have h1 : 1 ≤ (2 : ℝ) * (t : ℝ) := by have := t.2.1; nlinarith [t.2.1]
      linarith
    rw [ht1, clampI_one]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, clampI_zero]
    exact h

/-- Concatenation of two paths with matching endpoints, as a continuous map. -/
def catCM (α β : C(I, X)) (h : α 1 = β 0) : C(I, X) :=
  ⟨catFun α β h, continuous_catFun α β h⟩

theorem catCM_zero (α β : C(I, X)) (h : α 1 = β 0) : catCM α β h 0 = α 0 := by
  show catFun α β h 0 = α 0
  rw [show catFun α β h 0 =
      (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then α (clampI (2 * (((0 : I)) : ℝ)))
        else β (clampI (2 * (((0 : I)) : ℝ) - 1))) from rfl]
  rw [if_pos (by norm_num)]
  rw [show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]

theorem catCM_one (α β : C(I, X)) (h : α 1 = β 0) : catCM α β h 1 = β 1 := by
  show catFun α β h 1 = β 1
  rw [show catFun α β h 1 =
      (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then α (clampI (2 * (((1 : I)) : ℝ)))
        else β (clampI (2 * (((1 : I)) : ℝ) - 1))) from rfl]
  rw [if_neg (by norm_num)]
  rw [show (2 : ℝ) * (((1 : I)) : ℝ) - 1 = 1 by norm_num, clampI_one]

/-- The triple concatenation `(α * β) * ζ`, as an explicit function. -/
def cat3Fun (α β ζ : C(I, X)) (t : I) : X :=
  if (4 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (4 * (t : ℝ)))
  else if (2 : ℝ) * (t : ℝ) ≤ 1 then β (clampI (4 * (t : ℝ) - 1))
  else ζ (clampI (2 * (t : ℝ) - 1))

theorem continuous_cat3Fun (α β ζ : C(I, X)) (h1 : α 1 = β 0) (h2 : β 1 = ζ 0) :
    Continuous (cat3Fun α β ζ) := by
  rw [show cat3Fun α β ζ = fun t : I =>
      if (4 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (4 * (t : ℝ)))
      else if (2 : ℝ) * (t : ℝ) ≤ 1 then β (clampI (4 * (t : ℝ) - 1))
      else ζ (clampI (2 * (t : ℝ) - 1)) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · exact α.continuous.comp (continuous_clampI.comp (by fun_prop))
  · refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact β.continuous.comp (continuous_clampI.comp (by fun_prop))
    · exact ζ.continuous.comp (continuous_clampI.comp (by fun_prop))
    · fun_prop
    · fun_prop
    · intro t ht
      have ht1 : (2 : ℝ) * (t : ℝ) = 1 := by
        have h1' : 1 ≤ (2 : ℝ) * (t : ℝ) := by have := t.2.1; nlinarith [t.2.1]
        linarith
      have e1 : (4 : ℝ) * (t : ℝ) - 1 = 1 := by
        rw [show (4 : ℝ) * (t : ℝ) = 2 * ((2 : ℝ) * (t : ℝ)) by ring, ht1]; norm_num
      have e2 : (2 : ℝ) * (t : ℝ) - 1 = 0 := by rw [ht1]; norm_num
      rw [e1, e2, clampI_one, clampI_zero] <;> exact h2
  · fun_prop
  · fun_prop
  · intro t ht
    have ht1 : (4 : ℝ) * (t : ℝ) = 1 := by
      have h1' : 1 ≤ (4 : ℝ) * (t : ℝ) := by have := t.2.1; nlinarith [t.2.1]
      linarith
    have e : (2 : ℝ) * (t : ℝ) ≤ 1 := by linarith [ht1]
    rw [ht1, clampI_one, if_pos e, show (1 : ℝ) - 1 = 0 by norm_num, clampI_zero] <;> exact h1

/-- At a quarter of the interval, the triple concatenation `(α * β) * ζ` agrees with `α`. -/
theorem cat3Fun_quarter (α β ζ : C(I, X)) (t : I) :
    cat3Fun α β ζ (clampI ((t : ℝ) / 4)) = α t := by
  have hval : (((clampI ((t : ℝ) / 4)) : I) : ℝ) = (t : ℝ) / 4 := by
    rw [clampI_of_mem (by constructor <;> [linarith [t.2.1]; linarith [t.2.2]])]
  have hcond : (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) ≤ 1 := by
    rw [hval]; nlinarith [t.2.2]
  have harg : (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) = (t : ℝ) := by
    rw [hval]; ring
  rw [show cat3Fun α β ζ (clampI ((t : ℝ) / 4)) =
      (if (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) ≤ 1
        then α (clampI (4 * (((clampI ((t : ℝ) / 4)) : I) : ℝ)))
        else if (2 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) ≤ 1
          then β (clampI (4 * (((clampI ((t : ℝ) / 4)) : I) : ℝ) - 1))
          else ζ (clampI (2 * (((clampI ((t : ℝ) / 4)) : I) : ℝ) - 1))) from rfl]
  rw [if_pos hcond, harg, clampI_coe_I]

/-! ## The path field, the trivialisation and the section -/

/-- The reverse of the path field at `d`: a path from `d` back to `x₀`. -/
def sigRev (D : Set X) (s : C(↥D × I, X)) (d : ↥D) : C(I, X) :=
  ⟨fun t => s (d, clampI (1 - (t : ℝ))),
    s.continuous.comp (continuous_const.prodMk (continuous_clampI.comp (by fun_prop)))⟩

theorem sigRev_zero (D : Set X) (s : C(↥D × I, X)) (d : ↥D) :
    sigRev D s d 0 = s (d, 1) := by
  show s (d, clampI (1 - (((0 : I)) : ℝ))) = s (d, 1)
  rw [show (1 : ℝ) - (((0 : I)) : ℝ) = 1 by norm_num, clampI_one]

theorem sigRev_one (D : Set X) (s : C(↥D × I, X)) (d : ↥D) :
    sigRev D s d 1 = s (d, 0) := by
  show s (d, clampI (1 - (((1 : I)) : ℝ))) = s (d, 0)
  rw [show (1 : ℝ) - (((1 : I)) : ℝ) = 0 by norm_num, clampI_zero]

/-- The path field at `d`: a path from `x₀` to `d`. -/
def sigFwd (D : Set X) (s : C(↥D × I, X)) (d : ↥D) : C(I, X) :=
  ⟨fun t => s (d, t), s.continuous.comp (continuous_const.prodMk continuous_id)⟩

theorem sigFwd_zero (D : Set X) (s : C(↥D × I, X)) (d : ↥D) :
    sigFwd D s d 0 = s (d, 0) := rfl

theorem sigFwd_one (D : Set X) (s : C(↥D × I, X)) (d : ↥D) :
    sigFwd D s d 1 = s (d, 1) := rfl

/-- The base point of the parameter space attached to a point of the preimage. -/
def dOf (D : Set X) (q : evalOnePreimage (x₀ := x₀) D) : ↥D :=
  ⟨(evalOne X x₀) q.1, q.2⟩

theorem continuous_dOf (D : Set X) : Continuous (dOf (x₀ := x₀) D) :=
  Continuous.subtype_mk ((evalOne X x₀).continuous.comp continuous_subtype_val) _

theorem coe_dOf (D : Set X) (q : evalOnePreimage (x₀ := x₀) D) :
    ((dOf D q : ↥D) : X) = q.1.1 1 := rfl

/-- The path `γ * rev σ_d`, a loop at `x₀`. -/
def trivPathCM (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (q : evalOnePreimage (x₀ := x₀) D) : C(I, X) :=
  catCM q.1.1 (sigRev D s (dOf D q)) (by
    show q.1.1 1 = sigRev D s (dOf D q) 0
    rw [sigRev_zero, h1, coe_dOf])

theorem trivPathCM_zero (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (q : evalOnePreimage (x₀ := x₀) D) : trivPathCM D s h1 q 0 = x₀ := by
  show catCM q.1.1 (sigRev D s (dOf D q)) _ 0 = x₀
  rw [catCM_zero]
  exact q.1.2

theorem trivPathCM_one (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (q : evalOnePreimage (x₀ := x₀) D) :
    trivPathCM D s h1 q 1 = x₀ := by
  show catCM q.1.1 (sigRev D s (dOf D q)) _ 1 = x₀
  rw [catCM_one, sigRev_one]
  exact h0 (dOf D q)

/-- The path `δ * σ_d`, a path from `x₀` to `d`. -/
def sectPathCM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (d : ↥D) (δ : Path x₀ x₀) : C(I, X) :=
  catCM δ.toContinuousMap (sigFwd D s d) (by
    show δ.toContinuousMap 1 = sigFwd D s d 0
    rw [sigFwd_zero, h0]
    exact δ.target')

theorem sectPathCM_zero (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (d : ↥D) (δ : Path x₀ x₀) : sectPathCM D s h0 d δ 0 = x₀ := by
  show catCM δ.toContinuousMap (sigFwd D s d) _ 0 = x₀
  rw [catCM_zero]
  exact δ.source'

theorem sectPathCM_one (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (d : ↥D) (δ : Path x₀ x₀) :
    sectPathCM D s h0 d δ 1 = (d : X) := by
  show catCM δ.toContinuousMap (sigFwd D s d) _ 1 = (d : X)
  rw [catCM_one, sigFwd_one, h1]

/-- The uncurried trivialisation `(q,t) ↦ (q * rev σ_{q(1)})(t)`. -/
def trivRaw (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (w : (evalOnePreimage (x₀ := x₀) D) × I) : X :=
  if (2 : ℝ) * ((w.2 : I) : ℝ) ≤ 1 then w.1.1.1 (clampI (2 * ((w.2 : I) : ℝ)))
  else s (dOf D w.1, clampI (1 - (((clampI (2 * ((w.2 : I) : ℝ) - 1)) : I) : ℝ)))

theorem continuous_trivRaw (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X)) :
    Continuous (trivRaw (x₀ := x₀) D s h1) := by
  rw [show trivRaw (x₀ := x₀) D s h1 = fun w =>
      if (2 : ℝ) * ((w.2 : I) : ℝ) ≤ 1 then w.1.1.1 (clampI (2 * ((w.2 : I) : ℝ)))
      else s (dOf D w.1, clampI (1 - (((clampI (2 * ((w.2 : I) : ℝ) - 1)) : I) : ℝ)))
      from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hq : Continuous fun w : (evalOnePreimage (x₀ := x₀) D) × I => w.1.1.1 := by
      fun_prop
    exact continuous_eval.comp (hq.prodMk (continuous_clampI.comp (by fun_prop)))
  · have hd : Continuous fun w : (evalOnePreimage (x₀ := x₀) D) × I =>
        (dOf D w.1, clampI (1 - (((clampI (2 * ((w.2 : I) : ℝ) - 1)) : I) : ℝ))) :=
      ((continuous_dOf D).comp continuous_fst).prodMk (continuous_clampI.comp (by fun_prop))
    exact s.continuous.comp hd
  · fun_prop
  · fun_prop
  · intro w hw
    have h2 : (2 : ℝ) * ((w.2 : I) : ℝ) = 1 := hw
    have hz : (2 : ℝ) * ((w.2 : I) : ℝ) - 1 = 0 := by rw [h2]; norm_num
    show w.1.1.1 (clampI (2 * ((w.2 : I) : ℝ))) =
      s (dOf D w.1, clampI (1 - (((clampI (2 * ((w.2 : I) : ℝ) - 1)) : I) : ℝ)))
    have e : (1 : ℝ) - 1 = 0 := by norm_num
    have e0 : ((0 : I) : ℝ) = 0 := rfl
    simp only [hz, clampI_zero, e, e0, sub_zero, clampI_one, h2, h1, coe_dOf]

/-- **The trivialisation** `q ↦ (q(1), q * rev σ_{q(1)})` of the path–loop fibration over `D`. -/
def trivCM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) : C(evalOnePreimage (x₀ := x₀) D, ↥D × Path x₀ x₀) :=
  ⟨fun q => (dOf D q, ⟨trivPathCM D s h1 q, trivPathCM_zero D s h1 q,
      trivPathCM_one D s h0 h1 q⟩),
    Continuous.prodMk (continuous_dOf D) (continuous_induced_rng.mpr
      ((ContinuousMap.curry (⟨(trivRaw (x₀ := x₀) D s h1),
        continuous_trivRaw D s h1⟩ : C((evalOnePreimage (x₀ := x₀) D) × I, X))).continuous))⟩

/-- The uncurried section `((d,δ),t) ↦ (δ * σ_d)(t)`. -/
def sectRaw (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (w : (↥D × Path x₀ x₀) × I) : X :=
  if (2 : ℝ) * ((w.2 : I) : ℝ) ≤ 1 then w.1.2.toContinuousMap (clampI (2 * ((w.2 : I) : ℝ)))
  else s (w.1.1, clampI (2 * ((w.2 : I) : ℝ) - 1))

theorem continuous_sectRaw (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀) :
    Continuous (sectRaw (x₀ := x₀) D s h0) := by
  rw [show sectRaw (x₀ := x₀) D s h0 = fun w =>
      if (2 : ℝ) * ((w.2 : I) : ℝ) ≤ 1 then
        w.1.2.toContinuousMap (clampI (2 * ((w.2 : I) : ℝ)))
      else s (w.1.1, clampI (2 * ((w.2 : I) : ℝ) - 1)) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hd : Continuous fun w : (↥D × Path x₀ x₀) × I => w.1.2.toContinuousMap := by
      fun_prop
    exact continuous_eval.comp (hd.prodMk (continuous_clampI.comp (by fun_prop)))
  · have hd : Continuous fun w : (↥D × Path x₀ x₀) × I =>
        (w.1.1, clampI (2 * ((w.2 : I) : ℝ) - 1)) :=
      (continuous_fst.fst).prodMk (continuous_clampI.comp (by fun_prop))
    exact s.continuous.comp hd
  · fun_prop
  · fun_prop
  · intro w hw
    have h2 : (2 : ℝ) * ((w.2 : I) : ℝ) = 1 := hw
    show w.1.2.toContinuousMap (clampI (2 * ((w.2 : I) : ℝ))) =
      s (w.1.1, clampI (2 * ((w.2 : I) : ℝ) - 1))
    have e : (1 : ℝ) - 1 = 0 := by norm_num
    have e0 : ((0 : I) : ℝ) = 0 := rfl
    simp only [h2, clampI_one, e, clampI_zero, e0, sub_zero, h0]
    exact w.1.2.target'

/-- The section, as a map into the path space (before restricting the endpoint). -/
def sectCMaux (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀) :
    C(↥D × Path x₀ x₀, PathSpace X x₀) where
  toFun w := ⟨sectPathCM D s h0 w.1 w.2, sectPathCM_zero D s h0 w.1 w.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (ContinuousMap.curry (⟨sectRaw (x₀ := x₀) D s h0,
      continuous_sectRaw (x₀ := x₀) D s h0⟩ : C((↥D × Path x₀ x₀) × I, X))).continuous

/-- **The section** `(d,δ) ↦ (d, δ * σ_d)` of the trivialisation. -/
def sectCM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    C(↥D × Path x₀ x₀, evalOnePreimage (x₀ := x₀) D) :=
  ⟨fun w => ⟨sectCMaux D s h0 w, by
      have he : (sectCMaux D s h0 w).1 1 = (w.1 : X) :=
        sectPathCM_one D s h0 h1 w.1 w.2
      exact he ▸ w.1.2⟩,
    Continuous.subtype_mk (sectCMaux D s h0).continuous (fun w => by
      have he : (sectCMaux D s h0 w).1 1 = (w.1 : X) :=
        sectPathCM_one D s h0 h1 w.1 w.2
      exact he ▸ w.1.2)⟩

theorem coe_clampI_of_mem {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ((clampI r : I) : ℝ) = r := by
  rw [clampI_of_mem hr]

/-- The nested concatenation `(α * β) * ζ` agrees, as a function, with the three-branch formula
`cat3Fun α β ζ`. -/
theorem catFun_catCM_apply (α β ζ : C(I, X)) (h1 : α 1 = β 0) (h2 : β 1 = ζ 0) (t : I) :
    catFun (catCM α β h1) ζ (by rw [catCM_one, h2]) t = cat3Fun α β ζ t := by
  rw [show catFun (catCM α β h1) ζ (by rw [catCM_one, h2]) t =
      (if (2 : ℝ) * (t : ℝ) ≤ 1 then (catCM α β h1) (clampI (2 * (t : ℝ)))
       else ζ (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [show cat3Fun α β ζ t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then β (clampI (4 * (t : ℝ) - 1))
       else ζ (clampI (2 * (t : ℝ) - 1))) from rfl]
  by_cases h4 : (4 : ℝ) * (t : ℝ) ≤ 1
  · have h2t : (2 : ℝ) * (t : ℝ) ≤ 1 := by linarith
    have hc : ((clampI (2 * (t : ℝ)) : I) : ℝ) = 2 * (t : ℝ) :=
      coe_clampI_of_mem (by
        constructor <;> [linarith [t.2.1]; linarith])
    have hcc : (2 : ℝ) * (2 * (t : ℝ)) = 4 * (t : ℝ) := by ring
    rw [if_pos h2t, if_pos h4]
    show (catCM α β h1) (clampI (2 * (t : ℝ))) = α (clampI (4 * (t : ℝ)))
    rw [show (catCM α β h1) (clampI (2 * (t : ℝ))) =
        (if (2 : ℝ) * (((clampI (2 * (t : ℝ))) : I) : ℝ) ≤ 1 then
          α (clampI (2 * (((clampI (2 * (t : ℝ))) : I) : ℝ)))
         else β (clampI (2 * (((clampI (2 * (t : ℝ))) : I) : ℝ) - 1))) from rfl]
    have hcond : (2 : ℝ) * (((clampI (2 * (t : ℝ))) : I) : ℝ) ≤ 1 := by
      rw [hc]; linarith
    rw [if_pos hcond, hc, hcc]
  · rw [if_neg h4]
    by_cases h2t : (2 : ℝ) * (t : ℝ) ≤ 1
    · have hc : ((clampI (2 * (t : ℝ)) : I) : ℝ) = 2 * (t : ℝ) :=
        coe_clampI_of_mem (by
          constructor <;> [linarith [t.2.1]; linarith])
      simp only [if_pos h2t]
      show (catCM α β h1) (clampI (2 * (t : ℝ))) = β (clampI (4 * (t : ℝ) - 1))
      rw [show (catCM α β h1) (clampI (2 * (t : ℝ))) =
          (if (2 : ℝ) * (((clampI (2 * (t : ℝ))) : I) : ℝ) ≤ 1 then
            α (clampI (2 * (((clampI (2 * (t : ℝ))) : I) : ℝ)))
           else β (clampI (2 * (((clampI (2 * (t : ℝ))) : I) : ℝ) - 1))) from rfl]
      have hcond : ¬ (2 : ℝ) * (((clampI (2 * (t : ℝ))) : I) : ℝ) ≤ 1 := by
        rw [hc]; linarith
      rw [if_neg hcond, hc]
      congr 1
      ring
    · simp only [if_neg h2t]

/-- The "fold" argument of the stage-one homotopy: at time `t`, the loop `σ_d * rev σ_d` is
traversed, with `φ t = 2 - 4t` on the first half and `2t - 1` on the second. -/
def foldFun (t : I) : ℝ :=
  if (2 : ℝ) * (t : ℝ) ≤ 1 then 2 - 4 * (t : ℝ) else 2 * (t : ℝ) - 1

theorem foldFun_eq (t : I) :
    foldFun t = (if (2 : ℝ) * (t : ℝ) ≤ 1 then 2 - 4 * (t : ℝ) else 2 * (t : ℝ) - 1) :=
  rfl

theorem foldFun_quarter {t : I} (ht : (4 : ℝ) * (t : ℝ) = 1) : foldFun t = 1 := by
  have ht' : (t : ℝ) = 1 / 4 := by linarith
  rw [foldFun_eq, if_pos (by rw [ht']; norm_num)]
  rw [ht']; norm_num

theorem continuous_foldFun : Continuous foldFun := by
  rw [show foldFun = fun t : I =>
      (if (2 : ℝ) * (t : ℝ) ≤ 1 then 2 - 4 * (t : ℝ) else 2 * (t : ℝ) - 1) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro t ht
    have h4 : (4 : ℝ) * (t : ℝ) = 2 * ((2 : ℝ) * (t : ℝ)) := by ring
    rw [h4, ht]; norm_num

/-- The stage-one homotopy formula on the preimage: at parameter `u`, the `γ`-part fills the first
quarter of the interval and the "out and back" loop `σ_d * rev σ_d` — the fold — is squeezed
towards the endpoint `d` by the factor `1 - u`. -/
def A1Raw (D : Set X) (s : C(↥D × I, X)) (u : I) (q : evalOnePreimage (x₀ := x₀) D)
    (t : I) : X :=
  if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
  else s (dOf D q, clampI ((1 - (u : ℝ)) * foldFun t + (u : ℝ)))

theorem continuous_A1Raw (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X)) :
    Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
      A1Raw (x₀ := x₀) D s w.1.1 w.1.2 w.2 := by
  rw [show (fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
      A1Raw (x₀ := x₀) D s w.1.1 w.1.2 w.2) = fun w =>
      (if (4 : ℝ) * ((w.2 : I) : ℝ) ≤ 1 then w.1.2.1.1 (clampI (4 * ((w.2 : I) : ℝ)))
       else s (dOf D w.1.2, clampI ((1 - ((w.1.1 : I) : ℝ)) * foldFun w.2
         + ((w.1.1 : I) : ℝ)))) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hq : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I => w.1.2.1.1 := by
      fun_prop
    exact continuous_eval.comp (hq.prodMk (continuous_clampI.comp (by fun_prop)))
  · have hφ : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I => foldFun w.2 :=
      continuous_foldFun.comp continuous_snd
    have hu : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I => ((w.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hd : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        (dOf D w.1.2, clampI ((1 - ((w.1.1 : I) : ℝ)) * foldFun w.2 + ((w.1.1 : I) : ℝ))) :=
      ((continuous_dOf D).comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_clampI.comp (((continuous_const.sub hu).mul hφ).add hu))
    exact s.continuous.comp hd
  · fun_prop
  · fun_prop
  · intro w hw
    have h2 : (4 : ℝ) * ((w.2 : I) : ℝ) = 1 := hw
    have hc : (((clampI (4 * ((w.2 : I) : ℝ))) : I) : ℝ) = 4 * ((w.2 : I) : ℝ) :=
      coe_clampI_of_mem (by constructor <;> [linarith [w.2.1]; linarith [h2]])
    have harg : (1 - ((w.1.1 : I) : ℝ)) * foldFun w.2 + ((w.1.1 : I) : ℝ) = 1 := by
      rw [foldFun_quarter h2]; ring
    rw [harg, clampI_one, h1, coe_dOf, h2, clampI_one]

/-- The combined two-stage homotopy formula for `sectCM ∘ trivCM`: for `r ≤ 1/2` the stage-one
formula at parameter `2r`, and for `r ≥ 1/2` the stage-one formula at parameter `1` with the
`γ`-quarter stretched over the whole interval ("pause"). -/
def homARaw (D : Set X) (s : C(↥D × I, X))
    (w : (I × evalOnePreimage (x₀ := x₀) D) × I) : X :=
  if (2 : ℝ) * ((w.1.1 : I) : ℝ) ≤ 1 then
    A1Raw (x₀ := x₀) D s (clampI (2 * ((w.1.1 : I) : ℝ))) w.1.2 w.2
  else
    A1Raw (x₀ := x₀) D s 1 w.1.2
      (clampI ((7 : ℝ) / 4 * ((w.2 : I) : ℝ)
        - (3 : ℝ) / 2 * ((w.1.1 : I) : ℝ) * ((w.2 : I) : ℝ)))

theorem continuous_homARaw (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X)) :
    Continuous (homARaw (x₀ := x₀) D s) := by
  rw [show homARaw (x₀ := x₀) D s = fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
      (if (2 : ℝ) * ((w.1.1 : I) : ℝ) ≤ 1 then
        A1Raw (x₀ := x₀) D s (clampI (2 * ((w.1.1 : I) : ℝ))) w.1.2 w.2
       else A1Raw (x₀ := x₀) D s 1 w.1.2
        (clampI ((7 : ℝ) / 4 * ((w.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((w.1.1 : I) : ℝ) * ((w.2 : I) : ℝ)))) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · -- first branch: stage one at parameter `clampI (2r)`
    have hu' : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        ((w.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hm : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        ((clampI (2 * ((w.1.1 : I) : ℝ)), w.1.2), w.2) :=
      ((continuous_clampI.comp (continuous_const.mul hu')).prodMk
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd
    exact (continuous_A1Raw D s h1).comp hm
  · -- second branch: stage one at parameter `1`, time reparametrised
    have hu' : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        ((w.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hv : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        ((w.2 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have hcoef : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        ((7 : ℝ) / 4 * ((w.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((w.1.1 : I) : ℝ) * ((w.2 : I) : ℝ)) :=
      ((continuous_const (y := (7 : ℝ) / 4)).mul hv).sub
        (((continuous_const (y := (3 : ℝ) / 2)).mul hu').mul hv)
    have hm : Continuous fun w : (I × evalOnePreimage (x₀ := x₀) D) × I =>
        (((1 : I), w.1.2), clampI ((7 : ℝ) / 4 * ((w.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((w.1.1 : I) : ℝ) * ((w.2 : I) : ℝ))) :=
      (((continuous_const (y := (1 : I))).prodMk
        (continuous_snd.comp continuous_fst)).prodMk (continuous_clampI.comp hcoef))
    exact (continuous_A1Raw D s h1).comp hm
  · fun_prop
  · fun_prop
  · intro w hw
    have hw2 : ((w.1.1 : I) : ℝ) = 1 / 2 := by linarith
    have hcoef : (7 : ℝ) / 4 * ((w.2 : I) : ℝ)
        - (3 : ℝ) / 2 * ((w.1.1 : I) : ℝ) * ((w.2 : I) : ℝ) = ((w.2 : I) : ℝ) := by
      rw [hw2]; ring
    rw [hw, clampI_one, hcoef, clampI_coe_I]

/-- At homotopy parameter `0`, the combined formula is the stage-one formula at parameter `0`
(which is the composite `sectCM ∘ trivCM`, by `catFun_catCM_apply`). -/
theorem homARaw_zero (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D) (t : I) :
    homARaw (x₀ := x₀) D s (((0 : I), q), t) = A1Raw (x₀ := x₀) D s 0 q t := by
  rw [show homARaw (x₀ := x₀) D s (((0 : I), q), t) =
      (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then
        A1Raw (x₀ := x₀) D s (clampI (2 * (((0 : I)) : ℝ))) q t
       else A1Raw (x₀ := x₀) D s 1 q
        (clampI ((7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((0 : I)) : ℝ) * (t : ℝ))))
      from rfl]
  rw [if_pos (by norm_num), show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]

/-- At homotopy parameter `1`, the combined formula is the identity map (the "pause" has stretched
the `γ`-quarter over the whole interval). -/
theorem homARaw_one (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D) (t : I) :
    homARaw (x₀ := x₀) D s (((1 : I), q), t) = q.1.1.1 (clampI (t : ℝ)) := by
  rw [show homARaw (x₀ := x₀) D s (((1 : I), q), t) =
      (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then
        A1Raw (x₀ := x₀) D s (clampI (2 * (((1 : I)) : ℝ))) q t
       else A1Raw (x₀ := x₀) D s 1 q
        (clampI ((7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((1 : I)) : ℝ) * (t : ℝ))))
      from rfl]
  rw [if_neg (by norm_num)]
  rw [show (7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((1 : I)) : ℝ) * (t : ℝ) = (t : ℝ) / 4 by
    rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring]
  rw [show A1Raw (x₀ := x₀) D s 1 q (clampI ((t : ℝ) / 4)) =
      (if (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) ≤ 1 then
        q.1.1.1 (clampI (4 * (((clampI ((t : ℝ) / 4)) : I) : ℝ)))
       else s (dOf D q, clampI ((1 - (((1 : I)) : ℝ)) * foldFun (clampI ((t : ℝ) / 4))
         + (((1 : I)) : ℝ)))) from rfl]
  have h4 : (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) = (t : ℝ) := by
    rw [coe_clampI_of_mem (by constructor <;> [linarith [t.2.1]; linarith [t.2.2]])]
    ring
  rw [if_pos (by rw [h4]; exact t.2.2), h4, clampI_coe_I]

/-- The middle branch of the composite identification: for `1/4 ≤ t ≤ 1/2` the three-branch formula
agrees with the stage-one formula at parameter `0`. -/
theorem cat3Fun_eq_A1Raw_mid (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D)
    (t : I) (h4 : ¬ ((4 : ℝ) * (t : ℝ) ≤ 1)) (h2t : (2 : ℝ) * (t : ℝ) ≤ 1) :
    cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t
      = A1Raw (x₀ := x₀) D s 0 q t := by
  rw [show cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigRev D s (dOf D q)) (clampI (4 * (t : ℝ) - 1))
       else (sigFwd D s (dOf D q)) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [if_neg h4, if_pos h2t]
  rw [show A1Raw (x₀ := x₀) D s 0 q t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else s (dOf D q, clampI ((1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ))))
      from rfl]
  rw [if_neg h4]
  show (sigRev D s (dOf D q)) (clampI (4 * (t : ℝ) - 1))
      = s (dOf D q, clampI ((1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ)))
  have h4' : 1 < (4 : ℝ) * (t : ℝ) := not_le.mp h4
  have hc : ((clampI (4 * (t : ℝ) - 1) : I) : ℝ) = 4 * (t : ℝ) - 1 :=
    coe_clampI_of_mem (by constructor <;> [linarith; linarith [h2t]])
  have hfold : foldFun t = 2 - 4 * (t : ℝ) := by
    rw [foldFun_eq, if_pos h2t]
  have harg : (1 : ℝ) - ((clampI (4 * (t : ℝ) - 1) : I) : ℝ)
      = (1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ) := by
    rw [hc, hfold, show (((0 : I)) : ℝ) = 0 from rfl]
    ring
  rw [show (sigRev D s (dOf D q)) (clampI (4 * (t : ℝ) - 1))
      = s (dOf D q, clampI (1 - ((clampI (4 * (t : ℝ) - 1) : I) : ℝ))) from rfl]
  rw [← harg]

/-- The first outer branch of the composite identification: for `4t ≤ 1` both the three-branch
formula and the stage-one formula at parameter `0` are `γ (clampI (4t))`. -/
theorem cat3Fun_eq_A1Raw_low (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D)
    (t : I) (h4 : (4 : ℝ) * (t : ℝ) ≤ 1) :
    cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t
      = A1Raw (x₀ := x₀) D s 0 q t := by
  rw [show cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigRev D s (dOf D q)) (clampI (4 * (t : ℝ) - 1))
       else (sigFwd D s (dOf D q)) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [if_pos h4]
  rw [show A1Raw (x₀ := x₀) D s 0 q t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else s (dOf D q, clampI ((1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ))))
      from rfl]
  rw [if_pos h4]

/-- The second outer branch of the composite identification: for `¬ (2t ≤ 1)` both the three-branch
formula and the stage-one formula at parameter `0` are `s (dOf D q, clampI (2t-1))`. -/
theorem cat3Fun_eq_A1Raw_high (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D)
    (t : I) (h2t : ¬ ((2 : ℝ) * (t : ℝ) ≤ 1)) :
    cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t
      = A1Raw (x₀ := x₀) D s 0 q t := by
  have h4 : ¬ ((4 : ℝ) * (t : ℝ) ≤ 1) := by
    intro h
    exact h2t (by linarith)
  rw [show cat3Fun q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q)) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigRev D s (dOf D q)) (clampI (4 * (t : ℝ) - 1))
       else (sigFwd D s (dOf D q)) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [if_neg h4, if_neg h2t]
  rw [show A1Raw (x₀ := x₀) D s 0 q t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
       else s (dOf D q, clampI ((1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ))))
      from rfl]
  rw [if_neg h4]
  have hfold : foldFun t = 2 * (t : ℝ) - 1 := by
    rw [foldFun_eq, if_neg h2t]
  rw [show (sigFwd D s (dOf D q)) (clampI (2 * (t : ℝ) - 1))
      = s (dOf D q, clampI (2 * (t : ℝ) - 1)) from rfl]
  rw [show (1 - (((0 : I)) : ℝ)) * foldFun t + (((0 : I)) : ℝ)
      = 2 * (t : ℝ) - 1 by
    rw [hfold, show (((0 : I)) : ℝ) = 0 from rfl]; ring]

/-- **The composite `sectCM ∘ trivCM` computes to `A1Raw` at parameter `0`.**  This is the
identification of the stage-one homotopy's `r = 0` endpoint with the composite map: the path
`(γ * rev σ_d) * σ_d` evaluated at time `t` is `A1Raw D s 0 q t`. -/
theorem catFun_triv_sect (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (q : evalOnePreimage (x₀ := x₀) D) (t : I) :
    catFun (catCM q.1.1 (sigRev D s (dOf D q)) (by
        show q.1.1 1 = sigRev D s (dOf D q) 0
        rw [sigRev_zero, h1, coe_dOf]))
      (sigFwd D s (dOf D q)) (by
        show (catCM q.1.1 (sigRev D s (dOf D q)) _) 1 = sigFwd D s (dOf D q) 0
        rw [catCM_one, sigRev_one]
        rfl)
      t = A1Raw (x₀ := x₀) D s 0 q t := by
  rw [catFun_catCM_apply q.1.1 (sigRev D s (dOf D q)) (sigFwd D s (dOf D q))
    (by rw [sigRev_zero, h1, coe_dOf]) (by rw [sigRev_one]; rfl) t]
  by_cases h4 : (4 : ℝ) * (t : ℝ) ≤ 1
  · exact cat3Fun_eq_A1Raw_low D s q t h4
  · by_cases h2t : (2 : ℝ) * (t : ℝ) ≤ 1
    · exact cat3Fun_eq_A1Raw_mid D s q t h4 h2t
    · exact cat3Fun_eq_A1Raw_high D s q t h2t

theorem A1Raw_zero (D : Set X) (s : C(↥D × I, X)) (u : I) (q : evalOnePreimage (x₀ := x₀) D) :
    A1Raw (x₀ := x₀) D s u q 0 = x₀ := by
  rw [show A1Raw (x₀ := x₀) D s u q 0 =
      (if (4 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (((0 : I)) : ℝ)))
       else s (dOf D q, clampI ((1 - (u : ℝ)) * foldFun (0 : I) + (u : ℝ)))) from rfl]
  rw [if_pos (by norm_num), show (4 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]
  exact q.1.2

theorem A1Raw_one_mem (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (u : I) (q : evalOnePreimage (x₀ := x₀) D) : A1Raw (x₀ := x₀) D s u q 1 ∈ D := by
  rw [show A1Raw (x₀ := x₀) D s u q 1 =
      (if (4 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (((1 : I)) : ℝ)))
       else s (dOf D q, clampI ((1 - (u : ℝ)) * foldFun (1 : I) + (u : ℝ)))) from rfl]
  rw [if_neg (by norm_num)]
  have hfold : foldFun (1 : I) = 1 := by
    rw [foldFun_eq, if_neg (by norm_num)]
    norm_num
  rw [show (1 - (u : ℝ)) * foldFun (1 : I) + (u : ℝ) = 1 by rw [hfold]; ring,
    clampI_one, h1]
  exact (dOf D q).2

theorem homARaw_at_zero (D : Set X) (s : C(↥D × I, X)) (q : evalOnePreimage (x₀ := x₀) D)
    (r : I) : homARaw (x₀ := x₀) D s ((r, q), (0 : I)) = x₀ := by
  rw [show homARaw (x₀ := x₀) D s ((r, q), (0 : I)) =
      (if (2 : ℝ) * ((r : I) : ℝ) ≤ 1 then
        A1Raw (x₀ := x₀) D s (clampI (2 * ((r : I) : ℝ))) q (0 : I)
       else A1Raw (x₀ := x₀) D s 1 q
        (clampI ((7 : ℝ) / 4 * (((0 : I)) : ℝ)
          - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((0 : I)) : ℝ)))) from rfl]
  by_cases hr : (2 : ℝ) * ((r : I) : ℝ) ≤ 1
  · rw [if_pos hr]; exact A1Raw_zero D s _ q
  · rw [if_neg hr]
    rw [show (7 : ℝ) / 4 * (((0 : I)) : ℝ)
        - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]
    exact A1Raw_zero D s _ q


/-- The endpoint of the stage-one formula at parameter `1` lands in `D`, provided the time is at
least a quarter: for `4t = 1` the first branch gives `γ (clampI 1) = γ 1 = d`, and for `4t > 1` the
else branch gives `s (d, 1) = d`. -/
theorem A1Raw_one_mem_of_le (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (q : evalOnePreimage (x₀ := x₀) D) (t : I) (h : 1 ≤ (4 : ℝ) * (t : ℝ)) :
    A1Raw (x₀ := x₀) D s 1 q t ∈ D := by
  rcases lt_or_eq_of_le h with h' | h'
  · rw [show A1Raw (x₀ := x₀) D s 1 q t =
        (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
         else s (dOf D q, clampI ((1 - (((1 : I)) : ℝ)) * foldFun t + (((1 : I)) : ℝ))))
        from rfl]
    rw [if_neg (by linarith)]
    rw [show (1 - (((1 : I)) : ℝ)) * foldFun t + (((1 : I)) : ℝ) = 1 by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring]
    rw [clampI_one, h1]
    exact (dOf D q).2
  · rw [show A1Raw (x₀ := x₀) D s 1 q t =
        (if (4 : ℝ) * (t : ℝ) ≤ 1 then q.1.1.1 (clampI (4 * (t : ℝ)))
         else s (dOf D q, clampI ((1 - (((1 : I)) : ℝ)) * foldFun t + (((1 : I)) : ℝ))))
        from rfl]
    rw [if_pos (le_of_eq h'.symm), h'.symm, clampI_one]
    show q.1.1.1 (1 : I) ∈ D
    rw [show q.1.1.1 (1 : I) = ((dOf D q : ↥D) : X) from coe_dOf D q]
    exact (dOf D q).2

/-- The endpoint at time `1` of the combined formula lands in `D`. -/
theorem homARaw_at_one_mem (D : Set X) (s : C(↥D × I, X)) (h1 : ∀ d, s (d, 1) = (d : X))
    (q : evalOnePreimage (x₀ := x₀) D) (r : I) :
    homARaw (x₀ := x₀) D s ((r, q), (1 : I)) ∈ D := by
  rw [show homARaw (x₀ := x₀) D s ((r, q), (1 : I)) =
      (if (2 : ℝ) * ((r : I) : ℝ) ≤ 1 then
        A1Raw (x₀ := x₀) D s (clampI (2 * ((r : I) : ℝ))) q (1 : I)
       else A1Raw (x₀ := x₀) D s 1 q
        (clampI ((7 : ℝ) / 4 * (((1 : I)) : ℝ)
          - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((1 : I)) : ℝ)))) from rfl]
  by_cases hr : (2 : ℝ) * ((r : I) : ℝ) ≤ 1
  · rw [if_pos hr]
    exact A1Raw_one_mem (x₀ := x₀) D s h1 _ q
  · rw [if_neg hr]
    have hcoef : (7 : ℝ) / 4 * (((1 : I)) : ℝ)
        - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((1 : I)) : ℝ)
        = 7 / 4 - 3 / 2 * ((r : I) : ℝ) := by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring
    rw [hcoef]
    have hr' : 1 < (2 : ℝ) * ((r : I) : ℝ) := not_le.mp hr
    have h4 : 1 ≤ (4 : ℝ) * (((clampI (7 / 4 - 3 / 2 * ((r : I) : ℝ))) : I) : ℝ) := by
      rw [coe_clampI_of_mem (by constructor <;> [linarith [r.2.2]; linarith [hr']])]
      linarith [r.2.2]
    exact A1Raw_one_mem_of_le (x₀ := x₀) D s h1 q _ h4

/-- **The map of the first homotopy**, packaged as a continuous map `I × p⁻¹D → p⁻¹D`. -/
def homACM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    C(I × evalOnePreimage (x₀ := x₀) D, evalOnePreimage (x₀ := x₀) D) where
  toFun w := ⟨⟨ContinuousMap.mk (fun t => homARaw (x₀ := x₀) D s ((w.1, w.2), t))
        ((continuous_homARaw D s h1).comp
          (continuous_const.prodMk (continuous_id : Continuous fun t : I => t))),
      homARaw_at_zero (x₀ := x₀) D s w.2 w.1⟩,
    homARaw_at_one_mem (x₀ := x₀) D s h1 w.2 w.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (ContinuousMap.curry (⟨homARaw (x₀ := x₀) D s,
      continuous_homARaw D s h1⟩ :
      C((I × evalOnePreimage (x₀ := x₀) D) × I, X))).continuous

/-- The composite path `sectCM (trivCM q)` evaluated at time `t` is the nested concatenation
`(γ * rev σ_d) * σ_d` at time `t`. -/
theorem sectCM_trivCM_apply (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (q : evalOnePreimage (x₀ := x₀) D) (t : I) :
    ((sectCM D s h0 h1 ((trivCM D s h0 h1) q))).1.1 t =
      catFun (catCM q.1.1 (sigRev D s (dOf D q)) (by
          show q.1.1 1 = sigRev D s (dOf D q) 0
          rw [sigRev_zero, h1, coe_dOf]))
        (sigFwd D s (dOf D q)) (by
          show (catCM q.1.1 (sigRev D s (dOf D q)) _) 1 = sigFwd D s (dOf D q) 0
          rw [catCM_one, sigRev_one]
          rfl) t := rfl

/-- The `r = 0` endpoint of the first homotopy is the composite `sectCM ∘ trivCM`. -/
theorem homACM_zero_apply (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (q : evalOnePreimage (x₀ := x₀) D) :
    homACM D s h0 h1 ((0 : I), q) = (sectCM D s h0 h1).comp (trivCM D s h0 h1) q := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine ContinuousMap.ext (fun t => ?_)
  rw [show ((sectCM D s h0 h1).comp (trivCM D s h0 h1)) q
      = (sectCM D s h0 h1) ((trivCM D s h0 h1) q) from rfl]
  rw [show (homACM D s h0 h1 ((0 : I), q)).1.1 t
      = homARaw (x₀ := x₀) D s (((0 : I), q), t) from rfl, homARaw_zero D s q t,
    sectCM_trivCM_apply D s h0 h1 q t]
  exact (catFun_triv_sect D s h1 q t).symm

/-- The `r = 1` endpoint of the first homotopy is the identity. -/
theorem homACM_one_apply (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (q : evalOnePreimage (x₀ := x₀) D) :
    homACM D s h0 h1 ((1 : I), q) = q := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine ContinuousMap.ext (fun t => ?_)
  rw [show (homACM D s h0 h1 ((1 : I), q)).1.1 t
      = homARaw (x₀ := x₀) D s (((1 : I), q), t) from rfl, homARaw_one D s q t]
  show (q.1.1.1 (clampI (t : ℝ))) = (q.1.1.1 t)
  rw [clampI_coe_I]

/-- **The first homotopy**: the composite `sectCM ∘ trivCM` is homotopic to the identity on
`p⁻¹D`. -/
def homSectTriv (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    ContinuousMap.Homotopy ((sectCM D s h0 h1).comp (trivCM D s h0 h1))
      (ContinuousMap.id (evalOnePreimage (x₀ := x₀) D)) :=
  ContinuousMap.Homotopy.mk (homACM D s h0 h1)
    (fun q => homACM_zero_apply D s h0 h1 q)
    (fun q => homACM_one_apply D s h0 h1 q)

/-- The "fold" argument of the second homotopy: at time `t`, the loop `σ_d * rev σ_d` is traversed
from its basepoint `x₀`, with `χ t = 4t - 1` on the first half and `2 - 2t` on the second. -/
def chiFun (t : I) : ℝ :=
  if (2 : ℝ) * (t : ℝ) ≤ 1 then 4 * (t : ℝ) - 1 else 2 - 2 * (t : ℝ)

theorem chiFun_eq (t : I) :
    chiFun t = (if (2 : ℝ) * (t : ℝ) ≤ 1 then 4 * (t : ℝ) - 1 else 2 - 2 * (t : ℝ)) := rfl

theorem continuous_chiFun : Continuous chiFun := by
  rw [show chiFun = fun t : I =>
      (if (2 : ℝ) * (t : ℝ) ≤ 1 then 4 * (t : ℝ) - 1 else 2 - 2 * (t : ℝ)) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro t ht
    have h4 : (4 : ℝ) * (t : ℝ) = 2 * ((2 : ℝ) * (t : ℝ)) := by ring
    rw [h4, ht]; norm_num

/-- The stage-one formula of the second homotopy on `↥D × Ω`: the `δ`-part fills the first quarter
and the loop `σ_d * rev σ_d` is squeezed towards the basepoint `x₀` by the factor `1 - u`. -/
def B1Raw (D : Set X) (s : C(↥D × I, X)) (u : I) (w : ↥D × Path x₀ x₀) (t : I) : X :=
  if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
  else s (w.1, clampI ((1 - (u : ℝ)) * chiFun t))

theorem continuous_B1Raw (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀) :
    Continuous fun z : (I × (↥D × Path x₀ x₀)) × I =>
      B1Raw (x₀ := x₀) D s z.1.1 z.1.2 z.2 := by
  rw [show (fun z : (I × (↥D × Path x₀ x₀)) × I =>
      B1Raw (x₀ := x₀) D s z.1.1 z.1.2 z.2) = fun z =>
      (if (4 : ℝ) * ((z.2 : I) : ℝ) ≤ 1 then
        z.1.2.2.toContinuousMap (clampI (4 * ((z.2 : I) : ℝ)))
       else s (z.1.2.1, clampI ((1 - ((z.1.1 : I) : ℝ)) * chiFun z.2))) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hδ : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => z.1.2.2.toContinuousMap := by
      fun_prop
    exact continuous_eval.comp (hδ.prodMk (continuous_clampI.comp (by fun_prop)))
  · have hχ : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => chiFun z.2 :=
      continuous_chiFun.comp continuous_snd
    have hu : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => ((z.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hd : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I =>
        (z.1.2.1, clampI ((1 - ((z.1.1 : I) : ℝ)) * chiFun z.2)) :=
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_clampI.comp ((continuous_const.sub hu).mul hχ)))
    exact s.continuous.comp hd
  · fun_prop
  · fun_prop
  · intro z hz
    have h2 : (4 : ℝ) * ((z.2 : I) : ℝ) = 1 := hz
    have hc : (((clampI (4 * ((z.2 : I) : ℝ))) : I) : ℝ) = 4 * ((z.2 : I) : ℝ) :=
      coe_clampI_of_mem (by constructor <;> [linarith [z.2.1]; linarith [h2]])
    have hz2 : ((z.2 : I) : ℝ) = 1 / 4 := by linarith
    have hχ : chiFun z.2 = 0 := by
      rw [chiFun_eq, if_pos (by rw [hz2]; norm_num)]
      rw [hz2]; norm_num
    rw [h2, clampI_one, hχ, mul_zero, clampI_zero, h0]
    exact z.1.2.2.target'

/-- The combined two-stage homotopy formula for `trivCM ∘ sectCM`. -/
def homBRaw (D : Set X) (s : C(↥D × I, X))
    (z : (I × (↥D × Path x₀ x₀)) × I) : X :=
  if (2 : ℝ) * ((z.1.1 : I) : ℝ) ≤ 1 then
    B1Raw (x₀ := x₀) D s (clampI (2 * ((z.1.1 : I) : ℝ))) z.1.2 z.2
  else
    B1Raw (x₀ := x₀) D s 1 z.1.2
      (clampI ((7 : ℝ) / 4 * ((z.2 : I) : ℝ)
        - (3 : ℝ) / 2 * ((z.1.1 : I) : ℝ) * ((z.2 : I) : ℝ)))

theorem continuous_homBRaw (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀) :
    Continuous (homBRaw (x₀ := x₀) D s) := by
  rw [show homBRaw (x₀ := x₀) D s = fun z : (I × (↥D × Path x₀ x₀)) × I =>
      (if (2 : ℝ) * ((z.1.1 : I) : ℝ) ≤ 1 then
        B1Raw (x₀ := x₀) D s (clampI (2 * ((z.1.1 : I) : ℝ))) z.1.2 z.2
       else B1Raw (x₀ := x₀) D s 1 z.1.2
        (clampI ((7 : ℝ) / 4 * ((z.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((z.1.1 : I) : ℝ) * ((z.2 : I) : ℝ)))) from rfl]
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hu : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => ((z.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hm : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I =>
        ((clampI (2 * ((z.1.1 : I) : ℝ)), z.1.2), z.2) :=
      ((continuous_clampI.comp
          ((continuous_const (y := (2 : ℝ))).mul hu)).prodMk
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd
    exact (continuous_B1Raw D s h0).comp hm
  · have hu : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => ((z.1.1 : I) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hv : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I => ((z.2 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    have hcoef : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I =>
        ((7 : ℝ) / 4 * ((z.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((z.1.1 : I) : ℝ) * ((z.2 : I) : ℝ)) :=
      ((continuous_const (y := (7 : ℝ) / 4)).mul hv).sub
        (((continuous_const (y := (3 : ℝ) / 2)).mul hu).mul hv)
    have hm : Continuous fun z : (I × (↥D × Path x₀ x₀)) × I =>
        (((1 : I), z.1.2), clampI ((7 : ℝ) / 4 * ((z.2 : I) : ℝ)
          - (3 : ℝ) / 2 * ((z.1.1 : I) : ℝ) * ((z.2 : I) : ℝ))) :=
      (((continuous_const (y := (1 : I))).prodMk
        (continuous_snd.comp continuous_fst)).prodMk (continuous_clampI.comp hcoef))
    exact (continuous_B1Raw D s h0).comp hm
  · fun_prop
  · fun_prop
  · intro z hz
    have hz2 : ((z.1.1 : I) : ℝ) = 1 / 2 := by linarith
    have hcoef : (7 : ℝ) / 4 * ((z.2 : I) : ℝ)
        - (3 : ℝ) / 2 * ((z.1.1 : I) : ℝ) * ((z.2 : I) : ℝ) = ((z.2 : I) : ℝ) := by
      rw [hz2]; ring
    rw [hz, clampI_one, hcoef, clampI_coe_I]

/-! ## The pointwise lemmas of the second homotopy -/

/-- `clampI` of a real number at least `1` is `1`. -/
theorem clampI_of_one_le {r : ℝ} (hr : 1 ≤ r) : clampI r = (1 : I) := by
  apply Subtype.ext
  show ((Set.projIcc (0 : ℝ) 1 zero_le_one r : I) : ℝ) = ((1 : I) : ℝ)
  rw [Set.coe_projIcc, min_eq_left hr, max_eq_right zero_le_one]
  rfl

/-- The `t = 0` endpoint of the second stage-one formula is the base point. -/
theorem B1Raw_zero (D : Set X) (s : C(↥D × I, X)) (u : I) (w : ↥D × Path x₀ x₀) :
    B1Raw (x₀ := x₀) D s u w 0 = x₀ := by
  rw [show B1Raw (x₀ := x₀) D s u w 0 =
      (if (4 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (((0 : I)) : ℝ)))
       else s (w.1, clampI ((1 - (u : ℝ)) * chiFun 0))) from rfl]
  rw [if_pos (by norm_num), show (4 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]
  exact w.2.source'

/-- The `t = 1` endpoint of the second stage-one formula is the base point (paused at the base
point). -/
theorem B1Raw_one (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀) (u : I)
    (w : ↥D × Path x₀ x₀) : B1Raw (x₀ := x₀) D s u w 1 = x₀ := by
  rw [show B1Raw (x₀ := x₀) D s u w 1 =
      (if (4 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (((1 : I)) : ℝ)))
       else s (w.1, clampI ((1 - (u : ℝ)) * chiFun 1))) from rfl]
  rw [if_neg (by norm_num)]
  have hc : chiFun 1 = 0 := by
    rw [chiFun_eq, if_neg (by norm_num)]
    norm_num
  rw [hc, mul_zero, clampI_zero, h0]

/-- First branch of the identification of the composite `trivCM ∘ sectCM` with the second
stage-one formula at parameter `0`. -/
theorem cat3Fun_eq_B1Raw_low (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (t : I)
    (h4 : (4 : ℝ) * (t : ℝ) ≤ 1) :
    cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t
      = B1Raw (x₀ := x₀) D s 0 w t := by
  rw [show cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigFwd D s w.1) (clampI (4 * (t : ℝ) - 1))
       else (sigRev D s w.1) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [show B1Raw (x₀ := x₀) D s 0 w t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else s (w.1, clampI ((1 - (((0 : I)) : ℝ)) * chiFun t))) from rfl]
  rw [if_pos h4, if_pos h4]

/-- Second branch (`1/4 ≤ t ≤ 1/2`) of the identification of the composite `trivCM ∘ sectCM` with
the second stage-one formula at parameter `0`. -/
theorem cat3Fun_eq_B1Raw_mid (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (t : I)
    (h4 : ¬ ((4 : ℝ) * (t : ℝ) ≤ 1)) (h2t : (2 : ℝ) * (t : ℝ) ≤ 1) :
    cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t
      = B1Raw (x₀ := x₀) D s 0 w t := by
  rw [show cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigFwd D s w.1) (clampI (4 * (t : ℝ) - 1))
       else (sigRev D s w.1) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [show B1Raw (x₀ := x₀) D s 0 w t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else s (w.1, clampI ((1 - (((0 : I)) : ℝ)) * chiFun t))) from rfl]
  rw [if_neg h4, if_pos h2t, if_neg h4]
  have hc : chiFun t = 4 * (t : ℝ) - 1 := by rw [chiFun_eq, if_pos h2t]
  show s (w.1, clampI (4 * (t : ℝ) - 1))
    = s (w.1, clampI ((1 - (((0 : I)) : ℝ)) * chiFun t))
  rw [hc, show (1 : ℝ) - (((0 : I)) : ℝ) = 1 by norm_num, one_mul]

/-- Third branch (`t ≥ 1/2`) of the identification of the composite `trivCM ∘ sectCM` with the
second stage-one formula at parameter `0`. -/
theorem cat3Fun_eq_B1Raw_high (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (t : I)
    (h2t : ¬ ((2 : ℝ) * (t : ℝ) ≤ 1)) :
    cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t
      = B1Raw (x₀ := x₀) D s 0 w t := by
  have h4 : ¬ ((4 : ℝ) * (t : ℝ) ≤ 1) := by
    intro h; exact h2t (by linarith)
  rw [show cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else if (2 : ℝ) * (t : ℝ) ≤ 1 then (sigFwd D s w.1) (clampI (4 * (t : ℝ) - 1))
       else (sigRev D s w.1) (clampI (2 * (t : ℝ) - 1))) from rfl]
  rw [show B1Raw (x₀ := x₀) D s 0 w t =
      (if (4 : ℝ) * (t : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (t : ℝ)))
       else s (w.1, clampI ((1 - (((0 : I)) : ℝ)) * chiFun t))) from rfl]
  rw [if_neg h4, if_neg h2t, if_neg h4]
  have hc : chiFun t = 2 - 2 * (t : ℝ) := by rw [chiFun_eq, if_neg h2t]
  have hcm : (((clampI (2 * (t : ℝ) - 1)) : I) : ℝ) = 2 * (t : ℝ) - 1 :=
    coe_clampI_of_mem (by constructor <;> [linarith [t.2.1]; linarith [t.2.2]])
  show s (w.1, clampI (1 - (((clampI (2 * (t : ℝ) - 1)) : I) : ℝ)))
    = s (w.1, clampI ((1 - (((0 : I)) : ℝ)) * chiFun t))
  rw [hc, show (1 : ℝ) - (((0 : I)) : ℝ) = 1 by norm_num, one_mul, hcm]
  rw [show (1 : ℝ) - (2 * (t : ℝ) - 1) = 2 - 2 * (t : ℝ) by ring]

/-- The composite `trivCM ∘ sectCM` at time `t` is the second stage-one formula at parameter `0`. -/
theorem catFun_triv_sect_B (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (w : ↥D × Path x₀ x₀) (t : I) :
    cat3Fun w.2.toContinuousMap (sigFwd D s w.1) (sigRev D s w.1) t
      = B1Raw (x₀ := x₀) D s 0 w t := by
  by_cases h4 : (4 : ℝ) * (t : ℝ) ≤ 1
  · exact cat3Fun_eq_B1Raw_low D s w t h4
  · by_cases h2t : (2 : ℝ) * (t : ℝ) ≤ 1
    · exact cat3Fun_eq_B1Raw_mid D s w t h4 h2t
    · exact cat3Fun_eq_B1Raw_high D s w t h2t

/-- At homotopy parameter `0`, the combined formula of the second homotopy is the stage-one
formula at parameter `0`. -/
theorem homBRaw_zero (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (t : I) :
    homBRaw (x₀ := x₀) D s (((0 : I), w), t) = B1Raw (x₀ := x₀) D s 0 w t := by
  rw [show homBRaw (x₀ := x₀) D s (((0 : I), w), t) =
      (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then
        B1Raw (x₀ := x₀) D s (clampI (2 * (((0 : I)) : ℝ))) w t
       else B1Raw (x₀ := x₀) D s 1 w
        (clampI ((7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((0 : I)) : ℝ) * (t : ℝ))))
      from rfl]
  rw [if_pos (by norm_num), show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]

/-- At homotopy parameter `1`, the combined formula of the second homotopy is the path itself (the
"pause" has stretched the `δ`-quarter over the whole interval). -/
theorem homBRaw_one (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (t : I) :
    homBRaw (x₀ := x₀) D s (((1 : I), w), t) = w.2.toContinuousMap (clampI (t : ℝ)) := by
  rw [show homBRaw (x₀ := x₀) D s (((1 : I), w), t) =
      (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then
        B1Raw (x₀ := x₀) D s (clampI (2 * (((1 : I)) : ℝ))) w t
       else B1Raw (x₀ := x₀) D s 1 w
        (clampI ((7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((1 : I)) : ℝ) * (t : ℝ))))
      from rfl]
  rw [if_neg (by norm_num)]
  rw [show (7 : ℝ) / 4 * (t : ℝ) - (3 : ℝ) / 2 * (((1 : I)) : ℝ) * (t : ℝ) = (t : ℝ) / 4 by
    rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring]
  rw [show B1Raw (x₀ := x₀) D s 1 w (clampI ((t : ℝ) / 4)) =
      (if (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) ≤ 1 then
        w.2.toContinuousMap (clampI (4 * (((clampI ((t : ℝ) / 4)) : I) : ℝ)))
       else s (w.1, clampI ((1 - (((1 : I)) : ℝ)) * chiFun (clampI ((t : ℝ) / 4))))) from rfl]
  have h4 : (4 : ℝ) * (((clampI ((t : ℝ) / 4)) : I) : ℝ) = (t : ℝ) := by
    rw [coe_clampI_of_mem (by constructor <;> [linarith [t.2.1]; linarith [t.2.2]])]
    ring
  rw [if_pos (by rw [h4]; exact t.2.2), h4, clampI_coe_I]

/-- At time `1` and stage parameter `1`, the second stage-one formula is the base point. -/
theorem B1Raw_one_of_quarter (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (w : ↥D × Path x₀ x₀) (τ : I) (h : (1 : ℝ) ≤ 4 * (τ : ℝ)) :
    B1Raw (x₀ := x₀) D s 1 w τ = x₀ := by
  rw [show B1Raw (x₀ := x₀) D s 1 w τ =
      (if (4 : ℝ) * (τ : ℝ) ≤ 1 then w.2.toContinuousMap (clampI (4 * (τ : ℝ)))
       else s (w.1, clampI ((1 - (((1 : I)) : ℝ)) * chiFun τ))) from rfl]
  by_cases h4 : (4 : ℝ) * (τ : ℝ) ≤ 1
  · rw [if_pos h4]
    have hτ : (τ : ℝ) = 1 / 4 := by linarith
    rw [show (4 : ℝ) * (τ : ℝ) = 1 by rw [hτ]; norm_num, clampI_one]
    exact w.2.target'
  · rw [if_neg h4]
    rw [show (1 : ℝ) - (((1 : I)) : ℝ) = 0 by norm_num, zero_mul, clampI_zero, h0]

/-- The base point of the parameter space attached to a point of the preimage of `sectCM`. -/
theorem dOf_sectCM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (w : ↥D × Path x₀ x₀) :
    dOf D (sectCM D s h0 h1 w) = w.1 := by
  apply Subtype.ext
  show ((sectCM D s h0 h1 w).1.1) 1 = (w.1 : X)
  exact sectPathCM_one D s h0 h1 w.1 w.2

/-- The composite `trivCM (sectCM w)` at time `t`, with the base point displayed as
`dOf (sectCM w)`. -/
theorem trivCM_sectCM_apply_dOf (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (w : ↥D × Path x₀ x₀) (t : I) :
    (trivCM D s h0 h1 (sectCM D s h0 h1 w)).2 t =
      catFun (catCM w.2.toContinuousMap (sigFwd D s w.1) (by
          show w.2.toContinuousMap 1 = (sigFwd D s w.1) 0
          rw [sigFwd_zero, h0]; exact w.2.target'))
        (sigRev D s (dOf D (sectCM D s h0 h1 w))) (by
          show (sectCM D s h0 h1 w).1.1 1 = sigRev D s (dOf D (sectCM D s h0 h1 w)) 0
          rw [sigRev_zero, h1, coe_dOf]) t := rfl

/-- A continuous map into a path space, built from a continuous map into `C(I, X)` and the two
endpoint conditions. -/
theorem continuous_path_mk {Y : Type} [TopologicalSpace Y] {f : Y → C(I, X)}
    (hf : Continuous f) {x : X} (h0 : ∀ y, f y 0 = x) (h1 : ∀ y, f y 1 = x) :
    Continuous fun y => (⟨f y, h0 y, h1 y⟩ : Path x x) :=
  (continuous_induced_rng (f := fun p : Path x x => p.toContinuousMap)).mpr hf

/-- The time-`0` endpoint of the combined second formula is the base point. -/
theorem homBRaw_at_time_zero (D : Set X) (s : C(↥D × I, X)) (w : ↥D × Path x₀ x₀) (r : I) :
    homBRaw (x₀ := x₀) D s ((r, w), (0 : I)) = x₀ := by
  rw [show homBRaw (x₀ := x₀) D s ((r, w), (0 : I)) =
      (if (2 : ℝ) * ((r : I) : ℝ) ≤ 1 then
        B1Raw (x₀ := x₀) D s (clampI (2 * ((r : I) : ℝ))) w (0 : I)
       else B1Raw (x₀ := x₀) D s 1 w
        (clampI ((7 : ℝ) / 4 * (((0 : I)) : ℝ)
          - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((0 : I)) : ℝ)))) from rfl]
  by_cases hr : (2 : ℝ) * ((r : I) : ℝ) ≤ 1
  · rw [if_pos hr]; exact B1Raw_zero D s _ w
  · rw [if_neg hr]
    rw [show (7 : ℝ) / 4 * (((0 : I)) : ℝ)
        - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]
    exact B1Raw_zero D s _ w

/-- The time-`1` endpoint of the combined second formula is the base point. -/
theorem homBRaw_at_time_one (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (w : ↥D × Path x₀ x₀) (r : I) :
    homBRaw (x₀ := x₀) D s ((r, w), (1 : I)) = x₀ := by
  rw [show homBRaw (x₀ := x₀) D s ((r, w), (1 : I)) =
      (if (2 : ℝ) * ((r : I) : ℝ) ≤ 1 then
        B1Raw (x₀ := x₀) D s (clampI (2 * ((r : I) : ℝ))) w (1 : I)
       else B1Raw (x₀ := x₀) D s 1 w
        (clampI ((7 : ℝ) / 4 * (((1 : I)) : ℝ)
          - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((1 : I)) : ℝ)))) from rfl]
  by_cases hr : (2 : ℝ) * ((r : I) : ℝ) ≤ 1
  · rw [if_pos hr]; exact B1Raw_one D s h0 _ w
  · rw [if_neg hr]
    rw [show (7 : ℝ) / 4 * (((1 : I)) : ℝ)
        - (3 : ℝ) / 2 * ((r : I) : ℝ) * (((1 : I)) : ℝ) = 7 / 4 - 3 / 2 * ((r : I) : ℝ) by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring]
    refine B1Raw_one_of_quarter D s h0 w _ ?_
    rcases lt_or_ge (7 / 4 - 3 / 2 * ((r : I) : ℝ)) 1 with hx | hx
    · rw [coe_clampI_of_mem (by constructor <;> [linarith [r.2.2]; exact le_of_lt hx])]
      linarith [r.2.2]
    · rw [clampI_of_one_le hx]; norm_num

/-- **The map of the second homotopy**, packaged as a continuous map
`I × (↥D × Ω) → ↥D × Ω`. -/
def homBACM (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    C(I × (↥D × Path x₀ x₀), ↥D × Path x₀ x₀) where
  toFun z := (z.2.1, ⟨ContinuousMap.mk (fun t => homBRaw (x₀ := x₀) D s ((z.1, z.2), t))
      ((continuous_homBRaw D s h0).comp
        (continuous_const.prodMk (continuous_id : Continuous fun t : I => t))),
      homBRaw_at_time_zero (x₀ := x₀) D s z.2 z.1,
      homBRaw_at_time_one (x₀ := x₀) D s h0 z.2 z.1⟩)
  continuous_toFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
    refine continuous_path_mk (f := fun z : I × (↥D × Path x₀ x₀) =>
      ⟨fun t => homBRaw (x₀ := x₀) D s ((z.1, z.2), t),
        (continuous_homBRaw D s h0).comp
          (continuous_const.prodMk (continuous_id : Continuous fun t : I => t))⟩) ?_ ?_ ?_
    · exact (ContinuousMap.curry (⟨fun p : (I × (↥D × Path x₀ x₀)) × I =>
        homBRaw (x₀ := x₀) D s p,
        continuous_homBRaw D s h0⟩ : C((I × (↥D × Path x₀ x₀)) × I, X))).continuous
    -- the two endpoint conditions are already the ones used in `toFun`

/-- The `r = 0` endpoint of the second homotopy is the composite `trivCM ∘ sectCM`. -/
theorem homBACM_zero_apply (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (w : ↥D × Path x₀ x₀) :
    homBACM D s h0 h1 ((0 : I), w) = (trivCM D s h0 h1).comp (sectCM D s h0 h1) w := by
  refine Prod.ext ?_ ?_
  · rw [show ((trivCM D s h0 h1).comp (sectCM D s h0 h1)) w
        = (trivCM D s h0 h1) ((sectCM D s h0 h1) w) from rfl]
    show w.1 = dOf D (sectCM D s h0 h1 w)
    exact (dOf_sectCM D s h0 h1 w).symm
  · refine Path.ext ?_
    funext t
    rw [show (homBACM D s h0 h1 ((0 : I), w)).2 t
        = homBRaw (x₀ := x₀) D s (((0 : I), w), t) from rfl]
    rw [homBRaw_zero D s w t]
    rw [show ((trivCM D s h0 h1).comp (sectCM D s h0 h1)) w
        = (trivCM D s h0 h1) ((sectCM D s h0 h1) w) from rfl]
    rw [trivCM_sectCM_apply_dOf D s h0 h1 w t]
    rw [catFun_catCM_apply w.2.toContinuousMap (sigFwd D s w.1)
      (sigRev D s (dOf D (sectCM D s h0 h1 w)))
      (by show w.2.toContinuousMap 1 = (sigFwd D s w.1) 0
          rw [sigFwd_zero, h0]; exact w.2.target')
      (by show (sigFwd D s w.1) 1 = (sigRev D s (dOf D (sectCM D s h0 h1 w))) 0
          rw [sigFwd_one, sigRev_zero, h1 (dOf D (sectCM D s h0 h1 w)), h1, coe_dOf,
            show (sectCM D s h0 h1 w).1.1 1 = (w.1 : X) from
              sectPathCM_one D s h0 h1 w.1 w.2]) t]
    rw [show (sigRev D s (dOf D (sectCM D s h0 h1 w))) = (sigRev D s w.1) from
      congrArg (sigRev D s) (dOf_sectCM D s h0 h1 w)]
    exact (catFun_triv_sect_B D s h0 h1 w t).symm

/-- The `r = 1` endpoint of the second homotopy is the identity. -/
theorem homBACM_one_apply (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) (w : ↥D × Path x₀ x₀) :
    homBACM D s h0 h1 ((1 : I), w) = w := by
  refine Prod.ext ?_ ?_
  · rfl
  · refine Path.ext ?_
    funext t
    rw [show (homBACM D s h0 h1 ((1 : I), w)).2 t
        = homBRaw (x₀ := x₀) D s (((1 : I), w), t) from rfl]
    rw [homBRaw_one D s w t]
    show w.2.toContinuousMap (clampI (t : ℝ)) = w.2.toContinuousMap t
    rw [clampI_coe_I]

/-- **The second homotopy**: the composite `trivCM ∘ sectCM` is homotopic to the identity on
`↥D × Ω`. -/
def homTrivSect (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    ContinuousMap.Homotopy ((trivCM D s h0 h1).comp (sectCM D s h0 h1))
      (ContinuousMap.id (↥D × Path x₀ x₀)) :=
  ContinuousMap.Homotopy.mk (homBACM D s h0 h1)
    (fun w => homBACM_zero_apply D s h0 h1 w)
    (fun w => homBACM_one_apply D s h0 h1 w)

/-- **The trivialisation is a homotopy equivalence.** -/
def trivHomotopyEquiv (D : Set X) (s : C(↥D × I, X)) (h0 : ∀ d, s (d, 0) = x₀)
    (h1 : ∀ d, s (d, 1) = (d : X)) :
    ContinuousMap.HomotopyEquiv (evalOnePreimage (x₀ := x₀) D) (↥D × Path x₀ x₀) where
  toFun := trivCM D s h0 h1
  invFun := sectCM D s h0 h1
  left_inv := ⟨homSectTriv D s h0 h1⟩
  right_inv := ⟨homTrivSect D s h0 h1⟩

end

end Work.StemsB
