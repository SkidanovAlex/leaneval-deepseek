import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.LoopShiftShifted
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.ConnectingMap

/-!
# The fibre of the projection of the homotopy fibre, and the pair sequence

For `i : C(A,X)` and `a₀ : A` the homotopy fibre `E = homotopyFibre i a₀` (`Work.RatHurewicz`)
is the space of pairs `(a, γ)` with `γ` a path in `X` from `i a₀` to `i a`.  Its first projection
`p = homotopyFibreFst i a₀ : E → A` is a Serre fibration
(`Work.RatHurewicz.isSerreFibration_homotopyFibreFst`), and the fibre `F = p ⁻¹' {a₀}` consists of
the pairs `(a₀, γ)` with `γ` a loop in `X` at `i a₀`; thus `F` is the loop space `ΩX` and
`π_{m+1}(F) ≅ π_{m+2}(X)` by the currying isomorphism `Work.StemsB.stepMulEquiv`.

This file fixes the vocabulary of that identification:

* `Work.RatHurewicz.fibrePsi`, `Work.RatHurewicz.fibrePhi` — the two inverse continuous maps
  between `F` and `Path (i a₀) (i a₀)` (the identity on the underlying path);
* `Work.RatHurewicz.pairShiftHom` — the composite
  `π_{m+2}(X) → π_{m+1}(ΩX) → π_{m+1}(F)`, a monoid homomorphism;
* `Work.RatHurewicz.fibreDMap` — the connecting map `π_{m+2}(A) → π_{m+1}(F)` of the fibration `p`;
* `Work.RatHurewicz.pairLift` — the *explicit* lift, in the fibre, of the cube of a based cube of
  `A`: for a based `(m+2)`-cube `f` of `A` and `(x,t) : I^{m+1} × I` it is the point
  `(f (t, x), s ↦ i (f (min s t, x)))` of `E`.

The two mathematical contents proved elsewhere (using this vocabulary) are
`Work.RatHurewicz.pairShiftHom_bijective` (`Submission/Work/RatHurewicz/PairShiftBijective.lean`)
and the identification of the connecting map with `i_*` after the loop shift,
`Work.RatHurewicz.fibreDMap_eq_pairShiftHom`
(`Submission/Work/RatHurewicz/PairLESCrux.lean`); the long exact sequence of the pair is assembled
from them in `Submission/Work/RatHurewicz/pair_les.lean`.

## How the two mathematical contents are used

The two identifications of this vocabulary that are needed are:

* **`pairShiftHom_bijective`** (`Submission/Work/RatHurewicz/PairShiftBijective.lean`):
  the composite `πmap (fibrePsi i a₀) m (Path.refl (i a₀)) ∘ stepMulEquiv m` is a bijection.
  Strategy: `fibrePhi i a₀` is both a left and a right inverse of `fibrePsi i a₀`
  (`fibrePhi_fibrePsi`, `fibrePsi_fibrePhi`), so by `πmap_comp_apply`, `πmap_id_apply`,
  `πmap_congr` and `πmap_homotopyGroupCast` the two induced maps on homotopy groups are mutually
  inverse (up to transports along base point equalities, e.g. `fibrePhi_fibreOfPt`), and
  `stepMulEquiv m` is a multiplicative equivalence.

* **`fibreDMap_eq_pairShiftHom`** (`Submission/Work/RatHurewicz/PairLESCrux.lean`): the connecting
  map of the fibration `homotopyFibreFst i a₀` equals `π_{m+2}(X) → π_{m+1}(F)` composed with
  `i_*`.  Strategy: both sides are monoid homomorphisms out of
  `HomotopyGroup (Fin (m+2)) A a₀`, so it suffices to check them on the class `⟦f⟧` of a based cube
  `f : Ω^(m+2) A a₀`.  There, `dFun_mk` (from `Work.StemsB.ConnectingMap`) identifies the left hand
  side with `⟦dGenLoop p e₀ hrel f⟧`, which is the top face of the canonical lift `dLift`; the
  explicit lift `pairLift i a₀ f` satisfies the same hypotheses of
  `Work.StemsB.liftUniqueness` (`pairLift_spec_lift`, `pairLift_spec_zero`, `pairLift_spec_bdry`),
  so its top face is homotopic to `dGenLoop p e₀ hrel f`.  On the other hand
  `pairShiftHom_comp_apply_mk` (with `πmap_apply_mk`) identifies the right hand side with the class
  of `genLoopMap (fibrePsi i a₀) (m+1) (Faux (m+1) (genLoopMap i (m+2) f))`, and
  `genLoopMap_fibrePsi_Faux_eq` says that this *is* the top face of `pairLift i a₀ f`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-! ## The fibre of `homotopyFibreFst` is the loop space -/

/-- The fibre `F = p ⁻¹' {p e₀}` of the projection `p = homotopyFibreFst i a₀` of the homotopy
fibre: the points `(a₀, γ)` of `E` with `γ` a loop in `X` at `i a₀`. -/
abbrev fibreOf (i : C(A, X)) (a₀ : A) : Type _ :=
  fibre (homotopyFibreFst i a₀) ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))

/-- **The loop space as a subspace of the fibre of the homotopy fibre projection**: a loop `γ` at
`i a₀` gives the point `(a₀, γ)` of `E`, which lies over `a₀`. -/
def fibrePsi (i : C(A, X)) (a₀ : A) : C(Path (i a₀) (i a₀), fibreOf i a₀) where
  toFun γ := ⟨⟨(a₀, ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩, rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    refine (continuous_const.prodMk ?_)
    exact Continuous.subtype_mk continuous_induced_dom _

/-- The base point of `fibreOf i a₀`: the point `(a₀, constant loop)` of the homotopy fibre.  It is
definitionally equal to `fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)` and is
spelled this way so that it is *syntactically* the base point of `πmap (fibrePsi i a₀)`. -/
abbrev fibreOfPt (i : C(A, X)) (a₀ : A) : fibreOf i a₀ :=
  fibrePsi i a₀ (Path.refl (i a₀))

/-- **The underlying loop of a point of `F`**, the inverse of `fibrePsi`. -/
def fibrePhi (i : C(A, X)) (a₀ : A) : C(fibreOf i a₀, Path (i a₀) (i a₀)) where
  toFun e :=
    { toContinuousMap := e.1.1.2.1
      source' := e.1.1.2.2
      target' := (e.1.2).trans (congrArg i e.2) }
  continuous_toFun := by
    refine (continuous_induced_rng (f := (Path.toContinuousMap : Path (i a₀) (i a₀) → C(I, X)))).2 ?_
    show Continuous (fun e : fibreOf i a₀ => ((e.1.1.2).1 : C(I, X)))
    fun_prop

/-- `fibrePhi` is a left inverse of `fibrePsi`. -/
theorem fibrePhi_fibrePsi (i : C(A, X)) (a₀ : A) (γ : Path (i a₀) (i a₀)) :
    fibrePhi i a₀ (fibrePsi i a₀ γ) = γ := by
  ext t
  rfl

/-- `fibrePhi` is a right inverse of `fibrePsi`. -/
theorem fibrePsi_fibrePhi (i : C(A, X)) (a₀ : A) (e : fibreOf i a₀) :
    fibrePsi i a₀ (fibrePhi i a₀ e) = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact e.2.symm
  · rfl

/-- `fibrePsi` sends the constant loop to the base point of `F`. -/
theorem fibrePsi_refl (i : C(A, X)) (a₀ : A) :
    fibrePsi i a₀ (Path.refl (i a₀)) = fibreOfPt i a₀ := rfl

/-- `fibrePhi` sends the base point of `F` to the constant loop. -/
theorem fibrePhi_fibreOfPt (i : C(A, X)) (a₀ : A) :
    fibrePhi i a₀ (fibreOfPt i a₀) = Path.refl (i a₀) := by
  rw [← fibrePsi_refl i a₀, fibrePhi_fibrePsi]

/-- The transport of homotopy groups along an equality of base points depends only on the
proposition. -/
theorem homotopyGroupCast_congr {Y : Type*} [TopologicalSpace Y] {y₀ y₁ : Y} (h h' : y₀ = y₁)
    (n : ℕ) : homotopyGroupCast h n = homotopyGroupCast h' n := by
  rw [Subsingleton.elim h h']

/-- **Naturality of `πmap` with respect to the transport of homotopy groups along an equality of
base points.** -/
theorem πmap_homotopyGroupCast {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (n : ℕ) {y₀ y₁ : Y} (h : y₀ = y₁)
    (a : HomotopyGroup (Fin (n + 1)) Y y₀) :
    πmap f n y₁ (homotopyGroupCast h n a)
      = homotopyGroupCast (congrArg f h) n (πmap f n y₀ a) := by
  subst h
  simp

/-! ## The connecting map of the fibration `homotopyFibreFst` -/

/-- The relative homotopy lifting property of the projection `homotopyFibreFst i a₀`, from
`Work.RatHurewicz.isSerreFibration_homotopyFibreFst`. -/
theorem fibreHrel (i : C(A, X)) (a₀ : A) : ∀ k, HasHLPRel (homotopyFibreFst i a₀) k :=
  fun k => exists_lift_rel (homotopyFibreFst i a₀)
    (isSerreFibration_homotopyFibreFst i a₀) k

/-- **The connecting map** `π_{m+2}(A) → π_{m+1}(F)` of the long exact homotopy sequence of the
fibration `homotopyFibreFst i a₀ : E → A`. -/
def fibreDMap (i : C(A, X)) (a₀ : A) (m : ℕ) :
    HomotopyGroup (Fin (m + 2)) A a₀ →*
      HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀) :=
  dMap (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) m

/-! ## The loop-space shift into the fibre -/

/-- **The curried map `π_{m+2}(X) →* π_{m+1}(F)`**: the loop-space shift
`π_{m+2}(X) ≃* π_{m+1}(ΩX)` (`Work.StemsB.stepMulEquiv`) composed with the isomorphism induced by
the identification of `ΩX` with the fibre `F` of the homotopy fibre projection. -/
def pairShiftHom (i : C(A, X)) (a₀ : A) (m : ℕ) :
    HomotopyGroup (Fin (m + 2)) X (i a₀) →*
      HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀) :=
  (πmap (fibrePsi i a₀) m (Path.refl (i a₀))).comp (stepMulEquiv m).toMonoidHom

/-- `pairShiftHom` on a representative: the curried cube. -/
theorem pairShiftHom_apply_mk (i : C(A, X)) (a₀ : A) (m : ℕ)
    (γ : GenLoop (Fin (m + 2)) X (i a₀)) :
    pairShiftHom i a₀ m ⟦γ⟧
      = ⟦genLoopMap (fibrePsi i a₀) (m + 1) (Faux (m + 1) γ)⟧ := by
  show πmap (fibrePsi i a₀) m (Path.refl (i a₀)) (stepEquivGroup (m + 1) ⟦γ⟧) = _
  rw [stepEquivGroup_mk, πmap_apply_mk]

/-- `pairShiftHom` on the image of `i_*`, on a representative of a based cube of `A`. -/
theorem pairShiftHom_comp_apply_mk (i : C(A, X)) (a₀ : A) (m : ℕ)
    (f : GenLoop (Fin (m + 2)) A a₀) :
    pairShiftHom i a₀ m (πmap i (m + 1) a₀ ⟦f⟧)
      = ⟦genLoopMap (fibrePsi i a₀) (m + 1) (Faux (m + 1) (genLoopMap i (m + 2) f))⟧ := by
  rw [πmap_apply_mk]
  exact pairShiftHom_apply_mk i a₀ m (genLoopMap i (m + 2) f)

/-! ## The explicit lift of the cube of a based cube of `A` -/

theorem min_zero_I (t : I) : min (0 : I) t = 0 := min_eq_left (by exact_mod_cast t.2.1)

theorem min_one_I (t : I) : min (1 : I) t = t := min_eq_right (by exact_mod_cast t.2.2)

theorem min_I_one (t : I) : min t (1 : I) = t := min_eq_left (by exact_mod_cast t.2.2)

theorem min_I_zero (t : I) : min t (0 : I) = 0 := min_eq_right (by exact_mod_cast t.2.1)

/-- Continuity of the uncurried explicit lift, componentwise. -/
theorem continuous_pairPath (i : C(A, X)) {a₀ : A} {m : ℕ}
    (f : GenLoop (Fin (m + 2)) A a₀) :
    Continuous
      (fun w : ((Fin (m + 1) → I) × I) × I => i (f (Fin.cons (min w.2 w.1.2) w.1.1))) := by
  fun_prop

/-- Continuity of the path component of the explicit lift at a fixed parameter. -/
theorem continuous_pairPath_fixed (i : C(A, X)) {a₀ : A} {m : ℕ}
    (f : GenLoop (Fin (m + 2)) A a₀) (q : (Fin (m + 1) → I) × I) :
    Continuous (fun s : I => i (f (Fin.cons (min s q.2) q.1))) := by
  fun_prop

/-- **The explicit lift in the homotopy fibre of the cube of a based cube of `A`.**  For a based
`(m+2)`-cube `f` of `A` and `q = (x,t) : I^{m+1} × I`, this is the point
`(f (t,x), s ↦ i (f (min s t, x)))` of `E = homotopyFibre i a₀`.  It is a lift of `cubeReindex f`
(`p ∘ pairLift f = cubeReindex f`) which is constantly `e₀` on the bottom face `t = 0` and on the
lateral boundary; its top face `t = 1` is the curried cube of `i ∘ f`. -/
def pairLiftFun (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀)
    (q : (Fin (m + 1) → I) × I) : homotopyFibre i a₀ :=
  ⟨(f (Fin.cons q.2 q.1),
    ⟨⟨fun s : I => i (f (Fin.cons (min s q.2) q.1)), continuous_pairPath_fixed i f q⟩,
      by
        show i (f (Fin.cons (min (0 : I) q.2) q.1)) = i a₀
        rw [min_zero_I]
        exact congrArg i (f.2 _ ⟨0, Or.inl rfl⟩)⟩),
    by
      show i (f (Fin.cons (min (1 : I) q.2) q.1)) = i (f (Fin.cons q.2 q.1))
      rw [min_one_I]⟩

/-- The explicit lift, as a continuous map. -/
def pairLift (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀) :
    C((Fin (m + 1) → I) × I, homotopyFibre i a₀) where
  toFun := pairLiftFun i a₀ f
  continuous_toFun := by
    have hcm : Continuous (fun q : (Fin (m + 1) → I) × I =>
        (⟨fun s : I => i (f (Fin.cons (min s q.2) q.1)),
          continuous_pairPath_fixed i f q⟩ : C(I, X))) :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_pairPath i f)
    have hpath : Continuous (fun q : (Fin (m + 1) → I) × I =>
        (⟨⟨fun s : I => i (f (Fin.cons (min s q.2) q.1)),
            continuous_pairPath_fixed i f q⟩,
          (by
            show i (f (Fin.cons (min (0 : I) q.2) q.1)) = i a₀
            rw [min_zero_I]
            exact congrArg i (f.2 _ ⟨0, Or.inl rfl⟩))⟩ : PathSpace X (i a₀))) :=
      Continuous.subtype_mk hcm _
    have hfst : Continuous (fun q : (Fin (m + 1) → I) × I => f (Fin.cons q.2 q.1)) :=
      (map_continuous f).comp (continuous_pi_iff.mpr (fun j => by
        cases j using Fin.cases with
        | zero => exact continuous_snd
        | succ k => exact (continuous_apply k).comp continuous_fst))
    have hpair : Continuous (fun q : (Fin (m + 1) → I) × I =>
        (f (Fin.cons q.2 q.1),
          (⟨⟨fun s : I => i (f (Fin.cons (min s q.2) q.1)),
              continuous_pairPath_fixed i f q⟩,
            (by
              show i (f (Fin.cons (min (0 : I) q.2) q.1)) = i a₀
              rw [min_zero_I]
              exact congrArg i (f.2 _ ⟨0, Or.inl rfl⟩))⟩ : PathSpace X (i a₀)))) :=
      hfst.prodMk hpath
    exact Continuous.subtype_mk hpair _

/-- The `A`-coordinate of the explicit lift is the cube of `f` itself. -/
@[simp]
theorem pairLift_coe_fst (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀)
    (q : (Fin (m + 1) → I) × I) :
    ((pairLift i a₀ f) q : homotopyFibre i a₀).1.1 = f (Fin.cons q.2 q.1) := rfl

/-- The underlying loop of the explicit lift, evaluated at `s`. -/
@[simp]
theorem pairLift_coe_snd (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀)
    (q : (Fin (m + 1) → I) × I) (s : I) :
    (((pairLift i a₀ f) q : homotopyFibre i a₀).1.2.1 : C(I, X)) s
      = i (f (Fin.cons (min s q.2) q.1)) := rfl

/-- The explicit lift is a lift of `cubeReindex f`. -/
theorem pairLift_spec_lift (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀) :
    (homotopyFibreFst i a₀).comp (pairLift i a₀ f) = cubeReindex (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀) f := by
  ext q
  rfl

/-- The explicit lift is constantly `e₀` on the bottom face. -/
theorem pairLift_spec_zero (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀)
    (x : Fin (m + 1) → I) :
    pairLift i a₀ f (x, 0) = homotopyFibreBasepoint i a₀ := by
  apply Subtype.ext
  apply Prod.ext
  · show f (Fin.cons (0 : I) x) = a₀
    exact f.2 _ ⟨0, Or.inl rfl⟩
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    show i (f (Fin.cons (min s (0 : I)) x)) = i a₀
    rw [min_I_zero]
    exact congrArg i (f.2 _ ⟨0, Or.inl rfl⟩)

/-- The explicit lift is constantly `e₀` on the lateral boundary. -/
theorem pairLift_spec_bdry (i : C(A, X)) (a₀ : A) {m : ℕ} (f : GenLoop (Fin (m + 2)) A a₀)
    (x : CubeBdry (m + 1)) (t : I) :
    pairLift i a₀ f (x.1, t) = homotopyFibreBasepoint i a₀ := by
  apply Subtype.ext
  apply Prod.ext
  · show f (Fin.cons t x.1) = a₀
    exact f.2 _ (cons_mem_boundary x.2)
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    show i (f (Fin.cons (min s t) x.1)) = i a₀
    exact congrArg i (f.2 _ (cons_mem_boundary x.2))

/-- **The top face of the explicit lift is the curried cube**: as a based `(m+1)`-cube of the
fibre `F`, the map `x ↦ pairLift f (x,1)` is the currying of the based `(m+2)`-cube `i ∘ f`. -/
theorem genLoopMap_fibrePsi_Faux_eq (i : C(A, X)) (a₀ : A) (m : ℕ)
    (f : GenLoop (Fin (m + 2)) A a₀) :
    genLoopMap (fibrePsi i a₀) (m + 1) (Faux (m + 1) (genLoopMap i (m + 2) f))
      = topFaceG (m + 1) (cubeReindex (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀) f)
          (cubeReindex_one _) (pairLift i a₀ f)
          (pairLift_spec_lift i a₀ f) (pairLift_spec_bdry i a₀ f) := by
  apply GenLoop.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · show a₀ = f (Fin.cons (1 : I) x)
    exact (f.2 _ ⟨0, Or.inr rfl⟩).symm
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    show (genLoopMap i (m + 2) f) (Fin.cons s x) = i (f (Fin.cons (min s (1 : I)) x))
    rw [min_I_one]
    rfl

end

end Work.RatHurewicz

