import Mathlib
import Submission.Work.Serre.SweepDefs
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.DomeMap

/-!
# The "disk step" of the sweep

`Work.Serre.SweepRel m` is the three-face lifting property `Work.Serre.Sweep` for the cube `I^m`,
*with the lateral boundary* `∂I^m × I × I` also prescribed.  This is the shape in which the
relative homotopy lifting property `Work.StemsB.HasHLPRel` applies verbatim, and it is the form in
which the two induction steps of `Work.Serre.sweepCube_bdry` consume `Sweep`:

* `Sweep (I^m)` from `SweepRel m` and `Sweep ↥(∂I^m)` (`Sweep.of_sweepRel`),
* `Sweep ↥(∂I^{m+1})` by glueing the two closed pieces `F = {z | z (Fin.last m) = 0}` and the
  dome `D = ∂I^{m+1} ∖ int F`, each homeomorphic to `I^m` and each solved by `SweepRel m`.

The file also contains the two elementary gluing lemmas for continuous maps on a finite closed
cover, and the "insert last coordinate" bookkeeping (`snocPt`) for the identification
`I^{m+1} ≅ I^m × I`.
-/

open scoped Topology unitInterval
open ContinuousMap

/-!
## How the disk step is proved (notes for the reader)

**`sweepRelOfHasHLPRel`** (`HasHLPRel p (m+1) ⟹ SweepRel m p`).

Given `H : I^m × I_s × I_t → B` (i.e. `H (x, s, t)` with `x : Fin m → I`), the faces
`f₀ (x,t)`, `f₁ (x,s)`, `f₂ (x,s)`, the rim lift `Grim (x,s,t)` and all the compatibilities, apply
`HasHLPRel p (m+1)` to the cube `I^{m+1}` with coordinates `y = snocPt x t`
(so `initPt y = x` and `y (Fin.last m) = t`) and homotopy direction `s`:

* `Hrel y s := H (initPt y, s, y (Fin.last m))`;
* `frel y := f₀ (initPt y, y (Fin.last m))` (the bottom face `s = 0`);
* `grel (y,s)` is the *gluing* of
  `Grim (initPt y, s, y (Fin.last m))` (when `initPt y ∈ ∂I^m`),
  `f₁ (initPt y, s)` (when `y (Fin.last m) = 0`) and `f₂ (initPt y, s)` (when it is `1`).

The three closed pieces `{initPt y ∈ ∂I^m}`, `{y last = 0}`, `{y last = 1}` cover `CubeBdry (m+1)`;
the pairwise agreements on the overlaps are exactly `hGrim₁`, `hGrim₂` (for the two rim overlaps)
and `hGrim₀`, `c₀`, `c₁` (for the two `s = 0` overlaps).  Continuity of `grel` is proved by
`continuous_of_isClosed_cover` (closed set `{initPt y ∈ ∂I^m}` against its complement, which is the
union of the two closed sets `{y last = 0}`, `{y last = 1}`), each piece being handled by
`ContinuousOn.if` / `continuousOn_iff_continuous_domRestrict` after `rw [dif_pos ..]`.
The value on the rim is the `Grim` branch (test it *first*) — this is what gives the last conjunct
of the conclusion.  Finally `G x s t := Grel (snocPt x t, s)`.

**`sweepBdrySucc`** (`SweepRel m p` and `Sweep ↥∂I^m` give `Sweep ↥∂I^{m+1}`).

Write the data of `Sweep ↥(∂I^{m+1})` on `(z, s, t)` with `z : ↥(∂I^{m+1})`.  Split
`∂I^{m+1} = F ∪ D` with `F = {z | z (Fin.last m) = 0}` (≅ `I^m` via `x ↦ snocPt x 0`) and
`D = {z | IsDomePt z}` (≅ `I^m` via `e`, whose underlying map is `domePt`).  Both `F` and `D` are
closed, and `F ∩ D = {snocPt x 0 | x ∈ ∂I^m}`.  Apply `SweepRel m` on each piece (transporting
`H`, `f₀`, `f₁`, `f₂` and the rim lift `Grim` along the two homeomorphisms); the last conjunct of
`SweepRel` says that both pieces equal `Grim` on the rim, and `IsDomeHomeo` says `e y = snocPt y 0`
for `y ∈ ∂I^m`, so the two parametrisations of `F ∩ D` agree and the pieces match.  Glue with
`continuous_of_isClosed_cover`.  -/

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable {m : ℕ}

/-! ## Gluing continuous maps on a finite closed cover -/

/-- A map which agrees with two prescribed maps on two closed sets covering the space, and which
is continuous on each of them, is continuous. -/
theorem continuous_of_isClosed_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (h : s ∪ t = Set.univ)
    [DecidablePred (· ∈ s)]
    {f g : X → Y} (hfs : ContinuousOn f s) (hgt : ContinuousOn g t)
    (hfg : ∀ x ∈ s ∩ t, f x = g x) :
    Continuous (fun x => if x ∈ s then f x else g x) := by
  classical
  have hsub : sᶜ ⊆ t := fun x hx => by
    have hx' : x ∈ s ∪ t := by rw [h]; trivial
    rcases hx' with h' | h'
    · exact absurd h' hx
    · exact h'
  have hcl : closure sᶜ ⊆ t := ht.closure_subset_iff.mpr hsub
  refine continuous_if ?_ ?_ ?_
  · intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    have hx1 : x ∈ s := by simpa [hs.closure_eq] using hx.1
    exact hfg x ⟨hx1, hcl hx.2⟩
  · have : closure {x : X | x ∈ s} = s := by
      rw [show {x : X | x ∈ s} = s from rfl, hs.closure_eq]
    rwa [this]
  · exact hgt.mono hcl

/-- Continuity is local on a finite closed cover. -/
theorem continuousOn_of_isClosed_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) {f : X → Y}
    (hfs : ContinuousOn f s) (hft : ContinuousOn f t) : ContinuousOn f (s ∪ t) := by
  have hcov : (⋃ i : Fin 2, (if i = 0 then s else t)) = s ∪ t := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  rw [← hcov]
  refine (locallyFinite_of_finite (fun i : Fin 2 => (if i = 0 then s else t : Set X))).continuousOn_iUnion
    ?_ ?_
  · intro i; fin_cases i
    · simpa using hs
    · simpa using ht
  · intro i; fin_cases i
    · simpa using hfs
    · simpa using hft

/-! ## The `I^{m+1} ≅ I^m × I` bookkeeping -/

/-- The point of `I^{m+1}` whose first `m` coordinates are `x` and whose last coordinate is `b`. -/
def snocPt (x : Fin m → unitInterval) (b : unitInterval) : Fin (m + 1) → unitInterval :=
  Fin.insertNth (α := fun _ => unitInterval) (Fin.last m) b x

@[simp] theorem snocPt_last (x : Fin m → unitInterval) (b : unitInterval) :
    snocPt x b (Fin.last m) = b :=
  Fin.insertNth_apply_same _ _ _

@[simp] theorem snocPt_castSucc (x : Fin m → unitInterval) (b : unitInterval) (i : Fin m) :
    snocPt x b i.castSucc = x i := by
  rw [snocPt, ← Fin.succAbove_last, Fin.insertNth_apply_succAbove]

/-- The first `m` coordinates of a point of `I^{m+1}`. -/
def initPt (y : Fin (m + 1) → unitInterval) : Fin m → unitInterval := fun i => y i.castSucc

@[simp] theorem snocPt_initPt (x : Fin m → unitInterval) (b : unitInterval) :
    initPt (snocPt x b) = x := by
  funext i; simp [initPt]

theorem snocPt_self (y : Fin (m + 1) → unitInterval) :
    snocPt (initPt y) (y (Fin.last m)) = y := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp [initPt]

/-- Membership in the boundary of `I^{m+1}`, decomposed along the last coordinate. -/
theorem mem_boundary_succ_last_iff (y : Fin (m + 1) → unitInterval) :
    y ∈ Cube.boundary (Fin (m + 1)) ↔
      (y (Fin.last m) = 0 ∨ y (Fin.last m) = 1) ∨ initPt y ∈ Cube.boundary (Fin m) := by
  rw [Cube.boundary, Cube.boundary]
  constructor
  · rintro ⟨i, h⟩
    induction i using Fin.lastCases with
    | last => exact Or.inl h
    | cast j => exact Or.inr ⟨j, h⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨Fin.last m, h⟩
    · exact ⟨j.castSucc, hj⟩

theorem snocPt_mem_boundary_of_last {x : Fin m → unitInterval} (b : unitInterval)
    (hb : b = 0 ∨ b = 1) : snocPt x b ∈ Cube.boundary (Fin (m + 1)) := by
  refine (mem_boundary_succ_last_iff _).mpr (Or.inl ?_)
  rw [snocPt_last]; exact hb

theorem snocPt_mem_boundary_of_mem {x : Fin m → unitInterval} (hx : x ∈ Cube.boundary (Fin m))
    (b : unitInterval) : snocPt x b ∈ Cube.boundary (Fin (m + 1)) := by
  refine (mem_boundary_succ_last_iff _).mpr (Or.inr ?_)
  rwa [snocPt_initPt]

/-! ## The disk-step predicate -/

/-- **The disk step.**  `SweepRel m p` is `Sweep (I^m) p` with the additional data of a lift of
`H` on the lateral boundary `∂I^m × I × I` (agreeing with the three faces where they meet). -/
def SweepRel (m : ℕ) (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (H : C((Fin m → unitInterval) × unitInterval × unitInterval, B))
    (f₀ : C((Fin m → unitInterval) × unitInterval, E))
    (_h₀ : p.comp f₀ = H.comp ⟨fun x : (Fin m → unitInterval) × unitInterval =>
      (x.1, 0, x.2), by fun_prop⟩)
    (f₁ : C((Fin m → unitInterval) × unitInterval, E))
    (_h₁ : p.comp f₁ = H.comp ⟨fun x : (Fin m → unitInterval) × unitInterval =>
      (x.1, x.2, 0), by fun_prop⟩)
    (f₂ : C((Fin m → unitInterval) × unitInterval, E))
    (_h₂ : p.comp f₂ = H.comp ⟨fun x : (Fin m → unitInterval) × unitInterval =>
      (x.1, x.2, 1), by fun_prop⟩)
    (_c₀ : ∀ z : Fin m → unitInterval, f₀ (z, 0) = f₁ (z, 0))
    (_c₁ : ∀ z : Fin m → unitInterval, f₀ (z, 1) = f₂ (z, 0))
    (Grim : C(Work.StemsB.CubeBdry m × unitInterval × unitInterval, E))
    (_hGrim : p.comp Grim = H.comp ⟨fun x : Work.StemsB.CubeBdry m × unitInterval × unitInterval =>
      (x.1.1, x.2), by fun_prop⟩)
    (_hGrim₀ : ∀ (x : Work.StemsB.CubeBdry m) (b : unitInterval), Grim (x, 0, b) = f₀ (x.1, b))
    (_hGrim₁ : ∀ (x : Work.StemsB.CubeBdry m) (a : unitInterval), Grim (x, a, 0) = f₁ (x.1, a))
    (_hGrim₂ : ∀ (x : Work.StemsB.CubeBdry m) (a : unitInterval), Grim (x, a, 1) = f₂ (x.1, a)),
    ∃ G : C((Fin m → unitInterval) × unitInterval × unitInterval, E), p.comp G = H ∧
      (∀ z t, G (z, 0, t) = f₀ (z, t)) ∧
      (∀ z s, G (z, s, 0) = f₁ (z, s)) ∧
      (∀ z s, G (z, s, 1) = f₂ (z, s)) ∧
      (∀ (x : Work.StemsB.CubeBdry m) (u v : unitInterval), G (x.1, u, v) = Grim (x, u, v))

/-- The properties of the "dome" homeomorphism `I^m ≅ ∂I^{m+1} ∖ int {z | z (Fin.last m) = 0}`
used in the boundary step of the induction. -/
def IsDomeHomeo {m : ℕ} (hm : 1 ≤ m)
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) : Prop :=
  (∀ y : Fin m → unitInterval,
    ((e y : ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
      Fin (m + 1) → unitInterval) = Work.RatHurewicz.domePt hm y) ∧
  (∀ y : Fin m → unitInterval,
    y ∈ Cube.boundary (Fin m) ↔
      (((e y : ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
        Fin (m + 1) → unitInterval) (Fin.last m) = 0)) ∧
  (∀ y : Fin m → unitInterval, y ∈ Cube.boundary (Fin m) →
    ((e y : ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
      Fin (m + 1) → unitInterval) = snocPt y 0)

/-- The canonical map `↥∂I^m × I × I → I^m × I × I`. -/
def bdryRestr (m : ℕ) : C(Work.StemsB.CubeBdry m × unitInterval × unitInterval,
    (Fin m → unitInterval) × unitInterval × unitInterval) where
  toFun x := (x.1.1, x.2)
  continuous_toFun := by fun_prop

/-- The canonical map `↥∂I^m × I → I^m × I`. -/
def bdryRestr2 (m : ℕ) : C(Work.StemsB.CubeBdry m × unitInterval,
    (Fin m → unitInterval) × unitInterval) where
  toFun x := (x.1.1, x.2)
  continuous_toFun := by fun_prop

/-- The disk step plus the boundary sweep gives the sweep of the cube. -/
theorem Sweep.of_sweepRel {p : C(E, B)} {m : ℕ} (h : SweepRel m E B p)
    (hbdry : Sweep ↥(Cube.boundary (Fin m)) E B p) :
    Sweep (Fin m → unitInterval) E B p := by
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁
  obtain ⟨Grim, hGrim, hGrim₀, hGrim₁, hGrim₂⟩ :=
    hbdry (H.comp (bdryRestr m)) (f₀.comp (bdryRestr2 m))
      (by ext x; exact congrFun (congrArg DFunLike.coe h₀) (x.1.1, x.2))
      (f₁.comp (bdryRestr2 m))
      (by ext x; exact congrFun (congrArg DFunLike.coe h₁) (x.1.1, x.2))
      (f₂.comp (bdryRestr2 m))
      (by ext x; exact congrFun (congrArg DFunLike.coe h₂) (x.1.1, x.2))
      (fun z => c₀ z.1) (fun z => c₁ z.1)
  obtain ⟨G, hG, hG₀, hG₁, hG₂, _⟩ := h H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁ Grim hGrim hGrim₀ hGrim₁ hGrim₂
  exact ⟨G, hG, hG₀, hG₁, hG₂⟩

end

end Work.Serre
