import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Defs
import Submission.Work.ThomBordism.Transversality.Sard.det_eq_zero_iff_not_surjective
import Submission.Work.ThomBordism.Transversality.Sard.volume_image_critical_det_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The stratification of the critical set (the road to rectangular Sard)

This file fixes the **vocabulary of the induction** that proves Sard's theorem in the rectangular
case `n ≥ m` (the case needed for transversality), together with the base case and the
measure-theoretic bookkeeping.

## The stratification

For `f : E → F` and `k ≥ 1` let

`Zk f k = {x | VanishToOrder f k x}`, where `VanishToOrder f k x` says that **all iterated
derivatives of `f` of orders `1, …, k` vanish at `x`** (`iteratedFDeriv ℝ j f x = 0` for
`1 ≤ j ≤ k`).  The sets are nested `Zk f 1 ⊇ Zk f 2 ⊇ …`, every point of `Zk f 1` has zero
derivative, and the critical set decomposes as

`{x | IsCriticalPoint f x} ⊆ ({x | IsCriticalPoint f x} \ Zk f 1) ∪ ⋃_{k} (Zk f (k+1) \ Zk f (k+2))
  ∪ Zk f (N+1)`

(`Zk_one_subset_decomp`), a *countable* union of the pieces on which the three parts of the
classical proof of Sard's theorem act:

* `{x | IsCriticalPoint f x} \ Zk f 1` — **the non-vanishing-derivative piece**: `f` is
  straightened, its slices are maps `ℝ^n → ℝ^m` and Sard in the rectangular case follows from the
  induction hypothesis for `(n, m)` (the Fubini/Tonelli step);
* `Zk f k \ Zk f (k+1)` — **the vanishing piece**: at such a point a partial derivative of order
  `k` has non-vanishing derivative, so `f` is very flat along the hypersurface `{σ = 0}` on which
  the piece lies, and Sard for the restriction to that hypersurface (source dimension `n`, target
  `m`) gives the induction step;
* `Zk f (K-1)` — **the flat piece**, handled by the Taylor estimate
  `Sard.volume_image_eq_zero_of_isFlat` (the technical heart, already proved).

## The induction predicate

`SardEuclidOn n m` is the statement of Sard's theorem for `C^∞` maps `ℝ^n → ℝ^m`, **localized on
an open set** (this is the form in which the induction steps consume each other); `SardEuclid n m`
is the global statement.  `sardEuclid_of_sardEuclidOn` deduces the global statement (the trivial
direction: localize at `univ`), and `SardEuclid` gives the input `SardRectangular` of the chapter.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set Function

namespace Work.ThomBordism.Transversality

noncomputable section

/-! ## The sets `Zk` -/

/-- `VanishToOrder f k x`: all iterated derivatives of `f` of orders `1, …, k` vanish at `x`. -/
def VanishToOrder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (k : ℕ) (x : E) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0

/-- The **stratum** `Zk f k`: the set of points at which all derivatives of `f` of orders
`1, …, k` vanish.  These are the sets of the standard stratification of the critical set
(`Zk f 1 ⊇ Zk f 2 ⊇ …`). -/
def Zk {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (k : ℕ) : Set E :=
  {x | VanishToOrder f k x}

theorem mem_Zk {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {k : ℕ} {x : E} :
    x ∈ Zk f k ↔ VanishToOrder f k x := Iff.rfl

theorem Zk_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) : Zk f 0 = univ := by
  ext x
  simp only [mem_Zk, VanishToOrder, Set.mem_univ, iff_true]
  intro j hj1 hj2
  omega

theorem vanishToOrder_mono {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {k k' : ℕ} {x : E}
    (h : k ≤ k') (hx : VanishToOrder f k' x) : VanishToOrder f k x :=
  fun j hj1 hj2 => hx j hj1 (le_trans hj2 h)

theorem Zk_antitone {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {k k' : ℕ} (h : k ≤ k') :
    Zk f k' ⊆ Zk f k :=
  fun _ hx => vanishToOrder_mono h hx

/-- `Zk f 1` is exactly the set of points with vanishing derivative. -/
theorem vanishToOrder_one_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} :
    VanishToOrder f 1 x ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro h
    ext v
    have h1 := h 1 le_rfl le_rfl
    have := congrArg (fun (L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) =>
      L (fun _ => v)) h1
    simpa [iteratedFDeriv_one_apply] using this
  · intro h j hj1 hj2
    have hj : j = 1 := by omega
    subst hj
    ext m
    rw [iteratedFDeriv_one_apply, h]
    simp

/-- `C^∞` (the smooth height) as an element of the height type `ℕ∞ω`.  This abbreviation exists so
that statements in this chapter can be written **without** `open scoped ContDiff` (writing
`ContDiff ℝ ⊤` would be *analytic*: in this Mathlib `⊤` means analytic and `C^∞` is
`((⊤ : ℕ∞) : ℕ∞ω)`). -/
abbrev smoothHeight : ℕ∞ω := ((⊤ : ℕ∞) : ℕ∞ω)

/-- `f` is `C^∞` (smooth) on the set `U`. -/
abbrev CInfOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (U : Set E) : Prop :=
  ContDiffOn ℝ smoothHeight f U

/-- `f` is `C^∞` (smooth). -/
abbrev CInf {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) : Prop :=
  ContDiff ℝ smoothHeight f

/-- `f` is `C^∞` (smooth) at the point `x`. -/
abbrev CInfAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : Prop :=
  ContDiffAt ℝ smoothHeight f x

/-! ## The induction predicate -/

/-- **Sard's theorem for `C^∞` maps `ℝ^n → ℝ^m`, global form.**  The image of the critical set has
measure zero.  This is the statement that gives `SardRectangular` (item 1 of the chapter). -/
def SardEuclid (n m : ℕ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
    CInf f → volume (f '' {x | IsCriticalPoint f x}) = 0

/-- **Sard's theorem for `C^∞` maps `ℝ^n → ℝ^m`, localized on an open set** `U`: the image of the
critical set of `f` *inside* `U` has measure zero.  This is the form in which the induction steps
of the proof consume each other (a step produces a null image on an open neighbourhood, and the
steps themselves are applied to maps that are only smooth on such a neighbourhood). -/
def SardEuclidOn (n m : ℕ) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (U : Set (EuclideanSpace ℝ (Fin n))),
    IsOpen U → CInfOn f U →
      volume (f '' ({x | IsCriticalPoint f x} ∩ U)) = 0

/-- The global statement is the local statement at `U = univ`. -/
theorem sardEuclid_of_sardEuclidOn {n m : ℕ} (h : SardEuclidOn n m) : SardEuclid n m := by
  intro f hf
  simpa [CInf] using h f univ isOpen_univ hf.contDiffOn

theorem SardEuclidOn.mono_set {n m : ℕ} (h : SardEuclidOn n m)
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hVU : V ⊆ U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (hf : CInfOn f U) :
    volume (f '' ({x | IsCriticalPoint f x} ∩ V)) = 0 :=
  h f V hV (hf.mono hVU)

/-! ## The equidimensional base case, localized -/

/-- **Sard's theorem, equidimensional case, localized on an arbitrary set**: for `f : ℝⁿ → ℝⁿ`
differentiable on a set `s` and with singular derivative there, the image `f '' s` is null.

This is Mathlib's `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` combined with
`det_eq_zero_iff_not_surjective`.  It is the base case `n = m` of the induction. -/
theorem volume_image_eq_zero_of_isCriticalPoint_on {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x)
    (hs' : ∀ x ∈ s, IsCriticalPoint f x) :
    volume (f '' s) = 0 := by
  refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) hs ?_
  intro x hx
  exact (Sard.det_eq_zero_iff_not_surjective (fderiv ℝ f x)).mpr (hs' x hx)

/-- **The base case `n = m` of the induction**, in the localized form: for a `C^∞` map
`f : ℝⁿ → ℝⁿ` and an open set `U`, the image of the critical set inside `U` is null. -/
theorem sardEuclidOn_self (n : ℕ) : SardEuclidOn n n := by
  intro f U hU hf
  refine volume_image_eq_zero_of_isCriticalPoint_on (s := {x | IsCriticalPoint f x} ∩ U) ?_ ?_
  · intro x hx
    exact ((hf.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by simp)).hasFDerivAt
      |>.hasFDerivWithinAt
  · intro x hx
    exact hx.1

/-! ## The decomposition of the critical set -/

/-- **The decomposition of the critical set along the stratification.**  Every critical point either
has non-vanishing derivative (`Crit f \ Zk f 1`), or lies in one of the strata differences
`Zk f (k+1) \ Zk f (k+2)` (a countable union), or is `(N+1)`-flat. -/
theorem Zk_one_subset_decomp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (N : ℕ) :
    Zk f 1 ⊆ (⋃ k : ℕ, (Zk f (k+1) \ Zk f (k+2))) ∪ Zk f (N+1) := by
  classical
  intro x hx
  by_cases h : ∃ k : ℕ, x ∉ Zk f (k+1)
  · have hspec : x ∉ Zk f (Nat.find h + 1) := Nat.find_spec h
    have hpos : 1 ≤ Nat.find h := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · rw [h0] at hspec
        exact absurd hx hspec
      · exact hpos
    have hZ : x ∈ Zk f (Nat.find h) := by
      rcases Nat.eq_zero_or_pos (Nat.find h - 1) with h0 | hpos'
      · have : Nat.find h = 1 := by omega
        rw [this]
        exact hx
      · have hlt : Nat.find h - 1 < Nat.find h := by omega
        have hpred : Nat.find h - 1 + 1 = Nat.find h := Nat.succ_pred_eq_of_pos hpos
        rw [← hpred]
        exact not_not.mp (Nat.find_min h hlt)
    refine Or.inl (Set.mem_iUnion.mpr ⟨Nat.find h - 1, ?_⟩)
    have hle : Nat.find h - 1 + 1 = Nat.find h := Nat.succ_pred_eq_of_pos hpos
    have hle' : Nat.find h - 1 + 2 = Nat.find h + 1 := by omega
    rw [hle, hle']
    exact ⟨hZ, hspec⟩
  · push Not at h
    exact Or.inr (h N)

/-- **The critical point set decomposes along the stratification.** -/
theorem isCriticalPoint_subset_decomp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (N : ℕ) :
    {x | IsCriticalPoint f x} ⊆
      ({x | IsCriticalPoint f x} \ Zk f 1) ∪ (⋃ k : ℕ, (Zk f (k+1) \ Zk f (k+2)))
        ∪ Zk f (N+1) := by
  intro x hx
  by_cases h1 : x ∈ Zk f 1
  · rcases Zk_one_subset_decomp f N h1 with hB | hC
    · exact Or.inl (Or.inr hB)
    · exact Or.inr hC
  · exact Or.inl (Or.inl ⟨hx, h1⟩)

end

end Work.ThomBordism.Transversality
