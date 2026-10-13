/-
  WilVP (curric-46): the vocabulary of the `ValProp_TR` route ("uniform iso-balls").

  Design: `sources/wilkiesVP/wilkies_valprop_design.md`, exact nodes
  `sources/wilkiesVP/wilkies_valprop_design.lean`, fixes
  `sources/wilkiesVP/wilkies_valprop_design_REVIEW.md`.

  Route:  `Work.WilC4.realULPM` (C4) + `Work.WilC4.ulpm_mono_param` (C4, proved)
            |
            +-- N1 `isoBall_real : IsoBallProp ℝ`               (file `N1_iso.lean` + nodes)
            +-- N2 `transferOfIsoBall : IsoBallProp ℝ -> all M` (file `N2_transfer.lean`)
            +-- N3 `valProp_of_isoBall : (all M) -> ValProp`    (file `N3_valprop.lean`)
            |
            `ValProp_TR`                                        (file `ValProp_TR.lean`)

  This file: *definitions only* (plus the two bookkeeping lemmas `mem_shiftFam`,
  `shiftFam_eq_preimage`).  It is deliberately free of `Submission.Work.WilC5.stdPart` and of
  `Submission.Work.WilC5.LRcReduct`: importing those makes every later statement that mentions
  an `ℝ`-structure instance (`ModelULPM ℝ`, `IsoBallProp ℝ`, `RhoFam`, any N1 node, N2) fail to
  elaborate (review fix F1).  Only N3a's file may import `stdPart`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

namespace Work.WilVP

/-! ## 0. The interface: uniform iso-balls -/

/-- **IsoBallProp M.** For every `∅`-definable family of partial functions `x ↦ y` (parameters
`c`) whose domain fibres are bounded, there are `N : ℕ` and an `∅`-definable family `P_c` of at
most `N` points such that `|F_c|` changes by at most the factor `N` on the ball of radius
`dist(x, P_c)/N` around any point `x` with `F_c(x) ≠ 0` (and the ball lies in the domain).

More precisely: for `x, y₀, y` with `F_c(x) = y₀ ≠ 0` and `N|y − x| < |x − p|` for every
`p ∈ P_c`, the value `F_c(y) =: y₁` exists and `|y₁| ≤ N|y₀|`, `|y₀| ≤ N|y₁|`. -/
def IsoBallProp (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M] : Prop :=
  ∀ (k : ℕ) (Y : Set (Fin (k + 2) → M)), (∅ : Set M).Definable LRc Y →
    (∀ (c : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
    (∀ c : Fin k → M, ∃ R : M, ∀ x y : M, Fin.cons x (Fin.cons y c) ∈ Y → |x| ≤ R) →
    ∃ N : ℕ, 0 < N ∧ ∃ P : Set (Fin (k + 1) → M), (∅ : Set M).Definable LRc P ∧
      ∀ c : Fin k → M, {x : M | Fin.cons x c ∈ P}.encard ≤ N ∧
        ∀ x y₀ y : M, Fin.cons x (Fin.cons y₀ c) ∈ Y → y₀ ≠ 0 →
          (∀ p : M, Fin.cons p c ∈ P → (N : M) * |y - x| < |x - p|) →
          ∃ y₁ : M, Fin.cons y (Fin.cons y₁ c) ∈ Y ∧
            |y₁| ≤ (N : M) * |y₀| ∧ |y₀| ≤ (N : M) * |y₁|

/-! ## 1. The recentred family -/

/-- The recentred family `t ↦ F_c(p + σ t)` with parameters `(p, c)` (`σ = 1` right, `σ = -1`
left).  A tuple `v` has coordinates `v 0 = t` (the new variable), `v 1 = y` (the value),
`v 2 = p` (the new centre) and `Fin.tail (Fin.tail (Fin.tail v)) = c`. -/
def shiftFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (σ : ℝ) : Set (Fin ((k + 1) + 2) → ℝ) :=
  {v | Fin.cons (v 2 + σ * v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail (Fin.tail v)))) ∈ Y}

/-- Membership in the recentred family, in the coordinates `(t, y, p, c)`. -/
theorem mem_shiftFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (σ t y p : ℝ) (c : Fin k → ℝ) :
    Fin.cons t (Fin.cons y (Fin.cons p c)) ∈ shiftFam Y σ ↔
      Fin.cons (p + σ * t) (Fin.cons y c) ∈ Y := by
  rw [shiftFam, Set.mem_ofPred_eq]
  have h1 : ((Fin.cons t (Fin.cons y (Fin.cons p c)) : Fin ((k + 1) + 2) → ℝ) 2) = p := rfl
  have h0 : ((Fin.cons t (Fin.cons y (Fin.cons p c)) : Fin ((k + 1) + 2) → ℝ) 0) = t := rfl
  have h2 : ((Fin.cons t (Fin.cons y (Fin.cons p c)) : Fin ((k + 1) + 2) → ℝ) 1) = y := rfl
  have h3 : (Fin.tail (Fin.tail (Fin.tail
      (Fin.cons t (Fin.cons y (Fin.cons p c)) : Fin ((k + 1) + 2) → ℝ)))) = c := by
    funext i; rfl
  rw [h1, h0, h2, h3]

/-- Membership in the recentred family, with an arbitrary parameter tuple `c'`. -/
theorem mem_shiftFam' {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (σ t y : ℝ) (c' : Fin (k + 1) → ℝ) :
    Fin.cons t (Fin.cons y c') ∈ shiftFam Y σ ↔
      Fin.cons (c' 0 + σ * t) (Fin.cons y (Fin.tail c')) ∈ Y := by
  have hc : (Fin.cons t (Fin.cons y c') : Fin ((k + 1) + 2) → ℝ) =
      Fin.cons t (Fin.cons y (Fin.cons (c' 0) (Fin.tail c'))) := by
    rw [Fin.cons_self_tail c']
  rw [hc, mem_shiftFam]

/-- The recentred family as a preimage of `Y`. -/
theorem shiftFam_eq_preimage {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (σ : ℝ) :
    shiftFam Y σ = (fun v : Fin ((k + 1) + 2) → ℝ =>
      Fin.cons (v 2 + σ * v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail (Fin.tail v))))) ⁻¹' Y :=
  rfl

/-- `shiftFam` of a family of graphs is a family of graphs. -/
theorem shiftFam_fun {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {σ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') :
    ∀ (c' : Fin (k + 1) → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c') ∈ shiftFam Y σ →
      Fin.cons x (Fin.cons y' c') ∈ shiftFam Y σ → y = y' := by
  intro c' x y y' hy hy'
  rw [mem_shiftFam'] at hy hy'
  exact hfun (Fin.tail c') (c' 0 + σ * x) y y' hy hy'

/-! ## 2. Good radii and the iso-radius -/

/-- `r` is a **good radius** at `x` (where the value is `y₀ ≠ 0`): the open `r`-ball around `x`
lies in the domain of the fibre and `|F_c|` stays within the factor `K₀` of `|y₀|` on it. -/
def IsoGood {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (K₀ : ℝ) (c : Fin k → ℝ) (x y₀ r : ℝ) : Prop :=
  ∀ u : ℝ, |u - x| < r → ∃ y : ℝ, Fin.cons u (Fin.cons y c) ∈ Y ∧
    |y| ≤ K₀ * |y₀| ∧ |y₀| ≤ K₀ * |y|

/-- Goodness is downward closed in the radius. -/
theorem IsoGood.mono {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ} {c : Fin k → ℝ}
    {x y₀ r r' : ℝ} (hrr' : r' ≤ r) (h : IsoGood Y K₀ c x y₀ r) :
    IsoGood Y K₀ c x y₀ r' :=
  fun u hu => h u (lt_of_lt_of_le hu hrr')

/-- The iso-radius family `ρ_c(x) = inf {r ≥ 0 : r not good}` (as a graph, with parameters `c`).
The tuple is `v = (x, ρ, c)`: `v 0 = x`, `v 1 = ρ`, `Fin.tail (Fin.tail v) = c`.

It is **intrinsic**: no centre is involved.  It is defined only where the value `y₀` at `x`
exists and is nonzero. -/
def RhoFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (K₀ : ℝ) : Set (Fin (k + 2) → ℝ) :=
  {v | ∃ y₀ : ℝ, Fin.cons (v 0) (Fin.cons y₀ (Fin.tail (Fin.tail v))) ∈ Y ∧ y₀ ≠ 0 ∧
    IsGLB {r : ℝ | 0 ≤ r ∧ ¬ IsoGood Y K₀ (Fin.tail (Fin.tail v)) (v 0) y₀ r} (v 1)}

/-- The fibre-level version of `RhoFam` membership: `ρ` is the iso-radius of the `c`-fibre at
`x` (a value `y₀ ≠ 0` at `x` exists and `ρ` is the GLB of the bad radii). -/
def RhoVal {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (K₀ : ℝ) (c : Fin k → ℝ) (x ρ : ℝ) : Prop :=
  ∃ y₀ : ℝ, Fin.cons x (Fin.cons y₀ c) ∈ Y ∧ y₀ ≠ 0 ∧
    IsGLB {r : ℝ | 0 ≤ r ∧ ¬ IsoGood Y K₀ c x y₀ r} ρ

/-- `RhoVal` at `(x, ρ, c)` is `RhoFam` membership of the corresponding tuple. -/
theorem rhoFam_mem_iff {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (x ρ : ℝ) (c : Fin k → ℝ) :
    Fin.cons x (Fin.cons ρ c) ∈ RhoFam Y K₀ ↔ RhoVal Y K₀ c x ρ := by
  rw [RhoFam, Set.mem_ofPred_eq, RhoVal]
  have h1 : (Fin.tail (Fin.tail (Fin.cons x (Fin.cons ρ c) : Fin (k + 2) → ℝ))) = c := by
    funext i; simp [Fin.tail]
  have h2 : (Fin.cons x (Fin.cons ρ c) : Fin (k + 2) → ℝ) 0 = x := rfl
  have h3 : (Fin.cons x (Fin.cons ρ c) : Fin (k + 2) → ℝ) 1 = ρ := rfl
  rw [h1, h2, h3]

/-- The specialisation of `rhoFam_mem_iff` to a fixed value `y₀`. -/
theorem rhoVal_iff {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (c : Fin k → ℝ) (x ρ : ℝ) :
    RhoVal Y K₀ c x ρ ↔ ∃ y₀ : ℝ, Fin.cons x (Fin.cons y₀ c) ∈ Y ∧ y₀ ≠ 0 ∧
      IsGLB {r : ℝ | 0 ≤ r ∧ ¬ IsoGood Y K₀ c x y₀ r} ρ :=
  Iff.rfl

/-! ## 3. Fibre vocabulary -/

/-- The domain family of `Y`: the parameters `(x, c)` where the `c`-fibre has a value at `x`. -/
def DomFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | ∃ y : ℝ, Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y}

/-- The zero family of `Y`: the parameters `(x, c)` where the `c`-fibre has the value `0` at
`x`. -/
def ZeroFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {v | ∃ y : ℝ, Fin.cons (v 0) (Fin.cons y (Fin.tail v)) ∈ Y ∧ y = 0}

/-- The fibre of the domain family at `c`. -/
def DomFib {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y}

/-- The fibre of the zero family at `c`. -/
def ZeroFib {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y ∧ y = 0}

/-- The fibre where the fibre of `Y` has a *nonzero* value at `x`. -/
def ValFib {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0}

theorem domFib_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) :
    {x : ℝ | Fin.cons x c ∈ DomFam Y} = DomFib Y c := rfl

theorem zeroFib_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) :
    {x : ℝ | Fin.cons x c ∈ ZeroFam Y} = ZeroFib Y c := rfl

/-- For a family of graphs, "the value at `x` is nonzero" is the same as "there is a value and
`x` is not a zero of the fibre". -/
theorem valFib_eq {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') (c : Fin k → ℝ) :
    ValFib Y c = DomFib Y c \ ZeroFib Y c := by
  ext x
  constructor
  · rintro ⟨y, hy, hy0⟩
    exact ⟨⟨y, hy⟩, fun hz => by
      obtain ⟨y', hy', hy'0⟩ := hz
      exact hy0 (by rw [hfun c x y y' hy hy', hy'0])⟩
  · rintro ⟨⟨y, hy⟩, hz⟩
    refine ⟨y, hy, fun hy0 => hz ⟨y, hy, hy0⟩⟩

end Work.WilVP