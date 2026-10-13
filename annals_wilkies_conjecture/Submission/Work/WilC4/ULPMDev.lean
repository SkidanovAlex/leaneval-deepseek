/-
  WilC4/ULPMDev : the vocabulary of the *deviation* step of the proof of H1
  (`Work.WilC4.Route.realULPM`).

  ## What this file is for

  `Route.ModelULPM` needs, for a `∅`-definable family of graphs `Y ⊆ ℝ^{k+2}`: a uniform bound
  `N`, a finite `Qs ⊆ ℚ` and a `∅`-definable breakpoint family `B` with `|B_c| ≤ N` such that any
  two positive points on the same side of `B_c` have comparable normalised values.

  The plan (see `ULPM_NOTES.md` §3–§4bis and `ULPM_E_DEV.md`) is:

  1. The critical set `B₀ : (ulpm_crit)` makes the fibre continuous, vanishing only all-or-nothing
     and a function off `B₀`; adding `ulpm_mono_param` applied to `Y` and to `RatGraph Y` makes the
     fibre and the doubling ratio *monotone* off `B₀`.
  2. `E := Route.ClusterE Y B₀` is **finite** (`ulpm_E_finite`) and consists of `0` and of `2^q`,
     `q ∈ ℚ`.
  3. **The deviation decay.**  `w = f_c(2x)/f_c(x)` at an `M`-deep point is within a factor
     `1 + ε` of some positive element of `E`, for `M` large (`dev_decay`), with a *power* rate
     (`dev_rate`, from `pb_decay`).  The vocabulary for this is defined here.
  4. Telescoping over the dyadic chain inside a slot of
     `B := B₀ ∪ ∂{x : f_c(2x)/f_c(x) ∈ Mid}` (`Mid` = the geometric midpoints of `E ∩ (0,∞)`).

  This module fixes the vocabulary of steps 2 and 3 (the ratio relation `RatW`, the bad-scale set
  `BadScale`, the deviation bound `DevBdd` and its capped-sup graph `DevG`) and proves the
  bookkeeping lemmas that relate `RatW` to the pre-existing `Route.RatGraph` (so that
  `ulpm_mono_param` applies to the ratio) and that `Route.ClusterE` and `ClusterER` coincide.
-/
import Mathlib
import Submission.Work.WilC4.ULPMRoute
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ulpm_crit
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.ulpm_E_finite
import Submission.Work.WilC4.pb_decay

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr InD valY IsDeep InSlot SameSide)

variable {k : ℕ}

/-! ## 1. The doubling ratio of the fibre -/

/-- `RatW Y c x w` : `w` is the doubling ratio `f_c(2x)/f_c(x)` of the fibre of `Y` at the
parameter `c`.  Written without division (`w * y = y'` with `y ≠ 0`), so it is a relation that can
enter a `Definable` statement.  This is exactly the fibre relation of `Route.RatGraph`, see
`ratGraph_mem_iff`. -/
def RatW (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x w : ℝ) : Prop :=
  ∃ y y' : ℝ, Gr Y c x y ∧ Gr Y c (2 * x) y' ∧ y ≠ 0 ∧ w * y = y'

/-- `RatW` is the fibre relation of `Route.RatGraph`. -/
theorem ratGraph_mem_iff (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x w : ℝ) :
    Fin.cons x (Fin.cons w c) ∈ Route.RatGraph Y ↔ RatW Y c x w := by
  constructor
  · rintro ⟨y, y', hy, hy0, hy', hwy⟩
    simp only [Fin.cons_zero, Fin.cons_succ] at hy hy' hwy
    exact ⟨y, y', hy, hy', hy0, hwy⟩
  · rintro ⟨y, y', hy, hy', hy0, hwy⟩
    exact ⟨y, y', by simpa using hy, hy0, by simpa using hy', by simpa using hwy⟩

/-- The graph of the doubling ratio is a family of graphs as soon as `Y` is.  (A copy of
`Route.ratGraph_is_graph` in the `RatW` spelling, used to feed `ulpm_mono_param`.) -/
theorem ratW_functional {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y') :
    ∀ (c : Fin k → ℝ) (x w w' : ℝ), RatW Y c x w → RatW Y c x w' → w = w' := by
  intro c x w w' hw hw'
  rw [← ratGraph_mem_iff] at hw hw'
  exact Route.ratGraph_is_graph hfun c x w w' hw hw'

/-- The zero-free part of the family: the fibre of `Y₀` is nowhere zero (wherever defined). -/
def Nozero (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) := {v | v ∈ Y ∧ v 1 ≠ 0}

/-- The total, zero-free replacement of `Y`: the fibre is `f_c(x)` where that is defined and
nonzero, and the constant `1` where it is undefined or zero.

This is the family to which `GoodFibre` and hence `ulpm_E_finite` can be applied: its fibre is
total and nowhere zero, and it agrees with `Y` on every interval on which `f_c` is nowhere zero. -/
def UlpmTot (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | (v ∈ Y ∧ v 1 ≠ 0) ∨
    (v 1 = 1 ∧ ∀ y' : ℝ, ¬ (Gr Y (fun i : Fin k => v i.succ.succ) (v 0) y' ∧ y' ≠ 0))}

theorem ulpmTot_gr_iff (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ) :
    Gr (UlpmTot Y) c x y ↔
      (Gr Y c x y ∧ y ≠ 0) ∨ (y = 1 ∧ ∀ y' : ℝ, ¬ (Gr Y c x y' ∧ y' ≠ 0)) := by
  simp only [Gr, UlpmTot, Set.mem_setOf_eq, Fin.cons_succ, Fin.cons_zero]
  tauto


theorem nozero_gr_iff {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x y : ℝ} :
    Gr (Nozero Y) c x y ↔ Gr Y c x y ∧ y ≠ 0 := Iff.rfl

/-- The fibre of `Y` at a point where it is nonzero is the fibre of `Nozero Y`. -/
theorem gr_of_mem_nozero {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x y : ℝ}
    (h : Gr Y c x y) (hy : y ≠ 0) : Gr (Nozero Y) c x y := ⟨h, hy⟩

/-! ## 2. The two cluster sets coincide -/

/-- `ClusterER` (real scales) contains `ClusterE` (natural scales): the real-scale condition at
the *integer* scale `B` is literally the natural-scale condition. -/
theorem ClusterER_subset_ClusterE (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    ClusterER Y B₀ ⊆ Route.ClusterE Y B₀ := by
  intro ρ hρ B hB
  have hB' : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  obtain ⟨c, x, hx, hdeep, hrat⟩ := hρ (B : ℝ) hB'
  exact ⟨c, x, hx, hdeep, hrat⟩

theorem ClusterE_eq_ClusterER (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) :
    Route.ClusterE Y B₀ = ClusterER Y B₀ :=
  Set.Subset.antisymm (ClusterE_subset_ClusterER Y B₀) (ClusterER_subset_ClusterE Y B₀)

/-! ## 3. The bad scales and the deviation bound -/

/-- `BadScale Y B₀ ε` : the set of scales `M > 0` at which some `M`-deep doubling ratio is at
multiplicative distance `> ε` from every positive cluster value.  `dev_decay` says that this set
is bounded above for every `ε > 0`. -/
def BadScale (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    (ε : ℝ) : Set ℝ :=
  {M | 0 < M ∧ ∃ (c : Fin k → ℝ) (x w : ℝ),
    0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧
      ∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|}

/-- The geometric midpoints of two *consecutive* positive elements of `E`: the points `x` with
`x ^ 2 = ρ₁ * ρ₂`, `0 < x`, where `ρ₁ < ρ₂` are consecutive positive elements of `E`.  Taking
`B` to contain the level crossings of the doubling ratio with `Mid (ClusterE Y B₀)` confines the
ratio to a single band on every slot of `B`, which is what makes the telescoping of the ULPM
proof work. -/
def Mid (E : Set ℝ) : Set ℝ :=
  {x | ∃ ρ₁ ∈ E, ∃ ρ₂ ∈ E, 0 < ρ₁ ∧ ρ₁ < ρ₂ ∧
    (∀ ρ ∈ E, 0 < ρ → ρ ≤ ρ₁ ∨ ρ₂ ≤ ρ) ∧ x * x = ρ₁ * ρ₂ ∧ 0 < x}

/-- The structural hypotheses on a breakpoint family `B₀` for a `∅`-definable family of graphs
`Y`: off `B₀` the fibre is a continuous nonvanishing function, and the doubling ratio is monotone.
This is what `ulpm_crit` (applied to `Y`) together with `ulpm_mono_param` (applied to `Y` and to
`RatGraph Y`) supplies. -/
def ULPMStruct (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Prop :=
  GoodFibre Y B₀ ∧
    ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
      ∀ x₁ x₂ x₃ w₁ w₂ w₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → RatW Y c x₁ w₁ → RatW Y c x₂ w₂ → RatW Y c x₃ w₃ →
        (w₁ ≤ w₂ ∧ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ∧ w₂ ≤ w₁)

/-- `DevBdd Y B E M y` : `y` is an upper bound for the multiplicative deviations of the `B`-deep
doubling ratios from the cluster set `E` at scale `M`. -/
def DevBdd (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    (M y : ℝ) : Prop :=
  ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x → IsDeepR B c M x → RatW Y c x w →
    ∃ ρ ∈ E, 0 < ρ ∧ |w / ρ - 1| ≤ y

/-- `DevG Y B E` : the graph of the *least* upper bound (capped at `1`) for the deviations.  At a
scale `M` this is the singleton `{min (sup deviations) 1}` when the deviations are bounded by `1`,
and the empty set otherwise.  It is the `∅`-definable 2-ary family to which `pb_decay` is applied
in `dev_rate`. -/
def DevG (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | DevBdd Y B E (v 0) (v 1) ∧ v 1 ≤ 1 ∧ ∀ y' : ℝ, y' < v 1 → ¬ DevBdd Y B E (v 0) y'}

/-- `BadScale` in the `DevBdd` spelling: a tolerance `ε > 0` bounds the deviations at scale `M`
for every large `M` iff no large `M` is `BadScale`-bad at tolerance `ε`. -/
theorem badScale_iff (Y : Set (Fin (k + 2) → ℝ)) (B : Set (Fin (k + 1) → ℝ)) (E : Set ℝ)
    {ε : ℝ} :
    (∃ M : ℝ, M ∈ BadScale Y B E ε) ↔ (∃ M : ℝ, 0 < M ∧ ¬ DevBdd Y B E M ε) := by
  constructor
  · rintro ⟨M, hM, c, x, w, hx, hdeep, hrat, hbad⟩
    exact ⟨M, hM, fun hbdd => by
      obtain ⟨ρ, hρE, hρ0, hle⟩ := hbdd c x w hx hdeep hrat
      exact absurd hle (not_le.mpr (hbad ρ hρE hρ0))⟩
  · rintro ⟨M, hM, hbdd⟩
    refine ⟨M, hM, ?_⟩
    by_contra hcon
    refine hbdd fun c x w hx hdeep hrat => ?_
    by_contra hcon2
    exact hcon ⟨c, x, w, hx, hdeep, hrat, fun ρ hρE hρ0 => by
      by_contra hle
      exact hcon2 ⟨ρ, hρE, hρ0, le_of_not_gt hle⟩⟩

end Work.WilC4
