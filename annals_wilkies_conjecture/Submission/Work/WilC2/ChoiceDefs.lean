/-
  Area C2 (WilC2): the *definable choice* on a fibre, semantic side.

  Given a parametric `LRc`-formula `φ : ParamFormula n` (parameters `Fin n`, one point variable),
  the fibre over `v : Fin n → M` is `Fib φ v = {y | φ.Realize (Sum.elim v (fun _ => y))}`.

  The choice is built in three steps.

  * `LeftComp φ v` is the **leftmost component** of the fibre: the set of points `y` of the fibre
    which are connected inside the fibre to *every* lower fibre point, i.e.
    `∀ z ∈ Fib, z < y → (z,y) ⊆ Fib`.  This is an order-convex (hence connected) nonempty subset
    of the fibre as soon as the fibre is nonempty and a finite union of intervals
    (`LeftComp_nonempty` in `Submission.Work.WilC2.LeftComp_nonempty`).

  * `rescale y = y / (1 + |y|)` is the increasing homeomorphism `ℝ → (-1,1)` taking the leftmost
    component to a *bounded* interval.  So the image `TZset φ v = rescale '' LeftComp φ v` is a
    nonempty bounded interval and has an infimum `m` and a supremum `M`, each characterized by a
    purely order-theoretic (hence first-order) property `IsInfTZ`, `IsSupTZ`.

  * the selected point is the preimage under `rescale` of the midpoint `(m+M)/2`, which lies in
    the interval `TZset φ v` because that interval is order-convex.

  The point of the rescaling is that it removes all case distinctions (bounded / unbounded /
  singleton) from the construction, so that the first-order formula defining the choice stays
  short: `ChoiceCond φ v y` is the resulting condition on `(v,y)`, and the syntactic counterpart
  is a formula `selectForm φ : ParamFormula n` whose realisation is exactly `ChoiceCond`
  (module `Submission.Work.WilC2.selectForm`).
-/
import Submission.Work.WilC2.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

variable {n : ℕ}

/-! ## 1. The fibre and its leftmost component -/

/-- The fibre of the parametric family `φ` at the parameter `v`. -/
def Fib {M : Type*} [LRc.Structure M] (φ : ParamFormula n) (v : Fin n → M) : Set M :=
  {y | φ.Realize (Sum.elim v (fun _ => y))}

/-- The leftmost component of the fibre: the points `y` of the fibre connected inside the fibre to
every lower point of the fibre. -/
def LeftComp {M : Type*} [LRc.Structure M] [LinearOrder M] (φ : ParamFormula n)
    (v : Fin n → M) : Set M :=
  {y | y ∈ Fib φ v ∧ ∀ z, z ∈ Fib φ v → z < y → ∀ w, z < w → w < y → w ∈ Fib φ v}

theorem mem_LeftComp {M : Type*} [LRc.Structure M] [LinearOrder M] {φ : ParamFormula n}
    {v : Fin n → M} {y : M} :
    y ∈ LeftComp φ v ↔ y ∈ Fib φ v ∧
      ∀ z, z ∈ Fib φ v → z < y → ∀ w, z < w → w < y → w ∈ Fib φ v := Iff.rfl

theorem LeftComp_subset_Fib {M : Type*} [LRc.Structure M] [LinearOrder M] {φ : ParamFormula n}
    {v : Fin n → M} : LeftComp φ v ⊆ Fib φ v := fun _ hy => hy.1

/-- The leftmost component is order-convex: if `x ≤ y` both lie in it, everything between does. -/
theorem LeftComp_ordConnected {M : Type*} [LRc.Structure M] [LinearOrder M]
    {φ : ParamFormula n} {v : Fin n → M} : (LeftComp φ v).OrdConnected := by
  refine Set.OrdConnected.mk ?_
  intro x ⟨hxF, hx⟩ y ⟨hyF, hy⟩ w hw
  obtain ⟨hxw, hwy⟩ := hw
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hxw with h | h
    · rw [← h]; exact hxF
    · rcases eq_or_lt_of_le hwy with h' | h'
      · rw [h']; exact hyF
      · exact hy x hxF (lt_trans h h') w h h'
  · intro z hzF hzw w' hzw' hw'w
    have hzlt : z < y := lt_of_lt_of_le hzw hwy
    have hw'lt : w' < y := lt_of_lt_of_le hw'w hwy
    exact hy z hzF hzlt w' hzw' hw'lt

/-! ## 2. The rescaling `y ↦ y / (1 + |y|)` of `ℝ` -/

/-- The rescaling `y ↦ y / (1 + |y|)`, an increasing homeomorphism `ℝ → (-1,1)`. -/
def rescale (y : ℝ) : ℝ := y / (1 + |y|)

theorem rescale_eq_div (y : ℝ) : rescale y = y / (1 + |y|) := rfl

theorem rescale_of_nonneg {y : ℝ} (h : 0 ≤ y) : rescale y = y / (1 + y) := by
  rw [rescale, abs_of_nonneg h]

theorem rescale_of_neg {y : ℝ} (h : y < 0) : rescale y = y / (1 - y) := by
  rw [rescale, abs_of_neg h]
  ring_nf

theorem rescale_nonneg {y : ℝ} (h : 0 ≤ y) : 0 ≤ rescale y := by
  rw [rescale_of_nonneg h]
  exact div_nonneg h (by linarith)

theorem rescale_pos {y : ℝ} (h : 0 < y) : 0 < rescale y := by
  rw [rescale_of_nonneg h.le]
  exact div_pos h (by linarith)

theorem rescale_neg {y : ℝ} (h : y < 0) : rescale y < 0 := by
  rw [rescale_of_neg h]
  exact div_neg_of_neg_of_pos h (by linarith)

theorem rescale_abs_lt_one (y : ℝ) : |rescale y| < 1 := by
  have h : 0 < 1 + |y| := by positivity
  rw [rescale_eq_div, abs_div, abs_of_pos h, div_lt_one h]
  linarith

theorem rescale_injective : Function.Injective rescale := by
  intro y₁ y₂ h
  rcases le_or_gt 0 y₁ with h₁ | h₁
  · rcases le_or_gt 0 y₂ with h₂ | h₂
    · rw [rescale_of_nonneg h₁, rescale_of_nonneg h₂,
        div_eq_div_iff (by linarith) (by linarith)] at h
      nlinarith
    · exact absurd h.symm (ne_of_lt (lt_of_lt_of_le (rescale_neg h₂) (rescale_nonneg h₁)))
  · rcases le_or_gt 0 y₂ with h₂ | h₂
    · exact absurd h (ne_of_lt (lt_of_lt_of_le (rescale_neg h₁) (rescale_nonneg h₂)))
    · rw [rescale_of_neg h₁, rescale_of_neg h₂,
        div_eq_div_iff (by linarith) (by linarith)] at h
      linarith

theorem rescale_mono : Monotone rescale := by
  intro y₁ y₂ hy
  rcases le_or_gt 0 y₁ with h₁ | h₁
  · have h₂ : 0 ≤ y₂ := le_trans h₁ hy
    rw [rescale_of_nonneg h₁, rescale_of_nonneg h₂,
      div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · rcases le_or_gt 0 y₂ with h₂ | h₂
    · exact le_trans (le_of_lt (rescale_neg h₁)) (rescale_nonneg h₂)
    · rw [rescale_of_neg h₁, rescale_of_neg h₂,
        div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith

theorem rescale_bddAbove (S : Set ℝ) : BddAbove (rescale '' S) :=
  ⟨1, by rintro _ ⟨y, -, rfl⟩; exact le_of_lt (abs_lt.mp (rescale_abs_lt_one y)).2⟩

theorem rescale_bddBelow (S : Set ℝ) : BddBelow (rescale '' S) :=
  ⟨-1, by rintro _ ⟨y, -, rfl⟩; exact le_of_lt (abs_lt.mp (rescale_abs_lt_one y)).1⟩

/-- The rescaling is inverted by `t ↦ t / (1 - |t|)` on `(-1,1)`. -/
theorem rescale_inv {t : ℝ} (ht : |t| < 1) : rescale (t / (1 - |t|)) = t := by
  have ht1 : 0 < 1 - |t| := by linarith [abs_lt.mp ht]
  rcases le_or_gt 0 t with ht0 | ht0
  · have habs : |t| = t := abs_of_nonneg ht0
    have h1 : (1 : ℝ) - t ≠ 0 := by rw [← habs]; exact ne_of_gt ht1
    have hu : 0 ≤ t / (1 - |t|) := div_nonneg ht0 ht1.le
    rw [rescale_of_nonneg hu, habs]
    have h2 : (1 : ℝ) + t / (1 - t) ≠ 0 := by
      rw [show (1 : ℝ) + t / (1 - t) = 1 / (1 - t) by field_simp; ring]
      exact div_ne_zero one_ne_zero h1
    field_simp
    ring
  · have habs : |t| = -t := abs_of_neg ht0
    have hpos : 0 < 1 + t := by linarith [abs_lt.mp ht]
    have hu : t / (1 - |t|) < 0 := div_neg_of_neg_of_pos ht0 ht1
    rw [rescale_of_neg hu, habs,
      show (1 : ℝ) - -t = 1 + t by ring]
    have h1 : (1 : ℝ) + t ≠ 0 := ne_of_gt hpos
    have h2 : (1 : ℝ) - t / (1 + t) ≠ 0 := by
      rw [show (1 : ℝ) - t / (1 + t) = 1 / (1 + t) by field_simp; ring]
      exact div_ne_zero one_ne_zero h1
    field_simp
    ring

/-- The rescaling is an increasing bijection onto `(-1,1)`, hence carries intervals to
intervals. -/
theorem rescale_image_ordConnected {S : Set ℝ} (hS : S.OrdConnected) :
    (rescale '' S).OrdConnected := by
  refine Set.OrdConnected.mk ?_
  intro x hx z hz y hy
  obtain ⟨hxy, hyz⟩ := hy
  obtain ⟨a, haS, rfl⟩ := hx
  obtain ⟨b, hbS, rfl⟩ := hz
  have hy1 : |y| < 1 := by
    have h1 := abs_lt.mp (rescale_abs_lt_one a)
    have h2 := abs_lt.mp (rescale_abs_lt_one b)
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine ⟨y / (1 - |y|), hS.out' haS hbS ⟨?_, ?_⟩, rescale_inv hy1⟩
  · by_contra hcon
    rw [not_le] at hcon
    have h3 : rescale (y / (1 - |y|)) ≤ rescale a := rescale_mono hcon.le
    rw [rescale_inv hy1] at h3
    have h4 : y = rescale a := le_antisymm h3 hxy
    have h5 : y / (1 - |y|) = a := rescale_injective (by rw [rescale_inv hy1, h4])
    linarith
  · by_contra hcon
    rw [not_le] at hcon
    have h3 : rescale b ≤ rescale (y / (1 - |y|)) := rescale_mono hcon.le
    rw [rescale_inv hy1] at h3
    have h4 : y = rescale b := le_antisymm hyz h3
    have h5 : y / (1 - |y|) = b := rescale_injective (by rw [rescale_inv hy1, h4])
    linarith

/-! ## 3. The relation `t = y / (1 + |y|)` and the choice condition -/

/-- `t = y / (1 + |y|)`, written without the `|·|` symbol (the two branches are `y ≥ 0` and
`y < 0`). -/
def RescaleRel {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M] (y t : M) : Prop :=
  (0 ≤ y ∧ t * (1 + y) = y) ∨ (y < 0 ∧ t * (1 - y) = y)

theorem rescaleRel_iff_real {y t : ℝ} : RescaleRel y t ↔ rescale y = t := by
  constructor
  · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
    · rw [rescale_of_nonneg hy, div_eq_iff (by linarith)]
      linarith
    · rw [rescale_of_neg hy, div_eq_iff (by linarith)]
      linarith
  · intro h
    rcases le_or_gt 0 y with hy | hy
    · left
      refine ⟨hy, ?_⟩
      rw [rescale_of_nonneg hy, div_eq_iff (by linarith)] at h
      linarith
    · right
      refine ⟨hy, ?_⟩
      rw [rescale_of_neg hy, div_eq_iff (by linarith)] at h
      linarith

/-- The rescaled leftmost component: the set of values `rescale y`, `y` in the leftmost
component.  Over `ℝ` this is `rescale '' LeftComp φ v` (`TZset_eq_image`). -/
def TZset {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [LRc.Structure M]
    (φ : ParamFormula n) (v : Fin n → M) : Set M :=
  {t | ∃ y', y' ∈ LeftComp φ v ∧ RescaleRel y' t}

theorem TZset_eq_image {n : ℕ} (φ : ParamFormula n) (v : Fin n → ℝ) :
    TZset φ v = rescale '' LeftComp φ v := by
  ext t
  constructor
  · rintro ⟨y, hy, hrel⟩
    exact ⟨y, hy, rescaleRel_iff_real.mp hrel⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rescaleRel_iff_real.mpr rfl⟩

/-- `m` is the infimum of the rescaled leftmost component (a purely order-theoretic, hence
first-order, characterisation). -/
def IsInfTZ {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [LRc.Structure M]
    (φ : ParamFormula n) (v : Fin n → M) (m : M) : Prop :=
  (∀ t, t ∈ TZset φ v → m ≤ t) ∧ ∀ m', (∀ t, t ∈ TZset φ v → m' ≤ t) → m' ≤ m

/-- `M` is the supremum of the rescaled leftmost component. -/
def IsSupTZ {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [LRc.Structure M]
    (φ : ParamFormula n) (v : Fin n → M) (s : M) : Prop :=
  (∀ t, t ∈ TZset φ v → t ≤ s) ∧ ∀ s', (∀ t, t ∈ TZset φ v → t ≤ s') → s ≤ s'

/-- **The choice condition.**  `y` lies in the leftmost component of the fibre, and its rescaling
is the midpoint of the rescaled leftmost component. -/
def ChoiceCond {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [LRc.Structure M]
    (φ : ParamFormula n) (v : Fin n → M) (y : M) : Prop :=
  y ∈ LeftComp φ v ∧ ∃ m s t : M,
    IsInfTZ φ v m ∧ IsSupTZ φ v s ∧ RescaleRel y t ∧ t + t = m + s

end Work.WilC2
