/-
  WilC4/ULPMAsm : glue lemmas for the final assembly of `Work.WilC4.realULPM`.

  Nothing here is deep; this is the bookkeeping that connects the pieces:

  * `ClusterE_mono` / `IsDeepR.mono_B` — deepness and the cluster set are monotone in the
    breakpoint family (`B₀ ⊆ B` ⇒ `ClusterE Y B ⊆ ClusterE Y B₀`).
  * `mono_valY_of_trichotomy` — a three-point "monotone or antitone" trichotomy for the *relation*
    `Gr` gives `MonotoneOn`/`AntitoneOn` for the value function `valY` (via `mono_of_three_point`).
  * `ratW_ratioY` — where the fibre is a continuous nonvanishing function, `RatW` holds for the
    ratio `valY (2x) / valY x`.
  * `expSet_toFinset` — `ExpSet E` as a `Finset` when `E` is finite.
  * `ulpmTot_eq_of_ne_zero` — where the fibre of `Y` is defined and nonzero, it agrees with the
    fibre of `UlpmTot Y`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.ULPMB
import Submission.Work.WilC4.mono_of_three_point
import Submission.Work.WilC4.monoOn_Icc_of_Ioo

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr InD valY ratioY eq_valY valY_mem IsDeep ClusterE)

variable {k : ℕ}

/-! ## 1. Monotonicity in the breakpoint family -/

/-- Deepness is antitone in the breakpoint family: the window misses a larger family as soon as it
misses a smaller one. -/
theorem IsDeepR.mono_B {B₀ B : Set (Fin (k + 1) → ℝ)} (hsub : B₀ ⊆ B) {c : Fin k → ℝ}
    {M x : ℝ} (h : IsDeepR B c M x) : IsDeepR B₀ c M x :=
  fun b hb => h b (hsub hb)

/-- `Route.IsDeep` is antitone in the breakpoint family. -/
theorem Route.IsDeep.mono_B {B₀ B : Set (Fin (k + 1) → ℝ)} (hsub : B₀ ⊆ B) {c : Fin k → ℝ}
    {M : ℕ} {x : ℝ} (h : Route.IsDeep B c M x) : Route.IsDeep B₀ c M x :=
  fun b hb => h b (hsub hb)

/-- The cluster exponent set is monotone in the breakpoint family: `B₀ ⊆ B` makes deepness at `B`
strictly stronger, so `ClusterE Y B ⊆ ClusterE Y B₀`. -/
theorem ClusterE_mono {Y : Set (Fin (k + 2) → ℝ)} {B₀ B : Set (Fin (k + 1) → ℝ)}
    (hsub : B₀ ⊆ B) : ClusterE Y B ⊆ ClusterE Y B₀ := by
  intro ρ hρ N hN
  obtain ⟨c, x, hx, hdeep, hrat⟩ := hρ N hN
  exact ⟨c, x, hx, hdeep.mono_B hsub, hrat⟩

/-! ## 2. From a three-point trichotomy for `Gr` to monotonicity of `valY` -/

/-- A three-point "monotone or antitone" trichotomy for the *relation* `Gr` (as produced by
`ulpm_mono_param`) gives `MonotoneOn`/`AntitoneOn` for the value function `valY`, provided the
fibre is a total function on the interval (`GoodFibre`). -/
theorem mono_valY_of_trichotomy {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B)
    (htri : ∀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b →
      x₃ ∈ Set.Ioo a b → x₁ < x₂ → x₂ < x₃ → Gr Y c x₁ y₁ → Gr Y c x₂ y₂ → Gr Y c x₃ y₃ →
      (y₁ ≤ y₂ ∧ y₂ ≤ y₃) ∨ (y₃ ≤ y₂ ∧ y₂ ≤ y₁)) :
    MonotoneOn (valY Y c) (Set.Ioo a b) ∨ AntitoneOn (valY Y c) (Set.Ioo a b) := by
  obtain ⟨hex, -, -⟩ := hgf c a b hab hfree
  refine mono_of_three_point hab fun x₁ x₂ x₃ hx₁ hx₂ hx₃ h12 h23 => ?_
  have h₁ : InD Y c x₁ := (hex x₁ hx₁).exists.imp fun y hy => hy
  have h₂ : InD Y c x₂ := (hex x₂ hx₂).exists.imp fun y hy => hy
  have h₃ : InD Y c x₃ := (hex x₃ hx₃).exists.imp fun y hy => hy
  exact htri x₁ x₂ x₃ _ _ _ hx₁ hx₂ hx₃ h12 h23
    (valY_mem Y c x₁ h₁) (valY_mem Y c x₂ h₂) (valY_mem Y c x₃ h₃)

/-! ## 3. `RatW` for the value ratio -/

/-- Where the fibre is a total nonvanishing continuous function on an interval, the value ratio
satisfies `RatW`. -/
theorem ratW_ratioY {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (h2x : 2 * x ∈ Set.Ioo a b) :
    RatW Y c x (ratioY Y c x) := by
  obtain ⟨hex, hne, -⟩ := hgf c a b hab hfree
  have h₁ : InD Y c x := (hex x hx).exists.imp fun y hy => hy
  have h₂ : InD Y c (2 * x) := (hex (2 * x) h2x).exists.imp fun y hy => hy
  refine ⟨valY Y c x, valY Y c (2 * x), valY_mem Y c x h₁, valY_mem Y c (2 * x) h₂, ?_, ?_⟩
  · exact hne x hx _ (valY_mem Y c x h₁)
  · rw [ratioY]
    field_simp [hne x hx _ (valY_mem Y c x h₁)]

/-! ## 4. `ExpSet E` as a `Finset` -/

/-- `ExpSet E` as a `Finset`, when `E` is finite. -/
theorem expSet_toFinset {E : Set ℝ} (hE : E.Finite) :
    (↑((expSet_finite hE).toFinset) : Set ℚ) = ExpSet E :=
  (expSet_finite hE).coe_toFinset

/-! ## 5. `Y` versus `UlpmTot Y` where `f_c` is nowhere zero -/

/-- Where the fibre of `Y` is defined and nonzero, `UlpmTot Y` has the same value. -/
theorem ulpmTot_eq_of_ne_zero {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x y : ℝ}
    (hy : Gr Y c x y) (hy0 : y ≠ 0) : Gr (UlpmTot Y) c x y :=
  (ulpmTot_gr_iff Y c x y).mpr (Or.inl ⟨hy, hy0⟩)

/-- Conversely, a nonzero value of the fibre of `UlpmTot Y` is a value of the fibre of `Y`. -/
theorem gr_of_ulpmTot_ne_one {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ} {x y : ℝ}
    (hy : Gr (UlpmTot Y) c x y) (hy1 : y ≠ 1) : Gr Y c x y := by
  rcases (ulpmTot_gr_iff Y c x y).mp hy with ⟨hg, -⟩ | ⟨hy_eq, -⟩
  · exact hg
  · exact absurd hy_eq hy1

end Work.WilC4
