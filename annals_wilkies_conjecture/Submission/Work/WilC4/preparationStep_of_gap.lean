/-
  WilC4 : **H4** of the C4 route (`sources/wilkiesC4route/wilkies_C4_route.md` §3):
  the Gap lemma gives the preparation step.

  `PreparationStep` says that for a model `M ⊨ TR`, a `dcl`-closed base `T` and an element
  `a : M`, the values occurring in `V := Dcl T {a}` are generated over `Γ T` by the value of a
  single element.

  Proof (the dichotomy of the route doc §3).  Let `V := Dcl T {a}`.

  * *All values of `V` lie in `Γ T`.*  Then the generator is `δ = 1` (its value is `0`): for
    `y ≠ 0` comparable with `c ∈ V`, the hypothesis gives `c` comparable with some `c' ∈ T \ {0}`,
    and `ValEq y c'` makes `c'⁻¹ y` a unit; `T` is closed under inverses because it is `dcl`-closed.
  * *Some `y₀ ∈ V \ {0}` has a new value.*  Put `b := |y₀| > 0` (the Gap lemma needs a positive
    element; `b` has the same value as `y₀`).  Then `b ∈ V` and `b ∉ T`; since `b ∈ V = Dcl T {a}`,
    Steinitz exchange (`WilC2.dcl_exchange`) yields `a ∈ Dcl T {b}`, so `Dcl T {a} ⊆ Dcl T {b}`
    (an element definable over `T` may be absorbed as a parameter).  The Gap lemma at `b` then
    says that for every nonzero `z ∈ Dcl T {b}` there are `p : ℤ`, `n > 0` and `α ∈ T \ {0}` with
    `z^n/(α b^p)` a unit; replacing `z` by any `y` in the same Archimedean class gives the spanning
    with the single generator `b`, and `ValSpans` is monotone in the spanned set.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC4.dcl_neg
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.valEq_refl
import Submission.Work.WilC4.valEq_symm
import Submission.Work.WilC4.valEq_trans
import Submission.Work.WilC4.valEq_iff_unitVal_div
import Submission.Work.WilC4.valSpans_mono_V
import Submission.Work.WilC4.valSpans_self_zero
import Submission.Work.WilC4.isUnitVal_of_valEq_mul_pow_div

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language

namespace Work.WilC4

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-! ## 1. The two formulations of the definable closure -/

/-- `Dcl S A` (singletons as constant `Fin 1`-tuples) is the `WilC2` definable closure of the
parameter set `S ∪ A` (singletons as `Set.Definable₁`). -/
lemma dcl_eq_wilC2 (S A : Set M) : Dcl S A = Work.WilC2.Dcl (S ∪ A) := by
  have h : Dcl S A = Dcl (∅ : Set M) (S ∪ A) := by
    ext x
    simp only [Dcl, DefinableElt, Set.empty_union]
  rw [h]
  exact Work.WilC2.dcl_eq_WilC4 (S ∪ A)

/-- A `dcl`-closed set is fixed by the `WilC2` definable closure. -/
lemma wilC2_dcl_eq_self {T : Set M} (hT : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) :
    Work.WilC2.Dcl T = T := by
  rw [← Work.WilC2.dcl_eq_WilC4 T]
  have h : Dcl (∅ : Set M) T = Dcl T (∅ : Set M) := by
    ext x
    simp only [Dcl, DefinableElt, Set.empty_union, Set.union_empty]
  rw [h]
  ext x
  exact hT x

/-- Elements of a `dcl`-closed set have inverses in it. -/
lemma inv_mem_of_dcl_closed {T : Set M} (hT : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T)
    {x : M} (hx : x ∈ T) (hx0 : x ≠ 0) : x⁻¹ ∈ T :=
  (hT x⁻¹).mp (dcl_inv ((hT x).mpr hx) hx0)

/-- **Absorption of a definable extra parameter.**  If `a` is definable from `T ∪ {b}` then
`Dcl T {a} ⊆ Dcl T {b}`: the parameter `a` may be replaced by its definition over `T ∪ {b}`. -/
lemma dcl_singleton_subset_of_mem {T : Set M} {a b : M}
    (h : a ∈ Dcl T {b}) : Dcl T {a} ⊆ Dcl T {b} := by
  have h' : a ∈ Work.WilC2.Dcl (T ∪ {b}) := by
    rwa [dcl_eq_wilC2 T {b}] at h
  have hmain : Work.WilC2.Dcl (T ∪ {a}) ⊆ Work.WilC2.Dcl (T ∪ {b}) := by
    calc Work.WilC2.Dcl (T ∪ {a})
        ⊆ Work.WilC2.Dcl (Work.WilC2.Dcl (T ∪ {b})) := by
          apply Work.WilC2.dcl_mono
          intro z hz
          rcases hz with hz | hz
          · exact Work.WilC2.subset_dcl_aux (T ∪ {b}) (Or.inl hz)
          · rw [Set.mem_singleton_iff] at hz
            subst hz
            exact h'
      _ = Work.WilC2.Dcl (T ∪ {b}) := Work.WilC2.dcl_idem (T ∪ {b})
  rw [dcl_eq_wilC2 T {a}, dcl_eq_wilC2 T {b}]
  exact hmain

/-! ## 2. The Archimedean class of `|x|` -/

/-- `x` and `-x` are comparable. -/
lemma valEq_neg_self {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x : M} :
    ValEq x (-x) := ⟨1, Nat.one_pos, by simp, by simp⟩

/-- `|x|` and `x` are comparable: the absolute value only changes the sign. -/
lemma valEq_abs_iff {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x y : M} :
    ValEq |x| y ↔ ValEq x y := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx]
    constructor
    · intro h; exact valEq_trans valEq_neg_self h
    · intro h; exact valEq_trans (valEq_symm valEq_neg_self) h

/-! ## 3. The Gap lemma gives a spanning generator -/

/-- The Gap lemma at `b` yields the spanning of the values of `Dcl T {b}` by the single value
`ν b`.  The Gap lemma produces, for `z ∈ Dcl T {b}`, `z ≠ 0`, a relation
`IsUnitVal (z^n / (α * b^p))` with `α ∈ T`; writing it as `α⁻¹ * z^n / b^p` gives exactly the
spanning expression, and any `y` comparable with `z` is handled by
`isUnitVal_of_valEq_mul_pow_div`. -/
lemma valSpans_of_gapLemma {T : Set M} (hTinv : ∀ x ∈ T, x ≠ 0 → x⁻¹ ∈ T) {b : M}
    (hgap : ∀ z ∈ Dcl T {b}, z ≠ 0 →
      ∃ (p : ℤ) (n : ℕ), 0 < n ∧ ∃ α ∈ T, α ≠ 0 ∧ IsUnitVal (z ^ n / (α * b ^ p))) :
    ValSpans T (Dcl T {b}) 1 := by
  refine ⟨(fun _ : Fin 1 => b), ?_⟩
  intro y hy0 hyV
  obtain ⟨c, hcV, hc0, hcy⟩ := hyV
  obtain ⟨p, n, hn, α, hαT, hα0, hunit⟩ := hgap c hcV hc0
  refine ⟨n, hn.ne', (fun _ : Fin 1 => p), α⁻¹, hTinv α hαT hα0, inv_ne_zero hα0, ?_⟩
  have hmono : zmono (fun _ : Fin 1 => b) (fun _ : Fin 1 => p) = b ^ p := by simp [zmono]
  rw [hmono]
  have hunit' : IsUnitVal (α⁻¹ * c ^ n / b ^ p) := by
    have hcast : α⁻¹ * c ^ n / b ^ p = c ^ n / (α * b ^ p) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring
    rw [hcast]; exact hunit
  exact isUnitVal_of_valEq_mul_pow_div hc0 hcy hunit'

/-! ## 4. H4 -/

theorem preparationStep_of_gap
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    (hG : ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
      [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
      [(FirstOrder.Language.constantsOn ℝ).Structure M],
      M ⊨ WilkiesDesign.CG.TR → Work.WilC4.Route.GapLemma M) :
    Work.WilC4.PreparationStep := by
  intro M i1 i2 i3 i4 i5 i6 hM T hTdcl a
  haveI : M ⊨ WilkiesDesign.CG.TR := hM
  have hTinv : ∀ x ∈ T, x ≠ 0 → x⁻¹ ∈ T := fun x hx hx0 =>
    inv_mem_of_dcl_closed hTdcl hx hx0
  by_cases hcase : ∀ y ∈ Dcl T {a}, y ≠ 0 → ValOf T y
  · -- every value of `Dcl T {a}` already lies in `Γ T`: the generator is `1`
    refine ⟨1, one_ne_zero, (fun _ : Fin 1 => (1 : M)), ?_⟩
    intro y hy0 hyV
    obtain ⟨c, hcV, hc0, hcy⟩ := hyV
    obtain ⟨c', hc'T, hc'0, hc'eq⟩ := hcase c hcV hc0
    refine ⟨1, one_ne_zero, (fun _ : Fin 1 => (0 : ℤ)), c'⁻¹, hTinv c' hc'T hc'0,
      inv_ne_zero hc'0, ?_⟩
    have hmono : zmono (fun _ : Fin 1 => (1 : M)) (fun _ : Fin 1 => (0 : ℤ)) = 1 := by
      simp [zmono]
    rw [hmono, pow_one, div_one]
    have hcomm : c'⁻¹ * y = y / c' := by rw [div_eq_mul_inv, mul_comm]
    rw [hcomm]
    exact isUnitVal_div_of_valEq hc'0 (valEq_trans hcy hc'eq)
  · -- some `y₀ ∈ Dcl T {a}` has a value outside `Γ T`: use the Gap lemma at `|y₀|`
    push Not at hcase
    obtain ⟨y₀, hy₀V, hy₀0, hy₀notV⟩ := hcase
    have hbpos : 0 < |y₀| := abs_pos.mpr hy₀0
    have hnotValOf : ¬ ValOf T |y₀| := by
      rintro ⟨c, hcT, hc0, hceq⟩
      exact hy₀notV ⟨c, hcT, hc0, (valEq_abs_iff (x := y₀) (y := c)).mp hceq⟩
    have hbV : |y₀| ∈ Dcl T {a} := by
      rcases le_total 0 y₀ with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_nonpos h]
        exact dcl_neg hy₀V
    have hnotT : |y₀| ∉ T := fun hT =>
      hnotValOf ⟨|y₀|, hT, abs_ne_zero.mpr hy₀0, valEq_refl |y₀|⟩
    have hb_wc2 : |y₀| ∈ Work.WilC2.Dcl (insert a T) := by
      have h := hbV
      rw [dcl_eq_wilC2 T {a}, Set.union_singleton] at h
      exact h
    have hb_not_wc2 : |y₀| ∉ Work.WilC2.Dcl T := by
      intro h
      exact hnotT (by rwa [wilC2_dcl_eq_self hTdcl] at h)
    have hex : a ∈ Work.WilC2.Dcl (insert |y₀| T) :=
      Work.WilC2.dcl_exchange hR hC0 hUF T hb_wc2 hb_not_wc2
    have ha_dcl : a ∈ Dcl T {|y₀|} := by
      rw [dcl_eq_wilC2 T {|y₀|}, Set.union_singleton]
      exact hex
    have hdcleq : Dcl T {a} ⊆ Dcl T {|y₀|} := dcl_singleton_subset_of_mem ha_dcl
    have hgap := hG M hM T hTdcl |y₀| hbpos
      (fun c hcT hc0 hceq => hnotValOf ⟨c, hcT, hc0, hceq⟩)
    exact ⟨|y₀|, abs_ne_zero.mpr hy₀0,
      valSpans_mono_V hdcleq (valSpans_of_gapLemma hTinv hgap)⟩

end Work.WilC4
