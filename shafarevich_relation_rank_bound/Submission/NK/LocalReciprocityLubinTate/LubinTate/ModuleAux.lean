import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Setup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Step
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_solution

/-!
# The `R`-module structure of a Lubin–Tate formal group: the underlying series

Milne, *Classical Field Theory*, §I.1: given a Lubin–Tate series `f` for `(π, q)` over `A`, one
obtains

* the **Lubin–Tate group law** `F` — the unique `F ∈ A⟦X,Y⟧` with `F ≡ X + Y (mod deg 2)` and
  `f(F(X,Y)) = F(f(X),f(Y))` (Milne's Proposition I.2.12), obtained here by one application of
  `existsUnique_lubinTate_solution` (Milne's Lemma I.2.11);
* for every `a ∈ A` the **`a`-multiplication series** `[a]`, the unique `φ ∈ A⟦X⟧` with
  `φ ≡ aX (mod deg 2)` and `f ∘ φ = φ ∘ f` — for `a = π` this is `f` itself.

This file contains the definitions and their immediately defining properties.  The group-law axioms
for `F` and the module axioms for `a ↦ [a]` are proved in the files that import this one.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

noncomputable section

variable {A : Type u} [CommRing A] {π : A} {q : ℕ} {f : MvPowerSeries (Fin 1) A}

/-- The linear form `c X` in one variable. -/
def linForm1 (c : A) : MvPowerSeries (Fin 1) A := MvPowerSeries.C c * MvPowerSeries.X 0

/-- The linear form `a X + b Y` in two variables. -/
def linForm2 (a b : A) : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.C a * MvPowerSeries.X 0 + MvPowerSeries.C b * MvPowerSeries.X 1

theorem linForm1_cond (c : A) :
    (linForm1 c).constantCoeff = 0 ∧
      ∀ s : Fin 1 →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s (linForm1 c) = 0 := by
  constructor
  · simp [linForm1]
  · intro s hs
    rw [linForm1, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    have hne : s ≠ Finsupp.single (0 : Fin 1) 1 := by
      intro h
      rw [h] at hs
      simp [Finsupp.degree_single] at hs
    rw [if_neg hne, mul_zero]

theorem linForm2_cond (a b : A) :
    (linForm2 a b).constantCoeff = 0 ∧
      ∀ s : Fin 2 →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s (linForm2 a b) = 0 := by
  constructor
  · simp [linForm2]
  · intro s hs
    have h0 : MvPowerSeries.coeff s (MvPowerSeries.C a * MvPowerSeries.X 0) = 0 := by
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      have hne : s ≠ Finsupp.single (0 : Fin 2) 1 := by
        intro h
        rw [h] at hs
        simp [Finsupp.degree_single] at hs
      rw [if_neg hne, mul_zero]
    have h1 : MvPowerSeries.coeff s (MvPowerSeries.C b * MvPowerSeries.X 1) = 0 := by
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
      have hne : s ≠ Finsupp.single (1 : Fin 2) 1 := by
        intro h
        rw [h] at hs
        simp [Finsupp.degree_single] at hs
      rw [if_neg hne, mul_zero]
    rw [linForm2, map_add, h0, h1, add_zero]

/-- The unique existence statement produced by Milne's Lemma I.2.11 for `f = g`. -/
theorem existsUnique_mulSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) :
    ∃! φ : MvPowerSeries (Fin 1) A,
      (∀ s : Fin 1 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
        = MvPowerSeries.coeff s (linForm1 c)) ∧
      MvPowerSeries.subst ![φ] f = φ.subst (gSub 1 f) :=
  existsUnique_lubinTate_solution hπ hpow hf hf (linForm1 c) (linForm1_cond c)

theorem existsUnique_lawSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    ∃! φ : MvPowerSeries (Fin 2) A,
      (∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
        = MvPowerSeries.coeff s (linForm2 1 1)) ∧
      MvPowerSeries.subst ![φ] f = φ.subst (gSub 2 f) :=
  existsUnique_lubinTate_solution hπ hpow hf hf (linForm2 1 1) (linForm2_cond 1 1)

/-- **The `c`-multiplication series** `[c]`: the unique `φ` with `φ ≡ cX (mod deg 2)` and
`f ∘ φ = φ ∘ f`. -/
noncomputable def mulSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) : MvPowerSeries (Fin 1) A :=
  Classical.choose (existsUnique_mulSeries hπ hpow hf c)

/-- **The Lubin–Tate group law** `F`: the unique `F` with `F ≡ X + Y (mod deg 2)` and
`f(F(X,Y)) = F(f(X),f(Y))`. -/
noncomputable def lawSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : MvPowerSeries (Fin 2) A :=
  Classical.choose (existsUnique_lawSeries hπ hpow hf)

variable {hπ : IsLubinTateCoeff π q} {hpow : IsFrobeniusPower π q} {hf : IsLubinTateSeries π q f}

theorem mulSeries_lin (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) {s : Fin 1 →₀ ℕ} (hs : s.degree ≤ 1) :
    MvPowerSeries.coeff s (mulSeries hπ hpow hf c) = MvPowerSeries.coeff s (linForm1 c) :=
  (Classical.choose_spec (existsUnique_mulSeries hπ hpow hf c)).1.1 s hs

theorem mulSeries_comm (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) :
    MvPowerSeries.subst ![mulSeries hπ hpow hf c] f
      = (mulSeries hπ hpow hf c).subst (gSub 1 f) :=
  (Classical.choose_spec (existsUnique_mulSeries hπ hpow hf c)).1.2

theorem lawSeries_lin (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {s : Fin 2 →₀ ℕ} (hs : s.degree ≤ 1) :
    MvPowerSeries.coeff s (lawSeries hπ hpow hf) = MvPowerSeries.coeff s (linForm2 1 1) :=
  (Classical.choose_spec (existsUnique_lawSeries hπ hpow hf)).1.1 s hs

/-- The equation defining the group law: `f ∘ F = F(f(X),f(Y))`. -/
theorem lawSeries_spec (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    MvPowerSeries.subst ![lawSeries hπ hpow hf] f
      = (lawSeries hπ hpow hf).subst (gSub 2 f) :=
  (Classical.choose_spec (existsUnique_lawSeries hπ hpow hf)).1.2

theorem mulSeries_unique (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {c : A} {φ : MvPowerSeries (Fin 1) A}
    (hlin : ∀ s : Fin 1 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
      = MvPowerSeries.coeff s (linForm1 c))
    (heq : MvPowerSeries.subst ![φ] f = φ.subst (gSub 1 f)) :
    φ = mulSeries hπ hpow hf c :=
  ExistsUnique.unique (existsUnique_mulSeries hπ hpow hf c) ⟨hlin, heq⟩
    (Classical.choose_spec (existsUnique_mulSeries hπ hpow hf c)).1

theorem lawSeries_unique (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {φ : MvPowerSeries (Fin 2) A}
    (hlin : ∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
      = MvPowerSeries.coeff s (linForm2 1 1))
    (heq : MvPowerSeries.subst ![φ] f = φ.subst (gSub 2 f)) :
    φ = lawSeries hπ hpow hf :=
  ExistsUnique.unique (existsUnique_lawSeries hπ hpow hf) ⟨hlin, heq⟩
    (Classical.choose_spec (existsUnique_lawSeries hπ hpow hf)).1

theorem mulSeries_unique' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {c : A} {φ : MvPowerSeries (Fin 1) A}
    (hlin : OrderGe 2 (φ - linForm1 c))
    (heq : MvPowerSeries.subst ![φ] f = φ.subst (gSub 1 f)) :
    φ = mulSeries hπ hpow hf c :=
  mulSeries_unique hπ hpow hf (fun s hs => (orderGe_sub_iff.mp hlin) s (by omega)) heq

theorem lawSeries_unique' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {φ : MvPowerSeries (Fin 2) A}
    (hlin : OrderGe 2 (φ - linForm2 1 1))
    (heq : MvPowerSeries.subst ![φ] f = φ.subst (gSub 2 f)) :
    φ = lawSeries hπ hpow hf :=
  lawSeries_unique hπ hpow hf (fun s hs => (orderGe_sub_iff.mp hlin) s (by omega)) heq

theorem mulSeries_constantCoeff (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) : (mulSeries hπ hpow hf c).constantCoeff = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mulSeries_lin hπ hpow hf c (by simp)]
  simp [linForm1]

theorem mulSeries_orderGe_one (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) : OrderGe 1 (mulSeries hπ hpow hf c) :=
  OrderGe.of_constantCoeff (mulSeries_constantCoeff hπ hpow hf c)

theorem mulSeries_orderGe_two (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) :
    OrderGe 2 (mulSeries hπ hpow hf c - linForm1 c) :=
  orderGe_sub_iff.mpr fun s hs => mulSeries_lin hπ hpow hf c (by omega)

theorem lawSeries_constantCoeff (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : (lawSeries hπ hpow hf).constantCoeff = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lawSeries_lin hπ hpow hf (by simp)]
  simp [linForm2]

theorem lawSeries_orderGe_one (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : OrderGe 1 (lawSeries hπ hpow hf) :=
  OrderGe.of_constantCoeff (lawSeries_constantCoeff hπ hpow hf)

theorem lawSeries_orderGe_two (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    OrderGe 2 (lawSeries hπ hpow hf - linForm2 1 1) :=
  orderGe_sub_iff.mpr fun s hs => lawSeries_lin hπ hpow hf (by omega)

/-- `gSub 1 f` is the constant family `f`. -/
theorem gSub_one_eq : gSub 1 f = ![f] := by
  funext i
  fin_cases i
  show MvPowerSeries.subst (![MvPowerSeries.X 0] : Fin 1 → MvPowerSeries (Fin 1) A) f = f
  have h : (![MvPowerSeries.X 0] : Fin 1 → MvPowerSeries (Fin 1) A) = MvPowerSeries.X := by
    funext j
    fin_cases j
    rfl
  rw [h]
  exact congr_fun (MvPowerSeries.subst_self (R := A) (σ := Fin 1)) f

/-- `gSub 2 f` is the family `(f(X₀), f(X₁))`. -/
theorem gSub_two_eq :
    gSub 2 f = ![MvPowerSeries.subst ![MvPowerSeries.X (0 : Fin 2)] f,
      MvPowerSeries.subst ![MvPowerSeries.X (1 : Fin 2)] f] := by
  funext i
  fin_cases i <;> rfl

/-- The equation defining the group law, in the `IsEndoSeries` form of `Series.lean`. -/
theorem lawSeries_isEndoSeries (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) : IsEndoSeries (lawSeries hπ hpow hf) f := by
  rw [IsEndoSeries, ← gSub_two_eq]
  exact lawSeries_spec hπ hpow hf

/-! ### The substitution calculus: `subst1` and `subst2` -/

/-- Substitute a single series `g` for the variable of a one-variable series `φ`. -/
def subst1 {τ : Type*} (g : MvPowerSeries τ A) (φ : MvPowerSeries (Fin 1) A) :
    MvPowerSeries τ A :=
  MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) φ

/-- Substitute two series `g₀, g₁` for the two variables of a two-variable series `F`. -/
def subst2 {τ : Type*} (g₀ g₁ : MvPowerSeries τ A) (F : MvPowerSeries (Fin 2) A) :
    MvPowerSeries τ A :=
  MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) F

theorem subst1_apply {τ : Type*} (g : MvPowerSeries τ A) (φ : MvPowerSeries (Fin 1) A) :
    subst1 g φ = MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) φ := rfl

theorem subst2_apply {τ : Type*} (g₀ g₁ : MvPowerSeries τ A) (F : MvPowerSeries (Fin 2) A) :
    subst2 g₀ g₁ F = MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) F := rfl

theorem hasSubst_vec1 {τ : Type*} {g : MvPowerSeries τ A} (hg : g.constantCoeff = 0) :
    MvPowerSeries.HasSubst (![g] : Fin 1 → MvPowerSeries τ A) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i; exact hg

theorem hasSubst_vec2 {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    (h₀ : g₀.constantCoeff = 0) (h₁ : g₁.constantCoeff = 0) :
    MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i
    · exact h₀
    · exact h₁

/-- **Linear part of a one-variable substitution**: if `h ≡ tX (mod deg 2)` and `g` has positive
order, then `h(g) ≡ t·g (mod deg 2)`. -/
theorem coeff_subst_one_linear {τ : Type*} {t : A} {h : MvPowerSeries (Fin 1) A}
    (hlin : OrderGe 2 (h - linForm1 t)) {g : MvPowerSeries τ A} (hg : OrderGe 1 g)
    {e : τ →₀ ℕ} (he : e.degree < 2) :
    MvPowerSeries.coeff e (subst1 g h)
      = t * MvPowerSeries.coeff e g := by
  rw [subst1]
  have hsub : MvPowerSeries.HasSubst (![g] : Fin 1 → MvPowerSeries τ A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i; exact OrderGe.constantCoeff hg
  have hX : MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) (linForm1 t)
      = MvPowerSeries.C t * g := by
    rw [linForm1, MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_C,
      MvPowerSeries.subst_X hsub]
    rfl
  have hzero : MvPowerSeries.coeff e
      (MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) (h - linForm1 t)) = 0 :=
    OrderGe.subst (fun i => by fin_cases i; exact hg) hlin e he
  have hsum : MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) h
      = MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) (linForm1 t)
        + MvPowerSeries.subst (![g] : Fin 1 → MvPowerSeries τ A) (h - linForm1 t) := by
    rw [← MvPowerSeries.subst_add hsub]
    congr 1
    ring
  rw [hsum, map_add, hX, MvPowerSeries.coeff_C_mul, hzero, add_zero]

/-- **Linear part of a two-variable substitution**: if `F ≡ s₀X + s₁Y (mod deg 2)` and `g₀, g₁`
have positive order, then `F(g₀,g₁) ≡ s₀g₀ + s₁g₁ (mod deg 2)`. -/
theorem coeff_subst_two_linear {τ : Type*} {F : MvPowerSeries (Fin 2) A} {s₀ s₁ : A}
    (hF : OrderGe 2 (F - linForm2 s₀ s₁)) {g₀ g₁ : MvPowerSeries τ A}
    (h₀ : OrderGe 1 g₀) (h₁ : OrderGe 1 g₁) {e : τ →₀ ℕ} (he : e.degree < 2) :
    MvPowerSeries.coeff e (subst2 g₀ g₁ F)
      = s₀ * MvPowerSeries.coeff e g₀ + s₁ * MvPowerSeries.coeff e g₁ := by
  rw [subst2]
  have hsub : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i
      · exact OrderGe.constantCoeff h₀
      · exact OrderGe.constantCoeff h₁
  have hX : MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) (linForm2 s₀ s₁)
      = MvPowerSeries.C s₀ * g₀ + MvPowerSeries.C s₁ * g₁ := by
    rw [linForm2, MvPowerSeries.subst_add hsub, MvPowerSeries.subst_mul hsub,
      MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_C, MvPowerSeries.subst_C,
      MvPowerSeries.subst_X hsub, MvPowerSeries.subst_X hsub]
    simp
  have hzero : MvPowerSeries.coeff e
      (MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) (F - linForm2 s₀ s₁)) = 0 :=
    OrderGe.subst (fun i => by fin_cases i; exact h₀; exact h₁) hF e he
  have hsum : MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) F
      = MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) (linForm2 s₀ s₁)
        + MvPowerSeries.subst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A) (F - linForm2 s₀ s₁) := by
    rw [← MvPowerSeries.subst_add hsub]
    congr 1
    ring
  rw [hsum, map_add, hX, hzero, add_zero, map_add, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_C_mul]

/-- The one-variable case of `coeff_subst_two_linear`. -/
theorem coeff_subst_one_linear' {τ : Type*} {t : A} {h : MvPowerSeries (Fin 1) A}
    (hlin : OrderGe 2 (h - linForm1 t)) {g : MvPowerSeries τ A} (hg : OrderGe 1 g)
    {e : τ →₀ ℕ} (he : e.degree < 2) :
    MvPowerSeries.coeff e (subst1 g h) = t * MvPowerSeries.coeff e g :=
  coeff_subst_one_linear hlin hg he

/-- Coefficients of the one-variable linear form. -/
theorem coeff_linForm1 (c : A) (s : Fin 1 →₀ ℕ) :
    MvPowerSeries.coeff s (linForm1 c)
      = c * (if s = Finsupp.single (0 : Fin 1) 1 then 1 else 0) := by
  rw [linForm1, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]

/-- Coefficients of the two-variable linear form. -/
theorem coeff_linForm2 (a b : A) (s : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff s (linForm2 a b)
      = a * (if s = Finsupp.single (0 : Fin 2) 1 then 1 else 0)
        + b * (if s = Finsupp.single (1 : Fin 2) 1 then 1 else 0) := by
  rw [linForm2, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]

/-- The two-variable version of Milne's Lemma I.2.11 for the linear form `aX + bY`. -/
theorem existsUnique_lawSeries2 (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (a b : A) :
    ∃! φ : MvPowerSeries (Fin 2) A,
      (∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
        = MvPowerSeries.coeff s (linForm2 a b)) ∧
      MvPowerSeries.subst ![φ] f = φ.subst (gSub 2 f) :=
  existsUnique_lubinTate_solution hπ hpow hf hf (linForm2 a b) (linForm2_cond a b)

/-- The one-variable version of Milne's Lemma I.2.11 for the linear form `cX` (restated). -/
theorem existsUnique_mulSeries' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) :
    ∃! φ : MvPowerSeries (Fin 1) A,
      (∀ s : Fin 1 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
        = MvPowerSeries.coeff s (linForm1 c)) ∧
      MvPowerSeries.subst ![φ] f = φ.subst (gSub 1 f) :=
  existsUnique_mulSeries hπ hpow hf c


theorem subst1_congr {τ : Type*} {g : MvPowerSeries τ A} {φ ψ : MvPowerSeries (Fin 1) A}
    (h : φ = ψ) : subst1 g φ = subst1 g ψ := by rw [h]

theorem subst2_congr {τ : Type*} {g₀ g₁ : MvPowerSeries τ A} {F G : MvPowerSeries (Fin 2) A}
    (h : F = G) : subst2 g₀ g₁ F = subst2 g₀ g₁ G := by rw [h]

/-- Substituting the variable itself is the identity. -/
theorem subst1_X {φ : MvPowerSeries (Fin 1) A} : subst1 (MvPowerSeries.X 0) φ = φ := by
  rw [subst1]
  have h : (![MvPowerSeries.X 0] : Fin 1 → MvPowerSeries (Fin 1) A) = MvPowerSeries.X := by
    funext i
    fin_cases i
    rfl
  rw [h]
  exact congr_fun (MvPowerSeries.subst_self (R := A) (σ := Fin 1)) φ

/-- Substituting the variables themselves is the identity. -/
theorem subst2_X {F : MvPowerSeries (Fin 2) A} :
    subst2 (MvPowerSeries.X 0) (MvPowerSeries.X 1) F = F := by
  rw [subst2]
  have h : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X (1 : Fin 2)] :
      Fin 2 → MvPowerSeries (Fin 2) A) = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact congr_fun (MvPowerSeries.subst_self (R := A) (σ := Fin 2)) F

/-- The one-variable commutation of `[c]` with `f`, in `subst1` form. -/
theorem mulSeries_comm_subst1 (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (c : A) :
    subst1 (mulSeries hπ hpow hf c) f = subst1 f (mulSeries hπ hpow hf c) := by
  have h := mulSeries_comm hπ hpow hf c
  rw [gSub_one_eq] at h
  rw [subst1, subst1, h]

/-- The defining equation of the group law in the `subst1`/`subst2` form. -/
theorem lawSeries_isEndoSeries' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) :
    subst1 (lawSeries hπ hpow hf) f
      = subst2 (subst1 (MvPowerSeries.X 0) f) (subst1 (MvPowerSeries.X 1) f)
          (lawSeries hπ hpow hf) :=
  lawSeries_isEndoSeries hπ hpow hf

/-- Scaling the one-variable linear form. -/
theorem coeff_linForm1_smul (a t : A) (e : Fin 1 →₀ ℕ) :
    MvPowerSeries.coeff e (linForm1 (a * t)) = a * MvPowerSeries.coeff e (linForm1 t) := by
  rw [coeff_linForm1, coeff_linForm1, mul_assoc]

/-- Scaling the two-variable linear form. -/
theorem coeff_linForm2_smul (a s₀ s₁ : A) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (linForm2 (a * s₀) (a * s₁))
      = a * MvPowerSeries.coeff e (linForm2 s₀ s₁) := by
  rw [coeff_linForm2, coeff_linForm2]
  rw [mul_add, mul_assoc, mul_assoc]


/-! ### Composition lemmas for `subst1` and `subst2` -/

/-- Composition of a one-variable series on the right: `H(f ∘ g) = (H(f))(g)`. -/
theorem subst1_comp {σ : Type*} {H : MvPowerSeries σ A} {g h : MvPowerSeries (Fin 1) A}
    (ha : MvPowerSeries.HasSubst (![g] : Fin 1 → MvPowerSeries (Fin 1) A))
    (hb : MvPowerSeries.HasSubst (![H] : Fin 1 → MvPowerSeries σ A)) :
    subst1 H (subst1 g h) = subst1 (subst1 H g) h := by
  rw [subst1, subst1, subst1, MvPowerSeries.subst_comp_subst_apply (ha := ha) (hb := hb)]
  congr 1
  funext i
  fin_cases i
  rfl

/-- Substituting into the two variables of a composite. -/
theorem subst2_subst1_comp {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    {F : MvPowerSeries (Fin 2) A} {φ : MvPowerSeries (Fin 1) A}
    (ha : MvPowerSeries.HasSubst (![F] : Fin 1 → MvPowerSeries (Fin 2) A))
    (hb : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A)) :
    subst2 g₀ g₁ (subst1 F φ) = subst1 (subst2 g₀ g₁ F) φ := by
  rw [subst1, subst2, subst1, MvPowerSeries.subst_comp_subst_apply (ha := ha) (hb := hb)]
  congr 1
  funext i
  fin_cases i
  rfl

/-- Substitution of a family into a composite of two-variable series. -/
theorem subst2_subst2_comp {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    {h₀ h₁ : MvPowerSeries (Fin 2) A} {F : MvPowerSeries (Fin 2) A}
    (ha : MvPowerSeries.HasSubst (![h₀, h₁] : Fin 2 → MvPowerSeries (Fin 2) A))
    (hb : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A)) :
    subst2 g₀ g₁ (subst2 h₀ h₁ F) = subst2 (subst2 g₀ g₁ h₀) (subst2 g₀ g₁ h₁) F := by
  rw [subst2, subst2, subst2, subst2,
    MvPowerSeries.subst_comp_subst_apply (ha := ha) (hb := hb)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Substituting a one-variable series into both entries of a substitution. -/
theorem subst1_subst2_comp {g₀ g₁ h : MvPowerSeries (Fin 1) A} {F : MvPowerSeries (Fin 2) A}
    (ha : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries (Fin 1) A))
    (hb : MvPowerSeries.HasSubst (![h] : Fin 1 → MvPowerSeries (Fin 1) A)) :
    subst1 h (subst2 g₀ g₁ F) = subst2 (subst1 h g₀) (subst1 h g₁) F := by
  rw [subst1, subst2, subst1, MvPowerSeries.subst_comp_subst_apply (ha := ha) (hb := hb)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem subst2_X0 {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    (h : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A)) :
    subst2 g₀ g₁ (MvPowerSeries.X 0) = g₀ := by
  rw [subst2, MvPowerSeries.subst_X h]
  rfl

theorem subst2_X1 {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    (h : MvPowerSeries.HasSubst (![g₀, g₁] : Fin 2 → MvPowerSeries τ A)) :
    subst2 g₀ g₁ (MvPowerSeries.X 1) = g₁ := by
  rw [subst2, MvPowerSeries.subst_X h]
  rfl

theorem subst1_constantCoeff {τ : Type*} {g : MvPowerSeries τ A} {φ : MvPowerSeries (Fin 1) A}
    (hg : g.constantCoeff = 0) (hφ : φ.constantCoeff = 0) : (subst1 g φ).constantCoeff = 0 := by
  rw [subst1]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_vec1 hg) (fun i => by
    fin_cases i; exact hg) hφ

theorem subst2_constantCoeff {τ : Type*} {g₀ g₁ : MvPowerSeries τ A}
    {F : MvPowerSeries (Fin 2) A} (h₀ : g₀.constantCoeff = 0) (h₁ : g₁.constantCoeff = 0)
    (hF : F.constantCoeff = 0) : (subst2 g₀ g₁ F).constantCoeff = 0 := by
  rw [subst2]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_vec2 h₀ h₁) (fun i => by
    fin_cases i
    · exact h₀
    · exact h₁) hF


/-- `linForm2 1 1` is the linear form `X + Y`. -/
theorem linForm2_one :
    linForm2 (1 : A) 1 = (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) := by
  rw [linForm2, map_one, one_mul, one_mul]

/-- `linForm1 1` is the variable `X`. -/
theorem linForm1_one : linForm1 (1 : A) = (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) A) := by
  rw [linForm1, map_one, one_mul]

/-- `linForm1 0` is zero. -/
theorem linForm1_zero : linForm1 (0 : A) = (0 : MvPowerSeries (Fin 1) A) := by
  rw [linForm1, map_zero, zero_mul]

/-- `f - πX` has order `≥ 2` for a Lubin–Tate series `f`. -/
theorem orderGe_two_sub_linForm1 (hf : IsLubinTateSeries π q f) :
    OrderGe 2 (f - linForm1 π) := by
  have h := orderGe_two_sub_C_mul_X hf.1 hf.2.1
  rwa [show MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1) = linForm1 π from rfl] at h

/-- Substituting a one-variable series into the variable `X` returns that series. -/
theorem subst1_self {τ : Type*} {g : MvPowerSeries τ A}
    (h : MvPowerSeries.HasSubst (![g] : Fin 1 → MvPowerSeries τ A)) :
    subst1 g (MvPowerSeries.X (0 : Fin 1)) = g := by
  rw [subst1, MvPowerSeries.subst_X h]
  rfl



/-- The defining equation of an endomorphism of the group law, in `subst1`/`subst2` form. -/
theorem isEndoSeries_iff_subst1_subst2 {L : MvPowerSeries (Fin 2) A} :
    IsEndoSeries L f ↔
      subst1 L f = subst2 (subst1 (MvPowerSeries.X 0) f) (subst1 (MvPowerSeries.X 1) f) L := by
  rw [IsEndoSeries]
  exact Iff.rfl

/-- One-variable commutation with `f`, in `subst1` form. -/
theorem commS_iff_subst1 {φ : MvPowerSeries (Fin 1) A} :
    (MvPowerSeries.subst ![φ] f = φ.subst (gSub 1 f)) ↔ subst1 φ f = subst1 f φ := by
  rw [gSub_one_eq]
  exact Iff.rfl

/-- Additivity of the coefficients of the linear form. -/
theorem coeff_linForm1_add (a b : A) (e : Fin 1 →₀ ℕ) :
    MvPowerSeries.coeff e (linForm1 (a + b))
      = MvPowerSeries.coeff e (linForm1 a) + MvPowerSeries.coeff e (linForm1 b) := by
  rw [coeff_linForm1, coeff_linForm1, coeff_linForm1, add_mul]



/-- Substituting a family of positive order into the zero series gives zero. -/
theorem subst1_zero {τ : Type*} {g : MvPowerSeries τ A}
    (h : MvPowerSeries.HasSubst (![g] : Fin 1 → MvPowerSeries τ A)) :
    subst1 g (0 : MvPowerSeries (Fin 1) A) = 0 := by
  rw [subst1, ← MvPowerSeries.substAlgHom_apply (f := (0 : MvPowerSeries (Fin 1) A)) h, map_zero]

/-- Substituting the zero series into a series of positive order gives zero. -/
theorem subst1_zero_fam {φ : MvPowerSeries (Fin 1) A} (hφ : φ.constantCoeff = 0) :
    subst1 (0 : MvPowerSeries (Fin 1) A) φ = 0 := by
  rw [subst1,
    show (![(0 : MvPowerSeries (Fin 1) A)] : Fin 1 → MvPowerSeries (Fin 1) A)
      = (0 : Fin 1 → MvPowerSeries (Fin 1) A) from by funext i; fin_cases i; rfl]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero hφ

/-- The two-variable uniqueness statement, in `subst1`/`subst2` form. -/
theorem existsUnique_lawSeries2' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) (a b : A) :
    ∃! φ : MvPowerSeries (Fin 2) A,
      (∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s φ
        = MvPowerSeries.coeff s (linForm2 a b)) ∧
      subst1 φ f = subst2 (subst1 (MvPowerSeries.X 0) f) (subst1 (MvPowerSeries.X 1) f) φ := by
  have h := existsUnique_lawSeries2 hπ hpow hf a b
  rw [gSub_two_eq] at h
  simpa only [subst1, subst2] using h

/-- The one-variable uniqueness statement, in `subst1` form. -/
theorem mulSeries_unique'' (hπ : IsLubinTateCoeff π q) (hpow : IsFrobeniusPower π q)
    (hf : IsLubinTateSeries π q f) {c : A} {φ : MvPowerSeries (Fin 1) A}
    (hlin : OrderGe 2 (φ - linForm1 c)) (heq : subst1 φ f = subst1 f φ) :
    φ = mulSeries hπ hpow hf c :=
  mulSeries_unique' hπ hpow hf hlin (commS_iff_subst1.mpr heq)


end

end NK.LocalReciprocityLubinTate.LubinTate
