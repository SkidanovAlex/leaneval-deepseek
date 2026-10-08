import Mathlib
import Submission.Work.CharLib.Defs
import Submission.Work.CharLib.CFun
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Induction`: restriction and induction of class functions

Base module of the restriction/induction area (area A6 of the Feit–Thompson drive).  It sets
up the conventions used by everything else in `Work.Induction`.

## Conventions

* class functions and the inner product are `Work.CharCore.cfInner` and
  `Work.CharCore.IsClassFun` (universe-polymorphic; definitionally the same as the `Work.CharLib`
  versions on groups in `Type 0`, see `cfInner_eq_charLib`);
* `Work.Induction.resFun H ψ` is the restriction `Res_H^G ψ = ψ ∘ H.subtype`, and
  `Work.Induction.resFunHom φ ψ` is restriction along an arbitrary group homomorphism
  `φ : H →* G` (so that restriction is functorial:
  `resFunHom (φ.comp ψ) = resFunHom ψ ∘ resFunHom φ`);
* `Work.Induction.indFun H φ` is the induced function
  `Ind_H^G φ g = |H|⁻¹ ∑_{x : x * g * x⁻¹ ∈ H} φ ⟨x * g * x⁻¹, _⟩`
  (the same formula as `Work.CharLib.indFun` and `Work.CharCore.indFun`, at an arbitrary
  universe, with the classical decidability instance fixed by the definition, so that
  statements mentioning `indFun` need no `DecidablePred` hypothesis);
* `Work.Induction.IsTI H` is the *trivial intersection* (TI) condition on a subgroup:
  `H ∩ Hˣ = 1` for every `x ∉ N_G(H)`, where `Hˣ = x H x⁻¹` is conjugation by `x`
  (Mathlib's pointwise action of `MulAut.conj x` on `Subgroup G`);
* `Work.Induction.conjFun H x φ h = φ (x * h * x⁻¹)` is the conjugate of a function on `H`
  along an element `x` of the normalizer of `H`; `Work.Induction.conjMem H x h` is
  `x * h * x⁻¹` as an element of `H`.

Throughout, class functions take values in `ℂ` and `G` is a finite group, written
multiplicatively.  For `H : Subgroup G` the type `H` is a group (the subgroup as a subtype) and
`Work.Induction.normalizer H` is its normalizer in `G`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Induction

variable {G : Type*} [Group G]

/-- Restriction of a complex-valued function along a group homomorphism `φ : H →* G`,
`resFunHom φ f = f ∘ φ`. -/
def resFunHom {H : Type*} [Group H] (φ : H →* G) (f : G → ℂ) : H → ℂ := f ∘ φ

/-- Restriction of a complex-valued function on `G` to a subgroup `H ≤ G`,
`Res_H^G f = f ∘ H.subtype`. -/
def resFun (H : Subgroup G) (f : G → ℂ) : H → ℂ := resFunHom H.subtype f

@[simp] theorem resFunHom_apply {H : Type*} [Group H] (φ : H →* G) (f : G → ℂ) (h : H) :
    resFunHom φ f h = f (φ h) := rfl

@[simp] theorem resFun_apply (H : Subgroup G) (f : G → ℂ) (h : H) : resFun H f h = f h := rfl

/-- `Work.Induction.resFun` is `Work.CharCore.resFun`. -/
theorem resFun_eq_charCore (H : Subgroup G) (f : G → ℂ) :
    resFun H f = CharCore.resFun H f := rfl

/-- `Work.Induction.cfInner`-compatible inner product: `Work.CharCore.cfInner`, restated here
for convenience. -/
abbrev cfInner {G : Type*} [Group G] [Fintype G] (f g : G → ℂ) : ℂ := CharCore.cfInner f g

/-- `Work.Induction.IsClassFun` is `Work.CharCore.IsClassFun`, restated here for convenience. -/
abbrev IsClassFun {G : Type*} [Group G] (f : G → ℂ) : Prop := CharCore.IsClassFun f

/-- The induced function of a function on a subgroup, in the classical trace form
`Ind_H^G φ g = |H|⁻¹ * ∑_{x : x * g * x⁻¹ ∈ H} φ ⟨x * g * x⁻¹, _⟩`.  (Same formula as
`Work.CharCore.indFun` and `Work.CharLib.indFun`; the classical decidability instance is fixed
by this definition, so no `DecidablePred` hypothesis is needed in statements.) -/
noncomputable def indFun (H : Subgroup G) [Fintype G] (φ : H → ℂ) : G → ℂ :=
  fun g => (Nat.card H : ℂ)⁻¹ *
    ∑ x : G, if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0

@[simp] theorem indFun_apply_def (H : Subgroup G) [Fintype G] (φ : H → ℂ) (g : G) :
    indFun H φ g = (Nat.card H : ℂ)⁻¹ *
      ∑ x : G, if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0 := rfl

/-- `Work.Induction.indFun` agrees with `Work.CharCore.indFun`. -/
theorem indFun_eq_charCore (H : Subgroup G) [Fintype G] (φ : H → ℂ) :
    indFun H φ = CharCore.indFun H φ := rfl

/-- Restriction is functorial. -/
theorem resFunHom_comp {H K : Type*} [Group H] [Group K] (φ : H →* G) (ψ : K →* H)
    (f : G → ℂ) : resFunHom (φ.comp ψ) f = resFunHom ψ (resFunHom φ f) := rfl

theorem resFunHom_add {H : Type*} [Group H] (φ : H →* G) (f g : G → ℂ) :
    resFunHom φ (f + g) = resFunHom φ f + resFunHom φ g := rfl

theorem resFunHom_neg {H : Type*} [Group H] (φ : H →* G) (f : G → ℂ) :
    resFunHom φ (-f) = -resFunHom φ f := rfl

theorem resFunHom_sub {H : Type*} [Group H] (φ : H →* G) (f g : G → ℂ) :
    resFunHom φ (f - g) = resFunHom φ f - resFunHom φ g := rfl

theorem resFunHom_mul {H : Type*} [Group H] (φ : H →* G) (f g : G → ℂ) :
    resFunHom φ (f * g) = resFunHom φ f * resFunHom φ g := rfl

theorem resFunHom_smul {H : Type*} [Group H] (φ : H →* G) (c : ℂ) (f : G → ℂ) :
    resFunHom φ (c • f) = c • resFunHom φ f := rfl

theorem resFunHom_zero {H : Type*} [Group H] (φ : H →* G) :
    resFunHom φ (0 : G → ℂ) = 0 := rfl

theorem resFunHom_one {H : Type*} [Group H] (φ : H →* G) :
    resFunHom φ (1 : G → ℂ) = 1 := rfl

theorem resFunHom_star {H : Type*} [Group H] (φ : H →* G) (f : G → ℂ) :
    resFunHom φ (star f) = star (resFunHom φ f) := rfl

theorem resFunHom_sum {H ι : Type*} [Group H] (φ : H →* G) (s : Finset ι) (F : ι → G → ℂ) :
    resFunHom φ (∑ i ∈ s, F i) = ∑ i ∈ s, resFunHom φ (F i) := by
  ext h
  simp [resFunHom]

theorem resFun_add (H : Subgroup G) (f g : G → ℂ) : resFun H (f + g) = resFun H f + resFun H g :=
  rfl

theorem resFun_neg (H : Subgroup G) (f : G → ℂ) : resFun H (-f) = -resFun H f := rfl

theorem resFun_sub (H : Subgroup G) (f g : G → ℂ) :
    resFun H (f - g) = resFun H f - resFun H g := rfl

theorem resFun_mul (H : Subgroup G) (f g : G → ℂ) : resFun H (f * g) = resFun H f * resFun H g :=
  rfl

theorem resFun_smul (H : Subgroup G) (c : ℂ) (f : G → ℂ) :
    resFun H (c • f) = c • resFun H f := rfl

theorem resFun_zero (H : Subgroup G) : resFun H (0 : G → ℂ) = 0 := rfl

theorem resFun_one (H : Subgroup G) : resFun H (1 : G → ℂ) = 1 := rfl

theorem resFun_star (H : Subgroup G) (f : G → ℂ) : resFun H (star f) = star (resFun H f) := rfl

theorem resFun_sum {ι : Type*} (H : Subgroup G) (s : Finset ι) (F : ι → G → ℂ) :
    resFun H (∑ i ∈ s, F i) = ∑ i ∈ s, resFun H (F i) :=
  resFunHom_sum H.subtype s F

/-- Restriction preserves class functions. -/
theorem isClassFun_resFun {H : Subgroup G} {f : G → ℂ} (hf : IsClassFun f) :
    IsClassFun (resFun H f) := by
  intro g h
  exact hf (g : G) (h : G)

/-- The normalizer `N_G(H)` of a subgroup `H ≤ G`. -/
abbrev normalizer (H : Subgroup G) : Subgroup G := Subgroup.normalizer (H : Set G)

theorem mem_normalizer_iff {H : Subgroup G} {x : G} :
    x ∈ normalizer H ↔ ∀ h : G, h ∈ H ↔ x * h * x⁻¹ ∈ H :=
  Subgroup.mem_normalizer_iff

/-- For `x` in the normalizer of `H` and `h ∈ H`, the conjugate `x * h * x⁻¹`, as an
element of `H`. -/
def conjMem (H : Subgroup G) (x : normalizer H) (h : H) : H :=
  ⟨x * h * x⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 h).mp h.2⟩

@[simp] theorem conjMem_val (H : Subgroup G) (x : normalizer H) (h : H) :
    ((conjMem H x h : H) : G) = x * h * x⁻¹ := rfl

/-- The conjugate of a class function along an element of the normalizer of `H`, viewed as a
function on `H`: `conjFun H x φ h = φ (x * h * x⁻¹)`. -/
def conjFun (H : Subgroup G) (x : normalizer H) (φ : H → ℂ) : H → ℂ :=
  φ ∘ conjMem H x

@[simp] theorem conjFun_apply (H : Subgroup G) (x : normalizer H) (φ : H → ℂ)
    (h : H) : conjFun H x φ h = φ (conjMem H x h) := rfl

/-- A subgroup `H` is a **TI subgroup** (trivial intersection subgroup) if `H ∩ Hˣ = 1` for
every `x ∉ N_G(H)`.  Equivalently (and this is the form used classically) `H ∩ Hˣ = 1` for
every `x ∉ H`. -/
def IsTI (H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ normalizer H → H ⊓ (MulAut.conj x • H) = ⊥

end Work.Induction
