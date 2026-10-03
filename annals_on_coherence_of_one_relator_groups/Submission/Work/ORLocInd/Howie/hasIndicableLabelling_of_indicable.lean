/-
# Indicability of a vertex group gives an indicable labelling (Howie's Case 1, global form)

This file proves `Work.ORLocInd.Howie.hasIndicableLabelling_of_indicable`, the bridge which turns
the *local* hypothesis of Howie's Case 1 (a surjection `G_x ↠ ℤ` from the vertex group at one
vertex `x` of the presented groupoid) into the *global* notion of an indicable labelling
(`Presentation.HasIndicableLabelling`), **with no connectivity hypothesis on the graph**.

## The mathematics

Let `Γ` be a graph (a `Quiver` with an involutive reversal), `P = ⟨Γ | R⟩` a groupoid presentation
and `φ : G_x = π₁(⟨Γ|R⟩,x) ↠ ℤ` a surjection.  We must produce a balanced labelling `θ` of the
arrows of `Γ` which vanishes on the relators of `P` and whose level `pathSum θ p` is nonzero on
some closed path.

Write `C = {y | x` reaches `y`}` for the connected component of `x` (a path from `x` to `y` of the
quiver, arrows being reversed freely).  Choose a *section* `d` of the reachability relation,
`d y : x → y` for `y ∈ C`, normalised so that `d x` is the empty path (`sec`, `sec_self`).  Let
`ψ = φ ∘ (F(Γ)_x ↠ π₁(⟨Γ|R⟩,x))`.  On the component of `x` put

  `θ e = ψ (d(i e) · e · d(t e)⁻¹)`,   i.e. `θ e = ψ (conjLoop d(i e) d(t e) e)`,

and put `θ e = 0` on every arrow whose source is outside `C` (then its target is outside `C` too,
so this is consistent).  All the work is in the following three facts.

* **Balancedness** (`thetaFun_balanced`): reversing an arrow swaps the roles of `d(i e)` and
  `d(t e)` in the conjugate, so the two labels are opposite (`conjLoop_reverse_eq_inv`, which is the
  telescoping identity `pmul_conj_reverse`).

* **The level formula** (`pathSum_thetaFun`): for a path `p : a → b` whose source is reachable,
  `pathSum θ p = ψ (d a · p · d b⁻¹)`.  This is the `pathSum_labOf` formula of
  `Howie/exists_labelling.lean`, but for a section which is only defined on the component of `x`;
  the induction uses that consecutive arrows share the section at their common endpoint and that
  conjugation is multiplicative (`conjLoop_comp`).

* **Vanishing on relators**: a relator of `P` with base outside `C` has all its arrows outside `C`
  and hence level `0` (`pathSum_thetaFun_eq_zero`); a relator with base inside `C` has, by the level
  formula, level `ψ (d b · r_i · d b⁻¹)`, the `ψ`-image of a conjugate of `r_i`, which lies in the
  normal closure of the relators (`mem_relatorNormalClosure_conj`) and hence is killed by
  `ψ = φ ∘ (F(Γ)_x ↠ G_x)`.

Finally `φ` is surjective, so some reduced loop `w` at `x` maps to the generator of
`Multiplicative ℤ`; the level formula at the closed path `w` (with `d x = nil`) shows that `θ` is
nonzero on it.  Hence `P.HasIndicableLabelling`.

## Contents

* `IndicableLabelling.Reach`, `sec`, `sec_self`, `sec_eq` — the reachable component of `x` and a
  section of it;
* `IndicableLabelling.conjLoop` and its API (`conjLoop_comp`, `conjLoop_mul_reverse`,
  `conjLoop_reverse_eq_inv`, `conjLoop_nil_self`, `conjLoop_nil_nil`);
* `IndicableLabelling.thetaFun`, `thetaLabelling`, `thetaFun_balanced`, `thetaFun_eq`,
  `thetaFun_eq_zero`, `pathSum_thetaFun`, `pathSum_thetaFun_eq_zero`;
* `toVertexGroup_surjective`, `exists_lift_of_surjective` — lifting a surjection through the
  projection `F(Γ)_x ↠ π₁(⟨Γ|R⟩,x)`;
* `hasIndicableLabelling_of_indicable` — the target.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.exists_labelling
import Submission.Work.ORLocInd.Howie.pmul_conj_comp
import Submission.Work.ORLocInd.Howie.pmul_conj_reverse
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_conj

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.Howie

/- Auxiliary results for `hasIndicableLabelling_of_indicable`: the labelling built from a
homomorphism `F(Γ)_x →* ℤ` on the component of `x`. -/
namespace IndicableLabelling

universe u

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The component of `x` and a section of it -/

/-- The vertices reachable from `x` by a path of the graph. -/
def Reach (x y : V) : Prop := Nonempty (Quiver.Path x y)

/-- A section of the reachability relation at `x`, normalised so that `sec x x h` is the empty
path.  By proof irrelevance (and `sec_eq`) its value depends only on the vertex. -/
noncomputable def sec (x : V) (y : V) (h : Reach x y) : Quiver.Path x y := by
  classical
  exact if hy : y = x then hy ▸ (Quiver.Path.nil : Quiver.Path x x) else Classical.choice h

theorem sec_self (x : V) (h : Reach x x) : sec x x h = Quiver.Path.nil := by
  classical
  unfold sec
  rw [dif_pos rfl]

/-- The value of the section does not depend on the chosen proof of reachability. -/
theorem sec_eq (x y : V) (h h' : Reach x y) : sec x y h = sec x y h' := by
  rw [Subsingleton.elim h h']

/-- Reachability is preserved backwards along a path. -/
theorem reach_of_path {x a b : V} (q : Quiver.Path a b) (h : Reach x b) : Reach x a :=
  ⟨(Classical.choice h).comp q.reverse⟩

/-- An arrow whose target is reachable has reachable source. -/
theorem reach_left_of_reach_right {x : V} {a b : V} (e : a ⟶ b) (h : Reach x b) : Reach x a :=
  reach_of_path (Quiver.Path.nil.cons e) h

/-- If the source of a path is not reachable then neither is its target. -/
theorem not_reach_of_path {x a b : V} (q : Quiver.Path a b) (h : ¬ Reach x a) : ¬ Reach x b :=
  fun hb => h (reach_of_path q hb)

/-! ## Conjugating a path by section paths -/

/-- The conjugate of the path `p : a → b` by the section paths `δ : x → a` and `γ : x → b`, as an
element of the vertex group at `x`: `δ · p · γ⁻¹`. -/
noncomputable def conjLoop (x : V) {a b : V} (δ : Quiver.Path x a) (γ : Quiver.Path x b)
    (p : Quiver.Path a b) : VertexGroup x :=
  ⟨pmul (pmul δ p) γ.reverse, pmul_isReduced _ _⟩

/-- Conjugation is multiplicative when the two section paths at the common endpoint agree. -/
theorem conjLoop_comp (x : V) {a b c : V} (δ : Quiver.Path x a) (γ : Quiver.Path x b)
    (ε : Quiver.Path x c) (p : Quiver.Path a b) (q : Quiver.Path b c) :
    conjLoop x δ γ p * conjLoop x γ ε q = conjLoop x δ ε (p.comp q) := by
  apply Subtype.ext
  change pmul (pmul (pmul δ p) γ.reverse) (pmul (pmul γ q) ε.reverse)
    = pmul (pmul δ (p.comp q)) ε.reverse
  exact pmul_conj_comp δ γ ε p q

/-- A conjugate cancels against the conjugate of the reversed path. -/
theorem conjLoop_mul_reverse (x : V) {a b : V} (δ : Quiver.Path x a) (γ : Quiver.Path x b)
    (p : Quiver.Path a b) : conjLoop x δ γ p * conjLoop x γ δ p.reverse = 1 := by
  apply Subtype.ext
  change pmul (pmul (pmul δ p) γ.reverse) (pmul (pmul γ p.reverse) δ.reverse) = Quiver.Path.nil
  exact pmul_conj_reverse δ γ p

/-- The conjugate of the reverse is the inverse of the conjugate. -/
theorem conjLoop_reverse_eq_inv (x : V) {a b : V} (δ : Quiver.Path x a) (γ : Quiver.Path x b)
    (p : Quiver.Path a b) : conjLoop x γ δ p.reverse = (conjLoop x δ γ p)⁻¹ := by
  have h := conjLoop_mul_reverse x δ γ p
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- The conjugate of the empty path by the same section path at both ends is trivial. -/
theorem conjLoop_nil_self (x : V) {a : V} (δ : Quiver.Path x a) :
    conjLoop x δ δ (Quiver.Path.nil : Quiver.Path a a) = 1 := by
  apply Subtype.ext
  change pmul (pmul δ Quiver.Path.nil) δ.reverse = Quiver.Path.nil
  rw [pmul_nil_right, pmul_red_left, pmul_reverse]

/-- Conjugating a reduced loop at `x` by the empty path leaves it unchanged. -/
theorem conjLoop_nil_nil (x : V) (w : VertexGroup x) :
    conjLoop x (Quiver.Path.nil : Quiver.Path x x) (Quiver.Path.nil : Quiver.Path x x) w.1 = w := by
  apply Subtype.ext
  change pmul (pmul Quiver.Path.nil w.1) (Quiver.Path.nil : Quiver.Path x x) = w.1
  rw [pmul_nil_left, pmul_nil_right, red_eq_self (isReduced_red w.1), red_eq_self w.2]

/-! ## The labelling of the component of `x` -/

/-- The labelling of the arrows determined by a homomorphism `ψ : F(Γ)_x →* ℤ`: the arrow `e` is
sent to the `ψ`-value of `d(i(e)) · e · d(t(e))⁻¹`, where `d` is the chosen section of reachability
from `x`; arrows whose source is not reachable from `x` get the label `0`. -/
noncomputable def thetaFun (x : V) (ψ : VertexGroup x →* Multiplicative ℤ)
    (e : Quiver.Total V) : ℤ := by
  classical
  exact if h : Reach x e.left then
    Multiplicative.toAdd (ψ (conjLoop x (sec x e.left h)
      (sec x e.right ⟨(sec x e.left h).cons e.hom⟩) e.hom.toPath))
  else 0

/-- The value of `thetaFun` on an arrow with reachable source, computed with any two section
paths. -/
theorem thetaFun_eq (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) {a b : V} (f : a ⟶ b)
    (ha : Reach x a) (hb : Reach x b) :
    thetaFun x ψ (Quiver.Total.mk a b f)
      = Multiplicative.toAdd (ψ (conjLoop x (sec x a ha) (sec x b hb) f.toPath)) := by
  rw [thetaFun, dif_pos ha]

/-- The value of `thetaFun` on an arrow with unreachable source. -/
theorem thetaFun_eq_zero (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) {a b : V} (f : a ⟶ b)
    (ha : ¬ Reach x a) : thetaFun x ψ (Quiver.Total.mk a b f) = 0 := by
  rw [thetaFun, dif_neg ha]

/-- `thetaFun` is a balanced labelling: reversing an arrow negates its label. -/
theorem thetaFun_balanced (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) :
    IsBalanced (thetaFun x ψ) := by
  intro e
  obtain ⟨a, b, f⟩ := e
  rw [Quiver.totalReverse_mk]
  by_cases h : Reach x a
  · have hb : Reach x b := ⟨(sec x a h).cons f⟩
    rw [thetaFun_eq x ψ (Quiver.reverse f) hb h, thetaFun_eq x ψ f h hb,
      show (Quiver.reverse f).toPath = f.toPath.reverse from (Quiver.Path.reverse_toPath f).symm,
      conjLoop_reverse_eq_inv, map_inv, toAdd_inv]
  · have hb : ¬ Reach x b := fun hb => h (reach_left_of_reach_right f hb)
    rw [thetaFun_eq_zero x ψ (Quiver.reverse f) hb, thetaFun_eq_zero x ψ f h, neg_zero]

/-- The level of a path with reachable source is the `ψ`-value of its conjugate. -/
theorem pathSum_thetaFun (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) :
    ∀ {a b : V} (p : Quiver.Path a b) (ha : Reach x a) (hb : Reach x b),
      pathSum (thetaFun x ψ) p
        = Multiplicative.toAdd (ψ (conjLoop x (sec x a ha) (sec x b hb) p)) := by
  intro a b p
  induction p with
  | nil =>
      intro ha hb
      rw [pathSum_nil, conjLoop_nil_self x (sec x a ha), map_one, toAdd_one]
  | cons q e ih =>
      intro ha hb
      have hc : Reach x _ := ⟨(sec x a ha).comp q⟩
      rw [pathSum_cons, ih ha hc, thetaFun_eq x ψ e hc hb, ← toAdd_mul, ← map_mul,
        conjLoop_comp, Quiver.Path.comp_toPath_eq_cons]

/-- The level of a path with unreachable source is zero. -/
theorem pathSum_thetaFun_eq_zero (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) :
    ∀ {a b : V} (p : Quiver.Path a b), ¬ Reach x a → pathSum (thetaFun x ψ) p = 0 := by
  intro a b p
  induction p with
  | nil => intro _; rw [pathSum_nil]
  | cons q e ih =>
      intro ha
      have hc : ¬ Reach x _ := not_reach_of_path q ha
      rw [pathSum_cons, ih ha, thetaFun_eq_zero x ψ e hc]
      simp

/-- The labelling attached to a homomorphism `ψ : F(Γ)_x →* ℤ`. -/
noncomputable def thetaLabelling (x : V) (ψ : VertexGroup x →* Multiplicative ℤ) : Labelling V :=
  ⟨thetaFun x ψ, thetaFun_balanced x ψ⟩

end IndicableLabelling

open IndicableLabelling

universe u

/-! ## Lifting a surjection to the free vertex group -/

/-- The projection `F(Γ)_x ↠ π₁(⟨Γ|R⟩,x)` is surjective. -/
theorem toVertexGroup_surjective {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (x : V) : Function.Surjective (P.toVertexGroup x) :=
  QuotientGroup.mk'_surjective _

/-- If `π₁(⟨Γ|R⟩,x)` admits a surjection onto `ℤ`, then some reduced loop at `x` is sent to the
generator `ofAdd 1`. -/
theorem exists_lift_of_surjective {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (x : V) (φ : P.vertexGroup x →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) :
    ∃ w : VertexGroup x, φ (P.toVertexGroup x w) = Multiplicative.ofAdd 1 := by
  obtain ⟨g, hg⟩ := hφ (Multiplicative.ofAdd 1)
  obtain ⟨w, hw⟩ := toVertexGroup_surjective P x g
  exact ⟨w, by rw [hw]; exact hg⟩

/-! ## The target theorem -/

theorem hasIndicableLabelling_of_indicable {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V) (x : V)
    (φ : P.vertexGroup x →* Multiplicative ℤ) (hφ : Function.Surjective φ) :
    P.HasIndicableLabelling := by
  classical
  -- `ψ = φ ∘ (F(Γ)_x ↠ π₁(⟨Γ|R⟩,x))`
  set ψ : VertexGroup x →* Multiplicative ℤ := φ.comp (P.toVertexGroup x) with hψ
  refine ⟨thetaLabelling x ψ, ?_, ?_⟩
  · -- the labelling vanishes on the relators
    intro i
    change pathSum (thetaFun x ψ) (P.path i) = 0
    by_cases h : Reach x (P.base i)
    · -- a relator with base in the component of `x`: its level is the `ψ`-image of a conjugate of
      -- the relator, i.e. of an element of the normal closure of the relators
      rw [pathSum_thetaFun x ψ (P.path i) h h]
      have hmem : P.toVertexGroup x
          (conjLoop x (sec x (P.base i) h) (sec x (P.base i) h) (P.path i)) = 1 := by
        rw [P.toVertexGroup_apply]
        exact (QuotientGroup.eq_one_iff _).mpr
          (mem_relatorNormalClosure_conj P x i (sec x (P.base i) h))
      rw [hψ]
      simp only [MonoidHom.comp_apply]
      rw [hmem, map_one, toAdd_one]
    · -- a relator with base outside the component of `x` has all its arrows outside it
      rw [pathSum_thetaFun_eq_zero x ψ (P.path i) h]
  · -- the labelling is nonzero on a closed path mapping to the generator
    obtain ⟨w, hw⟩ := exists_lift_of_surjective P x φ hφ
    refine ⟨x, w.1, ?_⟩
    change pathSum (thetaFun x ψ) w.1 ≠ 0
    rw [pathSum_thetaFun x ψ w.1 ⟨Quiver.Path.nil⟩ ⟨Quiver.Path.nil⟩,
      sec_self x ⟨Quiver.Path.nil⟩, conjLoop_nil_nil x w, hψ]
    rw [MonoidHom.comp_apply, hw, toAdd_ofAdd]
    exact one_ne_zero

end Work.ORLocInd.Howie
