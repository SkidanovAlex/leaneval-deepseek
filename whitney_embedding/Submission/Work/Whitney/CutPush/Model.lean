import Mathlib

/-!
# The flat model of the collar push: the collision equation

This module records the *mechanism* of the Whitney finger in the flat model, in the form in which
the geometric obligation of `Submission/Work/Whitney/CutPush/Assembly.lean` has to be discharged.

The target is `A × B`.  The *first* (fixed) sheet is the graph of a map `h₁ : A → B`, the *second*
(pushed) sheet the graph of `h₂ : A → B`.  The push is the bump-modulated translation

  `bumpPush κ c e (x, y) = (x + κ (x,y) • c, y + κ (x,y) • e)`

(the displacement `(c, e)` is constant, its amplitude `κ : A × B → ℝ` is the bump).

`bumpPush_mem_sheet₁_iff` is the **collision equation**: the pushed second sheet meets the first
sheet exactly at the parameters `x` solving

  `h₂ x + κ (x, h₂ x) • e = h₁ (x + κ (x, h₂ x) • c)`.

Everything analytic about the finger is the statement that this equation has no solution on the
pushed range (`bumpPush_disjoint_sheet₁_of_no_solution`): a pushed value which is off the second
sheet's own image is then off the whole image, which is exactly the "placement" clause of the
interface (see `Localisation.lean`: only the *moved* sources have to be checked).

`model_no_collision` verifies the criterion for the explicit model of
`NOTES_SignedBigonPush_STATUS.md` §2: the second sheet is the graph of `β (x)₀ = (x₀ - a)(x₀ - b)`,
`β (x)_j = x_j` (`j ≥ 1`), the displacement is the first coordinate vector `eVec`, and the bump
exceeds `(b - a)²/4` on the sheet.  Both crossings (`x₀ = a` and `x₀ = b`) have *opposite* type
(`det dβ` changes sign), and `(b - a)²/4 < 1` (i.e. `b - a < 2`) is what makes such a bump
available inside `[0,1]`.  This is the model in which the collar push is *known* to exist.

The residual obligation of the chapter is to transport this to the manifold: choose the collar `W₀`
around the arc `γ₂` (containing `p₂`, `q₂`, missing `p₁`, `q₁`) and the bump so that `κ` vanishes on
a neighbourhood of `f '' frontier W₀` (in particular on the "cut" spheres around `p₁`, `q₁`), and
verify the collision equation there.  Note (see `README.md` §4) that the support of the push cannot
be bounded by a ball around a single double point: that form is refuted by the linking invariant.
-/

namespace Work.Whitney.CutPush

open Filter Topology

set_option linter.unusedVariables false

section Abstract

variable {A B : Type*} [Add A] [SMul ℝ A] [Add B] [SMul ℝ B]

/-- The first (fixed) sheet: the graph of `h₁`. -/
def sheet₁ (h₁ : A → B) : Set (A × B) := {p | p.2 = h₁ p.1}

/-- The second (pushed) sheet: the graph of `h₂`. -/
def sheet₂ (h₂ : A → B) : Set (A × B) := {p | p.2 = h₂ p.1}

/-- The bump-modulated translation: a constant displacement `(c, e)` whose amplitude is the bump
`κ`. -/
noncomputable def bumpPush (κ : A × B → ℝ) (c : A) (e : B) : A × B → A × B :=
  fun p => (p.1 + κ p • c, p.2 + κ p • e)

/-- **The collision equation.**  The pushed second sheet meets the first sheet exactly at the
parameters `x` solving `h₂ x + κ (x, h₂ x) • e = h₁ (x + κ (x, h₂ x) • c)`. -/
theorem bumpPush_mem_sheet₁_iff {h₁ h₂ : A → B} {κ : A × B → ℝ} {c : A} {e : B}
    {x : A} :
    bumpPush κ c e (x, h₂ x) ∈ sheet₁ h₁ ↔
      h₂ x + κ (x, h₂ x) • e = h₁ (x + κ (x, h₂ x) • c) :=
  Iff.rfl

/-- **The no-collision criterion.**  If the collision equation has no solution on a set `s` of
parameters, then the pushed second sheet over `s` misses the first sheet. -/
theorem bumpPush_disjoint_sheet₁_of_no_solution {h₁ h₂ : A → B} {κ : A × B → ℝ} {c : A} {e : B}
    {s : Set A}
    (h : ∀ x ∈ s, h₂ x + κ (x, h₂ x) • e ≠ h₁ (x + κ (x, h₂ x) • c)) :
    bumpPush κ c e '' (sheet₂ h₂ ∩ {p | p.1 ∈ s}) ∩ sheet₁ h₁ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨⟨a, b⟩, ⟨hp₂, hp⟩, rfl⟩, hy⟩
  simp only [bumpPush, sheet₁, sheet₂, Set.mem_ofPred_eq] at hp₂ hy
  subst hp₂
  exact h a hp hy

end Abstract

/-! ## The explicit model of `NOTES_SignedBigonPush_STATUS.md` §2 -/

/-- The second sheet of the explicit model: `β (x)₀ = (x₀ - a) (x₀ - b)` and `β (x)_j = x_j` for
`j ≥ 1`.  Its graph crosses the plane `{0}` exactly at `x = a e₀` and `x = b e₀`, and the two
crossings have *opposite* type (`det dβ` changes sign there). -/
noncomputable def modelBeta {n : ℕ} (a b : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun (i : Fin n) => if (i : ℕ) = 0 then (x i - a) * (x i - b) else x i

/-- **The model computation.**  If the bump is larger than `(b - a)²/4` on the (pushed) second
sheet, then the pushed second sheet misses the first sheet *entirely*: the collision equation has
no solution.

The point of the model is the inequality `(b - a)²/4 < 1`: the bump can be taken `1` on the sheet,
so it exceeds the depth `(b - a)²/4` by which the second sheet dips below the first, and no landing
occurs at all.  (`x ↦ (x₀ - a)(x₀ - b)` has its minimum `-(b - a)²/4` on the line where all the
other coordinates vanish — the line where the two sheets would otherwise meet — and `b - a < 2`
is exactly what lets a `[0,1]`-valued bump dominate that depth.) -/
theorem model_no_collision {n : ℕ} [NeZero n] {a b : ℝ} (hab : a < b) (hba : b - a < 2)
    {κ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    (hκ : ∀ x : Fin n → ℝ, (b - a) ^ 2 / 4 < κ (x, modelBeta a b x)) :
    ∀ x : Fin n → ℝ,
      modelBeta a b x + κ (x, modelBeta a b x) • (Pi.single (0 : Fin n) (1 : ℝ)) ≠ 0 := by
  intro x hx
  have h0 := congrFun hx (0 : Fin n)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, smul_eq_mul,
    mul_one] at h0
  have hβ : modelBeta a b x (0 : Fin n) = (x 0 - a) * (x 0 - b) := by simp [modelBeta]
  rw [hβ] at h0
  have hquad : -((x 0 - a) * (x 0 - b)) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x 0 - a - b)]
  have := hκ x
  linarith

/-! ## The normal shear: the diffeomorphism of the push

The push of the construction (see `README.md` §6) is, in the "tubular" coordinates
`(u, v) ∈ ℝⁿ × ℝⁿ` supplied by `Work.Whitney.exists_tubular_data_smooth` (`H (u, 0)` is the sheet
coordinate, `v` the normal offset), the **normal shear**

    `normalShear (fun u => κ u • e) : (u, v) ↦ (u, v + κ u • e)`,

a shift of the normal coordinate by an amount that depends only on the *sheet* coordinate.
`normalShear d` is a `C^∞` diffeomorphism of `ℝⁿ × ℝⁿ` with the explicit `C^∞` inverse
`normalShear (-d)`; no fold condition is needed, because the shear preserves the sheet coordinate
and its differential is block triangular with identity diagonal.  This is the algebraic core of the
construction: conjugated by `H` it gives the ambient diffeomorphism `ψ` and its inverse `σ`, and the
support of `ψ` is the *slab* `supp (κ • e) × ℝⁿ` — unbounded in the normal direction, which is
exactly what the linking obstruction of `README.md` §4 requires. -/

variable {n : ℕ}

/-- **The normal shear.**  `normalShear d` shifts the second coordinate by `d` of the first. -/
def normalShear (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  fun p => (p.1, p.2 + d p.1)

/-- The normal shear, unfolded. -/
theorem normalShear_apply (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    normalShear d p = (p.1, p.2 + d p.1) := rfl

/-- **The normal shear is a diffeomorphism**, with the explicit inverse `normalShear (-d)`. -/
theorem normalShear_leftInverse (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    Function.LeftInverse (normalShear (-d)) (normalShear d) := by
  intro p
  simp only [normalShear]
  exact Prod.ext rfl (by simp)

/-- **The normal shear is a diffeomorphism**, with the explicit inverse `normalShear (-d)`. -/
theorem normalShear_rightInverse (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    Function.RightInverse (normalShear (-d)) (normalShear d) := by
  intro p
  simp only [normalShear]
  exact Prod.ext rfl (by simp)

/-- **The normal shear is smooth** when `d` is.  (No fold condition: the differential is block
triangular with identity diagonal.) -/
theorem contDiff_normalShear {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (normalShear d) := by
  rw [show normalShear d = fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1, p.2 + d p.1) from funext (normalShear_apply d)]
  fun_prop

/-- **The normal shear preserves the sheet coordinate**: `(normalShear d p).1 = p.1`.  This is why
the *collision equation* of `bumpPush_mem_sheet₁_iff` is the right one on the push: the base
coordinate of a pushed point is unchanged. -/
theorem normalShear_fst (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    (normalShear d p).1 = p.1 := rfl

/-- **The model computation, localised to the support.**  The estimate is only needed on the
*support* of the bump (outside it the bump vanishes and the construction does not move the point);
this is the form in which `model_no_collision` is used for a *collar* (a bump supported on the
finger, not a globally large amplitude), cf. `README.md` §7. -/
theorem model_no_collision_of_mem {n : ℕ} [NeZero n] {a b : ℝ} (hab : a < b)
    {κ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)}
    (hκs : ∀ x ∈ s, (b - a) ^ 2 / 4 < κ (x, modelBeta a b x))
    {x : Fin n → ℝ} (hx : x ∈ s) :
    modelBeta a b x + κ (x, modelBeta a b x) • (Pi.single (0 : Fin n) (1 : ℝ)) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin n)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, smul_eq_mul,
    mul_one] at h0
  have hβ : modelBeta a b x (0 : Fin n) = (x 0 - a) * (x 0 - b) := by simp [modelBeta]
  rw [hβ] at h0
  have hquad : -((x 0 - a) * (x 0 - b)) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x 0 - a - b)]
  have := hκs x hx
  linarith

/-! ## Step 1 of the construction: the conjugated shear is injective

`README.md` §6 / `NOTES_NEXT.md` Step 1: the ambient `ψ` of the push is the normal shear read in the
tabular coordinates of `Work.Whitney.exists_tubular_data_smooth` (`H`).  This lemma is the algebraic
content of that step: if `H` is injective on `B`, `g` is a left inverse of `H` on `B`, and the shear
`normalShear d` maps the support region `A` into `B`, then the conjugated shear
`y ↦ H (normalShear d (g y))` is injective on `H '' A` — with the inverse
`y ↦ H (normalShear (-d) (g y))`.  (`H` is smooth and its shear is smooth by
`contDiff_normalShear`, so this is the injectivity half of the diffeomorphism; the extension by the
identity off `H '' A` needs `d = 0` on a neighbourhood of `∂A`, which is the shape condition of
`README.md` §7.) -/

variable {n : ℕ} {F : Type*}

/-- **The conjugated normal shear is injective.** -/
theorem injOn_normalShear_conj
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {B A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hH : Set.InjOn H B) (hg : ∀ x ∈ B, g (H x) = x)
    (hAB : A ⊆ B) (hA : ∀ x ∈ A, normalShear d x ∈ B) :
    Set.InjOn (fun y : F => H (normalShear d (g y))) (H '' A) := by
  rintro y ⟨a, ha, hy⟩ y' ⟨a', ha', hy'⟩ h
  dsimp only at h
  have hga : g y = a := by
    rw [← hy]
    exact hg a (hAB ha)
  have hga' : g y' = a' := by
    rw [← hy']
    exact hg a' (hAB ha')
  rw [hga, hga'] at h
  have h1 : normalShear d a = normalShear d a' := hH (hA a ha) (hA a' ha') h
  have h2 : a = a' := by
    have h3 := congrArg (normalShear (-d)) h1
    rw [normalShear_leftInverse, normalShear_leftInverse] at h3
    exact h3
  rw [← hy, ← hy', h2]

/-! ## Step 1 of the construction: the ambient push on a slab

`NOTES_NEXT.md` Step 1: the ambient `ψ` of the push is `normalShear d` read through the tubular
coordinates `H` of `Work.Whitney.exists_tubular_data_smooth`, extended by the identity off the
support.  The support of a *normal* shear `(u,v) ↦ (u, v + d u)` is a slab *over the support of
`d`* (its first coordinate is unchanged, `normalShear_fst`), so for any set `A` with
`normalShear d '' A ⊆ A` the extension is clean: identity off `H '' A`, the conjugated shear on
`H '' A`.  (The hypotheses below are exactly that invariance plus `A ⊆ B`, `H` injective on `B` and
`g` a left inverse of `H` on `B`; no boundedness of `A` is used, so this applies to the ball `B` of
`exists_tubular_data_smooth` together with a *thickened slab* `A` inside it.)

`slabPush_leftInverse` proves that `slabPush H g (-d) A` is a left inverse of `slabPush H g d A`
(hence `slabPush H g d A` is injective, `Function.LeftInverse.injective`), and
`slabPush_rightInverse` the other way.  What remains of Step 1 is *smoothness* of `slabPush`
(which needs the smoothness of `g`, i.e. of the inverse of `H` on its image). -/

variable {n : ℕ} {F : Type*}

/-- **The ambient push on a slab.**  The identity off `H '' A`, the conjugated normal shear on
`H '' A`. -/
noncomputable def slabPush
    (H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F)
    (g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (y : F) : F := by
  classical
  exact if y ∈ H '' A then H (normalShear d (g y)) else y

/-- The slab push on the pushed slab. -/
theorem slabPush_of_mem
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))} {y : F}
    (hy : y ∈ H '' A) :
    slabPush H g d A y = H (normalShear d (g y)) := by
  classical
  simp only [slabPush, if_pos hy]

/-- The slab push off the pushed slab is the identity. -/
theorem slabPush_of_notMem
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))} {y : F}
    (hy : y ∉ H '' A) :
    slabPush H g d A y = y := by
  classical
  simp only [slabPush, if_neg hy]

/-- The normal shear preserves a slab (its first coordinate is unchanged). -/
theorem normalShear_mem_slab {U : Set (EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)} (hx : x.1 ∈ U) :
    normalShear d x ∈ U ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
  ⟨hx, trivial⟩

/-- **The slab push is a left inverse of the reverse slab push** (with the negated shear). -/
theorem slabPush_leftInverse
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {A B : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hH : Set.InjOn H B)
    (hg : ∀ x ∈ B, g (H x) = x)
    (hAB : A ⊆ B)
    (hA : ∀ x ∈ A, normalShear d x ∈ A)
    (hA' : ∀ x ∈ A, normalShear (-d) x ∈ A) :
    Function.LeftInverse
      (slabPush H g (-d)
        A)
      (slabPush H g d A) := by
  intro y
  by_cases hy : y ∈ H '' A
  · have hψ : slabPush H g d A y
        = H (normalShear d (g y)) := slabPush_of_mem hy
    obtain ⟨a, ha, hay⟩ := hy
    have hgy : g y = a := by rw [← hay]; exact hg a (hAB ha)
    have hga : g y ∈ A := by
      rw [hgy]; exact ha
    have hmem : H (normalShear d (g y))
        ∈ H '' A :=
      ⟨normalShear d (g y), hA _ hga, rfl⟩
    rw [hψ, slabPush_of_mem hmem]
    have h1 : g (H (normalShear d (g y))) = normalShear d (g y) :=
      hg _ (hAB (hA (g y) hga))
    rw [h1, normalShear_leftInverse]
    rw [hgy]
    exact hay
  · rw [slabPush_of_notMem hy, slabPush_of_notMem hy]

/-- **The slab push is a right inverse of the reverse slab push** (with the negated shear). -/
theorem slabPush_rightInverse
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {A B : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hH : Set.InjOn H B)
    (hg : ∀ x ∈ B, g (H x) = x)
    (hAB : A ⊆ B)
    (hA : ∀ x ∈ A, normalShear d x ∈ A)
    (hA' : ∀ x ∈ A, normalShear (-d) x ∈ A) :
    Function.RightInverse
      (slabPush H g (-d)
        A)
      (slabPush H g d A) := by
  intro y
  by_cases hy : y ∈ H '' A
  · have hσ : slabPush H g (-d) A y
        = H (normalShear (-d) (g y)) := slabPush_of_mem hy
    obtain ⟨a, ha, hay⟩ := hy
    have hgy : g y = a := by rw [← hay]; exact hg a (hAB ha)
    have hga : g y ∈ A := by
      rw [hgy]; exact ha
    have hmem : H (normalShear (-d) (g y))
        ∈ H '' A :=
      ⟨normalShear (-d) (g y), hA' _ hga, rfl⟩
    rw [hσ, slabPush_of_mem hmem]
    have h1 : g (H (normalShear (-d) (g y))) = normalShear (-d) (g y) :=
      hg _ (hAB (hA' (g y) hga))
    rw [h1, normalShear_rightInverse]
    rw [hgy]
    exact hay
  · rw [slabPush_of_notMem hy, slabPush_of_notMem hy]

/-- **The slab push is injective** (it has a left inverse). -/
theorem slabPush_injective
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {A B : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hH : Set.InjOn H B)
    (hg : ∀ x ∈ B, g (H x) = x)
    (hAB : A ⊆ B)
    (hA : ∀ x ∈ A, normalShear d x ∈ A)
    (hA' : ∀ x ∈ A, normalShear (-d) x ∈ A) :
    Function.Injective
      (slabPush H g d A) :=
  (slabPush_leftInverse hH hg hAB hA hA').injective

/-! ## Step 1 (continued): smoothness of the ambient push

`slabPush` is the identity off `H '' A` and the conjugated normal shear on `H '' A`.  Its
smoothness therefore reduces to two facts: `H '' A` is open (so that on it the push is literally
`H ∘ normalShear d ∘ g`, a composite of smooth maps), and the two pieces agree on a neighbourhood of
`frontier (H '' A)` (the *gluing* condition, which in the construction is supplied by `d = 0` on a
neighbourhood of `∂A`: there the shear is the identity, so the push is the identity near the
boundary).  `contDiff_slabPush` is the resulting statement; it is estimate-free. -/

/-- The push is the conjugated shear on the pushed region. -/
theorem slabPush_eventuallyEq_comp [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hAopen : IsOpen (H '' A)) {y : F} (hy : y ∈ H '' A) :
    slabPush H g d A =ᶠ[𝓝 y] fun z => H (normalShear d (g z)) := by
  filter_upwards [hAopen.mem_nhds hy] with z hz
  exact slabPush_of_mem hz

/-- The push is the identity off the pushed region. -/
theorem slabPush_eventuallyEq_id_of_notMem_closure [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {y : F} (hy : y ∉ closure (H '' A)) :
    slabPush H g d A =ᶠ[𝓝 y] id := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz
  exact slabPush_of_notMem (fun h => hz (subset_closure h))

/-- **Smoothness of the ambient push.**  On the pushed region it is a composite of smooth maps; off
the closure of that region it is the identity; and on the frontier the two agree (the *gluing*
hypothesis, supplied in the construction by the bump vanishing near the frontier). -/
theorem contDiff_slabPush [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hAopen : IsOpen (H '' A))
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hglue : ∀ y ∈ frontier (H '' A), ∀ᶠ z in 𝓝 y, slabPush H g d A z = z) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (slabPush H g d A) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hyf : y ∈ frontier (H '' A)
  · exact (contDiffAt_id).congr_of_eventuallyEq (hglue y hyf)
  · by_cases hy : y ∈ H '' A
    · exact ((hH.comp ((contDiff_normalShear hd).comp hg)).contDiffAt).congr_of_eventuallyEq
        (slabPush_eventuallyEq_comp (H := H) (g := g) (d := d) hAopen hy)
    · have hycl : y ∉ closure (H '' A) := by
        intro hcl
        have hyf' : y ∈ frontier (H '' A) := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨hcl, subset_closure hy⟩
        exact hyf hyf'
      exact (contDiffAt_id).congr_of_eventuallyEq
        (slabPush_eventuallyEq_id_of_notMem_closure (H := H) (g := g) (d := d) hycl)

/-- The normal shear fixes every point at which the displacement vanishes. -/
theorem normalShear_eq_self
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)} (hx : d x.1 = 0) :
    normalShear d x = x :=
  Prod.ext rfl (by simp [normalShear, hx])

/-- **The gluing condition for the ambient push**, from geometry: if `d` vanishes on a neighbourhood
`W` of `∂A`, `g` inverts `H` on `A`, and the image of the part of `A` on which `d` does not vanish
does not accumulate at the frontier of `H '' A`, then `slabPush` is the identity on a neighbourhood
of `frontier (H '' A)`. -/
theorem slabPush_eventuallyEq_id_of_frontier [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))} {W : Set
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hdW : ∀ x ∈ W, d x.1 = 0)
    (hfix : ∀ x ∈ A, g (H x) = x)
    (hfar : ∀ y ∈ frontier (H '' A), y ∉ closure (H '' (A \ W))) :
    ∀ y ∈ frontier (H '' A), ∀ᶠ z in 𝓝 y, slabPush H g d A z = z := by
  intro y hy
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hfar y hy)] with z hz
  by_cases hzA : z ∈ H '' A
  · obtain ⟨x, hxA, rfl⟩ := hzA
    have hgx : g (H x) = x := hfix x hxA
    have hmem : g (H x) ∈ W := by
      by_contra hcon
      exact hz (subset_closure ⟨g (H x), ⟨by rw [hgx]; exact hxA, hcon⟩, by rw [hgx]⟩)
    rw [slabPush_of_mem ⟨x, hxA, rfl⟩, normalShear_eq_self (hdW _ hmem), hgx]
  · exact slabPush_of_notMem hzA

/-- **Step 1 of the construction, complete: the ambient push is a smooth self-map with a smooth
two-sided inverse.**  Given the tubular data (`H` smooth, `g` a smooth left inverse of `H` on `A`),
a smooth displacement `d` vanishing on a neighbourhood `W` of `∂A`, and the geometric condition that
the image of the part of `A` where `d` does not vanish does not accumulate at `frontier (H '' A)`,
the push `slabPush H g d A` is `C^∞` (here) and its two-sided inverse is `slabPush H g (-d) A`
(`slabPush_leftInverse`, `slabPush_rightInverse`). -/
theorem contDiff_slabPush_of_geometry
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → F}
    {g : F → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A W : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hAopen : IsOpen (H '' A))
    (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdW : ∀ x ∈ W, d x.1 = 0)
    (hfix : ∀ x ∈ A, g (H x) = x)
    (hfar : ∀ y ∈ frontier (H '' A), y ∉ closure (H '' (A \ W))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (slabPush H g d A) :=
  contDiff_slabPush hAopen hH hg hd (slabPush_eventuallyEq_id_of_frontier hdW hfix hfar)

end Work.Whitney.CutPush
