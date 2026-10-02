import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Submission.Work.Deep.Reed.Prob.Certified.Defs

/-!
# One-coordinate slicing of the convex distance

For a product indexed by `Option α` we relate Talagrand's convex distance in the
full product to the convex distance of the slices `A_ω` and of the projection
`B = {x | ∃ ω, (ω, x) ∈ A}` in the product indexed by `α`:

* `cdsq_option_le` : `cdsq A (ω, x) ≤ λ · cdsq A_ω x + (1-λ) · cdsq B x + (1-λ)²`;
* `cdsq_option_le_succ` : the case `λ = 0`, valid also for empty slices:
  `cdsq A (ω, x) ≤ cdsq B x + 1`.

These are the pointwise estimates behind the induction step of Talagrand's
convex distance inequality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

variable {α : Type*} [Fintype α]

lemma sqnorm_option (p : Option α → ℝ) :
    sqnorm p = p none ^ 2 + sqnorm (fun a => p (some a)) := by
  rw [sqnorm, Fintype.sum_option, sqnorm]

section Slice
variable {Ω : Option α → Type*} [∀ o, Fintype (Ω o)]

/-- The point of the product space obtained by gluing a slice point to `ω`. -/
def glue (ω : Ω none) (x : ∀ a, Ω (some a)) : ∀ o, Ω o := fun o => o.casesOn ω x

/-- The lift of a vector on the `α`-coordinates to the `Option α`-coordinates,
with value `c` in the `none` coordinate. -/
def lift (c : ℝ) (p : α → ℝ) : Option α → ℝ := fun o => o.casesOn c p

@[simp] lemma lift_none (c : ℝ) (p : α → ℝ) : lift c p none = c := rfl
@[simp] lemma lift_some (c : ℝ) (p : α → ℝ) (a : α) : lift c p (some a) = p a := rfl
@[simp] lemma glue_none (ω : Ω none) (x : ∀ a, Ω (some a)) : glue ω x none = ω := rfl
@[simp] lemma glue_some (ω : Ω none) (x : ∀ a, Ω (some a)) (a : α) :
    glue ω x (some a) = x a := rfl

lemma sqnorm_lift (c : ℝ) (p : α → ℝ) : sqnorm (lift c p) = c ^ 2 + sqnorm p := by
  rw [sqnorm_option]
  simp

lemma lift_affine (a b : ℝ) (hab : a + b = 1) (p q : α → ℝ) :
    lift 1 (fun i => a * p i + b * q i) = fun o => a * lift 1 p o + b * lift 1 q o := by
  funext o; cases o <;> simp [lift, hab]

lemma lift0_affine (a b : ℝ) (p q : α → ℝ) :
    lift 0 (fun i => a * p i + b * q i) = fun o => a * lift 0 p o + b * lift 0 q o := by
  funext o; cases o <;> simp [lift]

/-- The preimage of a convex set under `lift 0` (an affine map) is convex. -/
lemma convex_preimage_lift0 {C : Set (Option α → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ {p : α → ℝ | lift 0 p ∈ C} := by
  intro p hp q hq lam mu hl hm hlm
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have hpq : (lam • p + mu • q : α → ℝ) = fun i => lam * p i + mu * q i := by
    funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have heq : (fun o => lam * lift 0 p o + mu * lift 0 q o)
      = lam • (lift 0 p) + mu • (lift 0 q) := by
    funext o; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpq, lift0_affine, heq]
  exact hC hp hq hl hm hlm

lemma convex_preimage_lift1 {C : Set (Option α → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ {p : α → ℝ | lift 1 p ∈ C} := by
  intro p hp q hq lam mu hl hm hlm
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have hpq : (lam • p + mu • q : α → ℝ) = fun i => lam * p i + mu * q i := by
    funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have heq : (fun o => lam * lift 1 p o + mu * lift 1 q o)
      = lam • (lift 1 p) + mu • (lift 1 q) := by
    funext o; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpq, lift_affine _ _ hlm, heq]
  exact hC hp hq hl hm hlm

lemma lift_zero_01 {s : α → ℝ} (h01 : ∀ i, s i = 0 ∨ s i = 1) :
    ∀ o, lift 0 s o = 0 ∨ lift 0 s o = 1 := by
  intro o; cases o with
  | none => exact Or.inl rfl
  | some a => exact h01 a

lemma lift_one_01 {s : α → ℝ} (h01 : ∀ i, s i = 0 ∨ s i = 1) :
    ∀ o, lift 1 s o = 0 ∨ lift 1 s o = 1 := by
  intro o; cases o with
  | none => exact Or.inr rfl
  | some a => exact h01 a

lemma lift_zero_agrees {s : α → ℝ} {ω : Ω none} {x y : ∀ a, Ω (some a)}
    (h : ∀ i, s i = 0 → x i = y i) :
    ∀ o, lift 0 s o = 0 → glue ω x o = glue ω y o := by
  intro o ho; cases o with
  | none => rfl
  | some a => exact h a ho

lemma lift_one_agrees {s : α → ℝ} {ω ω' : Ω none} {x y : ∀ a, Ω (some a)}
    (h : ∀ i, s i = 0 → x i = y i) :
    ∀ o, lift 1 s o = 0 → glue ω x o = glue ω' y o := by
  intro o ho; cases o with
  | none => exact absurd ho (by norm_num [lift])
  | some a => exact h a ho

/-- Points of the slice up-set give points of the full up-set, with `none`-value `0`. -/
lemma lift0_mem_Uset {A : Set (∀ o, Ω o)} {ω : Ω none} {x : ∀ a, Ω (some a)}
    {s : α → ℝ} (hs : s ∈ Uset {x : ∀ a, Ω (some a) | glue ω x ∈ A} x) :
    lift 0 s ∈ Uset A (glue ω x) := by
  obtain ⟨h01, y, hy, hys⟩ := hs
  exact ⟨lift_zero_01 h01, glue ω y, hy, lift_zero_agrees hys⟩

/-- Points of the up-set of the projection give points of the full up-set,
with `none`-value `1`. -/
lemma lift1_mem_Uset {A : Set (∀ o, Ω o)} {ω : Ω none} {x : ∀ a, Ω (some a)}
    {t : α → ℝ} (ht : t ∈ Uset {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} x) :
    lift 1 t ∈ Uset A (glue ω x) := by
  obtain ⟨h01, y, ⟨ω', hy⟩, hys⟩ := ht
  exact ⟨lift_one_01 h01, glue ω' y, hy, lift_one_agrees hys⟩

/-- **One-coordinate slicing.**  For `λ ∈ [0,1]`, if the `ω`-slice of `A` is
nonempty, the convex distance in the product is controlled by the distance to the
slice and to the projection. -/
theorem cdsq_option_le {A : Set (∀ o, Ω o)} {ω : Ω none} {x : ∀ a, Ω (some a)}
    (hne : (Uset {x : ∀ a, Ω (some a) | glue ω x ∈ A} x).Nonempty)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    cdsq A (glue ω x) ≤
      lam * cdsq {x : ∀ a, Ω (some a) | glue ω x ∈ A} x
        + (1 - lam) * cdsq {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} x
        + (1 - lam) ^ 2 := by
  set Aω : Set (∀ a, Ω (some a)) := {x : ∀ a, Ω (some a) | glue ω x ∈ A} with hAω
  set B : Set (∀ a, Ω (some a)) := {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} with hB
  have hAne : A.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    obtain ⟨-, y, hy, -⟩ := hs
    exact ⟨glue ω y, hy⟩
  have hBne_set : B.Nonempty := by
    obtain ⟨z, hz⟩ := hAne
    refine ⟨fun a => z (some a), ?_⟩
    refine ⟨z none, ?_⟩
    have hzg : glue (z none) (fun a => z (some a)) = z := by funext o; cases o <;> rfl
    rw [hzg]; exact hz
  have hAωne : (Vset Aω x).Nonempty := hne.mono (subset_convexHull ℝ _)
  have hBne : (Vset B x).Nonempty :=
    (Uset_nonempty (x := x) (by simpa [hB] using hBne_set)).mono (subset_convexHull ℝ _)
  have hsub0 : Vset Aω x ⊆ {p : α → ℝ | lift 0 p ∈ Vset A (glue ω x)} := by
    refine convexHull_min ?_ (convex_preimage_lift0 (convex_convexHull ℝ _))
    intro s hs
    exact subset_convexHull ℝ _ (lift0_mem_Uset (ω := ω) (by simpa [hAω] using hs))
  have hsub1 : Vset B x ⊆ {p : α → ℝ | lift 1 p ∈ Vset A (glue ω x)} := by
    refine convexHull_min ?_ (convex_preimage_lift1 (convex_convexHull ℝ _))
    intro s hs
    exact subset_convexHull ℝ _ (lift1_mem_Uset (ω := ω) (by simpa [hB] using hs))
  have key : ∀ p₁ ∈ Vset Aω x, ∀ p₂ ∈ Vset B x,
      cdsq A (glue ω x) - (1 - lam) ^ 2 ≤ lam * sqnorm p₁ + (1 - lam) * sqnorm p₂ := by
    intro p₁ hp₁ p₂ hp₂
    have hmem : (fun o => lam * lift 0 p₁ o + (1 - lam) * lift 1 p₂ o) ∈ Vset A (glue ω x) :=
      (convex_convexHull ℝ _) (hsub0 hp₁) (hsub1 hp₂) h0 (by linarith) (by ring)
    have hbound := cdsq_le_sqnorm hmem
    have hlift : (fun o => lam * lift 0 p₁ o + (1 - lam) * lift 1 p₂ o)
        = lift (1 - lam) (fun a => lam * p₁ a + (1 - lam) * p₂ a) := by
      funext o; cases o <;> simp [lift]
    rw [hlift, sqnorm_lift] at hbound
    have hsum : sqnorm (fun a => lam * p₁ a + (1 - lam) * p₂ a)
        ≤ lam * sqnorm p₁ + (1 - lam) * sqnorm p₂ := sqnorm_add_le h0 h1
    linarith
  rcases eq_or_lt_of_le h0 with hlam0 | hlampos
  · -- λ = 0
    have hkey : ∀ p₂ ∈ Vset B x, cdsq A (glue ω x) - 1 ≤ sqnorm p₂ := by
      intro p₂ hp₂
      obtain ⟨p₁, hp₁⟩ := hAωne
      have hk := key p₁ hp₁ p₂ hp₂
      rw [← hlam0] at hk
      simpa using hk
    have hmain : cdsq A (glue ω x) - 1 ≤ cdsq B x := le_cdsq_of_forall hBne hkey
    rw [← hlam0]
    simpa using hmain
  · rcases lt_or_eq_of_le h1 with hlt1 | heq1
    · -- 0 < λ < 1
      have hstepA : ∀ p₂ ∈ Vset B x,
          cdsq A (glue ω x) - (1 - lam) ^ 2 - lam * cdsq Aω x ≤ (1 - lam) * sqnorm p₂ := by
        intro p₂ hp₂
        have hdiv : (cdsq A (glue ω x) - (1 - lam) ^ 2 - (1 - lam) * sqnorm p₂) / lam
            ≤ cdsq Aω x := by
          refine le_cdsq_of_forall hAωne fun p₁ hp₁ => ?_
          rw [div_le_iff₀ hlampos]
          have hk := key p₁ hp₁ p₂ hp₂
          linarith
        rw [div_le_iff₀ hlampos] at hdiv
        nlinarith [hdiv]
      have hstepB : (cdsq A (glue ω x) - (1 - lam) ^ 2 - lam * cdsq Aω x) / (1 - lam)
          ≤ cdsq B x := by
        refine le_cdsq_of_forall hBne fun p₂ hp₂ => ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hstepA p₂ hp₂]
      rw [div_le_iff₀ (by linarith)] at hstepB
      nlinarith [hstepB]
    · -- λ = 1
      have hkey : ∀ p₁ ∈ Vset Aω x, cdsq A (glue ω x) ≤ sqnorm p₁ := by
        intro p₁ hp₁
        obtain ⟨p₂, hp₂⟩ := hBne
        have hk := key p₁ hp₁ p₂ hp₂
        rw [heq1] at hk
        simpa using hk
      have hmain : cdsq A (glue ω x) ≤ cdsq Aω x := le_cdsq_of_forall hAωne hkey
      rw [heq1]
      simpa using hmain

/-- The case `λ = 0` of the slicing estimate, valid with empty `ω`-slice:
`cdsq A (ω,x) ≤ cdsq B x + 1`. -/
theorem cdsq_option_le_succ {A : Set (∀ o, Ω o)} {ω : Ω none} {x : ∀ a, Ω (some a)}
    (hne : (Uset {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} x).Nonempty) :
    cdsq A (glue ω x) ≤ cdsq {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} x + 1 := by
  set B : Set (∀ a, Ω (some a)) := {x : ∀ a, Ω (some a) | ∃ ω', glue ω' x ∈ A} with hB
  have hsub1 : Vset B x ⊆ {p : α → ℝ | lift 1 p ∈ Vset A (glue ω x)} := by
    refine convexHull_min ?_ (convex_preimage_lift1 (convex_convexHull ℝ _))
    intro s hs
    exact subset_convexHull ℝ _ (lift1_mem_Uset (ω := ω) (by simpa [hB] using hs))
  have hBne : (Vset B x).Nonempty := hne.mono (subset_convexHull ℝ _)
  have key : ∀ p₂ ∈ Vset B x, cdsq A (glue ω x) ≤ sqnorm p₂ + 1 := by
    intro p₂ hp₂
    have hmem : lift 1 p₂ ∈ Vset A (glue ω x) := hsub1 hp₂
    have hbound := cdsq_le_sqnorm hmem
    rw [sqnorm_lift] at hbound
    linarith
  have : cdsq A (glue ω x) - 1 ≤ cdsq B x := by
    refine le_cdsq_of_forall hBne fun p₂ hp₂ => ?_
    have := key p₂ hp₂
    linarith
  linarith

end Slice

end Work.Deep.Reed.Prob
