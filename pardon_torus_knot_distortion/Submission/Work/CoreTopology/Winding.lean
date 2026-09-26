import Submission.Work.CoreTopology.Basic

/-!
# Lifts and the winding vector of a curve on a parametrised torus

For a parametrised torus `P` (with surface `F = P.carrier`), a **lift** of a closed
curve `γ : ℝ → F` is a continuous map `Λ = (Θ, Φ) : ℝ → ℝ²` with
`P.psi (Θ t) (Φ t) = γ t`.  Because the parametrisation is injective modulo `2π`,
the two coordinates `Θ`, `Φ` of a lift are determined up to additive constants in
`2πℤ`; the *winding vector* of `γ` is

  `(a, b)` where `Θ (2π) = Θ 0 + a·2π` and `Φ (2π) = Φ 0 + b·2π`,

an element of `ℤ²` independent of the lift.

A closed curve is **essential** if its winding vector is nonzero; this is the
combinatorial replacement for "not null-homotopic in `F`" used throughout.

The standard curve `standardTorusCurve p q` has the lift `t ↦ (p t, q t)` and
winding vector `(p, q)`; the meridian and longitude circles have winding vectors
`(0, 1)` and `(1, 0)`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

variable {P : ParamTorus}

/-- A lift of a closed curve `γ` on the torus `F` to the parameter plane `ℝ²`. -/
structure LiftOf (P : ParamTorus) (γ : ClosedCurve P) where
  /-- First ("longitude") parameter of the lift. -/
  Θ : ℝ → ℝ
  /-- Second ("meridian") parameter of the lift. -/
  Φ : ℝ → ℝ
  /-- Continuity of the first parameter. -/
  contΘ : Continuous Θ
  /-- Continuity of the second parameter. -/
  contΦ : Continuous Φ
  /-- The lift really parametrises `γ`. -/
  lifts : ∀ t : ℝ, P.psi (Θ t) (Φ t) = γ.γ t

theorem two_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by positivity

namespace LiftOf

variable {γ : ClosedCurve P}

/-- Along a lift of a *closed* curve, each parameter changes by an integer
multiple of `2π` after one period. -/
theorem period_shift (L : LiftOf P γ) (t : ℝ) :
    ∃ a b : ℤ, L.Θ (t + 2 * Real.pi) = L.Θ t + a * (2 * Real.pi) ∧
      L.Φ (t + 2 * Real.pi) = L.Φ t + b * (2 * Real.pi) := by
  have h : P.psi (L.Θ (t + 2 * Real.pi)) (L.Φ (t + 2 * Real.pi)) = P.psi (L.Θ t) (L.Φ t) := by
    rw [L.lifts (t + 2 * Real.pi), γ.periodic t, ← L.lifts t]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (P.inj_mod _ _ _ _).mp h
  exact ⟨a, b, ha, hb⟩

/-- The **winding vector** of a lifted closed curve: the pair of integer multiples
of `2π` by which the two parameters advance over one period. -/
noncomputable def winding (L : LiftOf P γ) : ℤ × ℤ :=
  ((L.period_shift 0).choose, (L.period_shift 0).choose_spec.choose)

/-- Characterising property of the winding vector. -/
theorem winding_spec (L : LiftOf P γ) :
    L.Θ (2 * Real.pi) = L.Θ 0 + (L.winding).1 * (2 * Real.pi) ∧
      L.Φ (2 * Real.pi) = L.Φ 0 + (L.winding).2 * (2 * Real.pi) := by
  have h := (L.period_shift 0).choose_spec.choose_spec
  simp only [winding, zero_add] at h ⊢
  exact h

/-- A continuous real function all of whose values are integer multiples of `2π`
is constant.  This is the discreteness of `2πℤ` inside the connected line. -/
theorem continuous_int_multiple_const (d : ℝ → ℝ) (hd : Continuous d)
    (hint : ∀ t : ℝ, ∃ k : ℤ, d t = k * (2 * Real.pi)) :
    ∃ k : ℤ, ∀ t : ℝ, d t = k * (2 * Real.pi) := by
  obtain ⟨k₀, hk₀⟩ := hint 0
  refine ⟨k₀, fun t => ?_⟩
  by_contra hne
  obtain ⟨k, hk⟩ := hint t
  have hk_ne : k ≠ k₀ := by
    intro h; apply hne; rw [hk, h]
  have key : ∀ (a b : ℝ) (ka kb : ℤ), d a = ka * (2 * Real.pi) →
      d b = kb * (2 * Real.pi) → ka < kb → False := by
    intro a b ka kb ha hb hlt
    have hmid : (ka : ℝ) * (2 * Real.pi) < ((ka : ℝ) + 1 / 2) * (2 * Real.pi) := by
      have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
      nlinarith
    have hmid2 : ((ka : ℝ) + 1 / 2) * (2 * Real.pi) < (kb : ℝ) * (2 * Real.pi) := by
      have hkb : (ka : ℝ) + 1 ≤ (kb : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      nlinarith [Real.pi_pos]
    have hmem : ((ka : ℝ) + 1 / 2) * (2 * Real.pi) ∈ Icc (d a) (d b) := by
      rw [ha, hb]; exact ⟨le_of_lt hmid, le_of_lt hmid2⟩
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hd hmem
    obtain ⟨k', hk'⟩ := hint c
    have hcancel : ((ka : ℝ) + 1 / 2) = (k' : ℝ) := by
      apply mul_right_cancel₀ two_pi_ne_zero
      rw [← hc, hk']
    have hint' : (2 * ka + 1 : ℤ) = 2 * k' := by
      have : ((2 * ka + 1 : ℤ) : ℝ) = ((2 * k' : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  rcases lt_or_gt_of_ne hk_ne with hlt | hgt
  · exact key t 0 k k₀ hk hk₀ hlt
  · exact key 0 t k₀ k hk₀ hk hgt

/-- The winding vector only depends on the parameter functions `(Θ, Φ)` of the lift: two lifts
of (possibly different) closed curves given by the same parameters have the same winding
vector. -/
theorem winding_congr {P' : ParamTorus} {γ' : ClosedCurve P'} (L : LiftOf P γ)
    (L' : LiftOf P' γ') (hΘ : ∀ t : ℝ, L'.Θ t = L.Θ t) (hΦ : ∀ t : ℝ, L'.Φ t = L.Φ t) :
    L'.winding = L.winding := by
  have h1 := L'.winding_spec
  have h2 := L.winding_spec
  have hfst : (L'.winding).1 = (L.winding).1 := by
    have hmul : (L'.winding).1 * (2 * Real.pi) = (L.winding).1 * (2 * Real.pi) := by
      have h := h1.1
      rw [hΘ (2 * Real.pi), hΘ 0] at h
      linarith [h, h2.1]
    exact_mod_cast mul_right_cancel₀ two_pi_ne_zero hmul
  have hsnd : (L'.winding).2 = (L.winding).2 := by
    have hmul : (L'.winding).2 * (2 * Real.pi) = (L.winding).2 * (2 * Real.pi) := by
      have h := h1.2
      rw [hΦ (2 * Real.pi), hΦ 0] at h
      linarith [h, h2.2]
    exact_mod_cast mul_right_cancel₀ two_pi_ne_zero hmul
  exact Prod.ext hfst hsnd

/-- The winding vector describes the advance of the lift over *every* period, not only the
period starting at `0`. -/
theorem period_shift_winding (L : LiftOf P γ) (t : ℝ) :
    L.Θ (t + 2 * Real.pi) = L.Θ t + (L.winding).1 * (2 * Real.pi) ∧
      L.Φ (t + 2 * Real.pi) = L.Φ t + (L.winding).2 * (2 * Real.pi) := by
  have hΘcont : Continuous fun s : ℝ => L.Θ (s + 2 * Real.pi) - L.Θ s :=
    (L.contΘ.comp (continuous_id.add continuous_const)).sub L.contΘ
  have hΦcont : Continuous fun s : ℝ => L.Φ (s + 2 * Real.pi) - L.Φ s :=
    (L.contΦ.comp (continuous_id.add continuous_const)).sub L.contΦ
  have hΘint : ∀ s : ℝ, ∃ k : ℤ, L.Θ (s + 2 * Real.pi) - L.Θ s = k * (2 * Real.pi) := by
    intro s; obtain ⟨a, _, ha, _⟩ := L.period_shift s; exact ⟨a, by linarith⟩
  have hΦint : ∀ s : ℝ, ∃ k : ℤ, L.Φ (s + 2 * Real.pi) - L.Φ s = k * (2 * Real.pi) := by
    intro s; obtain ⟨_, b, _, hb⟩ := L.period_shift s; exact ⟨b, by linarith⟩
  obtain ⟨k, hk⟩ := continuous_int_multiple_const _ hΘcont hΘint
  obtain ⟨l, hl⟩ := continuous_int_multiple_const _ hΦcont hΦint
  have hspec := L.winding_spec
  have hk0 : k = (L.winding).1 := by
    have : k * (2 * Real.pi) = (L.winding).1 * (2 * Real.pi) := by
      have := hk 0; rw [zero_add] at this; linarith
    exact_mod_cast mul_right_cancel₀ two_pi_ne_zero this
  have hl0 : l = (L.winding).2 := by
    have : l * (2 * Real.pi) = (L.winding).2 * (2 * Real.pi) := by
      have := hl 0; rw [zero_add] at this; linarith
    exact_mod_cast mul_right_cancel₀ two_pi_ne_zero this
  exact ⟨by have := hk t; rw [hk0] at this; linarith,
    by have := hl t; rw [hl0] at this; linarith⟩

/-- Two lifts of the same closed curve differ by a constant, which is an integer
multiple of `2π` in each coordinate. -/
theorem eq_add_const_Θ (L L' : LiftOf P γ) :
    ∃ k : ℤ, ∀ t : ℝ, L'.Θ t = L.Θ t + k * (2 * Real.pi) := by
  have hd : Continuous (fun t : ℝ => L'.Θ t - L.Θ t) := L'.contΘ.sub L.contΘ
  have hint : ∀ t : ℝ, ∃ k : ℤ, (L'.Θ t - L.Θ t) = k * (2 * Real.pi) := by
    intro t
    have h : P.psi (L'.Θ t) (L'.Φ t) = P.psi (L.Θ t) (L.Φ t) := by
      rw [L'.lifts t, L.lifts t]
    obtain ⟨⟨k, hk⟩, _⟩ := (P.inj_mod _ _ _ _).mp h
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := continuous_int_multiple_const _ hd hint
  exact ⟨k, fun t => by linarith [hk t]⟩

/-- Two lifts of the same closed curve differ by a constant, which is an integer
multiple of `2π` in each coordinate. -/
theorem eq_add_const_Φ (L L' : LiftOf P γ) :
    ∃ k : ℤ, ∀ t : ℝ, L'.Φ t = L.Φ t + k * (2 * Real.pi) := by
  have hd : Continuous (fun t : ℝ => L'.Φ t - L.Φ t) := L'.contΦ.sub L.contΦ
  have hint : ∀ t : ℝ, ∃ k : ℤ, (L'.Φ t - L.Φ t) = k * (2 * Real.pi) := by
    intro t
    have h : P.psi (L'.Θ t) (L'.Φ t) = P.psi (L.Θ t) (L.Φ t) := by
      rw [L'.lifts t, L.lifts t]
    obtain ⟨_, ⟨k, hk⟩⟩ := (P.inj_mod _ _ _ _).mp h
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := continuous_int_multiple_const _ hd hint
  exact ⟨k, fun t => by linarith [hk t]⟩

/-- The winding vector does not depend on the chosen lift. -/
theorem winding_eq (L L' : LiftOf P γ) : L'.winding = L.winding := by
  obtain ⟨k, hk⟩ := L.eq_add_const_Θ L'
  obtain ⟨m, hm⟩ := L.eq_add_const_Φ L'
  have h1 : ((L'.winding).1 : ℝ) = ((L.winding).1 : ℝ) := by
    have hA := (L'.winding_spec).1
    have hB := (L.winding_spec).1
    have hk2 := hk (2 * Real.pi)
    have hk0 := hk 0
    apply mul_right_cancel₀ two_pi_ne_zero
    linarith
  have h2 : ((L'.winding).2 : ℝ) = ((L.winding).2 : ℝ) := by
    have hA := (L'.winding_spec).2
    have hB := (L.winding_spec).2
    have hm2 := hm (2 * Real.pi)
    have hm0 := hm 0
    apply mul_right_cancel₀ two_pi_ne_zero
    linarith
  have h1' : (L'.winding).1 = (L.winding).1 := by exact_mod_cast h1
  have h2' : (L'.winding).2 = (L.winding).2 := by exact_mod_cast h2
  exact Prod.ext h1' h2'

end LiftOf

/-- A closed curve on the torus is **essential** if it admits a lift with nonzero
winding vector.  (By `LiftOf.winding_eq` this does not depend on the lift, and by
the path-lifting property of the universal covering every closed curve admits a
lift, so this is exactly "nonzero winding vector".) -/
def IsEssential (P : ParamTorus) (γ : ClosedCurve P) : Prop :=
  ∃ L : LiftOf P γ, L.winding ≠ (0, 0)

theorem IsEssential.winding_ne {γ : ClosedCurve P} (h : IsEssential P γ)
    (L : LiftOf P γ) : L.winding ≠ (0, 0) := by
  obtain ⟨L', hL'⟩ := h
  rw [L'.winding_eq L]
  exact hL'

/-- The region `U ⊆ ℝ³` **contains an essential loop** of the torus `F = P.carrier`: there is a
closed curve of `F` with nonzero winding vector whose image lies in `U`.  Since a closed curve of
a torus is null-homotopic exactly when its winding vector vanishes, this is "`F ∩ U` contains a
loop that is not null-homotopic in `F`". -/
def ParamTorus.ContainsEssentialLoop (P : ParamTorus) (U : Set R3) : Prop :=
  ∃ γ : ClosedCurve P, IsEssential P γ ∧ ∀ t : ℝ, γ t ∈ U

theorem ParamTorus.containsEssentialLoop_mono (P : ParamTorus) {U V : Set R3} (h : U ⊆ V)
    (hU : P.ContainsEssentialLoop U) : P.ContainsEssentialLoop V := by
  obtain ⟨γ, hess, hmem⟩ := hU
  exact ⟨γ, hess, fun t => h (hmem t)⟩

/-! ## The meridian and longitude circles -/

/-- The lift `(θ, t) ↦ (θ, t)` of the meridian circle at parameter `θ`. -/
def meridianLift (P : ParamTorus) (θ : ℝ) : LiftOf P (meridianCurve P θ) where
  Θ := fun _ => θ
  Φ := fun t => t
  contΘ := continuous_const
  contΦ := continuous_id
  lifts := fun _ => rfl

theorem meridianLift_winding (P : ParamTorus) (θ : ℝ) :
    (meridianLift P θ).winding = (0, 1) := by
  have h1 : ((meridianLift P θ).winding).1 = 0 := by
    have hspec := (meridianLift P θ).winding_spec.1
    have hconst : (meridianLift P θ).Θ (2 * Real.pi) = (meridianLift P θ).Θ 0 := rfl
    have hmul : ((meridianLift P θ).winding).1 * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero
  have h2 : ((meridianLift P θ).winding).2 = 1 := by
    have hspec := (meridianLift P θ).winding_spec.2
    have hΦ : (meridianLift P θ).Φ (2 * Real.pi) = 2 * Real.pi := rfl
    have hΦ0 : (meridianLift P θ).Φ 0 = 0 := rfl
    have hmul : ((meridianLift P θ).winding).2 * (2 * Real.pi) = 1 * (2 * Real.pi) := by
      rw [hΦ, hΦ0] at hspec; linarith [hspec]
    exact_mod_cast (mul_right_cancel₀ two_pi_ne_zero hmul)
  exact Prod.ext h1 h2

/-- The lift `(t, φ) ↦ (t, φ)` of the longitude circle at parameter `φ`. -/
def longitudeLift (P : ParamTorus) (φ : ℝ) : LiftOf P (longitudeCurve P φ) where
  Θ := fun t => t
  Φ := fun _ => φ
  contΘ := continuous_id
  contΦ := continuous_const
  lifts := fun _ => rfl

theorem longitudeLift_winding (P : ParamTorus) (φ : ℝ) :
    (longitudeLift P φ).winding = (1, 0) := by
  have h1 : ((longitudeLift P φ).winding).1 = 1 := by
    have hspec := (longitudeLift P φ).winding_spec.1
    have hΘ : (longitudeLift P φ).Θ (2 * Real.pi) = 2 * Real.pi := rfl
    have hΘ0 : (longitudeLift P φ).Θ 0 = 0 := rfl
    have hmul : ((longitudeLift P φ).winding).1 * (2 * Real.pi) = 1 * (2 * Real.pi) := by
      rw [hΘ, hΘ0] at hspec; linarith [hspec]
    exact_mod_cast (mul_right_cancel₀ two_pi_ne_zero hmul)
  have h2 : ((longitudeLift P φ).winding).2 = 0 := by
    have hspec := (longitudeLift P φ).winding_spec.2
    have hconst : (longitudeLift P φ).Φ (2 * Real.pi) = (longitudeLift P φ).Φ 0 := rfl
    have hmul : ((longitudeLift P φ).winding).2 * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero
  exact Prod.ext h1 h2

theorem meridianCurve_essential (P : ParamTorus) (θ : ℝ) :
    IsEssential P (meridianCurve P θ) :=
  ⟨meridianLift P θ, by rw [meridianLift_winding]; decide⟩

theorem longitudeCurve_essential (P : ParamTorus) (φ : ℝ) :
    IsEssential P (longitudeCurve P φ) :=
  ⟨longitudeLift P φ, by rw [longitudeLift_winding]; decide⟩

/-! ## The standard `(p,q)` curve -/

/-- The standard `(p,q)`-torus curve, as a closed curve on the standard torus. -/
def standardCurve (p q : ℕ) : ClosedCurve standard where
  γ := fun t : ℝ => Work.Core.torusMap ((p : ℝ) * t) ((q : ℝ) * t)
  cont := torusMap_continuous_linear _ _
  periodic := by
    intro t
    show Work.Core.torusMap ((p : ℝ) * (t + 2 * Real.pi)) ((q : ℝ) * (t + 2 * Real.pi)) =
      Work.Core.torusMap ((p : ℝ) * t) ((q : ℝ) * t)
    rw [show (p : ℝ) * (t + 2 * Real.pi) = (p : ℝ) * t + (p : ℤ) * (2 * Real.pi) from by
          push_cast; ring,
        show (q : ℝ) * (t + 2 * Real.pi) = (q : ℝ) * t + (q : ℤ) * (2 * Real.pi) from by
          push_cast; ring]
    exact (Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨(p : ℤ), rfl⟩, ⟨(q : ℤ), rfl⟩⟩
  mem := fun t => ⟨((p : ℝ) * t, (q : ℝ) * t), rfl⟩

/-- The underlying function of `standardCurve p q` is the standard `(p,q)`-curve. -/
theorem standardCurve_apply (p q : ℕ) (t : ℝ) :
    standardCurve p q t = standardTorusCurve p q t :=
  (Work.Core.standardTorusCurve_eq_torusMap p q t).symm

/-- The lift `t ↦ (p t, q t)` of the standard `(p,q)`-curve. -/
def standardCurveLift (p q : ℕ) : LiftOf standard (standardCurve p q) where
  Θ := fun t => (p : ℝ) * t
  Φ := fun t => (q : ℝ) * t
  contΘ := by fun_prop
  contΦ := by fun_prop
  lifts := fun t => rfl

theorem standardCurveLift_winding (p q : ℕ) :
    (standardCurveLift p q).winding = ((p : ℤ), (q : ℤ)) := by
  have h1 : ((standardCurveLift p q).winding).1 = (p : ℤ) := by
    have hspec := (standardCurveLift p q).winding_spec.1
    have hΘ : (standardCurveLift p q).Θ (2 * Real.pi) = (p : ℝ) * (2 * Real.pi) := rfl
    have hΘ0 : (standardCurveLift p q).Θ 0 = 0 := by simp [standardCurveLift]
    have hmul : ((standardCurveLift p q).winding).1 * (2 * Real.pi) =
        (p : ℤ) * (2 * Real.pi) := by
      rw [hΘ, hΘ0] at hspec; push_cast; linarith [hspec]
    exact_mod_cast (mul_right_cancel₀ two_pi_ne_zero hmul)
  have h2 : ((standardCurveLift p q).winding).2 = (q : ℤ) := by
    have hspec := (standardCurveLift p q).winding_spec.2
    have hΦ : (standardCurveLift p q).Φ (2 * Real.pi) = (q : ℝ) * (2 * Real.pi) := rfl
    have hΦ0 : (standardCurveLift p q).Φ 0 = 0 := by simp [standardCurveLift]
    have hmul : ((standardCurveLift p q).winding).2 * (2 * Real.pi) =
        (q : ℤ) * (2 * Real.pi) := by
      rw [hΦ, hΦ0] at hspec; push_cast; linarith [hspec]
    exact_mod_cast (mul_right_cancel₀ two_pi_ne_zero hmul)
  exact Prod.ext h1 h2

theorem standardCurve_essential (p q : ℕ) (hp : 0 < p) :
    IsEssential standard (standardCurve p q) :=
  ⟨standardCurveLift p q, by
    rw [standardCurveLift_winding]
    intro h
    have h1 : (p : ℤ) = 0 := congrArg Prod.fst h
    omega⟩

end

end Work.CoreTopology
