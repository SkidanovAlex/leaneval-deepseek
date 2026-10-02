import Mathlib
import Submission.Work.Serre.SweepDefs
import Submission.Work.Serre.SweepRelDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base case `Z = ∂I¹` of the "three faces" lifting property

`Work.Serre.Sweep Z p` (see `Submission/Work/Serre/SweepDefs.lean`) is the statement that for a map
`p : E → B` and a test space `Z`, every lift of a base map `H : Z × I × I → B` defined on the three
faces `{s = 0}`, `{t = 0}`, `{t = 1}` of the prism `Z × I_s × I_t` extends to a lift of `H`.

Here we prove the base case of the induction of `Work.Serre.sweepCube_bdry`:

`Sweep` for the one-point space `I⁰` implies `Sweep` for `∂I¹ = {0, 1}`.

The point is that `∂I¹` is a *disjoint union of two points*: it is covered by the two clopen (in
fact, for us, closed) pieces `S = {z | z 0 = 0}` and `T = {z | z 0 = 1}`.  Given data on
`∂I¹ × I × I`, restrict it to the constant-`z₀` piece (where `z₀ = 0 ∈ ∂I¹`) and to the
constant-`z₁` piece (`z₁ = 1 ∈ ∂I¹`) and apply the hypothesis `Sweep I⁰` to the two restrictions,
obtaining lifts `G₀` and `G₁`.  Glue them by
`G (z, s, t) = if z 0 = 0 then G₀ (·, s, t) else G₁ (·, s, t)`; continuity is
`Work.Serre.continuous_of_isClosed_cover` (`SweepRelDefs.lean`), and the face conditions hold on
each piece because the two points of `∂I¹` are exactly `z₀` and `z₁` (`Fin 1` is a subsingleton).

This is the `m = 0` instance of the general fact that `Sweep` holds for a space which is a finite
disjoint union of points, and it is the first step of the induction in `sweepCube_bdry`.
-/

namespace Work.Serre

open scoped Topology unitInterval

theorem sweepBdryOne {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (h : Work.Serre.Sweep (Fin 0 → unitInterval) E B p) :
    Work.Serre.Sweep ↥(Cube.boundary (Fin 1)) E B p := by
  classical
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁
  -- The two points of `∂I¹` and the (unique) point of `I⁰`.
  let Z : Type := ↥(Cube.boundary (Fin 1))
  let z₀ : Z := ⟨fun _ => (0 : unitInterval), ⟨0, Or.inl rfl⟩⟩
  let z₁ : Z := ⟨fun _ => (1 : unitInterval), ⟨0, Or.inr rfl⟩⟩
  let pt : Fin 0 → unitInterval := fun i => i.elim0
  -- A point of `∂I¹` has its only coordinate equal to `0` or to `1`.
  have hcoord : ∀ u : Fin 1 → unitInterval, u ∈ Cube.boundary (Fin 1) → u 0 = 0 ∨ u 0 = 1 := by
    intro u hu
    obtain ⟨i, hi | hi⟩ := hu
    · exact Or.inl (by rw [Subsingleton.elim i 0] at hi; exact hi)
    · exact Or.inr (by rw [Subsingleton.elim i 0] at hi; exact hi)
  -- ... hence its only coordinate determines it: `∂I¹ = {z₀, z₁}`.
  have hz₀ : ∀ z : Z, ((z : Fin 1 → unitInterval) 0 = 0) → z = z₀ := by
    intro z hz
    refine Subtype.ext (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    exact hz
  have hz₁ : ∀ z : Z, ((z : Fin 1 → unitInterval) 0 = 1) → z = z₁ := by
    intro z hz
    refine Subtype.ext (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    exact hz
  -- The two inclusions of `I⁰ × I` and `I⁰ × I × I` into the corresponding `Z`-products at `z`.
  let r₂ : Z → C((Fin 0 → unitInterval) × unitInterval, Z × unitInterval) :=
    fun z => ⟨fun y => (z, y.2), by fun_prop⟩
  let r₃ : Z → C((Fin 0 → unitInterval) × unitInterval × unitInterval,
      Z × unitInterval × unitInterval) :=
    fun z => ⟨fun y => (z, y.2.1, y.2.2), by fun_prop⟩
  have hfH : ∀ (z : Z) (y : Fin 0 → unitInterval) (s t : unitInterval),
      (H.comp (r₃ z)) (y, s, t) = H (z, s, t) := fun _ _ _ _ => rfl
  -- The hypothesis `Sweep I⁰` applied to the data restricted to the point `z` of `∂I¹`.
  have key : ∀ z : Z, ∃ G : C((Fin 0 → unitInterval) × unitInterval × unitInterval, E),
      p.comp G = H.comp (r₃ z) ∧
      (∀ (y : Fin 0 → unitInterval) (t : unitInterval), G (y, 0, t) = f₀ (z, t)) ∧
      (∀ (y : Fin 0 → unitInterval) (s : unitInterval), G (y, s, 0) = f₁ (z, s)) ∧
      (∀ (y : Fin 0 → unitInterval) (s : unitInterval), G (y, s, 1) = f₂ (z, s)) := by
    intro z
    obtain ⟨G, hG, hG₀, hG₁, hG₂⟩ :=
      h (H.comp (r₃ z)) (f₀.comp (r₂ z))
        (by ext y; exact congrFun (congrArg DFunLike.coe h₀) (z, y.2))
        (f₁.comp (r₂ z))
        (by ext y; exact congrFun (congrArg DFunLike.coe h₁) (z, y.2))
        (f₂.comp (r₂ z))
        (by ext y; exact congrFun (congrArg DFunLike.coe h₂) (z, y.2))
        (fun _ => c₀ z) (fun _ => c₁ z)
    exact ⟨G, hG, fun y t => hG₀ y t, fun y s => hG₁ y s, fun y s => hG₂ y s⟩
  obtain ⟨G₀, hG₀p, hG₀₀, hG₀₁, hG₀₂⟩ := key z₀
  obtain ⟨G₁, hG₁p, hG₁₀, hG₁₁, hG₁₂⟩ := key z₁
  -- The two closed pieces `S = {z 0 = 0}` and `T = {z 0 = 1}` covering `Z × I × I`.
  let S : Set (Z × unitInterval × unitInterval) :=
    {x | (((x.1 : Z) : Fin 1 → unitInterval) 0 = (0 : unitInterval))}
  let T : Set (Z × unitInterval × unitInterval) :=
    {x | (((x.1 : Z) : Fin 1 → unitInterval) 0 = (1 : unitInterval))}
  have hS : IsClosed S := by
    show IsClosed {x : Z × unitInterval × unitInterval |
      (((x.1 : Z) : Fin 1 → unitInterval) 0) = (0 : unitInterval)}
    exact isClosed_eq
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hT : IsClosed T := by
    show IsClosed {x : Z × unitInterval × unitInterval |
      (((x.1 : Z) : Fin 1 → unitInterval) 0) = (1 : unitInterval)}
    exact isClosed_eq
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hcov : S ∪ T = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases hcoord (x.1 : Fin 1 → unitInterval) x.1.2 with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
  have hne : (0 : unitInterval) ≠ 1 := zero_ne_one
  have hGc : Continuous (fun x : Z × unitInterval × unitInterval =>
      if x ∈ S then G₀ (pt, x.2.1, x.2.2) else G₁ (pt, x.2.1, x.2.2)) :=
    continuous_of_isClosed_cover hS hT hcov
      (G₀.continuous.comp (by fun_prop)).continuousOn
      (G₁.continuous.comp (by fun_prop)).continuousOn
      (fun x hx => by
        have h0 : (((x.1 : Z) : Fin 1 → unitInterval) 0) = 0 := hx.1
        have h1 : (((x.1 : Z) : Fin 1 → unitInterval) 0) = 1 := hx.2
        exact absurd (h0.symm.trans h1) hne)
  -- The glued lift.
  let G : C(Z × unitInterval × unitInterval, E) :=
    ⟨fun x => if x ∈ S then G₀ (pt, x.2.1, x.2.2) else G₁ (pt, x.2.1, x.2.2), hGc⟩
  have hG_S : ∀ x : Z × unitInterval × unitInterval, x ∈ S → G x = G₀ (pt, x.2.1, x.2.2) := by
    intro x hx
    show (if x ∈ S then G₀ (pt, x.2.1, x.2.2) else G₁ (pt, x.2.1, x.2.2)) =
      G₀ (pt, x.2.1, x.2.2)
    rw [if_pos hx]
  have hG_T : ∀ x : Z × unitInterval × unitInterval, x ∉ S → G x = G₁ (pt, x.2.1, x.2.2) := by
    intro x hx
    show (if x ∈ S then G₀ (pt, x.2.1, x.2.2) else G₁ (pt, x.2.1, x.2.2)) =
      G₁ (pt, x.2.1, x.2.2)
    rw [if_neg hx]
  have hcoT : ∀ x : Z × unitInterval × unitInterval, x ∉ S →
      (((x.1 : Z) : Fin 1 → unitInterval) 0) = 1 := by
    intro x hx
    rcases hcoord (x.1 : Fin 1 → unitInterval) x.1.2 with hh | hh
    · exact absurd hh hx
    · exact hh
  have hzxS : ∀ x : Z × unitInterval × unitInterval, x ∈ S → x.1 = z₀ :=
    fun x hx => hz₀ x.1 hx
  have hzxT : ∀ x : Z × unitInterval × unitInterval, x ∉ S → x.1 = z₁ :=
    fun x hx => hz₁ x.1 (hcoT x hx)
  have hz₁' : ∀ z : Z, ¬ (((z : Z) : Fin 1 → unitInterval) 0 = 0) →
      (((z : Z) : Fin 1 → unitInterval) 0) = 1 := by
    intro z hz
    rcases hcoord (z : Fin 1 → unitInterval) z.2 with hh | hh
    · exact absurd hh hz
    · exact hh
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · -- `G` lifts `H`
    ext x
    show p (G x) = H x
    by_cases hx : x ∈ S
    · have h1 : p (G₀ (pt, x.2.1, x.2.2)) = H (z₀, x.2.1, x.2.2) :=
        (congrFun (congrArg DFunLike.coe hG₀p) (pt, x.2.1, x.2.2)).trans
          (hfH z₀ pt x.2.1 x.2.2)
      rw [hG_S x hx, h1, ← hzxS x hx]
    · have h1 : p (G₁ (pt, x.2.1, x.2.2)) = H (z₁, x.2.1, x.2.2) :=
        (congrFun (congrArg DFunLike.coe hG₁p) (pt, x.2.1, x.2.2)).trans
          (hfH z₁ pt x.2.1 x.2.2)
      rw [hG_T x hx, h1, ← hzxT x hx]
  · intro z t
    -- the face `s = 0`
    by_cases hz : (((z : Z) : Fin 1 → unitInterval) 0 = 0)
    · have hmem : ((z, 0, t) : Z × unitInterval × unitInterval) ∈ S := hz
      have h1 : G (z, 0, t) = G₀ (pt, 0, t) := by
        simpa using hG_S (z, 0, t) hmem
      rw [h1, hG₀₀ pt t, ← hz₀ z hz]
    · have hz1 := hz₁' z hz
      have hmem : ¬ (((z, 0, t) : Z × unitInterval × unitInterval) ∈ S) := hz
      have h1 : G (z, 0, t) = G₁ (pt, 0, t) := by
        simpa using hG_T (z, 0, t) hmem
      rw [h1, hG₁₀ pt t, ← hz₁ z hz1]
  · intro z w
    -- the face `t = 0`
    by_cases hz : (((z : Z) : Fin 1 → unitInterval) 0 = 0)
    · have hmem : ((z, w, 0) : Z × unitInterval × unitInterval) ∈ S := hz
      have h1 : G (z, w, 0) = G₀ (pt, w, 0) := by
        simpa using hG_S (z, w, 0) hmem
      rw [h1, hG₀₁ pt w, ← hz₀ z hz]
    · have hz1 := hz₁' z hz
      have hmem : ¬ (((z, w, 0) : Z × unitInterval × unitInterval) ∈ S) := hz
      have h1 : G (z, w, 0) = G₁ (pt, w, 0) := by
        simpa using hG_T (z, w, 0) hmem
      rw [h1, hG₁₁ pt w, ← hz₁ z hz1]
  · intro z w
    -- the face `t = 1`
    by_cases hz : (((z : Z) : Fin 1 → unitInterval) 0 = 0)
    · have hmem : ((z, w, 1) : Z × unitInterval × unitInterval) ∈ S := hz
      have h1 : G (z, w, 1) = G₀ (pt, w, 1) := by
        simpa using hG_S (z, w, 1) hmem
      rw [h1, hG₀₂ pt w, ← hz₀ z hz]
    · have hz1 := hz₁' z hz
      have hmem : ¬ (((z, w, 1) : Z × unitInterval × unitInterval) ∈ S) := hz
      have h1 : G (z, w, 1) = G₁ (pt, w, 1) := by
        simpa using hG_T (z, w, 1) hmem
      rw [h1, hG₁₂ pt w, ← hz₁ z hz1]

end Work.Serre
