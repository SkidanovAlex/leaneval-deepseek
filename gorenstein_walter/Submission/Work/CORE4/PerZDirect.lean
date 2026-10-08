import Mathlib
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.Case2CentCard
import Submission.Work.CORE4.Fibre9ImageCard
import Submission.Work.CORE4.Fibre9SupProj

namespace Work.CORE4

/-- If `P` commutes elementwise with `E`, `π : ↥(P ⊔ E) →* ↥E` is a projection modulo `P`
(i.e. `x * (π x)⁻¹ ∈ P` for every `x ∈ P ⊔ E`), and `w ∈ P ⊔ E` commutes with an element
`t ∈ E`, then the projection `π w ∈ E` commutes with `t` as well.

Indeed `w = (w * (π w)⁻¹) * π w` with `a := w * (π w)⁻¹ ∈ P`; the element `a` commutes with
both `t` and `π w` (as both lie in `E`), so `w t = t w` reduces to `π w · t = t · π w`. -/
theorem proj_centralizes {G : Type} [Group G] {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (π : ↥(P ⊔ E) →* ↥E)
    (hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P) :
    ∀ (w : ↥(P ⊔ E)) (t : G), t ∈ E → (w : G) * t = t * (w : G) →
      ((π w : ↥E) : G) * t = t * ((π w : ↥E) : G) := by
  intro w t ht hwt
  obtain ⟨a, haP, ha_eq⟩ : ∃ a ∈ P, a = (w : G) * (((π w : ↥E) : G))⁻¹ := ⟨_, hproj w, rfl⟩
  have hwt' : (a * ((π w : ↥E) : G)) * t = t * (a * ((π w : ↥E) : G)) := by
    have hw_eq : (w : G) = a * ((π w : ↥E) : G) := by rw [ha_eq]; group
    rw [hw_eq] at hwt
    exact hwt
  have hat : a * t = t * a := hcomm a haP t ht
  have key : a * (((π w : ↥E) : G) * t) = a * (t * ((π w : ↥E) : G)) := by
    calc a * (((π w : ↥E) : G) * t)
        = (a * ((π w : ↥E) : G)) * t := by group
      _ = t * (a * ((π w : ↥E) : G)) := hwt'
      _ = (t * a) * ((π w : ↥E) : G) := by group
      _ = (a * t) * ((π w : ↥E) : G) := by rw [← hat]
      _ = a * (t * ((π w : ↥E) : G)) := by group
  exact mul_left_cancel key

theorem PerZDirect {G : Type} [Group G] [Finite G] {p : ℕ} {X E' T A Y : Subgroup G}
    (hXE : X ⊓ E' = ⊥) (hXc : X ≤ Subgroup.centralizer (E' : Set G))
    (hTE : T ≤ E') (hTcard : Nat.card ↥T = p)
    (huniq : ∀ Z : Subgroup G, Z ≤ E' → Nat.card ↥Z = p →
      Z ≤ Subgroup.centralizer (T : Set G) → Z = T)
    (hA : A = X ⊔ T) (hYcard : Nat.card ↥Y = p)
    (hY : Y ≤ X ⊔ E') (hYX : Y ⊓ X = ⊥)
    (hYc : A ≤ Subgroup.centralizer (Y : Set G)) : Y ≤ A := by
  classical
  -- `X` commutes elementwise with `E'`, so `X ⊔ E'` is the internal direct product `X × E'`.
  have hcomm : ∀ x ∈ X, ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hXc hx) y hy).symm
  obtain ⟨π, hπ⟩ := ProjOfInfBot X E' hcomm hXE
  have hproj : ∀ x : ↥(X ⊔ E'), (x : G) * (((π x : ↥E') : G))⁻¹ ∈ X :=
    proj_mul_inv_mem hcomm π hπ
  -- The projection of `Y` into the `E'`-coordinate of the direct product `X × E'`.
  set Z : Subgroup G := Subgroup.map E'.subtype ((Y.subgroupOf (X ⊔ E')).map π) with hZdef
  have hTA : T ≤ A := by rw [hA]; exact le_sup_right
  have hZleE : Z ≤ E' := by rw [hZdef]; exact Subgroup.map_subtype_le _
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, Fibre9ImageCard π hproj hY hYX, hYcard]
  have hZcent : Z ≤ Subgroup.centralizer (T : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [hZdef, Subgroup.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [Subgroup.mem_map] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    rw [Subgroup.mem_subgroupOf] at hw
    have hwt : (w : G) * t = t * (w : G) :=
      Subgroup.mem_centralizer_iff.mp (hYc (hTA ht)) (w : G) hw
    have hp := proj_centralizes hcomm π hproj w t (hTE ht) hwt
    rw [← hwu]
    exact hp.symm
  have hZeqT : Z = T := huniq Z hZleE hZcard hZcent
  have hsup : X ⊔ Y = X ⊔ Z := Fibre9SupProj π hproj hY
  rw [hA, ← hZeqT, ← hsup]
  exact le_sup_right

end Work.CORE4
