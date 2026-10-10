import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.map_AM2
import Submission.Work.MotT.AM2_descent
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# T4, steps 2–3: extension of `θ` to an `L`-automorphism of `L(E)`, and node C2 over `L`

The two-root Kummer field `L = K(ζ, w₁, w₂)` (`Work.MotT.KummerField2`) is finite Galois over `K`
(`Work.MotT.isGalois_KummerField2`), so `L^{Gal(L/K)} = K`.  Both twist fields sit inside
`M = ML2 = L(E) = FunctionField (D.E.baseChange L)` as the `K`-subfields `AM21`, `AM22`, with

* `AM21 ≅ F_{h₁}`, `AM22 ≅ F_{h₂}` over `K` (`Work.MotT.map_AM2`), and
* `AM21 ⊗_K L ≅ M`, `AM22 ⊗_K L ≅ M` (`Work.MotT.AM2_descent`).

Hence a `K`-isomorphism `θ : F_{h₁} ≃ₐ[K] F_{h₂}` extends to an `L`-algebra automorphism `Θ` of `M`
(`Work.MotT.exists_algEquiv_ML2`), to which node C2 over `L` applies
(`Work.MotT.c2_at_ML2`): `Θ = τ_Q ∘ [-1]^ε` with `Q` an **`L`-point** of `E` and `ε : Fin 2`.

Running C2 over `L` (rather than over `K̄`) is the point of the whole construction: it is what makes
the point `Q`, and hence the coordinates of the final `K`-point of the twisted Klein curve, rational
over `L`, hence over `K` by Galois descent.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type} [Field K]

/-- **`AM21 ≅ F_{h₁}`**: the restriction of `iota2` to the `K`-twist field of `h₁`. -/
def AM21algEquiv (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    ↥(AM21 D h₁ h₂ hk) ≃ₐ[K] ↥(twistFieldTK D h₁) :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨iota2 D h₁ h₂ hk x, by
        rw [← (map_AM2 D h₁ h₂ hk).1]; exact ⟨(x : ML2 D h₁ h₂ hk), x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := by intro c; ext; simp }
    ⟨fun x y hxy => Subtype.ext ((iota2_injective D h₁ h₂ hk) (Subtype.ext_iff.mp hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := (IntermediateField.mem_map (AM21 D h₁ h₂ hk)).mp (by
          rw [(map_AM2 D h₁ h₂ hk).1]; exact y.2)
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/-- **`AM22 ≅ F_{h₂}`**: the restriction of `iota2` to the `K`-twist field of `h₂`. -/
def AM22algEquiv (D : Work.MotV.KleinData K) (h₁ h₂ : K) (hk : ringChar K ≠ 5) :
    ↥(AM22 D h₁ h₂ hk) ≃ₐ[K] ↥(twistFieldTK D h₂) :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨iota2 D h₁ h₂ hk x, by
        rw [← (map_AM2 D h₁ h₂ hk).2]; exact ⟨(x : ML2 D h₁ h₂ hk), x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := by intro c; ext; simp }
    ⟨fun x y hxy => Subtype.ext ((iota2_injective D h₁ h₂ hk) (Subtype.ext_iff.mp hxy)),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := (IntermediateField.mem_map (AM22 D h₁ h₂ hk)).mp (by
          rw [(map_AM2 D h₁ h₂ hk).2]; exact y.2)
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/-- The `K`-isomorphism `AM21 ≃ₐ[K] AM22` induced by `θ`. -/
def thetaL (D : Work.MotV.KleinData K) {h₁ h₂ : K} (hk : ringChar K ≠ 5)
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂) :
    ↥(AM21 D h₁ h₂ hk) ≃ₐ[K] ↥(AM22 D h₁ h₂ hk) :=
  (AM21algEquiv D h₁ h₂ hk).trans (θ.trans (AM22algEquiv D h₁ h₂ hk).symm)

/-- **T4, step 2.**  A `K`-isomorphism `θ : F_{h₁} ≃ₐ[K] F_{h₂}` of twist fields extends to an
`L`-algebra automorphism `Θ` of `M = L(E)`, `L = K(ζ, w₁, w₂)`. -/
theorem exists_algEquiv_ML2 (D : Work.MotV.KleinData K) (hD : D.Good) {h₁ h₂ : K} (h₁0 : h₁ ≠ 0)
    (h₂0 : h₂ ≠ 0) (hk : ringChar K ≠ 5)
    (θ : twistFieldTK D h₁ ≃ₐ[K] twistFieldTK D h₂) :
    ∃ Θ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk,
      ∀ x : ↥(AM21 D h₁ h₂ hk),
        (Θ (x : ML2 D h₁ h₂ hk) : ML2 D h₁ h₂ hk) =
          ((thetaL D hk θ x : ↥(AM22 D h₁ h₂ hk)) : ML2 D h₁ h₂ hk) := by
  obtain ⟨hLI1, hsup1⟩ := (AM2_descent D hD h₁0 h₂0 hk).1
  obtain ⟨hLI2, hsup2⟩ := (AM2_descent D hD h₁0 h₂0 hk).2
  obtain ⟨Θ, hΘ⟩ := extend_algEquiv_of_linearDisjoint (K := K)
    (L := ↥(KummerField2 K h₁ h₂ hk)) (Ω := ML2 D h₁ h₂ hk)
    (AM21 D h₁ h₂ hk) (AM22 D h₁ h₂ hk) hLI1 hLI2 hsup1 hsup2 (thetaL D hk θ)
  exact ⟨Θ, fun x => hΘ x⟩

end

end Work.MotT
