import Mathlib
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.hypTorus_cyclic

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-- When `d = c²` with `c ≠ 0` in a field of odd characteristic, the "non-split torus"
`hypTorus F d = {!![a, d*b; b, a] | a² - d b² = 1}` has `q - 1` elements.

Indeed `a² - c² b² = (a + b c)(a - b c) = 1`, so `x ↦ a + b c` is a multiplicative injection of
`hypTorus F d` into `Fˣ`, and it is onto: for `t ≠ 0`, take `a = (t + t⁻¹)/2`,
`b = (t - t⁻¹)/(2c)`.  Hence `hypTorus F d ≃ Fˣ` and `|Fˣ| = |F| - 1`. -/
theorem hypTorus_card_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d c : F)
    (hc : c * c = d) (hc0 : c ≠ 0) :
    Nat.card (Work.L2F.hypTorus F d) = Nat.card F - 1 := by
  have hρ : c * c = RingHom.id F d := by rw [RingHom.id_apply]; exact hc
  let hom : Work.L2F.hypTorus F d →* F := Work.L2F.Conic.hypHom d (RingHom.id F) c hρ
  let φ : Work.L2F.hypTorus F d →* Fˣ := hom.toHomUnits
  have hφcoe : ∀ x, (φ x : F) = Work.L2F.Conic.hypHom d (RingHom.id F) c hρ x := by
    intro x
    dsimp only [φ, hom]
    exact MonoidHom.coe_toHomUnits _ x
  have hinj : Function.Injective φ := by
    intro x y hxy
    refine Work.L2F.Conic.hypHom_id_injective d c hρ hc0 h2 ?_
    have h := congrArg (fun u : Fˣ => (u : F)) hxy
    rwa [hφcoe x, hφcoe y] at h
  have hsurj : Function.Surjective φ := by
    intro t
    have ht0 : (t : F) ≠ 0 := t.ne_zero
    set a : F := ((t : F) + (t : F)⁻¹) / 2 with ha
    set b : F := ((t : F) - (t : F)⁻¹) / (2 * c) with hb
    have hsum : a + b * c = (t : F) := by rw [ha, hb]; field_simp; ring
    have hdiff : a - b * c = (t : F)⁻¹ := by rw [ha, hb]; field_simp; ring
    have hab : a ^ 2 - d * b ^ 2 = 1 := by
      have h1 : a ^ 2 - d * b ^ 2 = (a + b * c) * (a - b * c) := by rw [← hc]; ring
      rw [h1, hsum, hdiff, mul_inv_cancel₀ ht0]
    let x : Matrix.SpecialLinearGroup (Fin 2) F :=
      ⟨!![a, d * b; b, a], Work.L2F.Conic.hypMat_det d a b hab⟩
    have hxmem : x ∈ Work.L2F.hypTorus F d :=
      (Work.L2F.Conic.mem_hypTorus F d x).mpr ⟨a, b, hab, rfl⟩
    refine ⟨⟨x, hxmem⟩, ?_⟩
    apply Units.ext
    dsimp only [φ, hom]
    rw [MonoidHom.coe_toHomUnits, Work.L2F.Conic.hypHom_apply,
      Work.L2F.Conic.hypHomFun_apply_form d (RingHom.id F) c ⟨x, hxmem⟩ a b rfl]
    simpa only [RingHom.id_apply] using hsum
  rw [Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)]
  exact Nat.card_units F

end Work.L2F.Props
