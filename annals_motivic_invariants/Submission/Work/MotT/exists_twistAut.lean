import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotT.coeffAlgEquiv
import Submission.Work.MotV.twCoord_eq
import Submission.Work.MotV5.coeffAut
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## Auxiliary facts about the coefficient action on `Ω = K̄(E)`

The coefficient action `Work.MotV5.coeffAction D.E γ` of `γ ∈ Aut_K(K̄)` on
`Ω = OmK D = K̄(E)` (`Submission/Work/MotV5/coeffAut.lean`, whose `General` section is stated for
an arbitrary scalar extension `R → K → L`) acts on the constants by `γ` and fixes the generic
point `genX, genY`; hence it fixes all Klein coordinates `κ_i` (which are `K`-linear combinations
of `1, x, y, x², xy`) and all Klein ratios `κ_i/κ_0`. -/

section Helpers

variable {K : Type} [Field K]

/-- The coefficient action fixes the Klein basis `1, x, y, x², xy`, since `Φ_γ` fixes `genX` and
`genY`. -/
lemma coeffAction_kleinBas (D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) (m : Fin 5) :
    Work.MotV5.coeffAction D.E γ (Work.MotV.kleinBas D (KbK K) m)
      = Work.MotV.kleinBas D (KbK K) m := by
  fin_cases m <;>
    simp [Work.MotV.kleinBas, Work.MotV5.coeffAction_genX, Work.MotV5.coeffAction_genY]

/-- The coefficient action fixes the Klein coordinates `κ_i`: they are `K`-linear combinations of
the basis `1, x, y, x², xy`, whose coefficients lie in the base field `K`. -/
lemma coeffAction_kleinCoord (D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) (i : Fin 5) :
    Work.MotV5.coeffAction D.E γ (Work.MotV.kleinCoord D (KbK K) i)
      = Work.MotV.kleinCoord D (KbK K) i := by
  simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [Work.MotV5.coeffAction_algebraMap D.E γ, AlgEquiv.commutes γ (D.coord i m)]
  · exact coeffAction_kleinBas D γ m

/-- The coefficient action fixes the Klein ratios `κ_i/κ_0`. -/
lemma coeffAction_kleinRatio (D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) (i : Fin 5) :
    Work.MotV5.coeffAction D.E γ
        (Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0)
      = Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0 := by
  rw [map_div₀, coeffAction_kleinCoord D γ i, coeffAction_kleinCoord D γ 0]

/-- The coefficient action on the fifth root `w = wK D h` of `h`: it multiplies it by the Kummer
cocycle `c = γ(root5K h)/root5K h`. -/
lemma coeffAction_wK (D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) (h : K)
    (hh : h ≠ 0) :
    Work.MotV5.coeffAction D.E γ (wK D h)
      = algebraMap (KbK K) (OmK D) (γ (root5K h) / root5K h) * wK D h := by
  rw [show wK D h = algebraMap (KbK K) (OmK D) (root5K h) from rfl,
    Work.MotV5.coeffAction_algebraMap D.E γ, ← map_mul]
  congr 1
  rw [div_mul_cancel₀ _ (root5K_ne_zero hh)]

/-- The coefficient action on the twisted Klein coordinates: `γ*` multiplies `twCoordK D h i` by
`c^{-i}`, where `c = γ(root5K h)/root5K h` is the Kummer cocycle. -/
lemma coeffAction_twCoordK (D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) (h : K)
    (hh : h ≠ 0) (i : Fin 5) :
    Work.MotV5.coeffAction D.E γ (twCoordK D h i)
      = (algebraMap (KbK K) (OmK D) (γ (root5K h) / root5K h))⁻¹ ^ (i : ℕ) *
        twCoordK D h i := by
  rw [twCoordK, map_mul, map_pow, map_inv₀, coeffAction_wK D γ h hh,
    coeffAction_kleinRatio D γ i]
  rw [mul_inv_rev, mul_pow]
  first | refl_ring1 | ring

/-- The Kummer cocycle `c = γ(root5K h)/root5K h` satisfies `c^5 = 1` and, when `c ≠ 1`, it is a
primitive fifth root of unity (`c` has order dividing `5`). -/
lemma isPrimitiveRoot_cocycle (_D : Work.MotV.KleinData K) (γ : KbK K ≃ₐ[K] KbK K) {h : K}
    (hh : h ≠ 0) (hc : γ (root5K h) / root5K h ≠ 1) :
    IsPrimitiveRoot (γ (root5K h) / root5K h) 5 := by
  have halg : algebraMap K (KbK K) h ≠ 0 := fun h0 =>
    hh ((algebraMap K (KbK K)).injective (by rw [h0, map_zero]))
  have h5 : (γ (root5K h) / root5K h) ^ 5 = 1 := by
    rw [div_pow, ← map_pow, root5K_spec, AlgEquiv.commutes γ h, div_self halg]
  rw [IsPrimitiveRoot.iff_orderOf]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h5 hc

/-- **The diagonal part `Δ_c`.**  For every `h ≠ 0` there is a `K`-algebra automorphism `Δ` of
`Ω = K̄(E)` fixing the constants `K̄` and acting on the Klein ratios by
`κ_i/κ_0 ↦ c^i·κ_i/κ_0`, where `c = γ(root5K h)/root5K h` is the Kummer cocycle.

For `c ≠ 1`, `c` is a primitive fifth root of unity (`isPrimitiveRoot_cocycle`) and `Δ` is the
automorphism supplied by `D.Good.T_diag` at `L = K̄`, restricted to scalars `K`; for `c = 1` we
take `Δ = 1`. -/
lemma exists_diag (D : Work.MotV.KleinData K) (hD : D.Good) (γ : KbK K ≃ₐ[K] KbK K) (h : K)
    (hh : h ≠ 0) :
    ∃ Δ : OmK D ≃ₐ[K] OmK D,
      (∀ x : KbK K, Δ (algebraMap (KbK K) (OmK D) x) = algebraMap (KbK K) (OmK D) x) ∧
      (∀ i : Fin 5,
        Δ (Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0)
          = algebraMap (KbK K) (OmK D) (γ (root5K h) / root5K h) ^ (i : ℕ) *
            (Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0)) := by
  by_cases hc : γ (root5K h) / root5K h = 1
  · refine ⟨1, fun x => by simp, fun i => by simp [hc]⟩
  · have hprim := isPrimitiveRoot_cocycle D γ hh hc
    obtain ⟨σ, hσ⟩ := hD.T_diag (KbK K) (γ (root5K h) / root5K h) hprim
    refine ⟨AlgEquiv.restrictScalars K σ, fun x => ?_, fun i => ?_⟩
    · rw [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
    · rw [AlgEquiv.restrictScalars_apply]
      exact hσ i

end Helpers

/-- **The twisted Galois action on `K̄(E)`.**  For `h ≠ 0` and `γ ∈ Aut_K(K̄)` there is a
`K`-algebra automorphism `γ*_h` of `Ω = K̄(E) = Work.MotT.OmK D` acting on the constants `K̄` by `γ`
and fixing the twisted Klein coordinates `Work.MotT.twCoordK D h i` (`i : Fin 5`).

Construction: `γ*_h := Δ_c ∘ Φ_γ`, where `Φ_γ` is the coefficient action of `γ` (act on the
constants `K̄` by `γ`, fix `genX`, `genY`; available as `Work.MotT.coeffAlgEquiv` /
`Submission.Work.MotV5.coeffAut`), `c := γ(root5K h)/root5K h ∈ K̄` is the Kummer cocycle
(`c ^ 5 = 1`), and `Δ_c` is the automorphism of `Ω` acting on the Klein ratios by
`κ_i/κ_0 ↦ c^i·κ_i/κ_0` (`Work.MotV.KleinData.Good.T_diag` at `L = KbK K` for `c ≠ 1`; `Δ_1 = 1`).

Computation: since `Φ_γ` fixes `genX, genY` it fixes the Klein ratios `κ_i/κ_0`, so
`γ*_h(w_h^{-i}·κ_i/κ_0) = c^{-i}·w_h^{-i}·c^i·κ_i/κ_0 = w_h^{-i}·κ_i/κ_0 = twCoordK D h i`
(using `c = γ(w_h)/w_h`).

This is the automorphism whose fixed field is the twist field `F_h` (node T2), and it is the input
of the equivariance and cocycle computations of `Work.MotT.twist_iso_pointK`. -/
theorem exists_twistAut {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) {h : K} (hh : h ≠ 0) (γ : Work.MotT.KbK K ≃ₐ[K] Work.MotT.KbK K) :
    ∃ g : Work.MotT.OmK D ≃ₐ[K] Work.MotT.OmK D,
      (∀ c : Work.MotT.KbK K, g (algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D) c) =
        algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D) (γ c)) ∧
      (∀ i : Fin 5, g (Work.MotT.twCoordK D h i) = Work.MotT.twCoordK D h i) := by
  obtain ⟨Δ, hΔconst, hΔrat⟩ := exists_diag D hD γ h hh
  -- The Kummer cocycle is a non-zero constant of `Ω`.
  have hc_ne : γ (Work.MotT.root5K h) / Work.MotT.root5K h ≠ 0 :=
    div_ne_zero (fun h0 => Work.MotT.root5K_ne_zero hh
      (γ.injective (by rw [h0, map_zero]))) (Work.MotT.root5K_ne_zero hh)
  have hc0 : algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
      (γ (Work.MotT.root5K h) / Work.MotT.root5K h) ≠ 0 := by
    intro h0
    exact hc_ne ((algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)).injective (by rw [h0, map_zero]))
  refine ⟨(Work.MotV5.coeffAction D.E γ).trans Δ, ?_, ?_⟩
  · intro x
    rw [AlgEquiv.trans_apply, Work.MotV5.coeffAction_algebraMap D.E γ, hΔconst]
  · intro i
    have hΦ := coeffAction_twCoordK D γ h hh i
    have hΔw : Δ (Work.MotT.wK D h) = Work.MotT.wK D h := hΔconst (Work.MotT.root5K h)
    have hΔ : Δ (Work.MotT.twCoordK D h i)
        = algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
            (γ (Work.MotT.root5K h) / Work.MotT.root5K h) ^ (i : ℕ) *
          Work.MotT.twCoordK D h i := by
      rw [Work.MotT.twCoordK, map_mul, map_pow, map_inv₀, hΔw, hΔrat i]
      first | refl_ring1 | ring
    have hfix : Δ ((algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
        (γ (Work.MotT.root5K h) / Work.MotT.root5K h))⁻¹ ^ (i : ℕ))
        = (algebraMap (Work.MotT.KbK K) (Work.MotT.OmK D)
            (γ (Work.MotT.root5K h) / Work.MotT.root5K h))⁻¹ ^ (i : ℕ) := by
      rw [← map_inv₀, ← map_pow]
      exact hΔconst _
    show Δ (Work.MotV5.coeffAction D.E γ (Work.MotT.twCoordK D h i)) = Work.MotT.twCoordK D h i
    rw [hΦ, map_mul, hΔ, hfix, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, one_mul]

end Work.MotT
