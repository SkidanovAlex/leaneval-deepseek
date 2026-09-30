/-
# `polarToUHS v` is an open embedding

The map `Work.Cusp.polarToUHS v : E4 → E4` is
`(r, θ, w₁, w₂) ↦ (x, s)` with `x = (‖σ_v‖/2π · θ) • σ̂_v + w₁ • e₂ + w₂ • e₃` (the horizontal
part, in the orthonormal frame `(σ̂_v, e₂, e₃)`) and `s = e^{R₀ − r}`.

It is the product of two independent maps: the *linear* part `(θ,w₁,w₂) ↦ x`, which is a linear
isomorphism of `ℝ³` because `(σ̂_v, e₂, e₃)` is an orthonormal basis (`frame_orthonormal`) and
`‖σ_v‖ ≠ 0` (`slope_ne_zero`), and the *height* part `r ↦ e^{R₀ − r}`, which is `Real.exp`
composed with a reflection of `ℝ`.  Each is an open embedding, hence so is the product, hence so is
`polarToUHS v` (the two coordinate splittings of `E4` used to display the product are
homeomorphisms).
-/
import Mathlib
import Submission.Work.Cusp.polarToUHS_ThetaPolar
import Submission.Work.Space.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.RTOWed

open Work.Cusp Topology Function
open scoped Real InnerProductSpace

/-! ### The linear part `Y v` -/

/-- The horizontal part of `polarToUHS v` on the `(θ,w₁,w₂)`-coordinates: the linear map
`w ↦ (‖σ_v‖/2π · w 0) • σ̂_v + w 1 • e₂ + w 2 • e₃`.  This is the linear part of `polarToUHS v`,
which acts only on `(q 1, q 2, q 3)`. -/
def ptuY (v : Fin 5) : E3 →ₗ[ℝ] E3 where
  toFun w := ((‖slope v‖ / (2 * Real.pi)) * w 0) • frame1 v + w 1 • frame2 v + w 2 • frame3 v
  map_add' w w' := by ext i <;> fin_cases i <;> (simp; ring)
  map_smul' a w := by ext i <;> fin_cases i <;> (simp; ring)

/-- The scalar `‖σ_v‖/2π` in front of the angle coordinate. -/
def ptuCst (v : Fin 5) : ℝ := ‖slope v‖ / (2 * Real.pi)

lemma ptuCst_ne_zero (v : Fin 5) : ptuCst v ≠ 0 := by
  rw [ptuCst, div_ne_zero_iff]
  exact ⟨norm_ne_zero_iff.mpr (slope_ne_zero v), by positivity⟩

lemma ptuY_apply (v : Fin 5) (w : E3) :
    ptuY v w = (ptuCst v * w 0) • frame1 v + w 1 • frame2 v + w 2 • frame3 v := rfl

lemma ptuY_inner_f1 (v : Fin 5) (w : E3) :
    inner ℝ (ptuY v w) (frame1 v) = ptuCst v * w 0 := by
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := frame_orthonormal v
  simp only [ptuY_apply, ptuCst, inner_add_left, real_inner_smul_left]
  rw [show inner ℝ (frame1 v) (frame1 v) = 1 from by
        rw [real_inner_self_eq_norm_sq, h1]; norm_num,
      show inner ℝ (frame2 v) (frame1 v) = 0 from by rw [real_inner_comm, h12],
      show inner ℝ (frame3 v) (frame1 v) = 0 from by rw [real_inner_comm, h13]]
  ring

lemma ptuY_inner_f2 (v : Fin 5) (w : E3) : inner ℝ (ptuY v w) (frame2 v) = w 1 := by
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := frame_orthonormal v
  simp only [ptuY_apply, inner_add_left, real_inner_smul_left]
  rw [show inner ℝ (frame1 v) (frame2 v) = 0 from h12,
      show inner ℝ (frame2 v) (frame2 v) = 1 from by
        rw [real_inner_self_eq_norm_sq, h2]; norm_num,
      show inner ℝ (frame3 v) (frame2 v) = 0 from by rw [real_inner_comm, h23]]
  ring

lemma ptuY_inner_f3 (v : Fin 5) (w : E3) : inner ℝ (ptuY v w) (frame3 v) = w 2 := by
  obtain ⟨h12, h13, h23, h1, h2, h3⟩ := frame_orthonormal v
  simp only [ptuY_apply, inner_add_left, real_inner_smul_left]
  rw [show inner ℝ (frame1 v) (frame3 v) = 0 from h13,
      show inner ℝ (frame2 v) (frame3 v) = 0 from h23,
      show inner ℝ (frame3 v) (frame3 v) = 1 from by
        rw [real_inner_self_eq_norm_sq, h3]; norm_num]
  ring

/-- The two-sided inverse of `ptuY v`: it reads off the coefficients of `z` in the orthonormal
frame `(σ̂_v, e₂, e₃)`, undoing the scaling by `‖σ_v‖/2π` of the first one. -/
def ptuZ (v : Fin 5) (z : E3) : E3 :=
  !₂[inner ℝ z (frame1 v) / ptuCst v, inner ℝ z (frame2 v), inner ℝ z (frame3 v)]

lemma ptuZ_ptuY (v : Fin 5) (w : E3) : ptuZ v (ptuY v w) = w := by
  rw [ptuZ, ptuY_inner_f1, ptuY_inner_f2, ptuY_inner_f3,
    mul_div_cancel_left₀ _ (ptuCst_ne_zero v)]
  ext i; fin_cases i <;> simp

lemma ptuY_ptuZ (v : Fin 5) (z : E3) : ptuY v (ptuZ v z) = z := by
  rw [ptuY_apply]
  have h0 : (ptuZ v z) 0 = inner ℝ z (frame1 v) / ptuCst v := by simp [ptuZ]
  have h1 : (ptuZ v z) 1 = inner ℝ z (frame2 v) := by simp [ptuZ]
  have h2 : (ptuZ v z) 2 = inner ℝ z (frame3 v) := by simp [ptuZ]
  rw [h0, h1, h2, mul_div_cancel₀ _ (ptuCst_ne_zero v)]
  exact frame_expansion v z

lemma ptuY_surjective (v : Fin 5) : Surjective (ptuY v) := fun z => ⟨ptuZ v z, ptuY_ptuZ v z⟩

lemma ptuY_injective (v : Fin 5) : Injective (ptuY v) := fun a b h => by
  have := congrArg (ptuZ v) h
  rwa [ptuZ_ptuY, ptuZ_ptuY] at this

lemma ptuY_isOpenEmbedding (v : Fin 5) : IsOpenEmbedding (ptuY v) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (LinearMap.continuous_of_finiteDimensional (ptuY v))
    (ptuY_injective v)
    (LinearMap.isOpenMap_of_finiteDimensional (ptuY v) (ptuY_surjective v))

/-! ### The height part -/

/-- The height part of `polarToUHS v`: `r ↦ e^{R₀ − r}`, `Real.exp` after the reflection
`r ↦ R₀ − r`. -/
def ptuH : ℝ → ℝ := Real.exp ∘ fun t => R0 - t

lemma ptuH_isOpenEmbedding : IsOpenEmbedding ptuH := by
  have h1 : IsOpenEmbedding (fun t : ℝ => R0 - t) := by
    have hfe : (fun t : ℝ => R0 - t) = ⇑((Homeomorph.neg ℝ).trans (Homeomorph.addRight R0)) := by
      funext t; simp [Homeomorph.trans_apply, sub_eq_add_neg, add_comm]
    rw [hfe]
    exact ((Homeomorph.neg ℝ).trans (Homeomorph.addRight R0)).isOpenEmbedding
  exact Real.isOpenEmbedding_exp.comp h1

/-! ### The two coordinate splittings of `E4` -/

/-- The domain splitting `(q 0 | q 1, q 2, q 3)`: `E4 ≃ ℝ × ℝ³`, written as `E4 ≃ ℝ³ × ℝ` with
the `ℝ³` part first. -/
def ptuEqD : E4 ≃ E3 × ℝ where
  toFun q := (!₂[q 1, q 2, q 3], q 0)
  invFun p := !₂[p.2, p.1 0, p.1 1, p.1 2]
  left_inv q := by ext i <;> fin_cases i <;> simp
  right_inv p := by
    obtain ⟨w, t⟩ := p
    refine Prod.ext ?_ ?_
    · ext i; fin_cases i <;> simp
    · rfl

/-- The codomain splitting `(y 0, y 1, y 2 | y 3)`: the horizontal coordinates of the UHS point
first, the height last. -/
def ptuEqC : E4 ≃ E3 × ℝ where
  toFun y := (!₂[y 0, y 1, y 2], y 3)
  invFun p := !₂[p.1 0, p.1 1, p.1 2, p.2]
  left_inv y := by ext i <;> fin_cases i <;> simp
  right_inv p := by
    obtain ⟨w, t⟩ := p
    refine Prod.ext ?_ ?_
    · ext i; fin_cases i <;> simp
    · rfl

def ptuDh : E4 ≃ₜ E3 × ℝ where
  toEquiv := ptuEqD
  continuous_toFun := by
    change Continuous (fun q : E4 => (!₂[q 1, q 2, q 3], q 0)); fun_prop
  continuous_invFun := by
    change Continuous (fun p : E3 × ℝ => (!₂[p.2, p.1 0, p.1 1, p.1 2] : E4)); fun_prop

def ptuCh : E4 ≃ₜ E3 × ℝ where
  toEquiv := ptuEqC
  continuous_toFun := by
    change Continuous (fun y : E4 => (!₂[y 0, y 1, y 2], y 3)); fun_prop
  continuous_invFun := by
    change Continuous (fun p : E3 × ℝ => (!₂[p.1 0, p.1 1, p.1 2, p.2] : E4)); fun_prop

@[simp] lemma ptuCh_apply (y : E4) : ptuCh y = (!₂[y 0, y 1, y 2], y 3) := rfl
@[simp] lemma ptuDh_apply (q : E4) : ptuDh q = (!₂[q 1, q 2, q 3], q 0) := rfl
@[simp] lemma ptuCh_symm_apply (p : E3 × ℝ) : ptuCh.symm p = (!₂[p.1 0, p.1 1, p.1 2, p.2] : E4) := rfl
@[simp] lemma ptuDh_symm_apply (p : E3 × ℝ) : ptuDh.symm p = (!₂[p.2, p.1 0, p.1 1, p.1 2] : E4) := rfl

/-! ### The product decomposition -/

/-- **`polarToUHS v` is the product of the linear part and the height part**, read in the two
splittings `ptuCh`, `ptuDh`: `ptuCh (polarToUHS v q) = (ptuY v (q 1,q 2,q 3), ptuH (q 0))`. -/
lemma ptu_chart_eq (v : Fin 5) (q : E4) :
    ptuCh (polarToUHS v q) = Prod.map (ptuY v) ptuH (ptuDh q) := by
  rw [ptuCh_apply, ptuDh_apply]
  simp only [Prod.map]
  refine Prod.ext ?_ ?_
  · ext i <;> fin_cases i <;> simp [polarToUHS, ptuY]
  · simp [polarToUHS, ptuH]

/-- The conjugation identity: `polarToUHS v = ptuCh.symm ∘ (ptuY v × ptuH) ∘ ptuDh`. -/
lemma ptu_chart_eq_fun (v : Fin 5) :
    polarToUHS v = ⇑ptuCh.symm ∘ (Prod.map (ptuY v) ptuH) ∘ ⇑ptuDh := by
  funext q
  simp only [Function.comp_apply]
  rw [← ptu_chart_eq v q]
  exact (ptuCh.symm_apply_apply (polarToUHS v q)).symm

/-! ### The theorem -/

theorem polarToUHS_isOpenEmbedding (v : Work.Space.Cusp) :
    Topology.IsOpenEmbedding (Work.Cusp.polarToUHS v) := by
  have hF : IsOpenEmbedding (Prod.map (ptuY v) ptuH) :=
    (ptuY_isOpenEmbedding v).prodMap ptuH_isOpenEmbedding
  rw [ptu_chart_eq_fun v]
  rw [Homeomorph.comp_isOpenEmbedding_iff ptuCh.symm]
  rw [Homeomorph.isOpenEmbedding_comp_iff ptuDh]
  exact hF

end Work.RTOWed
