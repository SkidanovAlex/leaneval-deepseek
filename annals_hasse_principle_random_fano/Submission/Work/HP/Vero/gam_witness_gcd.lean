import Mathlib
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.orth_witness
import Submission.Work.HP.Lat.gcdMinors2_linear
import Submission.Work.HP.Defs

/-!
# The witness `Z ∈ Γ_{x,y}` pairing with `ν₂(x+y)` to `gcdMinors2 x y ^ 2`

The paper's second-moment analysis needs, for a linearly independent pair `x, y`, a coefficient
vector `Z ∈ Γ_{x,y} = Λ_{ν₂x} ∩ Λ_{ν₂y}` whose pairing against `ν₂(x+y)` equals `gcdMinors2 x y ^ 2`.

The construction is the standard one.  Bézout's identity on the `2 × 2` minors, together with the
two-term vectors orthogonal to `x` (resp. `y`), gives

* `u` with `⟨u, x⟩ = 0` and `⟨u, y⟩ = d`  (`orth_witness`),
* `v` with `⟨v, y⟩ = 0` and `⟨v, x⟩ = d`  (the symmetric form),

where `d = gcdMinors2 x y`.  Then `Z = σ(u,v)` lies in `Γ_{x,y}` because `⟨u,x⟩ = ⟨v,y⟩ = 0`, and

`⟨σ(u,v), ν₂(x+y)⟩ = (⟨u, x+y⟩)(⟨v, x+y⟩) = (0 + d)(d + 0) = d^2`.

Everything rests on `dot_veronese_sigma` (the pairing identity for `σ`) and `sigma_mem_Gam`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-- `gcdMinors2` is symmetric in its two arguments. -/
lemma gcdMinors2_comm {ι : Type*} [Fintype ι] (x y : ι → ℤ) :
    gcdMinors2 y x = gcdMinors2 x y := by
  have h := Work.HP.Lat.gcdMinors2_linear x y 0 1 1 0
  simpa using h

/-- Exchanging the two vectors of a linearly independent pair preserves linear independence. -/
lemma linearIndependent_swap {n : ℕ} (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : LinearIndependent ℤ ![y, x] := by
  have h' := h.comp (Equiv.swap (0 : Fin 2) 1) (Equiv.injective _)
  convert h' using 2
  funext i
  fin_cases i <;> simp

/-- A vector orthogonal to `y` whose pairing with `x` is `gcdMinors2 x y`. -/
lemma orth_witness_symm {n : ℕ} (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) :
    ∃ v : Fin (n + 1) → ℤ, (∑ i, v i * y i = 0) ∧ (∑ i, v i * x i = gcdMinors2 x y) := by
  obtain ⟨v, hv, hvx⟩ := orth_witness y x (linearIndependent_swap x y hxy)
  exact ⟨v, hv, hvx.trans (gcdMinors2_comm x y)⟩

theorem gam_witness_gcd {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    ∃ Z : Mon 2 n → ℤ, Z ∈ Gam 2 n x y ∧
      (∑ m, veronese 2 n (x + y) m * Z m) = gcdMinors2 x y ^ 2 := by
  obtain ⟨u, hux, huy⟩ := orth_witness x y hxy
  obtain ⟨v, hvy, hvx⟩ := orth_witness_symm x y hxy
  refine ⟨sigma n u v, sigma_mem_Gam x y u v hux hvy, ?_⟩
  rw [dot_veronese_sigma n (x + y) u v]
  have hxu : (∑ i, x i * u i) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (x i) (u i))]
    exact hux
  have hyv : (∑ j, y j * v j) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (y j) (v j))]
    exact hvy
  have hxv : (∑ j, x j * v j) = gcdMinors2 x y := by
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (x j) (v j))]
    exact hvx
  have huy' : (∑ i, y i * u i) = gcdMinors2 x y := by
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (y i) (u i))]
    exact huy
  have hu : (∑ i, (x + y) i * u i) = gcdMinors2 x y := by
    rw [show (∑ i, (x + y) i * u i) = ∑ i, (x i * u i + y i * u i) from
      Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])]
    rw [Finset.sum_add_distrib, hxu, huy', zero_add]
  have hv : (∑ j, (x + y) j * v j) = gcdMinors2 x y := by
    rw [show (∑ j, (x + y) j * v j) = ∑ j, (x j * v j + y j * v j) from
      Finset.sum_congr rfl (fun j _ => by rw [Pi.add_apply, add_mul])]
    rw [Finset.sum_add_distrib, hyv, hxv, add_zero]
  rw [hu, hv]
  ring

end Work.HP.Vero
