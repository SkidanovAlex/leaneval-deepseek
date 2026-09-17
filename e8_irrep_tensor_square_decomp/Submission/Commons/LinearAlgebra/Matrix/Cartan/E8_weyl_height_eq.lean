import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef

/-!
# The Weyl orbit of `ρ` in `E₈`: the only conjugate of height `620` is `ρ` itself

Let `A = CartanMatrix.E₈` and let `ρ = ω₀ + ⋯ + ω₇` be the Weyl vector, i.e. the constant vector
`(1, …, 1)` of the weight lattice written in the fundamental-weight (`ω`) basis.  A word `L` of
simple reflections acts on the `ω`-coordinates by

  `(sᵢ v)ⱼ = vⱼ - vᵢ A_{ij}`,

and the *height* of `v` is the sum of its coordinates in the simple-root basis, i.e.

  `e8ht v = ∑ᵢ (A⁻¹ v)ᵢ = ∑ᵢ ∑ⱼ (A⁻¹)_{ij} vⱼ = ⟪ρ, v⟫`.

The main point is that the invariant bilinear form `⟪v,w⟫ = v ⬝ A⁻¹ w` is preserved by every simple
reflection, so every Weyl conjugate `v = wact L ρ` satisfies `⟪v, v⟫ = ⟪ρ, ρ⟫ = 620`, while the
height is `⟪ρ, v⟫`.  If the height were also `620` we would get

  `⟪v - ρ, v - ρ⟫ = ⟪v,v⟫ - 2⟪ρ,v⟫ + ⟪ρ,ρ⟫ = 620 - 1240 + 620 = 0`,

and positive definiteness of the form (in the simple-root coordinates, where it is the Cartan form
of `E₈`, positive definite by `E8_posDef`) forces `v = ρ`.

Hence: `E8_weyl_height_eq` — an element of the Weyl orbit of `ρ` of height `620` must be `ρ`.
-/

set_option linter.unusedSimpArgs false

namespace Commons.LinearAlgebra.Matrix.Cartan

open E8NormTwo

/-- The simple reflection at the node `i`, acting on weights written in the fundamental-weight
basis, exactly as in the statement. -/
private def srf (i : Fin 8) (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  fun j => v j - v i * CartanMatrix.E₈ i j

/-- The fold of the statement: `wact L v` is `v` reflected successively along the entries of `L`. -/
private def act (L : List (Fin 8)) (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v

/-- The Weyl vector `ρ = ω₀ + ⋯ + ω₇`, in the fundamental-weight basis. -/
private def rho : Fin 8 → ℤ := fun _ => 1

private lemma act_cons (i : Fin 8) (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    act (i :: L) v = act L (srf i v) := rfl

/-- The squared length `qZ v = v ⬝ A⁻¹ v` is invariant under the fold. -/
private lemma qZ_act (L : List (Fin 8)) (v : Fin 8 → ℤ) : qZ (act L v) = qZ v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih => rw [act_cons, ih]; exact qZ_refl v i

/-- The height of the Weyl vector is `620`, the sum of all entries of `A⁻¹`. -/
private lemma qZ_rho : qZ rho = 620 := by decide

/-- `form2 x y = ∑ i, x i * (A y) i` for the Cartan matrix `A` over `ℚ`. -/
private lemma form2_eq_sum_mulVec (x y : Fin 8 → ℚ) :
    form2 x y = ∑ i, x i * (E8q.mulVec y) i := by
  rw [form2]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [E8q, E8, Matrix.map_apply, Int.coe_castRingHom]
  ring

/-- The pairing `⟪xc v, xc ρ⟫` is the height of `v` (with `xc v = A⁻¹ v` the simple-root
coordinates of `v`). -/
private lemma form2_xc_rho (v : Fin 8 → ℤ) :
    form2 (xc v) (xc rho) = (e8ht v : ℚ) := by
  rw [form2_eq_sum_mulVec, E8q_mul_xc]
  simp only [rho, Int.cast_one, mul_one, e8ht]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [xc]

/-- Expansion of the square of a difference for the form `form2`. -/
private lemma form2_sub_self (x y : Fin 8 → ℚ) :
    form2 (x - y) (x - y) = form2 x x - 2 * form2 x y + form2 y y := by
  have h := form2_bilin x y 1
  simpa using h

/-- **A weight of squared length `620` whose height is `620` is the Weyl vector `ρ`.**

Writing `⟪v, w⟫ = v ⬝ A⁻¹ w` for the `W`-invariant form, the hypothesis `qZ v = 620` says
`⟪v, v⟫ = ⟪ρ, ρ⟫` while `e8ht v = 620` says `⟪ρ, v⟫ = 620`; hence

  `⟪v - ρ, v - ρ⟫ = 620 - 2 · 620 + 620 = 0`,

and positive definiteness of the form (carried over to the simple-root coordinates, where it is the
Cartan form of `E₈`) forces `v = ρ`. -/
theorem E8_eq_rho_of_qZ_eq_e8ht (v : Fin 8 → ℤ) (hv : qZ v = 620) (hht : e8ht v = 620) :
    v = fun _ => 1 := by
  have h1 : form2 (xc v) (xc rho) = 620 := by
    rw [form2_xc_rho, hht]; norm_num
  have h2 : form2 (xc v) (xc v) = 620 := by
    rw [form2_xc_self, hv]; norm_num
  have h3 : form2 (xc rho) (xc rho) = 620 := by
    rw [form2_xc_self, qZ_rho]; norm_num
  have hzero : form2 (xc v - xc rho) (xc v - xc rho) = 0 := by
    rw [form2_sub_self, h2, h1, h3]; norm_num
  have hsub : xc v - xc rho = 0 := by
    by_contra hne
    have hpos : 0 < form2 (xc v - xc rho) (xc v - xc rho) := by
      simpa only [form2] using E8_posDef _ hne
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  have hxc : xc v = xc rho := sub_eq_zero.mp hsub
  have hfun : (fun j => (v j : ℚ)) = fun j => ((rho j : ℤ) : ℚ) := by
    rw [← E8q_mul_xc v, ← E8q_mul_xc rho, hxc]
  funext j
  have h1' : ((v j : ℤ) : ℚ) = ((rho j : ℤ) : ℚ) := congr_fun hfun j
  have h2' : v j = rho j := by exact_mod_cast h1'
  simpa [rho] using h2'

/-- **The height of a Weyl conjugate of `ρ` is `620` only for `ρ` itself.**

This is `E8_weyl_height_eq` phrased with the fold `act` of the statement: on the Weyl orbit of `ρ`
the squared length `qZ` is constantly `620`, so the previous lemma applies. -/
private lemma key (L : List (Fin 8)) (h : e8ht (act L rho) = 620) : act L rho = rho := by
  have hv : qZ (act L rho) = 620 := by rw [qZ_act, qZ_rho]
  have hres := E8_eq_rho_of_qZ_eq_e8ht (act L rho) hv h
  exact hres

theorem E8_weyl_height_eq (L : List (Fin 8))
    (h : (∑ i, ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j *
      (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
        (fun _ => (1 : ℤ))) j) = 620) :
    L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) (fun _ => (1 : ℤ))
      = fun _ => 1 := by
  have hh : e8ht (act L rho) = 620 := by
    unfold act rho
    exact h
  have hk := key L hh
  unfold act rho at hk
  exact hk

end Commons.LinearAlgebra.Matrix.Cartan
