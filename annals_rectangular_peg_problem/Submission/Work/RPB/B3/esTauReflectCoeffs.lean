import Mathlib

/-!
# Coefficients for the `τ`-reflection

For every `N` we exhibit `N+1` distinct points `c j ∈ (-1, 0)` and real coefficients `a j`
such that the first `N+1` moments of the signed measure `∑ a j δ_{c j}` all equal `1`:

`∑ j, a j * (c j)^m = 1` for all `m ≤ N`.

The points are chosen explicitly, `c j = -((j:ℝ)+1)/((N:ℝ)+2)`, and the existence of the
coefficients is the invertibility of the (transposed) Vandermonde matrix of the nodes `c`,
i.e. `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` together with the fact that an
injective linear endomorphism of a finite-dimensional space is surjective.
-/

namespace Work.RPB.B3

theorem esTauReflectCoeffs (N : ℕ) :
    ∃ (c a : Fin (N+1) → ℝ), (∀ j, c j ∈ Set.Ioo (-1) 0) ∧ Function.Injective c ∧
      (∀ m : ℕ, m ≤ N → ∑ j, a j * (c j)^m = 1) := by
  let c : Fin (N+1) → ℝ := fun j => -((j:ℝ) + 1) / ((N:ℝ) + 2)
  have hc_mem : ∀ j, c j ∈ Set.Ioo (-1) 0 := by
    intro j
    constructor
    · have hlt1 : ((j:ℝ)+1)/((N:ℝ)+2) < 1 := by
        apply (div_lt_one (by positivity : (0:ℝ) < (N:ℝ)+2)).mpr
        have hcast : (j:ℝ) < (N:ℝ) + 1 := by
          have := j.isLt; exact_mod_cast this
        linarith
      simp only [c]
      rw [neg_div]
      linarith
    · have hx : (0:ℝ) < ((j:ℝ)+1)/((N:ℝ)+2) := div_pos (by positivity) (by positivity)
      simp only [c]
      rw [neg_div]
      linarith
  have hc_inj : Function.Injective c := by
    intro i j hij
    have hden : ((N:ℝ)+2) ≠ 0 := by positivity
    have h1 : ((i:ℝ)+1)/((N:ℝ)+2) = ((j:ℝ)+1)/((N:ℝ)+2) := by
      have := hij
      simp only [c, neg_div] at this
      exact neg_inj.mp this
    have h2 : ((i:ℝ)+1) = ((j:ℝ)+1) := by
      field_simp at h1
      linarith
    have h3 : (i:ℝ) = (j:ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h3)
  let T : (Fin (N+1) → ℝ) →ₗ[ℝ] (Fin (N+1) → ℝ) :=
  { toFun := fun a m => ∑ j, a j * c j ^ (m:ℕ)
    map_add' := by
      intro a b
      funext m
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      funext m
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring }
  have hT : ∀ a m, T a m = ∑ j, a j * c j ^ (m:ℕ) := fun a m => rfl
  have hinj : Function.Injective T := by
    intro a b hab
    have h0 : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hz : a - b = 0 := by
      apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hc_inj
      intro i
      have := congrFun h0 i
      rw [hT] at this
      simpa using this
    simpa using sub_eq_zero.mp hz
  have hsurj : Function.Surjective T := LinearMap.surjective_of_injective hinj
  obtain ⟨a, ha⟩ := hsurj (fun _ => 1)
  refine ⟨c, a, hc_mem, hc_inj, ?_⟩
  intro m hm
  have := congrFun ha ⟨m, Nat.lt_succ_of_le hm⟩
  rw [hT] at this
  simpa using this

end Work.RPB.B3
