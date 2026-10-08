import Mathlib
import Submission.Work.DSTR.trivialOfSqTrivial
import Submission.Work.COPR.Coprime11i

namespace Work.DSTR

theorem invTrickAbelian {V : Type*} [CommGroup V] [Finite V] (hVodd : Odd (Nat.card V))
    {τ ξ : MulAut V} (hτ2 : τ * τ = 1) (hcop : Nat.Coprime (orderOf ξ) (Nat.card V))
    (hξodd : Odd (orderOf ξ)) (hconj : τ * ξ * τ⁻¹ = ξ⁻¹)
    (hfix : ∀ v : V, τ v = v → ξ v = v) : ξ = 1 := by
  -- `τ` is an involution
  have hττ : ∀ v : V, τ (τ v) = v := by
    intro v
    have h := congrArg (fun f : MulAut V => f v) hτ2
    simpa [MulAut.mul_apply] using h
  -- elementwise form of `τ ξ τ⁻¹ = ξ⁻¹`
  have hτξa : ∀ v : V, τ (ξ v) = ξ⁻¹ (τ v) := by
    intro v
    have h := congrArg (fun f : MulAut V => f (τ v)) hconj
    simpa [MulAut.mul_apply] using h
  -- the fixed subgroup of `ξ`
  let D : Subgroup V :=
    { carrier := {x | ξ x = x}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  -- Step 1: `τ x * x` is fixed by `ξ` (it is fixed by `τ`)
  have hAx : ∀ x : V, ξ (τ x * x) = τ x * x := by
    intro x
    apply hfix
    rw [map_mul, hττ x]
    exact mul_comm x (τ x)
  -- Step 2: `τ x * ξ (ξ x)` is fixed by `ξ`
  have hBx : ∀ x : V, ξ (τ x * ξ (ξ x)) = τ x * ξ (ξ x) := by
    intro x
    have h1 := hAx (ξ x)
    rw [hτξa x] at h1
    have h2 : ξ (ξ⁻¹ (τ x) * ξ x) = τ x * ξ (ξ x) := by simp [map_mul]
    have hz : ξ (ξ⁻¹ (τ x) * ξ x) = ξ⁻¹ (τ x) * ξ x := h1
    have heq : ξ⁻¹ (τ x) * ξ x = τ x * ξ (ξ x) := hz.symm.trans h2
    rw [← heq]
    exact h1
  -- Step 3: `ξ (ξ x) * x⁻¹` is fixed by `ξ`, being a quotient of Steps 1 and 2
  have hCx : ∀ x : V, ξ (ξ (ξ x) * x⁻¹) = ξ (ξ x) * x⁻¹ := by
    intro x
    have hA := hAx x
    have hB := hBx x
    have hmem : ξ ((τ x * ξ (ξ x)) * (τ x * x)⁻¹)
        = (τ x * ξ (ξ x)) * (τ x * x)⁻¹ := by
      rw [map_mul, map_inv, hB, hA]
    have heq : (τ x * ξ (ξ x)) * (τ x * x)⁻¹ = ξ (ξ x) * x⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv]
      exact mul_div_mul_left_eq_div (ξ (ξ x)) x (τ x)
    rwa [heq] at hmem
  -- Step 4: `ξ x * x⁻¹` is fixed by `ξ` (odd order kills the square)
  have hξ2 : ∀ x : V, ξ (ξ x) * x⁻¹ ∈ D := by
    intro x
    change ξ (ξ (ξ x) * x⁻¹) = ξ (ξ x) * x⁻¹
    exact hCx x
  have hDfix : ∀ x : V, ξ x * x⁻¹ ∈ D := trivialOfSqTrivial ξ hξ2 hξodd
  have hH : ∀ x : V, ξ (ξ x * x⁻¹) = ξ x * x⁻¹ := by
    intro x
    have h := hDfix x
    change ξ (ξ x * x⁻¹) = ξ x * x⁻¹ at h
    exact h
  -- Step 5: an automorphism of order coprime to `|V|` whose "difference map" `x ↦ ξ x * x⁻¹`
  -- has image inside its own fixed subgroup must be trivial: the element `u = ξ x * x⁻¹`
  -- satisfies `ξ^k x = u^k x`, so `u ^ orderOf ξ = 1`, and `(orderOf u, |V|) = 1`.
  apply MulEquiv.ext
  intro x
  simp only [MulAut.one_apply]
  set u : V := ξ x * x⁻¹ with hu
  have hufix : ξ u = u := hH x
  have hux : u * x = ξ x := by rw [hu]; group
  have hpow : ∀ k : ℕ, (ξ ^ k) x = u ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hufix]
      rw [← hux, pow_succ, ← mul_assoc]
  have hum : u ^ orderOf ξ = 1 := by
    have h1 := hpow (orderOf ξ)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
    have h2 : u ^ orderOf ξ * x = 1 * x := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  have hcomp : Nat.Coprime (orderOf u) (Nat.card V) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hum) hcop
  have hone : orderOf u = 1 := hcomp.eq_one_of_dvd (orderOf_dvd_natCard u)
  have hu1 : u = 1 := orderOf_eq_one_iff.mp hone
  rw [← hux, hu1, one_mul]

end Work.DSTR
