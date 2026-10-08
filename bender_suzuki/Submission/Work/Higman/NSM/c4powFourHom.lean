import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman.NSM

/-- **The fourth-power map of a class-two subgroup covering `A ^ (2)`.**

If `A ≤ C` are subgroups of a group `P` with `C` centralising `A`, `C ^ (2) ≤ A`,
`⁅C, C⁆ = A ^ (2)` and `A` of exponent dividing `4`, then `C` has class two, every commutator
of `C` lies in the abelian group `A`, and the fourth-power map `x ↦ x ^ 4` is a homomorphism
`↥C →* ↥(A ^ (2))`.

Indeed for `x, y ∈ C` we have `(xy)² = [y,x]·x²·y²`; since `[y,x] ∈ A ^ (2)` is an involution
(`A` having exponent `4`) and `x², y² ∈ A` commute with everything in sight, expanding the
square gives `(xy)⁴ = x⁴·y⁴`.  The image lies in `A ^ (2)` because `x⁴ = (x²)²` with `x² ∈ A`. -/
theorem c4powFourHom {P : Type} [Group P] [Finite P] {A C : Subgroup P}
    (hAC : A ≤ C) (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    ∃ f : ↥C →* ↥(Work.Higman.powSub A 2),
      (∀ x : ↥C, (f x : P) = (x : P) ^ 4) := by
  -- `A` is abelian: it is contained in `C`, and `C` centralises `A`.
  have hab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv => (hZ v (hAC hv) u hu).symm
  -- The fourth power is multiplicative on `C`.
  have hpow4 : ∀ x y : P, x ∈ C → y ∈ C → (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
    intro x y hx hy
    -- every element of `A ^ (2) = ⁅C, C⁆` is an involution
    have hVsq : ∀ v ∈ Work.Higman.powSub A 2, v ^ 2 = 1 := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := (Work.Higman.mem_powSub_iff hab).mp hv
      rw [← pow_mul, show 2 * 2 = 4 from rfl]
      exact hexp a ha
    have hcom : ⁅y, x⁆ ∈ A := by
      have h1 : ⁅y, x⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hy hx
      rw [hCd] at h1
      exact Work.Higman.powSub_le (by norm_num) h1
    have hx2 : x ^ 2 ∈ A := hC2 (Work.Higman.pow_mem_powSub (n := 2) hx)
    have hy2 : y ^ 2 ∈ A := hC2 (Work.Higman.pow_mem_powSub (n := 2) hy)
    have hunfold : y * x = ⁅y, x⁆ * x * y := by
      rw [commutatorElement_def]; group
    -- `[y,x]` commutes with `x` (both lie in `C`, `[y,x]` in `A`)
    have hcx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := hZ x hx ⁅y, x⁆ hcom
    have hfinal : x * ⁅y, x⁆ * x * y * y = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      rw [hcx, pow_two, pow_two]; group
    -- `(xy)² = [y,x]·x²·y²`
    have hsq : (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
        _ = x * (⁅y, x⁆ * x * y) * y := by rw [hunfold]
        _ = x * ⁅y, x⁆ * x * y * y := by group
        _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := hfinal
    have hc2 : ⁅y, x⁆ ^ 2 = 1 :=
      hVsq _ (by rw [← hCd]; exact Subgroup.commutator_mem_commutator hy hx)
    calc (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (⁅y, x⁆ * (x ^ 2 * y ^ 2)) ^ 2 := by rw [hsq]
      _ = ⁅y, x⁆ ^ 2 * (x ^ 2 * y ^ 2) ^ 2 :=
            Commute.mul_pow (hab _ hcom _ (A.mul_mem hx2 hy2)) 2
      _ = x ^ 4 * y ^ 4 := by
            rw [hc2, one_mul, Commute.mul_pow (hab _ hx2 _ hy2) 2]
            simp only [← pow_mul, Nat.reduceMul]
  -- The fourth power of an element of `C` lies in `A ^ (2)`.
  have hmem : ∀ x : P, x ∈ C → x ^ 4 ∈ Work.Higman.powSub A 2 := by
    intro x hx
    have h1 : x ^ 2 ∈ A := hC2 (Work.Higman.pow_mem_powSub (n := 2) hx)
    have h2 : (x ^ 2) ^ 2 ∈ Work.Higman.powSub A 2 := Work.Higman.pow_mem_powSub (n := 2) h1
    have h3 : x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h3]; exact h2
  let f : ↥C →* ↥(Work.Higman.powSub A 2) :=
    { toFun := fun x => ⟨(x : P) ^ 4, hmem x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (hpow4 x y x.2 y.2) }
  exact ⟨f, fun x => rfl⟩

end Work.Higman.NSM
