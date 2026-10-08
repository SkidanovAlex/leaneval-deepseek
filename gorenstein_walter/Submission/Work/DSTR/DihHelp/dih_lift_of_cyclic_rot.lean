import Mathlib

namespace Work.DSTR.DihHelp

/-- Auxiliary function underlying the lift: `r i ↦ R i` and `sr i ↦ S * R i`. -/
def dihLiftFun {G : Type*} {m : ℕ} [Mul G] (R : ZMod m → G) (S : G) : DihedralGroup m → G
  | DihedralGroup.r i => R i
  | DihedralGroup.sr i => S * R i

@[simp]
theorem dihLiftFun_r {G : Type*} {m : ℕ} [Mul G] (R : ZMod m → G) (S : G) (i : ZMod m) :
    dihLiftFun R S (DihedralGroup.r i) = R i := rfl

@[simp]
theorem dihLiftFun_sr {G : Type*} {m : ℕ} [Mul G] (R : ZMod m → G) (S : G) (i : ZMod m) :
    dihLiftFun R S (DihedralGroup.sr i) = S * R i := rfl

theorem dih_lift_of_cyclic_rot {G : Type*} [Group G] {m : ℕ} (R : ZMod m → G) (S : G)
    (hR : ∀ i j : ZMod m, R i * R j = R (i + j)) (hS : S * S = 1)
    (hRS : ∀ i : ZMod m, R i * S = S * R (-i)) :
    ∃ F : DihedralGroup m →* G, (∀ i : ZMod m, F (DihedralGroup.r i) = R i) ∧
      (∀ i : ZMod m, F (DihedralGroup.sr i) = S * R i) := by
  have hR0 : R 0 = 1 := by
    have h : R 0 * R 0 = R 0 := by simpa using hR 0 0
    calc R 0 = (R 0)⁻¹ * (R 0 * R 0) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = (R 0)⁻¹ * R 0 := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  refine ⟨{ toFun := dihLiftFun R S,
            map_one' := ?_,
            map_mul' := ?_ }, ?_, ?_⟩
  · show R 0 = 1
    exact hR0
  · intro a b
    match a, b with
    | DihedralGroup.r i, DihedralGroup.r j =>
      show R (i + j) = R i * R j
      exact (hR i j).symm
    | DihedralGroup.r i, DihedralGroup.sr j =>
      show S * R (j - i) = R i * (S * R j)
      rw [(mul_assoc (R i) S (R j)).symm, hRS i, mul_assoc S (R (-i)) (R j), hR (-i) j,
        show (-i + j : ZMod m) = j - i by ring]
    | DihedralGroup.sr i, DihedralGroup.r j =>
      show S * R (i + j) = (S * R i) * R j
      rw [mul_assoc S (R i) (R j), hR i j]
    | DihedralGroup.sr i, DihedralGroup.sr j =>
      show R (j - i) = (S * R i) * (S * R j)
      rw [show (S * R i) * (S * R j) = R (j - i) by
        calc (S * R i) * (S * R j)
            = S * (R i * (S * R j)) := mul_assoc S (R i) (S * R j)
          _ = S * ((R i * S) * R j) := by
                rw [(mul_assoc (R i) S (R j)).symm]
          _ = S * ((S * R (-i)) * R j) := by rw [hRS i]
          _ = S * (S * (R (-i) * R j)) := by rw [mul_assoc S (R (-i)) (R j)]
          _ = (S * S) * (R (-i) * R j) := (mul_assoc S S (R (-i) * R j)).symm
          _ = R (-i) * R j := by rw [hS, one_mul]
          _ = R (-i + j) := hR (-i) j
          _ = R (j - i) := by rw [show (-i + j : ZMod m) = j - i by ring]]
  · intro i
    rfl
  · intro i
    rfl

end Work.DSTR.DihHelp
