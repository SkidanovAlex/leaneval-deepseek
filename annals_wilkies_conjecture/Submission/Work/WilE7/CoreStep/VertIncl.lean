/-
  WilE7 / CoreStep — the **vertical inclusion** `ℝ^{m+1} ↪ ℝ^{0+(n+(m+1))}`.

  `vertIncl n m w` is the vector whose *base* coordinates (the first `n`, inside
  `Fin (0 + (n + (m+1)))`) vanish and whose vertical coordinate at
  `Fin.natAdd 0 (Fin.natAdd n l)` is `w l`.  Equivalently, `vertIncl n m` is the linear section of
  the vertical projection complementary to the base projection `MainDesign.basePrLin n (m+1)`:
  its range is exactly the kernel of that base projection.

  These facts feed the dimension count of `Work.WilE7.CoreStep.verticalJacRank`: the "vertical
  Jacobian" of an absolute `Good` stratum `T` is the full Jacobian `jac T z` precomposed with
  `vertIncl` (see `Work.WilE7.CoreStep.submatrixMulVecComp`), so its rank is
  `(m+1) - dim (ker (jac T z) ⊓ ker (basePrLin n (m+1)))`, and rank–nullity for
  `basePrLin n (m+1)` restricted to `ker (jac T z)` identifies the latter with
  `(N - T.j) - projRank T z`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs

set_option autoImplicit false
noncomputable section
namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The linear inclusion of the last `m+1` coordinates into `ℝ^{0+(n+(m+1))}`: the base
coordinates of `vertIncl n m w` vanish and its vertical coordinate at
`Fin.natAdd 0 (Fin.natAdd n l)` equals `w l`. -/
def vertIncl (n m : ℕ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) where
  toFun w := Fin.addCases (fun j : Fin 0 => j.elim0) (Fin.addCases (fun _ : Fin n => (0 : ℝ)) w)
  map_add' w w' := by
    funext i
    revert i
    refine Fin.addCases (m := 0) (n := n + (m + 1)) ?_ ?_
    · intro j; exact j.elim0
    · intro l
      simp only [Pi.add_apply, Fin.addCases_right]
      revert l
      refine Fin.addCases (m := n) (n := m + 1) ?_ ?_
      · intro j; simp [Fin.addCases_left]
      · intro l; simp [Fin.addCases_right]
  map_smul' c w := by
    funext i
    revert i
    refine Fin.addCases (m := 0) (n := n + (m + 1)) ?_ ?_
    · intro j; exact j.elim0
    · intro l
      simp only [Pi.smul_apply, Fin.addCases_right, smul_eq_mul]
      revert l
      refine Fin.addCases (m := n) (n := m + 1) ?_ ?_
      · intro j; simp [Fin.addCases_left]
      · intro l; simp [Fin.addCases_right]

/-- On the vertical coordinates, `vertIncl n m` is the identity. -/
lemma vertIncl_vert (n m : ℕ) (w : Fin (m + 1) → ℝ) (l : Fin (m + 1)) :
    vertIncl n m w (Fin.natAdd 0 (Fin.natAdd n l)) = w l := by
  simp only [vertIncl, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_right]

/-- On the base coordinates, `vertIncl n m` vanishes. -/
lemma vertIncl_base (n m : ℕ) (w : Fin (m + 1) → ℝ) (j : Fin n) :
    vertIncl n m w (Fin.natAdd 0 (Fin.castAdd (m + 1) j)) = 0 := by
  simp only [vertIncl, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_right, Fin.addCases_left]

/-- Evaluation of the base projection `MainDesign.basePrLin` at a base index. -/
lemma basePrLin_eval (n m : ℕ) (v : Fin (0 + (n + m)) → ℝ) (i : Fin n) :
    basePrLin n m v i = v (Fin.natAdd 0 (Fin.castAdd m i)) := by
  simp only [basePrLin, LinearMap.funLeft_apply, Fin.natAdd_zero]

/-- `vertIncl n m` is injective. -/
lemma vertIncl_injective (n m : ℕ) : Function.Injective (vertIncl n m) := by
  intro w w' h
  funext l
  have h2 := congrFun h (Fin.natAdd 0 (Fin.natAdd n l))
  rw [vertIncl_vert, vertIncl_vert] at h2
  exact h2

/-- The range of `vertIncl n m` is the kernel of the base projection `basePrLin n (m+1)`. -/
lemma vertIncl_range (n m : ℕ) : (vertIncl n m).range = (basePrLin n (m + 1)).ker := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := hv
    rw [LinearMap.mem_ker]
    funext i
    rw [basePrLin_eval]
    exact vertIncl_base n m w i
  · intro hv
    rw [LinearMap.mem_ker] at hv
    refine ⟨fun l => v (Fin.natAdd 0 (Fin.natAdd n l)), ?_⟩
    funext i
    revert i
    refine Fin.addCases (m := 0) (n := n + (m + 1)) ?_ ?_
    · intro j; exact j.elim0
    · intro l
      simp only [vertIncl, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_right]
      revert l
      refine Fin.addCases (m := n) (n := m + 1) ?_ ?_
      · intro j
        simp only [Fin.addCases_left]
        rw [← basePrLin_eval n (m + 1) v j, congrFun hv j]
        simp
      · intro k; simp only [Fin.addCases_right]

end Work.WilE7.CoreStep
