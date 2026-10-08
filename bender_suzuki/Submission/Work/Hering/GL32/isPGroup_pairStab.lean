import Mathlib
import Submission.Work.Hering.GL32.AppIXP0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The stabiliser of a pair of points of `PG(2,2)` is a `2`-group

`GL32 = GL(3,2)` acts on the set `Pair` of unordered pairs of distinct nonzero vectors of
`V = F₂³` (the twenty-one lines of `PG(2,2)`), and `pairStab` is the stabiliser of the standard
pair `p₀ = {e₀, e₁}`.  This file proves

`isPGroup_pairStab : IsPGroup 2 pairStab`,

i.e. every element of the stabiliser has order a power of `2` (in fact of order dividing `4`).

The argument is elementary.  An element `g ∈ pairStab` either fixes `e₀` and `e₁`, or swaps them.

* If `g` fixes both, its matrix with respect to the standard basis `(e₀, e₁, e₂)` is
  `[[1,0,a],[0,1,b],[0,0,1]]` (the last entry is forced by `det g = 1`), and over `F₂` such a
  matrix squares to the identity: `g² = 1`.
* If `g` swaps them, then `g²` fixes both, so `g⁴ = (g²)² = 1` by the previous case.

Hence `g⁸ = 1` (indeed `g⁴ = 1`) for every `g ∈ pairStab`, which is exactly `IsPGroup 2 pairStab`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Hering.GL32

/-- The first basis vector, as a `Pi.single`. -/
lemma e₀_eq_single : e₀ = Pi.single (0 : Fin 3) (1 : ZMod 2) := by decide

/-- The second basis vector, as a `Pi.single`. -/
lemma e₁_eq_single : e₁ = Pi.single (1 : Fin 3) (1 : ZMod 2) := by decide

/-- **A linear automorphism of `F₂³` fixing `e₀` and `e₁` is an involution.**

`g` fixes the plane `⟨e₀,e₁⟩` pointwise, so with respect to the standard basis its matrix is
`[[1,0,a],[0,1,b],[0,0,c]]`; since `det g = 1` and the only unit of `F₂` is `1`, we get `c = 1`.
Such a matrix squares to the identity in characteristic two (the two possibly nonzero off-diagonal
terms are `a + a = 0` and `b + b = 0`). -/
lemma mul_self_eq_one_of_fix (g : GL32) (h0 : g e₀ = e₀) (h1 : g e₁ = e₁) : g * g = 1 := by
  set M : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v) with hM
  -- the first two columns of `M` are `e₀` and `e₁`
  have key0 : ∀ i, M i 0 = (Pi.single (0 : Fin 3) (1 : ZMod 2) : F2v) i := by
    intro i
    have hmv : M.mulVec (Pi.single (0 : Fin 3) (1 : ZMod 2)) =
        Pi.single (0 : Fin 3) (1 : ZMod 2) := by
      rw [hM, LinearMap.toMatrix'_mulVec, ← e₀_eq_single]
      exact h0
    rw [Matrix.mulVec_single_one] at hmv
    exact congrFun hmv i
  have key1 : ∀ i, M i 1 = (Pi.single (1 : Fin 3) (1 : ZMod 2) : F2v) i := by
    intro i
    have hmv : M.mulVec (Pi.single (1 : Fin 3) (1 : ZMod 2)) =
        Pi.single (1 : Fin 3) (1 : ZMod 2) := by
      rw [hM, LinearMap.toMatrix'_mulVec, ← e₁_eq_single]
      exact h1
    rw [Matrix.mulVec_single_one] at hmv
    exact congrFun hmv i
  have h00 : M 0 0 = 1 := by simpa using key0 0
  have h10 : M 1 0 = 0 := by simpa using key0 1
  have h20 : M 2 0 = 0 := by simpa using key0 2
  have h01 : M 0 1 = 0 := by simpa using key1 0
  have h11 : M 1 1 = 1 := by simpa using key1 1
  have h21 : M 2 1 = 0 := by simpa using key1 2
  -- `det M = 1` (the only unit of `F₂`) forces `M 2 2 = 1`
  have hdet : M.det = 1 := by rw [hM]; exact toMatrix'_det_eq_one g
  have h22 : M 2 2 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    rw [h00, h01, h11, h10, h20, h21] at hdet
    simpa using hdet
  -- hence `M * M = 1` (in characteristic two)
  have hMM : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22,
        CharTwo.add_self_eq_zero]
  have hlin : (g : F2v →ₗ[ZMod 2] F2v) * (g : F2v →ₗ[ZMod 2] F2v) = 1 := by
    apply LinearEquiv.injective LinearMap.toMatrix'
    rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_one, ← hM]
    exact hMM
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply]
  show g (g x) = x
  have hx := congrFun (congrArg (fun f : F2v →ₗ[ZMod 2] F2v => (f : F2v → F2v)) hlin) x
  simpa [Module.End.mul_apply] using hx

/-- **The two possible behaviours of an element of `pairStab`**: it either fixes both points of
the standard pair `{e₀,e₁}` or swaps them. -/
lemma fix_or_swap_of_mem_pairStab (g : GL32) (hg : g ∈ pairStab) :
    (g e₀ = e₀ ∧ g e₁ = e₁) ∨ (g e₀ = e₁ ∧ g e₁ = e₀) := by
  have h : pairPerm g p₀ = p₀ := hg
  have h2 : Sym2.mk (ptPerm g p₀pt) (ptPerm g p₁pt) = Sym2.mk p₀pt p₁pt := by
    have hh := congrArg Subtype.val h
    simpa [pairPerm, p₀, mkPair, Sym2.map_mk] using hh
  rcases Sym2.eq_iff.mp h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    refine ⟨?_, ?_⟩
    · have := congrArg Subtype.val ha; simpa [ptPerm_coe, p₀pt_val, p₁pt_val] using this
    · have := congrArg Subtype.val hb; simpa [ptPerm_coe, p₀pt_val, p₁pt_val] using this
  · right
    refine ⟨?_, ?_⟩
    · have := congrArg Subtype.val ha; simpa [ptPerm_coe, p₀pt_val, p₁pt_val] using this
    · have := congrArg Subtype.val hb; simpa [ptPerm_coe, p₀pt_val, p₁pt_val] using this

/-- **Every element of `pairStab` has order dividing `4`.**  In the fixing case it is an involution
(`mul_self_eq_one_of_fix`); in the swapping case its square fixes both points and is therefore an
involution too. -/
lemma pow_four_eq_one_of_mem_pairStab (g : GL32) (hg : g ∈ pairStab) : g ^ 4 = 1 := by
  rcases fix_or_swap_of_mem_pairStab g hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h := mul_self_eq_one_of_fix g h0 h1
    calc g ^ 4 = (g ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      _ = (g * g) * (g * g) := by simp only [pow_two]
      _ = 1 := by rw [h, one_mul]
  · have hsq0 : (g * g) e₀ = e₀ := by rw [LinearEquiv.mul_apply, h0, h1]
    have hsq1 : (g * g) e₁ = e₁ := by rw [LinearEquiv.mul_apply, h1, h0]
    have h := mul_self_eq_one_of_fix (g * g) hsq0 hsq1
    calc g ^ 4 = (g ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      _ = (g * g) * (g * g) := by simp only [pow_two]
      _ = 1 := h

/-- **The stabiliser of the pair `p₀ = {e₀,e₁}` is a `2`-group.**  Every element has order dividing
`4`, hence `g ^ 2 ^ 3 = g ^ 8 = 1`. -/
theorem isPGroup_pairStab : IsPGroup 2 pairStab := by
  intro g
  refine ⟨3, ?_⟩
  have h4 : (g : GL32) ^ 4 = 1 := pow_four_eq_one_of_mem_pairStab (g : GL32) g.2
  have h8 : (g : GL32) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h4, one_pow]
  exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h8)

end Work.Hering.GL32
