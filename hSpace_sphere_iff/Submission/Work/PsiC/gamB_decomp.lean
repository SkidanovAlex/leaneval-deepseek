import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.gamB_decomp` — the six-fold spectral projector of `gamB`

`gamB n = (cB n)⁻¹ * sB n` is a six-cycle of the tensor positions (`IB n`): its square is the
pair cycle `cB n`, its cube is the product `sB n` of the three pair swaps, hence its sixth power
is `1`.  Consequently the genuine (six-term) spectral projector `cycProj6 n μ` of `gamB` is the
product of the three-term projector `cycProj (cB n) (μ²)` of `cB = gamB²` and of the two-term
projector `halfProj (μ³) (sB n)` of `sB = gamB³`: the `μ`-eigenspace of `γ` is the intersection
of the `μ²`-eigenspace of `γ²` and the `μ³`-eigenspace of `γ³`.

The proof is a computation with powers of a single element `γ` of order six:
`(1/3)(1 + μ⁻²γ² + μ⁻⁴γ⁴)·(1/2)(1 + μ³γ³) = (1/6)(1 + μ⁻¹γ + μ⁻²γ² + … + μ⁻⁵γ⁵)`,
where `μ³ = μ⁻³` and `μ = μ⁻⁵` because `μ⁶ = 1`.  This is `GamBDecomp.six_decomp` below (an identity in an
arbitrary `ℂ`-algebra, so it applies to matrices over a possibly non-commutative ring `A`), which
is then transported to `gamB` via the `orbitSpec` formulation of the two projectors.
-/

namespace Work.PsiC

open Matrix

namespace GamBDecomp

/-! ## The six-cycle `gamB` and its powers -/

/-- `(cB n)⁻¹` pointwise: it rotates the three pairs forwards. -/
theorem cB_symm_apply (n : ℕ) (a b c d e f : Fin n) :
    (Work.KT.PsiC.cB n)⁻¹ (((a, b), (c, d)), (e, f)) = (((c, d), (e, f)), (a, b)) := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact (Work.KT.PsiC.cB_apply n c d e f a b).symm

/-- `gamB n` pointwise: it moves the second entry of each pair one pair forwards. -/
theorem gamB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.gamB n (((a, b), (c, d)), (e, f)) = (((d, c), (f, e)), (b, a)) := by
  show ((Work.KT.PsiC.cB n)⁻¹ * Work.KT.PsiC.sB n) (((a, b), (c, d)), (e, f)) = _
  rw [Equiv.Perm.mul_apply, Work.KT.PsiC.sB_apply, cB_symm_apply]

/-- `gamB n` squares to the pair cycle `cB n`. -/
theorem gamB_sq (n : ℕ) : Work.KT.PsiC.gamB n * Work.KT.PsiC.gamB n = Work.KT.PsiC.cB n := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  show Work.KT.PsiC.gamB n (Work.KT.PsiC.gamB n (((a, b), (c, d)), (e, f))) = _
  rw [gamB_apply n a b c d e f, gamB_apply n d c f e b a,
    Work.KT.PsiC.cB_apply n a b c d e f]

/-- `gamB n` cubes to the product `sB n` of the three pair swaps. -/
theorem gamB_cube (n : ℕ) : (Work.KT.PsiC.gamB n) ^ 3 = Work.KT.PsiC.sB n := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  show Work.KT.PsiC.gamB n (Work.KT.PsiC.gamB n (Work.KT.PsiC.gamB n
    (((a, b), (c, d)), (e, f)))) = _
  rw [gamB_apply n a b c d e f, gamB_apply n d c f e b a, gamB_apply n e f a b c d,
    Work.KT.PsiC.sB_apply n a b c d e f]

/-- `gamB n` has order six. -/
theorem gamB_pow_six (n : ℕ) : (Work.KT.PsiC.gamB n) ^ 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two, gamB_sq]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two, pow_one, Work.KT.PsiC.cB_cube]

/-! ## The same statements for the permutation matrices -/

/-- `(cB n).permMatrix = ((gamB n).permMatrix)²`. -/
theorem cB_permMatrix_eq (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) :
    (Work.KT.PsiC.cB n).permMatrix A = ((Work.KT.PsiC.gamB n).permMatrix A) ^ 2 := by
  rw [Work.KT.PsiC.permMatrix_pow (A := A) (Work.KT.PsiC.gamB n) 2, pow_two, gamB_sq]

/-- `(sB n).permMatrix = ((gamB n).permMatrix)³`. -/
theorem sB_permMatrix_eq (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) :
    (Work.KT.PsiC.sB n).permMatrix A = ((Work.KT.PsiC.gamB n).permMatrix A) ^ 3 := by
  rw [Work.KT.PsiC.permMatrix_pow (A := A) (Work.KT.PsiC.gamB n) 3, gamB_cube]

/-- `((gamB n).permMatrix)⁶ = 1`. -/
theorem gamB_permMatrix_pow_six (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) :
    ((Work.KT.PsiC.gamB n).permMatrix A) ^ 6 = 1 := by
  rw [Work.KT.PsiC.permMatrix_pow, gamB_pow_six, Matrix.permMatrix_one]

/-! ## The abstract computation in a `ℂ`-algebra -/

/-- The two-term spectral projector of a cyclic action, expanded. -/
theorem orbitSpec_two {M : Type} [Ring M] [Algebra ℂ M] (lam : ℂ) (g : M) :
    Work.KT.Psi.orbitSpec lam g 2 = (2 : ℂ)⁻¹ • (1 + lam⁻¹ • g) := by
  simp only [Work.KT.Psi.orbitSpec, Work.KT.Psi.geoSum, Work.KT.Psi.qg, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  norm_num

/-- **The key identity.**  For an element `g` of order six and `y⁶ = 1`, the `y`-projector of `g`
factors as the product of the `y²`-projector of `g²` and the `y³`-projector of `g³`. -/
theorem six_decomp {M : Type} [Ring M] [Algebra ℂ M] (g : M) (hg : g ^ 6 = 1) (y : ℂ)
    (hy : y ^ 6 = 1) :
    ((3 : ℂ)⁻¹ • (1 + y ^ 2 • g ^ 2 + y ^ 4 • g ^ 4)) * ((2 : ℂ)⁻¹ • (1 + y ^ 3 • g ^ 3)) =
      (6 : ℂ)⁻¹ • (1 + y • g + y ^ 2 • g ^ 2 + y ^ 3 • g ^ 3 + y ^ 4 • g ^ 4 + y ^ 5 • g ^ 5) := by
  have hg7 : g ^ 7 = g := by
    rw [show (7 : ℕ) = 6 + 1 from rfl, pow_add, hg, one_mul, pow_one]
  have hy7 : y ^ 7 = y := by
    rw [show (7 : ℕ) = 6 + 1 from rfl, pow_add, hy, one_mul, pow_one]
  have hcross1 : (y ^ 2 • g ^ 2) * (y ^ 3 • g ^ 3) = y ^ 5 • g ^ 5 := by
    rw [smul_mul_smul, show y ^ 2 * y ^ 3 = y ^ 5 by ring,
      show g ^ 2 * g ^ 3 = g ^ 5 by rw [← pow_add]]
  have hcross2 : (y ^ 4 • g ^ 4) * (y ^ 3 • g ^ 3) = y • g := by
    rw [smul_mul_smul, show y ^ 4 * y ^ 3 = y ^ 7 by ring, hy7,
      show g ^ 4 * g ^ 3 = g ^ 7 by rw [← pow_add], hg7]
  have hexp : (1 + y ^ 2 • g ^ 2 + y ^ 4 • g ^ 4) * (1 + y ^ 3 • g ^ 3)
      = 1 + y ^ 3 • g ^ 3 + y ^ 2 • g ^ 2 + y ^ 5 • g ^ 5 + y ^ 4 • g ^ 4 + y • g := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [hcross1, hcross2]
    abel
  rw [smul_mul_smul, show (3 : ℂ)⁻¹ * (2 : ℂ)⁻¹ = (6 : ℂ)⁻¹ by norm_num, hexp]
  congr 1
  abel

/-- The same identity, in terms of `orbitSpec`. -/
theorem orbitSpec_six_decomp {M : Type} [Ring M] [Algebra ℂ M] (g : M) (hg : g ^ 6 = 1)
    (lam : ℂ) (hlam : lam ^ 6 = 1) :
    Work.KT.Psi.orbitSpec lam g 6 =
      Work.KT.Psi.orbitSpec (lam ^ 2) (g ^ 2) 3 * Work.KT.Psi.orbitSpec (lam ^ 3) (g ^ 3) 2 := by
  have hy6 : (lam⁻¹) ^ 6 = 1 := by rw [inv_pow, hlam, inv_one]
  have hL : Work.KT.Psi.orbitSpec lam g 6 =
      (6 : ℂ)⁻¹ • (1 + lam⁻¹ • g + (lam⁻¹)^2 • g^2 + (lam⁻¹)^3 • g^3 +
        (lam⁻¹)^4 • g^4 + (lam⁻¹)^5 • g^5) := by
    have hsum : (∑ j ∈ Finset.range 6, Work.KT.Psi.qg lam g ^ j) =
        ∑ j ∈ Finset.range 6, (lam⁻¹)^j • g^j :=
      Finset.sum_congr rfl fun j _ => Work.KT.Psi.qg_pow lam g j
    simp only [Work.KT.Psi.orbitSpec, Work.KT.Psi.geoSum, hsum, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, pow_one, one_smul, zero_add]
    abel
  have hR : Work.KT.Psi.orbitSpec (lam ^ 2) (g ^ 2) 3 *
        Work.KT.Psi.orbitSpec (lam ^ 3) (g ^ 3) 2 =
      ((3 : ℂ)⁻¹ • (1 + (lam⁻¹)^2 • g^2 + (lam⁻¹)^4 • g^4)) *
        ((2 : ℂ)⁻¹ • (1 + (lam⁻¹)^3 • g^3)) := by
    rw [Work.KT.PsiC.orbitSpec_three, orbitSpec_two]
    rw [show (lam ^ 2)⁻¹ = (lam⁻¹)^2 from (inv_pow lam 2).symm,
      show (lam ^ 3)⁻¹ = (lam⁻¹)^3 from (inv_pow lam 3).symm,
      show ((lam⁻¹)^2)^2 = (lam⁻¹)^4 by ring, show (g ^ 2)^2 = g ^ 4 by rw [← pow_mul]]
  rw [hL, hR, six_decomp g hg lam⁻¹ hy6]

/-- `cycProj6` is the `orbitSpec` projector of the six-cycle `gamB`. -/
theorem cycProj6_eq_orbitSpec (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (mu : ℂ) :
    (Work.KT.PsiC.cycProj6 (A := A) n mu : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) =
      Work.KT.Psi.orbitSpec mu ((Work.KT.PsiC.gamB n).permMatrix A) 6 := by
  have hsum : (∑ j ∈ Finset.range 6,
        Work.KT.Psi.qg mu ((Work.KT.PsiC.gamB n).permMatrix A) ^ j) =
      ∑ k ∈ Finset.range 6, (mu⁻¹)^k • ((Work.KT.PsiC.gamB n).permMatrix A)^k :=
    Finset.sum_congr rfl fun j _ => Work.KT.Psi.qg_pow mu _ j
  have hsum2 : (∑ k ∈ Finset.range 6,
        algebraMap ℂ A (mu⁻¹ ^ k) • ((Work.KT.PsiC.gamB n).permMatrix A) ^ k) =
      ∑ k ∈ Finset.range 6, (mu⁻¹)^k • ((Work.KT.PsiC.gamB n).permMatrix A)^k :=
    Finset.sum_congr rfl fun k _ => Work.KT.PsiC.smulA_eq_smulC (mu⁻¹ ^ k) _
  simp only [Work.KT.PsiC.cycProj6, Work.KT.Psi.orbitSpec, Work.KT.Psi.geoSum]
  rw [hsum, hsum2, show ((1 : ℂ) / 6) = (6 : ℂ)⁻¹ by norm_num,
    Work.KT.PsiC.smulA_eq_smulC]
  norm_num

end GamBDecomp

/-! ## The target -/

theorem gamB_decomp (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (mu : ℂ) (hmu : mu ^ 6 = 1) :
    (Work.KT.PsiC.cycProj6 (A := A) n mu : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) =
      Work.KT.PsiC.cycProj (Work.KT.PsiC.cB n) (mu ^ 2) *
        Work.KT.PsiC.halfProj (mu ^ 3) (Work.KT.PsiC.sB n) := by
  have hmu3 : (mu ^ 3) ^ 2 = 1 := by rw [← pow_mul, show 3 * 2 = 6 from rfl, hmu]
  calc (Work.KT.PsiC.cycProj6 (A := A) n mu)
      = Work.KT.Psi.orbitSpec mu ((Work.KT.PsiC.gamB n).permMatrix A) 6 :=
        GamBDecomp.cycProj6_eq_orbitSpec A n mu
    _ = Work.KT.Psi.orbitSpec (mu ^ 2) (((Work.KT.PsiC.gamB n).permMatrix A) ^ 2) 3 *
          Work.KT.Psi.orbitSpec (mu ^ 3) (((Work.KT.PsiC.gamB n).permMatrix A) ^ 3) 2 :=
        GamBDecomp.orbitSpec_six_decomp ((Work.KT.PsiC.gamB n).permMatrix A)
          (GamBDecomp.gamB_permMatrix_pow_six A n) mu hmu
    _ = Work.KT.PsiC.cycProj (Work.KT.PsiC.cB n) (mu ^ 2) *
          Work.KT.PsiC.halfProj (mu ^ 3) (Work.KT.PsiC.sB n) := by
        rw [Work.KT.PsiC.cycProj_eq_orbitSpec (A := A) (Work.KT.PsiC.cB n) (mu ^ 2),
          Work.KT.PsiC.halfProj_eq_orbitSpec (A := A) (Work.KT.PsiC.sB n) (mu ^ 3) hmu3,
          GamBDecomp.cB_permMatrix_eq A n, GamBDecomp.sB_permMatrix_eq A n]

end Work.PsiC
