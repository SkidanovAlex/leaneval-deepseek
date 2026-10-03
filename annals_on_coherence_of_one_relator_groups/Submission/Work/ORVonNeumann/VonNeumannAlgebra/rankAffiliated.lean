/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The extended rank function on the algebra of affiliated operators

For a countable group `G`, `U(G) = N(G)[(nzd)⁻¹]` is the Ore localisation of the group von
Neumann algebra `N(G)` at its set of non-zero-divisors.  The extended dimension function
`rk_G` of Jaikin-Zapirain–López-Álvarez (`The Atiyah conjecture for locally indicable groups`,
arXiv:1810.12135, §3.2) is the extension of the dimension function of `N(G)` to `U(G)`;
it is a *faithful* Sylvester matrix rank function.

Here we build the extension **algebraically**, from the following two inputs:

* the Sylvester rank function `rk` on `R = N(G)` (`Work.ORVonNeumann.Rep.vnRankFunction`),
  which is faithful;
* the fact that multiplication by a non-zero-divisor *on the left* (resp. right) of the
  `i`-th row (resp. `j`-th column) of a matrix does not change the rank
  (`Work.ORVonNeumann.Rep.rank_mul_diagonal_left`, `..._right`).

The construction: every matrix `A` over `R[S⁻¹]` has a *row presentation*
`A = diag (d₁,…,dₙ)⁻¹ · C` with `dᵢ ∈ S` and `C` a matrix over `R`; the extension is
`rk'(A) = rk(C)`.  Well-definedness of this value is the statement that two presentations of
the same matrix have numerators of the same rank, which uses only that the multipliers can be
taken to be non-zero-divisors (`Work.ORVonNeumann.mem_nonZeroDivisors_of_mul_eq`) together
with the rank invariance of the first input.  The axioms are then proved by computing
presentations of `A * B`, `blockDiag A B` and `blockUpper A C B` from presentations of the
parts.

## Main results

* `Work.ORVonNeumann.Ext.exists_sylvesterRankFunction_oreLocalization` — the extension
  exists and is faithful;
* `Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated` — the unconditional statement for
  `U(G)`, `G` countable.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.rank_vonNeumann
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.UStar
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumannOre
import Submission.Work.ORVonNeumann.Rep.oreCommonDenom
import Submission.Work.ORVonNeumann.Rep.rank_conjTranspose
import Submission.Work.ORVonNeumann.Rep.rank_mul_diagonal_left
import Submission.Work.ORVonNeumann.Rep.rank_mul_diagonal_right
import Submission.Work.ORVonNeumann.mem_nonZeroDivisors_of_mul_mem
import Submission.Work.ORVonNeumann.mem_nonZeroDivisors_of_mul_eq
import Submission.Work.ORVonNeumann.Rank.rank_eq_zero_iff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ORVonNeumann.Ext

open OreLocalization

universe u

variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]

/-! ### The numerator map and the inverse of a denominator -/

/-- The canonical map `R → R[S⁻¹]`. -/
noncomputable abbrev numU : R →+* OreLocalization S R := OreLocalization.numeratorRingHom

/-- The inverse in `R[S⁻¹]` of the image of `s ∈ S`. -/
noncomputable def invU (s : S) : OreLocalization S R :=
  (((OreLocalization.numeratorUnit (S := S) s)⁻¹ : (OreLocalization S R)ˣ) : OreLocalization S R)

theorem invU_def (s : S) : invU (S := S) s = ((1 : R) /ₒ s) := rfl

theorem invU_mul (s : S) : invU (S := S) s * numU (S := S) (s : R) = 1 := by
  show (↑((OreLocalization.numeratorUnit (S := S) s)⁻¹) : OreLocalization S R) *
      (↑(OreLocalization.numeratorUnit (S := S) s) : OreLocalization S R) = 1
  exact Units.inv_mul _

theorem mul_invU (s : S) : numU (S := S) (s : R) * invU (S := S) s = 1 := by
  show (↑(OreLocalization.numeratorUnit (S := S) s) : OreLocalization S R) *
      (↑((OreLocalization.numeratorUnit (S := S) s)⁻¹) : OreLocalization S R) = 1
  exact Units.mul_inv _

theorem invU_mul_invU (s t : S) :
    invU (S := S) s * invU (S := S) t = invU (S := S) (t * s) := by
  rw [invU_def, invU_def, invU_def]
  rw [OreLocalization.one_div_mul]

theorem oreDiv_eq_invU_mul (a : R) (s : S) :
    (a /ₒ s : OreLocalization S R) = invU (S := S) s * numU (S := S) a := by
  show (a /ₒ s : OreLocalization S R) = ((1 : R) /ₒ s) * (a /ₒ 1)
  rw [OreLocalization.one_div_mul, one_mul]

theorem numU_injective (hS : S ≤ nonZeroDivisors R) : Function.Injective (numU (S := S)) :=
  OreLocalization.numeratorHom_inj (hS.trans (fun _ hx => (mem_nonZeroDivisors_iff.mp hx).1))

/-! ### Matrices over the localization -/

/-- The entrywise image of a matrix over `R` in matrices over `R[S⁻¹]`. -/
noncomputable def numMat {n m : ℕ} (C : Matrix (Fin n) (Fin m) R) :
    Matrix (Fin n) (Fin m) (OreLocalization S R) :=
  C.map (numU (S := S))

theorem numMat_apply {n m : ℕ} (C : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    numMat (S := S) C i j = numU (S := S) (C i j) := rfl

theorem numMat_mul {n m k : ℕ} (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin m) (Fin k) R) :
    numMat (S := S) (C * D) = numMat (S := S) C * numMat (S := S) D :=
  Matrix.map_mul (f := numU (S := S))

theorem numMat_zero {n m : ℕ} :
    numMat (S := S) (0 : Matrix (Fin n) (Fin m) R) = 0 := by
  ext i j
  simp only [numMat_apply, Matrix.zero_apply, map_zero]

theorem diag_mul_eq {n m : ℕ} (x : Fin n → R) (C : Matrix (Fin n) (Fin m) R) :
    Matrix.diagonal x * C = (fun i j => x i * C i j) := by
  ext i j
  rw [Matrix.diagonal_mul]

theorem mul_diag_eq {n m : ℕ} (y : Fin m → R) (C : Matrix (Fin n) (Fin m) R) :
    C * Matrix.diagonal y = (fun i j => C i j * y j) := by
  ext i j
  rw [Matrix.mul_diagonal]

theorem invU_eq_of_eq {e s : S} {t : R} (h : (e : R) = t * (s : R)) :
    invU (S := S) s = invU (S := S) e * numU (S := S) t := by
  have h1 : numU (S := S) (e : R) = numU (S := S) t * numU (S := S) (s : R) := by
    rw [h, map_mul]
  have h2 : invU (S := S) e * numU (S := S) t * numU (S := S) (s : R) = 1 := by
    rw [mul_assoc, ← h1, invU_mul]
  calc invU (S := S) s
      = (invU (S := S) e * numU (S := S) t * numU (S := S) (s : R)) * invU (S := S) s := by
          rw [h2, one_mul]
    _ = invU (S := S) e * numU (S := S) t * (numU (S := S) (s : R) * invU (S := S) s) := by
          noncomm_ring
    _ = invU (S := S) e * numU (S := S) t := by rw [mul_invU, mul_one]

theorem numU_mul_invU_eq {s y : S} {a r : R} (h : (s : R) * a = r * (y : R)) :
    numU (S := S) a * invU (S := S) y = invU (S := S) s * numU (S := S) r := by
  have h1 : numU (S := S) (s : R) * numU (S := S) a
      = numU (S := S) r * numU (S := S) (y : R) := by
    rw [← map_mul, ← map_mul, h]
  calc numU (S := S) a * invU (S := S) y
      = (invU (S := S) s * numU (S := S) (s : R)) * numU (S := S) a * invU (S := S) y := by
          rw [invU_mul, one_mul]
    _ = invU (S := S) s * (numU (S := S) (s : R) * numU (S := S) a) * invU (S := S) y := by
          noncomm_ring
    _ = invU (S := S) s * (numU (S := S) r * numU (S := S) (y : R)) * invU (S := S) y := by
          rw [h1]
    _ = invU (S := S) s * numU (S := S) r * (numU (S := S) (y : R) * invU (S := S) y) := by
          noncomm_ring
    _ = invU (S := S) s * numU (S := S) r := by rw [mul_invU, mul_one]

theorem numMat_injective (hS : S ≤ nonZeroDivisors R) {n m : ℕ} :
    Function.Injective (numMat (S := S) : Matrix (Fin n) (Fin m) R →
      Matrix (Fin n) (Fin m) (OreLocalization S R)) := by
  intro C D h
  ext i j
  exact numU_injective hS (by simpa [numMat_apply] using congrArg (fun M => M i j) h)

/-! ### Row presentations

A matrix `A` over `R[S⁻¹]` is presented by a row-denominator function `x : Fin n → S` and a
matrix `C` over `R` if `A = diag (invU ∘ x) * numMat C`, i.e. entrywise
`A i j = invU (x i) * numU (C i j)`. -/

/-- The diagonal matrix `diag (invU ∘ x)` over the localization. -/
noncomputable def diagInv {n : ℕ} (x : Fin n → S) : Matrix (Fin n) (Fin n) (OreLocalization S R) :=
  Matrix.diagonal fun i => invU (S := S) (x i)

theorem diagInv_apply {n : ℕ} (x : Fin n → S) (i j : Fin n) :
    diagInv (S := S) x i j = if i = j then invU (S := S) (x i) else 0 := by
  rw [diagInv, Matrix.diagonal_apply]

theorem diagInv_mul {n : ℕ} (x y : Fin n → S) :
    diagInv (S := S) x * diagInv (S := S) y = diagInv (S := S) (fun i => y i * x i) := by
  rw [diagInv, diagInv, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact invU_mul_invU (S := S) (x i) (y i)

/-- A row presentation of a matrix over the localization: the denominators `x i ∈ S` of the
rows and the numerator matrix `C` over `R`. -/
def IsPres {n m : ℕ} (A : Matrix (Fin n) (Fin m) (OreLocalization S R)) (x : Fin n → S)
    (C : Matrix (Fin n) (Fin m) R) : Prop :=
  A = diagInv (S := S) x * numMat (S := S) C

theorem isPres_iff {n m : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)} {x : Fin n → S}
    {C : Matrix (Fin n) (Fin m) R} :
    IsPres (S := S) A x C ↔ ∀ i j, A i j = invU (S := S) (x i) * numU (S := S) (C i j) := by
  constructor
  · intro h i j
    rw [IsPres] at h
    rw [h, diagInv, Matrix.diagonal_mul, numMat_apply]
  · intro h
    rw [IsPres]
    ext i j
    rw [diagInv, Matrix.diagonal_mul, numMat_apply]
    exact h i j

/-- **Refining a presentation**: multiplying the numerator matrix on the `i`-th row by `z i`
and replacing the denominator `x i` by `y i` with `y i = z i * x i` yields a presentation with
the same underlying matrix. -/
theorem IsPres.refine {n m : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)} {x : Fin n → S}
    {C : Matrix (Fin n) (Fin m) R} (h : IsPres (S := S) A x C) {y : Fin n → S} {z : Fin n → R}
    (hz : ∀ i, (y i : R) = z i * (x i : R)) :
    IsPres (S := S) A y (fun i j => z i * C i j) := by
  have h' : ∀ i j, A i j = invU (S := S) (x i) * numU (S := S) (C i j) :=
    (isPres_iff (S := S)).mp h
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  have key : numU (S := S) (x i) * A i j = numU (S := S) (C i j) := by
    rw [h' i j, ← mul_assoc, mul_invU, one_mul]
  have hy : numU (S := S) (y i) = numU (S := S) (z i) * numU (S := S) (x i) := by
    rw [show (y i : R) = z i * (x i : R) from hz i, map_mul]
  calc A i j
      = (invU (S := S) (y i) * numU (S := S) (y i)) * A i j := by rw [invU_mul, one_mul]
    _ = (invU (S := S) (y i) * (numU (S := S) (z i) * numU (S := S) (x i))) * A i j := by
          rw [hy]
    _ = invU (S := S) (y i) * numU (S := S) (z i) * (numU (S := S) (x i) * A i j) := by
          noncomm_ring
    _ = invU (S := S) (y i) * numU (S := S) (z i) * numU (S := S) (C i j) := by rw [key]
    _ = invU (S := S) (y i) * (numU (S := S) (z i) * numU (S := S) (C i j)) := by noncomm_ring
    _ = invU (S := S) (y i) * numU (S := S) (z i * C i j) := by rw [map_mul]

theorem isPres_zero {n m : ℕ} :
    IsPres (S := S) (0 : Matrix (Fin n) (Fin m) (OreLocalization S R)) (fun _ => 1)
      (0 : Matrix (Fin n) (Fin m) R) := by
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  simp

theorem isPres_one :
    IsPres (S := S) (1 : Matrix (Fin 1) (Fin 1) (OreLocalization S R)) (fun _ => 1)
      (1 : Matrix (Fin 1) (Fin 1) R) := by
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have h1 : invU (S := S) (1 : S) = 1 := by
    have h := invU_mul (S := S) (1 : S)
    rw [Submonoid.coe_one, map_one, mul_one] at h
    exact h
  have h2 : ((1 : Matrix (Fin 1) (Fin 1) (OreLocalization S R)) i i) = 1 := by
    rw [Matrix.one_apply, if_pos rfl]
  have h3 : ((1 : Matrix (Fin 1) (Fin 1) R) i i) = 1 := by
    rw [Matrix.one_apply, if_pos rfl]
  rw [h2, h3, h1, map_one, one_mul]

/-! ### Existence of presentations -/

theorem exists_isPres (hS : S ≤ nonZeroDivisors R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (OreLocalization S R)) :
    ∃ (x : Fin n → S) (C : Matrix (Fin n) (Fin m) R), IsPres (S := S) A x C := by
  have h1 : ∀ i : Fin n, ∃ (a : Fin m → R) (s : Fin m → S),
      ∀ j, A i j = (a j /ₒ s j : OreLocalization S R) := by
    intro i
    choose a s has using fun j : Fin m =>
      OreLocalization.ind (β := fun q => ∃ (a : R) (s : S), q = (a /ₒ s : OreLocalization S R))
        (fun r t => ⟨r, t, rfl⟩) (A i j)
    exact ⟨a, s, has⟩
  choose a s has using h1
  have h2 : ∀ i : Fin n, ∃ (e : S) (b : Fin m → R),
      ∀ j, A i j = (b j /ₒ e : OreLocalization S R) := by
    intro i
    obtain ⟨e, t, b, -, hb⟩ := Work.ORVonNeumann.Rep.oreCommonDenom (S := S) hS (a i) (s i)
    exact ⟨e, b, fun j => (has i j).trans (hb j)⟩
  choose x b hb using h2
  refine ⟨x, b, ?_⟩
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  rw [hb i j, oreDiv_eq_invU_mul]

/-- A common denominator for two rows: two denominators `s`, `t` in `S` have a common left
multiple in `S`, and both multipliers can be chosen to be non-zero-divisors. -/
theorem exists_commonDenom_pair (hS : S ≤ nonZeroDivisors R) (s t : S) :
    ∃ (e : S) (u v : R), u ∈ nonZeroDivisors R ∧ v ∈ nonZeroDivisors R ∧
      (e : R) = u * (s : R) ∧ (e : R) = v * (t : R) := by
  obtain ⟨r', s', hore⟩ := OreLocalization.oreCondition (r := (t : R)) (s := s)
  refine ⟨⟨(s' : R) * (t : R), S.mul_mem s'.2 t.2⟩, r', s', ?_, hS s'.2,
    hore, rfl⟩
  exact Work.ORVonNeumann.mem_nonZeroDivisors_of_mul_eq (S := S) hS s'.2 t.2 s.2 hore

/-! ### Well-definedness of the rank of a presentation -/

theorem isPres_rank_eq (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    {n m : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)}
    {x x' : Fin n → S} {C C' : Matrix (Fin n) (Fin m) R}
    (h : IsPres (S := S) A x C) (h' : IsPres (S := S) A x' C') : rk.rank C = rk.rank C' := by
  have hpair : ∀ i : Fin n, ∃ (e : S) (u v : R),
      u ∈ nonZeroDivisors R ∧ v ∈ nonZeroDivisors R ∧
      (e : R) = u * (x i : R) ∧ (e : R) = v * (x' i : R) :=
    fun i => exists_commonDenom_pair (S := S) hS (x i) (x' i)
  choose e u v hu hv hue hve using hpair
  have hC : IsPres (S := S) A e (fun i j => u i * C i j) := h.refine hue
  have hC' : IsPres (S := S) A e (fun i j => v i * C' i j) := h'.refine hve
  have hCe := (isPres_iff (S := S)).mp hC
  have hC'e := (isPres_iff (S := S)).mp hC'
  have heq : (fun i j => u i * C i j) = (fun i j => v i * C' i j) := by
    funext i j
    refine numU_injective hS ?_
    have h2 : invU (S := S) (e i) * numU (S := S) (u i * C i j)
        = invU (S := S) (e i) * numU (S := S) (v i * C' i j) := by
      rw [← hCe i j, ← hC'e i j]
    have h3 : numU (S := S) (e i) * (invU (S := S) (e i) * numU (S := S) (u i * C i j))
        = numU (S := S) (e i) * (invU (S := S) (e i) * numU (S := S) (v i * C' i j)) :=
      congrArg (fun z => numU (S := S) (e i) * z) h2
    rw [← mul_assoc, mul_invU, one_mul, ← mul_assoc, mul_invU, one_mul] at h3
    exact h3
  have hu' : rk.rank (fun i j => u i * C i j) = rk.rank C := by
    have h1 := hleft (fun i => u i) hu C
    rwa [diag_mul_eq] at h1
  have hv' : rk.rank (fun i j => v i * C' i j) = rk.rank C' := by
    have h1 := hleft (fun i => v i) hv C'
    rwa [diag_mul_eq] at h1
  rw [← hu', heq, hv']

/-- The rank of a matrix over the localization, read off from a presentation. -/
noncomputable def extRank (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (OreLocalization S R)) : ℝ :=
  rk.rank ((exists_isPres (S := S) hS A).choose_spec.choose)

theorem extRank_eq (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    {n m : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)} {x : Fin n → S}
    {C : Matrix (Fin n) (Fin m) R} (h : IsPres (S := S) A x C) :
    extRank (S := S) hS rk A = rk.rank C :=
  isPres_rank_eq (S := S) hS rk hleft (exists_isPres (S := S) hS A).choose_spec.choose_spec h


/-! ### Auxiliary identities for the localisation -/

/-! ### Moving a column of denominators to the left -/

/-- **Moving a right diagonal of denominators to the left.**  For a matrix `C` over `R` and
denominators `y j ∈ S` there are row denominators `e i ∈ S` and a matrix `D` over `R` with
`numMat C * diag (invU ∘ y) = diag (invU ∘ e) * numMat D` (an identity over `R[S⁻¹]`) and
`diag e * C = D * diag y` (an identity over `R`). -/
theorem matrixMove {n m : ℕ} (C : Matrix (Fin n) (Fin m) R) (y : Fin m → S) :
    ∃ (e : Fin n → S) (D : Matrix (Fin n) (Fin m) R),
      numMat (S := S) C * diagInv (S := S) y = diagInv (S := S) e * numMat (S := S) D ∧
      Matrix.diagonal (fun i => (e i : R)) * C = D * Matrix.diagonal (fun j => (y j : R)) := by
  have h1 : ∀ (i : Fin n) (j : Fin m), ∃ (r : R) (s : S), (s : R) * C i j = r * (y j : R) := by
    intro i j
    obtain ⟨r, s, hrs⟩ := OreLocalization.oreCondition (C i j) (y j)
    exact ⟨r, s, hrs⟩
  choose r s hrs using h1
  have h2 : ∀ i : Fin n, ∃ (e : S) (t : Fin m → R), ∀ j, (e : R) = t j * (s i j : R) := by
    intro i
    obtain ⟨e, hc⟩ := Work.ORVonNeumann.Rep.exists_common_left_multiple (S := S) (s i)
    choose t ht using hc
    exact ⟨e, t, ht⟩
  choose e t ht using h2
  refine ⟨e, Matrix.of (fun i j => t i j * r i j), ?_, ?_⟩
  · ext i j
    rw [diagInv, Matrix.mul_diagonal, diagInv, Matrix.diagonal_mul, numMat_apply, numMat_apply,
      Matrix.of_apply]
    rw [numU_mul_invU_eq (S := S) (hrs i j), invU_eq_of_eq (S := S) (ht i j), map_mul]
    simp only [mul_assoc]
  · ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    calc (e i : R) * C i j = ((t i j : R) * (s i j : R)) * C i j := by rw [ht i j]
      _ = (t i j : R) * ((s i j : R) * C i j) := by rw [mul_assoc]
      _ = (t i j : R) * (r i j * (y j : R)) := by rw [hrs i j]
      _ = (t i j * r i j) * (y j : R) := by rw [mul_assoc]

/-! ### Multiplicativity of the extended rank -/

theorem extRank_mul_le (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hright : ∀ {n m : ℕ} (y : Fin m → R), (∀ j, y j ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (C * Matrix.diagonal y) = rk.rank C)
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (OreLocalization S R))
    (B : Matrix (Fin m) (Fin k) (OreLocalization S R)) :
    extRank (S := S) hS rk (A * B) ≤
      min (extRank (S := S) hS rk A) (extRank (S := S) hS rk B) := by
  obtain ⟨xA, CA, hA⟩ := exists_isPres (S := S) hS A
  obtain ⟨xB, CB, hB⟩ := exists_isPres (S := S) hS B
  obtain ⟨e, D, hU, hR⟩ := matrixMove (S := S) CA xB
  have hAB : IsPres (S := S) (A * B) (fun i => e i * xA i) (D * CB) := by
    have hA' : A = diagInv (S := S) xA * numMat (S := S) CA := hA
    have hB' : B = diagInv (S := S) xB * numMat (S := S) CB := hB
    show A * B = diagInv (S := S) (fun i => e i * xA i) * numMat (S := S) (D * CB)
    rw [hA', hB']
    calc (diagInv (S := S) xA * numMat (S := S) CA) * (diagInv (S := S) xB * numMat (S := S) CB)
        = diagInv (S := S) xA * (numMat (S := S) CA * diagInv (S := S) xB)
            * numMat (S := S) CB := by simp only [Matrix.mul_assoc]
      _ = diagInv (S := S) xA * (diagInv (S := S) e * numMat (S := S) D)
            * numMat (S := S) CB := by rw [hU]
      _ = (diagInv (S := S) xA * diagInv (S := S) e) * (numMat (S := S) D * numMat (S := S) CB) := by
            simp only [Matrix.mul_assoc]
      _ = diagInv (S := S) (fun i => e i * xA i) * numMat (S := S) (D * CB) := by
            rw [diagInv_mul, ← numMat_mul]
  have hD : rk.rank D = rk.rank CA := by
    have h1 : rk.rank (D * Matrix.diagonal (fun j => (xB j : R)))
        = rk.rank (Matrix.diagonal (fun i => (e i : R)) * CA) := by rw [← hR]
    rw [hright (fun j => (xB j : R)) (fun j => hS (xB j).2) D, hleft (fun i => (e i : R))
      (fun i => hS (e i).2) CA] at h1
    exact h1
  rw [extRank_eq (S := S) hS rk (hleft := hleft) hAB,
    extRank_eq (S := S) hS rk (hleft := hleft) hA,
    extRank_eq (S := S) hS rk (hleft := hleft) hB, ← hD]
  exact rk.mul_le D CB

/-! ### Additivity for block diagonal matrices -/

theorem isPres_blockDiag {n m p q : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)}
    {B : Matrix (Fin p) (Fin q) (OreLocalization S R)} {x : Fin n → S} {y : Fin p → S}
    {C : Matrix (Fin n) (Fin m) R} {D : Matrix (Fin p) (Fin q) R}
    (hA : IsPres (S := S) A x C) (hB : IsPres (S := S) B y D) :
    IsPres (S := S) (Work.ORVonNeumann.blockDiag A B) (Fin.addCases x y)
      (Work.ORVonNeumann.blockDiag C D) := by
  have hAe := (isPres_iff (S := S)).mp hA
  have hBe := (isPres_iff (S := S)).mp hB
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  rw [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Work.ORVonNeumann.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply]
  cases i using Fin.addCases with
  | left i' =>
    cases j using Fin.addCases with
    | left j' =>
      simpa only [Fin.addCases_left, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
        using hAe i' j'
    | right j'' =>
      simp only [Fin.addCases_left, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        Matrix.map_apply, map_zero, mul_zero]
  | right i'' =>
    cases j using Fin.addCases with
    | left j' =>
      simp only [Fin.addCases_right, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        Matrix.map_apply, map_zero, mul_zero]
    | right j'' =>
      simpa only [Fin.addCases_right, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
        using hBe i'' j''

theorem extRank_blockDiag_add (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (OreLocalization S R))
    (B : Matrix (Fin p) (Fin q) (OreLocalization S R)) :
    extRank (S := S) hS rk (Work.ORVonNeumann.blockDiag A B)
      = extRank (S := S) hS rk A + extRank (S := S) hS rk B := by
  obtain ⟨x, C, hA⟩ := exists_isPres (S := S) hS A
  obtain ⟨y, D, hB⟩ := exists_isPres (S := S) hS B
  rw [extRank_eq (S := S) hS rk (hleft := hleft) (isPres_blockDiag (S := S) hA hB),
    extRank_eq (S := S) hS rk (hleft := hleft) hA,
    extRank_eq (S := S) hS rk (hleft := hleft) hB,
    SylvesterRankFunction.rank_blockDiag]

/-! ### Subadditivity for block upper triangular matrices -/

theorem isPres_blockUpper {n m p q : ℕ} {A : Matrix (Fin n) (Fin m) (OreLocalization S R)}
    {C : Matrix (Fin n) (Fin q) (OreLocalization S R)}
    {B : Matrix (Fin p) (Fin q) (OreLocalization S R)} {x : Fin n → S} {y : Fin p → S}
    {CA : Matrix (Fin n) (Fin m) R} {CC : Matrix (Fin n) (Fin q) R}
    {CB : Matrix (Fin p) (Fin q) R}
    (hA : IsPres (S := S) A x CA) (hC : IsPres (S := S) C x CC) (hB : IsPres (S := S) B y CB) :
    IsPres (S := S) (Work.ORVonNeumann.blockUpper A C B) (Fin.addCases x y)
      (Work.ORVonNeumann.blockUpper CA CC CB) := by
  have hAe := (isPres_iff (S := S)).mp hA
  have hCe := (isPres_iff (S := S)).mp hC
  have hBe := (isPres_iff (S := S)).mp hB
  refine (isPres_iff (S := S)).mpr ?_
  intro i j
  rw [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply]
  cases i using Fin.addCases with
  | left i' =>
    cases j using Fin.addCases with
    | left j' =>
      simpa only [Fin.addCases_left, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
        using hAe i' j'
    | right j'' =>
      simpa only [Fin.addCases_left, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂] using hCe i' j''
  | right i'' =>
    cases j using Fin.addCases with
    | left j' =>
      simp only [Fin.addCases_right, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        Matrix.map_apply, map_zero, mul_zero]
    | right j'' =>
      simpa only [Fin.addCases_right, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
        using hBe i'' j''

theorem extRank_blockUpper_le (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hright : ∀ {n m : ℕ} (y : Fin m → R), (∀ j, y j ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (C * Matrix.diagonal y) = rk.rank C)
    {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (OreLocalization S R))
    (C : Matrix (Fin n) (Fin q) (OreLocalization S R))
    (B : Matrix (Fin p) (Fin q) (OreLocalization S R)) :
    extRank (S := S) hS rk A + extRank (S := S) hS rk B
      ≤ extRank (S := S) hS rk (Work.ORVonNeumann.blockUpper A C B) := by
  obtain ⟨x, CA, hA⟩ := exists_isPres (S := S) hS A
  obtain ⟨x', CC, hC⟩ := exists_isPres (S := S) hS C
  obtain ⟨y, CB, hB⟩ := exists_isPres (S := S) hS B
  have hpair : ∀ i : Fin n, ∃ (e : S) (u v : R),
      u ∈ nonZeroDivisors R ∧ v ∈ nonZeroDivisors R ∧
      (e : R) = u * (x i : R) ∧ (e : R) = v * (x' i : R) :=
    fun i => exists_commonDenom_pair (S := S) hS (x i) (x' i)
  choose e u v hu hv hue hve using hpair
  have hA' : IsPres (S := S) A e (fun i j => u i * CA i j) := hA.refine hue
  have hC' : IsPres (S := S) C e (fun i j => v i * CC i j) := hC.refine hve
  have hBU := isPres_blockUpper (S := S) hA' hC' hB
  have h1 : extRank (S := S) hS rk A = rk.rank (fun i j => u i * CA i j) :=
    extRank_eq (S := S) hS rk (hleft := hleft) hA'
  have h2 : extRank (S := S) hS rk B = rk.rank CB :=
    extRank_eq (S := S) hS rk (hleft := hleft) hB
  have h3 : extRank (S := S) hS rk (Work.ORVonNeumann.blockUpper A C B)
      = rk.rank (Work.ORVonNeumann.blockUpper (fun i j => u i * CA i j)
          (fun i j => v i * CC i j) CB) :=
    extRank_eq (S := S) hS rk (hleft := hleft) hBU
  have h5 : rk.rank (fun i j => u i * CA i j) + rk.rank CB
      ≤ rk.rank (Work.ORVonNeumann.blockUpper (fun i j => u i * CA i j)
          (fun i j => v i * CC i j) CB) := rk.blockUpper_le _ _ _
  rw [h1, h2, h3]
  exact h5

/-! ### Faithfulness -/

theorem extRank_faithful (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hfaith : rk.Faithful) {x : OreLocalization S R}
    (hx : extRank (S := S) hS rk (!![x] : Matrix (Fin 1) (Fin 1) (OreLocalization S R)) = 0) :
    x = 0 := by
  obtain ⟨y, C, hC⟩ := exists_isPres (S := S) hS (!![x] : Matrix (Fin 1) (Fin 1) (OreLocalization S R))
  have h1 : rk.rank C = 0 := by
    rw [← extRank_eq (S := S) hS rk (hleft := hleft) hC, hx]
  have h2 : C = 0 := (Work.ORVonNeumann.Rank.rank_eq_zero_iff rk hfaith C).mp h1
  have h3 : (!![x] : Matrix (Fin 1) (Fin 1) (OreLocalization S R)) = 0 := by
    have h := hC
    rw [IsPres] at h
    rw [h, h2, numMat_zero, mul_zero]
  have h4 := congrArg (fun M : Matrix (Fin 1) (Fin 1) (OreLocalization S R) => M 0 0) h3
  simpa using h4

/-! ### The extended rank function -/

noncomputable def extRankFunction (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hright : ∀ {n m : ℕ} (y : Fin m → R), (∀ j, y j ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (C * Matrix.diagonal y) = rk.rank C) :
    SylvesterRankFunction (OreLocalization S R) where
  toFun n m A := extRank (S := S) hS rk A
  map_zero n m := by
    rw [extRank_eq (S := S) hS rk (hleft := hleft) (isPres_zero (S := S))]
    exact rk.map_zero n m
  map_one := by
    rw [extRank_eq (S := S) hS rk (hleft := hleft) (isPres_one (S := S))]
    exact rk.map_one
  mul_le A B := extRank_mul_le (S := S) hS rk hleft hright A B
  blockDiag_add A B := extRank_blockDiag_add (S := S) hS rk hleft A B
  blockUpper_le A C B := extRank_blockUpper_le (S := S) hS rk hleft hright A C B

theorem extRankFunction_faithful (hS : S ≤ nonZeroDivisors R) (rk : SylvesterRankFunction R)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hright : ∀ {n m : ℕ} (y : Fin m → R), (∀ j, y j ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (C * Matrix.diagonal y) = rk.rank C)
    (hfaith : rk.Faithful) :
    (extRankFunction (S := S) hS rk hleft hright).Faithful :=
  fun _ hx => extRank_faithful (S := S) hS rk hleft hfaith hx

/-- **The extended rank function of an Ore localisation at non-zero-divisors.** -/
theorem exists_sylvesterRankFunction_oreLocalization (hS : S ≤ nonZeroDivisors R)
    (rk : SylvesterRankFunction R) (hfaith : rk.Faithful)
    (hleft : ∀ {n m : ℕ} (x : Fin n → R), (∀ i, x i ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (Matrix.diagonal x * C) = rk.rank C)
    (hright : ∀ {n m : ℕ} (y : Fin m → R), (∀ j, y j ∈ nonZeroDivisors R) →
      ∀ (C : Matrix (Fin n) (Fin m) R), rk.rank (C * Matrix.diagonal y) = rk.rank C) :
    ∃ rk' : SylvesterRankFunction (OreLocalization S R), rk'.Faithful :=
  ⟨extRankFunction (S := S) hS rk hleft hright,
    extRankFunction_faithful (S := S) hS rk hleft hright hfaith⟩

end Work.ORVonNeumann.Ext

namespace Work.ORVonNeumann.VonNeumannAlgebra

theorem rankAffiliated {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : ∃ rk : Work.ORVonNeumann.SylvesterRankFunction (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).affiliated, rk.Faithful := by
  letI : OreLocalization.OreSet (nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) :=
    (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).oreSet
  have hleft : ∀ {n m : ℕ} (x : Fin n → ↥(Work.ORVonNeumann.groupVonNeumann G)),
      (∀ i, x i ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) →
      ∀ (C : Matrix (Fin n) (Fin m) ↥(Work.ORVonNeumann.groupVonNeumann G)),
        (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank (Matrix.diagonal x * C)
          = (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C := by
    intro n m x hx C
    rw [Work.ORVonNeumann.Ext.diag_mul_eq]
    exact Work.ORVonNeumann.Rep.rank_mul_diagonal_left (G := G) x hx C
  have hright : ∀ {n m : ℕ} (y : Fin m → ↥(Work.ORVonNeumann.groupVonNeumann G)),
      (∀ j, y j ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) →
      ∀ (C : Matrix (Fin n) (Fin m) ↥(Work.ORVonNeumann.groupVonNeumann G)),
        (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank (C * Matrix.diagonal y)
          = (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C := by
    intro n m y hy C
    rw [Work.ORVonNeumann.Ext.mul_diag_eq]
    exact Work.ORVonNeumann.Rep.rank_mul_diagonal_right (G := G) y hy C
  exact Work.ORVonNeumann.Ext.exists_sylvesterRankFunction_oreLocalization
    (R := ↥(Work.ORVonNeumann.groupVonNeumann G))
    (S := nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) le_rfl
    (Work.ORVonNeumann.Rep.vnRankFunction (G := G))
    (Work.ORVonNeumann.Rep.vnRankFunction_faithful (G := G)) hleft hright

end Work.ORVonNeumann.VonNeumannAlgebra
