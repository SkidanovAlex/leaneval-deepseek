import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped Polynomial

noncomputable section

namespace Commons.RingTheory.Polynomial

/-- A polynomial of natural degree `< n` has (WithBot) degree `< n`. -/
lemma degree_lt_of_natDegree_lt {R : Type*} [Semiring R] {p : R[X]} {n : ℕ}
    (hn : p.natDegree < n) : p.degree < (n : WithBot ℕ) := by
  by_cases hp : p = 0
  · subst hp
    rw [degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mp hn

/-- A family inside a submodule is linearly independent when it is linearly independent
in the ambient module. -/
lemma linearIndependent_of_subtype {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {S : Submodule R M} {ι : Type*} [Fintype ι] {x : ι → M}
    (hx : ∀ i, x i ∈ S) (hind : LinearIndependent R x) :
    LinearIndependent R (fun i : ι => (⟨x i, hx i⟩ : S)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hM : ((∑ j, c j • (⟨x j, hx j⟩ : S) : S) : M) = 0 := by
    simpa using congrArg (fun z : S => (z : M)) hc
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hM
  exact (Fintype.linearIndependent_iff.mp hind) c hM i

/-- If `f` and `g` share a common divisor `s` of degree at least two, with
`f = s * a` and `g = s * b`, and the degrees of `a` and `b` leave room for
multiplying by `X` (i.e. `a.natDegree + 2 ≤ m` and `b.natDegree + 2 ≤ n`),
then the rank of the Sylvester matrix `sylvester f g m n` is at most `m + n - 2`.
(The kernel contains the two independent vectors `(-a, b)` and `(-a*X, b*X)`.) -/
theorem sylvester_rank_le_of_common_divisor {K : Type*} [Field K] (f g s a b : K[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hfs : f = s * a) (hgs : g = s * b) (hs2 : 2 ≤ s.natDegree)
    (ha : a.natDegree + 2 ≤ m) (hb : b.natDegree + 2 ≤ n) (hf0 : f ≠ 0) :
    Matrix.rank (Polynomial.sylvester f g m n) ≤ m + n - 2 := by
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hf0
    rw [hfs, ha0, mul_zero]
  have ha_lt : a.natDegree < m := by omega
  have hb_lt : b.natDegree < n := by omega
  have hmem1 : (-a : K[X]) ∈ Polynomial.degreeLT K m := by
    rw [Polynomial.mem_degreeLT]
    exact degree_lt_of_natDegree_lt (by simpa using ha_lt)
  have hmem2 : (b : K[X]) ∈ Polynomial.degreeLT K n := by
    rw [Polynomial.mem_degreeLT]
    exact degree_lt_of_natDegree_lt hb_lt
  have haX_lt : (-(a * X) : K[X]).natDegree < m := by
    calc (-(a * X) : K[X]).natDegree = (a * X).natDegree := by simp
      _ ≤ a.natDegree + (X : K[X]).natDegree := natDegree_mul_le
      _ = a.natDegree + 1 := by simp
      _ < m := by omega
  have hmem3 : (-(a * X) : K[X]) ∈ Polynomial.degreeLT K m := by
    rw [Polynomial.mem_degreeLT]
    exact degree_lt_of_natDegree_lt haX_lt
  have hbX_lt : (b * X : K[X]).natDegree < n := by
    calc (b * X : K[X]).natDegree ≤ b.natDegree + (X : K[X]).natDegree := natDegree_mul_le
      _ = b.natDegree + 1 := by simp
      _ < n := by omega
  have hmem4 : (b * X : K[X]) ∈ Polynomial.degreeLT K n := by
    rw [Polynomial.mem_degreeLT]
    exact degree_lt_of_natDegree_lt hbX_lt
  let p₁ : Polynomial.degreeLT K m := ⟨-a, hmem1⟩
  let q₁ : Polynomial.degreeLT K n := ⟨b, hmem2⟩
  let p₂ : Polynomial.degreeLT K m := ⟨-(a * X), hmem3⟩
  let q₂ : Polynomial.degreeLT K n := ⟨b * X, hmem4⟩
  let x₁ : Polynomial.degreeLT K m × Polynomial.degreeLT K n := (p₁, q₁)
  let x₂ : Polynomial.degreeLT K m × Polynomial.degreeLT K n := (p₂, q₂)
  let T : Polynomial.degreeLT K m × Polynomial.degreeLT K n →ₗ[K] Polynomial.degreeLT K (m + n) :=
    sylvesterMap f g hf hg
  have hT₁ : T x₁ = 0 := by
    dsimp [T, x₁, p₁, q₁]
    apply Subtype.ext
    change f * (q₁ : K[X]) + g * (p₁ : K[X]) = 0
    simp [p₁, q₁]
    rw [hfs, hgs]
    ring
  have hT₂ : T x₂ = 0 := by
    dsimp [T, x₂, p₂, q₂]
    apply Subtype.ext
    change f * (q₂ : K[X]) + g * (p₂ : K[X]) = 0
    simp [p₂, q₂]
    rw [hfs, hgs]
    ring
  have hx₁ : x₁ ∈ LinearMap.ker T := by rw [LinearMap.mem_ker]; exact hT₁
  have hx₂ : x₂ ∈ LinearMap.ker T := by rw [LinearMap.mem_ker]; exact hT₂
  let S : Submodule K (Polynomial.degreeLT K m × Polynomial.degreeLT K n) := LinearMap.ker T
  have hindV : LinearIndependent K ![x₁, x₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · have hp : ((∑ j : Fin 2, g j • (![x₁, x₂] j) : Polynomial.degreeLT K m × Polynomial.degreeLT K n).1 : K[X]) = 0 := by
        have h := congrArg (fun z : Polynomial.degreeLT K m × Polynomial.degreeLT K n => (z.1 : K[X])) hg
        simpa using h
      rw [Fin.sum_univ_two] at hp
      simp [x₁, x₂, p₁, p₂] at hp
      rw [smul_eq_C_mul, smul_eq_C_mul] at hp
      have hfac : -(C (g 0) * a) + -(C (g 1) * (a * X)) = -a * (C (g 0) + X * C (g 1)) := by ring
      rw [hfac] at hp
      have hna : (-a : K[X]) ≠ 0 := by exact neg_ne_zero.mpr ha0
      have hD : C (g 0) + X * C (g 1) = 0 := (mul_eq_zero.mp hp).resolve_left hna
      have hc0 : (C (g 0) + X * C (g 1)).coeff 0 = 0 := congrArg (fun p => p.coeff 0) hD
      simpa using hc0
    · have hp : ((∑ j : Fin 2, g j • (![x₁, x₂] j) : Polynomial.degreeLT K m × Polynomial.degreeLT K n).1 : K[X]) = 0 := by
        have h := congrArg (fun z : Polynomial.degreeLT K m × Polynomial.degreeLT K n => (z.1 : K[X])) hg
        simpa using h
      rw [Fin.sum_univ_two] at hp
      simp [x₁, x₂, p₁, p₂] at hp
      rw [smul_eq_C_mul, smul_eq_C_mul] at hp
      have hfac : -(C (g 0) * a) + -(C (g 1) * (a * X)) = -a * (C (g 0) + X * C (g 1)) := by ring
      rw [hfac] at hp
      have hna : (-a : K[X]) ≠ 0 := by exact neg_ne_zero.mpr ha0
      have hD : C (g 0) + X * C (g 1) = 0 := (mul_eq_zero.mp hp).resolve_left hna
      have hc1 : (C (g 0) + X * C (g 1)).coeff 1 = 0 := congrArg (fun p => p.coeff 1) hD
      simpa using hc1
  let x : Fin 2 → Polynomial.degreeLT K m × Polynomial.degreeLT K n := ![x₁, x₂]
  have hxmem : ∀ i, x i ∈ LinearMap.ker T := by
    intro i
    fin_cases i <;> simp [x, x₁, x₂] <;> assumption
  have hindS : LinearIndependent K (fun i : Fin 2 => (⟨x i, hxmem i⟩ : LinearMap.ker T)) := by
    exact linearIndependent_of_subtype (S := LinearMap.ker T) (x := x) hxmem hindV
  have hfin2 : 2 ≤ Module.finrank K S := by
    have hcard := hindS.fintype_card_le_finrank
    simpa [S] using hcard
  have hfinrange : Module.finrank K (LinearMap.range T) ≤ m + n - 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    have hdim : Module.finrank K (Polynomial.degreeLT K m × Polynomial.degreeLT K n) = m + n := by
      rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basisProd K m n)]
      simp
    rw [hdim] at hrn
    dsimp [S] at hfin2
    omega
  have htoMatrix :
      LinearMap.toMatrix (Polynomial.degreeLT.basisProd K m n) (Polynomial.degreeLT.basis K (m + n)) T =
        Polynomial.sylvester f g m n := by
    simpa [T, Polynomial.degreeLT.basisProd] using Polynomial.toMatrix_sylvesterMap' (R := K) f g hf hg
  have htoLin : Matrix.toLin (Polynomial.degreeLT.basisProd K m n) (Polynomial.degreeLT.basis K (m + n))
      (Polynomial.sylvester f g m n) = T := by
    rw [← htoMatrix]
    exact Matrix.toLin_toMatrix (Polynomial.degreeLT.basisProd K m n) (Polynomial.degreeLT.basis K (m + n)) T
  have hrank := Matrix.rank_eq_finrank_range_toLin (R := K) (A := Polynomial.sylvester f g m n)
      (m := Fin (m + n)) (n := Fin (m + n))
      (M₁ := Polynomial.degreeLT K (m + n))
      (M₂ := Polynomial.degreeLT K m × Polynomial.degreeLT K n)
      (v₁ := Polynomial.degreeLT.basis K (m + n))
      (v₂ := Polynomial.degreeLT.basisProd K m n)
  calc
    (Polynomial.sylvester f g m n).rank
        = Module.finrank K (LinearMap.range (Matrix.toLin (Polynomial.degreeLT.basisProd K m n)
            (Polynomial.degreeLT.basis K (m + n)) (Polynomial.sylvester f g m n))) := by
            simpa using hrank
    _ = Module.finrank K (LinearMap.range T) := by rw [htoLin]
    _ ≤ m + n - 2 := hfinrange

end Commons.RingTheory.Polynomial