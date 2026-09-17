import Mathlib
import Submission.Commons.Lattice.Basis.exists_coeff_bound

/-!
# The finite candidate list of lattice vectors

`Submission.Contact` needs a *fixed finite* list of lattice vectors `BoxL : Fin m → Vec d` that
(on an event of overwhelming probability) contains every lattice vector that the exploration
process can violate.  This file provides it as a coefficient box of a basis of the lattice:

    BoxL c = ∑ i, (c i - N) • b i ,      c : Fin d → Fin (2N+1),

with the all-`N` index (giving the zero vector) removed.  The list is closed under negation and
contains every lattice vector of norm at most `R` as soon as `N` is at least the basis
coordinate bound `K·R` (`Commons.Lattice.Basis.exists_coeff_bound`), which is supplied as the
hypothesis `hcoeff` below so that this file is independent of it.
-/

namespace Submission.LatticeBox

open Matrix

noncomputable section

variable {d : ℕ}

/-- Vectors of `ℝ^d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The coefficient box `Fin d → Fin (2N+1)`. -/
abbrev CoeffIdx (d N : ℕ) := Fin d → Fin (2 * N + 1)

/-- The integer coefficient attached to an index, in `[-N, N]`. -/
def coeffZ {d N : ℕ} (c : CoeffIdx d N) (i : Fin d) : ℤ := ((c i : ℕ) : ℤ) - N

/-- The index all of whose coefficients vanish. -/
def zeroCoeff {d N : ℕ} : CoeffIdx d N := fun _ => ⟨N, by omega⟩

lemma zeroCoeff_apply {d N : ℕ} (i : Fin d) : (zeroCoeff (d := d) (N := N)) i = ⟨N, by omega⟩ :=
  rfl

lemma coeffZ_zeroCoeff {d N : ℕ} (i : Fin d) :
    coeffZ (zeroCoeff (d := d) (N := N)) i = 0 := by
  simp [coeffZ, zeroCoeff]

/-- Negation of coefficients, as a map of the coefficient box. -/
def negCoeff {d N : ℕ} (c : CoeffIdx d N) : CoeffIdx d N :=
  fun i => ⟨2 * N - (c i : ℕ), by have := (c i).isLt; omega⟩

lemma coeffZ_negCoeff {d N : ℕ} (c : CoeffIdx d N) (i : Fin d) :
    coeffZ (negCoeff c) i = -coeffZ c i := by
  simp only [coeffZ, negCoeff]
  have := (c i).isLt
  omega

lemma negCoeff_negCoeff {d N : ℕ} (c : CoeffIdx d N) : negCoeff (negCoeff c) = c := by
  funext i
  have := (c i).isLt
  simp only [negCoeff]
  congr 1
  omega

lemma negCoeff_zeroCoeff {d N : ℕ} :
    negCoeff (zeroCoeff (d := d) (N := N)) = zeroCoeff := by
  funext i
  simp only [negCoeff, zeroCoeff]
  congr 1
  omega

/-- The index type with the zero coefficient vector removed. -/
abbrev BoxIdx (d N : ℕ) := {c : CoeffIdx d N // c ≠ zeroCoeff}

/-- Negation on the box (an involution). -/
def negIdx {d N : ℕ} (c : BoxIdx d N) : BoxIdx d N :=
  ⟨negCoeff c.1, fun h => c.2 (by
    have := congrArg negCoeff h
    rwa [negCoeff_negCoeff, negCoeff_zeroCoeff] at this)⟩

lemma negIdx_negIdx {d N : ℕ} (c : BoxIdx d N) : negIdx (negIdx c) = c := by
  refine Subtype.ext ?_
  simp only [negIdx]
  exact negCoeff_negCoeff c.1

/-- The vector attached to a coefficient index. -/
def boxVec {d N : ℕ} (b : Fin d → Vec d) (c : CoeffIdx d N) : Vec d :=
  ∑ i, ((coeffZ c i : ℤ) : ℝ) • b i

lemma boxVec_zeroCoeff {d N : ℕ} (b : Fin d → Vec d) :
    boxVec b (zeroCoeff (d := d) (N := N)) = 0 := by
  simp only [boxVec, coeffZ_zeroCoeff, Int.cast_zero, zero_smul, Finset.sum_const_zero]

lemma boxVec_negCoeff {d N : ℕ} (b : Fin d → Vec d) (c : CoeffIdx d N) :
    boxVec b (negCoeff c) = -boxVec b c := by
  simp only [boxVec, coeffZ_negCoeff, Int.cast_neg]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => neg_smul _ _

/-- The candidate list. -/
def BoxL {d N : ℕ} (b : Fin d → Vec d) : BoxIdx d N → Vec d := fun c => boxVec b c.1

lemma BoxL_negIdx {d N : ℕ} (b : Fin d → Vec d) (c : BoxIdx d N) :
    BoxL b (negIdx c) = -BoxL b c :=
  boxVec_negCoeff b c.1

/-- If the coefficient map is injective (i.e. `b` is linearly independent over `ℝ`), no candidate
is the zero vector. -/
lemma BoxL_ne_zero {d N : ℕ} {b : Fin d → Vec d}
    (hlin : ∀ c : CoeffIdx d N, boxVec b c = 0 → c = zeroCoeff) (c : BoxIdx d N) :
    BoxL b c ≠ 0 := fun h => c.2 (hlin c.1 h)

/-- Completion: every *nonzero* vector `x` that can be written as `boxVec b c` for some
coefficient index `c` is one of the candidates. -/
lemma exists_boxL_eq_of_ne_zero {d N : ℕ} (b : Fin d → Vec d) {x : Vec d}
    {c : CoeffIdx d N} (hx : x = boxVec b c) (hx0 : x ≠ 0) :
    ∃ c' : BoxIdx d N, BoxL b c' = x := by
  have hc : c ≠ zeroCoeff := fun h => hx0 (by rw [hx, h, boxVec_zeroCoeff])
  exact ⟨⟨c, hc⟩, hx.symm⟩

/-- **Membership in the candidate list.**  A nonzero vector whose coefficients (with respect to
`b`) are bounded by `N` is one of the candidates. -/
theorem exists_boxL_eq_of_mem {d N : ℕ} (b : Fin d → Vec d) {x : Vec d} (hx0 : x ≠ 0)
    {c : Fin d → ℤ} (hx : x = ∑ i, ((c i : ℤ) : ℝ) • b i)
    (hbound : ∀ i, |(c i : ℤ)| ≤ (N : ℤ)) :
    ∃ c' : BoxIdx d N, BoxL b c' = x := by
  have hle : ∀ i, -((N : ℤ)) ≤ c i ∧ c i ≤ (N : ℤ) := fun i => abs_le.mp (hbound i)
  refine exists_boxL_eq_of_ne_zero b
    (c := fun i => ⟨(c i + N).toNat, by have := (hle i).2; omega⟩) ?_ hx0
  rw [hx]
  simp only [boxVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (0 : ℤ) ≤ c i + N := by have := (hle i).1; omega
  have hci : ((c i + N).toNat : ℤ) = c i + N := Int.toNat_of_nonneg h1
  have hz : coeffZ (fun i => ⟨(c i + N).toNat, by have := (hle i).2; omega⟩ :
      CoeffIdx d N) i = c i := by
    simp only [coeffZ, hci]
    ring
  rw [hz]

/-- **The candidate list of a lattice basis.**  Given a lattice basis `b` and a coordinate bound
`|(b.repr x) i| ≤ K‖x‖` (supplied by `Commons.Lattice.Basis.exists_coeff_bound`), there is a
coefficient-box candidate list containing every nonzero lattice vector of norm at most `R`. -/
theorem exists_box_of_coeff_bound {d : ℕ} {Λ : Submodule ℤ (Vec d)}
    (b : Module.Basis (Fin d) ℤ Λ) (R : ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (x : Λ) (i : Fin d), |((b.repr x) i : ℝ)| ≤ K * ‖(x : Vec d)‖) :
    ∃ N : ℕ, ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R →
      ∃ c : BoxIdx d N, BoxL (fun i => ((b i : Λ) : Vec d)) c = x := by
  refine ⟨Nat.ceil (K * R), fun x hx hx0 hxR => ?_⟩
  have hrepr : x = ∑ i, (((b.repr ⟨x, hx⟩) i : ℤ) : ℝ) • ((b i : Λ) : Vec d) := by
    have h : ((((∑ i, (b.repr ⟨x, hx⟩) i • b i) : Λ)) : Vec d)
        = ∑ i, (((b.repr ⟨x, hx⟩) i : ℤ) : ℝ) • ((b i : Λ) : Vec d) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
    rw [← h, b.sum_repr]
  refine exists_boxL_eq_of_mem (fun i => ((b i : Λ) : Vec d)) hx0 hrepr fun i => ?_
  have h1 : |((b.repr ⟨x, hx⟩) i : ℝ)| ≤ K * R :=
    le_trans (hK ⟨x, hx⟩ i) (mul_le_mul_of_nonneg_left hxR hK0)
  have h1' : ((b.repr ⟨x, hx⟩) i : ℝ) ≤ (Nat.ceil (K * R) : ℝ) :=
    le_trans (le_abs_self _) (le_trans h1 (Nat.le_ceil _))
  have h2' : -((b.repr ⟨x, hx⟩) i : ℝ) ≤ (Nat.ceil (K * R) : ℝ) := by
    have := neg_abs_le ((b.repr ⟨x, hx⟩) i : ℝ)
    linarith [le_trans h1 (Nat.le_ceil (K * R))]
  have hlo : -((Nat.ceil (K * R) : ℤ)) ≤ b.repr ⟨x, hx⟩ i := by
    have hh : (-((Nat.ceil (K * R) : ℤ)) : ℝ) ≤ (((b.repr ⟨x, hx⟩) i : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hh
  have hhi : b.repr ⟨x, hx⟩ i ≤ ((Nat.ceil (K * R) : ℤ)) := by
    have hh : (((b.repr ⟨x, hx⟩) i : ℤ) : ℝ) ≤ ((Nat.ceil (K * R) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hh
  exact abs_le.mpr ⟨hlo, hhi⟩


/-- **The candidate list of a lattice.**  Every nonzero lattice vector of norm at most `R` is one
of the candidates. -/
theorem exists_box {d : ℕ} {Λ : Submodule ℤ (Vec d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin d) ℤ Λ) (R : ℝ) :
    ∃ N : ℕ, ∀ x : Vec d, x ∈ Λ → x ≠ 0 → ‖x‖ ≤ R →
      ∃ c : BoxIdx d N, BoxL (fun i => ((b i : Λ) : Vec d)) c = x := by
  obtain ⟨K, hK0, hK⟩ := Commons.Lattice.Basis.exists_coeff_bound Λ b
  exact exists_box_of_coeff_bound b R K hK0.le hK

end

end Submission.LatticeBox
