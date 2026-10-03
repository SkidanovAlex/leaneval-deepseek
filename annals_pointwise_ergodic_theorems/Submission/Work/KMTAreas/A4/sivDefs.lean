/-
# The block decomposition of Corollary `siv` (Krause--Mirek--Tao §5.1)

This module fixes the *geometric* objects of the proof of Corollary `siv`
(`Submission/Work/KMTAreas/A4/sivClaimZ.lean`), i.e. of the passage from the windowed
Corollary `struct-iii` (`StructiiiAClaim P A`) to the window-free `SivClaimZ P`:

* the block length `blkLen P N = (2 * coefBd P + 2) * N ^ deg P` and the window half-width
  `winBd P N = coefBd P * N ^ deg P`, where `coefBd P` is a coefficient bound with
  `|P(n) - n| ≤ coefBd P * N^deg P` for `|n| ≤ N`;
* the blocks `blkPiece P N g i = g · 1_{[iL, (i+1)L)}` and the windows
  `winPiece P N h i = h · 1_{[iL - W, (i+1)L + W]}` (`L = blkLen`, `W = winBd`);
* the local dual functions `blkDual P N h g i = Ã*_N(h · 1_{Ω_i}, g · 1_{B_i})` and the
  minor-arc parts `blkE P N ρ l h g i = (1 - Π_{≤l,≤l-Log N}) (blkDual P N h g i)`.

The geometry is that of `Submission/Work/KMTAreas/A4Z/SivGeom.lean` (the same partition of `ℤ`,
with the roles of the two functions read off directly from the definition of the first dual
function `AhalfTranspose`): `g` is cut into blocks of length `L`, and the dual function of the
`i`-th block only sees `h` on the window `Ω_i` at distance `≤ W` from it, so that
`blkDual P N h g i` is supported in `Ω_i`, while different windows are separated by
`≥ |i - j| N^d` (for `|i - j| ≥ 2`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.ImprovOneClaims
import Submission.Work.A7.poly_eval_abs_le_coeffSum
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger (GoodMajorArcs)
open Work.Analysis.EndVar (logN)

/-! ## The coefficient bound and the block geometry -/

/-- A coefficient bound for `P` adapted to the interval `[-N,N]`: for `|n| ≤ N` one has
`|P(n) - n| ≤ coefBd P * N ^ P.natDegree`. -/
noncomputable def coefBd (P : Polynomial ℤ) : ℕ :=
  (∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).natAbs) + 1

/-- The half-width of the windows: `winBd P N = coefBd P * N ^ deg P`. -/
noncomputable def winBd (P : Polynomial ℤ) (N : ℕ) : ℕ := coefBd P * N ^ P.natDegree

/-- The block length `blkLen P N = (2 * coefBd P + 2) * N ^ deg P`. -/
noncomputable def blkLen (P : Polynomial ℤ) (N : ℕ) : ℕ := (2 * coefBd P + 2) * N ^ P.natDegree

/-- The left end of the window of the `i`-th block. -/
noncomputable def blkAlpha (P : Polynomial ℤ) (N : ℕ) (i : ℤ) : ℤ :=
  i * (blkLen P N : ℤ) - (winBd P N : ℤ)

/-- The right end of the window of the `i`-th block. -/
noncomputable def blkBeta (P : Polynomial ℤ) (N : ℕ) (i : ℤ) : ℤ :=
  (i + 1) * (blkLen P N : ℤ) + (winBd P N : ℤ)

/-- The `i`-th block piece of `g`: `g` restricted to `[i L, (i+1) L)`, `L = blkLen P N`. -/
noncomputable def blkPiece (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (i : ℤ) : ℤ → ℂ :=
  fun x => if i * (blkLen P N : ℤ) ≤ x ∧ x < (i + 1) * (blkLen P N : ℤ) then g x else 0

/-- The window piece of `h`: `h` restricted to the window `[α_i, β_i]` of the `i`-th block. -/
noncomputable def winPiece (P : Polynomial ℤ) (N : ℕ) (h : ℤ → ℂ) (i : ℤ) : ℤ → ℂ :=
  fun x => if blkAlpha P N i ≤ x ∧ x ≤ blkBeta P N i then h x else 0

/-- The local dual function `Ã*_N(h · 1_{Ω_i}, g · 1_{B_i})` of the `i`-th block. -/
noncomputable def blkDual (P : Polynomial ℤ) (N : ℕ) (h g : ℤ → ℂ) (i : ℤ) : ℤ → ℂ :=
  AhalfTranspose N P (winPiece P N h i) (blkPiece P N g i)

/-- The minor-arc part `(1 - Π_{≤l,≤l - Log N})` of a function. -/
noncomputable def blkProj (P : Polynomial ℤ) (N : ℕ) (ρ : ℝ) (l : ℕ) (u : ℤ → ℂ) : ℤ → ℂ :=
  u - Work.KMTContract.kmtProj ρ l ((l : ℤ) - logN N) u

/-- The minor-arc part of the local dual function of the `i`-th block. -/
noncomputable def blkE (P : Polynomial ℤ) (N : ℕ) (ρ : ℝ) (l : ℕ) (h g : ℤ → ℂ)
    (i : ℤ) : ℤ → ℂ :=
  blkProj P N ρ l (blkDual P N h g i)

/-- The `i`-th block piece of a `1`-bounded function is `1`-bounded. -/
theorem norm_blkPiece_le {P : Polynomial ℤ} {N : ℕ} {g : ℤ → ℂ} (hg : ∀ x, ‖g x‖ ≤ 1)
    (i x : ℤ) : ‖blkPiece P N g i x‖ ≤ 1 := by
  rw [blkPiece]
  split
  · exact hg x
  · simp

/-- The window piece of a `1`-bounded function is `1`-bounded. -/
theorem norm_winPiece_le {P : Polynomial ℤ} {N : ℕ} {h : ℤ → ℂ} (hh : ∀ x, ‖h x‖ ≤ 1)
    (i x : ℤ) : ‖winPiece P N h i x‖ ≤ 1 := by
  rw [winPiece]
  split
  · exact hh x
  · simp


/-! ## The coefficient bound and the block arithmetic -/

/-- The sharp coefficient bound: `|P(n)| ≤ (Σ_j |coeff_j|) * N^deg P` for `0 ≤ n ≤ N`. -/
theorem abs_eval_le_coefBd {P : Polynomial ℤ} {N : ℕ} {n : ℤ}
    (hn1 : 0 ≤ n) (hn2 : n ≤ (N : ℤ)) (hN : 1 ≤ N) :
    |P.eval n| ≤ ((coefBd P - 1 : ℕ) : ℤ) * (N : ℤ) ^ P.natDegree := by
  have hcoe : ∀ j : ℕ, |P.coeff j| = ((P.coeff j).natAbs : ℤ) := fun j => by
    rw [Int.natCast_natAbs]
  have hsupp : P.support ⊆ Finset.range (P.natDegree + 1) := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp j hj))
  have hpd : ∀ j ∈ P.support, j ≤ P.natDegree := fun j hj =>
    Polynomial.le_natDegree_of_mem_supp j hj
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  calc |P.eval n| = |∑ j ∈ P.support, P.coeff j * n ^ j| := by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ ≤ ∑ j ∈ P.support, |P.coeff j| * n ^ j := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun j hj => by rw [abs_mul, abs_of_nonneg (pow_nonneg hn1 j)]
    _ ≤ ∑ j ∈ P.support, |P.coeff j| * (N : ℤ) ^ P.natDegree := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc n ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ hn1 hn2 j
          _ ≤ (N : ℤ) ^ P.natDegree := pow_le_pow_right₀ hN1 (hpd j hj)
    _ = (∑ j ∈ P.support, |P.coeff j|) * (N : ℤ) ^ P.natDegree := (Finset.sum_mul ..).symm
    _ ≤ (((coefBd P - 1 : ℕ)) : ℤ) * (N : ℤ) ^ P.natDegree := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 : ∑ j ∈ P.support, |P.coeff j|
            = ((∑ j ∈ P.support, (P.coeff j).natAbs : ℕ) : ℤ) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl fun j _ => hcoe j
        rw [h1, coefBd]
        have h2 : (∑ j ∈ P.support, (P.coeff j).natAbs) ≤
            ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).natAbs :=
          Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun j _ _ => Nat.zero_le _)
        exact_mod_cast h2

theorem coefBd_pos (P : Polynomial ℤ) : 1 ≤ coefBd P := by
  rw [coefBd]; omega

/-- The block membership `i * L ≤ x < (i+1) * L` determines `i = x / L`. -/
theorem ediv_eq_of_mem_Ico {L : ℤ} (hL : 0 < L) {i x : ℤ}
    (h1 : i * L ≤ x) (h2 : x < (i + 1) * L) : i = x / L := by
  have hxsplit : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hem : x % L < L := Int.emod_lt_of_pos x hL
  have hle : i ≤ x / L := by
    by_contra hc
    push_neg at hc
    have h4 : x / L + 1 ≤ i := by omega
    have h3 : ((x / L) + 1) * L ≤ i * L := Int.mul_le_mul_of_nonneg_right h4 hL.le
    have hsplit : ((x / L) + 1) * L = L * (x / L) + L := by ring
    omega
  have hlt : x / L < i + 1 := Int.ediv_lt_of_lt_mul hL h2
  omega

/-- The block membership in the other direction. -/
theorem mem_Ico_of_ediv_eq {L : ℤ} (hL : 0 < L) {m x : ℤ} (h : m = x / L) :
    m * L ≤ x ∧ x < (m + 1) * L := by
  subst h
  refine ⟨Int.ediv_mul_le x hL.ne', ?_⟩
  have hxsplit : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hem : x % L < L := Int.emod_lt_of_pos x hL
  have hsplit : ((x / L) + 1) * L = L * (x / L) + L := by ring
  omega

/-! ## The `ℓ²` norm on `ℤ` -/

/-- The square of the `ℓ²` norm of a sequence on `ℤ`. -/
noncomputable def l2sq (g : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖g x‖ ^ 2

/-- The `ℓ²` norm of a sequence on `ℤ`. -/
noncomputable def l2norm (g : ℤ → ℂ) : ℝ := Real.sqrt (l2sq g)

theorem l2sq_nonneg (g : ℤ → ℂ) : 0 ≤ l2sq g := tsum_nonneg fun x => sq_nonneg _

theorem l2norm_nonneg (g : ℤ → ℂ) : 0 ≤ l2norm g := Real.sqrt_nonneg _

theorem sq_l2norm {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    l2norm g ^ 2 = ∑' x : ℤ, ‖g x‖ ^ 2 := by
  rw [l2norm, l2sq, Real.sq_sqrt (tsum_nonneg fun x => sq_nonneg _)]

/-- **The bridge between `eLpNorm` at exponent `2` and the `ℓ²` norm.** -/
theorem eLpNorm_two_eq_ofReal_l2norm {g : ℤ → ℂ} (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) :
    MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      = ENNReal.ofReal (l2norm g) := by
  have hnn : ∀ x : ℤ, (0 : ℝ) ≤ ‖g x‖ ^ 2 := fun x => sq_nonneg _
  have hstep : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      = (∑' x : ℤ, ENNReal.ofReal (‖g x‖ ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
    norm_num
    rw [MeasureTheory.lintegral_count]
  rw [hstep, ← ENNReal.ofReal_tsum_of_nonneg hnn hg, l2norm, l2sq,
    ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hnn) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.sqrt_eq_rpow]

/-! ## The support radius and the centring translation -/

/-- The support radius of the centred pieces.  The windows have length
`blkLen P N + 2 * winBd P N`, and after the translation `blkCtr` they are contained in
`[-blkRad P N, blkRad P N]` with `blkRad P N = blkLen P N + winBd P N`. -/
noncomputable def blkRad (P : Polynomial ℤ) (N : ℕ) : ℕ := blkLen P N + winBd P N

/-- The integer translation which places the right end of the `i`-th window at `blkRad`. -/
noncomputable def blkCtr (P : Polynomial ℤ) (N : ℕ) (i : ℤ) : ℤ :=
  blkBeta P N i - (blkRad P N : ℤ)

/-- The window length. -/
theorem blkBeta_sub_blkAlpha (P : Polynomial ℤ) (N : ℕ) (i : ℤ) :
    blkBeta P N i - blkAlpha P N i
      = (blkLen P N : ℤ) + 2 * (winBd P N : ℤ) := by
  simp only [blkBeta, blkAlpha]
  ring

theorem blkRad_cast (P : Polynomial ℤ) (N : ℕ) :
    (blkRad P N : ℤ) = (blkLen P N : ℤ) + (winBd P N : ℤ) := by
  rw [blkRad]
  push_cast
  ring

/-- A point of the window of the `i`-th block, translated by `blkCtr`, lies in
`[-blkRad, blkRad]`. -/
theorem abs_sub_blkCtr_le (P : Polynomial ℤ) (N : ℕ) (i y : ℤ)
    (h1 : blkAlpha P N i ≤ y) (h2 : y ≤ blkBeta P N i) :
    |y - blkCtr P N i| ≤ (blkRad P N : ℤ) := by
  have hdiff := blkBeta_sub_blkAlpha P N i
  have hrad := blkRad_cast P N
  have hW : (0 : ℤ) ≤ (winBd P N : ℤ) := by positivity
  have hL : (0 : ℤ) ≤ (blkLen P N : ℤ) := by positivity
  have hupper : y - blkCtr P N i ≤ (blkRad P N : ℤ) := by
    simp only [blkCtr]
    linarith
  have hlower : -((blkRad P N : ℤ)) ≤ y - blkCtr P N i := by
    simp only [blkCtr]
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The block piece is supported in the closed window `[blkAlpha, blkBeta]`. -/
theorem blkPiece_eq_zero_of_not_mem_window (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℂ) (i x : ℤ)
    (hx : ¬(blkAlpha P N i ≤ x ∧ x ≤ blkBeta P N i)) : blkPiece P N g i x = 0 := by
  rw [blkPiece]
  refine if_neg fun hc => hx ⟨?_, ?_⟩
  · simp only [blkAlpha]
    have hW : (0 : ℤ) ≤ (winBd P N : ℤ) := by positivity
    linarith [hc.1]
  · simp only [blkBeta]
    have hW : (0 : ℤ) ≤ (winBd P N : ℤ) := by positivity
    linarith [hc.2]


end Work.KMTAreas.A4
