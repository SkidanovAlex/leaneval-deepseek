import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.ChiS1Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.latticeComm_le` — the Schur/Young bound on the lattice commutator

Row 3 (`RowQ2`) of the `NH` ruling (`LEAD_RULING_NH`, work item (A2)) needs the lattice
commutator estimate

    `‖[χ, f_L(D)]‖ ≤ C_fc·S₁/κ_lat`,   `S₁ = chiS1 = Σ_m ‖2πm‖·|χ̂(2πm)|`,

whose linear-algebra form is the statement below: for every lattice function `φ` that is
`L/κ`-Lipschitz along the dual lattice,

    `Σ_{n∈ℤ³} (Σ_{s∈S} χ̂(2π(n−s))·(φ s − φ n)·c s)² ≤ (L·S₁/κ)²·Σ_{s∈S} c s²`

for every finite `S` and every coefficient family `c`.

The mathematics is the `‖w ∗ d‖₂ ≤ ‖w‖₁‖d‖₂` Young inequality for convolution on `ℓ²(ℤ³)` by
the weight `w(m) = ‖2πm‖·|χ̂(2πm)|`: writing `z_n = Σ_s χ̂(n−s)(φ s − φ n)c_s`, the Lipschitz
hypothesis gives `|z_n| ≤ (L/κ)·Σ_s w(n−s)|c_s|`, and Young's inequality (proved here by a
weighted Cauchy–Schwarz plus the translation invariance of the lattice sum) finishes with
`‖w‖₁ = S₁`.

The one analytic input — that `w` really is summable, so that `chiS1 = Σ'_m w(m)` is the honest
`ℓ¹` norm — comes from the corpus Schwartz decay `Work.BoseK15.ChiReg_corpus 52`
(`|χ̂(p)|·(1+‖p‖²)^52 ≤ C`) together with the lattice decay
`Work.BoseK15.sum_inv_one_add_norm_le 51`.

## Contents

* `vec_sub'`, `vec_sub_norm`: `2π(a−b)` and `2π(b−a)` have the same norm;
* `chiHatWeight`, `chiS1_eq_tsum_chiHatWeight`, `summable_chiHatWeight`: the weight and its
  `ℓ¹`-summability (`chiS1` is *by definition* the `tsum` of the weight);
* `young_pointwise`, `young_summable`, `young_tsum`: the three Young-inequality ingredients,
  stated for an abstract nonnegative summable weight `w` (no dependence on `χ̂`);
* `latticeComm_le`: the target.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

/-! ## 1. The lattice vector `vec` and the symmetry of its norm -/

/-- `vec` is additive on the lattice indices: `2π(a − b) = 2πa − 2πb`. -/
lemma vec_sub' (a b : Fin 3 → ℤ) :
    Work.BoseB4.vec (a - b) = Work.BoseB4.vec a - Work.BoseB4.vec b := by
  show WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * ((a - b) i : ℝ)) = _
  rw [show (fun i : Fin 3 => 2 * Real.pi * ((a - b) i : ℝ))
      = (fun i : Fin 3 => 2 * Real.pi * (a i : ℝ)) - (fun i : Fin 3 => 2 * Real.pi * (b i : ℝ))
      from ?_]
  · exact WithLp.toLp_sub 2 _ _
  · ext i
    simp only [Pi.sub_apply]
    push_cast
    ring

/-- `‖vec (a − b)‖ = ‖vec (b − a)‖`: the Lipschitz hypothesis `hφ` is stated at `p − q`, while
the convolution weight is naturally indexed by `n − s`. -/
lemma vec_sub_norm (a b : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec (a - b)‖ = ‖Work.BoseB4.vec (b - a)‖ := by
  rw [vec_sub', vec_sub']
  exact norm_sub_rev _ _

/-! ## 2. The weight `w(m) = ‖2πm‖·|χ̂(2πm)|` and its `ℓ¹`-summability -/

/-- The lattice weight of the commutator bound, `w(m) = ‖vec m‖·|χ̂(vec m)|`; its total mass
`∑' m, w m` is `chiS1`. -/
noncomputable def chiHatWeight (m : Fin 3 → ℤ) : ℝ :=
  ‖Work.BoseB4.vec m‖ * |chiHat (Work.BoseB4.vec m)|

lemma chiHatWeight_nonneg (m : Fin 3 → ℤ) : 0 ≤ chiHatWeight m :=
  mul_nonneg (norm_nonneg _) (abs_nonneg _)

/-- `chiS1` *is* the total mass of the weight (definitional). -/
lemma chiS1_eq_tsum_chiHatWeight : chiS1 = ∑' m : Fin 3 → ℤ, chiHatWeight m := rfl

/-- The lattice decay of `Work.BoseK15`: `Σ_{n∈S} (1+‖vec n‖²)^{-51} ≤ C` for every finite `S`. -/
lemma summable_normWeight :
    Summable (fun m : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 51)⁻¹) := by
  obtain ⟨C, _hC0, hC⟩ := Work.BoseK15.sum_inv_one_add_norm_le 51 (by norm_num)
  exact summable_of_sum_le (fun m => by positivity) hC

/-- **The weight is summable** (so that `chiS1` is the honest `ℓ¹`-norm of the convolution
kernel).  Pointwise, `Work.BoseK15.ChiReg_corpus 52` gives `|χ̂(p)| ≤ Cchi(1+‖p‖²)^{-52}`, hence
`w(m) ≤ Cchi·‖vec m‖·(1+‖vec m‖²)^{-52} ≤ Cchi·(1+‖vec m‖²)^{-51}` because
`‖vec m‖ ≤ 1 + ‖vec m‖²`; the latter is in `ℓ¹(ℤ³)` by `summable_normWeight`. -/
lemma summable_chiHatWeight : Summable chiHatWeight := by
  obtain ⟨Cchi, hCchi_nn, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
  refine Summable.of_nonneg_of_le
    (f := fun m : Fin 3 → ℤ => Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 51)⁻¹)
    (fun m => chiHatWeight_nonneg m) (fun m => ?_) ?_
  · change ‖Work.BoseB4.vec m‖ * |chiHat (Work.BoseB4.vec m)|
        ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 51)⁻¹
    have h52 : (0 : ℝ) < (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52 := by positivity
    have h1 : |chiHat (Work.BoseB4.vec m)| ≤ Cchi / (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ h52]
      exact hChi.1 (Work.BoseB4.vec m)
    have h2 : Cchi / (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52
        = Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52)⁻¹ := by
      rw [div_eq_mul_inv]
    calc ‖Work.BoseB4.vec m‖ * |chiHat (Work.BoseB4.vec m)|
        ≤ ‖Work.BoseB4.vec m‖ * (Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52)⁻¹) :=
          mul_le_mul_of_nonneg_left (h2 ▸ h1) (norm_nonneg _)
      _ = Cchi * (‖Work.BoseB4.vec m‖ * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52)⁻¹) := by
          ring
      _ ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 51)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hCchi_nn
          have hnorm_le : ‖Work.BoseB4.vec m‖ ≤ 1 + ‖Work.BoseB4.vec m‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Work.BoseB4.vec m‖ - 1/2)]
          calc ‖Work.BoseB4.vec m‖ * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52)⁻¹
              ≤ (1 + ‖Work.BoseB4.vec m‖ ^ 2)
                  * (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 52)⁻¹ :=
                mul_le_mul_of_nonneg_right hnorm_le (by positivity)
            _ = (((1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2) ^ 51)⁻¹ := by
                have ha : (1 : ℝ) + ‖Work.BoseB4.vec m‖ ^ 2 ≠ 0 := by positivity
                field_simp
  · exact summable_normWeight.mul_left Cchi

/-! ## 3. Young's inequality for a lattice convolution with a summable weight

Stated for an abstract nonnegative summable `w` on `ℤ³`; the translation invariance of the
lattice sum makes the total mass `B = ∑' m, w m` the sharp constant. -/

/-- **Weighted Cauchy–Schwarz**, pointwise in `n`: with `B = ∑' m, w m`,

`(Σ_{s∈S} w(n−s)|c s|)² ≤ B·Σ_{s∈S} w(n−s)c s²`.

The first factor is bounded by `B` via `Σ_{s∈S} w(n−s) ≤ Σ'_m w(n−m) = B` (the mirrored sum is a
reindexing of `w`), the second by the finite-dimensional weighted Cauchy–Schwarz
`Finset.sum_mul_sq_le_sq_mul_sq` applied to `√(w(n−s))` and `√(w(n−s))|c s|`. -/
theorem young_pointwise (w : (Fin 3 → ℤ) → ℝ) (hw : ∀ m, 0 ≤ w m) (hws : Summable w)
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℝ) (n : Fin 3 → ℤ) :
    (∑ s ∈ S, w (n - s) * |c s|) ^ 2
      ≤ (∑' m : Fin 3 → ℤ, w m) * ∑ s ∈ S, w (n - s) * c s ^ 2 := by
  have hshift : Summable (fun m : Fin 3 → ℤ => w (n - m)) :=
    (Equiv.summable_iff (Equiv.subLeft n)).mpr hws
  have hleB : (∑ s ∈ S, w (n - s)) ≤ ∑' m : Fin 3 → ℤ, w m := by
    calc (∑ s ∈ S, w (n - s)) ≤ ∑' m : Fin 3 → ℤ, w (n - m) :=
          Summable.sum_le_tsum S (fun i _ => hw (n - i)) hshift
      _ = ∑' m : Fin 3 → ℤ, w m := Equiv.tsum_eq (Equiv.subLeft n) w
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun s => Real.sqrt (w (n - s))) (fun s => Real.sqrt (w (n - s)) * |c s|)
  have e1 : (∑ s ∈ S, Real.sqrt (w (n - s)) * (Real.sqrt (w (n - s)) * |c s|))
      = ∑ s ∈ S, w (n - s) * |c s| := by
    refine Finset.sum_congr rfl fun s _ => ?_
    have h : Real.sqrt (w (n - s)) * Real.sqrt (w (n - s)) = w (n - s) := by
      rw [← sq, Real.sq_sqrt (hw _)]
    calc Real.sqrt (w (n - s)) * (Real.sqrt (w (n - s)) * |c s|)
        = (Real.sqrt (w (n - s)) * Real.sqrt (w (n - s))) * |c s| := by ring
      _ = w (n - s) * |c s| := by rw [h]
  have e2 : (∑ s ∈ S, (Real.sqrt (w (n - s))) ^ 2) = ∑ s ∈ S, w (n - s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Real.sq_sqrt (hw _)
  have e3 : (∑ s ∈ S, (Real.sqrt (w (n - s)) * |c s|) ^ 2)
      = ∑ s ∈ S, w (n - s) * c s ^ 2 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw _), sq_abs]
  rw [e1, e2, e3] at hcs
  calc (∑ s ∈ S, w (n - s) * |c s|) ^ 2
      ≤ (∑ s ∈ S, w (n - s)) * (∑ s ∈ S, w (n - s) * c s ^ 2) := hcs
    _ ≤ (∑' m : Fin 3 → ℤ, w m) * (∑ s ∈ S, w (n - s) * c s ^ 2) :=
        mul_le_mul_of_nonneg_right hleB
          (Finset.sum_nonneg (fun s _ => mul_nonneg (hw _) (sq_nonneg _)))

/-- `n ↦ Σ_{s∈S} w(n−s)c s²` is summable (a finite sum of translates of the summable `w`). -/
theorem young_summable (w : (Fin 3 → ℤ) → ℝ) (hws : Summable w)
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℝ) :
    Summable (fun n : Fin 3 → ℤ => ∑ s ∈ S, w (n - s) * c s ^ 2) := by
  have hshift : ∀ s : Fin 3 → ℤ, Summable (fun n : Fin 3 → ℤ => w (n - s)) := fun s =>
    (Equiv.summable_iff (Equiv.subRight s)).mpr hws
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((hshift a).mul_right (c a ^ 2)).add ih

/-- The total mass of that sum: `Σ'_n Σ_{s∈S} w(n−s)c s² = (Σ'_m w m)·Σ_{s∈S} c s²` (Fubini for
the finite index set `S`, then the translation invariance `Σ'_n w(n−s) = Σ'_m w m`). -/
theorem young_tsum (w : (Fin 3 → ℤ) → ℝ) (hws : Summable w)
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℝ) :
    (∑' n : Fin 3 → ℤ, ∑ s ∈ S, w (n - s) * c s ^ 2)
      = (∑' m : Fin 3 → ℤ, w m) * ∑ s ∈ S, c s ^ 2 := by
  have hshift : ∀ s : Fin 3 → ℤ, Summable (fun n : Fin 3 → ℤ => w (n - s)) := fun s =>
    (Equiv.summable_iff (Equiv.subRight s)).mpr hws
  have htsumShift : ∀ s : Fin 3 → ℤ, (∑' n : Fin 3 → ℤ, w (n - s)) = ∑' m : Fin 3 → ℤ, w m :=
    fun s => Equiv.tsum_eq (Equiv.subRight s) w
  rw [Summable.tsum_finsetSum (f := fun s n => w (n - s) * c s ^ 2) (s := S)
      (fun s _ => (hshift s).mul_right (c s ^ 2))]
  have hper : ∀ s ∈ S, (∑' n : Fin 3 → ℤ, w (n - s) * c s ^ 2)
      = (∑' m : Fin 3 → ℤ, w m) * c s ^ 2 := by
    intro s _
    rw [tsum_mul_right, htsumShift s]
  rw [Finset.sum_congr rfl hper, Finset.mul_sum]

/-! ## 4. The target -/

/-- **The lattice commutator bound** (work item (A2) of `LEAD_RULING_NH`): for a `L/κ`-Lipschitz
function `φ` on the dual lattice,

`Σ_{n∈ℤ³} (Σ_{s∈S} χ̂(2π(n−s))·(φ s − φ n)·c s)² ≤ (L·chiS1/κ)²·Σ_{s∈S} c s²`,

with `chiS1 = Σ'_m ‖2πm‖·|χ̂(2πm)|`.  This is Young's inequality for convolution with
`chiHatWeight` on `ℓ²(ℤ³)`: `|z_n| ≤ (L/κ)(w ∗ |c|)_n` and `‖w ∗ d‖₂ ≤ ‖w‖₁‖d‖₂ = chiS1‖c‖₂`. -/
theorem latticeComm_le (φ : (Fin 3 → ℤ) → ℝ) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ)
    (hφ : ∀ p q : Fin 3 → ℤ, |φ p - φ q| ≤ L * ‖Work.BoseB4.vec (p - q)‖ / κ)
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℝ) :
    (∑' n : Fin 3 → ℤ,
        (∑ s ∈ S, Work.BoseRowQ2.chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2)
      ≤ (L * Work.BoseRowQ2.chiS1 / κ) ^ 2 * ∑ s ∈ S, c s ^ 2 := by
  have hw : ∀ m : Fin 3 → ℤ, 0 ≤ chiHatWeight m := chiHatWeight_nonneg
  have hws : Summable chiHatWeight := summable_chiHatWeight
  have hLk : 0 ≤ L / κ := div_nonneg hL hκ.le
  -- (1) pointwise: the sum over `S` is dominated by `(L/κ)·Σ_s w(n−s)|c s|`
  have hpt : ∀ n : Fin 3 → ℤ,
      (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2
        ≤ (L / κ) ^ 2 * (∑ s ∈ S, chiHatWeight (n - s) * |c s|) ^ 2 := by
    intro n
    have habs : |∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s|
        ≤ (L / κ) * ∑ s ∈ S, chiHatWeight (n - s) * |c s| := by
      calc |∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s|
          ≤ ∑ s ∈ S, |chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s ∈ S, (L / κ) * (chiHatWeight (n - s) * |c s|) := by
            refine Finset.sum_le_sum fun s _ => ?_
            have hφ' : |φ s - φ n| ≤ L * ‖Work.BoseB4.vec (n - s)‖ / κ := by
              rw [← vec_sub_norm s n]
              exact hφ s n
            calc |chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s|
                = |chiHat (Work.BoseB4.vec (n - s))| * |φ s - φ n| * |c s| := by
                  rw [abs_mul, abs_mul]
              _ ≤ |chiHat (Work.BoseB4.vec (n - s))|
                    * (L * ‖Work.BoseB4.vec (n - s)‖ / κ) * |c s| := by
                  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                  exact mul_le_mul_of_nonneg_left hφ' (abs_nonneg _)
              _ = (L / κ) * (chiHatWeight (n - s) * |c s|) := by
                  rw [chiHatWeight]
                  ring_nf
        _ = (L / κ) * ∑ s ∈ S, chiHatWeight (n - s) * |c s| := by
            rw [Finset.mul_sum]
    calc (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2
        ≤ ((L / κ) * ∑ s ∈ S, chiHatWeight (n - s) * |c s|) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (mul_nonneg hLk
            (Finset.sum_nonneg (fun s _ => mul_nonneg (chiHatWeight_nonneg _) (abs_nonneg _))))]
          exact habs
      _ = (L / κ) ^ 2 * (∑ s ∈ S, chiHatWeight (n - s) * |c s|) ^ 2 := by rw [mul_pow]
  -- (2) Young, pointwise in `n`
  have hstep : ∀ n : Fin 3 → ℤ,
      (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2
        ≤ (L / κ) ^ 2 * ((∑' m : Fin 3 → ℤ, chiHatWeight m)
            * ∑ s ∈ S, chiHatWeight (n - s) * c s ^ 2) := by
    intro n
    exact le_trans (hpt n)
      (mul_le_mul_of_nonneg_left (young_pointwise chiHatWeight hw hws S c n)
        (sq_nonneg (L / κ)))
  have hT : Summable (fun n : Fin 3 → ℤ => ∑ s ∈ S, chiHatWeight (n - s) * c s ^ 2) :=
    young_summable chiHatWeight hws S c
  have hTt := young_tsum chiHatWeight hws S c
  have hM : Summable (fun n : Fin 3 → ℤ =>
      (L / κ) ^ 2 * ((∑' m : Fin 3 → ℤ, chiHatWeight m)
        * ∑ s ∈ S, chiHatWeight (n - s) * c s ^ 2)) :=
    (hT.mul_left (∑' m : Fin 3 → ℤ, chiHatWeight m)).mul_left ((L / κ) ^ 2)
  have hF : Summable (fun n : Fin 3 → ℤ =>
      (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hstep hM
  -- (3) sum the pointwise bounds
  have hmain := Summable.tsum_le_tsum hstep hF hM
  rw [tsum_mul_left, tsum_mul_left, hTt] at hmain
  have hfin : (∑' n : Fin 3 → ℤ,
        (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2)
      ≤ (L / κ) ^ 2 * ((∑' m : Fin 3 → ℤ, chiHatWeight m)
          * ((∑' m : Fin 3 → ℤ, chiHatWeight m) * ∑ s ∈ S, c s ^ 2)) := hmain
  calc (∑' n : Fin 3 → ℤ,
        (∑ s ∈ S, chiHat (Work.BoseB4.vec (n - s)) * (φ s - φ n) * c s) ^ 2)
      ≤ (L / κ) ^ 2 * ((∑' m : Fin 3 → ℤ, chiHatWeight m)
          * ((∑' m : Fin 3 → ℤ, chiHatWeight m) * ∑ s ∈ S, c s ^ 2)) := hfin
    _ = (L * chiS1 / κ) ^ 2 * ∑ s ∈ S, c s ^ 2 := by
        rw [← chiS1_eq_tsum_chiHatWeight]
        ring_nf

end Work.BoseRowQ2
