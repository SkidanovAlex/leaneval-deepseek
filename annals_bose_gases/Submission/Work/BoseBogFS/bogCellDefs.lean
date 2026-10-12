import ChallengeDeps
import Submission.Work.BoseBogFS.betaSc_decay
import Submission.Work.BoseBogFS.betaSc_sub_le
import Submission.Work.BoseBogFS.bogParamsData
import Submission.Work.BoseBogFS.cleanRiemBdefs
import Submission.Work.BoseBogFS.tauScRad_ge_eighth
import Submission.Work.BoseBogFS.tauSc_le_fsTau
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogCellDefs` — the per-cell majorant `bogMaj` of the clean Riemann row

This module fixes the vocabulary of the *assembled* per-cell majorant used in
`Work.BoseBogFS.cleanFun_tsum_le_integral`.

Everything is in the *scaled* variables `t = k/√P`, `P = ρ·a v`:

* `bogMesh v ρ μ = δ` (scaled mesh), `bogHalf = Δ = δ√3/2`;
* `bogRLot`/`bogRHit` — the two edge radii of the cell of `n`; `bogULot`/`bogUHit` — `τ_s` there,
  `bogVNt` — `β_s` at the lattice point, `bogOm` — the `β`-oscillation bound (`betaSc_sub_le`);
* `bogBs v R` — a bound on `sup |β_s|` (`betaSc_decay`), `bogOscM` — the crude oscillation bound,
  `bogVs = bogBs + max 0 bogOscM`;
* **three** per-cell majorants:
  * `bogMajA` — the τ-ball region (`r_hi ≤ c₁`), where `τ_s ≡ 0` on the cell;
  * `bogMajB` — the intermediate region (`c₁ < r_hi ≤ 16√Vs`), the unconditional
    `√`-difference bound (`Work.BoseBogFS.psiSc_cell_sqrt_le`);
  * `bogMajC` — the bulk (`16√Vs < r_hi`), literally the right-hand side of the master
    oscillation bound (`Work.BoseBogFS.psiSc_sub_le_master`).

`bogMaj` is the case-split; the per-cell inequalities live in `bogCellBounds`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The extracted constants of the `β`-rows -/

/-- The constant of `betaSc_decay`: `|β_s t| ≤ bogKB(1+R)³/(a v (1+√(ρ a v)‖t‖))`. -/
noncomputable def bogKB : ℝ := Classical.choose betaSc_decay

lemma bogKB_nonneg : 0 ≤ bogKB := (Classical.choose_spec betaSc_decay).1

theorem bogKB_spec {v : E3 → ℝ} {h : ScatSol v} {R ρ μ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (t : E3) :
    |betaSc v h ρ μ t|
      ≤ bogKB * (1 + R) ^ 3 / (a v * (1 + Real.sqrt (ρ * a v) * ‖t‖)) :=
  (Classical.choose_spec betaSc_decay).2 hR hρ hav hv hvrad hv_supp hRℓ t

/-- The constant of `betaSc_sub_le`: the `β`-oscillation on a ball of radius `Δ`. -/
noncomputable def bogKOs : ℝ := Classical.choose betaSc_sub_le

lemma bogKOs_nonneg : 0 ≤ bogKOs := (Classical.choose_spec betaSc_sub_le).1

theorem bogKOs_spec {v : E3 → ℝ} {h : ScatSol v} {R ρ μ rlo D : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) (hD : 0 ≤ D) (hrlo : 0 < rlo)
    (t t' : E3) (hdist : ‖t - t'‖ ≤ D) (hfar : rlo + D ≤ ‖t'‖) :
    |betaSc v h ρ μ t - betaSc v h ρ μ t'|
      ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * D
          / (1 + Real.sqrt (ρ * a v) * rlo) :=
  (Classical.choose_spec betaSc_sub_le).2 hR hρ hav hv hvrad hv_supp hRℓ hD hrlo t t' hdist hfar

/-! ## 2. The scaled lattice point is the lattice point of the scaled mesh -/

/-- `tSca v ρ μ n = lpt (bogMesh v ρ μ) n`. -/
lemma tSca_eq_lpt (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    tSca v ρ μ n = lpt (bogMesh v ρ μ) n := by
  ext i
  simp only [tSca, kAt, lpt, Work.BoseB4.vec, bogMesh, WithLp.ofLp_smul, Pi.smul_apply,
    WithLp.ofLp_toLp, smul_eq_mul]
  ring

lemma norm_tSca (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    ‖tSca v ρ μ n‖ = ‖lpt (bogMesh v ρ μ) n‖ := by rw [tSca_eq_lpt]

/-! ## 3. The region constants -/

/-- A bound on `sup_t |β_s t|`: `max 1 (K(1+R)³/a v)`. -/
def bogBs (v : E3 → ℝ) (R : ℝ) : ℝ :=
  max 1 (bogKB * (1 + R) ^ 3 / a v)

/-- The crude `β`-oscillation bound `K(1+R)³√(ρ/a)Δ` (the `bogOscK` denominator dropped). -/
def bogOscM (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  bogKOs * (1 + R) ^ 3 * Real.sqrt (ρ / a v) * bogHalf v ρ μ

/-- The natural bound on `V = max |v_lo| |v_hi|`: `bogBs + max 0 (bogOscM)`. -/
def bogVs (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  bogBs v R + max 0 (bogOscM v R ρ μ)

/-- The threshold separating the `√`-region (`bogMajB`) from the bulk (`bogMajC`). -/
def bogBigThr (v : E3 → ℝ) (R ρ μ : ℝ) : ℝ :=
  16 * Real.sqrt (bogVs v R ρ μ)

/-! ## 4. The cell gadgets (in terms of `tSca`) -/

/-- The lower edge radius of the cell of `n`. -/
def bogRLot (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  ‖tSca v ρ μ n‖ - bogHalf v ρ μ

/-- The upper edge radius of the cell of `n`. -/
def bogRHit (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  ‖tSca v ρ μ n‖ + bogHalf v ρ μ

/-- `τ_s` at the lower edge radius of the cell of `n`. -/
def bogULot (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  tauScRad v ρ μ (bogRLot v ρ μ n)

/-- `τ_s` at the upper edge radius of the cell of `n`. -/
def bogUHit (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  tauScRad v ρ μ (bogRHit v ρ μ n)

/-- `β_s` at the lattice point of the cell of `n`. -/
def bogVNt (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  betaSc v h ρ μ (tSca v ρ μ n)

/-- The honest `β`-oscillation bound of the cell of `n` (`bogOscK` at `r_lo`). -/
def bogOm (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogOscK bogKOs R ρ (a v) (bogHalf v ρ μ) (bogRLot v ρ μ n)

/-- The lower endpoint of `β_s` on the cell of `n`. -/
def bogVlot (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogVNt v h ρ μ n - bogOm v h R ρ μ n

/-- The upper endpoint of `β_s` on the cell of `n`. -/
def bogVhit (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogVNt v h ρ μ n + bogOm v h R ρ μ n

/-- `V = max |v_lo| |v_hi|` of the cell of `n`. -/
def bogVmaxt (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  max |bogVlot v h R ρ μ n| |bogVhit v h R ρ μ n|

/-! ## 5. The three per-cell majorants -/

/-- **Region A** (`r_hi ≤ c₁`, `τ_s ≡ 0` on the cell): `o + B²/(2 r_lo²)`. -/
def bogMajA (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  bogOscM v R ρ μ + (bogBs v R) ^ 2 / (2 * (bogRLot v ρ μ n) ^ 2)

/-- **Region B** (`c₁ < r_hi ≤ 16√Vs`): the unconditional `√`-difference bound. -/
def bogMajB (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  (bogUHit v ρ μ n - bogULot v ρ μ n)
    + Real.sqrt ((bogUHit v ρ μ n - bogULot v ρ μ n)
        * (2 * bogUHit v ρ μ n + 2 * bogVmaxt v h R ρ μ n))
    + bogOm v h R ρ μ n + Real.sqrt (2 * bogOm v h R ρ μ n * bogUHit v ρ μ n)
    + bogOm v h R ρ μ n * bogVmaxt v h R ρ μ n / (bogRLot v ρ μ n) ^ 2
    + (bogVmaxt v h R ρ μ n) ^ 2
        * (1 / (2 * (bogRLot v ρ μ n) ^ 2) - 1 / (2 * (bogRHit v ρ μ n) ^ 2))

/-- **Region C** (`16√Vs < r_hi`): the master oscillation bound
(`psiSc_sub_le_master`, with `oscβ = bogOm`). -/
def bogMajC (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  let r_lo := bogRLot v ρ μ n
  let r_hi := bogRHit v ρ μ n
  let u_lo := bogULot v ρ μ n
  let u_hi := bogUHit v ρ μ n
  let v_lo := bogVlot v h R ρ μ n
  let v_hi := bogVhit v h R ρ μ n
  let W_lo := Real.sqrt (u_lo ^ 2 + 2 * u_lo * v_lo)
  let S_lo := u_lo + v_lo + W_lo
  let V := bogVmaxt v h R ρ μ n
  let D := max 0 (r_hi ^ 2 - u_lo)
  2 * (V ^ 2 / (S_lo * W_lo)) * (u_hi - u_lo)
    + 2 * (V * (2 * D + 2 * V) / (r_lo ^ 2 * S_lo) + V ^ 2 * (1 + u_hi / W_lo) / S_lo ^ 2)
        * (v_hi - v_lo)
    + 2 * (V ^ 2 / 2) * (1 / r_lo ^ 2 - 1 / r_hi ^ 2)

/-- **The assembled per-cell majorant** (scaled units): `0` at the origin cell,
`bogMajA` on the τ-ball, `bogMajB` in the intermediate region and `bogMajC` in the bulk. -/
def bogMaj (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if n = 0 then 0
  else if bogRHit v ρ μ n ≤ bogC1 v ρ μ then bogMajA v h R ρ μ n
  else if bogRHit v ρ μ n ≤ bogBigThr v R ρ μ then bogMajB v h R ρ μ n
  else bogMajC v h R ρ μ n

/-! ## 6. Elementary nonnegativity -/

lemma bogHalf_pos {v : E3 → ℝ} {ρ μ : ℝ} (hδ : 0 < bogMesh v ρ μ) :
    0 < bogHalf v ρ μ := by
  rw [bogHalf]
  exact div_pos (mul_pos hδ (Real.sqrt_pos.mpr (by norm_num))) (by norm_num)

lemma bogOscM_nonneg {v : E3 → ℝ} {R ρ μ : ℝ} (hR : 0 ≤ R) (hav : 0 < a v)
    (hρ : 0 < ρ) (hδ : 0 < bogMesh v ρ μ) : 0 ≤ bogOscM v R ρ μ := by
  rw [bogOscM]
  have h1 : 0 ≤ Real.sqrt (ρ / a v) := Real.sqrt_nonneg _
  have h2 : 0 ≤ bogKOs * (1 + R) ^ 3 :=
    mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
  exact mul_nonneg (mul_nonneg h2 h1) (bogHalf_pos hδ).le

lemma bogBs_pos (v : E3 → ℝ) (R : ℝ) : 0 < bogBs v R := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma bogVs_pos (v : E3 → ℝ) (R ρ μ : ℝ) : 0 < bogVs v R ρ μ := by
  have h : 0 < bogBs v R := bogBs_pos v R
  have h2 : 0 ≤ max 0 (bogOscM v R ρ μ) := le_max_left _ _
  unfold bogVs
  linarith

lemma bogBigThr_pos (v : E3 → ℝ) (R ρ μ : ℝ) : 0 < bogBigThr v R ρ μ := by
  rw [bogBigThr]
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (bogVs_pos v R ρ μ))

/-! ## 5b. The three gated pieces (for the sums) -/

/-- The region-A piece of `bogMaj`, gated. -/
def bogT1 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRHit v ρ μ n ≤ bogC1 v ρ μ then bogMajA v h R ρ μ n else 0

/-- The region-B piece of `bogMaj`, gated. -/
def bogT2 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogRHit v ρ μ n ≤ bogBigThr v R ρ μ then bogMajB v h R ρ μ n else 0

/-- The region-C piece of `bogMaj`, gated and truncated below at `0`. -/
def bogT3 (v : E3 → ℝ) (h : ScatSol v) (R ρ μ : ℝ) (n : Fin 3 → ℤ) : ℝ :=
  if bogBigThr v R ρ μ < bogRHit v ρ μ n then max 0 (bogMajC v h R ρ μ n) else 0

end Work.BoseBogFS
