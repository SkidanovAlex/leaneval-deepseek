import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6Est.Kappa
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the data of `thm:BogHamDiag` and B4's mode decomposition

This module fixes the interface through which FS's `thm:BogHamDiag` is proved at
FS's parameters:

* `FsBogData n` — FS's data at the mesh-`n` mode lattice: the kernel `K`, the
  scalars `a, R, ρ_z, ℓ, μ, z, chiM, δ, ε_T, c₁, c₂, K_ℓ, s, d` and the
  localisation `χh` with its support (`χh = 0` beyond the kernel's cutoff `T`)
  and its normalisation `Σ_k χh(t_k)² ≤ ℓ³ chiM (1+δ)`;
* `FsBogDecomp D` — **B4's content, and the only hypothesis of the final
  theorem**: the second-quantised `𝒦^Bog` at the state equals the sum of the mode
  pair quadratic forms `fsQuadLin (𝒜_k) (ℬ_k) (𝒞_k)` evaluated at the (unit
  norm) pair states `φ k`, on FS's explicit `𝒜, ℬ, 𝒞`;
* `toBogHamInterface` — node B6's `BogHamInterface` built from that data, whose
  per-pair ground inequality is *proved* from B6's `pairForm_ground`
  (`Fock2ModeShift.fms_ground_estimate`), so that `decomp` is the only field a
  caller must supply.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

local notation "ℝ³" => Fin 3 → ℝ

/-- **FS's data at the mode lattice of mesh `meshD n`.**  Besides the ingredients
of `FsKernel`/the parameters, it carries the *localisation* `χh = χ̂_Λ(√(ρ_z a)·)`
with its support (inside the kernel's cutoff) and its `L²` normalisation
(`Σ_k χh² ≤ ℓ³ chiM (1+δ)`, FS's `(2π)⁻³∫|χ̂_Λ|² = ‖χ_Λ‖²_{L²} = chiM`). -/
structure FsBogData (n : ℕ) where
  K : FsKernel
  a : ℝ
  R : ℝ
  ρz : ℝ
  ℓ : ℝ
  μ : ℝ
  z : ℝ
  chiM : ℝ
  δ : ℝ
  εT : ℝ
  c1 : ℝ
  c2 : ℝ
  Kl : ℝ
  s : ℝ
  d : ℝ
  /-- FS's `χ̂_Λ(√(ρ_z a)·)` in scaled variables. -/
  χh : ℝ³ → ℝ
  /-- the localisation vanishes beyond the kernel's momentum cutoff. -/
  hχsupp : ∀ t : ℝ³, K.T < nrm t → χh t = 0
  /-- `chiM = ‖χ_Λ‖²_{L²} ≥ 0`. -/
  hchiM : 0 ≤ chiM
  /-- `δ = C(μa³)R²/a² ≥ 0`. -/
  hδ : 0 ≤ δ
  /-- FS's normalisation `(2π)⁻³∫|χ̂_Λ|² = ‖χ_Λ‖²_{L²} = chiM`. -/
  hχnorm : chiSqSum n χh ≤ ℓ ^ 3 * chiM * (1 + δ)
  /-- `ℓ³ ≥ 3` (FS: `ℓ ≫ 1`). -/
  hℓ3 : 3 ≤ ℓ ^ 3

/-- **B4's mode decomposition** at FS's data: the value of `𝒦^Bog` at the state
equals `½Σ_k (pair form value)` with FS's `𝒜_k, ℬ_k, 𝒞_k` and the (unit-norm)
pair states `φ k`.  This is the *only* hypothesis of the final theorem
`fsBogHamDiag_fs`. -/
structure FsBogDecomp {n : ℕ} (D : FsBogData n) where
  /-- the number of modes of the pair states. -/
  M : ℕ
  /-- the (unit-norm) state of the pair `(k, −k)`. -/
  φ : modeIdx n → ℕ × ℕ → ℝ
  hφ : ∀ k : modeIdx n, Submission.BoseGases.vanishOn M (φ k)
  hnorm : ∀ k : modeIdx n, Submission.BoseGases.rectNorm M (φ k) = 1
  /-- the value of `𝒦^Bog` at the state. -/
  Kbog : ℝ
  decomp : Kbog
    = ∑ k : modeIdx n,
        (1 / 2) * Submission.BoseGases.fsQuadLin
          (fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n k))
          (fsB D.ρz D.a D.K (modePos n k))
          (fsC D.ℓ D.ρz D.μ D.a D.z D.χh (modePos n k)) M (φ k)

/-! ## FS's elementary lower bounds -/

/-- **`𝒜_k + ℬ_k ≥ (16π − 2)ρ_z a` on the support of `χh`** — FS's
`𝒜(k)+ℬ(k) ≥ 2ρ_zŴ₁(0)(1 − C(μa³)R²/a²)`: on the support of the localisation
(which is inside the kernel's cutoff `T`) one has `β ≥ 8π − ηT ≥ 8π − 1`, whence
`𝒜+ℬ = ρ_z a(τ̃ + 2β) ≥ 2ρ_z a(8π − 1)`. -/
lemma fsAB_ge {ρz a : ℝ} (K : FsKernel) {εT c1 c2 : ℝ} (χh : ℝ³ → ℝ)
    (hρa : 0 ≤ ρz * a) (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hηT : K.η * K.T ≤ 1) (hχsupp : ∀ t : ℝ³, K.T < nrm t → χh t = 0)
    {t : ℝ³} (hχ0 : χh t ≠ 0) :
    (16 * Real.pi - 2) * (ρz * a) ≤ fsA ρz a K εT c1 c2 t + fsB ρz a K t := by
  have hr : 0 ≤ nrm t := Submission.BoseGases.eucNorm3_nonneg t
  have hle : nrm t ≤ K.T := by
    by_contra h
    exact hχ0 (hχsupp t (lt_of_not_ge h))
  have hβ : 8 * Real.pi - 1 ≤ K.β (nrm t) := by
    have h1 := K.beta_ge hr hle
    have h2 : K.η * nrm t ≤ K.η * K.T := mul_le_mul_of_nonneg_left hle K.ηnn
    linarith
  have hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) := fsTau_nonneg hε0 hε1 hr
  rw [fsA_add_fsB]
  have h2 : 2 * (8 * Real.pi - 1) ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) + 2 * K.β (nrm t) := by
    linarith
  calc (16 * Real.pi - 2) * (ρz * a) = ρz * a * (2 * (8 * Real.pi - 1)) := by ring
    _ ≤ ρz * a * (Work.BoseB6.fsTau εT c1 c2 (nrm t) + 2 * K.β (nrm t)) :=
        mul_le_mul_of_nonneg_left h2 hρa

/-- `𝒜 + ℬ > 0` (the same argument as `fsA_pos`: either `r ≤ T`, where
`β ≥ 8π − ηT > 0`, or `r > T > c₂`, where `τ̃ > 0`). -/
lemma fsSum_pos {ρz a : ℝ} (K : FsKernel) (hρz : 0 < ρz) (ha : 0 < a) {εT c1 c2 : ℝ}
    (hε0 : 0 ≤ εT) (hε1 : εT < 1) (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2)
    (hηT : K.η * K.T < 8 * Real.pi) (hTc : c1 < K.T) (t : ℝ³) :
    0 < fsA ρz a K εT c1 c2 t + fsB ρz a K t := by
  have hr : 0 ≤ nrm t := Submission.BoseGases.eucNorm3_nonneg t
  have key : 0 < Work.BoseB6.fsTau εT c1 c2 (nrm t) + K.β (nrm t) := by
    rcases lt_or_ge (nrm t) K.T with hT | hT
    · have h := (abs_le.mp (K.close _ hr hT.le)).1
      have h2 : K.η * nrm t < 8 * Real.pi :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT.le K.ηnn) hηT
      have h3 : 0 ≤ Work.BoseB6.fsTau εT c1 c2 (nrm t) :=
        fsTau_nonneg hε0 hε1.le hr
      have h4 : 0 ≤ K.β (nrm t) := K.nonneg _
      linarith
    · have hpos : 0 < Work.BoseB6.fsTau εT c1 c2 (nrm t) :=
        fsTau_pos hε0 hε1 hc1 (lt_of_lt_of_le hTc hT)
      linarith [K.nonneg (nrm t)]
  rw [fsA_add_fsB]
  have key2 : 0 < Work.BoseB6.fsTau εT c1 c2 (nrm t) + 2 * K.β (nrm t) := by
    linarith [K.nonneg (nrm t)]
  exact mul_pos (mul_pos hρz ha) key2

/-- **B4's decomposition plus FS's regime give node B6's `BogHamInterface`**,
with the per-pair Bogoliubov ground inequality *proved* from
`Work.BoseB6.pairForm_ground` (FS App. `theorem:bogolubov-complete`).  Thus
`FsBogDecomp.decomp` is the only unfilled field. -/
def toBogHamInterface {n : ℕ} (D : FsBogData n) (E : FsBogDecomp D)
    (hρz : 0 < D.ρz) (ha : 0 < D.a) (hε0 : 0 ≤ D.εT) (hε1 : D.εT ≤ 1 / 2)
    (hc1 : 0 ≤ D.c1) (hc12 : D.c1 ≤ D.c2) (hηT : D.K.η * D.K.T ≤ 1)
    (hc1T : D.c1 < D.K.T) :
    Work.BoseB6.BogHamInterface (modeIdx n) where
  Kbog := E.Kbog
  A := fun k => fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n k)
  B := fun k => fsB D.ρz D.a D.K (modePos n k)
  Ccoef := fun k => fsC D.ℓ D.ρz D.μ D.a D.z D.χh (modePos n k)
  q := fun k => Submission.BoseGases.fsQuadLin
    (fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n k))
    (fsB D.ρz D.a D.K (modePos n k))
    (fsC D.ℓ D.ρz D.μ D.a D.z D.χh (modePos n k)) E.M (E.φ k)
  Apos := fun k => fsA_pos D.K (mul_pos hρz ha) hε0 (by linarith [hε1]) hc1 hc12
    (by linarith [hηT, Real.pi_gt_three]) hc1T (modePos n k)
  Bsmall := fun k => fsB_abs_le_fsA D.K hε0 (by linarith [hε1]) hρz.le ha.le (modePos n k)
  AplusB := fun k => fsSum_pos D.K hρz ha hε0 (by linarith [hε1]) hc1 hc12
    (by linarith [hηT, Real.pi_gt_three]) hc1T (modePos n k)
  decomp := E.decomp
  pairGround := fun k => by
    have h := Work.BoseB6.pairForm_ground (A := fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n k))
      (B := fsB D.ρz D.a D.K (modePos n k))
      (L := fsC D.ℓ D.ρz D.μ D.a D.z D.χh (modePos n k)) (M := E.M) (φ := E.φ k)
      (fsA_pos D.K (mul_pos hρz ha) hε0 (by linarith [hε1]) hc1 hc12
        (by linarith [hηT, Real.pi_gt_three]) hc1T (modePos n k))
      (fsB_abs_le_fsA D.K hε0 (by linarith [hε1]) hρz.le ha.le (modePos n k))
      (fsSum_pos D.K hρz ha hε0 (by linarith [hε1]) hc1 hc12
        (by linarith [hηT, Real.pi_gt_three]) hc1T (modePos n k))
      (E.hφ k)
    rw [E.hnorm k] at h
    simpa using h

end Work.BoseB6Est
