/-
# SeedPortraitCert — the level-0 cover of the ray chain

Area `Submission/Work/SeedPortraitCert/`.  This is the `/33`-analogue of
`Work.TripodCert.lvl0_coverT` and `Work.SeedCertRay.lvl0_cover2`: the level-0 pieces
`seg hN (angA j) 64 4096` (and `angB j`) of the external rays of the two cycles are covered by the
emitted level-0 disk data `diskUnion (lvl0DiskP j)`.

The emitted data `dskP 0` is *exactly* geometric: its `(jj,k)`-th disk (`jj < 10` the angle class,
`k < 6` the sub-piece index) has centre `lvl0m k · qdirP jj` and radius `32 · 2^k + 2`.  The cover
then follows from the far field (`Work.SeedCertRay.farFieldRay`): a point `rayPt hN θ r` is within
`64/r ≤ 1` of `r · rayDirection θ`, the direction is within `10⁻⁴` of `qdirP jj`
(`DirBound.lean`), and the radial displacement is at most `32 · 2^k`.
-/
import Mathlib
import Submission.Work.SeedPortraitCert.Data
import Submission.Work.SeedPortraitCert.Angles
import Submission.Work.SeedPortraitCert.DirBound
import Submission.Work.SeedCertRay.lvl0_cover2
import Submission.Work.SeedCertRay.Final

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The geometric description of the level-0 data -/

/-- The `k`-th level-0 sub-disk of the angle class `jj` of the certificate: centre
`lvl0m k · qdirP jj`, radius `lvl0r k` (mantissa units). -/
def lvl0DiskPg (jj k : ℕ) : Disk :=
  ⟨Q (lvl0m k * gI dirBaseP (2 * (jj % 10))),
    Q (lvl0m k * gI dirBaseP (2 * (jj % 10) + 1)), Q (lvl0r k)⟩

/-- **The emitted level-0 data is the geometric one.** -/
theorem dskP0_shape (jj k : ℕ) (hjj : jj < 10) (hk : k < 6) :
    gI (dskP 0) (3 * (jj * NC + k)) = lvl0m k * gI dirBaseP (2 * jj) ∧
    gI (dskP 0) (3 * (jj * NC + k) + 1) = lvl0m k * gI dirBaseP (2 * jj + 1) ∧
    gI (dskP 0) (3 * (jj * NC + k) + 2) = lvl0r k := by
  interval_cases jj <;> interval_cases k <;> decide

/-- The `i`-th sub-disk of angle class `j` of level `0` is the geometric disk
`lvl0DiskPg j i.val`. -/
theorem lvl0DiskP_eq (j : ℕ) (i : Fin NC) : lvl0DiskP j i = lvl0DiskPg j i.val := by
  obtain ⟨h1, h2, h3⟩ :=
    dskP0_shape (j % 10) i.val (by omega) (by simpa [NC] using i.isLt)
  simp only [lvl0DiskP, boxOfP, dskOf, lvl0DiskPg, h1, h2, h3]

/-- The centre of `lvl0DiskPg jj k` is `lvl0m k · qdirP jj`. -/
theorem lvl0DiskPg_center (jj k : ℕ) :
    (lvl0DiskPg jj k).center = (lvl0m k : ℂ) * qdirP jj := by
  have hcc : ∀ q : ℚ, (q : ℂ) = ((q : ℝ) : ℂ) := fun q => rfl
  dsimp only [lvl0DiskPg, Disk.center]
  rw [Q_mul_cast, Q_mul_cast]
  simp only [qdirP, hcc]
  ring

/-- The radius of `lvl0DiskPg jj k` is `32 · 2^k + 2 + 2⁻⁴⁰`. -/
theorem lvl0DiskPg_rad (jj k : ℕ) :
    ((lvl0DiskPg jj k).r : ℝ) = 32 * 2 ^ k + 2 + 1 / 2 ^ 40 := by
  have hMS : ((MS : ℚ) : ℝ) = 2 ^ 40 := by norm_num [MS]
  have hMSZ : ((MSZ : ℤ) : ℝ) = 2 ^ 40 := by norm_num [MSZ]
  dsimp only [lvl0DiskPg]
  rw [Q, lvl0r]
  push_cast
  rw [hMS, hMSZ]
  field_simp

/-! ## The covering estimate -/

/-- **The far-field estimate of one sub-piece.** -/
theorem farfield_ray_estP {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2) (hφ : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {d : ℂ} {k : ℕ} (hk : k < 6)
    (hdir : ‖Work.Landing.rayDirection θ - d‖ ≤ 1 / 10000)
    {r : ℝ} (hrlo : 64 * 2 ^ k ≤ r) (hrhi : r ≤ 128 * 2 ^ k) :
    ‖Work.EL.rayPt hN θ r - (lvl0m k : ℂ) * d‖ ≤ 32 * 2 ^ k + 2 := by
  have ht1 : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have ht32 : (2:ℝ) ^ k ≤ 32 := by
    have hk5 : k ≤ 5 := by omega
    calc (2:ℝ)^k ≤ 2^5 := pow_le_pow_right₀ (by norm_num) hk5
      _ = 32 := by norm_num
  have hr64 : (64:ℝ) ≤ r := by linarith
  have hr1 : (1:ℝ) < r := by linarith
  have hmR : ((lvl0m k : ℤ) : ℝ) = 96 * (2:ℝ)^k := by simp [lvl0m]
  have hmnorm : ‖(lvl0m k : ℂ)‖ = 96 * 2 ^ k := by
    rw [Complex.norm_intCast, hmR, abs_of_nonneg (by positivity)]
  have hm32 : ‖(lvl0m k : ℂ)‖ ≤ 3072 := by rw [hmnorm]; linarith
  have hrm : |r - (lvl0m k : ℝ)| ≤ 32 * 2 ^ k := by
    rw [hmR, abs_le]
    constructor <;> linarith
  have hdir' : ‖Work.Landing.rayDirection θ‖ = 1 := by
    rw [Work.Landing.rayDirection, Complex.norm_exp]
    simp
  have hfar := farFieldRay hc hc2 hφ hN (θ := θ) (r := r) hr64 hr1
  have hsplit : Work.EL.rayPt hN θ r - (lvl0m k : ℂ) * d
      = (Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
        + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)
        + ((lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d) := by ring
  rw [hsplit]
  have h1 : ‖Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ‖ ≤ 1 := by
    have h2 : 64 / r ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < r)]
      linarith
    linarith
  have h2 : ‖(r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ‖
      ≤ 32 * 2 ^ k := by
    rw [show (r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ
          = ((r - (lvl0m k : ℝ) : ℝ) : ℂ) * Work.Landing.rayDirection θ from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hdir', mul_one]
    exact hrm
  have h3 : ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d‖ ≤ 2/5 := by
    rw [show (lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d
          = (lvl0m k : ℂ) * (Work.Landing.rayDirection θ - d) from by ring, norm_mul]
    have h4 := mul_le_mul hm32 hdir (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3072)
    linarith
  calc ‖(Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
          + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)
          + ((lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d)‖
      ≤ ‖(Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
          + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)‖
        + ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d‖ :=
          norm_add_le _ _
    _ ≤ (‖Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ‖
          + ‖(r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ‖)
        + ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * d‖ := by
          linarith [norm_add_le (Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
            ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)]
    _ ≤ 32 * 2 ^ k + 2 := by linarith

/-- **The far-field cover of one sub-piece.** -/
theorem lvl0DiskPg_mem_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2) (hφ : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {jj k : ℕ} (hk : k < 6)
    (hdir : ‖Work.Landing.rayDirection θ - qdirP jj‖ ≤ 1 / 10000)
    {r : ℝ} (hrlo : 64 * 2 ^ k ≤ r) (hrhi : r ≤ 128 * 2 ^ k) :
    (lvl0DiskPg jj k).mem (Work.EL.rayPt hN θ r) := by
  have hkey := farfield_ray_estP hN hc hc2 hφ hk hdir hrlo hrhi
  rw [Disk.mem, lvl0DiskPg_center jj k, lvl0DiskPg_rad jj k]
  linarith

/-- The `k`-fold subdivision of the level-0 piece, as a six-way case split. -/
theorem lvl0_cover_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar)
    (hc2 : ‖c‖ ≤ 2) {θ : ℝ} (j : ℕ) (hj : j < 10)
    (hdir : ‖Work.Landing.rayDirection θ - qdirP j‖ ≤ 1 / 10000) :
    Work.SeedCertRay.seg hN θ (Work.SeedCertRay.rhoL 1) (Work.SeedCertRay.rhoL 0)
      ⊆ Work.SeedCertRay.diskUnion (lvl0DiskP j) := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [Set.mem_Icc, rhoL_one, rhoL_zero] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rw [mem_diskUnion]
  rcases lt_or_ge r 128 with h0 | h0
  · refine ⟨⟨0, by norm_num [NC]⟩, ?_⟩
    rw [lvl0DiskP_eq j ⟨0, by norm_num [NC]⟩]
    exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 0) (by norm_num) hdir (by linarith) (by linarith)
  rcases lt_or_ge r 256 with h1 | h1
  · refine ⟨⟨1, by norm_num [NC]⟩, ?_⟩
    rw [lvl0DiskP_eq j ⟨1, by norm_num [NC]⟩]
    exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 1) (by norm_num) hdir (by linarith) (by linarith)
  rcases lt_or_ge r 512 with h2 | h2
  · refine ⟨⟨2, by norm_num [NC]⟩, ?_⟩
    rw [lvl0DiskP_eq j ⟨2, by norm_num [NC]⟩]
    exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 2) (by norm_num) hdir (by linarith) (by linarith)
  rcases lt_or_ge r 1024 with h3 | h3
  · refine ⟨⟨3, by norm_num [NC]⟩, ?_⟩
    rw [lvl0DiskP_eq j ⟨3, by norm_num [NC]⟩]
    exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 3) (by norm_num) hdir (by linarith) (by linarith)
  rcases lt_or_ge r 2048 with h4 | h4
  · refine ⟨⟨4, by norm_num [NC]⟩, ?_⟩
    rw [lvl0DiskP_eq j ⟨4, by norm_num [NC]⟩]
    exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 4) (by norm_num) hdir (by linarith) (by linarith)
  refine ⟨⟨5, by norm_num [NC]⟩, ?_⟩
  rw [lvl0DiskP_eq j ⟨5, by norm_num [NC]⟩]
  exact lvl0DiskPg_mem_of hN hc hc2 hφ (k := 5) (by norm_num) hdir (by linarith) (by linarith)

/-! ## The level-0 covers of the two cycles -/

/-- **(D0) of the `12/33`-chain.** -/
theorem lvl0_coverA {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (j : ℕ) (hj : j < 5) :
    Work.SeedCertRay.seg hN (angA j) (Work.SeedCertRay.rhoL 1) (Work.SeedCertRay.rhoL 0)
      ⊆ Work.SeedCertRay.diskUnion (lvl0DiskP j) :=
  lvl0_cover_of hN hφ hc hc2 j (by omega)
    (by simpa only [Nat.mod_eq_of_lt hj] using dirBoundA j hj)

/-- **(D0) of the `13/33`-chain.** -/
theorem lvl0_coverB {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (j : ℕ) (hj : j < 5) :
    Work.SeedCertRay.seg hN (angB j) (Work.SeedCertRay.rhoL 1) (Work.SeedCertRay.rhoL 0)
      ⊆ Work.SeedCertRay.diskUnion (lvl0DiskP (5 + j)) :=
  lvl0_cover_of hN hφ hc hc2 (5 + j) (by omega)
    (by simpa only [Nat.mod_eq_of_lt hj] using dirBoundB j hj)

end

end Work.SeedPortraitCert
