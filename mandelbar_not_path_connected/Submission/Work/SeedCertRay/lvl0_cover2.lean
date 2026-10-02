/-
# `Work.SeedCertRay.lvl0_cover2` — the level-0 cover of the ray chain

The level-0 pieces of the ray chain are the segments `seg hN (T^[j] α₁) 64 4096` of the ten
external rays of the `α₁`-orbit between the levels `ρ 1 = 64` and `ρ 0 = 4096`.  This module
proves that each of them is covered by the emitted level-0 disk data `diskUnion (Dd 0 j)`.

The emitted data `dsk 0` (`Work.SeedCertRay.DataAll`) is *exactly* geometric: its `(jj,k)`-th
disk, `jj < 10` the angle index and `k < 6` the sub-piece index, has

* centre `lvl0mid k · q_j` with `lvl0mid k = 96 · 2^k` the midpoint of the `k`-th sub-interval
  `[64 · 2^k, 128 · 2^k]` of `[64, 4096]` along the base direction `q_j = qdirC jj`, and
* radius `32 · 2^k + 2` (half the sub-interval, plus the tolerance `2`).

This is `dsk0_shape` + `Dd_zero_eq`.  The covering then follows from the far field: a point
`rayPt hN θ r` is within `64/r ≤ 1` of `r · rayDirection θ` (`farFieldRay`), the direction is
within `10⁻⁴` of `qdirC jj` (`hdir`), and the radial displacement `|r - 96·2^k| ≤ 32·2^k`
inside the `k`-th sub-interval.  Since `r ≤ 4096` and `|lvl0mid k| ≤ 3072`, the total error is
at most `1 + 32·2^k + 3072·10⁻⁴ < 32·2^k + 2`, with room to spare against the certified radius.
-/
import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.farFieldRay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

set_option linter.unusedVariables false

/-! ## The geometric description of the level-0 data -/

/-- The midpoint `96 · 2^k` of the `k`-th sub-interval `[64·2^k, 128·2^k]` of `[64, 4096]`
(mantissa units: the radius of a level-0 disk is `lvl0m k · q` with `q` a base direction). -/
def lvl0m (k : ℕ) : ℤ := 96 * 2 ^ k

/-- The mantissa of the radius `32 · 2^k + 2` of the `k`-th level-0 sub-disk. -/
def lvl0r (k : ℕ) : ℤ := (32 * 2 ^ k + 2) * MSZ + 1

/-- The `k`-th level-0 disk of the angle `jj`: centre `lvl0m k · q_jj`, radius `lvl0r k`. -/
def lvl0Disk (jj k : ℕ) : Disk :=
  ⟨Q (lvl0m k * gI dirBase (2 * jj)), Q (lvl0m k * gI dirBase (2 * jj + 1)), Q (lvl0r k)⟩

/-- **The emitted level-0 data is the geometric one.**  For every angle index `jj < 10` and
every sub-piece index `k < 6`, the `(jj,k)`-th triple of `dsk 0` is
`(lvl0m k · x_jj, lvl0m k · y_jj, lvl0r k)` with `(x_jj, y_jj) = dirBase` at `jj`. -/
theorem dsk0_shape (jj k : ℕ) (hjj : jj < 10) (hk : k < 6) :
    gI (dsk 0) (3 * (jj * NC + k)) = lvl0m k * gI dirBase (2 * jj) ∧
    gI (dsk 0) (3 * (jj * NC + k) + 1) = lvl0m k * gI dirBase (2 * jj + 1) ∧
    gI (dsk 0) (3 * (jj * NC + k) + 2) = lvl0r k := by
  interval_cases jj <;> interval_cases k <;> decide

/-- The `k`-th sub-disk of angle `j` of level `0` is the geometric disk `lvl0Disk (j % 10) k`. -/
theorem Dd_zero_eq (j k : ℕ) (hk : k < 6) :
    Dd 0 j ⟨k, hk⟩ = lvl0Disk (j % 10) k := by
  obtain ⟨h1, h2, h3⟩ := dsk0_shape (j % 10) k (Nat.mod_lt j (by norm_num)) hk
  simp only [Dd, dskOf, lvl0Disk, h1, h2, h3]

/-! ## Centre and radius of the geometric level-0 disks -/

/-- The two-coordinate decoding of a mantissa product: `Q (m a) = m · Q a`. -/
lemma Q_mul_cast (m a : ℤ) :
    ((((Q (m * a) : ℚ)) : ℝ) : ℂ) = (m : ℂ) * ((((Q a : ℚ)) : ℝ) : ℂ) := by
  have hR : ((Q (m * a) : ℚ) : ℝ) = (m : ℝ) * ((Q a : ℚ) : ℝ) := by
    simp only [Q, Int.cast_mul]
    push_cast
    ring
  rw [hR]
  push_cast
  ring

/-- The centre of `lvl0Disk jj k` is `lvl0m k · qdirC jj`. -/
theorem lvl0Disk_center (jj k : ℕ) : (lvl0Disk jj k).center = (lvl0m k : ℂ) * qdirC jj := by
  have hcc : ∀ q : ℚ, (q : ℂ) = ((q : ℝ) : ℂ) := fun q => rfl
  dsimp only [lvl0Disk, Disk.center]
  rw [Q_mul_cast, Q_mul_cast]
  simp only [qdirC, hcc]
  ring

/-- The radius of `lvl0Disk jj k` is `32 · 2^k + 2 + 2⁻⁴⁰`, i.e. `32 · 2^k + 2` up to `1/MSZ`. -/
theorem lvl0Disk_rad (jj k : ℕ) : ((lvl0Disk jj k).r : ℝ) = 32 * 2 ^ k + 2 + 1 / 2 ^ 40 := by
  have hMS : ((MS : ℚ) : ℝ) = 2 ^ 40 := by norm_num [MS]
  have hMSZ : ((MSZ : ℤ) : ℝ) = 2 ^ 40 := by norm_num [MSZ]
  dsimp only [lvl0Disk]
  rw [Q, lvl0r]
  push_cast
  rw [hMS, hMSZ]
  field_simp

/-! ## The covering estimate -/

/-- **The far-field cover of one sub-piece.**  If `r` lies in the `k`-th sub-interval
`[64·2^k, 128·2^k]` of `[64, 4096]` (`k < 6`) and the ray direction is within `10⁻⁴` of
`qdirC jj`, then `rayPt hN θ r` lies in the level-0 disk `lvl0Disk jj k`.

The estimate is `‖rayPt - r·d‖ ≤ 64/r ≤ 1` (`farFieldRay`), `‖r·d - m·d‖ = |r - m| ≤ 32·2^k`
and `‖m·d - m·q_jj‖ ≤ 3072 · 10⁻⁴`, against the radius `32·2^k + 2`. -/
theorem lvl0Disk_mem_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2) (hφ : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {jj k : ℕ} (hk : k < 6)
    (hdir : ‖Work.Landing.rayDirection θ - qdirC jj‖ ≤ 1 / 10000)
    {r : ℝ} (hrlo : 64 * 2 ^ k ≤ r) (hrhi : r ≤ 128 * 2 ^ k) :
    (lvl0Disk jj k).mem (Work.EL.rayPt hN θ r) := by
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
  have key : ‖Work.EL.rayPt hN θ r - (lvl0m k : ℂ) * qdirC jj‖ ≤ 32 * 2 ^ k + 2 := by
    have hsplit : Work.EL.rayPt hN θ r - (lvl0m k : ℂ) * qdirC jj
        = (Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
          + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)
          + ((lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj) := by ring
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
    have h3 : ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj‖ ≤ 2/5 := by
      rw [show (lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj
            = (lvl0m k : ℂ) * (Work.Landing.rayDirection θ - qdirC jj) from by ring, norm_mul]
      have h4 := mul_le_mul hm32 hdir (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3072)
      linarith
    calc ‖(Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
            + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)
            + ((lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj)‖
        ≤ ‖(Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
            + ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)‖
          + ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj‖ :=
            norm_add_le _ _
      _ ≤ (‖Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ‖
            + ‖(r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ‖)
          + ‖(lvl0m k : ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * qdirC jj‖ := by
            linarith [norm_add_le (Work.EL.rayPt hN θ r - (r:ℂ) * Work.Landing.rayDirection θ)
              ((r:ℂ) * Work.Landing.rayDirection θ - (lvl0m k : ℂ) * Work.Landing.rayDirection θ)]
      _ ≤ 32 * 2 ^ k + 2 := by linarith
  rw [Disk.mem, lvl0Disk_center jj k, lvl0Disk_rad jj k]
  linarith

/-! ## The target -/

theorem lvl0_cover2 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hc2 : ‖c‖ ≤ 2) (j : ℕ) (hj : j < 10) (hdir : ‖Work.Landing.rayDirection ((Work.EL.T^[j]) Work.EL.alpha1) - Work.SeedCertRay.qdirC (j % 10)‖ ≤ 1 / 10000) :
    Work.SeedCertRay.seg hN ((Work.EL.T^[j]) Work.EL.alpha1) 64 4096 ⊆ Work.SeedCertRay.diskUnion (Work.SeedCertRay.Dd 0 j) := by
  intro z hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hr1, hr2⟩ := hr
  rw [mem_diskUnion]
  rcases lt_or_ge r 128 with h0 | h0
  · refine ⟨⟨0, by norm_num [NC]⟩, ?_⟩
    rw [Dd_zero_eq j 0 (by norm_num)]
    exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge r 256 with h1 | h1
  · refine ⟨⟨1, by norm_num [NC]⟩, ?_⟩
    rw [Dd_zero_eq j 1 (by norm_num)]
    exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge r 512 with h2 | h2
  · refine ⟨⟨2, by norm_num [NC]⟩, ?_⟩
    rw [Dd_zero_eq j 2 (by norm_num)]
    exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge r 1024 with h3 | h3
  · refine ⟨⟨3, by norm_num [NC]⟩, ?_⟩
    rw [Dd_zero_eq j 3 (by norm_num)]
    exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge r 2048 with h4 | h4
  · refine ⟨⟨4, by norm_num [NC]⟩, ?_⟩
    rw [Dd_zero_eq j 4 (by norm_num)]
    exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨⟨5, by norm_num [NC]⟩, ?_⟩
  rw [Dd_zero_eq j 5 (by norm_num)]
  exact lvl0Disk_mem_of hN hc hc2 hφ (by norm_num) hdir (by norm_num; linarith) (by norm_num; linarith)

end

end Work.SeedCertRay
