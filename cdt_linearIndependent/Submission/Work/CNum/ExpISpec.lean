import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.angIv_facts
import Submission.Work.CNum.angIv_gaps
import Submission.Work.CNum.CosP_tail
import Submission.Work.CNum.SinP_tail
import Submission.Work.CNum.ExpAux.csOfInterval_mem
import Submission.Work.CNum.ExpAux.qcos_qsin_mem
import Submission.Work.CNum.ExpAux.sin_sub_sin_lower

/-!
# `Work.CNum.ExpISpec` — soundness of the table `expI`

`Work.CNum.expI k` is the mantissa-level interval enclosure of `e^{i k π/1024}` (`k ≤ 1024`)
computed by `Fx.lean`: the angle is split as `kπ/1024 = q·(π/4) + m·(π/1024)` with `q = k/256`,
`m = k % 256`, and the two factors are evaluated by the tables `qcos`/`qsin` (exact values of
`cos`/`sin` at multiples of `π/4`, with `√(1/2)` from the integer square root) and `csOf`
(the `TAYN = 11` Taylor partial sums on the angle interval `angIv m`).

This file assembles those soundness statements into

`expI k ∋ e^{i k π/1024}`   for all `k ≤ 1024`,

i.e. `Work.CNum.ExpISpec`.

* `ExpAux.csOfInterval_mem` gives the enclosure of the *partial sums* `cosP · 11`, `sinP · 11`
  on the whole angle interval `angIv m`;
* `CosP_tail`/`SinP_tail` compare those partial sums with `cos`/`sin` (alternating series, error
  `< 2/24!`, `< 2/25!`);
* the numerical gap `angIv_gaps` (`θ - lo ≥ 2⁻⁴⁰`, `hi - θ ≥ 2⁻⁴¹`) shows that the endpoint of the
  enclosure overshoots the *partial sum* by more than the truncation error, which is what upgrades
  "partial sums" to "`cos`/`sin`" in `csOf_mem` below (`cos_sub_cos_lower'`, `ExpAux.sin_sub_sin_lower`).

The final step multiplies the two enclosures with the addition theorems of `cos`/`sin`.
-/

namespace Work.CNum

open Work.ANum

/-! ## 1. The quantitative gap between the partial sums and `cos`/`sin` -/

/-- On `[0, π/2]` the sine is at least half its argument. -/
lemma sin_ge_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) : x / 2 ≤ Real.sin x := by
  have h := Real.mul_le_sin h0 h1
  have hp : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have h2 := mul_le_mul_of_nonneg_right hp h0
  linarith

/-- **Lower bound for `cos lr - cos θ`.**  If `lr ≤ θ ≤ π/4` and `θ ≥ 3/1024` while the gap
`θ - lr ≥ 2⁻⁴⁰` is at least one `angIv`-step, then `cos lr - cos θ` already dominates the Taylor
truncation error `4/24!`.  (The bound proved is `cos lr - cos θ ≥ θ(θ - lr)/8 ≥ 3·2⁻⁵³`.) -/
lemma cos_sub_cos_lower' {lr θ : ℝ} (h0 : 0 ≤ lr) (_h1 : lr ≤ θ) (h2 : θ ≤ Real.pi / 4)
    (h3 : (3 : ℝ) / 1024 ≤ θ) (h4 : ((2 : ℝ) ^ 40)⁻¹ ≤ θ - lr) :
    4 * ((Nat.factorial 24 : ℝ))⁻¹ ≤ Real.cos lr - Real.cos θ := by
  have h20 : (0 : ℝ) < ((2 : ℝ) ^ 40)⁻¹ := by norm_num
  have hlr0 : (0 : ℝ) ≤ θ - lr := le_trans h20.le h4
  have hA : θ / 4 ≤ Real.sin ((lr + θ) / 2) := by
    have h0' : (0 : ℝ) ≤ (lr + θ) / 2 := by linarith
    have h1' : (lr + θ) / 2 ≤ Real.pi / 2 := by linarith [h2, Real.pi_pos]
    have := sin_ge_half h0' h1'
    linarith
  have hB : (θ - lr) / 4 ≤ Real.sin ((θ - lr) / 2) := by
    have h0' : (0 : ℝ) ≤ (θ - lr) / 2 := by linarith
    have h1' : (θ - lr) / 2 ≤ Real.pi / 2 := by linarith [h2, Real.pi_pos]
    have := sin_ge_half h0' h1'
    linarith
  have hA0 : (0 : ℝ) ≤ θ / 4 := by linarith
  have hB0 : (0 : ℝ) ≤ (θ - lr) / 4 := by linarith
  have hAA : (0 : ℝ) ≤ Real.sin ((lr + θ) / 2) := le_trans hA0 hA
  have hBB : (0 : ℝ) ≤ Real.sin ((θ - lr) / 2) := le_trans hB0 hB
  have hid : Real.cos lr - Real.cos θ
      = 2 * Real.sin ((lr + θ) / 2) * Real.sin ((θ - lr) / 2) := by
    rw [Real.cos_sub_cos]
    rw [show (lr - θ) / 2 = -((θ - lr) / 2) by ring, Real.sin_neg]
    ring
  rw [hid]
  have hprod : 2 * (θ / 4) * ((θ - lr) / 4)
      ≤ 2 * Real.sin ((lr + θ) / 2) * Real.sin ((θ - lr) / 2) := by
    have h := mul_le_mul hA hB hB0 hAA
    linarith
  have hkey : (3 : ℝ) / 2 ^ 53 ≤ 2 * (θ / 4) * ((θ - lr) / 4) := by
    have hbc : ((3 : ℝ) / 1024) * ((2 : ℝ) ^ 40)⁻¹ ≤ θ * (θ - lr) :=
      mul_le_mul h3 h4 h20.le (le_trans (by norm_num : (0 : ℝ) ≤ 3 / 1024) h3)
    have he : ((3 : ℝ) / 1024) * ((2 : ℝ) ^ 40)⁻¹ / 8 = (3 : ℝ) / 2 ^ 53 := by norm_num
    have hgoal : 2 * (θ / 4) * ((θ - lr) / 4) = θ * (θ - lr) / 8 := by ring
    rw [hgoal]
    linarith [hbc, he]
  have hfin : 4 * ((Nat.factorial 24 : ℝ))⁻¹ ≤ (3 : ℝ) / 2 ^ 53 := by norm_num
  linarith

/-! ## 2. From the Taylor partial sums to `cos`/`sin` -/

/-- `(csOf m).re` encloses `cosP z 11` for `z ∈ angIv m`; the angular gap of `angIv_gaps` separates
`θ = mπ/1024` from the endpoints of its interval, which absorbs the Taylor truncation error.  The
degenerate case `m = 0` has `angIv 0 = [0,0]`, so `θ = 0` and both partial sums are exact. -/
lemma csOf_mem (m : ℕ) (hm : m ≤ 255) :
    (csOf m).re.Mem (Real.cos ((m : ℝ) * Real.pi / 1024)) ∧
    (csOf m).im.Mem (Real.sin ((m : ℝ) * Real.pi / 1024)) := by
  by_cases h0 : m = 0
  · subst h0
    have hz : (angIv 0).Mem (0 : ℝ) := by
      refine ⟨?_, ?_⟩ <;> norm_num [angIv, Iv.Mem, m2r]
    obtain ⟨hre, him⟩ := ExpAux.csOfInterval_mem (m := 0) hz
    rw [cosP_zero] at hre
    rw [sinP_zero] at him
    exact ⟨by simpa [Real.cos_zero] using hre, by simpa [Real.sin_zero] using him⟩
  · have hm1 : 1 ≤ m := by omega
    set θ : ℝ := (m : ℝ) * Real.pi / 1024 with hθdef
    set lr : ℝ := m2r (angIv m).lo with hlrdef
    set ur : ℝ := m2r (angIv m).hi with hurdef
    have hlo0 : 0 ≤ lr := angIv_lo_nonneg m
    have hlole : lr ≤ θ := angIv_lo_le m
    have hlehi : θ ≤ ur := angIv_hi_ge m
    have hhi4 : ur ≤ Real.pi / 4 := angIv_hi_le_pi_div_four m hm
    have hθ0 : 0 ≤ θ := hlo0.trans hlole
    have hθ4 : θ ≤ Real.pi / 4 := hlehi.trans hhi4
    have hgap : ((2 : ℝ) ^ 40)⁻¹ ≤ θ - lr := angIv_gaps.1 m hm1
    have hgap' : ((2 : ℝ) ^ 41)⁻¹ ≤ ur - θ := angIv_gaps.2 m hm1
    have hθ3 : (3 : ℝ) / 1024 ≤ θ := by
      rw [hθdef]
      have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      nlinarith [Real.pi_gt_three]
    have hmemθ : (angIv m).Mem θ := angIv_facts.1 m
    have hmemlr : (angIv m).Mem lr := ⟨le_rfl, hlole.trans hlehi⟩
    have hmemur : (angIv m).Mem ur := ⟨hlole.trans hlehi, le_rfl⟩
    obtain ⟨hreθ, himθ⟩ := ExpAux.csOfInterval_mem hmemθ
    obtain ⟨hrelr, _⟩ := ExpAux.csOfInterval_mem hmemlr
    obtain ⟨_, himur⟩ := ExpAux.csOfInterval_mem hmemur
    have htailθ := CosP_tail hθ0 hθ4
    have htaillr := CosP_tail hlo0 (hlole.trans hθ4)
    have htailθs := SinP_tail hθ0 hθ4
    have htailurs := SinP_tail (hθ0.trans hlehi) hhi4
    have hmargC := cos_sub_cos_lower' hlo0 hlole hθ4 hθ3 hgap
    have hmargS := ExpAux.sin_sub_sin_lower hθ0 hlehi hhi4 hgap'
    refine ⟨⟨hreθ.1.trans htailθ.1, ?_⟩, ⟨himθ.1.trans htailθs.1, ?_⟩⟩
    · linarith [hreθ.2, hrelr.1, hrelr.2, htailθ.1, htailθ.2, htaillr.2, hmargC]
    · linarith [himθ.2, himur.1, himur.2, htailθs.1, htailθs.2, htailurs.2, hmargS]

/-! ## 3. The table `expI` -/

theorem ExpISpec {k : ℕ} (hk : k ≤ 1024) :
    Cpx.Mem (expI k) (Complex.exp (Complex.I * ((k : ℂ) * Real.pi / 1024))) := by
  have hq4 : k / 256 ≤ 4 := by omega
  have hm255 : k % 256 ≤ 255 := by
    have := Nat.mod_lt k (by norm_num : 0 < 256)
    omega
  have hkdecomp : k = 256 * (k / 256) + k % 256 := (Nat.div_add_mod k 256).symm
  have hkR : (k : ℝ) = 256 * ((k / 256 : ℕ) : ℝ) + ((k % 256 : ℕ) : ℝ) := by
    conv_lhs => rw [hkdecomp]
    push_cast
    ring
  have hcs := csOf_mem (k % 256) hm255
  have hqq := ExpAux.qcos_qsin_mem (k / 256) hq4
  have hθ : (k : ℝ) * Real.pi / 1024
      = ((k / 256 : ℕ) : ℝ) * Real.pi / 4 + ((k % 256 : ℕ) : ℝ) * Real.pi / 1024 := by
    rw [hkR]
    ring
  have hI : Complex.I * ((k : ℂ) * Real.pi / 1024)
      = (((k : ℝ) * Real.pi / 1024 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hbody : expI k
      = ⟨Iv.sub (IvM (qcos (k / 256)) (csOf (k % 256)).re)
              (IvM (qsin (k / 256)) (csOf (k % 256)).im),
         Iv.add (IvM (qsin (k / 256)) (csOf (k % 256)).re)
              (IvM (qcos (k / 256)) (csOf (k % 256)).im)⟩ := rfl
  rw [hI, Complex.exp_ofReal_mul_I, hbody]
  simp only [Cpx.Mem, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, add_zero, sub_zero]
  constructor
  · rw [hθ, Real.cos_add]
    exact Iv.mem_sub (IvMSpec hqq.1 hcs.1) (IvMSpec hqq.2 hcs.2)
  · rw [hθ, Real.sin_add]
    exact Iv.mem_add (IvMSpec hqq.2 hcs.1) (IvMSpec hqq.1 hcs.2)

end Work.CNum
