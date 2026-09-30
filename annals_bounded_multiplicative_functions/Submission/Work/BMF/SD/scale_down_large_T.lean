import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.cell_position
import Submission.Work.BMF.SD.grid_selection
import Submission.Work.BMF.primesIn_card_le_pi0
import Submission.Work.BMF.SD.narrow_high_pairs
import Submission.Work.BMF.SD.sdlT_ballbound
import Submission.Work.BMF.SD.sdlT_isfam_image

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD 09-30: new scale_down decomposition (read _NOTE_BMF_SD_0930_VERDICT.md at the workspace root; your node's route and constants are in its docstring). Narrow the prime window AFTER counting (pigeonhole into sub-windows of ratio 1+ρ), then split on T = X/H at a threshold T₁ depending only on c₀. No new analytic number theory is needed.
Assembly. This is largely written already in L87's Submission/Work/BMF/SD/_asm.lean (scale_down_core, §9 route): START from it, swap its good_window_pairs input for SD.narrow_high_pairs, and add the hypothesis T₁ ≤ X/H and the T₁ output. When the sibling lands, add import Submission.Work.BMF.SD.narrow_high_pairs.
-/

set_option maxHeartbeats 4000000

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex

/-- **Counting budget of the grid selection.**  With `T = X/H ≥ 676·(Cp+1)/κ`, a constant `c`
small against `κ/(676 (Cp+1))` and `κ/(32 K₃)` and `Cp/(2K₃)`, `m ≥ cT` (an integer),
`J ≥ 10T/3 - 2` and `δ/g ≤ 168`, the pigeonhole inequality of `grid_selection` holds against the
lower bound `κ T π` on the number of available pairs. -/
private lemma sdlT_budget {κ Cp K₃ c T pp : ℝ} {m J dh : ℕ}
    (hκ : 0 < κ) (hCp : 0 < Cp) (hK : 0 < K₃) (hc : 0 < c) (hpp : 1 ≤ pp) (hT : 1 ≤ T)
    (hc1 : c ≤ κ / (1352 * (Cp + 1))) (hc2 : c ≤ κ / (32 * K₃)) (hc3 : c ≤ Cp / (2 * K₃))
    (hTb : 1352 * (Cp + 1) / κ ≤ T)
    (hm1 : c * T ≤ (m : ℝ)) (hm2 : (m : ℝ) ≤ c * T + 1)
    (hJ : (J : ℝ) + 1 ≤ 10 * T / 3 + 3) (hdh : (dh : ℝ) ≤ 168) :
    (m : ℝ) * (2 * ((dh : ℝ) + 1)) * ((Cp * pp + 1) - 2 * K₃ * c * pp)
      + ((J : ℝ) + 1) * (2 * K₃ * c * pp) ≤ κ * T * pp := by
  have hc1'' : 338 * (Cp + 1) * c ≤ κ / 4 := by
    have hpos : 0 < 1352 * (Cp + 1) := by positivity
    have h := (le_div_iff₀ hpos).mp hc1
    linarith
  have hc2'' : 32 * K₃ * c ≤ κ := by
    have hpos : 0 < 32 * K₃ := by positivity
    have h := (le_div_iff₀ hpos).mp hc2
    linarith
  have hc3'' : 2 * K₃ * c ≤ Cp := by
    have hpos : 0 < 2 * K₃ := by positivity
    have h := (le_div_iff₀ hpos).mp hc3
    linarith
  have hTb'' : 1352 * (Cp + 1) ≤ κ * T := by
    have h := (div_le_iff₀ hκ).mp hTb
    linarith
  have hTpp : (0 : ℝ) ≤ T * pp := by
    have h1 : (0 : ℝ) < T := by linarith
    exact mul_nonneg h1.le (by linarith)
  have hMt : Cp * pp + 1 - 2 * K₃ * c * pp ≤ (Cp + 1) * pp := by
    have h : (0 : ℝ) ≤ 2 * K₃ * c * pp := by positivity
    linarith
  have hMt0 : 0 ≤ Cp * pp + 1 - 2 * K₃ * c * pp := by
    have h : 2 * K₃ * c * pp ≤ Cp * pp :=
      mul_le_mul_of_nonneg_right hc3'' (by linarith : (0 : ℝ) ≤ pp)
    linarith
  have h1 : 2 * ((dh : ℝ) + 1) ≤ 338 := by linarith
  have h2 : (0 : ℝ) ≤ 2 * ((dh : ℝ) + 1) := by positivity
  have hstep1 : (m : ℝ) * (2 * ((dh : ℝ) + 1)) * (Cp * pp + 1 - 2 * K₃ * c * pp)
      ≤ (c * T + 1) * 338 * ((Cp + 1) * pp) := by
    have h3 : (0 : ℝ) ≤ (Cp + 1) * pp := by
      have : (0 : ℝ) < Cp + 1 := by linarith
      exact mul_nonneg this.le (by linarith)
    calc (m : ℝ) * (2 * ((dh : ℝ) + 1)) * (Cp * pp + 1 - 2 * K₃ * c * pp)
        ≤ (m : ℝ) * (2 * ((dh : ℝ) + 1)) * ((Cp + 1) * pp) :=
          mul_le_mul_of_nonneg_left hMt (by positivity)
      _ ≤ (c * T + 1) * 338 * ((Cp + 1) * pp) := by
          have h4 : (0 : ℝ) ≤ c * T + 1 := by
            have : (0 : ℝ) ≤ c * T := by positivity
            linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul hm2 h1 h2 h4) h3
  have hid1 : (c * T + 1) * 338 * ((Cp + 1) * pp)
      = 338 * (Cp + 1) * (c * T) * pp + 338 * (Cp + 1) * pp := by ring
  have hb1a : 338 * (Cp + 1) * (c * T) * pp ≤ κ / 4 * (T * pp) := by
    have h3 : 338 * (Cp + 1) * (c * T) * pp = (338 * (Cp + 1) * c) * (T * pp) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right hc1'' hTpp
  have hb1b : 338 * (Cp + 1) * pp ≤ κ / 4 * (T * pp) := by
    have h4 : κ / 4 * (T * pp) = (κ * T / 4) * pp := by ring
    rw [h4]
    apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ pp)
    linarith [hTb'']
  have hstep2 : ((J : ℝ) + 1) * (2 * K₃ * c * pp) ≤ (10 * T / 3 + 3) * (2 * K₃ * c * pp) :=
    mul_le_mul_of_nonneg_right hJ (by positivity)
  have hid2 : (10 * T / 3 + 3) * (2 * K₃ * c * pp)
      = (10 * T / 3) * (2 * K₃ * c * pp) + 3 * (2 * K₃ * c * pp) := by ring
  have hb2a : (10 * T / 3) * (2 * K₃ * c * pp) ≤ κ / 4 * (T * pp) := by
    have h5 : (10 * T / 3) * (2 * K₃ * c * pp) = ((20 / 3) * K₃ * c) * (T * pp) := by ring
    rw [h5]
    apply mul_le_mul_of_nonneg_right _ hTpp
    linarith [hc2'']
  have hb2b : 3 * (2 * K₃ * c * pp) ≤ κ / 4 * (T * pp) := by
    have h6 : 3 * (2 * K₃ * c * pp) = (6 * K₃ * c) * pp := by ring
    have h7 : κ / 4 * (T * pp) = (κ / 4 * T) * pp := by ring
    rw [h6, h7]
    apply mul_le_mul_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ pp)
    linarith [hc2'', hT]
  linarith [hstep1, hid1, hb1a, hb1b, hstep2, hid2, hb2a, hb2b]

/-- Scaling down in the large-aspect regime `X/H ≥ T₁` (`T₁` is an OUTPUT, depending on `k, c₀`
only): the grid-of-cells assembly of `SD/SD4_STATUS.md` §9 (I4) and `SD/_asm.lean`, fed by the
sibling `Work.BMF.SD.narrow_high_pairs` (add its import) instead of `admissible_good_pairs`.

Route.  `narrow_high_pairs k c₀` gives `κ, A₁` and a window `[a,b]` (`5b ≤ 7a`) with a set
`S := (goodPairs f F.pol (c₀/2) H a b F.fam).filter (X/(10a) ≤ pos)` of `≥ κ T π₀(a)` pairs; every
position satisfies `X/(10a) ≤ y/p` and `y/p + H/a ≤ (y+H)/a ≤ 10X/a`.  `cell_position k hk (c₀/2)`
gives `C₃ c₃ K₃`; `primesIn_card_le_pi0` gives `Cp, Pp`.
`grid_selection S s g M t δ J m` with `s := X/(10a)`, `g := 3H/a` (balls of radius `3H/(2a)`),
`J := ⌈10T/3⌉₊ + 1`, `M := Cp π₀(a) + 1` (`hbound`: `ballPairs_mono` + `ball_card_le` +
`primesIn a b ⊆ primesIn a (2a)` + `primesIn_card_le_pi0`), `t := 2 K₃ c π₀(a)`,
`δ := 503H/a` (`2(⌈δ/g⌉₊+1) = 338`), `m := ⌈c T⌉₊`.  `hT` holds when
`c ≤ κ/(2704 Cp)`, `c ≤ κ/(48 K₃)`, `c ≤ Cp/(2K₃)` and `T ≥ T₁ := max 1 (max (4/c₀) (2704 Cp/κ))`
(then `(cT+1)·676 Cp π₀ + (10T/3+3)·t ≤ 0.77 κ T π₀`, using `Cp π₀(a) ≥ 1` for `a ≥ P₀`).
Per grid point `u`: `cell_position` on `ballPairs S u (3H/(2a))` (`≥ t > 0` pairs) gives
`x'_u` (a pair position, so admissible), `pol'_u`, `S'_u` with `#S'_u ≥ t/(2K₃) = c π₀(a)`;
`|x'_u - x'_v| ≥ 503H/a - 3H/a = 500H/a`; `F'` := image of the grid points, `c ≤ min c₀ c₃`,
`C := C₃`, `A := max A₁ 2`, `P₀ := max (max Pp 4) (the threshold making Cp π₀(a) ≥ 1)`. -/
theorem scale_down_large_T (k : ℕ) (hk : 1 ≤ k) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c C A P₀ T₁ : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < P₀ ∧ 1 ≤ T₁ ∧ c ≤ c₀ ∧
      ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
        (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
        (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X → P₀ ≤ P →
        A ≤ Real.log Q / Real.log P → T₁ ≤ X / H →
        ∀ (F : Work.BMF.PhaseFamily k f c₀ X H),
        ∃ (a b : ℝ) (F' : Work.BMF.PhaseFamily k f c (X / a) (H / a)),
          P ≤ a ∧ a ≤ b ∧ b ≤ Q ∧ 5 * b ≤ 7 * a ∧
            ∀ x' ∈ F'.fam, c * Work.BMF.pi0 a ≤
              ((Work.BMF.incPairs k C F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x')
                x').card : ℝ) := by
  obtain ⟨κ, A₁, hκpos, hA₁pos, hnhp⟩ := narrow_high_pairs k c₀ hc₀
  obtain ⟨Cp, Pp, hCppos, hpi⟩ := primesIn_card_le_pi0
  obtain ⟨C₃, c₃, K₃, hC₃pos, hc₃pos, hK₃pos, hcell⟩ :=
    cell_position k hk (c₀ / 2) (by linarith)
  set T₁ : ℝ := max 1 (max (4 / c₀) (1352 * (Cp + 1) / κ)) with hT₁def
  have hT₁1 : 1 ≤ T₁ := le_max_left _ _
  have hT₁c₀ : 4 / c₀ ≤ T₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT₁κ : 1352 * (Cp + 1) / κ ≤ T₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  set c : ℝ := min (min c₀ c₃)
    (min (min (κ / (1352 * (Cp + 1))) (κ / (32 * K₃))) (Cp / (2 * K₃))) with hcdef
  set A : ℝ := max A₁ 2 with hAdef
  set P₀ : ℝ := max (max Pp 4) A with hP₀def
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min hc₀ hc₃pos)
      (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  have hcc₀ : c ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₃ : c ≤ c₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1 : c ≤ κ / (1352 * (Cp + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hc2 : c ≤ κ / (32 * K₃) :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hc3 : c ≤ Cp / (2 * K₃) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hP₀pos : 0 < P₀ := by
    rw [hP₀def]
    exact lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) (le_max_left _ _))
  refine ⟨c, C₃, A, P₀, T₁, hcpos, hC₃pos, hApos, hP₀pos, hT₁1, hcc₀, ?_⟩
  intro f hf hmul X H P Q h2P hPQ hQ3 hHX hP₀P hAQ hTle F
  have hA₁ : A₁ ≤ Real.log Q / Real.log P := le_trans (le_max_left _ _) hAQ
  -- basic numerical facts
  have hPpos : (0 : ℝ) < P := by linarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQ2 : (2 : ℝ) ≤ Q := le_trans h2P hPQ
  have hP4 : (4 : ℝ) ≤ P := by
    rw [hP₀def] at hP₀P
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP₀P
  have hPpP : Pp ≤ P := by
    rw [hP₀def] at hP₀P
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP₀P
  have h8 : (8 : ℝ) ≤ Q ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hQ2 3
    norm_num at h
    exact h
  have hHpos : (0 : ℝ) < H := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le hHpos hHX
  have hQleH : Q ≤ H := by
    have h1 : Q ≤ Q ^ 3 := by
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ Q by linarith) (show 1 ≤ 3 by norm_num)
      simpa using h
    linarith
  have hQ4 : (4 : ℝ) ≤ Q := le_trans hP4 hPQ
  have h14Q : 14 * Q ≤ X := by
    have h16 : (16 : ℝ) ≤ Q ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hQ4 2
      norm_num at h
      linarith
    nlinarith [h16, hQ4, hQ3, hHX]
  -- the sibling's window
  obtain ⟨a, b, hPa, hab, h57, hbQ, hScard0⟩ :=
    hnhp f hf hmul X H P Q h2P hPQ hQ3 hHX hA₁ (le_trans hT₁c₀ hTle) F
  set S : Finset (ℝ × ℕ) :=
    (goodPairs f F.pol (c₀ / 2) H a b F.fam).filter
      (fun q => X / (10 * a) ≤ q.1 / (q.2 : ℝ)) with hSdef
  have hScard : κ * (X / H) * pi0 a ≤ (S.card : ℝ) := by rw [hSdef]; exact hScard0
  -- facts about `a`, `b`
  have hapos : 0 < a := lt_of_lt_of_le hPpos hPa
  have ha4 : (4 : ℝ) ≤ a := le_trans hP4 hPa
  have ha1 : (1 : ℝ) < a := by linarith
  have haQ : a ≤ Q := le_trans hab hbQ
  have haPp : Pp ≤ a := le_trans hPpP hPa
  have hbpos : 0 < b := lt_of_lt_of_le hapos hab
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb_le : b ≤ 7 * a / 5 := by linarith
  have h14aX : 14 * a ≤ X := by nlinarith [haQ, h14Q]
  have hHa : (1 : ℝ) ≤ H / a := by rw [le_div_iff₀ hapos]; nlinarith [hQleH, haQ]
  have hlogapos : 0 < Real.log a := Real.log_pos ha1
  have hpi0pos : 0 < pi0 a := by rw [pi0]; exact div_pos hapos hlogapos
  have hpi0ge1 : (1 : ℝ) ≤ pi0 a := by
    rw [pi0, le_div_iff₀ hlogapos]
    linarith [Real.log_le_sub_one_of_pos hapos]
  have hXHpos : 0 < X / H := div_pos hXpos hHpos
  have hXHge1 : (1 : ℝ) ≤ X / H := by rw [le_div_iff₀ hHpos]; linarith
  -- membership facts for `S`
  have hSgood : ∀ q ∈ S, q ∈ goodPairs f F.pol (c₀ / 2) H a b F.fam := by
    intro q hq
    rw [hSdef, Finset.mem_filter] at hq
    exact hq.1
  have hSmem : ∀ q ∈ S, q.1 ∈ F.fam ∧ q.2 ∈ primesIn a b ∧
      X / (10 * a) ≤ q.1 / (q.2 : ℝ) := by
    intro q hq
    have h1 := mem_goodPairs.mp (hSgood q hq)
    rw [hSdef, Finset.mem_filter] at hq
    exact ⟨h1.1, h1.2.1, hq.2⟩
  have hSsub : S ⊆ F.fam ×ˢ primesIn a b := by
    intro q hq
    exact Finset.mem_product.mpr ⟨(hSmem q hq).1, (hSmem q hq).2.1⟩
  have hSp : ∀ q ∈ S, a ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ b := by
    intro q hq
    have hq' := (hSmem q hq).2.1
    rw [primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hq'
    exact ⟨le_trans (Nat.le_ceil a) (by exact_mod_cast hq'.1.1),
      le_trans (by exact_mod_cast hq'.1.2) (Nat.floor_le hbpos.le)⟩
  have hSp1 : ∀ q ∈ S, (1 : ℝ) ≤ q.1 / (q.2 : ℝ) := by
    intro q hq
    have h1 := (hSmem q hq).2.2
    have h2 : (1 : ℝ) ≤ X / (10 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  -- grid parameters
  set g : ℝ := 3 * H / a with hgdef
  set δ : ℝ := 503 * H / a with hδdef
  set Jn : ℕ := ⌈10 * (X / H) / 3⌉₊ + 1 with hJndef
  set t : ℝ := 2 * K₃ * c * pi0 a with htdef
  set M : ℝ := Cp * pi0 a + 1 with hMdef
  set mm : ℕ := ⌈c * (X / H)⌉₊ with hmmdef
  have hgpos : 0 < g := by rw [hgdef]; positivity
  have hJpos : 0 < Jn := by rw [hJndef]; omega
  have htpos : 0 < t := by rw [htdef]; positivity
  have hg2 : g / 2 = 3 * H / (2 * a) := by rw [hgdef]; ring
  have h2Kc : 2 * K₃ * c ≤ Cp := by
    have h := hc3
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K₃)] at h
    linarith
  -- the positions lie in `[X/(10a), X/(10a) + J·g]`
  have hpos : ∀ q ∈ S, X / (10 * a) ≤ q.1 / (q.2 : ℝ) ∧
      q.1 / (q.2 : ℝ) ≤ X / (10 * a) + (Jn : ℝ) * g := by
    intro q hq
    refine ⟨(hSmem q hq).2.2, ?_⟩
    obtain ⟨hqf, hqpr, hqfilt⟩ := hSmem q hq
    obtain ⟨hqa, hqb⟩ := hSp q hq
    have hq2pos : 0 < (q.2 : ℝ) := lt_of_lt_of_le hapos hqa
    have hq1nn : 0 ≤ q.1 := by
      have h1 : (0 : ℝ) ≤ q.1 / (q.2 : ℝ) :=
        le_trans (by positivity : (0 : ℝ) ≤ X / (10 * a)) hqfilt
      have h2 : 0 ≤ q.1 / (q.2 : ℝ) * (q.2 : ℝ) := mul_nonneg h1 hq2pos.le
      rwa [div_mul_cancel₀ q.1 (ne_of_gt hq2pos)] at h2
    have hq1u : q.1 + H ≤ 10 * X := (F.isFam.1 q.1 hqf).2
    have hstep1 : q.1 / (q.2 : ℝ) ≤ q.1 / a := div_le_div_of_nonneg_left hq1nn hapos hqa
    have hstep2 : q.1 / a ≤ (10 * X - H) / a :=
      div_le_div_of_nonneg_right (by linarith) hapos.le
    have hstep3 : (10 * X - H) / a ≤ 10 * X / a := by
      apply div_le_div_of_nonneg_right _ hapos.le
      linarith
    have hJg : 10 * X / a ≤ (Jn : ℝ) * g := by
      have h1 : 10 * (X / H) / 3 ≤ ((⌈10 * (X / H) / 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : (Jn : ℝ) = ((⌈10 * (X / H) / 3⌉₊ : ℕ) : ℝ) + 1 := by
        rw [hJndef]; push_cast; ring
      rw [h2, hgdef]
      have h3 : (10 * (X / H) / 3) * (3 * H / a) = 10 * X / a := by
        have h3a : (3 : ℝ) * H / a ≠ 0 := ne_of_gt (by positivity)
        field_simp
      have h4 : (10 * (X / H) / 3) * (3 * H / a)
          ≤ ((⌈10 * (X / H) / 3⌉₊ : ℕ) : ℝ) * (3 * H / a) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith [h4, h3]
    have h0 : (0 : ℝ) ≤ X / (10 * a) := by positivity
    linarith
  -- the ball bound
  have hbound : ∀ x : ℝ, ((ballPairs S x (g / 2)).card : ℝ) ≤ M := by
    intro x
    have h := sdlT_ballbound (Cp := Cp) (Pp := Pp) (x := x) hpi hSsub hHpos hapos hbpos hb_le
      (fun y hy y' hy' hne => F.isFam.2 y hy y' hy' hne) haPp
    rw [hMdef, hg2]
    exact h
  have htM : t + 1 ≤ M := by
    rw [htdef, hMdef]
    nlinarith [h2Kc, hpi0pos]
  -- the grid index
  have hmm1 : c * (X / H) ≤ (mm : ℝ) := by rw [hmmdef]; exact Nat.le_ceil _
  -- the counting budget
  have hT : (mm : ℝ) * (2 * (⌈δ / g⌉₊ + 1)) * (M - t) + ((Jn : ℕ) + 1 : ℝ) * t
      ≤ (S.card : ℝ) := by
    have hδg : ⌈δ / g⌉₊ ≤ 168 := by
      rw [Nat.ceil_le, hδdef, hgdef]
      have h1 : (503 * H / a) / (3 * H / a) = 503 / 3 := by
        have h3 : (3 : ℝ) * H / a ≠ 0 := ne_of_gt (by positivity)
        field_simp
      rw [h1]
      norm_num
    have hd1 : 2 * ((⌈δ / g⌉₊ : ℝ) + 1) ≤ 338 := by
      have h2 : (⌈δ / g⌉₊ : ℝ) ≤ 168 := by exact_mod_cast hδg
      linarith
    have hJ1 : ((Jn : ℕ) : ℝ) + 1 ≤ 10 * (X / H) / 3 + 3 := by
      have h2 : ((⌈10 * (X / H) / 3⌉₊ : ℕ) : ℝ) ≤ 10 * (X / H) / 3 + 1 := by
        have h3 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 10 * (X / H) / 3 by positivity)
        linarith
      rw [hJndef]
      push_cast
      linarith
    have hmm2 : (mm : ℝ) ≤ c * (X / H) + 1 := by
      rw [hmmdef]
      have h3 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ c * (X / H) by positivity)
      linarith
    have hbud := sdlT_budget (κ := κ) (Cp := Cp) (K₃ := K₃) (c := c) (T := X / H)
      (pp := pi0 a) (m := mm) (J := Jn) (dh := ⌈δ / g⌉₊) hκpos hCppos hK₃pos hcpos
      hpi0ge1 hXHge1 hc1 hc2 hc3 (le_trans hT₁κ hTle) hmm1 hmm2 hJ1
      (by exact_mod_cast hδg)
    rw [hMdef, htdef]
    linarith [hbud, hScard]
  -- the grid selection
  obtain ⟨Xg, hgrid, hsepX, hcardX, hballX⟩ :=
    grid_selection S (X / (10 * a)) g M t δ Jn mm hgpos hJpos htM hpos hbound hT
  have hXg1 : ∀ u ∈ Xg, (1 : ℝ) ≤ u := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := hgrid u hu
    have h0 : (1 : ℝ) ≤ X / (10 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h1 : (0 : ℝ) ≤ (j : ℝ) * g := by positivity
    linarith
  -- the per-cell data
  have hCell : ∀ u ∈ Xg, ∃ (x' : ℝ) (pol' : ℝ[X]) (S' : Finset (ℝ × ℕ)),
      S' ⊆ ballPairs S u (3 * H / (2 * a)) ∧
      (∃ q ∈ ballPairs S u (3 * H / (2 * a)), x' = q.1 / (q.2 : ℝ)) ∧
      c₃ * (H / a) ≤ ‖corr f pol' x' (H / a)‖ ∧
      pol' ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      ((ballPairs S u (3 * H / (2 * a))).card : ℝ) / (2 * K₃) ≤ (S'.card : ℝ) ∧
      (∀ q ∈ S', |q.1 / (q.2 : ℝ) - x'| ≤ 3 * H / a ∧
        PolyRel k C₃ 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))
          (dil (q.2 : ℝ) (F.pol q.1)) x' (H / a) pol') := by
    intro u hu
    have hne : (ballPairs S u (3 * H / (2 * a))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have h1 : t ≤ ((ballPairs S u (3 * H / (2 * a))).card : ℝ) := by
        have h2 := hballX u hu
        rwa [hg2] at h2
      rw [hemp] at h1
      simp only [Finset.card_empty, Nat.cast_zero] at h1
      linarith [htpos]
    exact hcell f hf F.pol H a b u (ballPairs S u (3 * H / (2 * a)))
      hapos hab h57 hHa (hXg1 u hu) hb1 hne
      (fun q hq => hSp1 q (mem_ballPairs.mp hq).1)
      (fun q hq => hSp q (mem_ballPairs.mp hq).1)
      (fun q hq => (mem_ballPairs.mp hq).2)
      (fun q hq => (mem_goodPairs.mp (hSgood q (mem_ballPairs.mp hq).1)).2.2)
      (fun q hq => dil_mem_degreeLE (F.deg q.1 (hSmem q (mem_ballPairs.mp hq).1).1))
  let xf : ℝ → ℝ := fun u => if hu : u ∈ Xg then Classical.choose (hCell u hu) else u
  let pf : ℝ → ℝ[X] := fun u =>
    if hu : u ∈ Xg then Classical.choose (Classical.choose_spec (hCell u hu)) else 0
  let Sf : ℝ → Finset (ℝ × ℕ) := fun u =>
    if hu : u ∈ Xg then
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hCell u hu))) else ∅
  have hspec : ∀ u ∈ Xg, Sf u ⊆ ballPairs S u (3 * H / (2 * a)) ∧
      (∃ q ∈ ballPairs S u (3 * H / (2 * a)), xf u = q.1 / (q.2 : ℝ)) ∧
      c₃ * (H / a) ≤ ‖corr f (pf u) (xf u) (H / a)‖ ∧
      pf u ∈ degreeLE ℝ (k : WithBot ℕ) ∧
      ((ballPairs S u (3 * H / (2 * a))).card : ℝ) / (2 * K₃) ≤ ((Sf u).card : ℝ) ∧
      (∀ q ∈ Sf u, |q.1 / (q.2 : ℝ) - xf u| ≤ 3 * H / a ∧
        PolyRel k C₃ 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))
          (dil (q.2 : ℝ) (F.pol q.1)) (xf u) (H / a) (pf u)) := by
    intro u hu
    have h1 : xf u = Classical.choose (hCell u hu) := by
      simp only [xf]; rw [dif_pos hu]
    have h2 : pf u = Classical.choose (Classical.choose_spec (hCell u hu)) := by
      simp only [pf]; rw [dif_pos hu]
    have h3 : Sf u
        = Classical.choose (Classical.choose_spec (Classical.choose_spec (hCell u hu))) := by
      simp only [Sf]; rw [dif_pos hu]
    have h4 := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hCell u hu)))
    simp only [h1, h2, h3]
    exact h4
  let pol' : ℝ → ℝ[X] := fun x' =>
    if h : ∃ u ∈ Xg, xf u = x' then pf (Classical.choose h) else 0
  have hpol'_val : ∀ (x' : ℝ) (h : ∃ u ∈ Xg, xf u = x'), pol' x' = pf (Classical.choose h) := by
    intro x' h
    simp only [pol']
    rw [dif_pos h]
  refine ⟨a, b, ⟨Xg.image xf, pol', ?_, ?_, ?_, ?_⟩, hPa, hab, hbQ, h57, ?_⟩
  · -- `IsFam`
    refine sdlT_isfam_image (fam := F.fam) (S := S) (Xg := Xg) (xf := xf)
      hXpos hHpos hapos ?_ ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨q, hq, hqx⟩ := (hspec u hu).2.1
      exact ⟨q, (mem_ballPairs.mp hq).1, hqx⟩
    · intro q hq
      exact ⟨(hSmem q hq).1, (hSp q hq).1, (hSmem q hq).2.2⟩
    · intro y hy
      exact (F.isFam.1 y hy).2
    · intro u hu v hv hne
      have h1 := hsepX u hu v hv hne
      rwa [hδdef] at h1
    · intro u hu
      obtain ⟨q, hq, hqx⟩ := (hspec u hu).2.1
      rw [hqx]
      exact (mem_ballPairs.mp hq).2
  · -- `card_ge`
    have hinj : Set.InjOn xf ↑Xg := by
      intro u hu v hv huv
      by_contra hne
      have h1 := hsepX u hu v hv hne
      have h2 : |xf u - u| ≤ 3 * H / (2 * a) := by
        obtain ⟨q, hq, hqx⟩ := (hspec u hu).2.1
        rw [hqx]
        exact (mem_ballPairs.mp hq).2
      have h3 : |xf v - v| ≤ 3 * H / (2 * a) := by
        obtain ⟨q, hq, hqx⟩ := (hspec v hv).2.1
        rw [hqx]
        exact (mem_ballPairs.mp hq).2
      have h5 : |u - v| ≤ |u - xf u| + |xf u - v| := abs_sub_le u (xf u) v
      have h6 : |xf u - v| ≤ |xf u - xf v| + |xf v - v| := abs_sub_le (xf u) (xf v) v
      have h7 : |u - xf u| = |xf u - u| := abs_sub_comm u (xf u)
      have h8 : 503 * H / a ≤ |u - v| := by
        have := h1
        rwa [hδdef] at this
      rw [h7] at h5
      have h10 : 500 * H / a ≤ |xf u - xf v| := by
        have h9 : 503 * H / a - 3 * H / (2 * a) - 3 * H / (2 * a) = 500 * H / a := by ring
        linarith
      rw [huv, sub_self, abs_zero] at h10
      have h11 : (0 : ℝ) < 500 * H / a := by positivity
      linarith
    rw [Finset.card_image_of_injOn hinj]
    have h9 : (X / a) / (H / a) = X / H := by field_simp
    rw [h9]
    exact le_trans hmm1 (by exact_mod_cast hcardX)
  · -- `deg`
    intro x' hx'
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx'
    have hwit : ∃ u ∈ Xg, xf u = x' := ⟨u, hu, hux⟩
    rw [hpol'_val x' hwit]
    exact (hspec (Classical.choose hwit) (Classical.choose_spec hwit).1).2.2.2.1
  · -- `corr_ge`
    intro x' hx'
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx'
    have hwit : ∃ u ∈ Xg, xf u = x' := ⟨u, hu, hux⟩
    rw [hpol'_val x' hwit]
    have h2 : xf (Classical.choose hwit) = x' := (Classical.choose_spec hwit).2
    obtain ⟨-, -, hcorr, -, -, -⟩ :=
      hspec (Classical.choose hwit) (Classical.choose_spec hwit).1
    rw [h2] at hcorr
    exact le_trans (mul_le_mul_of_nonneg_right hcc₃ (by positivity : (0 : ℝ) ≤ H / a)) hcorr
  · -- the incidences
    intro x' hx'
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx'
    have hwit : ∃ u ∈ Xg, xf u = x' := ⟨u, hu, hux⟩
    change c * pi0 a ≤
      ((incPairs k C₃ F.fam a b H (3 * H / a) (H / a) F.pol (pol' x') x').card : ℝ)
    rw [hpol'_val x' hwit]
    obtain ⟨hsub, hrepb, hcorr, hdeg, hcardS, hinc⟩ :=
      hspec (Classical.choose hwit) (Classical.choose_spec hwit).1
    have hx'eq : xf (Classical.choose hwit) = x' := (Classical.choose_spec hwit).2
    have hsub2 : Sf (Classical.choose hwit) ⊆
        incPairs k C₃ F.fam a b H (3 * H / a) (H / a) F.pol (pf (Classical.choose hwit)) x' := by
      intro q hq
      obtain ⟨h1, h2⟩ := hinc q hq
      rw [hx'eq] at h1 h2
      have hqS : q ∈ S := (mem_ballPairs.mp (hsub hq)).1
      rw [incPairs, Finset.mem_filter]
      refine ⟨?_, h1, h2⟩
      rw [Finset.mem_product]
      exact ⟨(hSmem q hqS).1, (hSmem q hqS).2.1⟩
    have hlow : c * pi0 a ≤ ((Sf (Classical.choose hwit)).card : ℝ) := by
      have hb := hballX (Classical.choose hwit) (Classical.choose_spec hwit).1
      rw [hg2] at hb
      have hc2 : c * pi0 a = t / (2 * K₃) := by
        rw [htdef]
        field_simp
      rw [hc2]
      exact le_trans (div_le_div_of_nonneg_right hb (by positivity)) hcardS
    exact le_trans hlow (by exact_mod_cast Finset.card_le_card hsub2)

end Work.BMF.SD
