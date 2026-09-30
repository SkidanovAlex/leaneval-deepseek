import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.corr_shift
import Submission.Work.BMF.SD.scale_down_large_T
import Submission.Work.BMF.SD.scale_down_small_T

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- NOTE (SESSION SD4): the import list is deliberately kept inside the CLASH-FREE world
-- (`Submission.Work.BMF.SD.eC_mul_nat` is declared both by `SD/weyl_inverse` -- reachable from
-- `Work.BMF.large_sieve_poly` and `SD/scale_helpers` -- and by `SD/tk_short`; a file importing
-- both fails to elaborate).  The scaling-down assembly must import, together with this module,
--   * `Submission.Work.BMF.SD.admissible_good_pairs` (counting half; lives in the `tk_short` world)
--   * `Submission.Work.BMF.SD.cell_position`      (cell half; clash-free port of `cell_incidence`)
-- so neither `SD/scale_helpers` nor `Work.BMF.large_sieve_poly` may appear here.
-- See `Submission/Work/BMF/SD/SD4_STATUS.md` sections 3 and 9.

set_option maxHeartbeats 4000000

namespace Work.BMF

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-! ## The scaling-down step, with the (corrected) analytic input isolated -/

/-- **A sub-family of a phase family is a phase family (same phases, weaker constant).**
Used by the assembly of `scale_down`: the sources `y ≥ X₀` of `F` form a phase family whose
elements all satisfy `y/p ≥ X₀/(7a/5)` for every prime `p ≤ 7a/5`, so choosing `X₀ ≥ 7X/50`
makes every one of their rescaled intervals admissible (`≥ X/(10a)`) for the new family. -/
lemma phaseFamily_filter_ge {k : ℕ} {f : ℕ → ℂ} {c₀ c X H X₀ : ℝ} (F : PhaseFamily k f c₀ X H)
    (hcc : c ≤ c₀) (hH : 0 ≤ H)
    (hcard : c * (X / H) ≤ ((F.fam.filter (fun y => X₀ ≤ y)).card : ℝ)) :
    ∃ F' : PhaseFamily k f c X H,
      F'.fam = F.fam.filter (fun y => X₀ ≤ y) ∧ ∀ y, F'.pol y = F.pol y := by
  refine ⟨⟨F.fam.filter (fun y => X₀ ≤ y), F.pol, ?_, hcard, ?_, ?_⟩, rfl, fun _ => rfl⟩
  · refine ⟨fun y hy => F.isFam.1 y (Finset.mem_filter.mp hy).1, fun y hy y' hy' hne =>
      F.isFam.2 y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hne⟩
  · intro y hy
    exact F.deg y (Finset.mem_filter.mp hy).1
  · intro y hy
    exact le_trans (mul_le_mul_of_nonneg_right hcc hH) (F.corr_ge y (Finset.mem_filter.mp hy).1)

/-- The analytic input for the scaling-down step: a *prime* `a ∈ [P,Q]`, a window
`b ∈ [a, 7a/5]`, and a subfamily `Y ⊆ F.fam` of `≥ c₁ X/H` source intervals which simultaneously
(i) have a large rescaled correlation at the length `H/a` itself, and (ii) are each hit by
`≥ c₁ π₀(a)` rescaled source intervals lying within `3H/a` of `y/a` whose rescaled phase is
`PolyRel k C 1`-related to `(1/a)_* φ_y`. -/
def GPIHyp (k : ℕ) (c₀ : ℝ) : Prop :=
  ∃ c₁ C A₀ : ℝ, 0 < c₁ ∧ 1 ≤ C ∧ 0 < A₀ ∧ c₁ ≤ c₀ ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n),
      ∀ (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X →
        A₀ ≤ Real.log Q / Real.log P →
      ∀ (F : PhaseFamily k f c₀ X H),
      ∃ (a : ℕ) (b : ℝ) (Y : Finset ℝ), P ≤ (a : ℝ) ∧ (a : ℝ) ≤ b ∧ b ≤ Q ∧
        5 * b ≤ 7 * (a : ℝ) ∧ Nat.Prime a ∧ Y ⊆ F.fam ∧ c₁ * (X / H) ≤ (Y.card : ℝ) ∧
        (∀ y ∈ Y, c₁ * (H / (a : ℝ)) ≤
          ‖corr f (dil (a : ℝ) (F.pol y)) (y / (a : ℝ)) (H / (a : ℝ))‖) ∧
        (∀ y ∈ Y, c₁ * pi0 (a : ℝ) ≤
          (((F.fam ×ˢ primesIn (a : ℝ) b).filter (fun q : ℝ × ℕ =>
            |q.1 / (q.2 : ℝ) - y / (a : ℝ)| ≤ 3 * H / (a : ℝ) ∧
            PolyRel k C 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))
              (dil (q.2 : ℝ) (F.pol q.1)) (y / (a : ℝ)) (H / (a : ℝ))
              (dil (a : ℝ) (F.pol y)))).card : ℝ))

/-- MRT Fourier Prop. 3.1 / MRTTZ Prop. 3.4 (scaling down), as a formal statement. -/
theorem scale_down_aux (k : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) (hgp : GPIHyp k c₀) :
    ∃ c C A P₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < P₀ ∧ c ≤ c₀ ∧
      ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
        (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
        (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X → P₀ ≤ P →
        A ≤ Real.log Q / Real.log P →
        ∀ (F : PhaseFamily k f c₀ X H),
        ∃ (a b : ℝ) (F' : PhaseFamily k f c (X / a) (H / a)),
          P ≤ a ∧ a ≤ b ∧ b ≤ Q ∧ 5 * b ≤ 7 * a ∧
            ∀ x' ∈ F'.fam, c * pi0 a ≤
              ((incPairs k C F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) := by
  obtain ⟨c₁, C, A₀, hc₁, hC, hA₀, hc₁c₀, hmain⟩ := hgp
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨c₁, C, max A₀ 2, 4, hc₁, hCpos,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right A₀ 2), by norm_num, hc₁c₀, ?_⟩
  intro f hf hmul X H P Q h2P hPQ hQH hHX hP0P hA F
  obtain ⟨a, b, Y, hPa, hab, hbQ, h57, hap, hYsub, hYcard, hYcorr, hYinc⟩ :=
    hmain f hf hmul X H P Q h2P hPQ hQH hHX (le_trans (le_max_left A₀ 2) hA) F
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap.pos
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  set Z : Finset ℝ := Y.image (fun y => y / (a : ℝ)) with hZdef
  have hZmem : ∀ x' ∈ Z, ∃ y ∈ Y, y / (a : ℝ) = x' := by
    intro x' hx'
    rw [hZdef] at hx'
    exact Finset.mem_image.mp hx'
  have hinj : ∀ y ∈ Y, ∀ y' ∈ Y, y / (a : ℝ) = y' / (a : ℝ) → y = y' := by
    intro y _ y' _ h
    have h2 := congrArg (fun z : ℝ => z * (a : ℝ)) h
    rwa [div_mul_cancel₀ _ ha_ne, div_mul_cancel₀ _ ha_ne] at h2
  have hExists : ∀ x' : ℝ, ∃ p : ℝ[X], (x' ∈ Z →
      ∃ y ∈ Y, y / (a : ℝ) = x' ∧ p = dil (a : ℝ) (F.pol y)) ∧ (x' ∉ Z → p = 0) := by
    intro x'
    by_cases h : x' ∈ Z
    · obtain ⟨y, hyY, hyx⟩ := hZmem x' h
      exact ⟨dil (a : ℝ) (F.pol y), fun _ => ⟨y, hyY, hyx, rfl⟩, fun h' => absurd h h'⟩
    · exact ⟨0, fun h' => absurd h' h, fun _ => rfl⟩
  let pol' : ℝ → ℝ[X] := fun x' => Classical.choose (hExists x')
  have hpolY : ∀ x' (hx' : x' ∈ Z), ∃ y ∈ Y, y / (a : ℝ) = x' ∧
      pol' x' = dil (a : ℝ) (F.pol y) := fun x' hx' =>
    (Classical.choose_spec (hExists x')).1 hx'
  refine ⟨(a : ℝ), b, ⟨Z, pol', ?hisFam, ?hcard, ?hdeg, ?hcorr⟩, hPa, hab, hbQ, h57, ?_inc⟩
  · -- `IsFam (X/a) (H/a) Z`
    constructor
    · intro x' hx'
      obtain ⟨y, hyY, rfl⟩ := hZmem x' hx'
      obtain ⟨h1, h2⟩ := F.isFam.1 y (hYsub hyY)
      constructor
      · have h4 : X / (a : ℝ) / 10 = X / 10 / (a : ℝ) := by ring
        rw [h4]
        exact div_le_div_of_nonneg_right h1 ha_pos.le
      · have h3 : 10 * (X / (a : ℝ)) = 10 * X / (a : ℝ) := by ring
        rw [h3, ← add_div]
        exact div_le_div_of_nonneg_right h2 ha_pos.le
    · intro x' hx' y' hy' hxy
      obtain ⟨u, huY, rfl⟩ := hZmem x' hx'
      obtain ⟨v, hvY, rfl⟩ := hZmem y' hy'
      have huv : u ≠ v := fun h => hxy (by rw [h])
      have hsep := F.isFam.2 u (hYsub huY) v (hYsub hvY) huv
      have h1 : u / (a : ℝ) - v / (a : ℝ) = (u - v) / (a : ℝ) := by rw [← sub_div]
      have h3 : |u / (a : ℝ) - v / (a : ℝ)| = |u - v| / (a : ℝ) := by
        rw [h1, abs_div, abs_of_pos ha_pos]
      have h2 : (500 : ℝ) * (H / (a : ℝ)) = 500 * H / (a : ℝ) := by ring
      rw [h3, h2]
      exact div_le_div_of_nonneg_right hsep ha_pos.le
  · -- `card_ge`
    have h1 : Z.card = Y.card := by
      rw [hZdef]
      exact Finset.card_image_of_injOn hinj
    have h2 : (X / (a : ℝ)) / (H / (a : ℝ)) = X / H := by field_simp
    rw [h2, h1]
    exact hYcard
  · -- `deg`
    intro x' hx'
    obtain ⟨y, hyY, hyx, hp⟩ := hpolY x' hx'
    rw [hp]
    exact dil_mem_degreeLE (F.deg y (hYsub hyY))
  · -- `corr_ge`
    intro x' hx'
    obtain ⟨y, hyY, hyx, hp⟩ := hpolY x' hx'
    rw [hp]
    exact hyx ▸ hYcorr y hyY
  · -- incidences
    intro x' hx'
    obtain ⟨y, hyY, hyx, hp⟩ := hpolY x' hx'
    change c₁ * pi0 (a : ℝ) ≤ ((incPairs k C F.fam (a : ℝ) b H
      (3 * H / (a : ℝ)) (H / (a : ℝ)) F.pol (pol' x') x').card : ℝ)
    rw [hp]
    unfold incPairs
    exact hyx ▸ hYinc y hyY

end Work.BMF

namespace Work.BMF

/-- `pi0` is nonnegative (needed for the monotonicity bookkeeping in the case split below). -/
lemma pi0_nonneg (a : ℝ) (ha : 1 ≤ a) : 0 ≤ pi0 a := by
  rw [pi0]
  exact div_nonneg (by linarith) (Real.log_nonneg ha)

/-- `incPairs` is monotone in the `PolyRel` constant `C`. -/
lemma incPairs_mono_C {k : ℕ} {C C' : ℝ} (hC : C ≤ C') {src : Finset ℝ} {a b H R L' : ℝ}
    {pol : ℝ → Polynomial ℝ} {pol' : Polynomial ℝ} {x' : ℝ} (hH : 0 ≤ H) (hL' : 0 ≤ L') :
    incPairs k C src a b H R L' pol pol' x' ⊆ incPairs k C' src a b H R L' pol pol' x' := by
  classical
  intro q hq
  rw [incPairs, Finset.mem_filter] at hq ⊢
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hpprime : Nat.Prime q.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hq1).2).2
  have hp1 : (1 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast hpprime.one_lt.le
  have hpR : 0 ≤ H / (q.2 : ℝ) := div_nonneg hH (by linarith)
  exact ⟨hq1, hq2, PolyRel_mono hq3 hC hpR hL'⟩

/-- MRT Fourier Prop. 3.1 / MRTTZ Prop. 3.4 (scaling down). -/
theorem scale_down (k : ℕ) (hk : 1 ≤ k) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c C A P₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < P₀ ∧ c ≤ c₀ ∧
      ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
        (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
        (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X → P₀ ≤ P →
        A ≤ Real.log Q / Real.log P →
        ∀ (F : PhaseFamily k f c₀ X H),
        ∃ (a b : ℝ) (F' : PhaseFamily k f c (X / a) (H / a)),
          P ≤ a ∧ a ≤ b ∧ b ≤ Q ∧ 5 * b ≤ 7 * a ∧
            ∀ x' ∈ F'.fam, c * pi0 a ≤
              ((incPairs k C F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) := by
  classical
  -- the two regimes of the scaling-down step, split at the threshold `T₁` produced by
  -- `scale_down_large_T` (see `_NOTE_BMF_SD_0930_VERDICT.md`)
  obtain ⟨c_L, C_L, A_L, P_L, T₁, hc_L, hC_L, hA_L, hP_L, hT₁, hc_Lc₀, hmain_L⟩ :=
    Work.BMF.SD.scale_down_large_T k hk c₀ hc₀
  obtain ⟨c_S, C_S, A_S, P_S, hc_S, hC_S, hA_S, hP_S, hc_Sc₀, hmain_S⟩ :=
    Work.BMF.SD.scale_down_small_T k hk c₀ hc₀ T₁ hT₁
  refine ⟨min c_L c_S, max C_L C_S, max A_L A_S, max P_L P_S,
    lt_min hc_L hc_S, lt_max_of_lt_left hC_L, lt_max_of_lt_left hA_L, lt_max_of_lt_left hP_L,
    le_trans (min_le_left _ _) hc_Lc₀, ?_⟩
  intro f hf hmul X H P Q h2P hPQ hQ3 hHX hP0P hA F
  -- basic positivity
  have hPpos : (0 : ℝ) < P := by linarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hHpos : 0 < H := by
    have h8 : (8 : ℝ) ≤ Q ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_trans h2P hPQ) 3
      norm_num at h
      exact h
    linarith
  have hXpos : 0 < X := lt_of_lt_of_le hHpos hHX
  have hXHpos : 0 < X / H := div_pos hXpos hHpos
  have hP0_L : P_L ≤ P := le_trans (le_max_left P_L P_S) hP0P
  have hP0_S : P_S ≤ P := le_trans (le_max_right P_L P_S) hP0P
  have hA_L : A_L ≤ Real.log Q / Real.log P := le_trans (le_max_left A_L A_S) hA
  have hA_S : A_S ≤ Real.log Q / Real.log P := le_trans (le_max_right A_L A_S) hA
  rcases le_total (X / H) T₁ with hcase | hcase
  · -- bounded aspect: one centre-anchored cell
    obtain ⟨a, b, F', hPa, hab, hbQ, h57, hinc⟩ :=
      hmain_S f hf hmul X H P Q h2P hPQ hQ3 hHX hP0_S hA_S hcase F
    have hapos : 0 < a := lt_of_lt_of_le hPpos hPa
    have hHa : 0 ≤ H / a := div_nonneg hHpos.le hapos.le
    have hXHa : 0 ≤ (X / a) / (H / a) := div_nonneg (div_nonneg hXpos.le hapos.le) hHa
    refine ⟨a, b, F'.weaken (min_le_right _ _) hXHa hHa, hPa, hab, hbQ, h57, ?_⟩
    intro x' hx'
    have h1 := hinc x' hx'
    have hsub : incPairs k C_S F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x' ⊆
        incPairs k (max C_L C_S) F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x' :=
      incPairs_mono_C (le_max_right _ _) hHpos.le (by positivity)
    have h3 : ((incPairs k C_S F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ)
        ≤ ((incPairs k (max C_L C_S) F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    calc min c_L c_S * pi0 a ≤ c_S * pi0 a := mul_le_mul_of_nonneg_right (min_le_right _ _) (pi0_nonneg a (by linarith))
      _ ≤ ((incPairs k C_S F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) := h1
      _ ≤ _ := h3
  · -- large aspect: the grid-of-cells assembly
    obtain ⟨a, b, F', hPa, hab, hbQ, h57, hinc⟩ :=
      hmain_L f hf hmul X H P Q h2P hPQ hQ3 hHX hP0_L hA_L hcase F
    have hapos : 0 < a := lt_of_lt_of_le hPpos hPa
    have hHa : 0 ≤ H / a := div_nonneg hHpos.le hapos.le
    have hXHa : 0 ≤ (X / a) / (H / a) := div_nonneg (div_nonneg hXpos.le hapos.le) hHa
    refine ⟨a, b, F'.weaken (min_le_left _ _) hXHa hHa, hPa, hab, hbQ, h57, ?_⟩
    intro x' hx'
    have h1 := hinc x' hx'
    have hsub : incPairs k C_L F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x' ⊆
        incPairs k (max C_L C_S) F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x' :=
      incPairs_mono_C (le_max_left _ _) hHpos.le (by positivity)
    have h3 : ((incPairs k C_L F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ)
        ≤ ((incPairs k (max C_L C_S) F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    calc min c_L c_S * pi0 a ≤ c_L * pi0 a := mul_le_mul_of_nonneg_right (min_le_left _ _) (pi0_nonneg a (by linarith))
      _ ≤ ((incPairs k C_L F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x') x').card : ℝ) := h1
      _ ≤ _ := h3

end Work.BMF
