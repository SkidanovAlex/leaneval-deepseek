import Mathlib
import Submission.Work.KMTAreas.A7G.tailVarBound
import Submission.Work.KMTAreas.A7Rescue.blockSqFunWalk
import Submission.Work.KMTAreas.A7G.variationalBookkeeping
import Submission.Port.Aesm

/-!
# The *head* (short-window) variational bound for the low-pass Ionescu--Wainger family

This file proves `Work.KMTAreas.A7Rescue.headVarBound`: the `V^r`-variational norm of the
*height increment* `Π_{≤l,≤-(m₀+m)} - Π_{≤l-1,≤-(m₀+m)}` of the low-pass Ionescu--Wainger
projections, along an **arbitrary monotone walk** `m = L k` of levels confined to a short window
`L k ≤ N`, is bounded in `ℓᵖ` by `C (⌈log₂ (N+1)⌉ + 1) ‖f‖_{ℓᵖ}`, with `C` free of the height `l`,
of the base level `m₀`, of the walk `L` and of `N`.

The mathematical content is *Rademacher--Menshov*, not analysis:

* `walkVarNormRmLevels` — the `V^r`-norm of a monotone walk whose levels lie in `[0, K]`,
  `K ≤ 2^n`, is bounded by the base value plus the Rademacher--Menshov dyadic block square functions
  of the underlying sequence at the `n + 1` dyadic levels (`varTwo_le_rmLevels`, i.e. the
  Lewko--Lewko / Mirek--Stein form of the RM inequality, plus the elementary "monotone walk =
  subsequence" bookkeeping of `A7G/variationalBookkeeping`);
* `rmLevelSumLpKmtProj` — the sum of those dyadic block square functions of the projection walk is
  bounded in `ℓᵖ` by `C (n+1)‖f‖_{ℓᵖ}` with an `l`-free, `m₀`-free constant: this is
  `A7Rescue.blockSqFunWalk`, i.e. Khintchine's inequality + the uniform-in-signs annulus bound
  `A7G.annuliUniformSigns`;
* the base term `‖Π_{≤l,≤-m₀} f‖_{ℓᵖ}` is the single-scale bound `A7.kmtProj_lp_bound_uniform`.

Nothing here is new analysis: the two deep inputs (`annuliUniformSigns`, the uniform multiplier
bound) are already in the tree, and the whole point of the *short window* is that the logarithmic
loss of RM is affordable (this is the "head" of the head/tail split, at the base level `m₀`; the
tail is `A7G.tailVarBound`).
-/

namespace Work.KMTAreas.A7Rescue

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The Rademacher--Menshov reduction of a monotone walk -/

/-- **The `V^r`-norm of a monotone walk with levels in `[0, K]`, `K ≤ 2^n`, is bounded by the base
value plus the RM dyadic block square functions of the underlying sequence.**

`variationalNorm r (a ∘ σ) ≤ ‖a 0‖ₑ + 4 ∑_{l ≤ n} rmLevel n l a`.

The two-point chain `(0, σ k)` bounds the supremum part by `‖a 0‖ₑ + V²(a)` (`enorm_sub_le_varRho`),
and the chain part is bounded by `V²(a)` because a monotone reindexing of a chain is a chain whose
values still lie in `[0, K] ⊆ [0, 2^n]` (`A7G.varPart_two_comp_le`, in the windowed form).  The
windowed `2`-variation is then dominated by the `n + 1` RM dyadic block square functions
(`varTwo_le_rmLevels`). -/
theorem walkVarNormRmLevels {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ)
    (σ : ℕ → ℕ) (hσ : Monotone σ) {K n : ℕ} (hK : ∀ k, σ k ≤ K) (hKn : K ≤ 2 ^ n) :
    PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => a (σ k)) ≤
      ‖a 0‖ₑ + ENNReal.ofReal
        (4 * ∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l a) := by
  set S : ℝ := ∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l a with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun l _ => Work.BourgainPlan.Maximal.rmLevel_nonneg n l a
  -- the supremum part
  have hsup : (⨆ k : ℕ, ‖a (σ k)‖ₑ)
      ≤ ‖a 0‖ₑ + Work.BourgainPlan.Maximal.varTwo 0 K a := by
    refine iSup_le fun k => ?_
    have h1 : ‖a (σ k)‖ₑ ≤ ‖a 0‖ₑ + ‖a (σ k) - a 0‖ₑ := by
      have heq : a 0 + (a (σ k) - a 0) = a (σ k) := by ring
      calc ‖a (σ k)‖ₑ = ‖a 0 + (a (σ k) - a 0)‖ₑ := by rw [heq]
        _ ≤ ‖a 0‖ₑ + ‖a (σ k) - a 0‖ₑ := enorm_add_le _ _
    refine h1.trans (add_le_add le_rfl ?_)
    exact (Work.BourgainPlan.Maximal.enorm_sub_le_varRho (ρ := 2) (by norm_num)
        (Nat.zero_le _) (hK k) a).trans
      (Work.BourgainPlan.Maximal.varRho_le_varTwo (by norm_num) 0 K a)
  -- the chain part
  have hchain : Submission.PointwiseErgodicTheorems.varPart 2 (fun k : ℕ => a (σ k))
      ≤ Work.BourgainPlan.Maximal.varTwo 0 K a := by
    refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => ?_
    have hmono : Monotone fun j => σ (t j) := hσ.comp ht
    have hrange : ∀ j ≤ J, 0 ≤ σ (t j) ∧ σ (t j) ≤ K := fun j _ => ⟨Nat.zero_le _, hK _⟩
    calc ENNReal.ofReal ‖WithLp.toLp (2 : NNReal)
          (fun i : Fin J => a (σ (t (i + 1))) - a (σ (t i)))‖
        = ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J a (fun j => σ (t j))) :=
          Work.KMTAreas.A7G.ofReal_norm_toLp_two_eq_ofReal_chainLp J a (fun j => σ (t j))
      _ ≤ Work.BourgainPlan.Maximal.varRho 2 0 K a :=
          Work.BourgainPlan.Maximal.ofReal_chainLp_le_varRho 2 0 K J a (fun j => σ (t j))
            hmono hrange
      _ ≤ Work.BourgainPlan.Maximal.varTwo 0 K a :=
          Work.BourgainPlan.Maximal.varRho_le_varTwo (by norm_num) 0 K a
  -- the RM bound on the `2`-variation
  have hrm : Work.BourgainPlan.Maximal.varTwo 0 K a ≤ ENNReal.ofReal (2 * S) := by
    have h2 : Work.BourgainPlan.Maximal.varTwo 0 K a
        ≤ Work.BourgainPlan.Maximal.varTwo 0 (2 ^ n) a := by
      refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun h => ?_
      exact le_iSup_of_le J (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le
        (fun j hj => ⟨(h j hj).1, le_trans (h j hj).2 hKn⟩) le_rfl)))
    refine h2.trans ?_
    have h3 := Work.BourgainPlan.Maximal.varTwo_le_rmLevels n 0 a
    rw [Nat.zero_add] at h3
    have heq : (∑ l ∈ Finset.range (n + 1),
          Work.BourgainPlan.Maximal.rmLevel n l (fun r => a (0 + r)))
        = ∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l a := by
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      funext r
      simp
    rw [heq] at h3
    simpa only [hSdef] using h3
  -- `2 * ofReal (2S) = ofReal (4S)`
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (2 * S) = ENNReal.ofReal (4 * S) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  calc PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => a (σ k))
      ≤ PointwiseErgodicTheorems.variationalNorm 2 (fun k : ℕ => a (σ k)) :=
        Work.Analysis.Paraproduct.variationalNorm_mono_of_two_le hr _
    _ = (⨆ k : ℕ, ‖a (σ k)‖ₑ)
          + Submission.PointwiseErgodicTheorems.varPart 2 (fun k : ℕ => a (σ k)) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_eq_add 2 _
    _ ≤ (‖a 0‖ₑ + Work.BourgainPlan.Maximal.varTwo 0 K a)
          + Work.BourgainPlan.Maximal.varTwo 0 K a := add_le_add hsup hchain
    _ = ‖a 0‖ₑ + 2 * Work.BourgainPlan.Maximal.varTwo 0 K a := by rw [add_assoc, two_mul]
    _ ≤ ‖a 0‖ₑ + ENNReal.ofReal (4 * S) := by
        refine add_le_add le_rfl ?_
        rw [← htwo]
        exact mul_le_mul_of_nonneg_left hrm (by norm_num)

/-! ## The dyadic block square functions of the projection walk -/

/-- **The sum of the RM dyadic block square functions of the low-pass projection walk is bounded in
`ℓᵖ` by `C (n+1)‖f‖_{ℓᵖ}`**, with `C` free of the height, of `m₀` and of `n`.

This is the level-summed form of `A7Rescue.blockSqFunWalk` (which bounds each block square function
by the same `l`-free, `m₀`-free constant): there are `n + 1` terms. -/
theorem rmLevelSumLpKmtProj (ρ : ℝ) (p : ENNReal) (hp : 1 ≤ p) (hptop : p < ⊤) (Cρ : ℝ)
    (hUS : ∀ (l m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cρ * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h m₀ n : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ h (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
          (∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l
            (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * ((n : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cblk, hCblkpos, hblk⟩ := blockSqFunWalk ρ p hptop Cρ hUS
  refine ⟨Cblk, hCblkpos, ?_⟩
  intro h m₀ n hgood f
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hlev : ∀ l ∈ Finset.range (n + 1),
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal (Work.BourgainPlan.Maximal.rmLevel n l
        (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cblk * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro l hl
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hb := hblk h m₀ hgood id monotone_id n l hl' f
    refine le_trans (le_of_eq ?_) hb
    congr 1
    funext x
    rw [Work.BourgainPlan.Maximal.rmLevel, Real.sqrt_eq_rpow]
    simp only [id_eq]
  have hpoint : (fun x : ℤ => ENNReal.ofReal
        (∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l
          (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
      = fun x : ℤ => ∑ l ∈ Finset.range (n + 1), ENNReal.ofReal
          (Work.BourgainPlan.Maximal.rmLevel n l
            (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)) := by
    funext x
    exact ENNReal.ofReal_sum_of_nonneg
      (fun l _ => Work.BourgainPlan.Maximal.rmLevel_nonneg n l _)
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => ∑ l ∈ Finset.range (n + 1),
        ENNReal.ofReal (Work.BourgainPlan.Maximal.rmLevel n l
          (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
        p MeasureTheory.Measure.count
      ≤ ∑ _l ∈ Finset.range (n + 1), ENNReal.ofReal Cblk *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    (Work.KMTAreas.A7.eLpNorm_finset_sum_le_ennreal (Finset.range (n + 1))
      (fun l x => ENNReal.ofReal (Work.BourgainPlan.Maximal.rmLevel n l
        (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x))) hp hpt).trans
      (Finset.sum_le_sum hlev)
  have hconst : (∑ _l ∈ Finset.range (n + 1), ENNReal.ofReal Cblk *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
      = ENNReal.ofReal (Cblk * ((n : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h1 : (∑ _l ∈ Finset.range (n + 1), ENNReal.ofReal Cblk *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
        = ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal Cblk *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1, ← ENNReal.ofReal_natCast, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    have h2 : (((n + 1 : ℕ) : ℝ)) * Cblk = Cblk * ((n : ℝ) + 1) := by
      push_cast
      ring
    rw [h2]
  rw [hpoint]
  exact hsum.trans (le_of_eq hconst)

/-! ## The good major arcs at one level below -/

/-- **`GoodMajorArcs` is monotone in the height** (`ρ > 0`, `Cρ ≥ 0`): the narrowness hypothesis at
the height `l` implies the (weaker) hypothesis at the height `l - 1`. -/
lemma goodMajorArcs_pred {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 0 ≤ Cρ) {l : ℕ} {k : ℤ}
    (h : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k) :
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ (l - 1) k := by
  unfold Work.Analysis.IonescuWainger.GoodMajorArcs at h ⊢
  have hle : ((l - 1 : ℕ) : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast Nat.sub_le l 1
  have h1 : (2 : ℝ) ^ (ρ * ((l - 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have h2 : -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ -Cρ * (2 : ℝ) ^ (ρ * ((l - 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonpos_left h1 (by linarith)
  linarith

/-! ## The short-window bound at a single height -/

/-- Subadditivity of the variational norm with respect to a difference (`r ≥ 1`). -/
lemma variationalNorm_sub_le {r : NNReal} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (a - b)
      ≤ PointwiseErgodicTheorems.variationalNorm r a
        + PointwiseErgodicTheorems.variationalNorm r b := by
  have h : a - b = a + (-1 : ℂ) • b := by
    funext n
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    ring
  have h2 : PointwiseErgodicTheorems.variationalNorm r ((-1 : ℂ) • b)
      = PointwiseErgodicTheorems.variationalNorm r b := by
    rw [Submission.PointwiseErgodicTheorems.variationalNorm_smul hr]
    norm_num
  calc PointwiseErgodicTheorems.variationalNorm r (a - b)
      = PointwiseErgodicTheorems.variationalNorm r (a + (-1 : ℂ) • b) := by rw [h]
    _ ≤ PointwiseErgodicTheorems.variationalNorm r a
          + PointwiseErgodicTheorems.variationalNorm r ((-1 : ℂ) • b) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr a ((-1 : ℂ) • b)
    _ = PointwiseErgodicTheorems.variationalNorm r a
          + PointwiseErgodicTheorems.variationalNorm r b := by rw [h2]

/-- Passing to extended norms does not change the `eLpNorm`. -/
lemma eLpNorm_enorm_eq {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- **The short-window (`head`) variational bound at a single height.**  On the good major arcs,

`‖ V^r_{k} (Π_{≤h,≤-(m₀+L k)} f) ‖_{ℓᵖ} ≤ C (⌈log₂ (N+1)⌉ + 1) ‖f‖_{ℓᵖ}`

for every monotone walk `L` with `L k ≤ N`, uniformly in the height `h` and the base level `m₀`.

The proof splits the `V^r`-norm by Rademacher--Menshov (`walkVarNormRmLevels`) into the base value
plus the `n + 1` dyadic block square functions at the levels `≤ 2^n ≥ N`, bounds the level sum by
`C(n+1)‖f‖` (`rmLevelSumLpKmtProj`, i.e. Khintchine + the uniform-in-signs annulus bound
`annuliUniformSigns`), and the base value by the single-scale bound `kmtProj_lp_bound_uniform`. -/
theorem headVarSingle (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (h m₀ N : ℕ) (L : ℕ → ℕ), Monotone L → (∀ k : ℕ, L k ≤ N) →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ h (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (L k : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρA, hCρApos, CA, hCApos, hUSA⟩ :=
    Work.KMTAreas.A7G.annuliUniformSigns ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hSB⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  set Cρ0 : ℝ := max CρA CA with hCρ0def
  have hCρ0pos : 0 < Cρ0 := lt_max_of_lt_left hCρApos
  have hUS0 : ∀ (l m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ0 l (-(m₀ : ℤ)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cρ0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro l m₀ hg U ω f
    have hgA : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρA l (-(m₀ : ℤ)) :=
      Work.KMTAreas.A7Hi.goodMajorArcs_mono (by rw [hCρ0def]; exact le_max_left _ _) hg
    refine (hUSA l m₀ hgA U ω f).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (by rw [hCρ0def]; exact le_max_right _ _)) bot_le
  obtain ⟨CLsum, hCLpos, hLsum⟩ := rmLevelSumLpKmtProj ρ p (le_of_lt hp) hptop Cρ0 hUS0
  set Cρ : ℝ := max (max Cρ0 CρS) 2 with hCρdef
  have hCρpos : 0 < Cρ := lt_max_of_lt_right (by norm_num)
  have hle0 : Cρ0 ≤ Cρ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hleS : CρS ≤ Cρ := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨Cρ, hCρpos, CS + 4 * CLsum, by linarith, ?_⟩
  intro h m₀ N L hL hLN hgood f
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hpn : (1 : ℝ≥0∞) ≤ p := le_of_lt hp
  set n : ℕ := Nat.clog 2 (N + 1) with hn
  have hNn : N ≤ 2 ^ n := by
    have hcl := Nat.le_pow_clog (b := 2) (by norm_num : (1 : ℕ) < 2) (N + 1)
    rw [hn]
    omega
  have hgood0 : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ0 h (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono hle0 hgood
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS h (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono hleS hgood
  -- the pointwise Rademacher--Menshov bound
  have hpt2 : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (L k : ℤ))) f x)
        ≤ ‖Work.KMTContract.kmtProj ρ h (-(m₀ : ℤ)) f x‖ₑ
          + ENNReal.ofReal 4 * ENNReal.ofReal (∑ l ∈ Finset.range (n + 1),
              Work.BourgainPlan.Maximal.rmLevel n l
                (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)) := by
    intro x
    have h1 := walkVarNormRmLevels (r := r) (le_of_lt hr)
      (a := fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)
      (σ := L) hL (K := N) (n := n) hLN hNn
    have h2 : PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (L k : ℤ))) f x)
        ≤ ‖Work.KMTContract.kmtProj ρ h (-(m₀ : ℤ)) f x‖ₑ
          + ENNReal.ofReal (4 * ∑ l ∈ Finset.range (n + 1),
              Work.BourgainPlan.Maximal.rmLevel n l
                (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)) := by
      simpa using h1
    refine h2.trans (add_le_add le_rfl ?_)
    exact le_of_eq (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4))
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun k : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (L k : ℤ))) f x))
        p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            ‖Work.KMTContract.kmtProj ρ h (-(m₀ : ℤ)) f x‖ₑ) p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 4 * ENNReal.ofReal
            (∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l
              (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
          p MeasureTheory.Measure.count :=
    (Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt2 hp0 hpt).trans
      (Work.KMTAreas.A7.eLpNorm_add_le_ennreal (μ := MeasureTheory.Measure.count) hpn hpt)
  have hfirst : MeasureTheory.eLpNorm (fun x : ℤ =>
        ‖Work.KMTContract.kmtProj ρ h (-(m₀ : ℤ)) f x‖ₑ) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [eLpNorm_enorm_eq hp0 hpt]
    have h := hSB h (-(m₀ : ℤ)) hgoodS f
    rw [ENNReal.ofReal_toReal (ne_of_lt hptop)] at h
    exact h
  have hsecond : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 4 * ENNReal.ofReal
        (∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l
          (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (CLsum * ((n : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
    rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ENNReal.ofReal 4)
      ENNReal.ofReal_ne_top hp0 hpt]
    exact mul_le_mul_of_nonneg_left (hLsum h m₀ n hgood0 f) bot_le
  have hcombine : ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal 4 * (ENNReal.ofReal (CLsum * ((n : ℝ) + 1)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
      = ENNReal.ofReal (CS + 4 * (CLsum * ((n : ℝ) + 1))) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← add_mul,
      ← ENNReal.ofReal_add hCSpos.le (by positivity)]
  have hfinal : ENNReal.ofReal (CS + 4 * (CLsum * ((n : ℝ) + 1))) *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((CS + 4 * CLsum) * ((n : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    nlinarith [hCSpos, hCLpos, hn0, hn1]
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ =>
          ‖Work.KMTContract.kmtProj ρ h (-(m₀ : ℤ)) f x‖ₑ) p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 4 * ENNReal.ofReal
            (∑ l ∈ Finset.range (n + 1), Work.BourgainPlan.Maximal.rmLevel n l
              (fun j : ℕ => Work.KMTContract.kmtProj ρ h (-((m₀ : ℤ) + (j : ℤ))) f x)))
            p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal 4 * (ENNReal.ofReal (CLsum * ((n : ℝ) + 1)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := add_le_add hfirst hsecond
    _ = ENNReal.ofReal (CS + 4 * (CLsum * ((n : ℝ) + 1))) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hcombine
    _ ≤ ENNReal.ofReal ((CS + 4 * CLsum) * ((n : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hfinal
    _ = ENNReal.ofReal ((CS + 4 * CLsum) * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by rw [hn]

/-- **The requested short-window (`head`) variational bound, with the height increment**
`Π_{≤l,≤-(m₀+m)} - Π_{≤l-1,≤-(m₀+m)}`.

Write the family as the difference of the two single-height walks and use the subadditivity of the
variational norm; the height-`(l-1)` walk is controlled by `headVarSingle` with the good major arcs
at the height `l - 1` (`goodMajorArcs_pred`). -/
theorem headVarBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l m₀ N : ℕ) (L : ℕ → ℕ), Monotone L → (∀ k : ℕ, L k ≤ N) →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
      ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρpos, C1, hC1pos, hSingle⟩ := headVarSingle ρ hρ hρ1 r hr p hp hptop
  refine ⟨Cρ, hCρpos, 2 * C1, by linarith, ?_⟩
  intro l m₀ N L hL hLN hgood f
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hgoodB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ (l - 1) (-(m₀ : ℤ)) :=
    goodMajorArcs_pred hρ (le_of_lt hCρpos) hgood
  have hA := hSingle l m₀ N L hL hLN hgood f
  have hB := hSingle (l - 1) m₀ N L hL hLN hgoodB f
  have hsub : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x)
        + PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x) := by
    intro x
    exact variationalNorm_sub_le hr1 _ _
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x))
        p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x))
            p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x))
            p MeasureTheory.Measure.count :=
    (Work.KMTAreas.A7.eLpNorm_mono_ennreal hsub hp0 hpt).trans
      (Work.KMTAreas.A7.eLpNorm_add_le_ennreal (μ := MeasureTheory.Measure.count)
        (le_of_lt hp) hpt)
  have hA' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hA
  have hB' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hB
  have hdouble : ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1))
        + ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1))
      = ENNReal.ofReal (2 * C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) := by
    have hnn : (0 : ℝ) ≤ C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1) := by positivity
    rw [← ENNReal.ofReal_add hnn hnn]
    congr 1
    ring
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (L k) f x))
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (L k) f x))
          p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
          + ENNReal.ofReal (C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := add_le_add hA' hB'
    _ = ENNReal.ofReal (2 * C1 * ((Nat.clog 2 (N + 1) : ℝ) + 1)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← add_mul, hdouble]

end

end Work.KMTAreas.A7Rescue
