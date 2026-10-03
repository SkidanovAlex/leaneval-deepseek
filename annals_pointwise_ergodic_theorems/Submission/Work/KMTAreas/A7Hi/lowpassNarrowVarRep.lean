/-
# The narrow lacunary low-pass variational estimate for the unmodulated Ionescu--Wainger bumps
(`Work.KMTAreas.A7Hi.lowpassNarrowVarRep`)

Math: the low-frequency case of the paper's (lin-1) (Krause--Mirek--Tao, Annals 195 (2022), §8) in
the discrete `ℓᵖ(ℤ)` model: for the *unmodulated* bump family `ψ_n = varphiN ⌊a n⌋ 0` over a
`Λ`-lacunary scale family `a`, the `r`-variation (`2 < r`) is bounded on `ℓᵖ(ℤ)`, `1 < p < ∞`, by
`C (1 + l₁)² ‖f‖_{ℓᵖ}`, uniformly in the arithmetic height `l₁`, in the family `a`, and in the
narrowness level `k`.

## The reduction proved here (do not re-derive)

Write `lpf ρ l₁ m₀ m = kmtProj ρ l₁ (-(m₀+m))` (`Work.KMTAreas.A7Hi.lpf`), so that the walk at the
base level `m₀ = (-k).toNat` is the family `m ↦ lpf ρ l₁ m₀ m f`, and

  `Tle ρ l₁ (varphiN N 0) = kmtProj ρ l₁ (-(logN N))`   (`Tle_varphiN_zeroRep`)

with `logN` monotone makes the lacunary family a monotone reindexing of the walk
(`monotone_of_lacunaryRep`, `logN_monoRep`).  Since `variationalNorm r = supPart r + chainPart r`
(`LowpassDefs`), the target follows from the two *halves of the walk*:

* **the maximal (Men'shov/Lépingle) piece** with a *linear* loss,
  `‖sup_K |Σ_{i<K} (T_{i+1} - T_i) f|‖_{ℓᵖ} ≤ C (1+l₁)(‖sqFun f‖_{ℓᵖ} + ‖f‖_{ℓᵖ})`
  (delegated as `Work.KMTAreas.A7Hi.maxPieceLin`, and *verbatim* the tree's reviewed stub
  `Work.KMTAreas.A7Hi.lacunaryMaxPieceLinRep`); together with the *proved, `l₁`-free* single-scale
  bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` it gives
  `‖supPart r (walk f)‖_{ℓᵖ} ≤ A (1+l₁)‖f‖_{ℓᵖ}` via the telescoping
  `T_K = T_0 - Σ_{i<K} (T_{i+1}-T_i)` (`supPart_le_first_add_partSum`);

* **the chain piece** with a *linear* loss,
  `‖chainPart r (walk f)‖_{ℓᵖ} ≤ B (1+l₁)(‖supPart r (walk f)‖_{ℓᵖ} + ‖sqFun f‖_{ℓᵖ})`
  (delegated as `Work.KMTAreas.A7Hi.chainLin`, *verbatim* the reviewed stub
  `Work.KMTAreas.A7Hi.chainLeLinRep`).

The *proved, `l₁`-free* band square-function bound `Work.KMTAreas.A7Lpd.bandSquareUnif`
(`‖sqFun f‖_{ℓᵖ} ≤ C_B ‖f‖_{ℓᵖ}`) turns both into `≤ (1+l₁)·‖f‖`, and their sum into the target's
`(1+l₁)²`: `C_total = A + B (A + C_B)` with `A = C_S + C_M (C_B + 1)`.

## Status of the two pieces (checked by `#print axioms` in this session)

* `A7.kmtProj_lp_bound_uniform`, `A7Lpd.bandSquareUnif`, `A7G.plainBumpVarG` (the arithmetic-free
  `l₁ = 0` variational estimate), `A7Hi.DilVar`, `A7Hi2.sqFunBound`, `A7.lacDilTriVar`,
  `A7G.annuliUniformSigns`: **proved and axiom-clean**.
* the tree's sockets `A7Hi2.lacunaryMaxPiece`, `A7Hi2.chainLe`, `A7G.maximalLowpass`,
  `A7G.chainPartLowpass`, `A7G.lowpassAlphaTransferG`, `A7G.lowpassVarG` (and the `A7Rescue` copy):
  **all depend on an unproved axiom** (checked with `#print axioms`).
* the *parametric* copy `Work.KMTAreas.A7Hi.lowpassVarGD1` (this session) proves the same statement
  for `1 ≤ P.natDegree` (where the tree's copies assume `2 ≤ P.natDegree`) with a **clean** proof
  closure; the target is its `P = X` instance, because `varphitildeN 1 N 0 = varphiN N 0`
  definitionally.  This is the proof used below.

## The exact shape of the tree's reduction (verified this session)

`Work.KMTAreas.A7G.lowpassVarG (d) (hd : 1 ≤ d)` *states* the whole arithmetic-free-plus-comb
estimate `‖V^r_n (Tle ρ l₂ (varphitildeN d ⌊a n⌋ 0) f)‖_p ≤ C (1+l₂)² ‖f‖_p`, and since
`varphitildeN 1 N 0 = varphiN N 0` **definitionally** (both are `fun ξ ↦ kmtEta (2^{logN N} ξ)`,
see `A7/Large/Defs.lean`), its `d = 1` instance *is* this file's target.  Its proof is
`A7G.plainBumpVarG d hd` (clean) ∘ `A7G.lowpassAlphaTransferG d hd`, and the latter is proved from
`A7G.maximalLowpass` (the `l₁`-linear values-sup bound, *proved from the unproved*
`A7Hi2.lacunaryMaxPiece` plus the two clean bounds above) and `A7G.chainPartLowpass` (the
Lépingle/JSW chain step; that file carries an unfinished goal).  So the *only* two missing inputs of
that route are the two pieces delegated here, in their linear-loss forms.

## Dead routes (do not re-attempt)

* the KMSZ / `varRhoAll 2` route (`Work.A7Fix.lpfKmszLargeScale`): the `2`-variation of the walk is
  FALSE (Krause arXiv:1402.1803 §8; KMT's `r-counter`), so `LargeScaleBoundF`/`SignedDiffBoundF`
  are unsatisfiable; see `NOTES_A7Hi_lpfLargeScaleRep_VERDICT_FALSE.md`.
* the kernel/sieve-mass route (`Work.A7Hi2.SieveAssembly`): the sieve mass `Σ_d |sieveCoeff ρ l₁ d|`
  is exponential in `l₁` (both in the bounded-height and the deep regime), so no accounting of the
  kernel reaches `(1+l₁)²`.
* the "martingale/decimation" route: the arithmetic frequency set `iwArithFreqs ρ l₁` is
  `⋃_{q ≤ 2^{l₁}}(1/q)ℤ`, which is **never** a single torsion subgroup (it misses `1/q₀`), so the
  exact decimation identity `c(j) = q·1_{q|j}` for the arithmetic character *never* holds; the
  subadditivity over the residue classes then costs `(1/#per)Σ_r |c(r)|`, whose RMS is `√♯A`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.lowpassVarGD1
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar

noncomputable section

/-! ## Elementary identities for the unmodulated bump -/

/-- `varphiN N 0 = etaCut kmtEta (-(logN N))`: the unmodulated low-pass bump at scale `N` is the
continuous cutoff at level `-(logN N)`. -/
theorem varphiN_zero_eq_etaCutRep (N : ℕ) :
    Work.KMTAreas.A7.varphiN N 0
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(logN N)) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphiN, if_true, Work.Analysis.IonescuWainger.etaCut]
  congr 1
  rw [div_eq_mul_inv, zpow_neg, inv_inv, Real.rpow_intCast]
  ring

/-- `Tle ρ l₁ (varphiN N 0) = kmtProj ρ l₁ (-(logN N))`. -/
theorem Tle_varphiN_zeroRep (ρ : ℝ) (l₁ : ℕ) (N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN N 0)
      = Work.KMTContract.kmtProj ρ l₁ (-(logN N)) := by
  rw [varphiN_zero_eq_etaCutRep]
  exact Work.KMTAreas.A7.Tle_etaCut ρ l₁ (-(logN N))

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem monotone_of_lacunaryRep {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- `logN` is monotone in the scale (local copy). -/
theorem logN_monoRep {N M : ℕ} (h : N ≤ M) : logN N ≤ logN M := by
  unfold Work.Analysis.EndVar.logN
  exact Int.ofNat_le.mpr (Nat.log_mono_right (max_le_max h le_rfl))

/-- Combining two `ofReal`-multiples of the same `ℝ≥0∞`: if `a + b ≤ A'` (all nonnegative), then
`ofReal a * K + ofReal b * K ≤ ofReal A' * K`. -/
theorem ofReal_combine {a b A' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ A') (K : ℝ≥0∞) :
    ENNReal.ofReal a * K + ENNReal.ofReal b * K ≤ ENNReal.ofReal A' * K := by
  rw [← add_mul, ← ENNReal.ofReal_add ha hb]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) bot_le

/-- The `eLpNorm` of the `enorm` of a function is the `eLpNorm` of the function. -/
theorem eLpNorm_enorm_eqRep {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-! ## The telescoping bound for the values supremum -/

/-- **The values supremum of a sequence is bounded by its first value plus the maximal partial sum
of its increments.**  This is the finite telescoping `a n = a 0 + Σ_{i<n}(a (i+1) - a i)`. -/
theorem supPart_le_first_add_partSum (r : NNReal) (a : ℕ → ℂ) :
    supPart r a ≤ ‖a 0‖ₑ + ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K, (a (i + 1) - a i))‖ₑ := by
  refine iSup_le fun n => ?_
  have htel : (∑ i ∈ Finset.range n, (a (i + 1) - a i)) = a n - a 0 := Finset.sum_range_sub a n
  have hEq : a n = a 0 + ∑ i ∈ Finset.range n, (a (i + 1) - a i) := by
    rw [htel]; ring
  rw [hEq]
  refine (enorm_add_le (a 0) _).trans (add_le_add le_rfl ?_)
  exact le_iSup (fun K : ℕ => ‖(∑ i ∈ Finset.range K, (a (i + 1) - a i))‖ₑ) n

/-! ## The assembly -/

/-- **The assigned statement from the two linear-loss pieces.**

`hMax` is the lacunary maximal piece with a linear loss (`maxPieceLin`) and `hChain` the chain piece
with a linear loss (`chainLin`); both are strictly weaker than the tree's sharp (`l₁`-free) stubs
`A7Hi2.lacunaryMaxPiece` / `A7Hi2.chainLe`.  Everything else used here is proved and axiom-clean:
the single-scale bound `A7.kmtProj_lp_bound_uniform`, the band square function
`A7Lpd.bandSquareUnif`, and the elementary telescoping `supPart_le_first_add_partSum`. -/
theorem lowpassNarrowVarRep_of_pieces
    (hMax : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count
          + ENNReal.ofReal (C * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hChain : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ₀ : ℝ),
      ∃ B : ℝ, 0 < B ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7Hi.chainPart r
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (B * (1 + (l₁ : ℝ))) *
          (MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
              p MeasureTheory.Measure.count
           + MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
        (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hptne : p ≠ ⊤ := ne_of_lt hptop
  obtain ⟨CρM, hCρM, CM, hCM, hMaxB⟩ := hMax ρ hρ hρ1 p hp hptop
  obtain ⟨CρB, hCρB, CB, hCB, hBand⟩ :=
    Work.KMTAreas.A7Lpd.bandSquareUnif ρ hρ hρ1 p hp hptop
  obtain ⟨CρS, hCρS, CS, hCS, hSingle⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  set Cρ : ℝ := max CρM (max CρB CρS) with hCρdef
  have hCρpos : 0 < Cρ := by rw [hCρdef]; exact lt_max_of_lt_left hCρM
  obtain ⟨B, hBpos, hChainB⟩ := hChain ρ hρ hρ1 r hr p hp hptop Cρ
  set A : ℝ := CS + CM * (CB + 1) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hTpos : (0 : ℝ) < A + B * (A + CB) := by positivity
  refine ⟨Cρ, hCρpos, A + B * (A + CB), hTpos, ?_⟩
  intro k l₁ a ha ha1 f hgood hk
  -- bookkeeping: `k ≤ 0` and `m₀ := (-k).toNat`
  have hk0 : k ≤ 0 := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := hgood
    have h3 : (k : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast h3
  set m₀ : ℕ := (-k).toNat with hm₀def
  have hm₀ : ((m₀ : ℕ) : ℤ) = -k := by
    rw [hm₀def]; exact Int.toNat_of_nonneg (by omega)
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) := by
    rw [hm₀, neg_neg]; exact hgood
  have hgoodM : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρM l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (C₁ := CρM) (C₂ := Cρ)
      (by rw [hCρdef]; exact le_max_left _ _) hgood'
  have hgoodB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (C₁ := CρB) (C₂ := Cρ)
      (by rw [hCρdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)) hgood'
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (C₁ := CρS) (C₂ := Cρ)
      (by rw [hCρdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hgood'
  -- the three bounds
  have hSq : MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
        p MeasureTheory.Measure.count ≤ ENNReal.ofReal CB *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hBand l₁ m₀ hgoodB f
  have hbase : MeasureTheory.eLpNorm
        (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ) p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) := by
      funext y; simp only [Work.KMTAreas.A7Hi.lpf, Int.natCast_zero, add_zero]
    have h := hSingle l₁ (-(m₀ : ℤ)) hgoodS f
    rw [hpeq] at h
    rw [eLpNorm_enorm_eqRep hp0 hptne, h0]
    exact h
  have hPart := hMaxB l₁ m₀ hgoodM f
  -- the values-supremum bound
  have hSup : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hpt : ∀ x : ℤ, Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
        ≤ (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ) x
          + (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
              (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ) x := by
      intro x
      exact supPart_le_first_add_partSum r _
    have h1 : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
            + ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
                (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count :=
      Work.KMTAreas.A7.eLpNorm_mono_ennreal (fun x => hpt x) hp0 hptne
    have h2 : MeasureTheory.eLpNorm (fun x : ℤ =>
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
            + ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
                (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
            p MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
                (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
            p MeasureTheory.Measure.count :=
      Work.KMTAreas.A7.eLpNorm_add_le_ennreal (μ := MeasureTheory.Measure.count)
        (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        (v := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        (q := p) hp1 hptne
    have h3 : MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
                p MeasureTheory.Measure.count
          + ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hPart
    have hmono : CS + (CM * (1 + (l₁ : ℝ)) * CB + CM * (1 + (l₁ : ℝ)))
        ≤ A * (1 + (l₁ : ℝ)) := by
      have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
      have h1l : (1 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith
      have h2 : CS ≤ CS * (1 + (l₁ : ℝ)) := by nlinarith [hCS, h1l]
      have h3 : CM * (1 + (l₁ : ℝ)) * CB + CM * (1 + (l₁ : ℝ))
          = CM * (CB + 1) * (1 + (l₁ : ℝ)) := by ring
      rw [h3, hAdef]; nlinarith [h2, hCM, hCB, hCS, h1l, hl0]
    have hsqrew : MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) * (ENNReal.ofReal CB *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
          + ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      refine h3.trans (add_le_add ?_ le_rfl)
      exact mul_le_mul_of_nonneg_left hSq bot_le
    have hcount : ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) * (ENNReal.ofReal CB *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
          + ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        = ENNReal.ofReal (CM * (1 + (l₁ : ℝ)) * CB + CM * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
            p MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
                (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
                  - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
            p MeasureTheory.Measure.count := h1.trans h2
      _ ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
            + (ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) * (ENNReal.ofReal CB *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
              + ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :=
          add_le_add hbase hsqrew
      _ ≤ ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          have hmid : ENNReal.ofReal (CM * (1 + (l₁ : ℝ))) *
                (ENNReal.ofReal CB * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
              = ENNReal.ofReal (CM * (1 + (l₁ : ℝ)) * CB) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          rw [hmid]
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ofReal_combine (by positivity) (by positivity) hmono _
  -- the chain bound
  have hChainPart : MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B * (1 + (l₁ : ℝ))) *
          (ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
            + ENNReal.ofReal CB * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
    refine (hChainB l₁ m₀ hgood' f).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add hSup hSq) bot_le
  -- the dyadic bound
  have hmain : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((A + B * (A + CB)) * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have hsplit : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        = (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          + (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) := by
      funext x
      exact Work.KMTAreas.A7Hi.variationalNorm_eq_parts r _
    rw [hsplit]
    refine ((Work.KMTAreas.A7.eLpNorm_add_le_ennreal (μ := MeasureTheory.Measure.count)
      (u := fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      (q := p) hp1 hptne).trans ((add_le_add hSup hChainPart).trans ?_))
    -- constant bookkeeping
    have hArith : A * (1 + (l₁ : ℝ))
          + B * (1 + (l₁ : ℝ)) * (A * (1 + (l₁ : ℝ)) + CB)
        ≤ (A + B * (A + CB)) * (1 + (l₁ : ℝ)) ^ 2 := by
      have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
      have h1l : (1 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith
      have h1 : A ≤ A * (1 + (l₁ : ℝ)) := by nlinarith [hApos, h1l]
      have h2 : CB ≤ CB * (1 + (l₁ : ℝ)) := by nlinarith [hCB, h1l]
      have h3 : A * (1 + (l₁ : ℝ)) + CB ≤ (A + CB) * (1 + (l₁ : ℝ)) := by linarith
      have h4 : B * (1 + (l₁ : ℝ)) * (A * (1 + (l₁ : ℝ)) + CB)
          ≤ B * (1 + (l₁ : ℝ)) * ((A + CB) * (1 + (l₁ : ℝ))) := by
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : B * (1 + (l₁ : ℝ)) * ((A + CB) * (1 + (l₁ : ℝ)))
          ≤ B * (A + CB) * (1 + (l₁ : ℝ)) ^ 2 := by
        nlinarith [h1l, hBpos, add_pos hApos hCB]
      nlinarith [h1, h4, h5, h1l, hApos, hBpos, hCB, hl0]
    have hstep : ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
          + ENNReal.ofReal (B * (1 + (l₁ : ℝ))) *
            (ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
              + ENNReal.ofReal CB * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal ((A + B * (A + CB)) * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
      have hinner : ENNReal.ofReal (B * (1 + (l₁ : ℝ))) *
            (ENNReal.ofReal (A * (1 + (l₁ : ℝ))) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
              + ENNReal.ofReal CB * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
          = ENNReal.ofReal (B * (1 + (l₁ : ℝ)) * (A * (1 + (l₁ : ℝ)) + CB)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [hinner]
      exact ofReal_combine (by positivity) (by positivity) hArith _
    exact hstep
  -- the monotone reindexing of the lacunary family onto the dyadic walk
  set σ : ℕ → ℕ := fun n => ((logN (Nat.floor (a n))) + k).toNat with hσdef
  have hσcoe : ∀ n : ℕ, ((σ n : ℕ) : ℤ) = logN (Nat.floor (a n)) + k := by
    intro n
    rw [hσdef]
    exact Int.toNat_of_nonneg (by have h := hk n; omega)
  have hσmono : Monotone σ := by
    intro n m hnm
    have h1 : Nat.floor (a n) ≤ Nat.floor (a m) :=
      Nat.floor_mono ((monotone_of_lacunaryRep hΛ ha ha1) hnm)
    have h2 : logN (Nat.floor (a n)) ≤ logN (Nat.floor (a m)) := logN_monoRep h1
    have h3 : (0 : ℤ) ≤ logN (Nat.floor (a n)) + k := by have h := hk n; omega
    have h4 : (0 : ℤ) ≤ logN (Nat.floor (a m)) + k := by have h := hk m; omega
    show ((logN (Nat.floor (a n))) + k).toNat ≤ ((logN (Nat.floor (a m))) + k).toNat
    have hx : ((((logN (Nat.floor (a n))) + k).toNat : ℕ) : ℤ)
        = logN (Nat.floor (a n)) + k := Int.toNat_of_nonneg h3
    have hy : ((((logN (Nat.floor (a m))) + k).toNat : ℕ) : ℤ)
        = logN (Nat.floor (a m)) + k := Int.toNat_of_nonneg h4
    have h5 : ((((logN (Nat.floor (a n))) + k).toNat : ℕ) : ℤ)
        ≤ ((((logN (Nat.floor (a m))) + k).toNat : ℕ) : ℤ) := by rw [hx, hy]; omega
    exact_mod_cast h5
  have hreindex : ∀ x : ℤ, (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
        (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)
      = fun n : ℕ => (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) (σ n) := by
    intro x
    funext n
    have h1 : (-(logN (Nat.floor (a n))) : ℤ) = -((m₀ : ℤ) + ((σ n : ℕ) : ℤ)) := by
      rw [hm₀, hσcoe n]; ring_nf
    show Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x
      = Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((σ n : ℕ) : ℤ))) f x
    rw [Tle_varphiN_zeroRep, h1]
  rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) (σ n))) from by
    funext x; rw [hreindex x]]
  exact (Work.KMTAreas.A7.eLpNorm_mono_ennreal (fun x =>
        Work.KMTAreas.A7.variationalNorm_comp_mono_le
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) hσmono)
      hp0 hptne).trans hmain

/-! ## The assigned target

The statement below is the requester's, verbatim.  It is the `d = 1` instance of
`Work.KMTAreas.A7Hi.lowpassVarGD1` (the parametric proof of the paper's (lin-1)/(lin-2)
low-frequency case, `d ≥ 1`, for the bump family `varphitildeN d ⌊a n⌋ 0`), because
`varphitildeN 1 N 0 = varphiN N 0` definitionally.  The alternative route via the two linear-loss
pieces is recorded in `lowpassNarrowVarRep_of_pieces` above (and was superseded by the parametric
proof). -/
theorem lowpassNarrowVarRep (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
        (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hX : (Polynomial.X : Polynomial ℤ).natDegree = 1 := Polynomial.natDegree_X
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ :=
    Work.KMTAreas.A7Hi.lowpassVarGD1 Polynomial.X hX.ge ρ hρ hρ1 r hr p hp hptop Λ hΛ
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro k l₁ a ha ha1 f hgood hk
  have h := hb k l₁ a ha ha1 f hgood (by
    intro n
    have hn := hk n
    rw [hX]
    simpa using hn)
  simpa [Work.KMTAreas.A7.varphitildeN, Work.KMTAreas.A7.varphiN] using h

end

end Work.KMTAreas.A7Hi
