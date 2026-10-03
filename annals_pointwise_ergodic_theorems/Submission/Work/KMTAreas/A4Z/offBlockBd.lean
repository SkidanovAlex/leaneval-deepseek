/-
# The blockwise off-diagonal decay of `iw-prop`(i) with the explicit gain `2^{-8 d l}`

This module proves `Work.KMTAreas.A4Z.OffBlockBd` from the off-diagonal decay
`Work.KMTAreas.A4Z.OffDecayHyp` of Lemma `iw-prop`(i) of Krause--Mirek--Tao (the estimate
`(off-decay)`).

Recall the shape of the off-decay: for a function `f` supported in `[a,b]`, a window `[c,d]` with
`b < c` strictly to the right of the support, any exponent `q ∈ (1,∞)`, any order `M`, and on the
good major arcs `k ≤ -C_ρ(q,M) 2^{ρl}`,

`‖Π_{≤l,≤k} f‖_{ℓ^q([c,d])} ≤ C · ⟨l⟩ · max (2^k (c - b)) 1 ^ (-M) · ‖f‖_{ℓ^q}`.

Applying this with `q = 2`, `M = 8` to a function `ψ` supported in the window `suppWin P N i`
and to the block `I_m = [mL, (m+1)L)`, `L = N^{deg P}`, at distance `≳ |m - i| L` from the
support, the gain of the off-decay is

`max (2^k · (|m-i| - coeffSum P - 2) · L) 1 ^ (-8)`.

The key point of the present statement is the *sharp* form of the gain: with `k = d (l - Log N)`
we have `2^k · L ≥ 2^{d(l-1)}` (proved below as `twoPowKMulBlockLenGeSharp'`, a sharpening of
`two_pow_k_mul_blockLen_ge`, which only gives `2^{-d} ≤ 2^k L`), so the factor `2^{dl}` of the gain
is available, and the elementary inequality `1 + j ≤ (coeffSum P + 4) (j - coeffSum P - 2)`
(for `j ≥ coeffSum P + 3`) turns the gain into the constant-free product

`Koff · ⟨l⟩ · 2^{-8 d l} · (1 + |m - i|)^{-8}`

with `Koff` *independent of `l`* (the constant of the off-decay at `q = 2`, `M = 8`).  This is
the form consumed by the Schur summation in `pairingFarBd`.  This sharp form is what makes the
`2^{-c l}` decay of Corollary `siv-second` available; the coarser form
`Work.KMTAreas.A4Z.offDecayBlock` (with a constant depending on `l`) does not give it.

The block to the *left* of the window is handled by the mirrored off-decay (reflection of `ℤ`,
the kernel of `Π_{≤l,≤k}` being even, `kmtProj_reflect`); the statement `offDecay_left` is proved
here locally, mirroring `Work.KMTAreas.A4Z.offDecayBlock`, because the module
`Submission/Work/KMTAreas/A4Z/SivOffDecay.lean` carrying the same statement does not currently
compile.

The two arithmetic inputs are `Work.KMTAreas.A4Z.sharpGain` (the conversion of the off-decay gain
into `Koff · 2^{-8dl} (1+|m-i|)^{-8}` with a constant independent of `l`) and the sharpening above
of the scale comparison `2^k · L ≥ 2^{-d}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.SivOff
import Submission.Work.KMTAreas.A4Z.sharpGain

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-! ## Reflection of `ℤ` -/

/-- Negation on `ℤ` preserves the counting measure. -/
private lemma measurePreserving_neg_count :
    MeasurePreserving (fun x : ℤ => -x) (Measure.count : Measure ℤ)
      (Measure.count : Measure ℤ) := by
  refine MeasurePreserving.mk measurable_neg ?_
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  have hpre : (fun x : ℤ => -x) ⁻¹' s = Neg.neg '' s := by ext y; simp
  rw [hpre]
  exact Measure.count_injective_image neg_injective s

/-- Reflection of the argument preserves the `ℒᵖ`-seminorm against the counting measure on `ℤ`. -/
private lemma eLpNorm_comp_neg_count (u : ℤ → ℂ) (p : ENNReal) :
    eLpNorm (fun n : ℤ => u (-n)) p (Measure.count : Measure ℤ)
      = eLpNorm u p (Measure.count : Measure ℤ) :=
  eLpNorm_comp_measurePreserving (measurable_of_countable u).aestronglyMeasurable
    measurePreserving_neg_count

/-! ## The leftward form of the off-diagonal decay -/

/-- **The off-diagonal decay, mirrored**: for `f` supported in `[a,b]` and a window `[c,d]`
strictly to the *left* of the support (`d < a`), the projection `Π_{≤l,≤k} f` on that window decays
like `⟨2^k (a - d)⟩^{-M}`.  This is the reflection of `(off-decay)` under `x ↦ -x`, using that the
kernel of the Ionescu--Wainger projection is even (`kmtProj_reflect`). -/
private theorem offDecay_left (ρ : ℝ) (h : OffDecayHyp ρ) (M : ℕ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ B : NNReal, 0 < B ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
      ∀ (a b c d : ℤ) (f : ℤ → ℂ), MemLp f 2 (Measure.count : Measure ℤ) → d < a →
        (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
        eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
            2 (Measure.count : Measure ℤ)
          ≤ (B : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * ((a - d : ℤ) : ℝ)) 1) ^ (-(M : ℝ)))
            * eLpNorm f 2 (Measure.count : Measure ℤ) := by
  obtain ⟨Cρ, hCρ, B, hB, hoff⟩ := h 2 (by norm_num) M
  refine ⟨Cρ, hCρ, B, hB, ?_⟩
  intro l k hgood a b c d f hf hda hsupp
  have hsupp' : ∀ y : ℤ, y < -b ∨ -a < y → (fun y : ℤ => f (-y)) y = 0 := by
    intro y hy
    rcases hy with hy | hy
    · exact hsupp (-y) (Or.inr (by omega))
    · exact hsupp (-y) (Or.inl (by omega))
  have hmain := hoff l k hgood (-b) (-a) (-d) (-c) (fun y : ℤ => f (-y)) (by omega) hsupp'
  rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num] at hmain
  have hfacZ : (-d : ℤ) - (-a : ℤ) = a - d := by ring
  rw [hfacZ] at hmain
  have hfun : (fun y : ℤ => if -d ≤ y ∧ y ≤ -c then
        Work.KMTContract.kmtProj ρ l k (fun y : ℤ => f (-y)) y else 0)
      = (fun n : ℤ => (fun x : ℤ => if c ≤ x ∧ x ≤ d then
          Work.KMTContract.kmtProj ρ l k f x else 0) (-n)) := by
    funext y
    show (if -d ≤ y ∧ y ≤ -c then Work.KMTContract.kmtProj ρ l k (fun y : ℤ => f (-y)) y else 0)
      = (if c ≤ -y ∧ -y ≤ d then Work.KMTContract.kmtProj ρ l k f (-y) else 0)
    by_cases hc : -d ≤ y ∧ y ≤ -c
    · have hc' : c ≤ -y ∧ -y ≤ d := ⟨by omega, by omega⟩
      simp only [if_pos hc, if_pos hc']
      exact congrFun (Work.KMTAreas.A4.kmtProj_reflect ρ l k f hf) y
    · have hc' : ¬ (c ≤ -y ∧ -y ≤ d) := by
        rintro ⟨h1, h2⟩; exact hc ⟨by omega, by omega⟩
      simp only [if_neg hc, if_neg hc']
  rw [hfun] at hmain
  rw [eLpNorm_comp_neg_count (fun x : ℤ => if c ≤ x ∧ x ≤ d then
      Work.KMTContract.kmtProj ρ l k f x else 0) 2] at hmain
  rw [eLpNorm_comp_neg_count f 2] at hmain
  exact hmain

/-- `GoodMajorArcs` is monotone in the constant: a larger constant makes the hypothesis
`k ≤ -C 2^{ρl}` stronger. -/
private theorem goodMajorArcs_mono_const {ρ C C' : ℝ} (h : C ≤ C') {l : ℕ} {k : ℤ}
    (hk : GoodMajorArcs ρ C' l k) : GoodMajorArcs ρ C l k := by
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hle : C * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ C' * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    mul_le_mul_of_nonneg_right h hpow
  show (k : ℝ) ≤ -C * (2 : ℝ) ^ (ρ * (l : ℝ))
  have hk' : (k : ℝ) ≤ -C' * (2 : ℝ) ^ (ρ * (l : ℝ)) := hk
  linarith

/-- **The sharp relation between the height scale `2^k` and the block length**:
for `k = d (l - Log N)` (with `d = deg P`, `L = N^d = blockLen P N`), one has
`2^{d(l-1)} ≤ 2^k · L`.

Indeed `2^k L = (2^{l - Log N} N)^d`, and `2^{Log N} ≤ 2N` gives `2^{l - Log N} N ≥ 2^{l-1}`.
This is the refinement of `two_pow_k_mul_blockLen_ge` (which gives only `2^{-d} ≤ 2^k L`) that
makes the gain `2^{-8dl}` of `OffBlockBd` available. -/
private theorem twoPowKMulBlockLenGeSharp' (P : Polynomial ℤ) {N l : ℕ} (hN : 1 ≤ N) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - 1))
      ≤ (2 : ℝ) ^ ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
          * (blockLen P N : ℝ) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hgpos : (0 : ℝ) < (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ) :=
    Real.rpow_pos_of_pos h2pos _
  have hg2 : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ) ≤ 2 * (N : ℝ) := by
    rw [Real.rpow_intCast (2 : ℝ) (Work.Analysis.EndVar.logN N)]
    exact Work.KMTAreas.A4.two_pow_logN_le hN
  have hbase : (2 : ℝ) ^ ((l : ℝ) - 1)
      ≤ (2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ) := by
    have hle : (1 : ℝ) / 2 ≤ (N : ℝ) / (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ) := by
      rw [le_div_iff₀ hgpos]
      linarith
    calc (2 : ℝ) ^ ((l : ℝ) - 1) = (2 : ℝ) ^ ((l : ℝ)) * (1 / 2) := by
          rw [Real.rpow_sub h2pos, Real.rpow_one]; ring
      _ ≤ (2 : ℝ) ^ ((l : ℝ))
            * ((N : ℝ) / (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ) := by
          rw [Real.rpow_sub h2pos]; ring
  have hLn : (blockLen P N : ℝ) = (N : ℝ) ^ (P.natDegree : ℝ) := by
    rw [blockLen]
    push_cast
    exact (Real.rpow_natCast (N : ℝ) P.natDegree).symm
  have hstep : ((2 : ℝ) ^ ((l : ℝ) - 1)) ^ (P.natDegree : ℝ)
      ≤ ((2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ))
          ^ (P.natDegree : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase (Nat.cast_nonneg _)
  have h1 : ((2 : ℝ) ^ ((l : ℝ) - 1)) ^ (P.natDegree : ℝ)
      = (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - 1)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h2 : ((2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ))
          ^ (P.natDegree : ℝ)
      = (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
          * (blockLen P N : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (le_of_lt hNpos),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← hLn]
    have : ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (P.natDegree : ℝ)
        = (P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by ring
    rw [this]
  have h3 : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
      = (2 : ℝ) ^ ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) := by
    have hcast : (P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        = (((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hcast,
      Real.rpow_intCast (2 : ℝ) ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))]
  calc (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - 1))
      = ((2 : ℝ) ^ ((l : ℝ) - 1)) ^ (P.natDegree : ℝ) := h1.symm
    _ ≤ ((2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ))
          ^ (P.natDegree : ℝ) := hstep
    _ = (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
          * (blockLen P N : ℝ) := h2
    _ = (2 : ℝ) ^ ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
          * (blockLen P N : ℝ) := by rw [h3]

/-- A real multiple of an `NNReal`, pulled under `ENNReal.ofReal`. -/
private lemma nnreal_mul_ofReal (C : NNReal) (X : ℝ) :
    (C : ENNReal) * ENNReal.ofReal X = ENNReal.ofReal ((C : ℝ) * X) := by
  rw [← ENNReal.ofReal_coe_nnreal (p := C), ← ENNReal.ofReal_mul (by positivity)]

/-! ## The main result -/

theorem offBlockBd (P : Polynomial ℤ) (ρ : ℝ) (hOff : Work.KMTAreas.A4Z.OffDecayHyp ρ) :
    ∃ Cρ₀ : ℝ, 0 < Cρ₀ ∧ ∃ Koff : ℝ, 0 < Koff ∧
      Work.KMTAreas.A4Z.OffBlockBd P ρ Cρ₀ Koff := by
  obtain ⟨CρR, hCρRpos, C, hCpos, hoffR⟩ := hOff 2 (by norm_num) 8
  obtain ⟨CρL, hCρLpos, B, hBpos, hoffL⟩ := offDecay_left ρ hOff 8
  have hCposR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos
  have hBposR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
  have hcreal : (0 : ℝ) ≤ (coeffSum P : ℝ) := by
    have h : (0 : ℤ) ≤ coeffSum P := by
      rw [coeffSum]
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (P.coeff j))
    exact_mod_cast h
  have hK0pos : (0 : ℝ) < (2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4) := by
    have h4 : (0 : ℝ) < (coeffSum P : ℝ) + 4 := by linarith
    positivity
  refine ⟨max CρR CρL, lt_max_of_lt_left hCρRpos,
    ((C : ℝ) + (B : ℝ)) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (C : ℝ) + (B : ℝ) := by linarith
    exact mul_pos h1 (pow_pos hK0pos 8)
  · intro N l Cρ hN hCρle hgood i m ψ hψ hsupp hmi
    set k : ℤ := (P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N) with hkdef
    have hgoodR : GoodMajorArcs ρ CρR l k :=
      goodMajorArcs_mono_const (le_trans (le_max_left _ _) hCρle) hgood
    have hgoodL : GoodMajorArcs ρ CρL l k :=
      goodMajorArcs_mono_const (le_trans (le_max_right _ _) hCρle) hgood
    have hL1 : (1 : ℤ) ≤ blockLen P N := by
      rw [blockLen]
      exact_mod_cast (Nat.one_le_pow P.natDegree N (by omega))
    have hLpos : (0 : ℤ) < blockLen P N := by omega
    have h2pow : (1 : ℤ) ≤ 2 ^ P.natDegree := by
      have h := Nat.one_le_pow P.natDegree 2 (by norm_num : 1 ≤ (2 : ℕ))
      exact_mod_cast h
    have hfun : (fun x : ℤ => if x ∈ Finset.Ico (m * blockLen P N)
          ((m + 1) * blockLen P N) then
            Work.KMTContract.kmtProj ρ l k ψ x else 0)
        = (fun x : ℤ => if m * blockLen P N ≤ x ∧ x ≤ (m + 1) * blockLen P N - 1
            then Work.KMTContract.kmtProj ρ l k ψ x else 0) := by
      funext x
      simp only [Finset.mem_Ico]
      by_cases hx : m * blockLen P N ≤ x ∧ x < (m + 1) * blockLen P N
      · rw [if_pos hx, if_pos ⟨hx.1, by omega⟩]
      · rw [if_neg hx, if_neg (fun h => hx ⟨h.1, by omega⟩)]
    have hsupp' : ∀ x : ℤ, x < i * blockLen P N - shiftBd P N ∨
        (i + 1) * blockLen P N + shiftBd P N < x → ψ x = 0 := by
      intro x hx
      refine hsupp x ?_
      intro hmem
      simp only [suppWin, Set.mem_Icc] at hmem
      rcases hx with hx | hx <;> omega
    -- the arithmetic scale comparison `2^{d(l-1)} ≤ 2^k L`
    have hscale : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - 1))
        ≤ (2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ) := by
      have h := twoPowKMulBlockLenGeSharp' (N := N) (l := l) P hN
      rwa [← hkdef] at h
    -- the bound `coeffSum P + 3 ≤ |m - i|`, in `ℝ`
    have hjreal : (coeffSum P : ℝ) + 3 ≤ |(((m - i : ℤ) : ℝ))| := by
      rw [← Int.cast_abs]
      exact_mod_cast (by omega : coeffSum P + 3 ≤ |(m - i : ℤ)|)
    by_cases hi : i ≤ m
    · -- the block `I_m` is to the right of the window `suppWin P N i`
      have hmj : coeffSum P + 3 ≤ m - i := by
        have habs : |(m - i : ℤ)| = m - i := abs_of_nonneg (by omega)
        rw [← habs]
        omega
      have hbc : (i + 1) * blockLen P N + shiftBd P N < m * blockLen P N := by
        have h1 : i + 1 + (coeffSum P + 1) < m := by omega
        calc (i + 1) * blockLen P N + shiftBd P N
            = (i + 1 + (coeffSum P + 1)) * blockLen P N := by rw [shiftBd]; ring
          _ < m * blockLen P N := Int.mul_lt_mul_of_pos_right h1 hLpos
      have hmain := hoffR l k hgoodR (i * blockLen P N - shiftBd P N)
        ((i + 1) * blockLen P N + shiftBd P N) (m * blockLen P N)
        ((m + 1) * blockLen P N - 1) ψ hbc hsupp'
      rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num] at hmain
      -- the gap identity: `gapR = (|m - i| - coeffSum P - 2) * L`
      have hgapR : (((m * blockLen P N - ((i + 1) * blockLen P N
            + shiftBd P N)) : ℤ) : ℝ)
          = (((m - i : ℤ) : ℝ) - (coeffSum P : ℝ) - 2) * ((blockLen P N : ℤ) : ℝ) := by
        rw [shiftBd]; push_cast; ring
      have hbeq : (((m - i : ℤ) : ℝ)) = |(((m - i : ℤ) : ℝ))| := by
        rw [abs_of_nonneg]
        exact_mod_cast (by omega : (0 : ℤ) ≤ m - i)
      have hA : ((2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
            * (|(((m - i : ℤ) : ℝ))| - (coeffSum P : ℝ) - 2)
          ≤ max ((2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
              + shiftBd P N)) : ℤ) : ℝ)) 1 := by
        have h1 : ((2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
              * (|(((m - i : ℤ) : ℝ))| - (coeffSum P : ℝ) - 2)
            = (2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
                + shiftBd P N)) : ℤ) : ℝ) := by
          rw [hgapR, ← hbeq]; ring
        rw [h1]
        exact le_max_left _ _
      have hsharp : (max ((2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
              + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ))
          ≤ (2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
              * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
              * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
        sharpGain (d := P.natDegree) (l := l)
          (s := (2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
          (c := (coeffSum P : ℝ)) (j := |(((m - i : ℤ) : ℝ))|)
          (A := max ((2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
              + shiftBd P N)) : ℤ) : ℝ)) 1) hcreal hjreal hscale hA
      rw [hfun]
      calc eLpNorm (fun x : ℤ => if m * blockLen P N ≤ x ∧ x ≤ (m + 1) * blockLen P N - 1
              then Work.KMTContract.kmtProj ρ l k ψ x else 0) 2 Measure.count
          ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
                  + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)))
              * eLpNorm ψ 2 Measure.count := hmain
        _ = ENNReal.ofReal ((C : ℝ) * (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * (((m * blockLen P N - ((i + 1) * blockLen P N
                  + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ))))
              * eLpNorm ψ 2 Measure.count := by rw [nnreal_mul_ofReal]
        _ ≤ ENNReal.ofReal (((C : ℝ) + (B : ℝ))
              * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
              * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
              * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
              * eLpNorm ψ 2 Measure.count := by
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
            have hA0 : (0 : ℝ) ≤ max ((2 : ℝ) ^ k * (((m * blockLen P N
                - ((i + 1) * blockLen P N + shiftBd P N)) : ℤ) : ℝ)) 1 :=
              le_trans zero_le_one (le_max_right _ _)
            have hAnn : (0 : ℝ) ≤ (max ((2 : ℝ) ^ k * (((m * blockLen P N
                - ((i + 1) * blockLen P N + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)) :=
              Real.rpow_nonneg hA0 _
            have hmaxnn : (0 : ℝ) ≤ max ((l : ℝ)) 1 :=
              le_trans zero_le_one (le_max_right ((l : ℝ)) 1)
            have hCnn : (0 : ℝ) ≤ (C : ℝ) := le_of_lt hCposR
            have hK0nn : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4) :=
              le_of_lt hK0pos
            have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ))) :=
              Real.rpow_nonneg (by norm_num) _
            have h1jnn : (0 : ℝ) ≤ (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
              Real.rpow_nonneg (by linarith [abs_nonneg (((m - i : ℤ) : ℝ))]) _
            have hCBB : (C : ℝ) ≤ (C : ℝ) + (B : ℝ) := by linarith
            calc (C : ℝ) * (max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * (((m * blockLen P N
                    - ((i + 1) * blockLen P N + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)))
                = (C : ℝ) * max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * (((m * blockLen P N
                    - ((i + 1) * blockLen P N + shiftBd P N)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)) := by
                  ring
              _ ≤ (C : ℝ) * max ((l : ℝ)) 1
                    * ((2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                      * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                      * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hsharp (mul_nonneg hCnn hmaxnn)
              _ ≤ ((C : ℝ) + (B : ℝ)) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                    * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                    * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by
                  have h1 : (C : ℝ) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                        * max ((l : ℝ)) 1
                      ≤ ((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1 :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hCBB (pow_nonneg hK0nn 8)) hmaxnn
                  calc (C : ℝ) * max ((l : ℝ)) 1
                        * ((2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
                      = ((C : ℝ) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1)
                        * ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by ring
                    _ ≤ (((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1)
                        * ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
                        mul_le_mul_of_nonneg_right h1 (mul_nonneg h2nn h1jnn)
                    _ = ((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by ring
    · -- the block `I_m` is to the left of the window `suppWin P N i`
      have hlt : m < i := not_le.mp hi
      have hmj : coeffSum P + 3 ≤ i - m := by
        have habs : |(m - i : ℤ)| = i - m := by
          rw [abs_of_nonpos (by omega : (m - i : ℤ) ≤ 0)]
          omega
        rw [← habs]
        omega
      have hda : (m + 1) * blockLen P N - 1 < i * blockLen P N - shiftBd P N := by
        have h1 : m + 1 + (coeffSum P + 1) ≤ i := by omega
        have h2 : (m + 1) * blockLen P N + (coeffSum P + 1) * blockLen P N
            ≤ i * blockLen P N := by
          calc (m + 1) * blockLen P N + (coeffSum P + 1) * blockLen P N
              = (m + 1 + (coeffSum P + 1)) * blockLen P N := by ring
            _ ≤ i * blockLen P N := Int.mul_le_mul_of_nonneg_right h1 hLpos.le
        rw [shiftBd]
        omega
      have hmain := hoffL l k hgoodL (i * blockLen P N - shiftBd P N)
        ((i + 1) * blockLen P N + shiftBd P N) (m * blockLen P N)
        ((m + 1) * blockLen P N - 1) ψ hψ hda hsupp'
      rw [show (-((8 : ℕ) : ℝ)) = (-(8 : ℝ)) from by norm_num] at hmain
      -- the gap identity: `gapL = (|m - i| - coeffSum P - 2) * L + 1`
      have hgapL : ((((i * blockLen P N - shiftBd P N)
            - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)
          = (((i - m : ℤ) : ℝ) - (coeffSum P : ℝ) - 2) * ((blockLen P N : ℤ) : ℝ) + 1 := by
        rw [shiftBd]; push_cast; ring
      have hbeq : (((m - i : ℤ) : ℝ)) = -(((i - m : ℤ) : ℝ)) := by push_cast; ring
      have hA : ((2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
            * (|(((m - i : ℤ) : ℝ))| - (coeffSum P : ℝ) - 2)
          ≤ max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
              - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1 := by
        have hpow : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
        have habs2 : |(((i - m : ℤ) : ℝ))| = (((i - m : ℤ) : ℝ)) :=
          abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ i - m))
        have h1 : ((2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
              * (|(((m - i : ℤ) : ℝ))| - (coeffSum P : ℝ) - 2)
            = (2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
                - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ) - (2 : ℝ) ^ k := by
          rw [hgapL, hbeq, abs_neg, habs2]; ring
        rw [h1]
        have h2 : (2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
              - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ) - (2 : ℝ) ^ k
            ≤ (2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
              - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ) := by linarith
        exact le_trans h2 (le_max_left _ _)
      have hsharp : (max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
              - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ))
          ≤ (2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
              * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
              * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
        sharpGain (d := P.natDegree) (l := l)
          (s := (2 : ℝ) ^ k * ((blockLen P N : ℤ) : ℝ))
          (c := (coeffSum P : ℝ)) (j := |(((m - i : ℤ) : ℝ))|)
          (A := max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
              - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) hcreal hjreal hscale hA
      rw [hfun]
      calc eLpNorm (fun x : ℤ => if m * blockLen P N ≤ x ∧ x ≤ (m + 1) * blockLen P N - 1
              then Work.KMTContract.kmtProj ρ l k ψ x else 0) 2 Measure.count
          ≤ (B : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
                  - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)))
              * eLpNorm ψ 2 Measure.count := hmain
        _ = ENNReal.ofReal ((B : ℝ) * (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
                  - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ))))
              * eLpNorm ψ 2 Measure.count := by rw [nnreal_mul_ofReal]
        _ ≤ ENNReal.ofReal (((C : ℝ) + (B : ℝ))
              * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
              * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
              * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
              * eLpNorm ψ 2 Measure.count := by
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
            have hA0 : (0 : ℝ) ≤ max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
                - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1 :=
              le_trans zero_le_one (le_max_right _ _)
            have hAnn : (0 : ℝ) ≤ (max ((2 : ℝ) ^ k * ((((i * blockLen P N - shiftBd P N)
                - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)) :=
              Real.rpow_nonneg hA0 _
            have hmaxnn : (0 : ℝ) ≤ max ((l : ℝ)) 1 :=
              le_trans zero_le_one (le_max_right ((l : ℝ)) 1)
            have hBnn : (0 : ℝ) ≤ (B : ℝ) := le_of_lt hBposR
            have hK0nn : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4) :=
              le_of_lt hK0pos
            have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ))) :=
              Real.rpow_nonneg (by norm_num) _
            have h1jnn : (0 : ℝ) ≤ (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
              Real.rpow_nonneg (by linarith [abs_nonneg (((m - i : ℤ) : ℝ))]) _
            have hBCB : (B : ℝ) ≤ (C : ℝ) + (B : ℝ) := by linarith
            calc (B : ℝ) * (max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * ((((i * blockLen P N
                    - shiftBd P N) - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)))
                = (B : ℝ) * max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * ((((i * blockLen P N
                    - shiftBd P N) - ((m + 1) * blockLen P N - 1)) : ℤ) : ℝ)) 1) ^ (-(8 : ℝ)) := by
                  ring
              _ ≤ (B : ℝ) * max ((l : ℝ)) 1
                    * ((2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                      * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                      * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hsharp (mul_nonneg hBnn hmaxnn)
              _ ≤ ((C : ℝ) + (B : ℝ)) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                    * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                    * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by
                  have h1 : (B : ℝ) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                        * max ((l : ℝ)) 1
                      ≤ ((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1 :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hBCB (pow_nonneg hK0nn 8)) hmaxnn
                  calc (B : ℝ) * max ((l : ℝ)) 1
                        * ((2 ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
                      = ((B : ℝ) * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1)
                        * ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by ring
                    _ ≤ (((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1)
                        * ((2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
                        mul_le_mul_of_nonneg_right h1 (mul_nonneg h2nn h1jnn)
                    _ = ((C : ℝ) + (B : ℝ))
                          * ((2 : ℝ) ^ P.natDegree * ((coeffSum P : ℝ) + 4)) ^ 8
                          * max ((l : ℝ)) 1 * (2 : ℝ) ^ (-(8 * (P.natDegree : ℝ) * (l : ℝ)))
                          * (1 + |(((m - i : ℤ) : ℝ))|) ^ (-(8 : ℝ)) := by ring

end Work.KMTAreas.A4Z
