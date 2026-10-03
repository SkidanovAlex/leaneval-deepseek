/-
# The `B`-variant of the operator-level integration-by-parts identity (ii) of §6 (area A6)

This module proves `Work.KMTPlan.A6.MdlDecayLowHighB`, the *family-level* form of the
integration-by-parts identity (ii) of Krause--Mirek--Tao §6 at the pair `(0, k₂)` with `k₂ ≥ 1`:

```
mdlPartJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0
  = (mdlScale P k₂) mdlIota (sliceW(j₁=0,j₂=-1, w=W₁, t=1) − sliceW(..., t=1/2))
    − (mdlScaleGe P 0 k₂) · WInt(j₁=1, j₂=-1, w = W₁)
    + (mdlScale P k₂) mdlIota · WInt(j₁=0, j₂=-1, w = W₂)
```

It is the companion of `Work.KMTPlan.A6.MdlDecayLowHigh` (`Submission/Work/KMTPlan/A6/
MdlDecayLowHigh.lean`), of which it is a strict generalisation: the initial bounds on `f` and `g`
are the general `Complex.normSq (f x) ≤ Cf`, `Complex.normSq (g x) ≤ Cg` (instead of `≤ 1`), and
the non-singularity hypothesis `P'(⌊a n⌋ t) ≠ 0` on `[1/2,1]` is assumed only for the admissible
indices `n` (`mdlCore`), where it is actually needed — namely to make the two weights
`W₁ = N^{d-1}/P'(Nt)` and `W₂ = N^d P''(Nt)/P'(Nt)²` well defined and bounded on `[1/2,1]`.
This is the form in which the `k`-decay is consumed by the assembly of Case B
(`max k > max l`) of `Submission/Work/KMTPlan/A6/LowModelGainEstimate.lean`, where the model inputs
carry no normalisation.

The *mathematical content* (the frozen-`N` identity, i.e. the transfer of the bump-level identity
(ii) through the twisted bilinear multiplier `Btwist` via the kernel-level form
`MdlKerIdentLowHigh` and the flat `(p,z)`-sum calculus of `MdlLowHighFlat.lean`) is the sibling
lemma `Work.KMTPlan.A6.mdlDecayLowHigh_core` of `Submission/Work/KMTPlan/A6/MdlDecayLowHigh.lean`,
which is stated for arbitrary bounded families `F`, `G` and is therefore already the general form
needed here; this module (i) generalises the boundedness input of the model tuple from
`normSq ≤ 1` to `normSq ≤ Cf` (the auxiliary lemma `piExact_bounded_of_normSq` below) and (ii) runs
the case split on the core condition, peeling off for each `n` on the core the four kernel
packages, the two weight bounds and the two measurability facts.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayLowHigh

set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The exact-height projection of a `normSq`-bounded sequence is bounded -/

/-- The exact-height projection `piExact (kmtPj ρ) l k f` of a sequence whose squared modulus is
bounded by `Cf` is bounded.  (The `ℓ¹`-kernel argument of `MdlLowHighAux.mdl_mdlF_bounded`, with
the fixed hypothesis `Complex.normSq ≤ 1` replaced by `Complex.normSq ≤ Cf`; for `Cf < 0` the
hypothesis forces `f = 0`.) -/
theorem piExact_bounded_of_normSq (ρ : ℝ) (l : ℕ) (k : ℤ) {f : ℤ → ℂ} {Cf : ℝ}
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ Cf) :
    ∃ C : ℝ, ∀ y : ℤ,
      ‖Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f y‖ ≤ C := by
  have hbd : ∀ x : ℤ, ‖f x‖ ≤ max (Real.sqrt Cf) 0 := by
    intro x
    have h2 : ‖f x‖ ^ 2 ≤ Cf := by rw [← Complex.normSq_eq_norm_sq]; exact hf x
    rcases le_or_gt 0 Cf with hCf | hCf
    · exact le_trans ((Real.le_sqrt (norm_nonneg _) hCf).mpr h2) (le_max_left _ _)
    · have hzero : ‖f x‖ = 0 := by
        by_contra h
        have hpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
        nlinarith
      rw [hzero]
      exact le_max_right _ _
  have hbz : Work.KMTAreas.A5.BoundedZ f := ⟨max (Real.sqrt Cf) 0, hbd⟩
  refine ⟨(∑' j : ℤ, ‖Work.KMTAreas.A7.exactKer ρ l k j‖) * max (max (Real.sqrt Cf) 0) 0,
    fun y => ?_⟩
  rw [Work.A7.piExact_eq_convOp ρ l k hbz]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le (mdl_summable_exactKer_norm ρ l k) hbd y

/-! ## The family form of the identity (the target) -/

theorem MdlDecayLowHighB (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₂ : ℕ) (hk₂ : 1 ≤ k₂) (Cf Cg : ℝ)
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ Cf)
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ Cg)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n))
    (hP : ∀ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n →
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
        Work.KMTPlan.A6.PderivR P ((Nat.floor (a n) : ℝ) * t) ≠ 0) :
    Work.KMTPlan.A6.mdlPartJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0
      = fun n x => (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                  (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) 1 n x
              - Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                  (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) (1 / 2) n x)
        - (Work.KMTPlan.A6.mdlScaleGe P 0 k₂ : ℂ)
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1)
                (fun n t => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) n x
        + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
                (fun n t => Work.KMTPlan.A6.mdlW2 P (Nat.floor (a n)) t) n x := by
  funext n x
  by_cases hcore : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
  · -- the boundedness of the two model inputs, from the `normSq`-bounds
    obtain ⟨CF, hCF⟩ := piExact_bounded_of_normSq ρ l₁
      (-((uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ)) hf
    obtain ⟨CG, hCG⟩ := piExact_bounded_of_normSq ρ l₂
      (-(((P.natDegree : ℤ) * ((uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ)))) hg
    -- the two weight bounds, from the non-singularity hypothesis on the core
    obtain ⟨Cw₁, hCw₁0, hw₁⟩ := mdl_W1_bound P (Nat.floor (a n)) (hP n hcore)
    obtain ⟨Cw₂, hCw₂0, hw₂⟩ := mdl_W2_bound P (Nat.floor (a n)) (hP n hcore)
    have hwm₁ : AEStronglyMeasurable (fun t : ℝ => mdlW1 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW1 P (Nat.floor (a n))).aestronglyMeasurable
    have hwm₂ : AEStronglyMeasurable (fun t : ℝ => mdlW2 P (Nat.floor (a n)) t) volume :=
      (measurable_mdlW2 P (Nat.floor (a n))).aestronglyMeasurable
    -- the kernel of the window `m_* = mStarF u ⊗ mStargF (natDegree P) u` is in `ℓ¹(ℤ²)`
    have hK : Summable fun p : ℤ × ℤ =>
        ‖mdlBtwK ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max 0 k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max 0 k₂)))) p.1 p.2‖ :=
      mdl_summable_mdlBtwK_mStarF ρ P l₁ l₂ (uScale ρ (max (max l₁ l₂) (max 0 k₂)))
    -- the four kernel packages of the two bumps and their two modifications
    obtain ⟨a₁, ha₁, hb₁, hm₁⟩ := MdlKerVarphiNt ρ l₁ (Nat.floor (a n)) 0
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ := MdlKerVarphitildeNt ρ l₂ P.natDegree (Nat.floor (a n)) k₂ P
    obtain ⟨_, a₃, ha₃, hb₃, hm₃⟩ := mdlKerVarphiNtjOne ρ l₁ (Nat.floor (a n)) 0
    obtain ⟨_, a₄, ha₄, hb₄, hm₄⟩ := mdlKerVarphitildeNtjNeg ρ l₂ P (Nat.floor (a n)) k₂ hk₂
    have hF : ∀ y : ℤ, ‖mdlF ρ (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f y‖ ≤ CF := by
      intro y; simpa only [mdlF] using hCF y
    have hG : ∀ y : ℤ, ‖mdlG ρ P (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₂ g y‖ ≤ CG := by
      intro y; simpa only [mdlG] using hCG y
    rw [mdlPartJ, if_pos hcore]
    simp only [mdlSliceW, mdlWInt, if_pos hcore]
    exact mdlDecayLowHigh_core ρ P l₁ l₂ (Nat.floor (a n)) k₂ hk₂ (hN n)
      (uScale ρ (max (max l₁ l₂) (max 0 k₂)))
      (mdlF ρ (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
      (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₂ g)
      CF CG Cw₁ Cw₂ hF hG hCw₁0 hw₁ hwm₁ hCw₂0 hw₂ hwm₂ (hP n hcore) hK
      a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hb₄
      (fun i => (hm₁ i).aestronglyMeasurable) (fun i => (hm₂ i).aestronglyMeasurable)
      (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
  · rw [mdlPartJ, if_neg hcore]
    simp only [mdlSliceW, mdlWInt, if_neg hcore]
    ring

end

end Work.KMTPlan.A6
