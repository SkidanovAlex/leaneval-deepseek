import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.OpZ_reserve` — the kinetic reserve of a single slot

FS `lem:EstimatesOnQ3-js` needs, for every low-momentum slot `s` of the
localisation `f_L`, the *kinetic* reserve domination

  `∑_{k ∈ P_H} 𝒟_{s-k}⟨b_{s-k}†b_{s-k}Φ, Φ⟩ ≤ ⟨Φ, (∑_{q ∈ P_H^q} 𝒟_q b_q†b_q) Φ⟩`,

i.e. the shifted `P_H`-sum `k ↦ s - k` is dominated by the quarter-region reserve
`∑_{q ∈ P_H^q} 𝒟_q b_q†b_q` of `eq:EstimateQ3Tilde2+3`.

The proof is purely geometric and positive:
* `k ↦ s - k` is injective (`sub_right_inj`), so the sum over `P_H` is the sum
  over the *image* (`Finset.sum_image`);
* the image is contained in the quarter region `P_H^q` (`PH_subset_PHq_sub`),
  and none of its elements is the condensate mode `0` (a `P_H^q`-mode has
  momentum `≥ ¼K_H⁻¹a⁻¹ > 0 = ‖kmom 0‖`);
* every term of the reserve is nonnegative: `𝒟_q ≥ 0` on `P_H^q`
  (`FockData.Dcoef_nonneg` from `Q3KernelFSAll.AB`) and
  `⟨b_q†b_qΦ, Φ⟩ = ‖b_qΦ‖² ≥ 0` (`bp_bNumOp_nonneg`),

so `Finset.sum_le_sum_of_subset_of_nonneg` finishes.

No `t₀` beyond the one that makes `s - k ∈ P_H^q` (namely `μa³ ≤ 4^{-24}`) is
needed: `b₀`, `K₀` do not enter the argument.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7

set_option linter.unusedVariables false

/-- `kmom 0 = 0`: the momentum assignment is odd, so the condensate mode carries
zero momentum.  Hence a mode of the quarter region `P_H^q` — whose momenta are
bounded below by `1/(4K_Ha) > 0` — is never the mode `0`. -/
lemma kmom_zero_opZ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) : F.kmom (0 : Mode) = 0 := by
  have h2 : F.kmom (0 : Mode) = -F.kmom (0 : Mode) := by
    simpa using F.kmom_neg (0 : Mode)
  have h : F.kmom (0 : Mode) + F.kmom (0 : Mode) = 0 := eq_neg_iff_add_eq_zero.mp h2
  have h3 : (2 : ℝ) • F.kmom (0 : Mode) = 0 := by
    rw [two_smul]
    exact h
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-- A sum over an injectively reindexed finset is at most the sum over a larger
finset, provided the reindexing lands in the larger finset and the terms are
nonnegative *there*. -/
lemma sum_le_sum_image_opZ {ι : Type*} [DecidableEq ι] {t u : Finset ι}
    {φ : ι → ι} (hφ : ∀ i j, φ i = φ j → i = j) (hsub : ∀ i ∈ t, φ i ∈ u)
    {f : ι → ℝ} (hf : ∀ i ∈ u, 0 ≤ f i) : ∑ i ∈ t, f (φ i) ≤ ∑ j ∈ u, f j := by
  rw [← Finset.sum_image (s := t) (g := φ) (f := f) (fun x _ y _ h => hφ x y h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) (fun q hq _ => hf q hq)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact hsub i hi

/-- The **guarded** version of `OpZ_reserve`: at the corrected gate the region
fact `s − k ∈ P_H^q` is available only under the guard `Ŵ₁ k ≠ 0`, so the
`k`-sum is taken over the modes of `P_H` *with* `Ŵ₁ k ≠ 0`.  This is the design's
rule; it costs nothing downstream because every summand that consumes this lemma
carries the factor `Ŵ₁(k)²`. -/
theorem OpZ_reserve (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ (s : Mode), E.fL s ≠ 0 → ∀ (Φ : F.H),
          ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
              E.D (s - k) * F.bp (F.bNumOp E.alpha (s - k) Φ) Φ
            ≤ F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  obtain ⟨t₁, ht₁, hP⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨t₁, ht₁, ?_⟩
  intro Mode _ _ _ F T E hv ht hb hK s hfL Φ
  obtain ⟨hPHq, hsubq, -⟩ := hP F T E hv ht hb hK
  -- every shifted slot `s - k` (with `Ŵ₁ k ≠ 0`) is an *excited* mode of the
  -- quarter region
  have hmem : ∀ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
      s - k ∈ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    obtain ⟨hkPH, hkW⟩ := Finset.mem_filter.mp hk
    have hq : F.PHq E.KH E.aScat (s - k) := hsubq s k hfL hkPH hkW
    refine Finset.mem_filter.mpr ⟨?_, hq⟩
    rw [excited, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h0
    have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
    have ha : 0 < E.aScat := hv.a_pos
    have h4 : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
    have h3 : (0 : ℝ) < ‖F.kmom (s - k)‖ := lt_of_lt_of_le h4 hq
    rw [h0, kmom_zero_opZ F, norm_zero] at h3
    exact absurd h3 (lt_irrefl 0)
  -- `𝒟 ≥ 0` on the quarter region (`Q3KernelFSAll.AB` gives `|ℬ| ≤ 𝒜`)
  have hDnn : ∀ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), 0 ≤ E.D q := by
    intro q _
    simpa only [Work.BoseB7.Q3Env.D] using FockData.Dcoef_nonneg (hK.AB q)
  -- the reindexing of the `k`-sum by `k ↦ s - k`
  have hstep : (∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          E.D (s - k) * F.bp (F.bNumOp E.alpha (s - k) Φ) Φ)
      ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.D q * F.bp (F.bNumOp E.alpha q Φ) Φ :=
    sum_le_sum_image_opZ (t := (F.PHset E).filter (fun k => E.W1 k ≠ 0))
      (u := (excited Mode).filter (F.PHq E.KH E.aScat))
      (φ := fun k => s - k) (fun i j hij => sub_right_inj.mp hij) hmem
      (fun q hq => mul_nonneg (hDnn q hq) (bp_bNumOp_nonneg F E.alpha q Φ))
  calc ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          E.D (s - k) * F.bp (F.bNumOp E.alpha (s - k) Φ) Φ
      ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.D q * F.bp (F.bNumOp E.alpha q Φ) Φ := hstep
    _ = F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
        rw [Work.BoseB7.FockData.qw, Work.BoseB7.bp_dNumOpR]

end Work.BoseC3QAll.Est1
