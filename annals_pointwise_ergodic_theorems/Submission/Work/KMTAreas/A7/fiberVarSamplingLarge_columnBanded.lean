import Mathlib
import Submission.Work.KMTAreas.A7Hi.PacketRotationResidueBoundQuarter
import Submission.Work.KMTAreas.A7.fibreVarSampling_of_bandLimited
import Submission.Work.KMTAreas.A7Hi.FiberOpCutFixGeneral
import Submission.Work.KMTAreas.A7Hi.NonAliasingMono

/-!
# `fiberVarSamplingLarge_columnBanded` — session findings and the reduction to `PacketSep`

See `NOTES_A7_fiberVarSamplingLarge_columnBanded_SESSION.md` for the full account.  Summary:

* The target is `Work.KMTAreas.A7.fiberVarSamplingLarge` (the large-`L` fibre variational
  estimate) with one extra hypothesis (5): the columns
  `w n = if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0` are `ℓ²` and band-limited to the
  **plateau** arcs `⋃_{α ∈ iwArithFreqsNew ρ l₁} arcSet α (2^{-(2U)-1})` of `mStarF U`,
  `U = uScale ρ (max (max l₁ l₂) (max k₁ k₂))`.
* Hypothesis (5) makes the fibre at the residue `n₀` *exactly* the phased synthesis of the
  `mStarF U`-windows (the `A7Hi`/`A7Rep` window identities, PROVED), and makes the windows `ℓ²`
  and band-`δ` (`δ := 2^{-(2U)-1}`, the two-radius lemma
  `A7.windowEnvelopesHasFreqSupport_twoRadius`, PROVED — its separation hypothesis
  `2^{-2U} + δ < ‖α-β‖` is supplied by the target's `NonAliasing`).  The synthesis identity
  `∑_α window_α = w n` is the range identity, available from hypothesis (5) (the `2ε`-separation
  form of `A7Hi.FiberOpCutFixGeneral`/`plateau_mul_of_sep_four`, where `ε` is the *plateau*
  radius — this is why the hypothesis is stated at the plateau radius and not at the support
  radius).
* Therefore the target reduces to `PacketSep` below: the packet-rotation residue bound of
  `A7Hi.PacketRotationResidueBoundQuarter` (PROVED, `δq ≤ 1/4`) with that lattice hypothesis
  replaced by the non-aliasing hypothesis of the target.  The replacement is strictly stronger:
  non-aliasing gives only `4δ < d_min`, and the *effective* modulus of the residue average is the
  lcm of the orders of the new frequencies, which can be vastly bigger than `1/δ` (concrete
  regime `ρ = 1/100`, `l₁ = l₂ = k₁ = k₂ = 10^4`: `arithQ ρ l₁ = 2^{1.44·2^{10^4}}` while
  `2^{2U} = 2^{2^{201}}`), so `δ q ≫ 1/4` is compatible with all the hypotheses.  Making the
  crux true in that "no-Nyquist" regime is the open problem recorded in the notes (§4); the
  numerics there support it.

Proved in this file: `windowEnvelopes_memLp_band_of_column` (the windows of a band-limited `ℓ²`
column are `ℓ²` and band-`2^{-(2U)-1}`).  **The target itself is not proved**; its `sorry` is still
present and documented, and the reduction to `PacketSep` needs additionally the *range identity at
the plateau constant* (the workspace's `fiberOp_zero_eq_self_of_hasFreqSupport` asks for the
separation `4 * 2^{-2U} ≤ ‖α-β‖`, twice what `NonAliasing (-(2U))` gives; the correct constant is
`4 * 2^{-(2U)-1}`, which `NonAliasing` does give) plus the window/synthesis identities — see
`NOTES_A7_fiberVarSamplingLarge_columnBanded_SESSION.md` §8.
-/

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The packet-rotation residue bound under the non-aliasing hypothesis** (the crux of the
target; `A7Hi.PacketRotationResidueBoundQuarter` with `δ * q ≤ 1 / 4` replaced by
`NonAliasing (-(2U)) (iwArithFreqs ρ l₁)`). -/
def PacketSep : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ℝ), 1 < p → ∀ (r : NNReal), 2 < r →
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ U q : ℕ) (hq : 0 < q)
        (hA : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, q • α = 0)
        (hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
        (f : ℕ → Circ → ℤ → ℂ)
        (hbd : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ →
          ∃ hh : Memℓp (f n α) 2,
            Work.BourgainPlan.IonescuWainger.HasFreqSupport (f n α) hh
              (Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)))),
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p q (fun y n₀ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7Hi.winRot
                  (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) (f n) (n₀ : ℤ) y)) x)
            (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7Hi.winSynth
                (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) (f n) x))
            (ENNReal.ofReal p) MeasureTheory.Measure.count


/-- **The `mStarF U`-windows of a band-limited `ℓ²` column are `ℓ²` and band-`δ`**, with
`δ = 2^{-(2U)-1}`: the two-radius window lemma `A7.windowEnvelopesHasFreqSupport_twoRadius` with
the `m`-radius `2^{-2U}`, input radius `δ` and output radius `δ`.  Its separation hypothesis
`2^{-2U} + δ < ‖α - β‖` is exactly what `NonAliasing (-(2 * U))` supplies. -/
theorem windowEnvelopes_memLp_band_of_column (ρ : ℝ) (l₁ U : ℕ)
    (hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (u : ℤ → ℂ) (hu : Memℓp u 2)
    (huE : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
        Work.BourgainPlan.IonescuWainger.arcSet α ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)))) :
    ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
      ∃ hh : Memℓp (Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) u α) 2,
        Work.BourgainPlan.IonescuWainger.HasFreqSupport
          (Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) u α) hh
          (Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1))) := by
  intro α hα
  have hsep : ∀ α' ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, α' ≠ β →
      (2 : ℝ) ^ (-(2 * (U : ℤ))) + (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) < ‖α' - β‖ := by
    intro α' hα' β hβ hne
    have h1 : α' ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ :=
      Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα'
    have h2 : β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ :=
      Work.KMTAreas.A7.mem_iwArithFreqsNew_le hβ
    have hsep' : (2 : ℝ) ^ (-(2 * (U : ℤ)) + 1) < ‖α' - β‖ :=
      Work.KMTAreas.A7Hi.nonAliasing_separation hna h1 h2 hne
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
    have h3 : (2 : ℝ) ^ (-(2 * (U : ℤ)) + 1) = 2 * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
    have h4 : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) = (2 : ℝ) ^ (-(2 * (U : ℤ))) / 2 := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    rw [h3] at hsep'
    have hgoal : (2 : ℝ) ^ (-(2 * (U : ℤ))) + (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)
        < 2 * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
      rw [h4]; linarith
    linarith [hgoal, hsep']
  obtain ⟨hh, hsup⟩ := Work.KMTAreas.A7.windowEnvelopesHasFreqSupport_twoRadius (mStarF U)
    (kmt_integrable_mStarF U) (summable_cw_mStarF U)
    ((2 : ℝ) ^ (-(2 * (U : ℤ)))) ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1))
    ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) le_rfl
    (fun θ hθ => periodize_mStarF_mem_arcSet (U := U) hθ)
    (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) hsep u hu huE α hα
  have heq : Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) u α
      = Work.KMTAreas.A7Rep.winConvRep (mStarF U)
          (Work.KMTAreas.A7Rep.winModRep (-α) u) :=
    funext fun x => Work.KMTAreas.A7Hi.windowEnvelopes_eq (mStarF U) u α x
  exact ⟨heq.symm ▸ hh, Work.BourgainPlan.IonescuWainger.hasFreqSupport_congr heq.symm hsup⟩

/-! ## The range identity at the sharp (plateau) separation constant

`A7.fiberOp_zero_eq_self_of_hasFreqSupport` states its separation hypothesis with the *support*
radius of the window (`4 * δ₂`), which is twice what `NonAliasing (-(2U))` provides.  Below the
same statement is proved with the sharp constant `δ₁ + δ₂`: the only use of the separation is in
`iwSymbolSet_eq_one_of_mem_arcSet`, where the bound `‖β - α₀‖ ≤ δ₁ + δ₂` (from
`θ - α₀ ∈ arcSet 0 δ₁` and `θ - β ∈ arcSet 0 δ₂`) already contradicts it.  With
`δ₁ = 2^{-(2U)-1}` (the plateau radius of `mStarF U`) and `δ₂ = 2^{-2U}` (its support radius),
`δ₁ + δ₂ = 1.5 · 2^{-2U}`, and `NonAliasing (-(2U))` gives `2 · 2^{-2U} < ‖α - β‖`. -/

open Work.BourgainPlan.IonescuWainger in
/-- **The IW symbol of a plateau window is `1` on its band**, at the sharp separation `δ₁ + δ₂`. -/
theorem iwSymbolSet_eq_one_of_mem_arcSet_weak
    (A : Finset Circ) (m : ℝ → ℂ) (δ₁ δ₂ : ℝ)
    (hm1 : ∀ θ : Circ, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hm0 : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → δ₁ + δ₂ < ‖α - β‖)
    (α₀ : Circ) (hα₀ : α₀ ∈ A) (θ : Circ)
    (hθ : θ ∈ Work.BourgainPlan.IonescuWainger.arcSet α₀ δ₁) :
    Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize m) θ = 1 := by
  have hsub₁ : θ - α₀ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ := by
    have h := (Work.KMTAreas.A7Hi.arcSet_add_transport (θ - α₀) α₀ α₀ δ₁).mp
      (by rw [sub_add_cancel]; exact hθ)
    simpa using h
  have hone : Work.Analysis.IonescuWainger.periodize m (θ - α₀) = 1 := hm1 _ hsub₁
  have hzero : ∀ β ∈ A, β ≠ α₀ →
      Work.Analysis.IonescuWainger.periodize m (θ - β) = 0 := by
    intro β hβ hne
    by_contra hc
    have hsub₂ : θ - β ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂ := hm0 _ hc
    have hle₁ : ‖θ - α₀‖ ≤ δ₁ := by
      obtain ⟨t, ht, he⟩ := hsub₁
      rw [he, zero_add]
      calc ‖((t : ℝ) : Circ)‖ ≤ |t| := Work.KMTAreas.A7Hi.norm_coe_circle_le_abs t
        _ ≤ δ₁ := ht
    have hle₂ : ‖θ - β‖ ≤ δ₂ := by
      obtain ⟨t, ht, he⟩ := hsub₂
      rw [he, zero_add]
      calc ‖((t : ℝ) : Circ)‖ ≤ |t| := Work.KMTAreas.A7Hi.norm_coe_circle_le_abs t
        _ ≤ δ₂ := ht
    have hle : ‖β - α₀‖ ≤ δ₁ + δ₂ := by
      have hkey : β - α₀ = (θ - α₀) - (θ - β) := by abel
      rw [hkey]
      calc ‖(θ - α₀) - (θ - β)‖ ≤ ‖θ - α₀‖ + ‖θ - β‖ := norm_sub_le _ _
        _ ≤ δ₁ + δ₂ := by linarith
    have hge := hsep α₀ hα₀ β hβ (Ne.symm hne)
    rw [norm_sub_rev] at hge
    linarith
  rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  exact (Finset.sum_eq_single α₀ (fun β hβ hne => hzero β hβ hne)
    (fun h => absurd hα₀ h)).trans hone

/-- **The `0`-fibre of a plateau window fixes its band**, at the sharp separation `δ₁ + δ₂`. -/
theorem fiberOp_zero_eq_self_of_plateau
    (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ₁ δ₂ : ℝ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (hm1 : ∀ θ : Circ, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hm0 : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      α ≠ β → δ₁ + δ₂ < ‖α - β‖)
    (u : ℤ → ℂ) (hu : Memℓp u 2)
    (hband : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        Work.BourgainPlan.IonescuWainger.arcSet α δ₁)) :
    Work.KMTAreas.A7.fiberOp ρ l m 0 u = u := by
  set A := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l with hA
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  have hsym : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize m)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hΨ
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨u, hu⟩ with hF
  set F' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize m) hsym F
    with hF'
  have hfeq : ⇑F' = Work.KMTAreas.A7.fiberOp ρ l m 0 u := by
    rw [Work.KMTAreas.A7.fiberOp_zero_eq_iwConv ρ l m hm u,
      Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym F]
  have hft : Work.Analysis.IonescuWainger.fourierZ F'
      = Work.BourgainPlan.IonescuWainger.ftLp u hu := by
    have h1 : Work.Analysis.IonescuWainger.fourierZ F'
        = hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize m))
          • Work.Analysis.IonescuWainger.fourierZ F := by
      rw [hF']
      exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf _ hsym F
    rw [h1]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize m)))
        (Work.Analysis.IonescuWainger.fourierZ F),
      MeasureTheory.MemLp.coeFn_toLp hsym, hband] with ξ hsmul hσ hb
    rw [hsmul]
    change ⇑(hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize m))) ξ
        • (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ
      = (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ
    by_cases hmem : ξ ∈ ⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α δ₁
    · simp only [Set.mem_iUnion] at hmem
      obtain ⟨α₀, hα₀, hξα₀⟩ := hmem
      have hσ1 : Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize m) ξ = 1 :=
        iwSymbolSet_eq_one_of_mem_arcSet_weak A m δ₁ δ₂ hm1 hm0 hsep α₀ hα₀ ξ hξα₀
      rw [hσ, hσ1, one_smul]
    · have hz : (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ = 0 := hb hmem
      simp only [hz, smul_zero]
  have hFF : F' = F := by
    apply Work.Analysis.IonescuWainger.fourierZ.injective
    rw [hft]
    exact congrArg Work.Analysis.IonescuWainger.fourierZ hF.symm
  have hcoeeq : ⇑F' = ⇑F := congrArg (fun G : Work.Analysis.IonescuWainger.L2Z => ⇑G) hFF
  rw [← hfeq, hcoeeq, hF]




end

theorem fiberVarSamplingLarge_columnBanded :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (r : NNReal), 2 < r →
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        (∀ n : ℕ, (2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ)) →
        (∀ n : ℕ, k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
            ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
        Work.Analysis.IonescuWainger.NonAliasing
          (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) →
        (∀ n : ℕ, ∃ hh : Memℓp (fun x : ℤ => if S n then Work.KMTAreas.A7.Tex ρ l₁
              (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f x else 0) 2,
            Work.BourgainPlan.IonescuWainger.HasFreqSupport
              (fun x : ℤ => if S n then Work.KMTAreas.A7.Tex ρ l₁
                (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f x else 0) hh
              (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
                Work.BourgainPlan.IonescuWainger.arcSet α
                  ((2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)) - 1)))) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
            (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOp ρ l₁
                (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
                (if S n then Work.KMTAreas.A7.Tex ρ l₁
                  (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              (if S n then Work.KMTAreas.A7.Tex ρ l₁
                (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x))
          p MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7
