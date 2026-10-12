import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PotCubicResiduals
import Submission.Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_congr
import Submission.Work.BoseBoxFock.potTruncRepair
import Submission.Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubic_exists` — the `∃ Nmin` repair of the cubic (`Q̃₃`) row

⚠ **READ `Submission/Work/BoseBoxFock/FINDING_PotCubic_exists.md` SESSION 7 FIRST.**  This session
established that the recorded *low-band* estimate (`FINDING` §5.1/§6.2/§6.4) is **false as a proof
step**: the row is a sum over `pairSet n` of two-slot atoms, and that sum is the second-quantised
pair operator `dΓ(X)dΓ(Y) − dΓ(XY) = a†a†aa`, of `n`-particle norm `~n²` — so the crude bounds
carry a factor `n(n−1)`, and the low band then needs the `n₊`-window supplied by the hypothesis
`IsLowB` (FS `thm:aprioribounds` = the corpus node `NodeB1B`), not by `SpectralNPlusLe`
(whose window `𝓜 = K_M(μa³)^{-1/4}` is `t^{0.17}` *weaker* than the a-priori).  The target is
**TRUE**; the remaining work is (i) the dictionary `PotCubicFree`, (ii) `PotCubicLowBand` from
(a) the `IsLowB`-implied `n₊`-window and (b) the atomic (conjugate-structure) bound.
The `physSlot`/`SlotOpBound` bricks of SESSION 7 (`BoseBoxFock/SlotOpDefs.lean` and the five
delegated modules) are the correct substitute for the refuted `L¹`/`L²` bounds there.

Target:

    `∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ PotCubic v h fc fu R J Nmin ε₀ C`

`PotCubic` (`PotGroupDefs.lean`) is FS `lem:2ndQuand`'s **last displayed row** (FS l. 1624–1626),
i.e. the statement that the box's cubic `Q̃₃` row (`potCubic` = `AVpotD`, the *mode* sum
`ℓ⁻³Σ_{s∈excited}Σ_{k∈P_H}f_L(s)Ŵ₁(k)(a₀†ã_s†a_{s−k}a_k + h.c.)`) is dominated by the
*position-space* word `q3lowWord = 2Σ_{p∈pairSet n}∫_{abox}Q_{L,j}(aQ_j aP_iΦ)·(aQ_j aQ_iΦ)·w₁`
in the sense `≤ · + ½errKafz v R μ C·‖Φ‖²`.  FS omit the proof of that row ("a standard
calculation"); the `∃ Nmin` is the repair of the frozen `∀Nmin` form, whose small-`N`
truncation tails genuinely violate the inequality (`FINDING_PotChiLin_holds_FALSE.md`).

The full route, the four-term Poisson decomposition of the `k`-sum, the three error slots
(images / low-momentum cut / lattice truncation), the projection matching with `aP`/`aQ`/`Q_L`,
and the list of the bricks that are already proved in the corpus are recorded in
**`Submission/Work/BoseBoxFock/FINDING_PotCubic_exists.md`**.  The state of this file: the target
is still open; the analytic core of the row (the shifted, weighted Poisson sampling identity of
the lattice `(2π/ℓ)ℤ³`, its unweighted companion, and its truncated form) is delegated as
`Work.BoseBoxFock.latSampling_pair`, `…latSampling_one`, `…latSampling_pair_trunc`, and the
Fubini evaluation of the two-slot pairing produced by the pinning is delegated as
`Work.BoseBoxFock.cIPn_boxSlotOf_two_slot`; the remaining work is the (mechanical) assembly
recorded in the FINDING, §2.

⚠ **Import-cone obstacle** (FINDING §7): the slot-algebra modules (`MB.SlotWeakBase`,
`boxSlotSum_pair_decomp`, `bW4slot_eq_pairSet`, `boxSlotOf_comp_same`, `cIPn_boxSlotOf_two_slot`)
declare `Work.BoseBoxFock.etaOf_hasCompactSupport`, which `AVGoodState` (in this file's cone
through `PotGroupDefs`) declares again, so the two cones cannot be combined: the slot lemmas must
be re-proved *inside* this file's cone (the `PotGroupDefs`-only cone, from the strong twin
`Work.BoseBoxFock.boxSlotSum_rankOnePair`) or the duplicate declaration must be renamed by the
lead.  The `latSampling_*` modules have a `Mathlib`-only cone and can always be imported.
-/

namespace Work.BoseBoxFock

open Work.BoseDict

/-- **The atoms of the cubic row are `bW4slot`s.**

`potCubic`'s two atoms per `(s,k)` are
`(B (|evec0⟩⟨f (s−k)|)) ∘ (B (|g s⟩⟨f k|)) − B (|evec0⟩⟨f (s−k)| ∘ |g s⟩⟨f k|)` and the same with
the pairs swapped — i.e. exactly the slot-form four-letter word
`bW4slot e w₁ w₂ v₁ v₂ d = boxSlotSum e (|w₁⟩⟨v₁|) ∘ boxSlotSum e (|w₂⟩⟨v₂|)
    − boxSlotSum e (|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|)` (`slotPairDefs.lean`) at
`(w₁,v₁,w₂,v₂) = (evec0, f (s−k), g s, f k)` and `(f k, f (s−k), g s, evec0)`.

This is the first step of the assembly (FINDING §2, step 1): it puts the cubic row into the shape
on which the slot algebra of the corpus (`boxSlotSum_rankOnePair_weak`,
`boxSlotSum_pair_decomp`, `boxSlotOf_comp_same`, `cIPn_boxSlotOf_two_slot`) acts. -/
private lemma potCubic_eq_bW4slot_sum {m d : ℕ} [NeZero m] {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (e : Fin m → Work.BoseDict.Sp → ℂ) (f g : Mode → Fin m → ℝ) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (Θ : (Fin (d + 2) → Work.BoseDict.Sp) → ℂ) :
    potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ
      = (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
          (E.fL s * E.W1 k) •
            (bW4slot e (evec0 m) (g s) (f (s - k)) (f k) d Θ
              + bW4slot e (f k) (f (s - k)) (g s) (evec0 m) d Θ) := by
  simp only [potCubic, bW4slot, Function.comp_apply, Finset.sum_apply, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 0. The two mode-multiplicativity identities (the exponential factorisation)

The dictionary of `PotCubicFree` needs the `(s,k) ↦ (k, s−k)` change of variables, whose content
is that the box modes factor through the exponential:
`modeVec (ℓ, p+q) z = e^{i⟪q,z⟫}·modeVec (ℓ,p) z` and the same for `θ_s`.  These are the
"separation" identities of `FINDING_PotCubic_exists.md` §6.4. -/
theorem modeVec_add (ℓ : ℝ) (p q z : ℝ³) :
    Work.BoseK15.corpusBox.modeVec ℓ (p + q) z
      = Complex.exp (Complex.I * ((inner ℝ q z : ℝ) : ℂ))
          * Work.BoseK15.corpusBox.modeVec ℓ p z := by
  simp only [Work.BoseB4.BoxData.modeVec]
  rw [inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem thetaExp_add (ℓ : ℝ) (p q z : ℝ³) :
    Work.BoseK15.corpusBox.thetaExp ℓ (p + q) z
      = Complex.exp (Complex.I * ((inner ℝ q z : ℝ) : ℂ))
          * Work.BoseK15.corpusBox.thetaExp ℓ p z := by
  simp only [Work.BoseB4.BoxData.thetaExp]
  rw [inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-! ## 1. The `Finset` split of the `k`-sum

`potCubic` is `ℓ⁻³Σ_{s∈excited}Σ_{k∈PHs}(f_L(s)Ŵ₁(k))•(two atoms)`, so the label set is an
additive slot: this is the algebraic step behind the `PHset` ↔ `excited` comparison of
`PotCubicResiduals`. -/
theorem potCubic_finset_split {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → ℝ³) → ℂ) → ((ι → ℝ³) → ℂ))
    (f g : Mode → Fin m → ℝ) (s₁ s₂ : Finset Mode) (hdis : Disjoint s₁ s₂)
    (E : Work.BoseB7.Q3Env Mode) (Θ : (ι → ℝ³) → ℂ) :
    potCubic B f g (s₁ ∪ s₂) E Θ = potCubic B f g s₁ E Θ + potCubic B f g s₂ E Θ := by
  simp only [potCubic, Finset.sum_union hdis, Finset.sum_add_distrib, Pi.smul_apply,
    Finset.sum_apply, Pi.add_apply, smul_add]

/-- **The low-band decomposition of the cubic row.**  For `PHs ⊆ s`,

    `potCubic(B) f g PHs + potCubic(B) f g (s \ PHs) = potCubic(B) f g s`

i.e. the `PHs`-restricted row plus the *omitted low band* `s \ PHs` is the unrestricted row.
This is the algebraic first step of any proof of `PotCubicLowBand`: the residual is exactly the
inequality `−(∫ conj Θ · potCubic(low) Θ).re ≤ ½·errKafz v R μ C·normB` with
`low = excited \ PHset`.  (The `PHset ⊆ excited` inclusion is `Finset.filter_subset`.) -/
theorem potCubic_eq_add_sdiff {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ι : Type*}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → ((ι → ℝ³) → ℂ) → ((ι → ℝ³) → ℂ))
    (f g : Mode → Fin m → ℝ) (s PHs : Finset Mode) (hsub : PHs ⊆ s)
    (E : Work.BoseB7.Q3Env Mode) (Θ : (ι → ℝ³) → ℂ) :
    potCubic B f g PHs E Θ + potCubic B f g (s \ PHs) E Θ = potCubic B f g s E Θ := by
  rw [← potCubic_finset_split B f g PHs (s \ PHs) Finset.disjoint_sdiff E Θ,
    Finset.union_sdiff_of_subset hsub]

/-! ## 2. The reduction of the target to the two residuals of `PotCubicResiduals`

`PotCubicFree` is FS `lem:2ndQuand`'s last displayed row (the `k`-sum unrestricted);
`PotCubicLowBand` is the omitted low band `excited \ PHset`; `errKafz` is linear in its constant,
so the two error allowances add. -/
theorem PotCubic_of_free_low (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀₁ ε₀₂ C₁ C₂ : ℝ)
    (hfree : PotCubicFree v h fc fu R J Nmin ε₀₁ C₁)
    (hlow : PotCubicLowBand v h fc fu R J Nmin ε₀₂ C₂) :
    PotCubic v h fc fu R J Nmin (min ε₀₁ ε₀₂) (C₁ + C₂) := by
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin
    hKp hLp hθp T_NH hTNH
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₀₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₀₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have h1 := hfree HM hMono μ hAdm₁ hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth
    hint hemem hpin hKp hLp hθp T_NH hTNH
  have h2 := hlow HM hMono μ hAdm₂ hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth
    hint hemem hpin hKp hLp hθp T_NH hTNH
  have h3 : Work.BoseFixR.errKafz v R μ (C₁ + C₂)
      = Work.BoseFixR.errKafz v R μ C₁ + Work.BoseFixR.errKafz v R μ C₂ := by
    simp only [Work.BoseFixR.errKafz]; ring
  rw [h3]
  linarith

/-! ## 3. The exact reduction (SESSION 8)

`FINDING_PotCubic_exists.md` SESSION 8 shows that the target is *exactly*

    `(dictionary `PotCubicFree` on the `excited`-row) + (the low band `excited \ PHset`)`,

and that the low band is **payable** once the a-priori `n₊`-window
`Work.BoseBoxFix.B2AprioriWindowB v h J` (the second conjunct of FS `thm:aprioribounds`, i.e. the
corpus node `NodeB1B`) is available: the sharp value of the omitted band is
`9.67·t^{1.1385}a^{-2}·(n₊/nPlusWindow)^{3/2}‖Θ‖²` (`t = μ(a v)³`) against the allowance
`½errKafz ≈ ½C·t·a^{-2}‖Θ‖²`, a margin `t^{0.125}`, whereas the node's own window
`SpectralNPlusLe ℓ 𝓜` (`𝓜 = t^{-0.2531}`, **weaker** than `nPlusWindow = t^{-0.0789}`) does *not*
suffice.  The two inputs are therefore kept as explicit hypotheses of the following assembly: the
dictionary `PotCubicFree` (with all its bricks on disk) and the window-conditional low band, which
is the single analytic frontier.

The bridge `B2AprioriWindowB v h J ⟹ ∃ ε₀ C, PotCubicLowBand …` is filed as
`Work.BoseBoxFock.PotCubicLowBand_window`
(`Submission/Work/BoseBoxFock/PotCubicLowBand_window.lean`, with the *full* hypothesis list
`0 ≤ v`, `MemLp v 1`, `IsRadial v`, `0 < R`, `supp ⊆ ball 0 R`, `0 < a v` — the earlier filing at
`PotCubicLowBand_of_window.lean` dropped them, and is **false** as stated: without them the honest
weight `W1 = uvCut·chat(W1fun v h ℓ)` is not controlled by `a v`; see
`FINDING_PotCubicLowBand_of_window_FALSE.md`).  With that bridge and the dictionary, this assembly
*is* the target. -/
theorem PotCubic_exists_of_free_window (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ)
    (hlowBridge : ∀ Nmin : ℝ → ℕ, ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      PotCubicLowBand v h fc fu R J Nmin ε₀ C)
    (hfree : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      PotCubicFree v h fc fu R J Nmin ε₀ C) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotCubic v h fc fu R J Nmin ε₀ C := by
  obtain ⟨Nmin, ε₀₁, C₁, hε₁, hC₁, hfree'⟩ := hfree
  obtain ⟨ε₀₂, C₂, hε₂, hC₂, hlow⟩ := hlowBridge Nmin
  exact ⟨Nmin, min ε₀₁ ε₀₂, C₁ + C₂, lt_min hε₁ hε₂, add_nonneg hC₁ hC₂,
    PotCubic_of_free_low v h fc fu R J Nmin ε₀₁ ε₀₂ C₁ C₂ hfree' hlow⟩

theorem PotCubic_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotCubic v h fc fu R J Nmin ε₀ C := by
  sorry

end Work.BoseBoxFock
