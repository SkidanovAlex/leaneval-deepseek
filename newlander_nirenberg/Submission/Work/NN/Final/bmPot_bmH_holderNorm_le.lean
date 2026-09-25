import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Filter

namespace Work.NN.Final

variable {n : ℕ}

/-! ### `∂̄χ`: regularity, support and vanishing

The cut-off `χ` is smooth, so each `∂̄_a χ` is smooth; its support is contained in the topological
support of `χ` (which lies in `pd n ρ 3`), it is compactly supported, and it vanishes off
`tsupport χ`. -/

private lemma contDiff_dbarCoord_of {n : ℕ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ∀ m : ℕ, ContDiff ℝ m χ) (a : Fin n) :
    ContDiff ℝ ∞ (fun z => Work.CR.Flat.dbarCoord a χ z) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  refine (Work.CR.Flat.Polydisc.dbarCoordPhi a).contDiff.comp ?_
  rw [contDiff_infty]
  intro m
  exact (hχ (m + 1)).fderiv_right (by simp)

private lemma dbarCoord_eq_zero_of_notMem_tsupport {n : ℕ} {g : (Fin n → ℂ) → ℂ} {w : Fin n → ℂ}
    (hw : w ∉ tsupport g) (a : Fin n) : Work.CR.Flat.dbarCoord a g w = 0 := by
  have hn : (tsupport g)ᶜ ∈ nhds w := (isClosed_tsupport g).isOpen_compl.mem_nhds hw
  have heq : g =ᶠ[nhds w] (fun _ : Fin n → ℂ => 0) := by
    filter_upwards [hn] with y hy
    by_contra hy'
    exact hy (subset_tsupport g (Function.mem_support.mpr hy'))
  have hfd : fderiv ℝ g w = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  simp [Function.comp_apply, hfd]

private lemma tsupport_dbarCoord_subset {n : ℕ} {χ : (Fin n → ℂ) → ℂ} (a : Fin n) :
    tsupport (fun z => Work.CR.Flat.dbarCoord a χ z) ⊆ tsupport χ := by
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport χ)
  intro z hz
  by_contra hzc
  exact hz (dbarCoord_eq_zero_of_notMem_tsupport hzc a)

private lemma hasCompactSupport_dbarCoord {n : ℕ} {χ : (Fin n → ℂ) → ℂ}
    (hcs : HasCompactSupport χ) (a : Fin n) :
    HasCompactSupport (fun z => Work.CR.Flat.dbarCoord a χ z) := by
  rw [HasCompactSupport] at hcs ⊢
  exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) (tsupport_dbarCoord_subset a)

/-- A point at which some coordinate is at least `3 ρ` is outside `pd n ρ 3`. -/
private lemma notMem_pd_of_exists {n : ℕ} {ρ : Fin n → ℝ} {z : Fin n → ℂ}
    (hz : ∃ i, 3 * ρ i ≤ ‖z i‖) : z ∉ pd n ρ 3 := by
  obtain ⟨i, hi⟩ := hz
  rw [mem_pd]
  intro h
  exact absurd (h i) (not_lt.mpr hi)

/-- The defect form `bmH χ η` vanishes off the topological support of `χ`. -/
private lemma bmH_vanishes_off_pd {n : ℕ} {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (htsupp : tsupport χ ⊆ pd n ρ 3) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (a b c : Fin n)
    {z : Fin n → ℂ} (hz : z ∉ pd n ρ 3) : Work.NN.Core.bmH χ η a b c z = 0 := by
  have hzc : z ∉ tsupport χ := fun h => hz (htsupp h)
  have h0 : ∀ p : Fin n, Work.CR.Flat.dbarCoord p χ z = 0 :=
    fun p => dbarCoord_eq_zero_of_notMem_tsupport hzc p
  rw [Work.NN.Core.bmH, h0 c, h0 a, h0 b]
  ring

/-- On an open set, the `C^{k,α}` norm is invariant under negation (no differentiability of the
function is needed, because `iteratedFDerivWithin` of `-f` is `-` that of `f` on an open set). -/
private lemma holderNorm_neg_of_isOpen {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) (k : ℕ)
    (α : ℝ) (f : (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.holderNorm k α (fun z => -f z) Ω = Work.CR.Flat.holderNorm k α f Ω := by
  have hu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hneg : ∀ (i : ℕ) {x : Fin n → ℂ}, x ∈ Ω →
      iteratedFDerivWithin ℝ i (fun z => -f z) Ω x = -iteratedFDerivWithin ℝ i f Ω x :=
    fun i x hx => iteratedFDerivWithin_neg_apply (𝕜 := ℝ) (s := Ω) (i := i) (f := f) hu hx
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · rw [Work.CR.Flat.iterDerivNorm, Work.CR.Flat.iterDerivNorm]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun x hx => ?_
      rw [hneg i hx, norm_neg]
      exact le_iSup₂_of_le x hx le_rfl
    · refine iSup₂_le fun x hx => ?_
      refine le_iSup₂_of_le x hx ?_
      rw [hneg i hx, norm_neg]
  · rw [Work.CR.Flat.holderSeminorm, Work.CR.Flat.holderSeminorm]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [hneg i hx, hneg i hy,
        show (-iteratedFDerivWithin ℝ i f Ω x) - (-iteratedFDerivWithin ℝ i f Ω y)
          = -(iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y) from by abel,
        norm_neg]
      exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
    · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy ?_))
      rw [hneg i hx, hneg i hy,
        show (-iteratedFDerivWithin ℝ i f Ω x) - (-iteratedFDerivWithin ℝ i f Ω y)
          = -(iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y) from by abel,
        norm_neg]

/-- **The error term of one Bochner–Martinelli step gains one derivative.**

Let `χ` be a smooth cut-off (`∀ m, ContDiff ℝ m χ`) whose topological support lies in
`pd n ρ 3 ⊂ pd n ρ 4`, and let `η` have components of class `C^{k+1}` on `pd n ρ 4`.  Then the
`(0,2)`-form `z ↦ γ⁻¹ · bmPot (bmH χ η j l ·) z` has a `(k+1, α)`-norm on `pd n ρ (8/3)` bounded
by `C k` times the `(k, α)`-norms of `η` on `pd n ρ 4`.

**Proof route (please follow it; it uses only sorry-free inputs).**  View the family
`i ↦ bmH χ η j l i` as the `i₀`-th row of a degenerate `(0,2)`-form `X` (fix any `i₀ : Fin n`,
possible since `n > 0`; set the other rows to `0`).  Then
`z ↦ γ⁻¹ bmPot (fun i => bmH χ η j l i) z = - bmRow X i₀`, and the estimates are
`Work.NN.Core.bmRow_holder` (proved, sorry-free) applied with centre `0` and radii `6ρ`, whose
conclusion region is `polydisc 0 (3ρ) ⊇ pd n ρ (8/3)`.  Its hypotheses are: components of `X` of
class `C^{k+1}` (each `∂̄χ · η` product is globally `C^{k+1}` by
`Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport`, since `supp (∂̄χ) ⊆ tsupport χ ⊆ pd n ρ 3`
is a compact subset of the open `pd n ρ 4`), and support of `X` inside `polydisc 0 (3ρ)` (from
`tsupport χ ⊆ pd n ρ 3`).  Its right-hand side is the sum over all rows and columns of `X`, i.e.
`∑ m, holderNorm k α (bmH χ η j l m) Set.univ`; convert that to the norms of `η` on `pd n ρ 4`
with `holderNorm_univ_le_holderNorm_polydisc_of_vanishing` (support in `polydisc 0 (3ρ) ⊂
polydisc 0 (4ρ)`) and `holderNorm_mul_le_of_hasCompactSupport` (applied with `ζ := ∂̄_a χ`,
`Ω := pd n ρ 4`), plus `holderNorm_add_le`/`holderNorm_neg` for the three terms of `bmH`.

**CAUTION.**  Do **not** use `Work.CR.Flat.Cauchy.bmPotential_holderNorm_le_Ck`: it depends on
`sorryAx` (it is flagged as "the Vekua caveat"), so it would destroy the axiom profile of this
lemma.  After finishing, please check `#print axioms` of the lemma (it must not list `sorryAx`). -/
theorem bmPot_bmH_holderNorm_le {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ}
    (hχ : ∀ m : ℕ, ContDiff ℝ m χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (η i l) (pd n ρ 4)) →
      ∀ j l : Fin n,
        Work.CR.Flat.holderNorm (k + 1) α
            (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
              Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
            (pd n ρ (8 / 3 : ℝ))
          ≤ ENNReal.ofReal C *
              ∑ r : Fin n, ∑ s : Fin n,
                Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4) := by
  -- ### regularity and support of `∂̄χ`
  have hsd : ∀ a : Fin n, ContDiff ℝ ∞ (fun z => Work.CR.Flat.dbarCoord a χ z) :=
    fun a => contDiff_dbarCoord_of hχ a
  have hts4 : ∀ a : Fin n, tsupport (fun z => Work.CR.Flat.dbarCoord a χ z) ⊆ pd n ρ 4 :=
    fun a => (tsupport_dbarCoord_subset a).trans
      (htsupp.trans (pd_mono hρ (by norm_num : (3:ℝ) ≤ 4)))
  have hcsχ : HasCompactSupport χ := by
    refine Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc (c := 0) (r := fun j => 6 * ρ j)
      (fun j => by linarith [hρ j]) ?_
    intro z hz
    obtain ⟨i, hi⟩ := hz
    have hiP : 3 * ρ i ≤ ‖z i‖ := by
      have hi' : 6 * ρ i / 2 ≤ ‖z i‖ := by simpa using hi
      linarith
    exact Function.notMem_support.mp fun hz' =>
      notMem_pd_of_exists (ρ := ρ) ⟨i, hiP⟩ (htsupp (subset_tsupport χ hz'))
  have hcsd : ∀ a : Fin n, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord a χ z) :=
    fun a => hasCompactSupport_dbarCoord hcsχ a
  -- ### the multiplication constants, one per `∂̄_a χ`
  have hconst : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (pd n ρ 4) →
      Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord a χ z * f z) (pd n ρ 4)
        ≤ ENNReal.ofReal Ca * Work.CR.Flat.holderNorm k α f (pd n ρ 4) := fun a =>
    Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport (Ω := pd n ρ 4)
      (isOpen_pd ρ 4).uniqueDiffOn hα0.le hα1.le ((hsd a).of_le (by simp)) (hcsd a)
  choose Ca hCapos hCa using hconst
  set C3 : ℝ := ∑ a : Fin n, Ca a with hC3def
  have hC3pos : 0 < C3 := by
    rw [hC3def]
    exact lt_of_lt_of_le (hCapos ⟨0, hn⟩)
      (Finset.single_le_sum (f := fun a => Ca a) (fun a _ => le_of_lt (hCapos a))
        (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
  have hC3nn : 0 ≤ C3 := le_of_lt hC3pos
  have hCa_le : ∀ a : Fin n, Ca a ≤ C3 := fun a => by
    rw [hC3def]
    exact Finset.single_le_sum (f := fun a => Ca a) (fun a _ => le_of_lt (hCapos a))
      (Finset.mem_univ a)
  -- ### the constant of the row estimate
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.NN.Core.bmRow_holder (n := n) hn hα0 hα1 (c := 0)
    (r := fun j => 6 * ρ j) (fun j => by linarith [hρ j]) k
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hCpos : 0 < Cb * (n : ℝ) * (3 * C3) :=
    mul_pos (mul_pos hCbpos hnpos) (by linarith)
  refine ⟨Cb * (n : ℝ) * (3 * C3), hCpos, ?_⟩
  intro η hη j l
  set S : ℝ≥0∞ := ∑ r : Fin n, ∑ s : Fin n,
    Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4) with hSdef
  -- ### global `C^{k+1}`-regularity of the products `∂̄_a χ · η_{rs}`
  have hprodCD : ∀ (a r s : Fin n), ContDiff ℝ (k + 1)
      (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) := fun a r s =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (isOpen_pd ρ 4) (hsd a) (hts4 a) (hη r s)
  have hcd : ∀ (a r s : Fin n), ContDiffOn ℝ (k : ℕ∞)
      (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) Set.univ := fun a r s =>
    ((hprodCD a r s).of_le (by exact_mod_cast Nat.le_succ k)).contDiffOn
  -- ### comparison of the individual `η`-norms with the full double sum
  have hS1 : ∀ r : Fin n, (∑ s : Fin n, Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4)) ≤ S :=
    fun r => by
      rw [hSdef]
      exact Finset.single_le_sum (f := fun r => ∑ s : Fin n,
        Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4)) (fun _ _ => bot_le) (Finset.mem_univ r)
  have hS2 : ∀ r s : Fin n, Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4) ≤ S := fun r s =>
    (Finset.single_le_sum (f := fun s => Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4))
      (fun _ _ => bot_le) (Finset.mem_univ s)).trans (hS1 r)
  -- ### the bound for each individual product
  have hterm : ∀ (a r s : Fin n),
      Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) Set.univ
        ≤ ENNReal.ofReal C3 * S := by
    intro a r s
    have hvan : ∀ z : Fin n → ℂ, (∃ i, 3 * ρ i ≤ ‖z i - 0‖) →
        (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) z = 0 := by
      intro z hz
      obtain ⟨i, hi⟩ := hz
      have hiP : 3 * ρ i ≤ ‖z i‖ := by
        simp only [sub_zero] at hi
        exact hi
      have hzc : z ∉ tsupport χ := fun h => notMem_pd_of_exists (ρ := ρ) ⟨i, hiP⟩ (htsupp h)
      simp [dbarCoord_eq_zero_of_notMem_tsupport hzc a]
    have h1 : Work.CR.Flat.holderNorm k α
        (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) Set.univ
        ≤ Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z)
            (pd n ρ 4) :=
      Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
        (c := 0) (r := fun j => 3 * ρ j) (r' := fun j => 4 * ρ j) (k := k) (α := α)
        (fun j => by linarith [hρ j]) hα0.le hvan
    have h2 : Work.CR.Flat.holderNorm k α
        (fun z => Work.CR.Flat.dbarCoord a χ z * η r s z) (pd n ρ 4)
        ≤ ENNReal.ofReal (Ca a) * Work.CR.Flat.holderNorm k α (η r s) (pd n ρ 4) :=
      hCa a (η r s) ((hη r s).of_le (by exact_mod_cast Nat.le_succ k))
    refine h1.trans (h2.trans ?_)
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCa_le a)) _).trans
      (mul_le_mul_right (hS2 r s) _)
  -- ### the bound for `bmH`
  have hbmH : ∀ b : Fin n,
      Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ η j l b) Set.univ
        ≤ ENNReal.ofReal (3 * C3) * S := by
    intro b
    have hA : ContDiffOn ℝ (k : ℕ∞)
        (fun z => Work.CR.Flat.dbarCoord b χ z * η j l z) Set.univ := hcd b j l
    have hB : ContDiffOn ℝ (k : ℕ∞)
        (fun z => Work.CR.Flat.dbarCoord j χ z * η l b z) Set.univ := hcd j l b
    have hD : ContDiffOn ℝ (k : ℕ∞)
        (fun z => Work.CR.Flat.dbarCoord l χ z * η j b z) Set.univ := hcd l j b
    have heq : Work.NN.Core.bmH χ η j l b
        = fun z => (Work.CR.Flat.dbarCoord b χ z * η j l z
              + Work.CR.Flat.dbarCoord j χ z * η l b z)
            + (-(Work.CR.Flat.dbarCoord l χ z * η j b z)) := by
      funext z
      simp only [Work.NN.Core.bmH]
      ring
    rw [heq]
    calc Work.CR.Flat.holderNorm k α
          (fun z => (Work.CR.Flat.dbarCoord b χ z * η j l z
              + Work.CR.Flat.dbarCoord j χ z * η l b z)
            + (-(Work.CR.Flat.dbarCoord l χ z * η j b z))) Set.univ
        ≤ Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord b χ z * η j l z
                + Work.CR.Flat.dbarCoord j χ z * η l b z) Set.univ
            + Work.CR.Flat.holderNorm k α
              (fun z => -(Work.CR.Flat.dbarCoord l χ z * η j b z)) Set.univ :=
          Work.CR.Flat.Holder.holderNorm_add_le (hA.add hB) hD.neg (isOpen_univ.uniqueDiffOn)
      _ = Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord b χ z * η j l z
                + Work.CR.Flat.dbarCoord j χ z * η l b z) Set.univ
            + Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord l χ z * η j b z) Set.univ := by
          rw [holderNorm_neg_of_isOpen isOpen_univ]
      _ ≤ (Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord b χ z * η j l z) Set.univ
            + Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord j χ z * η l b z) Set.univ)
          + Work.CR.Flat.holderNorm k α
              (fun z => Work.CR.Flat.dbarCoord l χ z * η j b z) Set.univ :=
          add_le_add (Work.CR.Flat.Holder.holderNorm_add_le hA hB (isOpen_univ.uniqueDiffOn))
            le_rfl
      _ ≤ (ENNReal.ofReal C3 * S + ENNReal.ofReal C3 * S) + ENNReal.ofReal C3 * S :=
          add_le_add (add_le_add (hterm b j l) (hterm j l b)) (hterm l j b)
      _ = ENNReal.ofReal (3 * C3) * S := by
          have h3 : ENNReal.ofReal (3 * C3)
              = ENNReal.ofReal C3 + ENNReal.ofReal C3 + ENNReal.ofReal C3 := by
            rw [show (3:ℝ) * C3 = C3 + C3 + C3 by ring,
              ENNReal.ofReal_add (by linarith) (by linarith),
              ENNReal.ofReal_add hC3nn hC3nn]
          rw [h3, add_mul, add_mul]
  -- ### the degenerate form `X`
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀def
  let X : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
    fun a b => if a = i₀ then Work.NN.Core.bmH χ η j l b else 0
  have hXcd : ∀ a b : Fin n, ContDiff ℝ (k + 1) (X a b) := by
    intro a b
    by_cases ha : a = i₀
    · have hXb : X a b = fun z => Work.CR.Flat.dbarCoord b χ z * η j l z
            + Work.CR.Flat.dbarCoord j χ z * η l b z
          - Work.CR.Flat.dbarCoord l χ z * η j b z := by
        funext z
        simp only [X, ha, ite_true, Work.NN.Core.bmH]
      rw [hXb]
      exact ((hprodCD b j l).add (hprodCD j l b)).sub (hprodCD l j b)
    · have hXb : X a b = 0 := by
        funext z
        simp [X, ha]
      rw [hXb]
      exact contDiff_const
  have hXvan : ∀ a b : Fin n, ∀ z : Fin n → ℂ,
      (∃ i, (6 * ρ i) / 2 ≤ ‖z i - 0‖) → X a b z = 0 := by
    intro a b z hz
    obtain ⟨i, hi⟩ := hz
    have hiP : 3 * ρ i ≤ ‖z i‖ := by
      simp only [sub_zero] at hi
      linarith
    by_cases ha : a = i₀
    · have hXb : X a b = Work.NN.Core.bmH χ η j l b := by funext z; simp [X, ha]
      rw [hXb]
      exact bmH_vanishes_off_pd htsupp η j l b (notMem_pd_of_exists (ρ := ρ) ⟨i, hiP⟩)
    · simp [X, ha]
  have hrow := hCb X hXcd hXvan i₀
  -- ### the row identity
  have hXrow : (fun i : Fin n => X i₀ i) = fun i => Work.NN.Core.bmH χ η j l i := by
    funext i
    simp [X]
  have hfun_eq : (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
      = fun z => -(Work.NN.Core.bmRow X i₀ z) := by
    funext z
    simp only [Work.NN.Core.bmRow_apply]
    rw [hXrow]
    ring
  -- ### the sum over the rows of `X`
  have hXsum : (∑ a : Fin n, ∑ b : Fin n, Work.CR.Flat.holderNorm k α (X a b) Set.univ)
      = ∑ b : Fin n, Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ η j l b) Set.univ := by
    rw [Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun b _ => ?_
      have hXb : X i₀ b = Work.NN.Core.bmH χ η j l b := by funext z; simp [X]
      rw [hXb]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      have hXb : X a b = 0 := by funext z; simp [X, ha]
      rw [hXb, Work.CR.Flat.holderNorm_zero]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hsumB : (∑ b : Fin n, Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ η j l b) Set.univ)
      ≤ (n : ℝ≥0∞) * (ENNReal.ofReal (3 * C3) * S) := by
    calc ∑ b : Fin n, Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ η j l b) Set.univ
        ≤ ∑ _b : Fin n, ENNReal.ofReal (3 * C3) * S := Finset.sum_le_sum fun b _ => hbmH b
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal (3 * C3) * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ### the region comparison `pd n ρ (8/3) ⊆ polydisc 0 (3ρ)`
  have hsub : pd n ρ (8 / 3 : ℝ) ⊆ Work.CR.Flat.polydisc 0 (fun i => 6 * ρ i / 2) := by
    rw [show (fun i : Fin n => 6 * ρ i / 2) = fun i => 3 * ρ i from by funext i; ring]
    exact pd_mono hρ (by norm_num)
  -- ### assembly
  calc Work.CR.Flat.holderNorm (k + 1) α
        (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
        (pd n ρ (8 / 3 : ℝ))
      = Work.CR.Flat.holderNorm (k + 1) α (fun z => -(Work.NN.Core.bmRow X i₀ z))
          (pd n ρ (8 / 3 : ℝ)) := by rw [hfun_eq]
    _ = Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmRow X i₀) (pd n ρ (8 / 3 : ℝ)) :=
        holderNorm_neg_of_isOpen (isOpen_pd ρ (8 / 3)) (k + 1) α (Work.NN.Core.bmRow X i₀)
    _ ≤ Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmRow X i₀)
          (Work.CR.Flat.polydisc 0 (fun i => 6 * ρ i / 2)) :=
        Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 (fun i => 6 * ρ i / 2))
          (isOpen_pd ρ (8 / 3)) hsub (k + 1) α (Work.NN.Core.bmRow X i₀)
    _ ≤ ENNReal.ofReal Cb * ∑ a : Fin n, ∑ b : Fin n,
          Work.CR.Flat.holderNorm k α (X a b) Set.univ := hrow
    _ = ENNReal.ofReal Cb * ∑ b : Fin n,
          Work.CR.Flat.holderNorm k α (Work.NN.Core.bmH χ η j l b) Set.univ := by rw [hXsum]
    _ ≤ ENNReal.ofReal Cb * ((n : ℝ≥0∞) * (ENNReal.ofReal (3 * C3) * S)) :=
        mul_le_mul_right hsumB _
    _ = ENNReal.ofReal (Cb * (n : ℝ) * (3 * C3)) * S := by
        have h1 : ENNReal.ofReal Cb * ENNReal.ofReal (n : ℝ)
            = ENNReal.ofReal (Cb * (n : ℝ)) :=
          (ENNReal.ofReal_mul hCbpos.le).symm
        have h2 : ENNReal.ofReal (Cb * (n : ℝ)) * ENNReal.ofReal (3 * C3)
            = ENNReal.ofReal (Cb * (n : ℝ) * (3 * C3)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
        rw [← ENNReal.ofReal_natCast n,
          ← mul_assoc (ENNReal.ofReal Cb) (ENNReal.ofReal (n : ℝ))
            (ENNReal.ofReal (3 * C3) * S),
          h1, ← mul_assoc (ENNReal.ofReal (Cb * (n : ℝ))) (ENNReal.ofReal (3 * C3)) S, h2]

end Work.NN.Final
