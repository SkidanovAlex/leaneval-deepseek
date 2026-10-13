/-
# `E1Open/L12f_slot_le_O` — the level-`n` weighted slot bound for `L₁₂ f` in the open class

For a datum `f` which is `C^∞` on the **open** quadrant (`Work.FTS.EllipticEst.SmoothOpen f`),
honest in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`) and whose zero mode vanishes (`L₁₂ f 0 = 0`), the sum
of the weighted squares of the first `n + 1` radial iterates of `L₁₂ f` is integrable on
`Iz = [0,∞)` and bounded by `C · HkSq α n f`, uniformly in `α ∈ (0,1]`, `n ≤ 3` and `f`.

This is the level-`n` (`n ≤ 3`) form of `Work.FTS.StrongEps.EpsRLX.RadBound.L12fSlotLe` (which
proves the five-slot case `n = 4` against the **level-4** energy `HkSq α 4 f`); the consumer
(`E1Open.radA_slotSum_le_O`, then `E1_norm_O`) needs the bound against the *level-`n`* energy,
so the slot sum is capped at `n` and every angular moment `Qang f i` is consumed at level `n`.

The two inputs are

* `Work.FTS.OpenPkg.l12_open_bundle`: the operator identity `D_z^{k+1} (L₁₂ f) = -Qang f k`
  (`k ≤ 3`, the index-raising recursion) together with the weighted Hardy estimate
  `∫ (L₁₂ f)² w² ≤ 107 ∫ (Qang f 0)² w²`;
* the angular-moment bound `hQ` at level `n` (the unit of the open-quadrant Qang estimate,
  supplied by `E1Open.Qang_sq_w_sq_le_HkSq_O` with `CQ = ∫_θ Kθ²`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.H2.L12k0Q
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The level-`n` weighted slot bound for `L₁₂ f`**, given the level-`n` angular-moment bound
`hQ` as a hypothesis (so that this lemma is independent of the angular port). -/
theorem L12f_slot_le_O_of {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ (β : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ), 0 < β → β ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem β m g → ∀ i : ℕ, i ≤ m →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ CQ * Work.Spaces.HkSq β m g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α n f := by
  refine ⟨4 * (107 * CQ) + 1, by positivity, ?_⟩
  intro α hαIoc f hsm hmem4 h0 n hn
  have hαpos : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm n (by omega) hmem4
  -- the two definitions of `L₁₂` agree
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.OpenPkg.l12_open_bundle α f hαpos hα1 hsm hmem4 h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 f z with hudef
  -- ## the a.e. transfer `D_z^i u = -Qang f (i-1)` on `Iz`, `1 ≤ i ≤ 3`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      (fun z : ℝ => (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro i hi hi3
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang f (i - 1) z := by
      have h := hgen (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every slot
  have hInt : ∀ i : ℕ, i ≤ n → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact ((hQ α n f hαpos hα1 hsm hmemn (i - 1) (by omega)).1).congr
        (htrans i h (by omega))
  -- ## the bounds of the individual slots
  have hb0 : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    exact le_trans hb (mul_le_mul_of_nonneg_left
      (hQ α n f hαpos hα1 hsm hmemn 0 (Nat.zero_le n)).2 (by norm_num))
  have hbI : ∀ i : ℕ, 1 ≤ i → i ≤ n → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ CQ * Work.Spaces.HkSq α n f := by
    intro i hi hin
    rw [← MeasureTheory.integral_congr_ae (htrans i hi (by omega))]
    exact (hQ α n f hαpos hα1 hsm hmemn (i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 4 * (107 * (CQ * Work.Spaces.HkSq α n f)) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range (n + 1))
      (fun i hi => hInt i (by have := Finset.mem_range.mp hi; omega))]
    have hnd : 0 ≤ CQ * Work.Spaces.HkSq α n f :=
      mul_nonneg hCQ (Work.Spaces.HkSq_nonneg α n f)
    have hterm : ∀ i ∈ Finset.range (n + 1), (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact hb0
      · exact le_trans (hbI i h hin) (by linarith)
    have h1 : (∑ i ∈ Finset.range (n + 1), (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range (n + 1), 107 * (CQ * Work.Spaces.HkSq α n f) :=
      Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have hcard : (((n + 1 : ℕ)) : ℝ) ≤ 4 := by
      have : ((n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hn
      push_cast
      linarith
    refine le_trans h1 ?_
    have hnn : 0 ≤ 107 * (CQ * Work.Spaces.HkSq α n f) := by linarith
    exact mul_le_mul_of_nonneg_right hcard hnn
  -- ## integrability of the whole `z`-sum
  have hsumInt : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.range (n + 1))
      (fun i hi => hInt i (by have := Finset.mem_range.mp hi; omega))
  -- ## back to `Work.Coercivity.L12f`
  have hfun : Work.Coercivity.L12f f = u := by
    funext z
    have h1 : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
    rw [hudef, h1]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z
  have hcongr : (fun z : ℝ => ∑ c ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ∑ c ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter c u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    rw [hfun]
  constructor
  · rw [hcongr]
    exact hsumInt
  · rw [hcongr]
    refine le_trans hsum_le ?_
    have hk : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
    calc 4 * (107 * (CQ * Work.Spaces.HkSq α n f))
        = (4 * (107 * CQ)) * Work.Spaces.HkSq α n f := by ring
      _ ≤ (4 * (107 * CQ) + 1) * Work.Spaces.HkSq α n f :=
          mul_le_mul_of_nonneg_right (by linarith) hk

end Work.FTS.StrongEps.EpsE4Thr.E1Open
