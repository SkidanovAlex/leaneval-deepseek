import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.IDSPrufer.dir
import Submission.Work.TMComp.IDSPrufer.contx
import Submission.Work.TMComp.IDSPrufer.rotLift_approx
import Submission.Work.TMComp.IDSBox.charpoly
import Submission.Work.TMComp.IDSBox.eigroot
import Submission.Work.TMComp.IDSBox.rootcount
import Submission.Work.TMComp.IDSBox.window
import Submission.Work.TMComp.IDSBox.shiftFixed
import Submission.Work.TMComp.IDSEqui.count
import Submission.Work.TMComp.IDSSpec.kernel

/-!
# C6 (`P_IDSSpectrum`): spectral points are points of increase of the IDS

Assembly of the Sturm-oscillation proof (AJ (2.11)).  The auxiliary pieces live in
`Work.TMComp.IDSDefs` (shared vocabulary) and in the sibling modules
`IDSPrufer.dir`, `IDSPrufer.orbitE`, `IDSPrufer.rotLift_approx`, `IDSPrufer.contx`,
`IDSBox.charpoly`, `IDSBox.eigroot`, `IDSBox.rootcount`, `IDSBox.window`, `IDSBox.shift`,
`IDSEqui.count`, `IDSSpec.kernel`, `IDSComb.spaced`.
-/

noncomputable section

open scoped BigOperators
open Polynomial
open MeasureTheory
open Filter

namespace Work.TMComp

open Work.TMContract

/-- The Dirichlet state vector is never zero (the transfer matrices are invertible). -/
theorem jstate_ne_zero (α lam θ E : ℝ) : ∀ n : ℕ, jstate α lam θ E n ≠ (0, 0) := by
  have key : ∀ n : ℕ, jstate α lam θ E n = (0, 0) → jstate α lam θ E 0 = (0, 0) := by
    intro n
    induction n with
    | zero => intro h; exact h
    | succ n ih =>
      intro h
      apply ih
      have hrec : jstate α lam θ E (n + 1)
          = ((E - pot α lam θ n) * (jstate α lam θ E n).1 - (jstate α lam θ E n).2,
             (jstate α lam θ E n).1) := by simp [jstate]
      have h1 : (jstate α lam θ E n).1 = 0 := by
        have := congrArg Prod.snd h
        rw [hrec] at this
        simpa using this
      have h2 : (jstate α lam θ E n).2 = 0 := by
        have hh := congrArg Prod.fst h
        rw [hrec, h1, mul_zero, zero_sub] at hh
        exact neg_eq_zero.mp hh
      exact Prod.ext h1 h2
  intro n h
  have h0 := key n h
  simp [jstate] at h0

/-- The zero set of the `n`-th Dirichlet determinant is the set of half-integer values of
the `n`-step Prüfer angle. -/
theorem uSeq_eq_zero_iff (α lam θ E : ℝ) (n : ℕ)
    (hdir : ∃ ρ : ℝ, 0 ≤ ρ ∧
      uSeq α lam θ E n = ρ * Real.cos (Real.pi * pruferIter α lam E n θ 0) ∧
      vSeq α lam θ E n = ρ * Real.sin (Real.pi * pruferIter α lam E n θ 0)) :
    uSeq α lam θ E n = 0 ↔ ∃ m : ℤ, pruferIter α lam E n θ 0 = m + 1/2 := by
  obtain ⟨ρ, hρ0, hu, hv⟩ := hdir
  have hpos : 0 < ρ := by
    rcases lt_or_eq_of_le hρ0 with h | h
    · exact h
    · exfalso
      have hz : jstate α lam θ E n = (0, 0) := by
        have h1 : (jstate α lam θ E n).1 = 0 := by
          have hh : uSeq α lam θ E n = 0 := by rw [hu, ← h, zero_mul]
          simpa [uSeq] using hh
        have h2 : (jstate α lam θ E n).2 = 0 := by
          have hh : vSeq α lam θ E n = 0 := by rw [hv, ← h, zero_mul]
          simpa [vSeq] using hh
        exact Prod.ext h1 h2
      exact jstate_ne_zero α lam θ E n hz
  constructor
  · intro h0
    have hcos : Real.cos (Real.pi * pruferIter α lam E n θ 0) = 0 := by
      have hh : ρ * Real.cos (Real.pi * pruferIter α lam E n θ 0) = 0 := by rw [← hu, h0]
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hpos)
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
    refine ⟨k, ?_⟩
    have hk' : Real.pi * pruferIter α lam E n θ 0 = Real.pi * ((k : ℝ) + 1/2) := by
      rw [hk]; ring
    exact mul_left_cancel₀ Real.pi_ne_zero hk'
  · rintro ⟨m, hm⟩
    have hcos : Real.cos (Real.pi * ((m : ℝ) + 1/2)) = 0 := by
      rw [show Real.pi * ((m : ℝ) + 1/2) = ((2 * (m : ℝ) + 1) * Real.pi) / 2 by ring]
      exact Real.cos_eq_zero_iff.mpr ⟨m, by push_cast; ring⟩
    rw [hu, hm, hcos, mul_zero]

/-! ## The Prüfer orbit as a function of the energy

We prove the facts needed by the Sturm counting: `E ↦ pruferIter α lam E n θ 0` is antitone
and continuous, tends to `0` at `+∞` and to `n` at `-∞`.
-/

/-- One Prüfer step of the orbit, in terms of `pot`. -/
theorem pruferIter_succ' (α lam θ E : ℝ) (n : ℕ) :
    pruferIter α lam E (n + 1) θ 0
      = pruferStep (E - pot α lam θ n) (pruferIter α lam E n θ 0) := by
  rw [pruferIter]
  rfl

/-- The Prüfer step at a fixed angle tends to its cell index as the potential value grows. -/
theorem pruferStep_tendsto_atTop (t : ℝ) :
    Tendsto (fun a : ℝ => pruferStep a t) atTop (nhds ((⌊t + 1 / 2⌋ : ℤ) : ℝ)) := by
  by_cases h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · have hev : ∀ᶠ a : ℝ in atTop, ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = pruferStep a t := by
      filter_upwards with a
      exact (Work.TMComp.RotBasics.pruferStep_eq_of_floor_special rfl h).symm
    have hconst : Tendsto (fun _ : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ)) atTop
        (nhds ((⌊t + 1 / 2⌋ : ℤ) : ℝ)) := tendsto_const_nhds
    exact hconst.congr' hev
  · have hc : Tendsto
        (fun a : ℝ => Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a)
        atTop atBot := by
      rw [tendsto_atBot]
      intro b
      filter_upwards [eventually_ge_atTop
        (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - b)] with a ha
      linarith
    have hlim : Tendsto
        (fun a : ℝ => Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a))
        atTop (nhds (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.comp hc).mono_right nhdsWithin_le_nhds
    have hev : ∀ᶠ a : ℝ in atTop,
        ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2
          + Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a) / Real.pi
          = pruferStep a t := by
      filter_upwards with a
      exact (Work.TMComp.RotBasics.pruferStep_eq_of_floor rfl h).symm
    have hconst : Tendsto (fun _ : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2) atTop
        (nhds (((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2)) := tendsto_const_nhds
    have hthis := hconst.add (hlim.div_const Real.pi)
    have hkey : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 + (-(Real.pi / 2)) / Real.pi
        = ((⌊t + 1 / 2⌋ : ℤ) : ℝ) := by
      field_simp
      ring
    rw [hkey] at hthis
    exact hthis.congr' hev

/-- The Prüfer step at a fixed angle (not on the exceptional branch) tends to the *next*
cell index as the potential value goes to `-∞`. -/
theorem pruferStep_tendsto_atBot (t : ℝ)
    (h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) ≠ -1 / 2) :
    Tendsto (fun a : ℝ => pruferStep a t) atBot (nhds (((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1)) := by
  have hc : Tendsto
      (fun a : ℝ => Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a)
      atBot atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_le_atBot
      (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - b)] with a ha
    linarith
  have hlim : Tendsto
      (fun a : ℝ => Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a))
      atBot (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp hc).mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ a : ℝ in atBot,
      ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2
        + Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a) / Real.pi
        = pruferStep a t := by
    filter_upwards with a
    exact (Work.TMComp.RotBasics.pruferStep_eq_of_floor rfl h).symm
  have hconst : Tendsto (fun _ : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2) atBot
      (nhds (((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2)) := tendsto_const_nhds
  have hthis := hconst.add (hlim.div_const Real.pi)
  have hkey : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 + (Real.pi / 2) / Real.pi
      = ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 := by
    field_simp
    ring
  rw [hkey] at hthis
  exact hthis.congr' hev

/-- The iterated Prüfer angle is continuous in the energy. -/
theorem pruferIter_continuous_E (α lam θ : ℝ) (n : ℕ) :
    Continuous (fun E : ℝ => pruferIter α lam E n θ 0) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hfun : (fun E : ℝ => pruferIter α lam E (n + 1) θ 0)
        = fun E : ℝ => pruferStep (E - pot α lam θ n) (pruferIter α lam E n θ 0) := by
      funext E
      exact pruferIter_succ' α lam θ E n
    rw [hfun]
    exact Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp
      ((continuous_id.sub continuous_const).prodMk ih)

/-- The iterated Prüfer angle is antitone in the energy. -/
theorem pruferIter_antitone_E (α lam θ : ℝ) (n : ℕ) :
    Antitone (fun E : ℝ => pruferIter α lam E n θ 0) := by
  induction n with
  | zero =>
    intro a b _
    simp [pruferIter]
  | succ n ih =>
    intro a b hab
    show pruferIter α lam b (n + 1) θ 0 ≤ pruferIter α lam a (n + 1) θ 0
    rw [pruferIter_succ' α lam θ b n, pruferIter_succ' α lam θ a n]
    exact le_trans (Work.TMComp.RotBasics.pruferStep_mono _ (ih hab))
      (Work.TMComp.RotBasics.pruferStep_antitone _ (by linarith))

/-- The floor of `n + c` for `0 ≤ c < 1`. -/
theorem floor_nat_add (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ⌊(n : ℝ) + c⌋ = (n : ℤ) := by
  rw [Int.floor_eq_iff]
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by simp
  constructor
  · rw [hcast]; linarith
  · rw [hcast]; linarith

/-- The iterated Prüfer angle tends to `0` as the energy goes to `+∞`. -/
theorem pruferIter_tendsto_atTop (α lam θ : ℝ) (n : ℕ) :
    Tendsto (fun E : ℝ => pruferIter α lam E n θ 0) atTop (nhds 0) := by
  induction n with
  | zero => simpa [pruferIter] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
  | succ n ih =>
    have ha : Tendsto (fun E : ℝ => E - pot α lam θ n) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop (b + pot α lam θ n)] with E hE
      linarith
    have hlo : Tendsto (fun E : ℝ => pruferStep (E - pot α lam θ n) (-(1 / 4)))
        atTop (nhds 0) := by
      have h2 := (pruferStep_tendsto_atTop (-(1 / 4))).comp ha
      have h3 : ((⌊-(1 / 4 : ℝ) + 1 / 2⌋ : ℤ) : ℝ) = 0 := by norm_num
      rwa [h3] at h2
    have hhi : Tendsto (fun E : ℝ => pruferStep (E - pot α lam θ n) (1 / 4))
        atTop (nhds 0) := by
      have h2 := (pruferStep_tendsto_atTop (1 / 4)).comp ha
      have h3 : ((⌊(1 / 4 : ℝ) + 1 / 2⌋ : ℤ) : ℝ) = 0 := by norm_num
      rwa [h3] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [ih.eventually
        (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-(1 / 4)) (1 / 4) by norm_num))]
        with E hE
      rw [pruferIter_succ' α lam θ E n]
      exact Work.TMComp.RotBasics.pruferStep_mono _ (le_of_lt hE.1)
    · filter_upwards [ih.eventually
        (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-(1 / 4)) (1 / 4) by norm_num))]
        with E hE
      rw [pruferIter_succ' α lam θ E n]
      exact Work.TMComp.RotBasics.pruferStep_mono _ (le_of_lt hE.2)

/-- The iterated Prüfer angle tends to `n` as the energy goes to `-∞`. -/
theorem pruferIter_tendsto_atBot (α lam θ : ℝ) (n : ℕ) :
    Tendsto (fun E : ℝ => pruferIter α lam E n θ 0) atBot (nhds (n : ℝ)) := by
  induction n with
  | zero => simpa [pruferIter] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atBot (nhds 0))
  | succ n ih =>
    have ha : Tendsto (fun E : ℝ => E - pot α lam θ n) atBot atBot := by
      rw [tendsto_atBot]
      intro b
      filter_upwards [eventually_le_atBot (b + pot α lam θ n)] with E hE
      linarith
    have hfl1 : ⌊(n : ℝ) - 1 / 4 + 1 / 2⌋ = (n : ℤ) := by
      have h := floor_nat_add n (c := 1 / 4) (by norm_num) (by norm_num)
      convert h using 2
      ring
    have hfl2 : ⌊(n : ℝ) + 1 / 4 + 1 / 2⌋ = (n : ℤ) := by
      have h := floor_nat_add n (c := 3 / 4) (by norm_num) (by norm_num)
      convert h using 2
      ring
    have hs1 : ((n : ℝ) - 1 / 4) - ((⌊(n : ℝ) - 1 / 4 + 1 / 2⌋ : ℤ) : ℝ) ≠ -1 / 2 := by
      rw [hfl1]; push_cast; norm_num
    have hs2 : ((n : ℝ) + 1 / 4) - ((⌊(n : ℝ) + 1 / 4 + 1 / 2⌋ : ℤ) : ℝ) ≠ -1 / 2 := by
      rw [hfl2]; push_cast; norm_num
    have hlo : Tendsto (fun E : ℝ => pruferStep (E - pot α lam θ n) ((n : ℝ) - 1 / 4))
        atBot (nhds ((n + 1 : ℕ) : ℝ)) := by
      have h2 := (pruferStep_tendsto_atBot ((n : ℝ) - 1 / 4) hs1).comp ha
      have h3 : (((⌊(n : ℝ) - 1 / 4 + 1 / 2⌋ : ℤ) : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by
        rw [hfl1]; push_cast; ring
      rwa [h3] at h2
    have hhi : Tendsto (fun E : ℝ => pruferStep (E - pot α lam θ n) ((n : ℝ) + 1 / 4))
        atBot (nhds ((n + 1 : ℕ) : ℝ)) := by
      have h2 := (pruferStep_tendsto_atBot ((n : ℝ) + 1 / 4) hs2).comp ha
      have h3 : (((⌊(n : ℝ) + 1 / 4 + 1 / 2⌋ : ℤ) : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by
        rw [hfl2]; push_cast; ring
      rwa [h3] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [ih.eventually
        (isOpen_Ioo.mem_nhds (show (n : ℝ) ∈ Set.Ioo ((n : ℝ) - 1 / 4) ((n : ℝ) + 1 / 4) by
          constructor <;> linarith))]
        with E hE
      rw [pruferIter_succ' α lam θ E n]
      exact Work.TMComp.RotBasics.pruferStep_mono _ (le_of_lt hE.1)
    · filter_upwards [ih.eventually
        (isOpen_Ioo.mem_nhds (show (n : ℝ) ∈ Set.Ioo ((n : ℝ) - 1 / 4) ((n : ℝ) + 1 / 4) by
          constructor <;> linarith))]
        with E hE
      rw [pruferIter_succ' α lam θ E n]
      exact Work.TMComp.RotBasics.pruferStep_mono _ (le_of_lt hE.2)

/-! ## The finite-volume eigenvalue count in a window

If `m` orthonormal vectors have residual at most `ε` for the eigenvalue `E` of a Hermitian
matrix `A`, then at least `m (1 - (ε/ε')²)` eigenvalues of `A` lie in `[E - ε', E + ε']`.

We work over the coordinate space `Fin n → ℂ` with the ℓ²-type form `dotC` (the space
`Fin n → ℂ` carries the sup norm in Mathlib, so no inner-product API is available) and use
the eigenvector unitary of `A`.
-/

/-- The sesquilinear form `∑ k, conj (x k) * y k` on `Fin n → ℂ`, linear in the second
variable. -/
def dotC {n : ℕ} (x y : Fin n → ℂ) : ℂ := ∑ k, (starRingEnd ℂ) (x k) * y k

theorem dotC_self_eq {n : ℕ} (x : Fin n → ℂ) :
    dotC x x = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotC]
  push_cast
  exact Finset.sum_congr rfl fun k _ => by
    rw [Complex.normSq_eq_conj_mul_self.symm, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem dotC_self_re_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ (dotC x x).re := by
  rw [dotC_self_eq]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- Unitarity of `dotC`: a unitary matrix preserves it. -/
theorem dotC_star_mul_mulVec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : star U * U = 1)
    (x y : Fin n → ℂ) : dotC (Matrix.mulVec U x) (Matrix.mulVec U y) = dotC x y := by
  simp only [dotC, Matrix.mulVec, dotProduct]
  have hconj : ∀ k, (starRingEnd ℂ) (∑ i, U k i * x i)
      = ∑ i, (starRingEnd ℂ) (U k i) * (starRingEnd ℂ) (x i) := by
    intro k
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
  simp only [hconj]
  have step1 : ∀ k, (∑ i, (starRingEnd ℂ) (U k i) * (starRingEnd ℂ) (x i)) * (∑ j, U k j * y j)
      = ∑ i, ∑ j, ((starRingEnd ℂ) (U k i) * (starRingEnd ℂ) (x i)) * (U k j * y j) := by
    intro k
    rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun k _ => step1 k, Finset.sum_comm]
  have step2 : ∀ i, (∑ k, ∑ j, ((starRingEnd ℂ) (U k i) * (starRingEnd ℂ) (x i)) * (U k j * y j))
      = ∑ j, (∑ k, (starRingEnd ℂ) (U k i) * U k j) * ((starRingEnd ℂ) (x i) * y j) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i _ => step2 i]
  have step3 : ∀ i j, (∑ k, (starRingEnd ℂ) (U k i) * U k j) = (star U * U) i j := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  simp only [step3, hU]
  simp only [Matrix.one_apply]
  rw [show (∑ i, ∑ j, (if i = j then (1 : ℂ) else 0) * ((starRingEnd ℂ) (x i) * y j))
      = ∑ i, (starRingEnd ℂ) (x i) * y i from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j, (if i = j then (1 : ℂ) else 0) * ((starRingEnd ℂ) (x i) * y j))
        = ∑ j, if j = i then ((starRingEnd ℂ) (x i) * y j) else 0 from
      Finset.sum_congr rfl fun j _ => by
        rw [show (if i = j then (1 : ℂ) else 0) * ((starRingEnd ℂ) (x i) * y j)
            = if j = i then ((starRingEnd ℂ) (x i) * y j) else 0 from by
          by_cases h : i = j
          · subst h; simp
          · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]]]
    rw [Finset.sum_ite_eq']
    simp]

/-- The Fourier transform `x ↦ star U *ᵥ x` for a unitary `U` is an isometry for `dotC`. -/
theorem dotC_fourier {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : star U * U = 1)
    (hU' : U * star U = 1) (x y : Fin n → ℂ) :
    dotC (Matrix.mulVec (star U) x) (Matrix.mulVec (star U) y) = dotC x y := by
  refine dotC_star_mul_mulVec (star U) ?_ x y
  rw [star_star]
  exact hU'

/-- Entries of a diagonal matrix acting on a vector. -/
theorem diagonal_mulVec_apply {n : ℕ} (d v : Fin n → ℂ) :
    (Matrix.mulVec (Matrix.diagonal d) v) = fun k => d k * v k := by
  funext k
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (fun h => hj h.symm), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The finite-volume eigenvalue count in a window: if `m` orthonormal vectors have
residual at most `ε` for the eigenvalue `E` of a Hermitian matrix `A`, then at least
`m (1 - (ε/ε')²)` eigenvalues of `A` lie in `[E - ε', E + ε']`. -/
theorem window_mine {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    {E ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 < ε') {m : ℕ} (ψ : Fin m → Fin n → ℂ)
    (horth : ∀ i j : Fin m,
      (∑ k : Fin n, ψ i k * (starRingEnd ℂ) (ψ j k)) = if i = j then 1 else 0)
    (hres : ∀ i : Fin m,
      (∑ k : Fin n, ‖(Matrix.mulVec A (ψ i)) k - E * ψ i k‖ ^ 2) ≤ ε ^ 2) :
    ((Finset.univ.filter (fun k : Fin n => |hA.eigenvalues k - E| ≤ ε')).card : ℝ)
      ≥ (m : ℝ) * (1 - (ε / ε') ^ 2) := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set lam : Fin n → ℝ := hA.eigenvalues with hlamdef
  have hU1 : star U * U = 1 := hA.eigenvectorUnitary.2.1
  have hU2 : U * star U = 1 := hA.eigenvectorUnitary.2.2
  have hspec : A = U * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ)) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← hUdef] at h
    have hlam : (RCLike.ofReal ∘ hA.eigenvalues) = fun k => ((lam k : ℝ) : ℂ) := by
      funext k
      simp only [Function.comp_apply, hlamdef]
      rfl
    rw [hlam] at h
    exact h
  -- the action of `A` in the Fourier coordinates
  have hAact : ∀ x : Fin n → ℂ, Matrix.mulVec A x = Matrix.mulVec U
      (fun k => ((lam k : ℝ) : ℂ) * (Matrix.mulVec (star U) x) k) := by
    intro x
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagonal_mulVec_apply]
  -- the Fourier norm identity
  have hFourierNorm : ∀ x : Fin n → ℂ,
      (∑ k, ‖(Matrix.mulVec (star U) x) k‖ ^ 2) = ∑ k, ‖x k‖ ^ 2 := by
    intro x
    have h := dotC_fourier U hU1 hU2 x x
    rw [dotC_self_eq (Matrix.mulVec (star U) x), dotC_self_eq x] at h
    exact_mod_cast h
  have hFourierNormU : ∀ x : Fin n → ℂ,
      (∑ k, ‖(Matrix.mulVec U x) k‖ ^ 2) = ∑ k, ‖x k‖ ^ 2 := by
    intro x
    have h := dotC_star_mul_mulVec U hU1 x x
    rw [dotC_self_eq (Matrix.mulVec U x), dotC_self_eq x] at h
    exact_mod_cast h
  -- the residual in Fourier coordinates
  have hresid : ∀ i : Fin m,
      (∑ k, (lam k - E) ^ 2 * ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2) ≤ ε ^ 2 := by
    intro i
    set w : Fin n → ℂ := Matrix.mulVec (star U) (ψ i) with hw
    have h2 : Matrix.mulVec U (E • w) = E • ψ i := by
      rw [Matrix.mulVec_smul, hw, Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
    have h3 : Matrix.mulVec A (ψ i) - E • ψ i
        = Matrix.mulVec U (fun k => (((lam k - E : ℝ)) : ℂ) * w k) := by
      rw [hAact (ψ i), ← h2, ← Matrix.mulVec_sub]
      congr 1
      funext k
      simp only [Pi.sub_apply, Pi.smul_apply, hw, Complex.real_smul, ← sub_mul]
      push_cast
      ring
    have h5a : (∑ k, ‖(Matrix.mulVec A (ψ i) - E • ψ i) k‖ ^ 2)
        = ∑ k, (lam k - E) ^ 2 * ‖w k‖ ^ 2 := by
      rw [h3, hFourierNormU (fun k => (((lam k - E : ℝ)) : ℂ) * w k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
    have h5b : (∑ k, ‖(Matrix.mulVec A (ψ i)) k - E * ψ i k‖ ^ 2)
        = ∑ k, ‖(Matrix.mulVec A (ψ i) - E • ψ i) k‖ ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    exact (le_of_eq (h5b.trans h5a).symm).trans (hres i)
  -- Bessel: each column of the Fourier matrix has squared norm at most one
  have hdotC : ∀ i j : Fin m, dotC (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    have hdot : dotC (ψ i) (ψ j)
        = (starRingEnd ℂ) (∑ k, ψ i k * (starRingEnd ℂ) (ψ j k)) := by
      rw [dotC, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; simp
    rw [hdot, horth i j]
    by_cases hij : i = j <;> simp [hij]
  have hcol : ∀ k : Fin n,
      (∑ i : Fin m, ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2) ≤ 1 := by
    intro k
    set w : Fin m → Fin n → ℂ := fun i => Matrix.mulVec (star U) (ψ i) with hwdef
    have hdotw : ∀ i j : Fin m, dotC (w i) (w j) = if i = j then 1 else 0 := by
      intro i j
      have h : dotC (Matrix.mulVec (star U) (ψ i)) (Matrix.mulVec (star U) (ψ j))
          = dotC (ψ i) (ψ j) := dotC_fourier U hU1 hU2 (ψ i) (ψ j)
      have h2 : dotC (w i) (w j) = dotC (ψ i) (ψ j) := h
      rw [h2, hdotC i j]
    set x : Fin m → ℂ := fun i => (starRingEnd ℂ) (w i k) with hxdef
    have hxn : ∀ i : Fin m, ‖x i‖ ^ 2 = ‖w i k‖ ^ 2 := by
      intro i
      show ‖star (w i k)‖ ^ 2 = ‖w i k‖ ^ 2
      rw [norm_star]
    set z : Fin n → ℂ := fun j => ∑ i, x i * w i j with hzdef
    have hzk : z k = ((∑ i : Fin m, ‖w i k‖ ^ 2 : ℝ) : ℂ) := by
      rw [hzdef]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hxdef]
      show (starRingEnd ℂ) (w i k) * w i k = ((↑‖w i k‖ : ℂ)) ^ 2
      rw [show (starRingEnd ℂ) (w i k) * w i k = ((Complex.normSq (w i k) : ℝ) : ℂ) from
        Complex.normSq_eq_conj_mul_self.symm,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hzz : dotC z z = ((∑ i : Fin m, ‖w i k‖ ^ 2 : ℝ) : ℂ) := by
      have step : dotC z z = ∑ i : Fin m, ∑ i' : Fin m,
          ((starRingEnd ℂ) (x i) * x i') * dotC (w i) (w i') := by
        rw [dotC]
        have h1 : (∑ j : Fin n, (starRingEnd ℂ) (z j) * z j)
            = ∑ j : Fin n, ∑ i : Fin m, ∑ i' : Fin m,
                ((starRingEnd ℂ) (x i) * x i') * ((starRingEnd ℂ) (w i j) * w i' j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hzdef, map_sum]
          simp only [map_mul]
          rw [show (∑ i, (starRingEnd ℂ) (x i) * (starRingEnd ℂ) (w i j))
                * (∑ i', x i' * w i' j)
              = ∑ i, ∑ i', ((starRingEnd ℂ) (x i) * (starRingEnd ℂ) (w i j))
                  * (x i' * w i' j) from Finset.sum_mul_sum _ _ _ _]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun i' _ => by ring
        rw [h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [show (∑ j, ((starRingEnd ℂ) (x i) * x i')
              * ((starRingEnd ℂ) (w i j) * w i' j))
            = ((starRingEnd ℂ) (x i) * x i') * dotC (w i) (w i') from by
          rw [dotC, Finset.mul_sum]]
      rw [step]
      have step2 : (∑ i : Fin m, ∑ i' : Fin m,
            ((starRingEnd ℂ) (x i) * x i') * dotC (w i) (w i'))
          = ∑ i : Fin m, ((starRingEnd ℂ) (x i) * x i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ i', ((starRingEnd ℂ) (x i) * x i') * dotC (w i) (w i'))
            = ∑ i', if i' = i then ((starRingEnd ℂ) (x i) * x i') else 0 from by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [hdotw i i']
          by_cases h : i = i'
          · subst h; simp
          · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]]
        rw [Finset.sum_ite_eq']
        simp
      rw [step2]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (starRingEnd ℂ) (x i) * x i = ((Complex.normSq (x i) : ℝ) : ℂ) from
        Complex.normSq_eq_conj_mul_self.symm,
        Complex.normSq_eq_norm_sq, hxn i, Complex.ofReal_pow]
    have hSnn : (0 : ℝ) ≤ ∑ i : Fin m, ‖w i k‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hre : (dotC z z).re = ∑ i : Fin m, ‖w i k‖ ^ 2 := by
      rw [hzz, Complex.ofReal_re]
    have hzk_sq : ‖z k‖ ^ 2 = (∑ i : Fin m, ‖w i k‖ ^ 2 : ℝ) ^ 2 := by
      rw [hzk, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hle1 : (∑ i : Fin m, ‖w i k‖ ^ 2 : ℝ) ^ 2 ≤ ∑ i : Fin m, ‖w i k‖ ^ 2 := by
      rw [← hzk_sq, ← hre]
      rw [show (dotC z z).re = (∑ k', ‖z k'‖ ^ 2 : ℝ) from by
        rw [dotC_self_eq, Complex.ofReal_re]]
      exact Finset.single_le_sum (f := fun k' : Fin n => ‖z k'‖ ^ 2)
        (fun k' _ => sq_nonneg _) (Finset.mem_univ k)
    have hfinal : (∑ i : Fin m, ‖w i k‖ ^ 2 : ℝ) ≤ 1 := by
      nlinarith [hle1, hSnn]
    convert hfinal using 2
  -- the counting
  have hrow : ∀ i : Fin m,
      (∑ k ∈ (Finset.univ : Finset (Fin n)), ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2) = 1 := by
    intro i
    rw [show (∑ k ∈ (Finset.univ : Finset (Fin n)), ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2)
        = ∑ k, ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2 from by simp,
      hFourierNorm (ψ i)]
    have h := dotC_self_eq (ψ i)
    have h2 := hdotC i i
    rw [h2, if_pos rfl] at h
    exact_mod_cast h.symm
  set T : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => |lam k - E| ≤ ε') with hTdef
  set B : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => ¬ (|lam k - E| ≤ ε')) with hBdef
  set c : Fin m → Fin n → ℝ := fun i k => ‖(Matrix.mulVec (star U) (ψ i)) k‖ ^ 2 with hcdef
  have hcompl : ∀ i : Fin m, (∑ k ∈ B, c i k) ≤ (ε / ε') ^ 2 := by
    intro i
    have h2 : ∀ k ∈ B, c i k * ε' ^ 2 ≤ (lam k - E) ^ 2 * c i k := by
      intro k hk
      rw [hBdef, Finset.mem_filter] at hk
      have h3 : ε' < |lam k - E| := lt_of_not_ge hk.2
      have h4 : ε' ^ 2 ≤ (lam k - E) ^ 2 := by
        rw [← sq_abs (lam k - E)]
        exact pow_le_pow_left₀ hε'.le h3.le 2
      have h5 : 0 ≤ c i k := by rw [hcdef]; positivity
      calc c i k * ε' ^ 2 ≤ c i k * (lam k - E) ^ 2 := mul_le_mul_of_nonneg_left h4 h5
        _ = (lam k - E) ^ 2 * c i k := by ring
    have h6 : (∑ k ∈ B, c i k * ε' ^ 2) ≤ ∑ k ∈ B, (lam k - E) ^ 2 * c i k :=
      Finset.sum_le_sum h2
    have h8 : (∑ k ∈ B, (lam k - E) ^ 2 * c i k) ≤ ε ^ 2 := by
      have h9 : (∑ k ∈ B, (lam k - E) ^ 2 * c i k)
          ≤ ∑ k, (lam k - E) ^ 2 * c i k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k _ => Finset.mem_univ k) ?_
        intro k _ _
        rw [hcdef]; positivity
      rw [hcdef] at h9
      exact le_trans h9 (hresid i)
    have h10 : (∑ k ∈ B, c i k) * ε' ^ 2 ≤ ε ^ 2 := by
      rw [Finset.sum_mul]
      exact le_trans h6 h8
    have h11 : (0 : ℝ) < ε' ^ 2 := by positivity
    have h10' : (∑ k ∈ B, c i k) ≤ ε ^ 2 / ε' ^ 2 := by
      rw [le_div_iff₀ h11]
      exact h10
    rw [div_pow]
    exact h10'
  have hwin : ∀ i : Fin m, 1 - (ε / ε') ^ 2 ≤ ∑ k ∈ T, c i k := by
    intro i
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun k : Fin n => |lam k - E| ≤ ε') (fun k => c i k)
    have hT : (∑ k ∈ T, c i k)
        = ∑ k ∈ Finset.univ.filter (fun k : Fin n => |lam k - E| ≤ ε'), c i k := by rw [hTdef]
    have hB : (∑ k ∈ B, c i k)
        = ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (|lam k - E| ≤ ε')), c i k := by
      rw [hBdef]
    have htot : (∑ k ∈ (Finset.univ : Finset (Fin n)), c i k) = 1 := hrow i
    linarith [hT, hB, htot, hsplit, hcompl i]
  have hsum1 : (m : ℝ) * (1 - (ε / ε') ^ 2) ≤ ∑ i : Fin m, ∑ k ∈ T, c i k := by
    have h1 : (m : ℝ) * (1 - (ε / ε') ^ 2)
        = ∑ _i : Fin m, (1 - (ε / ε') ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h1]
    exact Finset.sum_le_sum fun i _ => hwin i
  have hsum2 : (∑ i : Fin m, ∑ k ∈ T, c i k) = ∑ k ∈ T, ∑ i : Fin m, c i k :=
    Finset.sum_comm
  have hsum3 : (∑ k ∈ T, ∑ i : Fin m, c i k) ≤ ∑ _k ∈ T, (1 : ℝ) := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hcdef]
    exact hcol k
  have hfinal : (m : ℝ) * (1 - (ε / ε') ^ 2) ≤ (T.card : ℝ) := by
    calc (m : ℝ) * (1 - (ε / ε') ^ 2) ≤ ∑ i : Fin m, ∑ k ∈ T, c i k := hsum1
      _ = ∑ k ∈ T, ∑ i : Fin m, c i k := hsum2
      _ ≤ ∑ _k ∈ T, (1 : ℝ) := hsum3
      _ = (T.card : ℝ) := by simp
  have hgoal : ((Finset.univ.filter (fun k : Fin n => |lam k - E| ≤ ε')).card : ℝ)
      ≥ (m : ℝ) * (1 - (ε / ε') ^ 2) := by
    rw [← hTdef]
    exact hfinal
  have hfilter : ((Finset.univ.filter (fun k : Fin n => |lam k - E| ≤ ε')).card : ℝ)
      = ((Finset.univ.filter (fun k : Fin n => |hA.eigenvalues k - E| ≤ ε')).card : ℝ) := by
    refine congrArg (fun s : Finset (Fin n) => (s.card : ℝ)) ?_
    apply Finset.filter_congr
    intro k _
    rw [hlamdef]
  rw [hfilter]
  exact hgoal

/-- Per-phase finite-volume eigenvalue count in a window: if `V` is a set of `R`-separated
shifts satisfying the phase condition `fracDist (θ + j α) < δ` (and such that the shifted
support stays inside the box), then the box at phase `θ` has at least `3 |V| / 4`
eigenvalues in the window `[E - εW, E + εW]`. -/
theorem window_count_theta {α lam E θ : ℝ} {n R : ℕ} {φ : ℤ → ℂ} {εc εW δ : ℝ}
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0)
    (hnorm : (∑' m : ℤ, ‖φ m‖ ^ 2) = 1)
    (hres : (∑' m : ℤ, ‖amoAct α lam 0 φ m - (E : ℂ) * φ m‖ ^ 2) ≤ εc ^ 2)
    (V : Finset ℤ)
    (hV : ∀ j ∈ V, (R : ℤ) ≤ j + 1 ∧ j + (R : ℤ) + 1 ≤ (n : ℤ) ∧
      fracDist (θ + (j : ℝ) * α) < δ)
    (hVsep : ∀ i ∈ V, ∀ j' ∈ V, i ≠ j' → 2 * (R : ℤ) - 1 ≤ |i - j'|)
    (hεc : 0 ≤ εc) (hδ0 : 0 ≤ δ) (hεW : 0 < εW)
    (hεres : εc + 4 * Real.pi * |lam| * δ ≤ εW / 2) :
    3 * (V.card : ℝ) / 4 ≤
      ((Finset.univ.filter (fun k : Fin n => |boxEig α lam θ n k - E| ≤ εW)).card : ℝ) := by
  set e : Fin V.card ↪o ℤ := V.orderEmbOfFin (rfl : V.card = V.card) with he
  have hemem : ∀ i : Fin V.card, e i ∈ V := fun i => V.orderEmbOfFin_mem _ i
  have hshift : ∀ (j : ℤ), (R : ℤ) ≤ j + 1 → j + (R : ℤ) + 1 ≤ (n : ℤ) →
      fracDist (θ + (j : ℝ) * α) < δ →
      ((∑ k : Fin n, ‖(Matrix.mulVec (Jbox α lam θ n) (shiftVec φ j n)) k
          - (E : ℂ) * shiftVec φ j n k‖ ^ 2) ≤ (εc + 4 * Real.pi * |lam| * δ) ^ 2 ∧
        (∑ k : Fin n, ‖shiftVec φ j n k‖ ^ 2) = 1 ∧
        (∀ i j' : ℤ, i ≠ j' → 2 * (R : ℤ) - 1 ≤ |i - j'| →
          (∑ k : Fin n, shiftVec φ i n k * (starRingEnd ℂ) (shiftVec φ j' n k)) = 0)) :=
    fun j hj hj2 hp => Work.TMComp.IDSBox.shift_fixed α lam E φ hsupp hnorm hεc hres θ n j hj hj2
      hδ0 hp
  have horth : ∀ i j : Fin V.card,
      (∑ k : Fin n, shiftVec φ (e i) n k * (starRingEnd ℂ) (shiftVec φ (e j) n k))
        = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h1 := (hshift (e i) (hV _ (hemem i)).1 (hV _ (hemem i)).2.1
        (hV _ (hemem i)).2.2).2.1
      have hcast : (∑ x : Fin n, shiftVec φ (e i) n x * (starRingEnd ℂ) (shiftVec φ (e i) n x))
          = (((∑ x : Fin n, ‖shiftVec φ (e i) n x‖ ^ 2 : ℝ)) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [hcast, h1, Complex.ofReal_one]
    · rw [if_neg hij]
      have hne : e i ≠ e j := fun h => hij (e.injective h)
      exact (hshift (e i) (hV _ (hemem i)).1 (hV _ (hemem i)).2.1
        (hV _ (hemem i)).2.2).2.2 (e i) (e j) hne
        (hVsep _ (hemem i) _ (hemem j) hne)
  have hresV : ∀ i : Fin V.card,
      (∑ k : Fin n, ‖(Matrix.mulVec (Jbox α lam θ n) (shiftVec φ (e i) n)) k
        - (E : ℂ) * shiftVec φ (e i) n k‖ ^ 2)
        ≤ (εc + 4 * Real.pi * |lam| * δ) ^ 2 := by
    intro i
    exact (hshift (e i) (hV _ (hemem i)).1 (hV _ (hemem i)).2.1 (hV _ (hemem i)).2.2).1
  have hwin : (V.card : ℝ) * (1 - ((εc + 4 * Real.pi * |lam| * δ) / εW) ^ 2)
      ≤ ((Finset.univ.filter (fun k : Fin n =>
          |(isHermitian_Jbox α lam θ n).eigenvalues k - E| ≤ εW)).card : ℝ) :=
    Work.TMComp.IDSBox.window (Jbox α lam θ n) (isHermitian_Jbox α lam θ n)
      (E := E) (ε := εc + 4 * Real.pi * |lam| * δ) (ε' := εW)
      (by
        have h4 : (0 : ℝ) ≤ 4 * Real.pi * |lam| * δ :=
          mul_nonneg (mul_nonneg (by positivity) (abs_nonneg lam)) hδ0
        linarith) hεW
      (fun i => shiftVec φ (e i) n) horth hresV
  have hratio : ((εc + 4 * Real.pi * |lam| * δ) / εW) ^ 2 ≤ 1 / 4 := by
    have h1 : (εc + 4 * Real.pi * |lam| * δ) / εW ≤ 1 / 2 := by
      rw [div_le_iff₀ hεW]
      linarith
    have h2 : 0 ≤ (εc + 4 * Real.pi * |lam| * δ) / εW := by
      apply div_nonneg _ (le_of_lt hεW)
      have hp : (0 : ℝ) ≤ 4 * Real.pi * |lam| * δ := by positivity
      linarith
    have hmul := mul_self_le_mul_self h2 h1
    nlinarith [hmul]
  have hmono : (1 : ℝ) - 1 / 4 ≤ 1 - ((εc + 4 * Real.pi * |lam| * δ) / εW) ^ 2 := by
    linarith [hratio]
  have h3 : (V.card : ℝ) * (1 - 1 / 4)
      ≤ ((Finset.univ.filter (fun k : Fin n =>
          |(isHermitian_Jbox α lam θ n).eigenvalues k - E| ≤ εW)).card : ℝ) := by
    calc (V.card : ℝ) * (1 - 1 / 4)
        ≤ (V.card : ℝ) * (1 - ((εc + 4 * Real.pi * |lam| * δ) / εW) ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ _ := hwin
  have hboxEig : boxEig α lam θ n = (isHermitian_Jbox α lam θ n).eigenvalues := rfl
  rw [hboxEig]
  linarith

theorem prove_IDSSpectrum : Work.TMContract.P_IDSSpectrum := by
  intro α lam hα E hE ε hε
  obtain ⟨H, hH, hspec⟩ := hE
  -- ### 1. A finitely supported approximate eigenvector of `H` at phase `0`.
  obtain ⟨R₀, φ, hsupp₀, hnorm, hresφ⟩ :=
    Work.TMComp.IDSSpec.kernel α lam H hH E hspec (ε := ε / 8) (by positivity)
  set R : ℕ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0 :=
    fun m hm => hsupp₀ m (le_trans (le_max_left _ _) hm)
  -- ### 2. The phase window `δ`.
  set δ : ℝ := min (1 / 2) (ε / (8 * (4 * Real.pi * |lam| + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδres : 4 * Real.pi * |lam| * δ ≤ ε / 8 := by
    have hle : δ ≤ ε / (8 * (4 * Real.pi * |lam| + 1)) := min_le_right _ _
    have hpos : (0 : ℝ) < 8 * (4 * Real.pi * |lam| + 1) := by positivity
    calc 4 * Real.pi * |lam| * δ
        ≤ 4 * Real.pi * |lam| * (ε / (8 * (4 * Real.pi * |lam| + 1))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ ε / 8 := by
          rw [mul_div_assoc', div_le_iff₀ hpos]
          nlinarith [abs_nonneg lam, Real.pi_pos, le_of_lt hε]
  -- ### 3. The equidistribution threshold, with `η := δ`.
  obtain ⟨Nc, hNc⟩ := Work.TMComp.IDSEqui.count (((2 * R : ℕ)) * α)
    (hα.natCast_mul (by omega : (2 * R : ℕ) ≠ 0)) δ hδ0 hδhalf δ hδ0
  -- ### 4. Parameters.
  obtain ⟨ce, hce⟩ : ∃ ce : ℕ, 28 / (3 * δ) + 3 ≤ (ce : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_ge (28 / (3 * δ) + 3)
    exact ⟨k, hk⟩
  set m₀ : ℕ := Nc + ce + R + 3 with hm₀def
  set n : ℕ := m₀ * (2 * R + 1) + 3 with hndef
  have hn1 : 1 ≤ n := by omega
  have hm₀Nc : Nc ≤ m₀ := by omega
  have hm₀R : R ≤ m₀ := by omega
  have hm₀big : 28 / (3 * δ) + 3 ≤ (m₀ : ℝ) := by
    have h2 : (ce : ℝ) ≤ (m₀ : ℝ) := by
      have : ce ≤ m₀ := by omega
      exact_mod_cast this
    linarith [hce]
  -- ### 5. Sturm oscillation: the box eigenvalue count is `n - Prüfer angle` up to `2`.
  have hSturm : ∀ θ X : ℝ,
      |(boxCount α lam θ X n : ℝ) - ((n : ℝ) - pruferIter α lam X n θ 0)| ≤ 2 := by
    intro θ X
    have hroot : ∀ E : ℝ, (jacPoly α lam θ n).eval E = 0 ↔
        ∃ m : ℤ, pruferIter α lam E n θ 0 = m + 1/2 := by
      intro E
      rw [eval_jacPoly]
      exact uSeq_eq_zero_iff α lam θ E n (Work.TMComp.IDSPrufer.dir α lam θ E n)
    have hch := Work.TMComp.IDSBox.charpoly α lam θ n
    have horb : Antitone (fun E : ℝ => pruferIter α lam E n θ 0) ∧
        Continuous (fun E : ℝ => pruferIter α lam E n θ 0) ∧
        Filter.Tendsto (fun E : ℝ => pruferIter α lam E n θ 0) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun E : ℝ => pruferIter α lam E n θ 0) Filter.atBot (nhds (n : ℝ)) :=
      ⟨pruferIter_antitone_E α lam θ n, pruferIter_continuous_E α lam θ n,
        pruferIter_tendsto_atTop α lam θ n, pruferIter_tendsto_atBot α lam θ n⟩
    have hrc := Work.TMComp.IDSBox.rootcount α lam θ n horb.2.1 horb.1 horb.2.2.1 horb.2.2.2
      hch.2.1 hch.2.2 hroot X
    have heg := Work.TMComp.IDSBox.eigroot (Jbox α lam θ n) (isHermitian_Jbox α lam θ n)
      (jacPoly α lam θ n) hch.1 X
    have hbc : (boxCount α lam θ X n : ℝ)
        = (((jacPoly α lam θ n).roots.filter (fun r => r < X)).card : ℝ) := by
      simp only [boxCount, boxEig]
      exact heg
    rw [hbc]
    exact hrc
  -- ### 6. Per-phase bound.
  have hpoint : ∀ θ : ℝ, 3 * δ * (m₀ : ℝ) / 4 - 4 ≤
      pruferIter α lam (E - ε) n θ 0 - pruferIter α lam (E + ε) n θ 0 := by
    intro θ
    let ιn : Fin m₀ → ℕ := fun i => R * (2 * (1 + (i : ℕ)))
    let ι : Fin m₀ → ℤ := fun i => (ιn i : ℤ)
    have hidxZ : ∀ i : Fin m₀, ι i = (R : ℤ) * (2 * (1 + (i : ℤ))) := by
      intro i
      simp only [ι, ιn]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hidxR : ∀ i : Fin m₀, ((ι i : ℤ) : ℝ) = (R : ℝ) * (2 * (1 + (i : ℝ))) := by
      intro i
      simp only [ι, ιn]
      rw [Int.cast_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    have hιinj : Function.Injective ι := by
      intro a b hab
      have h1 : R * (2 * (1 + (a : ℕ))) = R * (2 * (1 + (b : ℕ))) := by
        have h := hab
        simp only [ι, ιn] at h
        exact_mod_cast h
      have hRpos : 0 < R := by omega
      have h2 : 2 * (1 + (a : ℕ)) = 2 * (1 + (b : ℕ)) := Nat.eq_of_mul_eq_mul_left hRpos h1
      exact Fin.ext (by omega)
    set W : Finset (Fin m₀) :=
      Finset.univ.filter (fun i => fracDist (θ + ((ι i : ℤ) : ℝ) * α) < δ) with hWdef
    set V : Finset ℤ := W.image ι with hVdef
    -- the phase condition, written for `shiftCount`
    have hWeq : W = Finset.univ.filter
        (fun i : Fin m₀ => fracDist ((θ + ((2 * R : ℕ) : ℝ) * α) + (i : ℝ) * (((2 * R : ℕ) : ℝ) * α)) < δ) := by
      apply Finset.filter_congr
      intro i _
      have harg : ((ι i : ℤ) : ℝ) * α
          = (((2 * R : ℕ) : ℝ) * α) + (i : ℝ) * (((2 * R : ℕ) : ℝ) * α) := by
        rw [hidxR i]
        push_cast
        ring
      rw [harg]
      ring_nf
    have hWcount : δ * (m₀ : ℝ) ≤ (W.card : ℝ) := by
      have h := hNc m₀ hm₀Nc (θ + ((2 * R : ℕ) : ℝ) * α)
      rw [hWeq]
      have hsc : shiftCount (((2 * R : ℕ) : ℝ) * α) (θ + ((2 * R : ℕ) : ℝ) * α) δ m₀
          = (Finset.univ.filter (fun i : Fin m₀ =>
              fracDist ((θ + ((2 * R : ℕ) : ℝ) * α) + (i : ℝ) * (((2 * R : ℕ) : ℝ) * α)) < δ)).card
          := rfl
      rw [← hsc]
      linarith
    have hVcard : 3 * δ * (m₀ : ℝ) / 4 ≤ 3 * (V.card : ℝ) / 4 := by
      have hcard : (V.card : ℝ) = (W.card : ℝ) := by
        rw [hVdef]
        exact_mod_cast Finset.card_image_of_injective (f := ι) W hιinj
      rw [hcard]
      linarith [hWcount]
    -- the hypotheses on `V`
    have hVcond : ∀ j ∈ V, (R : ℤ) ≤ j + 1 ∧ j + (R : ℤ) + 1 ≤ (n : ℤ) ∧
        fracDist (θ + (j : ℝ) * α) < δ := by
      intro j hj
      rw [hVdef, Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [hWdef, Finset.mem_filter] at hi
      have hphase : fracDist (θ + ((ι i : ℤ) : ℝ) * α) < δ := hi.2
      have hi0 : (0 : ℤ) ≤ (i : ℤ) := by omega
      have hRpos : (0 : ℤ) < (R : ℤ) := by omega
      have hjge : (R : ℤ) ≤ ι i + 1 := by
        rw [hidxZ i]
        nlinarith [hRpos, hi0]
      have hjle : ι i + (R : ℤ) + 1 ≤ (n : ℤ) := by
        have hNat : R * (2 * (1 + (i : ℕ))) + R + 1 ≤ n := by
          have h1 : R * (2 * (1 + (i : ℕ))) ≤ R * (2 * m₀) :=
            Nat.mul_le_mul_left R (by omega)
          have hRle : R ≤ m₀ := by omega
          rw [hndef]
          calc R * (2 * (1 + (i : ℕ))) + R + 1 ≤ R * (2 * m₀) + R + 1 := by omega
            _ ≤ m₀ * (2 * R + 1) + 3 := by
                have hmul : m₀ * (2 * R + 1) = R * (2 * m₀) + m₀ := by ring
                rw [hmul]
                omega
        have hcast : ι i = ((R * (2 * (1 + (i : ℕ))) : ℕ) : ℤ) := rfl
        rw [hcast]
        exact_mod_cast hNat
      exact ⟨hjge, hjle, hphase⟩
    have hVsep : ∀ i ∈ V, ∀ j' ∈ V, i ≠ j' → 2 * (R : ℤ) - 1 ≤ |i - j'| := by
      intro i hi j' hj' hne
      rw [hVdef, Finset.mem_image] at hi hj'
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, rfl⟩ := hj'
      have hab : a ≠ b := by
        intro habs
        exact hne (by rw [habs])
      have hR0 : (0 : ℤ) ≤ (R : ℤ) := by omega
      have hstep : (R : ℤ) * (2 * (1 + (a : ℤ))) - (R : ℤ) * (2 * (1 + (b : ℤ)))
          = (R : ℤ) * (2 * ((a : ℤ) - (b : ℤ))) := by ring
      have habs : |(R : ℤ) * (2 * ((a : ℤ) - (b : ℤ)))|
          = (2 * (R : ℤ)) * |(a : ℤ) - (b : ℤ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hR0,
          abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
        ring
      rw [hidxZ a, hidxZ b, hstep, habs]
      have hne' : (a : ℤ) ≠ (b : ℤ) := fun h => hab (Fin.ext (by exact_mod_cast h))
      have hne0 : (a : ℤ) - (b : ℤ) ≠ 0 := sub_ne_zero.mpr hne'
      have h1 : (1 : ℤ) ≤ |(a : ℤ) - (b : ℤ)| := by
        have := abs_pos.mpr hne0
        omega
      nlinarith [h1, hR0]
    -- the finite-volume window count
    have hεc : (0 : ℝ) ≤ ε / 8 := by positivity
    have hεW : (0 : ℝ) < ε / 2 := by positivity
    have hεres : ε / 8 + 4 * Real.pi * |lam| * δ ≤ (ε / 2) / 2 := by linarith
    have hwin := window_count_theta (α := α) (lam := lam) (E := E) (θ := θ) (n := n) (R := R)
      (φ := φ) (εc := ε / 8) (εW := ε / 2) (δ := δ)
      hsupp hnorm hresφ V hVcond hVsep hεc (le_of_lt hδ0) hεW hεres
    -- convert to a count of box eigenvalues in `[E - ε, E + ε)`
    have hC : ((Finset.univ.filter (fun k : Fin n =>
          |boxEig α lam θ n k - E| ≤ ε / 2)).card : ℝ)
        ≤ (boxCount α lam θ (E + ε) n : ℝ) - (boxCount α lam θ (E - ε) n : ℝ) := by
      have hBsub : (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E - ε)) ⊆
          (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E + ε)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        linarith
      have hCsub : (Finset.univ.filter (fun k : Fin n => |boxEig α lam θ n k - E| ≤ ε / 2)) ⊆
          (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E + ε)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        rw [abs_le] at hk
        linarith [hk.2]
      have hdisj : Disjoint (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E - ε))
          (Finset.univ.filter (fun k : Fin n => |boxEig α lam θ n k - E| ≤ ε / 2)) := by
        rw [Finset.disjoint_left]
        intro k hk hk'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
        rw [abs_le] at hk'
        linarith [hk'.1]
      have hcard := Finset.card_union_of_disjoint hdisj
      have hunion : (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E - ε)) ∪
            (Finset.univ.filter (fun k : Fin n => |boxEig α lam θ n k - E| ≤ ε / 2)) ⊆
          (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E + ε)) :=
        Finset.union_subset hBsub hCsub
      have hle := Finset.card_le_card hunion
      rw [hcard] at hle
      have hnat : (Finset.univ.filter (fun k : Fin n => |boxEig α lam θ n k - E| ≤ ε / 2)).card
          ≤ (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E + ε)).card
            - (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E - ε)).card := by
        omega
      have hBA : (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E - ε)).card
          ≤ (Finset.univ.filter (fun k : Fin n => boxEig α lam θ n k < E + ε)).card :=
        Finset.card_le_card hBsub
      rw [boxCount, boxCount, ← Nat.cast_sub hBA]
      exact_mod_cast hnat
    -- Sturm oscillation at `E ± ε`
    have hS1 := hSturm θ (E + ε)
    have hS0 := hSturm θ (E - ε)
    rw [abs_le] at hS1 hS0
    linarith [hwin, hC, hVcard, hS1.1, hS1.2, hS0.1, hS0.2]
  -- ### 7. Integrate over the phase.
  have hcont1 : Continuous (fun θ : ℝ => pruferIter α lam (E - ε) n θ 0) :=
    Work.TMComp.IDSPrufer.contx α lam (E - ε) n
  have hcont2 : Continuous (fun θ : ℝ => pruferIter α lam (E + ε) n θ 0) :=
    Work.TMComp.IDSPrufer.contx α lam (E + ε) n
  have hint : (∫ θ in (0 : ℝ)..1,
        (pruferIter α lam (E - ε) n θ 0 - pruferIter α lam (E + ε) n θ 0))
      ≥ 3 * δ * (m₀ : ℝ) / 4 - 4 := by
    have hc : IntervalIntegrable (fun _ : ℝ => 3 * δ * (m₀ : ℝ) / 4 - 4) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hd : IntervalIntegrable (fun θ : ℝ =>
        pruferIter α lam (E - ε) n θ 0 - pruferIter α lam (E + ε) n θ 0) volume (0 : ℝ) 1 :=
      (hcont1.sub hcont2).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hc hd
      (fun θ _ => hpoint θ)
    have hconst : (∫ _θ in (0 : ℝ)..1, (3 * δ * (m₀ : ℝ) / 4 - 4))
        = 3 * δ * (m₀ : ℝ) / 4 - 4 := by simp
    linarith [hconst ▸ hmono]
  have hsub : (∫ θ in (0 : ℝ)..1, pruferIter α lam (E - ε) n θ 0)
      - (∫ θ in (0 : ℝ)..1, pruferIter α lam (E + ε) n θ 0)
      = ∫ θ in (0 : ℝ)..1,
        (pruferIter α lam (E - ε) n θ 0 - pruferIter α lam (E + ε) n θ 0) := by
    rw [intervalIntegral.integral_sub (hcont1.intervalIntegrable 0 1)
      (hcont2.intervalIntegrable 0 1)]
  -- ### 8. The rotation-number bound.
  set Xm : ℝ := ∫ θ in (0 : ℝ)..1, pruferIter α lam (E - ε) n θ 0 with hXm
  set Xp : ℝ := ∫ θ in (0 : ℝ)..1, pruferIter α lam (E + ε) n θ 0 with hXp
  set A : ℝ := 3 * δ * (m₀ : ℝ) / 4 - 4 with hAdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hra1 : |rotLift α lam (E - ε) - Xm / (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [hXm]
    exact Work.TMComp.IDSPrufer.rotLift_approx α lam (E - ε) hn1
  have hra2 : |rotLift α lam (E + ε) - Xp / (n : ℝ)| ≤ 1 / (n : ℝ) := by
    rw [hXp]
    exact Work.TMComp.IDSPrufer.rotLift_approx α lam (E + ε) hn1
  have hdiff : A / (n : ℝ) ≤ Xm / (n : ℝ) - Xp / (n : ℝ) := by
    rw [hAdef, hXm, hXp, ← sub_div]
    exact div_le_div_of_nonneg_right (by rw [hsub]; exact hint) (le_of_lt hnpos)
  have hbig : (6 : ℝ) < 3 * δ * (m₀ : ℝ) / 4 := by
    have hmul : 28 ≤ 3 * δ * ((m₀ : ℝ) - 3) := by
      have h1 : 28 / (3 * δ) ≤ (m₀ : ℝ) - 3 := by linarith [hm₀big]
      have h2 := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * δ)).mp h1
      linarith
    nlinarith [hmul, hδ0]
  have hkey6 : (2 : ℝ) < A := by rw [hAdef]; linarith
  have hfinal : rotLift α lam (E + ε) < rotLift α lam (E - ε) := by
    rw [abs_le] at hra1 hra2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have key1 : (rotLift α lam (E - ε)) * (n : ℝ) - Xm ≤ 1 := by
      have h' := mul_le_mul_of_nonneg_right hra1.2 hn0
      rw [sub_mul, div_mul_cancel₀ _ hnne, div_mul_cancel₀ _ hnne] at h'
      exact h'
    have key3 : -1 ≤ (rotLift α lam (E - ε)) * (n : ℝ) - Xm := by
      have h' := mul_le_mul_of_nonneg_right hra1.1 hn0
      have hL : -(1 / (n : ℝ)) * (n : ℝ) = -1 := by field_simp
      rw [hL, sub_mul, div_mul_cancel₀ _ hnne] at h'
      exact h'
    have key2 : (rotLift α lam (E + ε)) * (n : ℝ) - Xp ≤ 1 := by
      have h' := mul_le_mul_of_nonneg_right hra2.2 hn0
      rw [sub_mul, div_mul_cancel₀ _ hnne, div_mul_cancel₀ _ hnne] at h'
      exact h'
    have key4 : -1 ≤ (rotLift α lam (E + ε)) * (n : ℝ) - Xp := by
      have h' := mul_le_mul_of_nonneg_right hra2.1 hn0
      have hL : -(1 / (n : ℝ)) * (n : ℝ) = -1 := by field_simp
      rw [hL, sub_mul, div_mul_cancel₀ _ hnne] at h'
      exact h'
    have key5 : A ≤ Xm - Xp := by
      have h' := mul_le_mul_of_nonneg_right hdiff hn0
      rw [sub_mul, div_mul_cancel₀ _ hnne, div_mul_cancel₀ _ hnne,
        div_mul_cancel₀ _ hnne] at h'
      exact h'
    have hneg : (n : ℝ) * (rotLift α lam (E + ε) - rotLift α lam (E - ε)) < 0 := by
      nlinarith [key1, key2, key3, key4, key5, hkey6]
    have hneg' : (n : ℝ) * (rotLift α lam (E + ε) - rotLift α lam (E - ε)) < (n : ℝ) * 0 := by
      rw [mul_zero]; exact hneg
    have hlt : rotLift α lam (E + ε) - rotLift α lam (E - ε) < 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [hneg, hnpos, hc]
    linarith
  simp only [ids]
  linarith

end Work.TMComp