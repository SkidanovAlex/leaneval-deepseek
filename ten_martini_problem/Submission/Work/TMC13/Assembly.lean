import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMContract.Components
import Submission.Work.TMC13.Basic
import Submission.Work.TMC13.Estimate
import Submission.Work.TMC13.prufer_lift
import Submission.Work.TMC13.conjugating_lift
import Submission.Work.TMC13.RotLiftLimit

/-!
# Component C13 (`P_FictLip`) from the components C5 and C9

This file assembles the fictitious Lipschitz estimate for the integrated density of states
(AJ Theorem 6.1) from

* C5 (`P_RotBasics`), used only for the *existence* of the Prüfer rotation number limit, and
* C9 (`P_mAnalytic`), the fictitious reducibility of the transfer cocycle on a spectral
  interval,

plus the internal computations of `TMC13.Estimate`: the lift identity (`prufer_conj_int`)
and the propagation estimate (`rotLift_perturb`).

`fictLip_of` has exactly the shape used by the glue in `Submission/Work/TMContract/Glue.lean`:
it produces `P_FictLip` from C5 and C9 as hypotheses.
-/

noncomputable section

namespace Work.TMC13

open Matrix Filter MeasureTheory
open scoped Topology

/-! ## Periodicity of the Prüfer lift and of `ids` in the frequency -/

/-- Shifting the frequency by an integer does not change the Prüfer iteration. -/
lemma pruferIter_add_int (α : ℝ) (m : ℤ) (lam E : ℝ) (n : ℕ) (x t : ℝ) :
    Work.TMContract.pruferIter (α + (m : ℝ)) lam E n x t
      = Work.TMContract.pruferIter α lam E n x t := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have harg : E - 2 * lam * Real.cos (2 * Real.pi * (x + (k : ℝ) * (α + (m : ℝ))))
        = E - 2 * lam * Real.cos (2 * Real.pi * (x + (k : ℝ) * α)) := by
      have hkey : 2 * Real.pi * (x + (k : ℝ) * (α + (m : ℝ)))
          = 2 * Real.pi * (x + (k : ℝ) * α) + ((k : ℝ) * (m : ℝ)) * (2 * Real.pi) := by
        ring
      have hcast : ((k : ℝ) * (m : ℝ)) = (((k : ℤ) * m : ℤ) : ℝ) := by push_cast; ring
      rw [hkey, hcast, Real.cos_add_int_mul_two_pi]
    simp only [Work.TMContract.pruferIter, harg, ih]

/-- Shifting the frequency by an integer does not change `rotLift`. -/
lemma rotLift_add_int (α : ℝ) (m : ℤ) (lam E : ℝ) :
    Work.TMContract.rotLift (α + (m : ℝ)) lam E = Work.TMContract.rotLift α lam E := by
  unfold Work.TMContract.rotLift
  congr 1
  funext n
  simp only [pruferIter_add_int]

/-- Shifting the frequency by an integer does not change the integrated density of states. -/
lemma ids_add_int (α : ℝ) (m : ℤ) (lam E : ℝ) :
    Work.TMContract.ids (α + (m : ℝ)) lam E = Work.TMContract.ids α lam E := by
  unfold Work.TMContract.ids
  rw [rotLift_add_int]

/-- A continuous slice of a jointly analytic function of two variables. -/
lemma continuous_slice_of_jointAnalytic {a b : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioo a b ×ˢ Set.univ))
    {E : ℝ} (hE : E ∈ Set.Ioo a b) : Continuous (fun x : ℝ => f E x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (AnalyticAt.curry_right (hf (E, x) ⟨hE, Set.mem_univ x⟩)).continuousAt

/-! ## Normalising the conjugacy data

`P_mAnalytic` provides the conjugacy `C` with `det C = 1` and `HasDegree (C E) 0` only for
`E ∈ (a,b)`.  The lift construction `conjugating_lift` wants these globally; replace `C` by
the identity outside `(a,b)`. -/

lemma hasDegree_one :
    Work.TMContract.HasDegree (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 := by
  refine ⟨continuous_const, fun _ => 0, continuous_const, fun x => by simp, fun x => ?_⟩
  exact ⟨1, one_pos, by simp, by simp⟩

/-- Replace `C` by the identity outside `(a,b)`, so that all hypotheses of
`conjugating_lift` hold globally. -/
lemma normalize_C {a b : ℝ} {C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hper : ∀ E x : ℝ, C E (x + 1) = C E x)
    (hana : ∀ i j : Fin 2, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j)
      (Set.Ioo a b ×ˢ Set.univ))
    (hdet : ∀ E ∈ Set.Ioo a b, ∀ x : ℝ, (C E x).det = 1)
    (hdeg : ∀ E ∈ Set.Ioo a b, Work.TMContract.HasDegree (C E) 0) :
    ∃ C' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ E x : ℝ, C' E (x + 1) = C' E x) ∧ (∀ E x : ℝ, (C' E x).det = 1) ∧
      (∀ i j : Fin 2, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C' p.1 p.2 i j)
        (Set.Ioo a b ×ˢ Set.univ)) ∧
      (∀ E : ℝ, Work.TMContract.HasDegree (C' E) 0) ∧
      (∀ E ∈ Set.Ioo a b, C' E = C E) := by
  refine ⟨fun E x => if E ∈ Set.Ioo a b then C E x else 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro E x
    by_cases h : E ∈ Set.Ioo a b
    · simp only [h, if_true]; exact hper E x
    · simp only [h, if_false]
  · intro E x
    by_cases h : E ∈ Set.Ioo a b
    · simp only [h, if_true]; exact hdet E h x
    · simp only [h, if_false]; exact Matrix.det_one
  · intro i j
    refine AnalyticOnNhd.congr (isOpen_Ioo.prod isOpen_univ) (hana i j) ?_
    intro p hp
    have hp' : p.1 ∈ Set.Ioo a b := hp.1
    simp only [hp', if_true]
  · intro E
    by_cases h : E ∈ Set.Ioo a b
    · simpa only [h, if_true] using hdeg E h
    · simp only [h, if_false]; exact hasDegree_one
  · intro E hE
    funext x
    simp only [hE, if_true]

/-! ## The main assembly -/

/-- **C13 from C9 (and C5, unused).**  Fictitious Lipschitz continuity of `N` in `α` on a
spectral interval (AJ Theorem 6.1).

The only external component needed is C9 (`P_mAnalytic`); the existence of the Prüfer
rotation number (C5 part 1) is proved internally in `TMC13/RotLiftLimit.lean`. -/
theorem fictLip_of_mAnalytic (h9 : Work.TMContract.P_mAnalytic) :
    Work.TMContract.P_FictLip := by
  intro α lam a b hα hl0 hl1 hab hsub c d hac hdb
  obtain ⟨C₀, φ, hCana₀, hφana, hCper₀, hφper, hCdet₀, hCdeg₀, hconj₀⟩ :=
    h9 α lam a b hα hl0 hl1 hab hsub
  obtain ⟨C, hCper, hCdet, hCana, hCdeg, hCeq⟩ :=
    normalize_C (a := a) (b := b) hCper₀ hCana₀ hCdet₀ hCdeg₀
  have hconj : ∀ E ∈ Set.Ioo a b, ∀ x : ℝ,
      C E (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot (φ E x) * C E x := by
    intro E hE x
    have h := hconj₀ E hE x
    rw [← hCeq E hE] at h
    exact h
  have hpruferc := (prufer_lift (0 : ℝ)).1
  -- the bound with `K = L` for any pair `c ≤ d` with `a < c`, `d < b`
  have main : ∀ (c d : ℝ), a < c → d < b → c ≤ d → ∃ K : ℝ, ∀ α' E : ℝ, E ∈ Set.Icc c d →
      |Work.TMContract.ids α' lam E - Work.TMContract.ids α lam E| ≤ K * |α' - α| := by
    intro c d hac hdb hcd
    obtain ⟨h, hhcont, hhshift, hhproj, hM, hL⟩ :=
      conjugating_lift hac hdb hcd hCper hCdet hCana hCdeg
    obtain ⟨M, hM0, hMbnd⟩ := hM
    obtain ⟨L, hL0, hLbnd⟩ := hL
    have hkey : ∀ E ∈ Set.Icc c d, ∃ k : ℤ,
        (∀ y t : ℝ, h E (y + α) (Work.TMContract.pruferStep (amoA lam E y) t)
            = h E y t + 2 * φ E y + k) ∧
        (∀ α' : ℝ, |α' - α| ≤ 1 →
          |Work.TMContract.rotLift α' lam E - (2 * (∫ x in (0 : ℝ)..1, φ E x) + k)|
            ≤ L * |α' - α|) := by
      intro E hE
      have hE' : E ∈ Set.Ioo a b := ⟨lt_of_lt_of_le hac hE.1, lt_of_le_of_lt hE.2 hdb⟩
      have hClift : ∀ y : ℝ, IsProjLift (C E y) (h E y) := by
        intro y
        refine ⟨(hhcont E hE).comp (continuous_const.prodMk continuous_id),
          fun t => hhshift E hE y t, fun t => ?_⟩
        obtain ⟨cc, hcc, hcc'⟩ := hhproj E hE y t
        exact ⟨cc, hcc, by simpa [dvec] using hcc'⟩
      have hplift : ∀ y : ℝ, IsProjLift (Work.TMContract.tmR lam E y)
          (Work.TMContract.pruferStep (amoA lam E y)) := fun y => isProjLift_tmR lam E y
      have hconjE : ∀ y : ℝ, C E (y + α) * Work.TMContract.tmR lam E y
          = Work.TMContract.rot (φ E y) * C E y := fun y => hconj E hE' y
      have hid0 := prufer_conj_exists_int (C := C E) (φ := φ E) (h := h E) hClift hplift hconjE
      obtain ⟨k, hk⟩ := prufer_conj_int (α := α) (lam := lam) (E := E) (φ := φ E) (h := h E)
        (hhcont E hE) (continuous_slice_of_jointAnalytic hφana hE') hpruferc hid0
      exact ⟨k, hk, rotLift_perturb (α := α) (lam := lam) (E := E) (φ := φ E) (h := h E)
        (k := k) (M := M) (L := L) hpruferc (fun x => hφper E x)
        (continuous_slice_of_jointAnalytic hφana hE') (hhcont E hE) hk
        (fun y t => hMbnd E hE y t) (fun y s β hβ => hLbnd E hE y s β hβ)
        (fun α' => prufer_rotLift_tendsto α' lam E)⟩
    refine ⟨L, fun α' E hE => ?_⟩
    obtain ⟨k, _, hest⟩ := hkey E hE
    have hα0 : Work.TMContract.rotLift α lam E = 2 * (∫ x in (0 : ℝ)..1, φ E x) + k := by
      have h0 := hest α (by rw [sub_self, abs_zero]; norm_num)
      rw [sub_self, abs_zero, mul_zero] at h0
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
    have hids : ∀ β : ℝ, Work.TMContract.ids β lam E - Work.TMContract.ids α lam E
        = -(Work.TMContract.rotLift β lam E - Work.TMContract.rotLift α lam E) := by
      intro β
      unfold Work.TMContract.ids
      ring
    rcases le_or_gt |α' - α| 1 with hε | hε
    · rw [hids α', abs_neg, hα0]
      exact hest α' hε
    · -- far case: reduce the frequency modulo `1`
      set m : ℤ := round (α' - α)
      have hmred : |(α' - (m : ℝ)) - α| ≤ 1 := by
        have h := abs_sub_round (α' - α)
        have heq : (α' - (m : ℝ)) - α = (α' - α) - (m : ℝ) := by ring
        rw [heq, show m = round (α' - α) from rfl]
        linarith [h]
      have hmle : |(α' - (m : ℝ)) - α| ≤ |α' - α| := by
        have h := abs_sub_round (α' - α)
        have heq : (α' - (m : ℝ)) - α = (α' - α) - (m : ℝ) := by ring
        rw [heq, show m = round (α' - α) from rfl]
        linarith [h, hε.le]
      have hper' : Work.TMContract.ids α' lam E = Work.TMContract.ids (α' - (m : ℝ)) lam E := by
        have h := ids_add_int (α' - (m : ℝ)) m lam E
        have heq : (α' - (m : ℝ)) + (m : ℝ) = α' := by ring
        rw [heq] at h
        exact h
      rw [hper', hids (α' - (m : ℝ)), abs_neg, hα0]
      calc |Work.TMContract.rotLift (α' - (m : ℝ)) lam E
            - (2 * (∫ x in (0 : ℝ)..1, φ E x) + k)|
          ≤ L * |(α' - (m : ℝ)) - α| := hest (α' - (m : ℝ)) hmred
        _ ≤ L * |α' - α| := mul_le_mul_of_nonneg_left hmle hL0
  rcases le_total c d with hcd | hdc
  · exact main c d hac hdb hcd
  · rcases lt_or_eq_of_le hdc with hdc' | hdc'
    · refine ⟨0, fun α' E hE => ?_⟩
      exact absurd hE (by
        simp only [Set.mem_Icc]
        intro hh
        linarith [hh.1, hh.2])
    · exact main c d hac hdb (le_of_eq hdc'.symm)

/-- The same statement with the (now unnecessary) C5 hypothesis, kept for compatibility with
the component-style glue. -/
theorem fictLip_of (h5 : Work.TMContract.P_RotBasics) (h9 : Work.TMContract.P_mAnalytic) :
    Work.TMContract.P_FictLip :=
  fictLip_of_mAnalytic h9

end Work.TMC13
