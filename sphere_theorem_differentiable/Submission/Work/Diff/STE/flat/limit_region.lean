import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.flat.limit_prep
import Submission.Work.Diff.STE.flat.limit_aux
import Submission.Work.Diff.STE.flat.CSq_le_of_decay
import Submission.Work.Diff.STE.flat.exists_pos_det_of_posDef
import Submission.Work.Diff.STE.flat.continuousOn_seriesFunM_family
import Submission.Work.Diff.STE.flat.xperiodic_extend_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet region for the flat limit step

`Work.Diff.STE.flat.exists_globalization`: for a limit family `cinf` which is jointly continuous on
the slab, positive definite and `1`-periodic in space, and whose coefficients decay faster than
every polynomial weight, and for every `T < τ`, the level-`0` jets
`jetM (seriesFunM (cinf t)) x`, `t ∈ [0,T)`, lie in a fixed open set `V'` on which the DeTurck
nonlinearity `Φ` agrees with a globally smooth, `x`-periodic `Φ'`.

The point of the construction is that `Φ'` can be fed to the Moser composition estimate
(`Work.Diff.STE.flat.CSq_comp_xperiodic_le`, which needs a *globally* smooth, `x`-periodic
function), while the agreement on `V'` makes the tower expressions computed with `Φ'` equal to
those computed with `Φ`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The compact set of jets of bounded norm with value part of determinant bounded below. -/
def jetBox (R δ : ℝ) : Set (Jet n) := {w | ‖w‖ ≤ R ∧ δ ≤ (reMat w.1).det}

lemma isCompact_jetBox (R δ : ℝ) : IsCompact (jetBox (n := n) R δ) := by
  have h1 : IsCompact {w : Jet n | ‖w‖ ≤ R} := by
    simpa [Metric.closedBall, dist_eq_norm] using isCompact_closedBall (0 : Jet n) R
  have h2 : IsClosed {w : Jet n | δ ≤ (reMat w.1).det} :=
    isClosed_le continuous_const continuous_reMat_det
  have h3 : jetBox (n := n) R δ
      = {w : Jet n | ‖w‖ ≤ R} ∩ {w : Jet n | δ ≤ (reMat w.1).det} := rfl
  rw [h3]
  exact h1.inter_right h2


/-- The weighted majorant `k ↦ (⟨k⟩^N)⁻¹` is summable in dimension `n` for `N > n/2`. -/
lemma summable_wt_inv_pow {N : ℕ} (hN : Fintype.card (Fin n) < 2 * N) :
    Summable (fun k : Fin n → ℤ => ((wt k) ^ N)⁻¹) :=
  (Work.Diff.STE.summable_wt_zpow (ι := Fin n) N hN).congr (fun k => by
    rw [zpow_neg, zpow_natCast])

/-- Moment summability of a coefficient family with rapid decay. -/
lemma summable_moment_of_decay {τ : ℝ} {c : ℝ → (Fin n → ℤ) → MatC n}
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k : Fin n → ℤ) (a b : Fin n), ‖c t k a b‖ * (wt k) ^ M ≤ C)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) τ) (a b : Fin n) (N : ℕ) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c t k a b‖) := by
  obtain ⟨C, hC, hCb⟩ := hdec (N + n + 1)
  have hsum : Summable (fun k : Fin n → ℤ => C * ((wt k) ^ (n + 1))⁻¹) :=
    (summable_wt_inv_pow (n := n) (N := n + 1) (by simp only [Fintype.card_fin]; omega)).mul_left C
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le _) (norm_nonneg _)) (fun k => ?_) hsum
  have h1 := hCb t ht k a b
  have hpos : 0 < (wt k) ^ (n + 1) := pow_pos (wt_pos k) _
  have h2 : (wt k) ^ N * ‖c t k a b‖
      = (‖c t k a b‖ * (wt k) ^ (N + n + 1)) * ((wt k) ^ (n + 1))⁻¹ := by
    rw [pow_add]
    field_simp
    ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpos.le)

/-- The spatial `2`-jet of a Fourier series with rapidly decaying coefficients is uniformly
bounded. -/
lemma exists_bound_jetM' {τ : ℝ} (hτ : 0 < τ) (c : ℝ → (Fin n → ℤ) → MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k : Fin n → ℤ) (a b : Fin n), ‖c t k a b‖ * (wt k) ^ M ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
      ‖jetM (seriesFunM (c t)) x‖ ≤ R := by
  obtain ⟨C1, hC1, hC1b⟩ := CSq_le_of_decay (n := n) (τ := τ) (n + 3) c hdec
  obtain ⟨C2, hC2, hC2b⟩ := sup_pdList_le (n := n) (n + 1) 2 (by omega)
  refine ⟨C2 * Real.sqrt C1, by positivity, fun t ht x => ?_⟩
  have hbd : ∀ (l : List (Fin n)) (a b : Fin n), l.length ≤ 2 →
      ‖pdList l (fun y : Fin n → ℝ => seriesFunM (c t) y a b) x‖ ≤ C2 * Real.sqrt C1 := by
    intro l a b hl
    have hγ : (fun y : Fin n → ℝ => seriesFunM (c t) y a b)
        = seriesFun (fun k : Fin n → ℤ => c t k a b) := by
      funext y; rw [seriesFunM_apply]
    rw [hγ]
    exact (hC2b _ (summable_moment_of_decay hdec ht a b) l hl x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC1b t ht a b)) hC2)
  have h1 : ‖seriesFunM (c t) x‖ ≤ C2 * Real.sqrt C1 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    simpa only [pdList, List.foldr_nil] using hbd [] i j (by simp)
  have h2 : ‖(fun a : Fin n => pdM a (seriesFunM (c t)) x)‖ ≤ C2 * Real.sqrt C1 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro a
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    simpa only [pdM, pdList, List.foldr_cons, List.foldr_nil] using hbd [a] i j (by simp)
  have h3 : ‖(fun a : Fin n => fun b : Fin n => pdM a (pdM b (seriesFunM (c t))) x)‖
      ≤ C2 * Real.sqrt C1 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro a
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro b
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    simpa only [pdM, pdList, List.foldr_cons, List.foldr_nil] using hbd [a, b] i j (by simp)
  rw [show jetM (seriesFunM (c t)) x
      = (seriesFunM (c t) x,
          ((fun a : Fin n => pdM a (seriesFunM (c t)) x),
           (fun a : Fin n => fun b : Fin n => pdM a (pdM b (seriesFunM (c t))) x))) from rfl]
  rw [norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨h1, h2, h3⟩

/-- **The globalization of the nonlinearity on the jet region.**  Under the hypotheses of the
limit step and for `T < τ`, there are a globally smooth `x`-periodic `Φ'` and an open `V'` on
which `Φ' = Φ`, containing all the level-`0` jets `jetM (seriesFunM (cinf t)) x` for
`t ∈ [0,T)`. -/
theorem exists_globalization {Φ : (Fin n → ℝ) × Jet n → MatC n} (hshape : IsDeTurckNonlin Φ)
    {τ : ℝ} (hτ : 0 < τ) (cinf : ℝ → (Fin n → ℤ) → MatC n)
    (hcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => seriesFunM (cinf p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ))
    (hpd : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
      PosDefM (seriesFunM (cinf t) x))
    (hper : ∀ t ∈ Set.Ico (0 : ℝ) τ, Periodic1 (seriesFunM (cinf t)))
    (hdec0 : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k : Fin n → ℤ) (a b : Fin n), ‖cinf t k a b‖ * (wt k) ^ M ≤ C)
    {T : ℝ} (hTτ : T < τ) :
    ∃ (Φ' : (Fin n → ℝ) × Jet n → MatC n) (V' : Set (Jet n)),
      ContDiff ℝ (⊤ : ℕ∞) Φ' ∧
      (∀ (x : Fin n → ℝ) (w : Jet n) (i : Fin n),
        Φ' (x + Pi.single i 1, w) = Φ' (x, w)) ∧
      IsOpen V' ∧ (∀ w ∈ V', (reMat w.1).det ≠ 0) ∧
      (∀ (x : Fin n → ℝ) (w : Jet n), w ∈ V' → Φ' (x, w) = Φ (x, w)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ, jetM (seriesFunM (cinf t)) x ∈ V') := by
  obtain ⟨R, hR, hRbound⟩ := exists_bound_jetM' hτ cinf hdec0
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_det_of_posDef hτ hTτ cinf hcont hpd hper
  have hKc : IsCompact (jetBox (n := n) R δ) := isCompact_jetBox R δ
  have hKcV : jetBox (n := n) R δ ⊆ goodJ n := by
    intro w hw
    exact ne_of_gt (lt_of_lt_of_le hδpos hw.2)
  have hpergood : ∀ (x : Fin n → ℝ) (w : Jet n) (i : Fin n), w ∈ goodJ n →
      Φ (x + Pi.single i 1, w) = Φ (x, w) := fun x w i hw => phi_periodic hshape i hw
  obtain ⟨Φ', hΦ'sm, hΦ'per, W', hW'open, hKcW', hW'V, hW'agr⟩ :=
    xperiodic_extend_jet Φ (goodJ n) isOpen_goodJ hshape.1 hpergood (jetBox R δ) hKc hKcV
  refine ⟨Φ', W', hΦ'sm, hΦ'per, hW'open, fun w hw => hW'V hw, hW'agr, ?_⟩
  intro t ht x
  exact hKcW' ⟨hRbound t ⟨ht.1, lt_trans ht.2 hTτ⟩ x, hδ t ht x⟩

end

end Work.Diff.STE.flat
