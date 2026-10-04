import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.GalerkinSmooth
import Submission.Work.Diff.STE.flat.GalerkinJet
import Submission.Work.Diff.STE.flat.GalerkinLip
import Submission.Work.Diff.STE.flat.exists_radius_det_ne_zero
import Submission.Work.Diff.STE.flat.rhsExp_lipschitz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat.Galerkin
open scoped Topology

/-- The two descriptions of the Galerkin right-hand side agree. -/
lemma rhs_eq_rhsExp {n N : ℕ} (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n →
    Work.Diff.STE.Flat.MatC n) (a : Coeff n N) :
    rhs Φ a = rhsExp Φ a := by
  funext k i j
  have h : (fun x : Fin n → ℝ => Φ (x, Work.Diff.STE.Flat.jetM
        (Work.Diff.STE.Flat.seriesFunM (toCoeff a)) x) i j)
      = fun x => Φ (x, jetExp a x) i j := by
    funext x
    rw [jetM_seriesFunM_toCoeff]
  simp only [rhs, rhsExp, h]

theorem galerkin_ode_existence {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (N : ℕ) (c₀ : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hc₀ : ∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c₀ k = 0)
    (hnd : ∀ x : Fin n → ℝ,
      (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c₀ x)).det ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n,
      c 0 = c₀ ∧
      (∀ (t : ℝ) (k : Fin n → ℤ), k ∉ Work.Diff.STE.Flat.box n N → c t k = 0) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k : Fin n → ℤ) (i j : Fin n),
        HasDerivAt (fun s => c s k i j)
          (Work.Diff.STE.Flat.projBox N (fun m => Work.Diff.STE.fourierCoeff (fun x =>
            Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) m) k) t)
      := by
  classical
  set a₀ : Coeff n N := ofCoeff c₀ hc₀ with ha₀
  -- the initial datum, read as a box-supported coefficient family
  have hval₀ : ∀ x : Fin n → ℝ, valExp a₀ x = Work.Diff.STE.Flat.seriesFunM c₀ x := by
    intro x
    rw [valExp_eq_seriesFunM a₀ x, ha₀, toCoeff_ofCoeff]
  have hdet : ∀ x ∈ closedCube n, (Work.Diff.STE.Flat.reMat (valExp a₀ x)).det ≠ 0 := by
    intro x _
    rw [hval₀ x]
    exact hnd x
  -- the nonlinearity composed with the jet is Lipschitz near `a₀`
  obtain ⟨K, ρ, hρ, hLip⟩ := Phi_jetExp_lipschitz Φ hΦ a₀ hdet
  -- hence the Galerkin right-hand side is Lipschitz (and bounded) on the ball
  obtain ⟨K', hK', L, hL⟩ := rhsExp_lipschitz Φ K ρ hρ a₀ hLip
  -- the time step
  have hρpos : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  set δ : ℝ := (ρ : ℝ) / ((L : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos hρpos (by positivity)
  have hδbound : (L : ℝ) * δ ≤ (ρ : ℝ) := by
    rw [hδ, mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) + 1)]
    nlinarith [show (0 : ℝ) ≤ (ρ : ℝ) by positivity,
      show (0 : ℝ) ≤ (L : ℝ) by positivity]
  -- Picard–Lindelöf on the finite-dimensional space of coefficients supported in the box
  have hPL : IsPicardLindelof (fun (_ : ℝ) (v : Coeff n N) => rhsExp Φ v)
      (tmin := -δ) (tmax := δ) ⟨0, by constructor <;> linarith⟩ a₀ ρ 0 L K' :=
    { lipschitzOnWith := fun t _ => hK'
      continuousOn := fun x _ => continuousOn_const
      norm_le := fun t _ x hx => hL x hx
      mul_max_le := by
        simp only [NNReal.coe_zero, sub_zero, zero_sub, neg_neg, max_self]
        exact hδbound }
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (Metric.mem_closedBall_self (by simp))
  refine ⟨δ, hδpos, fun t => toCoeff (α t), ?_, ?_, ?_⟩
  · show toCoeff (α 0) = c₀
    have hα00 : α 0 = a₀ := hα0
    rw [hα00, ha₀, toCoeff_ofCoeff]
  · intro t k hk
    exact toCoeff_apply_not_mem (α t) hk
  · intro t ht k i j
    have htIoo : t ∈ Set.Ioo (-δ) δ := ⟨by linarith [ht.1, hδpos], ht.2⟩
    have hαt : HasDerivAt α (rhsExp Φ (α t)) t :=
      (hα t ⟨htIoo.1.le, htIoo.2.le⟩).hasDerivAt (Icc_mem_nhds htIoo.1 htIoo.2)
    by_cases hk : k ∈ Work.Diff.STE.Flat.box n N
    · -- frequencies inside the box: the derivative is the one prescribed by the ODE
      let Lc : Coeff n N →L[ℝ] ℂ :=
        (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) j).comp
          ((ContinuousLinearMap.proj (φ := fun _ : Fin n => (Fin n → ℂ)) i).comp
            (ContinuousLinearMap.proj (φ := fun _ : Work.Diff.STE.Flat.box n N =>
              Work.Diff.STE.Flat.MatC n)
              ⟨k, hk⟩))
      have hLd : HasDerivAt (fun s : ℝ => α s ⟨k, hk⟩ i j)
          ((rhsExp Φ (α t)) ⟨k, hk⟩ i j) t :=
        Lc.hasFDerivAt.comp_hasDerivAt t hαt
      have hfun : (fun s : ℝ => toCoeff (α s) k i j) = fun s : ℝ => α s ⟨k, hk⟩ i j := by
        funext s
        rw [toCoeff_apply_mem]
      have hkey : Work.Diff.STE.Flat.projBox N (fun m => Work.Diff.STE.fourierCoeff
            (fun x => Φ (x, Work.Diff.STE.Flat.jetM
              (Work.Diff.STE.Flat.seriesFunM (toCoeff (α t))) x) i j) m) k
          = (rhsExp Φ (α t)) ⟨k, hk⟩ i j := by
        rw [Work.Diff.STE.Flat.projBox_apply_of_mem N _ hk]
        have hjet : (fun x : Fin n → ℝ => Φ (x, Work.Diff.STE.Flat.jetM
              (Work.Diff.STE.Flat.seriesFunM (toCoeff (α t))) x) i j)
            = fun x => Φ (x, jetExp (α t) x) i j := by
          funext x
          rw [jetM_seriesFunM_toCoeff]
        rw [hjet]
        rfl
      rw [hfun, hkey]
      exact hLd
    · -- frequencies outside the box: both sides vanish
      have hfun : (fun s : ℝ => toCoeff (α s) k i j) = fun _ : ℝ => (0 : ℂ) := by
        funext s
        rw [toCoeff_apply_not_mem _ hk]
        rfl
      rw [hfun, Work.Diff.STE.Flat.projBox_apply_of_not_mem N _ hk]
      exact hasDerivAt_const t 0

end Work.Diff.STE.flat
