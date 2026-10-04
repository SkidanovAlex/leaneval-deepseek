import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.flat.limit_prep
import Submission.Work.Diff.STE.flat.limit_region
import Submission.Work.Diff.STE.flat.exists_limit_coeff
import Submission.Work.Diff.STE.flat.continuousOn_seriesFunM_family
import Submission.Work.Diff.STE.flat.dd_bounds
import Submission.Work.Diff.STE.flat.dd_deriv
import Submission.Work.Diff.STE.flat.contDiffOn_series_tower
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_seriesFunM
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly of the flat limit step

`Work.Diff.STE.flat.solvesOn_of_limit`: from the properties of the limit family `cinf` produced by
the Arzelà–Ascoli step (uniform rapid decay of the coefficients, `1`-periodicity in space, positive
definiteness, and the level-`1` equation) one obtains a solution `u t = seriesFunM (cinf t)` of the
flat DeTurck problem on `[0, τ)`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators
open Filter Set
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- A within-derivative on `[0,T)` is also a within-derivative on `[0,τ)` as soon as the point
is below `T`. -/
lemma hasDerivWithinAt_Ico_of_Ico {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} {f' : G} {T τ t : ℝ} (htT : t < T)
    (h : HasDerivWithinAt f f' (Set.Ico (0 : ℝ) T) t) :
    HasDerivWithinAt f f' (Set.Ico (0 : ℝ) τ) t := by
  have hu : Set.Ioo (t - 1) T ∈ 𝓝 t :=
    IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self t zero_lt_one, htT⟩
  have hsub : Set.Ico (0 : ℝ) τ ∩ Set.Ioo (t - 1) T ⊆ Set.Ico (0 : ℝ) T := by
    intro q hq
    exact ⟨hq.1.1, hq.2.2⟩
  exact (hasDerivWithinAt_inter hu).mp (h.mono hsub)

/-- **The assembly.**  A limit family satisfying the conclusions of the Arzelà–Ascoli step gives a
solution of the flat DeTurck problem on `[0, τ)`. -/
theorem solvesOn_of_limit {n : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ) (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    {τ : ℝ} (hτ : 0 < τ) (cinf : ℝ → (Fin n → ℤ) → MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k' : Fin n → ℤ) (a b : Fin n), ‖cinf t k' a b‖ * (wt k') ^ M ≤ C)
    (hper : ∀ t ∈ Set.Ico (0 : ℝ) τ, Periodic1 (seriesFunM (cinf t)))
    (hpd : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ, PosDefM (seriesFunM (cinf t) x))
    (hpde : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => cinf s k' a b)
        (Work.Diff.STE.fourierCoeff
          (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (cinf t)) x) a b) k')
        (Set.Ico (0 : ℝ) τ) t) :
    SolvesOn Φ τ (fun t => seriesFunM (cinf t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x, PosDefM (seriesFunM (cinf t) x)) := by
  have hsumM : Summable (fun k' : Fin n → ℤ => ((wt k') ^ (n + 1))⁻¹) :=
    summable_wt_inv_pow (N := n + 1) (by simp only [Fintype.card_fin]; omega)
  -- joint continuity on the slab
  have hcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => seriesFunM (cinf p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
    refine continuousOn_seriesFunM_family hτ cinf hdec (fun k' a b => ?_)
    exact fun t ht => (hpde t ht k' a b).continuousWithinAt
  -- the decay bound restricted to a slab `[0,T)`, `T < τ`
  have hdecT : ∀ T : ℝ, T < τ → ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ (k' : Fin n → ℤ) (a b : Fin n), ‖cinf t k' a b‖ * (wt k') ^ M ≤ C := by
    intro T hTτ M
    obtain ⟨C, hC, hCb⟩ := hdec M
    exact ⟨C, hC, fun t ht k' a b => hCb t ⟨ht.1, lt_trans ht.2 hTτ⟩ k' a b⟩
  -- the level-one coefficient equation, restricted to a slab
  have hpdeT : ∀ T : ℝ, T < τ → ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => dd Φ cinf 0 s k' a b)
        (dd Φ cinf 1 t k' a b) (Set.Ico (0 : ℝ) T) t := by
    intro T hTτ t ht k' a b
    have htτ : t ∈ Set.Ico (0 : ℝ) τ := ⟨ht.1, lt_trans ht.2 hTτ⟩
    rw [dd_one_apply]
    exact (hpde t htτ k' a b).mono (Set.Ico_subset_Ico_right hTτ.le)
  -- smoothness on each slab `[0,T)`, `T < τ`
  have hcdT : ∀ T : ℝ, T < τ → ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => seriesFunM (cinf p.1) p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) := by
    intro T hTτ
    rcases lt_or_ge 0 T with hT0 | hT0
    · obtain ⟨Φ', V', hΦ'sm, hΦ'per, hV'open, hV'det, hagr, hconf⟩ :=
        exists_globalization hshape hτ cinf hcont hpd hper hdec hTτ
      have hbd := dd_bounds k hk T hT0 Φ Φ' hshape hΦ'sm hΦ'per V' hV'open hV'det hagr cinf hconf
        (hdecT T hTτ)
      have hder := dd_deriv T hT0 Φ Φ' hshape hΦ'sm V' hV'open hV'det hagr cinf hconf hbd
        (hpdeT T hTτ)
      exact contDiffOn_series_tower T hT0 (fun j => dd Φ cinf j) hbd hder
    · intro p hp
      exact absurd hp.1.2 (not_lt.mpr (le_trans hT0 hp.1.1))
  -- glue the slabs into `[0,τ)`
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => seriesFunM (cinf p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
    refine contDiffOn_of_locally_contDiffOn (fun p hp => ?_)
    obtain ⟨t₀, x₀⟩ := p
    obtain ⟨T, htT, hTτ⟩ := exists_between hp.1.2
    refine ⟨Set.Ioo (t₀ - 1) T ×ˢ Set.univ, ?_, ?_, ?_⟩
    · exact isOpen_Ioo.prod isOpen_univ
    · exact ⟨⟨by linarith, htT⟩, trivial⟩
    · refine (hcdT T hTτ).mono (fun q hq => ?_)
      have h1 : q.1 ∈ Set.Ico (0 : ℝ) τ := (Set.mem_prod.mp hq.1).1
      have h2 : q.1 ∈ Set.Ioo (t₀ - 1) T := (Set.mem_prod.mp hq.2).1
      exact ⟨⟨h1.1, h2.2⟩, trivial⟩
  -- the equation
  have hpdeW : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s : ℝ => seriesFunM (cinf s) x)
        (Φ (x, jetM (seriesFunM (cinf t)) x)) (Set.Ico (0 : ℝ) τ) t := by
    intro t ht x
    obtain ⟨T, htT, hTτ⟩ := exists_between ht.2
    have hT0 : 0 < T := lt_of_le_of_lt ht.1 htT
    have htTmem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.1, htT⟩
    obtain ⟨Φ', V', hΦ'sm, hΦ'per, hV'open, hV'det, hagr, hconf⟩ :=
      exists_globalization hshape hτ cinf hcont hpd hper hdec hTτ
    obtain ⟨C1, hC1, hC1b⟩ :=
      (dd_bounds k hk T hT0 Φ Φ' hshape hΦ'sm hΦ'per V' hV'open hV'det hagr cinf hconf
        (hdecT T hTτ)) 1 (n + 1)
    have hC1nn : 0 ≤ C1 := hC1
    have hg : Summable (fun k' : Fin n → ℤ => C1 * ((wt k') ^ (n + 1))⁻¹) := hsumM.mul_left C1
    have hdiff : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
        ‖cinf s k' a b - cinf t k' a b‖
          ≤ |s - t| * (C1 * ((wt k') ^ (n + 1))⁻¹) := by
      intro s hs k' a b
      have hconv : Convex ℝ (Set.Ico (0 : ℝ) T) := convex_Ico (0 : ℝ) T
      have hderiv : ∀ u ∈ Set.Ico (0 : ℝ) T,
          HasDerivWithinAt (fun v : ℝ => cinf v k' a b) (dd Φ cinf 1 u k' a b)
            (Set.Ico (0 : ℝ) T) u := fun u hu => hpdeT T hTτ u hu k' a b
      have hbound : ∀ u ∈ Set.Ico (0 : ℝ) T, ‖dd Φ cinf 1 u k' a b‖
          ≤ C1 * ((wt k') ^ (n + 1))⁻¹ := by
        intro u hu
        have h1 := hC1b u hu k' a b
        have hpos : 0 < (wt k') ^ (n + 1) := pow_pos (wt_pos k') _
        rw [← le_div_iff₀ hpos] at h1
        simpa [div_eq_mul_inv] using h1
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hconv htTmem hs
      simpa [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using h
    have hdt : ∀ a b : Fin n, Summable (fun k' : Fin n → ℤ => ‖cinf t k' a b‖) := by
      intro a b
      obtain ⟨C', hC', hC'b⟩ := hdec (n + 1)
      refine Summable.of_nonneg_of_le (fun k' => norm_nonneg _) (fun k' => ?_) (hsumM.mul_left C')
      have h1 := hC'b t ht k' a b
      have hpos : 0 < (wt k') ^ (n + 1) := pow_pos (wt_pos k') _
      rw [← le_div_iff₀ hpos] at h1
      simpa [div_eq_mul_inv] using h1
    -- term-by-term differentiation on `[0,T)`
    have hser : HasDerivWithinAt (fun s : ℝ => seriesFunM (cinf s) x)
        (seriesFunM (dd Φ cinf 1 t) x) (Set.Ico (0 : ℝ) T) t := by
      refine hasDerivWithinAt_seriesFunM hT0 htTmem x cinf (dd Φ cinf 1 t)
        (fun k' => C1 * ((wt k') ^ (n + 1))⁻¹) hg
        (fun k' => mul_nonneg hC1nn (inv_nonneg.mpr (pow_nonneg (wt_pos k').le _)))
        hdiff hdt (fun k' a b => ?_)
      exact hpdeT T hTτ t htTmem k' a b
    -- transport to `[0,τ)` and identify the right-hand side
    have hmom : ∀ i j : Fin n, ∀ N : ℕ,
        Summable (fun k' : Fin n → ℤ => (wt k') ^ N * ‖cinf t k' i j‖) := by
      intro i j N
      obtain ⟨C'', hC'', hC''b⟩ := hdec (N + n + 1)
      refine Summable.of_nonneg_of_le
        (fun k' => mul_nonneg (pow_nonneg (wt_pos k').le _) (norm_nonneg _)) (fun k' => ?_)
        (hsumM.mul_left C'')
      have h1 := hC''b t ht k' i j
      have hpos : 0 < (wt k') ^ (n + 1) := pow_pos (wt_pos k') _
      have h2 : (wt k') ^ N * ‖cinf t k' i j‖
          = (‖cinf t k' i j‖ * (wt k') ^ (N + n + 1)) * ((wt k') ^ (n + 1))⁻¹ := by
        rw [pow_add]
        field_simp
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpos.le)
    have hgood : ∀ y : Fin n → ℝ, (reMat (seriesFunM (cinf t) y)).det ≠ 0 := by
      intro y
      exact (hpd t ht y).det_pos.ne'
    have hid := seriesFunM_dd_one Φ hshape hmom (hper t ht) hgood x
    have hser' := hasDerivWithinAt_Ico_of_Ico (τ := τ) htT hser
    rw [hid] at hser'
    exact hser'
  exact ⟨⟨hcd, hper, hpdeW⟩, hpd⟩

end

end Work.Diff.STE.flat
