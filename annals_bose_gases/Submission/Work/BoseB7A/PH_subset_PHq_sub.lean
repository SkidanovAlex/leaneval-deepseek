import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.PH_subset_PHq_sub` — `P_H ⊆ P_H^q` and `s − k ∈ P_H^q`

FS §10 replaces the high-momentum region
`P_H = {|k| ≥ ½K_H⁻¹a⁻¹}` by the *quarter* region
`P_H^q = {|q| ≥ ¼K_H⁻¹a⁻¹}` (`FockData.PHq`), because

* the diagonal kinetic reserve `(1−𝓁²)dNumOpR E (PH)` of `eq:EstimateQ3Tilde1`
  is dominated by `dNumOpR E (PHq)` (route: `P_H ⊆ P_H^q`), and
* the modes `s − k` occurring in the cubic word (`s ∈ supp f_L`, `k ∈ P_H`) are
  themselves in `P_H^q`, which is what allows the Bogoliubov kinetic gap to be
  charged on the *same* region (`eq:EstimateQ3Tilde2+3`, and the absorption of
  `Q₃^{(1)}`/`Q₃^{(2)}` by `∫𝒟b†b`).

Both facts are geometric, and both go through the *separation of the momentum
scales* `K_L√(μa) ≪ K_H⁻¹a⁻¹` of FS `con:KLKH`.  At FS's parameter point

  `K_L = (K_ℓd²)^{-1} = (μa³)^{-21/646}`,  `K_H = K̃_H(μa³)^{-5/12}`,

so (using `μa = (μa³)/a²`)

  `K_L√(μa)·(K_H a) = (μa³)^{55/1292}`,

which is `≤ 1/4` as soon as `μa³ ≤ 4^{-24}` (this diluteness is the `t₀` below;
it is *independent* of `K₀`, `b₀`, of the Fock data and of the parameters, as the
statement requires).  Then `‖k_s − k_k‖ ≥ ‖k_k‖ − ‖k_s‖ ≥ ½K_H⁻¹a⁻¹ − ¼K_H⁻¹a⁻¹
= ¼K_H⁻¹a⁻¹` and `P_H ⊆ P_H^q` is immediate from `½ ≥ ¼`.

## Contents

* `KL_eq_rpow`, `KH_eq_rpow`, `ratio_eq` — the diluteness arithmetic.
* `ratio_small` — the scale separation `K_L√(μa) ≤ ¼K_H⁻¹a⁻¹` at small `t`
  (the hypothesis `hsep` of `Work.BoseB7.PL_disjoint_PH`, with `1/4` in place of
  the `1/2` used there for the *disjointness* of `P_L` and `P_H`).
* `PH_subset_PHq` — `P_H ⊆ P_H^q`.
* `PH_subset_PHq_sub` — the two facts bundled, in the form the requester needs.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

set_option linter.unusedVariables false

/-! ## 1. The diluteness arithmetic of the two momentum cutoffs -/

/-- `K_L = (K_ℓd²)^{-1}` at FS's parameter point: `K_L = (μa³)^{-21/646}`. -/
lemma KL_eq_rpow {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    E.KL = hv.t ^ (-(21 / 646 : ℝ)) := by
  rw [hv.KL_eq, Work.BoseB7.KL, hv.Kl_eq, hv.d_eq]
  simp only [Work.BoseBox.fsXp]
  rw [← Real.rpow_natCast (hv.t ^ ((6 : ℝ) / 323)) 2, ← Real.rpow_mul hv.t_pos.le,
    ← Real.rpow_add hv.t_pos, Real.rpow_neg_one, ← Real.rpow_neg hv.t_pos.le]
  congr 1
  norm_num

/-- `K_H = K̃_H(μa³)^{-5/12}` at FS's parameter point:
`K_H = (μa³)^{-8/969}·(μa³)^{-5/12}`. -/
lemma KH_eq_rpow {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    E.KH = hv.t ^ (-(8 / 969 : ℝ)) * hv.t ^ (-(5 / 12 : ℝ)) := by
  rw [hv.KH_eq, Work.BoseB7.KH, hv.mu_eq]
  simp only [Work.BoseBox.fsXp]
  congr 1
  norm_num

/-- `Real.sqrt (μa) = (μa³)^{1/2}/a` at the diluteness `μa³ = t`. -/
lemma sqrt_mu_a_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    Real.sqrt (E.mu * E.aScat) = hv.t ^ (1 / 2 : ℝ) / E.aScat := by
  have ha : 0 < E.aScat := hv.a_pos
  have hmu : E.mu * E.aScat = hv.t / E.aScat ^ 2 := by
    rw [eq_div_iff (by positivity : E.aScat ^ 2 ≠ 0)]
    rw [← hv.mu_eq]; ring
  rw [hmu, Real.sqrt_div' _ (sq_nonneg E.aScat), Real.sqrt_sq (le_of_lt ha),
    Real.sqrt_eq_rpow]

/-- **The diluteness identity**: `K_L·√(μa)·(K_H a) = (μa³)^{55/1292}` at FS's
parameter point. -/
lemma ratio_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) = hv.t ^ (55 / 1292 : ℝ) := by
  have ht : 0 < hv.t := hv.t_pos
  have ha : 0 < E.aScat := hv.a_pos
  have hmul : Real.sqrt (E.mu * E.aScat) * E.aScat = hv.t ^ (1 / 2 : ℝ) := by
    rw [sqrt_mu_a_eq E hv, div_mul_cancel₀ _ (ne_of_gt ha)]
  have hKH : E.KH = hv.t ^ (-(8 / 969 : ℝ)) * hv.t ^ (-(5 / 12 : ℝ)) := KH_eq_rpow E hv
  calc E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat)
      = E.KL * (Real.sqrt (E.mu * E.aScat) * E.aScat) * E.KH := by ring
    _ = hv.t ^ (-(21 / 646 : ℝ)) * hv.t ^ (1 / 2 : ℝ)
          * (hv.t ^ (-(8 / 969 : ℝ)) * hv.t ^ (-(5 / 12 : ℝ))) := by
        rw [hmul, KL_eq_rpow E hv, hKH]
    _ = hv.t ^ (55 / 1292 : ℝ) := by
        rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 1
        norm_num

/-- **The scale separation** (`con:KLKH` in its sharp form): at diluteness
`μa³ ≤ 4^{-24}`, `K_L√(μa) ≤ ¼K_H⁻¹a⁻¹`.  This is the hypothesis `hsep` of
`Work.BoseB7.PL_disjoint_PH` strengthened from `1/2` to `1/4` (the extra margin
is exactly what makes `s − k ∈ P_H^q`). -/
theorem ratio_small {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) (hle : hv.t ≤ (1 / 4 : ℝ) ^ 24) :
    E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (4 * E.KH * E.aScat) := by
  have ht : 0 < hv.t := hv.t_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hP : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ 1 / 4 := by
    rw [ratio_eq E hv]
    have h1 : hv.t ^ (55 / 1292 : ℝ) ≤ hv.t ^ (1 / 24 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_ge ht hv.t_le_one ?_
      norm_num
    have h2 : hv.t ^ (1 / 24 : ℝ) ≤ ((1 / 4 : ℝ) ^ 24) ^ (1 / 24 : ℝ) :=
      Real.rpow_le_rpow ht.le hle (by norm_num)
    have h3 : ((1 / 4 : ℝ) ^ 24) ^ (1 / 24 : ℝ) = 1 / 4 := by
      rw [← Real.rpow_natCast (1 / 4 : ℝ) 24,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
    linarith
  have hpos : 0 < 4 * E.KH * E.aScat := by positivity
  rw [le_div_iff₀ hpos]
  calc (E.KL * Real.sqrt (E.mu * E.aScat)) * (4 * E.KH * E.aScat)
      = 4 * (E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat)) := by ring
    _ ≤ 4 * (1 / 4) := by linarith
    _ = 1 := by norm_num

/-! ## 2. The two region inclusions -/

/-- FS: `P_H ⊆ P_H^q`.  Since `2K_Ha ≥ 4K_Ha > 0`, `1/(4K_Ha) ≤ 1/(2K_Ha)`. -/
lemma PH_subset_PHq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E) (i : Mode)
    (hi : F.PH E.KH E.aScat i) : F.PHq E.KH E.aScat i := by
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hKa : 0 < E.KH * E.aScat := mul_pos hKH ha
  refine le_trans (one_div_le_one_div_of_le (show (0 : ℝ) < 2 * E.KH * E.aScat by positivity)
    (show 2 * E.KH * E.aScat ≤ 4 * E.KH * E.aScat by linarith)) hi

/-- FS: for `s` in the support of the low-momentum localisation `f_L` and
`k ∈ P_H`, the mode `s − k` lies in the quarter region `P_H^q`. -/
lemma sub_mem_PHq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    (hsmall : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 1 / (4 * E.KH * E.aScat))
    (hker : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E →
      F.kmom (s - k) = F.kmom s - F.kmom k)
    (hsupp : ∀ s : Mode, E.fL s ≠ 0 → F.PL E.KL E.mu E.aScat s)
    {s k : Mode} (hfL : E.fL s ≠ 0) (hk : k ∈ F.PHset E) :
    F.PHq E.KH E.aScat (s - k) := by
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hPLs : ‖F.kmom s‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) := hsupp s hfL
  have hPHk : 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := (Finset.mem_filter.mp hk).2
  have hsub : F.kmom (s - k) = F.kmom s - F.kmom k := hker s k hfL hk
  -- reverse triangle inequality
  have hrt : ‖F.kmom k‖ - ‖F.kmom s‖ ≤ ‖F.kmom s - F.kmom k‖ := by
    have h1 : ‖F.kmom k‖ - ‖F.kmom s‖ ≤ |‖F.kmom k‖ - ‖F.kmom s‖| := le_abs_self _
    have h2 : |‖F.kmom k‖ - ‖F.kmom s‖| ≤ ‖F.kmom k - F.kmom s‖ :=
      abs_norm_sub_norm_le _ _
    rw [norm_sub_rev (F.kmom k) (F.kmom s)] at h2
    linarith
  have harith : 1 / (2 * E.KH * E.aScat) - 1 / (4 * E.KH * E.aScat)
      = 1 / (4 * E.KH * E.aScat) := by
    field_simp
    ring
  have hkey : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom s - F.kmom k‖ := by
    have h1 : 1 / (2 * E.KH * E.aScat) - E.KL * Real.sqrt (E.mu * E.aScat)
        ≤ ‖F.kmom k‖ - ‖F.kmom s‖ := sub_le_sub hPHk hPLs
    have h2 : 1 / (4 * E.KH * E.aScat)
        ≤ 1 / (2 * E.KH * E.aScat) - E.KL * Real.sqrt (E.mu * E.aScat) := by
      have h3 := sub_le_sub_left hsmall (1 / (2 * E.KH * E.aScat))
      rwa [harith] at h3
    linarith
  change 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom (s - k)‖
  rw [hsub]
  exact hkey

/-! ## 3. The bundled statement -/

theorem PH_subset_PHq_sub (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        (∀ i : Mode, F.PH E.KH E.aScat i → F.PHq E.KH E.aScat i) ∧
        (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat (s - k)) := by
  refine ⟨(1 / 4 : ℝ) ^ 24, by positivity, ?_⟩
  intro Mode _ _ _ F T E hv hle _ hK
  have hsmall := ratio_small E hv hle
  exact ⟨fun i hi => PH_subset_PHq F E hv i hi,
    fun s k hfL hk => sub_mem_PHq F E hv hsmall hK.kmom_sub hK.fL_supp hfL hk⟩

end Work.BoseB7A
