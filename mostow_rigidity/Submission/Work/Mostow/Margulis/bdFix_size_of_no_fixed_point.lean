import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.ematFix
import Submission.Work.Mostow.eigNull
import Submission.Work.Mostow.cruxFixedPoint

/-!
# The boundary fixed set of a fixed-point-free isometry of `ℍⁿ`

`Work.Mostow.Margulis.bdFix_size_of_no_fixed_point`: an isometry `a` of `ℍⁿ` with no fixed point in
`ℍⁿ` fixes exactly one or exactly two points of the boundary sphere `Sph n`.

The argument is purely in the hyperboloid model:

* **Existence.**  `kleinLimit` produces a point `zs` of the closed Klein ball with
  `‖zs‖ ≤ 1`, `‖bd a zs‖ ≤ 1` and `⟪zs, bd a zs⟫ = 1`; Cauchy–Schwarz then forces
  `‖zs‖ = ‖bd a zs‖ = 1` and `bd a zs = zs`.  (This is the body of `cruxFixedPoint`, which does
  not actually use its positive-displacement hypothesis.)
* **At most two.**  Three distinct fixed boundary points `ξ₁, ξ₂, ξ₃` would give eigenvectors
  `nvec ξᵢ` of the effective matrix `emat a` with eigenvalues `μᵢ : ℝ`, and since `emat a`
  preserves the Minkowski form `mink` and `mink (nvec ξᵢ) (nvec ξⱼ) = ⟪ξᵢ,ξⱼ⟫ - 1 ≠ 0`,
  one gets `μᵢ μⱼ = 1` for `i ≠ j`.  Hence `μ₂ = μ₃`, and every eigenvalue of a null eigenvector
  is positive (`μ lev ξ (a • 0) = lev ξ 0 = 1`), so `μ₂ = μ₃ = 1`.  Then
  `nvec ξ₂ + nvec ξ₃` is a *timelike* fixed vector of `emat a`, which is the lift of a fixed point
  of `a` in `ℍⁿ` — contradiction.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Small Minkowski-form computations -/

/-- Minkowski pairing of two null vectors `nvec ξ = (ξ,1)`, `nvec η = (η,1)`. -/
lemma bdFixMink_nvec_nvec (ξ η : E n) :
    Work.Mostow.mink (Work.Mostow.nvec ξ) (Work.Mostow.nvec η) = inner ℝ ξ η - 1 := by
  rw [Work.Mostow.mink, Submission.Mostow.Hyper.inner_eq_sum]
  simp only [Work.Mostow.nvec, Sum.elim_inl, Sum.elim_inr]
  ring

/-- For two distinct points of the boundary sphere the pairing is strictly negative, hence non-zero. -/
lemma bdFixMink_nvec_nvec_ne_zero {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hne : ξ ≠ η) : Work.Mostow.mink (Work.Mostow.nvec ξ) (Work.Mostow.nvec η) ≠ 0 := by
  rw [bdFixMink_nvec_nvec]
  have hξn : ‖ξ‖ = 1 := (Work.Mostow.mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (Work.Mostow.mem_Sph_iff η).mp hη
  have hlt : inner ℝ ξ η < 1 := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
  intro h
  linarith

/-- `Work.Mostow.mink` is symmetric. -/
lemma bdFixMink_comm (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x y = Work.Mostow.mink y x := by
  rw [Work.Mostow.mink_eq_mform, Work.Mostow.mink_eq_mform, Work.Mostow.mform_comm]

/-- `Work.Mostow.mink` is homogeneous in its second argument. -/
lemma bdFixMink_smul_right (s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (s • y) = s * Work.Mostow.mink x y := by
  rw [bdFixMink_comm x (s • y), Work.Mostow.mink_smul_left, bdFixMink_comm y x]

/-- The Minkowski square of `nvec ξ₂ + nvec ξ₃`: `-2 (1 - ⟪ξ₂,ξ₃⟫)`, hence negative for distinct
boundary points. -/
lemma bdFixMink_self_add (ξ2 ξ3 : E n) (h2 : ξ2 ∈ Sph n) (h3 : ξ3 ∈ Sph n) :
    Work.Mostow.mink (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3)
      (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) = 2 * (inner ℝ ξ2 ξ3 - 1) := by
  have h2n : ‖ξ2‖ = 1 := (Work.Mostow.mem_Sph_iff ξ2).mp h2
  have h3n : ‖ξ3‖ = 1 := (Work.Mostow.mem_Sph_iff ξ3).mp h3
  rw [Work.Mostow.mink_eq_mform, Work.Mostow.mform_self_apply]
  have htime : (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) (Sum.inr 0) = 2 := by
    simp only [Pi.add_apply, Work.Mostow.nvec, Sum.elim_inr]
    norm_num
  rw [htime]
  have hsum : (∑ i : Fin n, (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) (Sum.inl i) ^ 2)
      = 2 + 2 * inner ℝ ξ2 ξ3 := by
    simp only [Work.Mostow.nvec, Pi.add_apply, Sum.elim_inl]
    rw [show (∑ i : Fin n, (ξ2 i + ξ3 i) ^ 2) =
        (∑ i, ξ2 i ^ 2) + 2 * (∑ i, ξ2 i * ξ3 i) + (∑ i, ξ3 i ^ 2) from by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring]
    rw [← Work.Mostow.norm_sq_eq_sum, ← Work.Mostow.norm_sq_eq_sum, ← Work.Mostow.inner_eq_sum]
    rw [h2n, h3n]
    ring
  rw [hsum]
  ring

/-! ## Eigenvalues of null eigenvectors -/

/-- The eigenvalue of `emat g` on a null eigenvector `nvec ξ` is positive.

Indeed `μ lev ξ (a • u) = lev ξ u` for every `u` (pair the eigenvector equation with
`hlift u` and use that `emat g` preserves `mink`), and `lev ξ 0 = 1`; the level `lev` is positive. -/
lemma bdFix_eigenval_pos (n : ℕ) (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (μ : ℝ)
    (heig : Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec ξ) = μ • Work.Mostow.nvec ξ) :
    0 < μ := by
  obtain ⟨hsheet, hisom, _⟩ := Work.Mostow.ematSpec g
  have h := hisom (Work.Mostow.nvec ξ) (Submission.Mostow.hlift (0 : E n))
  rw [heig, hsheet 0] at h
  rw [Work.Mostow.mink_smul_left] at h
  rw [Work.Mostow.mink_nvec_hlift, Work.Mostow.mink_nvec_hlift] at h
  have hlev0 : Work.Mostow.lev ξ (0 : E n) = 1 := by
    simp [Work.Mostow.lev, Submission.Mostow.tpart]
  rw [hlev0] at h
  have hpos : 0 < Work.Mostow.lev ξ (g • (0 : E n)) := Work.Mostow.lev_pos ξ hξ _
  have hpos' : 0 < μ * Work.Mostow.lev ξ (g • (0 : E n)) := by linarith
  rcases (mul_pos_iff.mp hpos') with ⟨hμ, _⟩ | ⟨hμ, hL⟩
  · exact hμ
  · exact absurd hL (not_lt.mpr (le_of_lt hpos))

/-- A *timelike* fixed vector of `emat a` is the lift of a fixed point of `a` in `ℍⁿ`. -/
lemma bdFix_fixed_point_of_timelike {n : ℕ} (a : PO n 1) (v : Fin n ⊕ Fin 1 → ℝ)
    (hmink : Work.Mostow.mink v v < 0) (hpos : 0 < v (Sum.inr 0))
    (heig : Matrix.mulVec (Work.Mostow.emat a) v = v) :
    ∃ u : E n, a • u = u := by
  set c : ℝ := Real.sqrt (-(Work.Mostow.mink v v)) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hcsq : c ^ 2 = -(Work.Mostow.mink v v) := by
    rw [hcdef, Real.sq_sqrt (by linarith)]
  refine ⟨Submission.Mostow.Hyper.spat (c⁻¹ • v), ?_⟩
  have hy : Submission.Mostow.hlift (Submission.Mostow.Hyper.spat (c⁻¹ • v)) = c⁻¹ • v := by
    apply Submission.Mostow.Hyper.hlift_spat_of_mink
    · rw [Submission.Mostow.Hyper.mink_smul, ← Work.Mostow.eigNull_mink_eq_hyper]
      field_simp
      nlinarith [hcsq]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_pos (inv_pos.mpr hcpos) hpos
  have heig' : Matrix.mulVec (Work.Mostow.emat a)
      (Submission.Mostow.hlift (Submission.Mostow.Hyper.spat (c⁻¹ • v)))
      = Submission.Mostow.hlift (Submission.Mostow.Hyper.spat (c⁻¹ • v)) := by
    rw [hy, Matrix.mulVec_smul, heig]
  have hsheet := (Work.Mostow.ematSpec a).1
  apply Submission.Mostow.Hyper.hlift_injective
  rw [← hsheet (Submission.Mostow.Hyper.spat (c⁻¹ • v))]
  exact heig'

/-! ## Existence of a fixed boundary point -/

/-- A fixed-point-free isometry of `ℍⁿ` (`n ≥ 1`) fixes a point of the boundary sphere.

This is the body of `Work.Mostow.cruxFixedPoint`; the positive-displacement hypothesis of that
statement is not used (`kleinLimit` needs none). -/
lemma bdFix_exists_fixed_boundary (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u) :
    ∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ := by
  obtain ⟨zs, hzsle, hwsle, hkey⟩ := Work.Mostow.kleinLimit n hn hA hI g hne
  have hcs : inner ℝ zs (bd g zs) ≤ ‖zs‖ * ‖bd g zs‖ := real_inner_le_norm zs (bd g zs)
  have h1 : 1 ≤ ‖zs‖ * ‖bd g zs‖ := by rw [← hkey]; exact hcs
  have h2 : ‖zs‖ * ‖bd g zs‖ ≤ 1 := by
    calc ‖zs‖ * ‖bd g zs‖ ≤ 1 * 1 := mul_le_mul hzsle hwsle (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hmul_eq : ‖zs‖ * ‖bd g zs‖ = 1 := le_antisymm h2 h1
  have hnormzs : ‖zs‖ = 1 := by
    have h3 : ‖zs‖ * ‖bd g zs‖ ≤ ‖zs‖ * 1 :=
      mul_le_mul_of_nonneg_left hwsle (norm_nonneg zs)
    linarith
  have hnormw : ‖bd g zs‖ = 1 := by
    have h := hmul_eq; rw [hnormzs, one_mul] at h; exact h
  refine ⟨zs, ?_, ?_⟩
  · rw [Work.Mostow.mem_Sph_iff]; exact hnormzs
  · have heq : inner ℝ zs (bd g zs) = ‖zs‖ * ‖bd g zs‖ := by rw [hkey, hmul_eq]
    have h2' := inner_eq_norm_mul_iff.mp heq
    rw [hnormzs, hnormw] at h2'
    simpa using h2'.symm

/-! ## No three distinct fixed boundary points -/

/-- A fixed-point-free isometry of `ℍⁿ` (`n ≥ 1`) cannot fix three distinct boundary points. -/
lemma bdFix_not_three (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (_hI : HypIsometryProp n)
    (a : PO n 1) (hnofix : ∀ u : E n, a • u ≠ u)
    (ξ1 ξ2 ξ3 : E n) (h1 : ξ1 ∈ Sph n) (h2 : ξ2 ∈ Sph n) (h3 : ξ3 ∈ Sph n)
    (hne12 : ξ1 ≠ ξ2) (hne13 : ξ1 ≠ ξ3) (hne23 : ξ2 ≠ ξ3)
    (hf1 : bd a ξ1 = ξ1) (hf2 : bd a ξ2 = ξ2) (hf3 : bd a ξ3 = ξ3) : False := by
  obtain ⟨μ1, hμ1ne, heig1⟩ := (Work.Mostow.bdFixIff n hn hA a ξ1 h1).mp hf1
  obtain ⟨μ2, _, heig2⟩ := (Work.Mostow.bdFixIff n hn hA a ξ2 h2).mp hf2
  obtain ⟨μ3, _, heig3⟩ := (Work.Mostow.bdFixIff n hn hA a ξ3 h3).mp hf3
  have hisom := (Work.Mostow.ematSpec a).2.1
  -- eigenvalues of distinct null eigenvectors are reciprocal
  have hrel : ∀ (x y : Fin n ⊕ Fin 1 → ℝ) (μ ν : ℝ),
      Matrix.mulVec (Work.Mostow.emat a) x = μ • x →
      Matrix.mulVec (Work.Mostow.emat a) y = ν • y →
      Work.Mostow.mink x y ≠ 0 → μ * ν = 1 := by
    intro x y μ ν hx hy hxy
    have h := hisom x y
    rw [hx, hy] at h
    rw [Work.Mostow.mink_smul_left, bdFixMink_smul_right] at h
    have h' : (μ * ν) * Work.Mostow.mink x y = 1 * Work.Mostow.mink x y := by
      rw [one_mul]
      linear_combination h
    exact mul_right_cancel₀ hxy h'
  have h12 := hrel (Work.Mostow.nvec ξ1) (Work.Mostow.nvec ξ2) μ1 μ2 heig1 heig2
    (bdFixMink_nvec_nvec_ne_zero h1 h2 hne12)
  have h13 := hrel (Work.Mostow.nvec ξ1) (Work.Mostow.nvec ξ3) μ1 μ3 heig1 heig3
    (bdFixMink_nvec_nvec_ne_zero h1 h3 hne13)
  have h23 := hrel (Work.Mostow.nvec ξ2) (Work.Mostow.nvec ξ3) μ2 μ3 heig2 heig3
    (bdFixMink_nvec_nvec_ne_zero h2 h3 hne23)
  have hμ23eq : μ2 = μ3 := mul_left_cancel₀ hμ1ne (by linarith : μ1 * μ2 = μ1 * μ3)
  have hμ2pos : 0 < μ2 := bdFix_eigenval_pos n a ξ2 h2 μ2 heig2
  have hμ2sq : μ2 * μ2 = 1 := by rw [← hμ23eq] at h23; exact h23
  have hμ2one : μ2 = 1 := by nlinarith
  -- `nvec ξ₂ + nvec ξ₃` is a timelike fixed vector
  have hAv : Matrix.mulVec (Work.Mostow.emat a) (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3)
      = μ2 • (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) := by
    rw [Matrix.mulVec_add, heig2, heig3, ← hμ23eq, smul_add]
  rw [hμ2one, one_smul] at hAv
  have hneg : Work.Mostow.mink (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3)
      (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) < 0 := by
    rw [bdFixMink_self_add ξ2 ξ3 h2 h3]
    have hlt : inner ℝ ξ2 ξ3 < 1 :=
      (inner_lt_one_iff_real_of_norm_eq_one ((Work.Mostow.mem_Sph_iff ξ2).mp h2)
        ((Work.Mostow.mem_Sph_iff ξ3).mp h3)).mpr hne23
    linarith
  have hpos : 0 < (Work.Mostow.nvec ξ2 + Work.Mostow.nvec ξ3) (Sum.inr 0) := by
    simp only [Pi.add_apply, Work.Mostow.nvec, Sum.elim_inr]; norm_num
  obtain ⟨u, hu⟩ := bdFix_fixed_point_of_timelike a _ hneg hpos hAv
  exact hnofix u hu

/-! ## The theorem -/

/-- An isometry of `ℍⁿ` with no fixed point in `ℍⁿ` (hence parabolic or loxodromic) fixes exactly
one or exactly two points of the boundary sphere `Sph n`.  Here `bdFix a = {ξ | ξ ∈ Sph n ∧ bd a ξ = ξ}`
is the boundary fixed set of `a`. -/
theorem bdFix_size_of_no_fixed_point (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (a : PO n 1) (hnofix : ∀ u : E n, a • u ≠ u) :
    (∃ ξ ∈ Sph n, bdFix a = {ξ}) ∨
      (∃ ξ ∈ Sph n, ∃ η ∈ Sph n, ξ ≠ η ∧ bdFix a = {ξ, η}) := by
  by_cases hn0 : n = 0
  · -- `E 0` is a single point, so there is no fixed-point-free isometry
    subst hn0
    exact absurd (Subsingleton.elim (a • (0 : E 0)) 0) (hnofix 0)
  · have hn1 : 1 ≤ n := by omega
    obtain ⟨ξ1, hξ1S, hξ1fix⟩ := bdFix_exists_fixed_boundary n hn1 hA hI a hnofix
    have hξ1 : ξ1 ∈ bdFix a := ⟨hξ1S, hξ1fix⟩
    by_cases h2 : ∃ η ∈ bdFix a, η ≠ ξ1
    · -- two distinct fixed points: the fixed set is exactly the pair
      obtain ⟨η, hη, hηne⟩ := h2
      refine Or.inr ⟨ξ1, hξ1S, η, hη.1, hηne.symm, ?_⟩
      ext ζ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hζ
        by_contra hc
        rw [not_or] at hc
        exact bdFix_not_three n hn1 hA hI a hnofix ξ1 η ζ hξ1S hη.1 hζ.1
          hηne.symm (Ne.symm hc.1) (Ne.symm hc.2) hξ1fix hη.2 hζ.2
      · rintro (rfl | rfl)
        · exact hξ1
        · exact hη
    · -- a single fixed point
      push Not at h2
      refine Or.inl ⟨ξ1, hξ1S, ?_⟩
      ext ζ
      rw [Set.mem_singleton_iff]
      exact ⟨fun hζ => h2 ζ hζ, fun h => h ▸ hξ1⟩

end Work.Mostow.Margulis
