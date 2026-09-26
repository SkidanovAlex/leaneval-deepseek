/-
# A neighbourhood of `𝓕̄` whose only `SL(2,ℤ)`-self-intersections come from neighbours

This file proves `Work.Asymptotics.exists_neighbour_nbdh_of_Propagates`, the geometric input to
CKMRV Proposition 3.2(1) (the propagation of the functional equations for the generating function
`F`).

The statement: given an open set `O` containing `closure 𝒟` (where `𝒟` is the `Γ(2)`-fundamental
domain (3.12)), there is an open neighbourhood `O_F` of `closure 𝓕` (the standard fundamental
domain (3.13)) such that

* each of the six translates `Mp i • O_F` stays inside `O` (`Mp = (I, T⁻¹, STS, S, ST⁻¹, TS)`,
  the translates whose closures tile `closure 𝒟`), and
* `O_F` is so small that `γ • O_F ∩ O_F ≠ ∅` forces `γ` to be a *neighbour* of `𝓕`, i.e. an
  element of `NeighborsP = {1, S, T, T⁻¹, TS, ST⁻¹, TST⁻¹}` up to sign.

The first point is `Work.Asymptotics.exists_Mp_nbdh`; the second is where the geometry enters.
`O_F` is cut down to the explicit thickening `nbdF` of `closure 𝓕`
(`Submission/Work/Asymptotics/DomainFThickening.lean`), and one shows that no non-neighbour
`γ ∈ SL(2,ℤ)` sends a point of `nbdF` into `nbdF`.

The argument is the classical reduction argument, run with explicit constants.  Write
`z = x + iy ∈ nbdF`, `w = γ • z ∈ ℍ` with `γ = (a,b;c,d)`, `det γ = 1`.  Since `nbdF` has
`Im > 3/4` and

  `Im (γ • z) = y / ‖c z + d‖²`,  `((c z + d).re)² ≤ ‖c z + d‖²`  (Mathlib),

`3/4 < Im w` gives `c² y < 4/3` and hence `c² ≤ 1` (`|c| ≤ 1`), because `y > 3/4`.  Then:

* `c = 0`: `γ = ±T^k` acts by translation, and `Re z, Re w ∈ (-1/16, 17/16)` force `|k| ≤ 1`,
  so `γ ∈ {±1, ±T, ±T⁻¹}` is a neighbour;
* `c = ±1`: the same two bounds give `(z + d)² < 7/16` (resp. `(d - z)² < 7/16`), which pins
  `d ∈ {-1,0}` (resp. `d ∈ {0,1}`), and then `w = a - 1/(z+d)` (resp. `w = -a - 1/(z-d)`),
  so `‖w - a‖ < 16/15` (resp. `‖w + a‖ < 16/15`).  Since `nbdF` is at distance `> 6/5` from
  every integer outside `{0,1}`, we get `a ∈ {0,1}` (resp. `a ∈ {0,-1}`), and the resulting
  `3 × 2` possibilities are exactly `±S, ±TS, ±ST⁻¹, ±TST⁻¹` — neighbours.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.exists_Mp_nbdh
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD
import Submission.Work.Asymptotics.DomainFThickening
import Submission.Work.Asymptotics.nbdF_c_sq_le_one
import Submission.Work.Asymptotics.nbdF_re_add_sq_lt
import Submission.Work.Asymptotics.nbdF_re_sub_sq_lt
import Submission.Work.Asymptotics.nbdF_int_eq_of_sq_lt
import Submission.Work.Asymptotics.nbdF_int_eq_zero_or_one
import Submission.Work.Asymptotics.coe_smul_eq_of_c_eq_one
import Submission.Work.Asymptotics.coe_smul_eq_of_c_eq_neg_one

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ## Some concrete neighbours -/

lemma one_mem_NeighborsP : (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

lemma neg_one_mem_NeighborsP : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

lemma T_mem_NeighborsP : (ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

lemma neg_T_mem_NeighborsP :
    (-ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

lemma T_inv_mem_NeighborsP :
    (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

lemma neg_T_inv_mem_NeighborsP :
    (-ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ NeighborsP := by
  simp [Work.Asymptotics.NeighborsP]

/-! ## The boundary pairings `S, TS, ST⁻¹, TST⁻¹` and their negatives

Each of these is a neighbour, and the four matrices with `γ 1 0 = 1` and `γ 0 0, γ 1 1` in the
ranges forced by the geometric bounds are precisely these. -/

/-- If `γ 1 0 = 1` and `(γ 0 0, γ 1 1)` is one of the four pairs `(0,0), (1,0), (0,-1), (1,-1)`
then `γ` is one of the neighbours `S, TS, ST⁻¹, TST⁻¹`. -/
lemma mem_NeighborsP_of_c_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hc : γ 1 0 = 1)
    (h0 : γ 0 0 = 0 ∨ γ 0 0 = 1) (h1 : γ 1 1 = 0 ∨ γ 1 1 = -1) : γ ∈ NeighborsP := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property; rwa [Matrix.det_fin_two] at h
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · -- `(a,d) = (0,0)`: `γ = S`
    have hb : γ 0 1 = -1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = ModularGroup.S := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (0,-1)`: `γ = S * T⁻¹`
    have hb : γ 0 1 = -1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = ModularGroup.S * ModularGroup.T⁻¹ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (1,0)`: `γ = T * S`
    have hb : γ 0 1 = -1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = ModularGroup.T * ModularGroup.S := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (1,-1)`: `γ = T * S * T⁻¹`
    have hb : γ 0 1 = -2 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]

/-- If `γ 1 0 = -1` and `(γ 0 0, γ 1 1)` is one of the four pairs `(0,0), (-1,0), (0,1), (-1,1)`
then `γ` is one of the neighbours `-S, -TS, -ST⁻¹, -TST⁻¹`. -/
lemma mem_NeighborsP_of_c_eq_neg_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hc : γ 1 0 = -1)
    (h0 : γ 0 0 = 0 ∨ γ 0 0 = -1) (h1 : γ 1 1 = 0 ∨ γ 1 1 = 1) : γ ∈ NeighborsP := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property; rwa [Matrix.det_fin_two] at h
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · -- `(a,d) = (0,0)`: `γ = -S`
    have hb : γ 0 1 = 1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = -ModularGroup.S := by
      ext i j; fin_cases i <;> fin_cases j <;>
        · rw [SpecialLinearGroup.coe_neg]; simp [ModularGroup.S, h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (0,1)`: `γ = -(S * T⁻¹)`
    have hb : γ 0 1 = 1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = -(ModularGroup.S * ModularGroup.T⁻¹) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        · rw [SpecialLinearGroup.coe_neg]; simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (-1,0)`: `γ = -(T * S)`
    have hb : γ 0 1 = 1 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = -(ModularGroup.T * ModularGroup.S) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        · rw [SpecialLinearGroup.coe_neg]; simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]
  · -- `(a,d) = (-1,1)`: `γ = -(T * S * T⁻¹)`
    have hb : γ 0 1 = 2 := by rw [h0, h1, hc] at hdet; linarith
    have heq : γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T⁻¹) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        · rw [SpecialLinearGroup.coe_neg]; simp [h0, h1, hb, hc]
    rw [heq]; simp [Work.Asymptotics.NeighborsP]

/-! ## The case `γ 1 0 = 0`: `γ` is a translate -/

/-- If the lower left entry of `γ` vanishes then `γ` is `T^k` or `-(T^k)` for the integer
`k = γ 0 0 * γ 0 1` (the image of `z` is the translate `z + k`). -/
lemma eq_T_zpow_or_neg_T_zpow {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hc : γ 1 0 = 0) :
    γ = ModularGroup.T ^ (γ 0 0 * γ 0 1) ∨ γ = -(ModularGroup.T ^ (γ 0 0 * γ 0 1)) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property; rwa [Matrix.det_fin_two] at h
  rw [hc, mul_zero, sub_zero] at hdet
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hc, ModularGroup.coe_T_zpow]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hc, ModularGroup.coe_T_zpow]

/-! ## The main geometric lemma -/

/-- No element of `SL(2,ℤ)` other than a neighbour of `𝓕` maps a point of the thickening `nbdF`
into `nbdF`. -/
theorem smul_notMem_nbdF_of_notMem_NeighborsP {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∉ NeighborsP) {z : UpperHalfPlane} (hz : z ∈ nbdF) : γ • z ∉ nbdF := by
  intro hw
  have hzy : (3 / 4 : ℝ) < z.im := im_gt_of_mem_nbdF hz
  have hwy : (3 / 4 : ℝ) < (γ • z).im := im_gt_of_mem_nbdF hw
  have hx1 : -(1 / 16 : ℝ) < z.re := (mem_nbdF.mp hz).1
  have hx2 : z.re < 1 + 1 / 16 := (mem_nbdF.mp hz).2.1
  have hn : (15 / 16 : ℝ) < ‖(z : ℂ)‖ := (mem_nbdF.mp hz).2.2.1
  have hn1 : (15 / 16 : ℝ) < ‖(z : ℂ) - 1‖ := (mem_nbdF.mp hz).2.2.2
  have hwx1 : -(1 / 16 : ℝ) < (γ • z).re := (mem_nbdF.mp hw).1
  have hwx2 : (γ • z).re < 1 + 1 / 16 := (mem_nbdF.mp hw).2.1
  -- the `c`-entry satisfies `c ^ 2 ≤ 1`
  have hc2 : (γ 1 0) ^ 2 ≤ 1 := nbdF_c_sq_le_one hz hw
  have hcases : γ 1 0 = 0 ∨ γ 1 0 = 1 ∨ γ 1 0 = -1 := by
    have hle : γ 1 0 ≤ 1 := by
      by_contra hcon
      have h2 : (2 : ℤ) ≤ γ 1 0 := by omega
      nlinarith [hc2, sq_nonneg (γ 1 0 - 1)]
    have hge : -1 ≤ γ 1 0 := by
      by_contra hcon
      have h2 : γ 1 0 ≤ (-2 : ℤ) := by omega
      nlinarith [hc2, sq_nonneg (γ 1 0 + 1)]
    omega
  rcases hcases with hc | hc | hc
  · -- `c = 0`: `γ` is a translate by the integer `γ 0 0 * γ 0 1`
    have hcases' := eq_T_zpow_or_neg_T_zpow hc
    have hRe : (γ • z).re = z.re + ((γ 0 0 * γ 0 1 : ℤ) : ℝ) := by
      rcases hcases' with h | h
      · rw [h, ModularGroup.re_T_zpow_smul]
        simp [ModularGroup.coe_T_zpow]
      · rw [h, ModularGroup.SL_neg_smul, ModularGroup.re_T_zpow_smul]
        simp [ModularGroup.coe_T_zpow]
    have hk : γ 0 0 * γ 0 1 = -1 ∨ γ 0 0 * γ 0 1 = 0 ∨ γ 0 0 * γ 0 1 = 1 := by
      have h1 : ((γ 0 0 * γ 0 1 : ℤ) : ℝ) < 1 + 1 / 8 := by linarith
      have h2 : -(1 + 1 / 8 : ℝ) < ((γ 0 0 * γ 0 1 : ℤ) : ℝ) := by linarith
      have h3 : γ 0 0 * γ 0 1 ≤ 1 := by
        by_contra hcon
        have h2' : (2 : ℤ) ≤ γ 0 0 * γ 0 1 := by omega
        have h2'' : (2 : ℝ) ≤ ((γ 0 0 * γ 0 1 : ℤ) : ℝ) := by exact_mod_cast h2'
        linarith
      have h4 : -1 ≤ γ 0 0 * γ 0 1 := by
        by_contra hcon
        have h2' : γ 0 0 * γ 0 1 ≤ (-2 : ℤ) := by omega
        have h2'' : ((γ 0 0 * γ 0 1 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h2'
        linarith
      omega
    have : γ ∈ NeighborsP := by
      rcases hcases' with h | h <;> rcases hk with hk | hk | hk <;>
        · rw [h, hk]
          simp [Work.Asymptotics.NeighborsP]
    exact hγ this
  · -- `c = 1`: `z + γ 1 1` is close to `0`
    have hsq : (z.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 < 7 / 16 := nbdF_re_add_sq_lt hz hw hc
    have hd : γ 1 1 = 0 ∨ γ 1 1 = -1 := nbdF_int_eq_of_sq_lt hx1 hx2 hsq
    have hcoe := coe_smul_eq_of_c_eq_one z hc
    -- `w - γ 0 0 = -1 / (z + γ 1 1)`
    have hdiff : ((γ • z : UpperHalfPlane) : ℂ) - ((γ 0 0 : ℤ) : ℂ) =
        -1 / ((z : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
      rw [hcoe]; ring
    have hlt : ‖((γ • z : UpperHalfPlane) : ℂ) - ((γ 0 0 : ℤ) : ℂ)‖ < 16 / 15 := by
      rcases hd with hd | hd
      · rw [hdiff, hd]
        have hz0 : (z : ℂ) + ((0 : ℤ) : ℂ) = (z : ℂ) := by push_cast; ring
        rw [hz0]
        simp only [norm_neg, norm_div, norm_one, one_div]
        simpa using (inv_lt_inv₀ (by linarith : (0:ℝ) < ‖(z : ℂ)‖)
          (by norm_num : (0:ℝ) < 15 / 16)).2 hn
      · rw [hdiff, hd]
        have hz1 : (z : ℂ) + ((-1 : ℤ) : ℂ) = (z : ℂ) - 1 := by push_cast; ring
        rw [hz1]
        simp only [norm_neg, norm_div, norm_one, one_div]
        simpa using (inv_lt_inv₀ (by linarith : (0:ℝ) < ‖(z : ℂ) - 1‖)
          (by norm_num : (0:ℝ) < 15 / 16)).2 hn1
    have ha : γ 0 0 = 0 ∨ γ 0 0 = 1 := by
      by_contra hcon
      simp only [not_or] at hcon
      have hsep := sep_nbdF hcon.1 hcon.2 hw
      linarith
    exact hγ (mem_NeighborsP_of_c_eq_one hc ha hd)
  · -- `c = -1`
    have hsq : (((γ 1 1 : ℤ) : ℝ) - z.re) ^ 2 < 7 / 16 := nbdF_re_sub_sq_lt hz hw hc
    have hd : γ 1 1 = 0 ∨ γ 1 1 = 1 := nbdF_int_eq_zero_or_one hx1 hx2 hsq
    have hcoe := coe_smul_eq_of_c_eq_neg_one z hc
    -- `w + γ 0 0 = -1 / (z - γ 1 1)`
    have hdiff : ((γ • z : UpperHalfPlane) : ℂ) - (((-γ 0 0 : ℤ)) : ℂ) =
        -1 / ((z : ℂ) - ((γ 1 1 : ℤ) : ℂ)) := by
      rw [hcoe]; push_cast; ring
    have hlt : ‖((γ • z : UpperHalfPlane) : ℂ) - (((-γ 0 0 : ℤ)) : ℂ)‖ < 16 / 15 := by
      rcases hd with hd | hd
      · rw [hdiff, hd]
        have hz0 : (z : ℂ) - ((0 : ℤ) : ℂ) = (z : ℂ) := by push_cast; ring
        rw [hz0]
        simp only [norm_neg, norm_div, norm_one, one_div]
        simpa using (inv_lt_inv₀ (by linarith : (0:ℝ) < ‖(z : ℂ)‖)
          (by norm_num : (0:ℝ) < 15 / 16)).2 hn
      · rw [hdiff, hd]
        have hz1 : (z : ℂ) - ((1 : ℤ) : ℂ) = (z : ℂ) - 1 := by push_cast; ring
        rw [hz1]
        simp only [norm_neg, norm_div, norm_one, one_div]
        simpa using (inv_lt_inv₀ (by linarith : (0:ℝ) < ‖(z : ℂ) - 1‖)
          (by norm_num : (0:ℝ) < 15 / 16)).2 hn1
    have ha : γ 0 0 = 0 ∨ γ 0 0 = -1 := by
      by_contra hcon
      simp only [not_or] at hcon
      have hsep := sep_nbdF (α := -γ 0 0) (by omega) (by omega) hw
      linarith
    exact hγ (mem_NeighborsP_of_c_eq_neg_one hc ha hd)

/-! ## The main theorem -/

theorem exists_neighbour_nbdh_of_Propagates {O : Set UpperHalfPlane} (hO : IsOpen O)
    (hD : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ O_F : Set UpperHalfPlane, IsOpen O_F ∧ closure Work.Asymptotics.DomainF ⊆ O_F ∧
      (∀ i : Fin 6, ∀ τ : UpperHalfPlane, τ ∈ O_F → (Work.Asymptotics.Mp i) • τ ∈ O) ∧
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (∃ τ : UpperHalfPlane, τ ∈ O_F ∧ γ • τ ∈ O_F) →
        γ ∈ Work.Asymptotics.NeighborsP) := by
  obtain ⟨U, hUopen, hFU, hUsub⟩ := exists_Mp_nbdh hO hD
  refine ⟨U ∩ nbdF, hUopen.inter isOpen_nbdF, Set.subset_inter hFU closure_DomainF_subset_nbdF,
    ?_, ?_⟩
  · intro i τ hτ
    exact hUsub (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hτ.1⟩)
  · rintro γ ⟨τ, hτ, hγτ⟩
    by_contra hγ
    exact smul_notMem_nbdF_of_notMem_NeighborsP hγ hτ.2 hγτ.2

end Work.Asymptotics
