import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.BCSToE
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.BCS.shortest_vec

/-!
# Geometry of numbers for `latZero_bound`

This file proves `Work.HP.Q44Child.latZeroGeom`, the reduced-basis input used in §3.4 of
Browning--Le Boudec--Sawin (the bound `N_c(Z;L) ≪ (Z/s₁)(Z/s₂)` for `L ∈ T_{3,4}`).

The construction is Davenport's: `b₀` is a shortest nonzero vector of `L`,
`b₁ ∈ L∖ℝb₀` minimises the distance to `ℝb₀` (i.e. `‖projScale b₀ b₁‖`),
`b₂ ∈ L∖span(b₀,b₁)` minimises the distance to `span(b₀,b₁)` and is normalised modulo `b₁`
so that the coefficient of `π_{b₀^⊥}b₁` in `π_{b₀^⊥}b₂` lies in `[-1/2,1/2]`.
The three vectors then form a `ℤ`-basis of `L` ("saturation"), and the two coefficient bounds
follow from the successive-minima comparison `lam_projScale_le`
(`(√3/2)‖u‖²λ_{j+1}(L) ≤ λ_j(projScale u '' L)`) applied to `L` and to its first projection.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Work.HP.Q44Child

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 0. Projection infrastructure

The lemmas in this section are the parts of the orthogonal-projection toolkit needed below; they
are proved here so that this file only depends on `Work.HP.BCSDefs` (the projection `projU`, the
inclusion `toEZ`) and on `Work.HP.MDEstimates.rk_projScale`. -/

/-- The Euclidean inner product of `toEZ v`, `toEZ w` is the integer `dotZ v w`. -/
lemma inner_toE_dotZ' (v w : ι → ℤ) :
    inner ℝ (Work.HP.toEZ v) (Work.HP.toEZ w) = ((Work.HP.dotZ v w : ℤ) : ℝ) := by
  simp [Work.HP.toEZ, Work.HP.dotZ_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    mul_comm]

/-- `‖toEZ u‖²` is the integer `dotZ u u`. -/
lemma norm_toE_sq_dotZ' (u : ι → ℤ) :
    ‖Work.HP.toEZ u‖ ^ 2 = ((Work.HP.dotZ u u : ℤ) : ℝ) := by
  rw [← Work.HP.eNorm_sq_eq u, Work.HP.norm_toEZ]

/-- `toEZ (projScale u y)` is `‖u‖²` times the orthogonal projection of `toEZ y` onto `u^⊥`. -/
lemma toE_projScale' (u y : ι → ℤ) (hu : u ≠ 0) :
    Work.HP.toEZ (Work.HP.projScale u y)
      = (Work.HP.eNorm u) ^ 2 • Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ y) := by
  have hA : ‖Work.HP.toEZ u‖ ^ 2 ≠ 0 := by
    rw [Work.HP.norm_toEZ]
    exact pow_ne_zero 2 (ne_of_gt (Work.HP.eNorm_pos_of_ne_zero hu))
  rw [← Work.HP.norm_toEZ u, Work.HP.projScale_apply]
  change Work.HP.toEHom (Work.HP.dotZ u u • y - Work.HP.dotZ y u • u) = _
  rw [map_sub, map_smul, map_smul]
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
  rw [show ((Work.HP.dotZ u u : ℤ) : ℝ) = ‖Work.HP.toEZ u‖ ^ 2 from
    (by rw [← Work.HP.eNorm_sq_eq u, Work.HP.norm_toEZ])]
  rw [show ((Work.HP.dotZ y u : ℤ) : ℝ) = inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) from
    (by rw [inner_toE_dotZ'])]
  rw [Work.HP.projU_apply, smul_sub, smul_smul,
    show ‖Work.HP.toEZ u‖ ^ 2 *
          ((‖Work.HP.toEZ u‖ ^ 2)⁻¹ * inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u))
        = inner ℝ (Work.HP.toEZ y) (Work.HP.toEZ u) from by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]]
  simp only [Work.HP.toEHom_apply]

/-- The Euclidean norm of `projScale u y` is `‖u‖²` times the norm of the orthogonal
projection of `y` onto `u^⊥`. -/
lemma eNorm_projScale' (u y : ι → ℤ) (hu : u ≠ 0) :
    Work.HP.eNorm (Work.HP.projScale u y)
      = (Work.HP.eNorm u) ^ 2 * ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ y)‖ := by
  rw [← Work.HP.norm_toEZ (Work.HP.projScale u y), toE_projScale' u y hu, norm_smul,
    Real.norm_of_nonneg (by positivity)]

/-- **Lifting bound.**  Any element `y` of `projScale u '' L` admits a lift `x ∈ L` with
`projScale u x = y` and `‖x‖² ≤ ‖y‖²/‖u‖⁴ + ‖u‖²/4`. -/
theorem exists_lift_norm' (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    {y : ι → ℤ} (hy : y ∈ Submodule.map (Work.HP.projScale u) L) :
    ∃ x ∈ L, Work.HP.projScale u x = y ∧
      Work.HP.eNorm x ^ 2 ≤
        Work.HP.eNorm y ^ 2 / Work.HP.eNorm u ^ 4 + Work.HP.eNorm u ^ 2 / 4 := by
  obtain ⟨x0, hx0L, hx0⟩ := Submodule.mem_map.mp hy
  have hu_norm_pos : 0 < ‖Work.HP.toEZ u‖ := by
    rw [Work.HP.norm_toEZ]; exact Work.HP.eNorm_pos_of_ne_zero hu0
  have hu_norm_ne : ‖Work.HP.toEZ u‖ ≠ 0 := ne_of_gt hu_norm_pos
  set r : ℝ := (‖Work.HP.toEZ u‖ ^ 2)⁻¹ * inner ℝ (Work.HP.toEZ x0) (Work.HP.toEZ u) with hr
  set m : ℤ := ⌊r + 1 / 2⌋ with hmdef
  have hm_cl : |r - (m : ℝ)| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ r + 1 / 2 := by rw [hmdef]; exact Int.floor_le (r + 1 / 2)
    have h2 : r + 1 / 2 < (m : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one (r + 1 / 2)
    rw [abs_le]; constructor <;> linarith
  refine ⟨x0 - m • u, L.sub_mem hx0L (L.smul_mem m hu), ?_, ?_⟩
  · rw [map_sub, map_smul]
    have hpu : Work.HP.projScale u u = 0 := by simp [Work.HP.projScale_apply]
    rw [hpu, smul_zero, sub_zero]; exact hx0
  · have hdec' : Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)
        = Work.HP.toEZ x0 - r • Work.HP.toEZ u := by
      rw [Work.HP.projU_apply, ← hr]
    have htoe : Work.HP.toEZ (x0 - m • u)
        = Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0) + (r - (m : ℝ)) • Work.HP.toEZ u := by
      have hz : Work.HP.toEZ (x0 - m • u)
          = Work.HP.toEZ x0 - (m : ℝ) • Work.HP.toEZ u := by
        change Work.HP.toEHom (x0 - m • u) = _
        rw [map_sub, map_smul, Work.HP.toEHom_apply, Work.HP.toEHom_apply]
        rw [← Int.cast_smul_eq_zsmul ℝ]
      rw [hz, hdec']
      module
    have hpy : ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)‖
        = ‖Work.HP.toEZ y‖ / ‖Work.HP.toEZ u‖ ^ 2 := by
      have h := toE_projScale' u x0 hu0
      rw [hx0] at h
      have h2 : ‖Work.HP.toEZ y‖
          = Work.HP.eNorm u ^ 2 * ‖Work.HP.projU (Work.HP.toEZ u) (Work.HP.toEZ x0)‖ := by
        rw [h, norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [h2, ← Work.HP.norm_toEZ u, mul_div_cancel_left₀ _ (pow_ne_zero 2 hu_norm_ne)]
    have herr1 : ((r - (m : ℝ)) * ‖Work.HP.toEZ u‖) ^ 2 ≤ ‖Work.HP.toEZ u‖ ^ 2 / 4 := by
      rw [mul_pow]
      have h1 : (r - (m : ℝ)) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_abs (r - (m : ℝ)), abs_nonneg (r - (m : ℝ))]
      calc (r - (m : ℝ)) ^ 2 * ‖Work.HP.toEZ u‖ ^ 2
          ≤ (1 / 4) * ‖Work.HP.toEZ u‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = ‖Work.HP.toEZ u‖ ^ 2 / 4 := by ring
    have herr2 : (‖Work.HP.toEZ y‖ / ‖Work.HP.toEZ u‖ ^ 2) ^ 2
        = ‖Work.HP.toEZ y‖ ^ 2 / ‖Work.HP.toEZ u‖ ^ 4 := by
      rw [div_pow]; congr 1; ring
    rw [← Work.HP.norm_toEZ (x0 - m • u), ← Work.HP.norm_toEZ y, ← Work.HP.norm_toEZ u]
    rw [htoe, Work.HP.norm_sq_add_smul', hpy, herr2]
    linarith [herr1]

/-! ## 0b. Successive minima under the scaled projection -/

/-- Adding the kernel vector back: if the images of a family `x` under the scaled projection
`projScale u` are linearly independent, then `u` together with `x` is linearly independent. -/
lemma linIndep_fin_cons_projScale' (u : ι → ℤ) (hu0 : u ≠ 0) {n : ℕ}
    (f x : Fin n → (ι → ℤ)) (hf : LinearIndependent ℤ f)
    (hpx : ∀ k, projScale u (x k) = f k) :
    LinearIndependent ℤ (Fin.cons u x : Fin (n + 1) → (ι → ℤ)) := by
  let Y : Fin (n + 1) → (ι → ℤ) := Fin.cons u x
  have hY0 : Y 0 = u := rfl
  have hYs : ∀ k : Fin n, Y k.succ = x k := fun k => rfl
  have hpu : projScale u u = 0 := by rw [projScale_apply]; simp
  have hf' := hf
  rw [Fintype.linearIndependent_iff] at hf'
  have key : ∀ a : Fin (n + 1) → ℤ, (∑ i, a i • Y i) = 0 → ∀ i, a i = 0 := by
    intro a ha
    have hproj : (∑ k : Fin n, a k.succ • f k) = 0 := by
      have h := congrArg (fun z : ι → ℤ => projScale u z) ha
      rw [map_sum, map_zero] at h
      have h2 : (∑ i : Fin (n + 1), projScale u (a i • Y i))
          = ∑ i : Fin (n + 1), a i • projScale u (Y i) :=
        Finset.sum_congr rfl fun i _ => map_smul (projScale u) (a i) (Y i)
      rw [h2] at h
      rw [Fin.sum_univ_succ] at h
      simp only [hY0, hYs, hpx, hpu, smul_zero, zero_add] at h
      exact h
    have hzero : ∀ k : Fin n, a k.succ = 0 := fun k => hf' (fun k => a k.succ) hproj k
    have ha0smul : a 0 • u = 0 := by
      have h := ha
      rw [Fin.sum_univ_succ] at h
      have hz : (∑ k : Fin n, a k.succ • Y k.succ) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hzero k, zero_smul]
      rw [hY0, hz, add_zero] at h
      exact h
    have ha0 : a 0 = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hu0
      have h := congrFun ha0smul i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact absurd h (mul_ne_zero hne hi)
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
    · rw [h]; exact ha0
    · rw [hk]; exact hzero k
  change LinearIndependent ℤ Y
  rw [Fintype.linearIndependent_iff]
  exact key

/-- `λ_n(L) ≤ ρ` as soon as `L` contains `n` linearly independent vectors of norm `≤ ρ`. -/
lemma lam_le_of_norms' (L : Submodule ℤ (ι → ℤ)) {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {f : Fin n → (ι → ℤ)} (hfL : ∀ i, f i ∈ L) (hfI : LinearIndependent ℤ f)
    (hfn : ∀ i, eNorm (f i) ≤ ρ) : lam L n ≤ ρ := by
  rw [lam_eq_sInf]
  exact csInf_le (bddBelow_lamSet L n) ⟨hρ, f, hfL, hfI, hfn⟩

/-- A shortest nonzero vector of `L` lies on the first successive minimum from above:
`‖u‖ ≤ λ_1(L)`. -/
lemma le_lam_one_of_shortest' (L : Submodule ℤ (ι → ℤ)) {u : ι → ℤ} (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v) : eNorm u ≤ lam L 1 := by
  rw [lam_eq_sInf]
  refine le_csInf ?hne ?hlower
  · exact ⟨eNorm u, eNorm_nonneg u, (fun _ : Fin 1 => u), (fun _ => hu),
      linearIndependent_unique_iff.mpr hu0, fun _ => le_rfl⟩
  · rintro r ⟨-, f, hfL, hfI, hfr⟩
    exact (hshort (f 0) (hfL 0) (hfI.ne_zero 0)).trans (hfr 0)

/-- Arithmetic in the case `‖u‖ < λ_{j+1}(L)`. -/
lemma arith_case_lt' {A t s : ℝ} (hA : 0 < A) (ht : 0 < t) (hAt : A < t)
    (hs : 0 ≤ s) (hsc : s < Real.sqrt 3 / 2 * A ^ 2 * t) :
    s ^ 2 / A ^ 4 + A ^ 2 / 4 < t ^ 2 := by
  have hA4 : (0 : ℝ) < A ^ 4 := by positivity
  have hsq : s ^ 2 < 3 / 4 * (A ^ 4 * t ^ 2) := by
    have h1 : s ^ 2 < (Real.sqrt 3 / 2 * A ^ 2 * t) ^ 2 :=
      pow_lt_pow_left₀ hsc hs (by norm_num)
    have h2 : (Real.sqrt 3 / 2 * A ^ 2 * t) ^ 2 = 3 / 4 * (A ^ 4 * t ^ 2) := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    linarith [h1, h2]
  have h3 : s ^ 2 / A ^ 4 < 3 / 4 * t ^ 2 := by
    rw [div_lt_iff₀ hA4]
    nlinarith [hsq]
  nlinarith [h3, hA, hAt]

/-- Arithmetic in the case `‖u‖ = λ_{j+1}(L)`. -/
lemma arith_case_eq' {A s : ℝ} (hA : 0 < A) (hs : 0 ≤ s)
    (hsc : s < Real.sqrt 3 / 2 * A ^ 2 * A) :
    s ^ 2 / A ^ 4 + A ^ 2 / 4 < A ^ 2 := by
  have hA4 : (0 : ℝ) < A ^ 4 := by positivity
  have hsq : s ^ 2 < 3 / 4 * (A ^ 4 * A ^ 2) := by
    have h1 : s ^ 2 < (Real.sqrt 3 / 2 * A ^ 2 * A) ^ 2 :=
      pow_lt_pow_left₀ hsc hs (by norm_num)
    have h2 : (Real.sqrt 3 / 2 * A ^ 2 * A) ^ 2 = 3 / 4 * (A ^ 4 * A ^ 2) := by
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    linarith [h1, h2]
  have h3 : s ^ 2 / A ^ 4 < 3 / 4 * A ^ 2 := by
    rw [div_lt_iff₀ hA4]
    nlinarith [hsq]
  linarith [h3]

/-- **Successive minima under the scaled projection.**  If `u` is a shortest nonzero vector of
the integral lattice `L`, then for `1 ≤ j ≤ rk L - 1` the `j`-th successive minimum of the
projected lattice `projScale u '' L` is at least `(√3/2)‖u‖²` times the `(j+1)`-st successive
minimum of `L`. -/
theorem lam_projScale_le' (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → Work.HP.eNorm u ≤ Work.HP.eNorm v) (j : ℕ) (hj : 1 ≤ j)
    (hjR : j ≤ Work.HP.rk L - 1) :
    Real.sqrt 3 / 2 * Work.HP.eNorm u ^ 2 * Work.HP.lam L (j + 1) ≤
      Work.HP.lam (Submodule.map (Work.HP.projScale u) L) j := by
  classical
  set A : ℝ := eNorm u with hA
  set t : ℝ := lam L (j + 1) with ht
  set Lp : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hLp
  set c : ℝ := Real.sqrt 3 / 2 * A ^ 2 * t with hc
  have hApos : 0 < A := by rw [hA]; exact eNorm_pos_of_ne_zero hu0
  have hshortA : ∀ v ∈ L, v ≠ 0 → A ≤ eNorm v := fun v hv hv0 => by
    rw [hA]; exact hshort v hv hv0
  have hrkLp : rk Lp = rk L - 1 := by rw [hLp]; exact MDEstimates.rk_projScale L u hu hu0 hshort
  have hjLp : j ≤ rk Lp := by omega
  have hAle : A ≤ t := by
    rw [ht, hA]
    exact (le_lam_one_of_shortest' L hu hu0 hshort).trans
      (lam_mono L (i := 1) (j := j + 1) (by omega) (by omega))
  have htpos : 0 < t := by
    rw [ht]
    exact lam_pos L (by omega) (by omega)
  have hcpos : 0 < c := by rw [hc]; positivity
  by_contra hcon
  push_neg at hcon
  set s : ℝ := (lam Lp j + c) / 2 with hs
  have hlam_lt_s : lam Lp j < s := by rw [hs]; linarith
  have hs_lt_c : s < c := by rw [hs]; linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    have h := lam_nonneg Lp j
    linarith
  obtain ⟨f, hfLp, hfI, hfn⟩ := lam_witness Lp hjLp hlam_lt_s
  have hlift : ∀ k : Fin j, ∃ x ∈ L, projScale u x = f k ∧
      eNorm x ^ 2 ≤ eNorm (f k) ^ 2 / A ^ 4 + A ^ 2 / 4 := by
    intro k
    obtain ⟨x, hxL, hxeq, hxbd⟩ := exists_lift_norm' L u hu hu0 (hfLp k)
    rw [← hA] at hxbd
    exact ⟨x, hxL, hxeq, hxbd⟩
  choose g hgL hgproj hgbd using hlift
  have hgbd' : ∀ k : Fin j, eNorm (g k) ^ 2 ≤ s ^ 2 / A ^ 4 + A ^ 2 / 4 := by
    intro k
    have h1 : eNorm (f k) ^ 2 ≤ s ^ 2 := by
      nlinarith [eNorm_nonneg (f k), hfn k, hs_nonneg]
    have h2 : eNorm (f k) ^ 2 / A ^ 4 ≤ s ^ 2 / A ^ 4 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    linarith [hgbd k, h2]
  have hgI : LinearIndependent ℤ (Fin.cons u g) :=
    linIndep_fin_cons_projScale' u hu0 f g hfI hgproj
  rcases lt_or_ge A t with hAt | hAt
  · let fam : Fin (j + 1) → (ι → ℤ) := Fin.cons u g
    have hfamI : LinearIndependent ℤ fam := hgI
    have hgn : ∀ k : Fin j, eNorm (g k) < t := by
      intro k
      have h1 : eNorm (g k) ^ 2 < t ^ 2 := by
        have h2 : s ^ 2 / A ^ 4 + A ^ 2 / 4 < t ^ 2 :=
          arith_case_lt' hApos htpos hAt hs_nonneg hs_lt_c
        linarith [hgbd' k, h2]
      have h3 : |eNorm (g k)| < |t| := sq_lt_sq.mp h1
      rwa [abs_of_nonneg (eNorm_nonneg (g k)), abs_of_pos htpos] at h3
    have hfam_lt : ∀ i : Fin (j + 1), eNorm (fam i) < t := by
      intro i
      dsimp only [fam]
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
      · rw [h, Fin.cons_zero]; exact hAt
      · rw [hk, Fin.cons_succ]; exact hgn k
    have hne : (Finset.univ : Finset (Fin (j + 1))).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨i₀, -, hmax⟩ :=
      (Finset.univ : Finset (Fin (j + 1))).exists_max_image (fun i => eNorm (fam i)) hne
    have hMlt : eNorm (fam i₀) < t := hfam_lt i₀
    have hle : t ≤ eNorm (fam i₀) := by
      have hfamL : ∀ i : Fin (j + 1), fam i ∈ L := by
        intro i
        dsimp only [fam]
        rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, hk⟩
        · rw [h, Fin.cons_zero]; exact hu
        · rw [hk, Fin.cons_succ]; exact hgL k
      rw [ht]
      exact lam_le_of_norms' L (eNorm_nonneg (fam i₀)) hfamL hfamI
        (fun i => hmax i (Finset.mem_univ i))
    exact absurd hle (not_le.mpr hMlt)
  · have hAeq : A = t := le_antisymm hAle hAt
    set k0 : Fin j := ⟨0, by omega⟩ with hk0def
    have hgn0 : eNorm (g k0) < A := by
      have h1 : eNorm (g k0) ^ 2 < A ^ 2 := by
        have h2 : s ^ 2 / A ^ 4 + A ^ 2 / 4 < A ^ 2 := by
          refine arith_case_eq' hApos hs_nonneg ?_
          have hsc := hs_lt_c
          rw [hc, ← hAeq] at hsc
          exact hsc
        linarith [hgbd' k0, h2]
      have h3 : |eNorm (g k0)| < |A| := sq_lt_sq.mp h1
      rwa [abs_of_nonneg (eNorm_nonneg (g k0)), abs_of_pos hApos] at h3
    have hg0ne : g k0 ≠ 0 := by
      intro h0
      have h1 : f k0 = 0 := by rw [← hgproj k0, h0, map_zero]
      exact hfI.ne_zero k0 h1
    have hmin0 := hshortA (g k0) (hgL k0) hg0ne
    linarith


/-! ## 1. Scaled projections: elementary identities -/

/-- `projScale u u = 0`. -/
lemma projScale_self_apply (u : ι → ℤ) : projScale u u = 0 := by
  rw [projScale_apply, sub_self]

/-- The norm of a scaled projection is at most `‖u‖²‖x‖`. -/
lemma eNorm_projScale_le' (u x : ι → ℤ) :
    eNorm (projScale u x) ≤ eNorm u ^ 2 * eNorm x := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : dotZ (0 : ι → ℤ) 0 = 0 := by simp [dotZ_apply]
    have h : projScale (0 : ι → ℤ) x = 0 := by rw [projScale_apply, h1]; simp
    rw [h, show eNorm (0 : ι → ℤ) = 0 from by simp [eNorm]]
    simp
  · rw [eNorm_projScale' u x hu, ← Work.HP.norm_toEZ x]
    exact mul_le_mul_of_nonneg_left (Work.HP.norm_projU_le (Work.HP.toEZ u) (Work.HP.toEZ x))
      (by positivity)

/-! ## 2. A shortest nonzero vector of a rank-one lattice generates it -/

/-- **A shortest nonzero vector of a rank-one sublattice generates it.**

If `M ⊆ ℤ^ι` is a sublattice of `ℤ`-rank one and `v ∈ M` is a nonzero vector of minimal
Euclidean norm in `M`, then every element of `M` is an integer multiple of `v`. -/
lemma rank_one_shortest_generates {M : Submodule ℤ (ι → ℤ)} (hM : rk M = 1) {v : ι → ℤ}
    (hv : v ∈ M) (hv0 : v ≠ 0) (hmin : ∀ y ∈ M, y ≠ 0 → eNorm v ≤ eNorm y) :
    ∀ y ∈ M, ∃ k : ℤ, y = k • v := by
  classical
  obtain ⟨n, bb⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) M
  have hn : n = 1 := by
    have h1 : Module.finrank ℤ M = n := by
      rw [Module.finrank_eq_card_basis bb, Fintype.card_fin]
    have h2 : Module.finrank ℤ M = 1 := hM
    omega
  subst hn
  set z : ι → ℤ := (bb 0 : ι → ℤ) with hz
  have hzM : z ∈ M := (bb 0).2
  have hz0 : z ≠ 0 := by
    intro h
    have h0 : bb 0 = 0 := Subtype.ext (by rw [← hz]; exact h)
    exact bb.ne_zero 0 h0
  have key : ∀ w : M, ∃ c : ℤ, (w : ι → ℤ) = c • z := by
    intro w
    have h : w ∈ Submodule.span ℤ (Set.range bb) := by
      rw [Module.Basis.span_eq]; trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c 0, ?_⟩
    have h2 := congrArg Subtype.val hc
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [Fin.sum_univ_one] at h2
    simpa [hz] using h2.symm
  obtain ⟨c, hcz⟩ := key ⟨v, hv⟩
  have hc : v = c • z := hcz
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hv0 hc
  have hcle : |(c : ℝ)| ≤ 1 := by
    have h1 : eNorm v = |(c : ℝ)| * eNorm z := by rw [hc, MDEstimates.eNorm_smul_int]
    have h2 := hmin z hzM hz0
    have h3 : 0 < eNorm z := eNorm_pos_of_ne_zero hz0
    rw [h1] at h2
    nlinarith [h2, h3]
  have hcabs : c = 1 ∨ c = -1 := by
    have h1 : (1 : ℤ) ≤ |c| := Int.one_le_abs hcne
    have h2 : (|c| : ℤ) ≤ 1 := by exact_mod_cast hcle
    have h3 : |c| = 1 := le_antisymm h2 h1
    exact (abs_eq (by norm_num : (0:ℤ) ≤ 1)).mp h3
  have hcc : c * c = 1 := by rcases hcabs with h | h <;> rw [h] <;> ring
  intro y hy
  obtain ⟨d, hdz⟩ := key ⟨y, hy⟩
  have hd : y = d • z := hdz
  refine ⟨d * c, ?_⟩
  rw [hd, hc, smul_smul, show d * c * c = d from by rw [mul_assoc, hcc, mul_one]]

/-! ## 3. Two vectors cannot both project to zero -/

/-- If `b₀ ∈ L` is a shortest nonzero vector of `L` and `f₀, f₁ ∈ L` are `ℤ`-linearly independent,
then they are not both annihilated by the scaled projection `projScale b₀`. -/
lemma not_both_projScale_zero {L : Submodule ℤ (ι → ℤ)} {b₀ : ι → ℤ} (hb₀L : b₀ ∈ L)
    (hb₀0 : b₀ ≠ 0) (hmin₀ : ∀ x ∈ L, x ≠ 0 → eNorm b₀ ≤ eNorm x)
    {f : Fin 2 → ι → ℤ} (hfL : ∀ i, f i ∈ L) (hfI : LinearIndependent ℤ f)
    (hz : ∀ i, projScale b₀ (f i) = 0) : False := by
  obtain ⟨m, hm⟩ := MDEstimates.projScale_eq_zero_imp L hb₀L hb₀0 hmin₀ (hfL 0) (hz 0)
  obtain ⟨n, hn⟩ := MDEstimates.projScale_eq_zero_imp L hb₀L hb₀0 hmin₀ (hfL 1) (hz 1)
  have hf0 : f 0 ≠ 0 := hfI.ne_zero 0
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hm; exact hf0 hm
  have hrel : ∑ i : Fin 2, (![n, -m] : Fin 2 → ℤ) i • f i = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hstep : n • f 0 + (-m) • f 1 = (n * m) • b₀ + ((-m) * n) • b₀ := by
      rw [hm, hn, smul_smul, smul_smul]
    rw [hstep, mul_comm n m, neg_mul, neg_smul, add_neg_cancel]
  have hg := (Fintype.linearIndependent_iff.mp hfI) ![n, -m] hrel
  have h2 := hg 1
  simp only [Matrix.cons_val_one] at h2
  exact hm0 (neg_eq_zero.mp h2)

/-! ## 4. The minimal distance to `ℝb₀` is at most `λ₂` -/

/-- **The minimal distance to `ℝb₀` is at most `λ₂`.**  If `b₀` is a shortest nonzero vector of
`L` and `b₁` minimises `‖projScale b₀ ·‖` over the vectors of `L` with `projScale b₀ · ≠ 0`,
then `‖projScale b₀ b₁‖ ≤ ‖b₀‖² λ₂(L)`. -/
lemma dist_proj_le_lam_two (L : Submodule ℤ (ι → ℤ)) {b₀ b₁ : ι → ℤ} (hb₀L : b₀ ∈ L)
    (hb₀0 : b₀ ≠ 0) (hmin₀ : ∀ x ∈ L, x ≠ 0 → eNorm b₀ ≤ eNorm x) (hb₁L : b₁ ∈ L)
    (hmin₁ : ∀ x ∈ L, projScale b₀ x ≠ 0 →
      eNorm (projScale b₀ b₁) ≤ eNorm (projScale b₀ x))
    (hrk : 2 ≤ rk L) :
    eNorm (projScale b₀ b₁) ≤ eNorm b₀ ^ 2 * lam L 2 := by
  have hb₀pos : 0 < eNorm b₀ ^ 2 := by
    have := eNorm_pos_of_ne_zero hb₀0
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ρ : ℝ := lam L 2 + ε / eNorm b₀ ^ 2 with hρ
  have hρgt : lam L 2 < ρ := by
    rw [hρ]; have := div_pos hε hb₀pos; linarith
  obtain ⟨f, hfL, hfI, hfn⟩ := lam_witness L hrk (ρ := ρ) hρgt
  have hsome : projScale b₀ (f 0) ≠ 0 ∨ projScale b₀ (f 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact not_both_projScale_zero hb₀L hb₀0 hmin₀ hfL hfI (fun i => by
      fin_cases i
      · exact hcon.1
      · exact hcon.2)
  have key : ∀ i : Fin 2, projScale b₀ (f i) ≠ 0 →
      eNorm (projScale b₀ b₁) ≤ eNorm b₀ ^ 2 * ρ := by
    intro i hi
    have h1 := hmin₁ (f i) (hfL i) hi
    have h2 : eNorm (projScale b₀ (f i)) ≤ eNorm b₀ ^ 2 * eNorm (f i) :=
      eNorm_projScale_le' b₀ (f i)
    have h3 : eNorm (f i) ≤ ρ := hfn i
    have h4 : eNorm b₀ ^ 2 * eNorm (f i) ≤ eNorm b₀ ^ 2 * ρ :=
      mul_le_mul_of_nonneg_left h3 hb₀pos.le
    linarith
  have hfin : eNorm (projScale b₀ b₁) ≤ eNorm b₀ ^ 2 * ρ := by
    rcases hsome with h | h
    · exact key 0 h
    · exact key 1 h
  have hsplit : eNorm b₀ ^ 2 * ρ = eNorm b₀ ^ 2 * lam L 2 + ε := by
    rw [hρ, mul_add, mul_div_cancel₀ _ (ne_of_gt hb₀pos)]
  rw [hsplit] at hfin
  exact hfin

/-! ## 5. Pythagoras for a normalised two-step decomposition -/

/-- **Pythagoras with a normalised second coefficient.**  Let `U ≠ 0` and `W` satisfy
`|⟪W,U⟫| ≤ ‖U‖²/2`.  Then for all real `t₁, t₂`,
`|t₂| ‖π_{U^⊥}W‖ ≤ ‖t₁U + t₂W‖` and `|t₁| ‖U‖ ≤ ‖t₁U + t₂W‖ + |t₂| ‖U‖/2`. -/
lemma projU_coord_bounds {U W : EuclideanSpace ℝ ι} (hU : U ≠ 0)
    (hW : |inner ℝ W U| ≤ ‖U‖ ^ 2 / 2) (t₁ t₂ : ℝ) :
    |t₂| * ‖Work.HP.projU U W‖ ≤ ‖t₁ • U + t₂ • W‖ ∧
    |t₁| * ‖U‖ ≤ ‖t₁ • U + t₂ • W‖ + |t₂| * ‖U‖ / 2 := by
  have hUp : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hU2 : 0 < ‖U‖ ^ 2 := by positivity
  set c : ℝ := inner ℝ W U / ‖U‖ ^ 2 with hc
  have hcabs : |c| ≤ 1 / 2 := by
    rw [hc, abs_div, abs_of_pos hU2, div_le_iff₀ hU2]
    linarith [hW]
  have hdecomp : t₁ • U + t₂ • W = t₂ • (Work.HP.projU U W) + (t₁ + t₂ * c) • U := by
    rw [Work.HP.projU_apply, hc, div_eq_inv_mul]
    module
  have hpyth : ‖t₁ • U + t₂ • W‖ ^ 2
      = (t₂ * ‖Work.HP.projU U W‖) ^ 2 + ((t₁ + t₂ * c) * ‖U‖) ^ 2 := by
    rw [hdecomp, ← map_smul]
    rw [Work.HP.norm_sq_add_smul' U (t₁ + t₂ * c) (t₂ • W)]
    rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hZnn : 0 ≤ ‖t₁ • U + t₂ • W‖ := norm_nonneg _
  constructor
  · have h1 : (|t₂| * ‖Work.HP.projU U W‖) ^ 2 ≤ ‖t₁ • U + t₂ • W‖ ^ 2 := by
      rw [hpyth, show (|t₂| * ‖Work.HP.projU U W‖) ^ 2
          = (t₂ * ‖Work.HP.projU U W‖) ^ 2 by rw [mul_pow, mul_pow, sq_abs]]
      nlinarith [sq_nonneg ((t₁ + t₂ * c) * ‖U‖)]
    nlinarith [h1, hZnn, mul_nonneg (abs_nonneg t₂) (norm_nonneg (Work.HP.projU U W))]
  · have h1 : ((t₁ + t₂ * c) * ‖U‖) ^ 2 ≤ ‖t₁ • U + t₂ • W‖ ^ 2 := by
      rw [hpyth]; nlinarith [sq_nonneg (t₂ * ‖Work.HP.projU U W‖)]
    have h2 : |(t₁ + t₂ * c) * ‖U‖| ≤ ‖t₁ • U + t₂ • W‖ := by
      have := sq_le_sq.mp h1
      rwa [abs_of_nonneg hZnn] at this
    rw [abs_mul, abs_of_pos hUp] at h2
    have h3 : |t₁| ≤ |t₁ + t₂ * c| + |t₂| / 2 := by
      have h3a : |t₁| ≤ |t₁ + t₂ * c| + |t₂ * c| := by
        calc |t₁| = |(t₁ + t₂ * c) - t₂ * c| := by ring_nf
          _ ≤ |t₁ + t₂ * c| + |t₂ * c| := by
              have := abs_sub_le (t₁ + t₂ * c) 0 (t₂ * c)
              simpa using this
      have h3b : |t₂ * c| ≤ |t₂| / 2 := by
        rw [abs_mul]
        have := mul_le_mul_of_nonneg_left hcabs (abs_nonneg t₂)
        linarith
      linarith
    have h4 : |t₁| * ‖U‖ ≤ |t₁ + t₂ * c| * ‖U‖ + |t₂| * ‖U‖ / 2 := by
      have h5 := mul_le_mul_of_nonneg_right h3 hUp.le
      linarith
    linarith [h2, h4]

/-! ## 6. Real arithmetic for the coefficient bounds -/

/-- **Arithmetic of the coefficient bounds.**  With `l₂ ≤ l₃`, `τ₁ ≤ l₂`, `τ₁ ≥ (√3/2)l₂`,
`τ₂ ≥ (3/4)l₃`, and the two coefficient estimates `|t₁|τ₁ ≤ B(1 + τ₁/(2τ₂))`,
`|t₂|τ₂ ≤ B`, one gets `t₁²l₂² ≤ 16B²` and `t₂²l₃² ≤ 16B²`. -/
lemma arith_bounds {l₂ l₃ τ₁ τ₂ B : ℝ} (hl2 : 0 < l₂) (hl23 : l₂ ≤ l₃) (hτ2 : 0 < τ₂)
    (hB : 0 ≤ B) (hτ1l : Real.sqrt 3 / 2 * l₂ ≤ τ₁) (hτ1u : τ₁ ≤ l₂)
    (hτ2l : 3 / 4 * l₃ ≤ τ₂) {t₁ t₂ : ℝ}
    (ht1 : |t₁| * τ₁ ≤ B * (1 + τ₁ / (2 * τ₂))) (ht2 : |t₂| * τ₂ ≤ B) :
    t₁ ^ 2 * l₂ ^ 2 ≤ 16 * B ^ 2 ∧ t₂ ^ 2 * l₃ ^ 2 ≤ 16 * B ^ 2 := by
  have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hl3 : 0 < l₃ := lt_of_lt_of_le hl2 hl23
  have hτ1nn : 0 ≤ τ₁ := by nlinarith [hτ1l, hl2, hs3]
  have hratio : τ₁ / (2 * τ₂) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hτ1u, hl23, hτ2l, hτ2]
  have hl2τ : l₂ ≤ 2 / Real.sqrt 3 * τ₁ := by
    have h := mul_le_mul_of_nonneg_left hτ1l (show (0:ℝ) ≤ 2 / Real.sqrt 3 by positivity)
    have h2 : 2 / Real.sqrt 3 * (Real.sqrt 3 / 2 * l₂) = l₂ := by field_simp
    rwa [h2] at h
  constructor
  · have h1 : |t₁| * l₂ ≤ 2 / Real.sqrt 3 * (B * (1 + τ₁ / (2 * τ₂))) := by
      have h2 : |t₁| * l₂ ≤ |t₁| * (2 / Real.sqrt 3 * τ₁) :=
        mul_le_mul_of_nonneg_left hl2τ (abs_nonneg t₁)
      have h3 : |t₁| * (2 / Real.sqrt 3 * τ₁) = 2 / Real.sqrt 3 * (|t₁| * τ₁) := by ring
      rw [h3] at h2
      have h4 : 2 / Real.sqrt 3 * (|t₁| * τ₁) ≤ 2 / Real.sqrt 3 * (B * (1 + τ₁ / (2 * τ₂))) :=
        mul_le_mul_of_nonneg_left ht1 (by positivity)
      linarith
    have h5 : 1 + τ₁ / (2 * τ₂) ≤ 5 / 3 := by linarith
    have h6 : B * (1 + τ₁ / (2 * τ₂)) ≤ B * (5 / 3) := mul_le_mul_of_nonneg_left h5 hB
    have h7 : |t₁| * l₂ ≤ 2 / Real.sqrt 3 * (B * (5 / 3)) := by
      have h8 : 2 / Real.sqrt 3 * (B * (1 + τ₁ / (2 * τ₂))) ≤ 2 / Real.sqrt 3 * (B * (5 / 3)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      linarith
    have h9 : (|t₁| * l₂) ^ 2 ≤ 16 * B ^ 2 := by
      have h10 : (2 / Real.sqrt 3 * (B * (5 / 3))) ^ 2 ≤ 16 * B ^ 2 := by
        have h11 : (2 / Real.sqrt 3 * (B * (5 / 3))) ^ 2 = 100 / 27 * B ^ 2 := by
          rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
          ring
        rw [h11]; nlinarith [sq_nonneg B]
      have h12 : (|t₁| * l₂) ^ 2 ≤ (2 / Real.sqrt 3 * (B * (5 / 3))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h7 2
      linarith
    rwa [mul_pow, sq_abs] at h9
  · have h1 : |t₂| * l₃ ≤ 4 / 3 * (|t₂| * τ₂) := by
      have h2 : |t₂| * (3 / 4 * l₃) ≤ |t₂| * τ₂ := mul_le_mul_of_nonneg_left hτ2l (abs_nonneg t₂)
      linarith
    have h2 : |t₂| * l₃ ≤ 4 / 3 * B := by
      have h3 : 4 / 3 * (|t₂| * τ₂) ≤ 4 / 3 * B := mul_le_mul_of_nonneg_left ht2 (by norm_num)
      linarith
    have h4 : (|t₂| * l₃) ^ 2 ≤ 16 * B ^ 2 := by
      have h5 : (4 / 3 * B) ^ 2 ≤ 16 * B ^ 2 := by nlinarith [sq_nonneg B]
      have h6 : (|t₂| * l₃) ^ 2 ≤ (4 / 3 * B) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      linarith
    rwa [mul_pow, sq_abs] at h4

/-! ## 7. Linear independence and saturation of the Davenport triple -/

/-- The three vectors of a Davenport triple are `ℤ`-linearly independent, since the two scaled
projections kill `b₀`, then `u = projScale b₀ b₁`, but not `v = projScale u (projScale b₀ b₂)`. -/
lemma linIndep_of_geom {b₀ b₁ b₂ : ι → ℤ} (hne₀ : b₀ ≠ 0) (hne₁ : projScale b₀ b₁ ≠ 0)
    (hne₂ : projScale (projScale b₀ b₁) (projScale b₀ b₂) ≠ 0) :
    LinearIndependent ℤ ![b₀, b₁, b₂] := by
  have hsplit : ∀ c : Fin 3 → ℤ,
      (∑ i, c i • (![b₀, b₁, b₂] : Fin 3 → ι → ℤ) i) = c 0 • b₀ + c 1 • b₁ + c 2 • b₂ := by
    intro c
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • b₀ + c 1 • b₁ + c 2 • b₂ = 0 := by rw [← hsplit c]; exact hc
  have hc2 : c 2 = 0 := by
    have hproj : projScale (projScale b₀ b₁)
        (projScale b₀ (c 0 • b₀ + c 1 • b₁ + c 2 • b₂)) = 0 := by
      rw [hc', map_zero, map_zero]
    simp only [map_add, map_smul] at hproj
    rw [projScale_self_apply b₀, map_zero, smul_zero, projScale_self_apply (projScale b₀ b₁),
      smul_zero, zero_add, zero_add] at hproj
    exact (smul_eq_zero.mp hproj).resolve_right hne₂
  have hc1 : c 1 = 0 := by
    have hproj : projScale b₀ (c 0 • b₀ + c 1 • b₁ + c 2 • b₂) = 0 := by
      rw [hc', map_zero]
    simp only [map_add, map_smul] at hproj
    rw [hc2, zero_smul, add_zero] at hproj
    rw [projScale_self_apply b₀, smul_zero, zero_add] at hproj
    exact (smul_eq_zero.mp hproj).resolve_right hne₁
  have hc0 : c 0 = 0 := by
    rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hc'
    exact (smul_eq_zero.mp hc').resolve_right hne₀
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

/-- `dotZ (x - m • u) u = dotZ x u - m * dotZ u u`. -/
lemma dotZ_sub_smul (x u : ι → ℤ) (m : ℤ) : dotZ (x - m • u) u = dotZ x u - m * dotZ u u := by
  rw [dotZ_apply, dotZ_apply, dotZ_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Saturation.**  Under the minimality hypotheses of the Davenport construction the three
vectors `b₀, b₁, b₂` span `L`.  Each layer is generated: `projScale b₀` realises `L/(ℤb₀)` onto a
lattice of rank `rk L - 1`, its shortest vector generates the next layer, and the same argument
applies once more to the second scaled projection. -/
lemma span_eq_of_geom (L : Submodule ℤ (ι → ℤ)) {b₀ b₁ b₂ : ι → ℤ}
    (hmem₀ : b₀ ∈ L) (hne₀ : b₀ ≠ 0) (hmin₀ : ∀ x ∈ L, x ≠ 0 → eNorm b₀ ≤ eNorm x)
    (hmem₁ : b₁ ∈ L) (hne₁ : projScale b₀ b₁ ≠ 0)
    (hmin₁ : ∀ x ∈ L, projScale b₀ x ≠ 0 → eNorm (projScale b₀ b₁) ≤ eNorm (projScale b₀ x))
    (hmem₂ : b₂ ∈ L) (hne₂ : projScale (projScale b₀ b₁) (projScale b₀ b₂) ≠ 0)
    (hmin₂ : ∀ x ∈ L, projScale (projScale b₀ b₁) (projScale b₀ x) ≠ 0 →
      eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂)) ≤
        eNorm (projScale (projScale b₀ b₁) (projScale b₀ x)))
    (hrk : rk L = 3) :
    Submodule.span ℤ ({b₀, b₁, b₂} : Set (ι → ℤ)) = L := by
  classical
  have hrk₁ : rk (Submodule.map (projScale b₀) L) = 2 := by
    rw [MDEstimates.rk_projScale L b₀ hmem₀ hne₀ hmin₀, hrk]
  have humin : ∀ y ∈ Submodule.map (projScale b₀) L, y ≠ 0 → eNorm (projScale b₀ b₁) ≤ eNorm y := by
    intro y hy hy0
    obtain ⟨z, hzL, hz⟩ := Submodule.mem_map.mp hy
    rw [← hz]
    exact hmin₁ z hzL (by rw [hz]; exact hy0)
  have hrk₂ : rk (Submodule.map (projScale (projScale b₀ b₁))
      (Submodule.map (projScale b₀) L)) = 1 := by
    rw [MDEstimates.rk_projScale (Submodule.map (projScale b₀) L) (projScale b₀ b₁)
      (Submodule.mem_map_of_mem hmem₁) hne₁ humin, hrk₁]
  have hvmin : ∀ y ∈ Submodule.map (projScale (projScale b₀ b₁))
      (Submodule.map (projScale b₀) L), y ≠ 0 →
        eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂)) ≤ eNorm y := by
    intro y hy hy0
    obtain ⟨z, hzL₁, hz⟩ := Submodule.mem_map.mp hy
    obtain ⟨z', hz'L, hz'⟩ := Submodule.mem_map.mp hzL₁
    rw [← hz, ← hz']
    exact hmin₂ z' hz'L (by rw [hz', hz]; exact hy0)
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x (rfl | rfl | rfl)
    · exact hmem₀
    · exact hmem₁
    · exact hmem₂
  · have hle : ({b₀, b₁} : Set (ι → ℤ)) ⊆ {b₀, b₁, b₂} := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    have sat2 : ∀ y ∈ L, projScale (projScale b₀ b₁) (projScale b₀ y) = 0 →
        y ∈ Submodule.span ℤ ({b₀, b₁} : Set (ι → ℤ)) := by
      intro y hyL hy
      have hyL₁ : projScale b₀ y ∈ Submodule.map (projScale b₀) L :=
        Submodule.mem_map_of_mem hyL
      obtain ⟨k, hk⟩ := MDEstimates.projScale_eq_zero_imp (Submodule.map (projScale b₀) L)
        (Submodule.mem_map_of_mem hmem₁) hne₁ humin hyL₁ hy
      have hy'' : y - k • b₁ ∈ L := L.sub_mem hyL (L.smul_mem k hmem₁)
      have hz : projScale b₀ (y - k • b₁) = 0 := by
        rw [map_sub, map_smul, hk, sub_self]
      obtain ⟨j, hj⟩ := MDEstimates.projScale_eq_zero_imp L hmem₀ hne₀ hmin₀ hy'' hz
      have hyeq : y = j • b₀ + k • b₁ := by rw [← hj]; abel
      rw [hyeq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ j (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ k (Submodule.subset_span (by simp)))
    intro x hxL
    by_cases hz : projScale (projScale b₀ b₁) (projScale b₀ x) = 0
    · exact Submodule.span_mono hle (sat2 x hxL hz)
    · have hxL₂ : projScale (projScale b₀ b₁) (projScale b₀ x) ∈
          Submodule.map (projScale (projScale b₀ b₁)) (Submodule.map (projScale b₀) L) :=
        Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hxL)
      obtain ⟨k, hk⟩ := rank_one_shortest_generates hrk₂
        (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hmem₂)) hne₂ hvmin _ hxL₂
      have hy : x - k • b₂ ∈ L := L.sub_mem hxL (L.smul_mem k hmem₂)
      have hz2 : projScale (projScale b₀ b₁) (projScale b₀ (x - k • b₂)) = 0 := by
        rw [map_sub, map_sub, map_smul, map_smul, hk, sub_self]
      have hmem := sat2 (x - k • b₂) hy hz2
      have hxdecomp : x = (x - k • b₂) + k • b₂ := by abel
      rw [hxdecomp]
      exact Submodule.add_mem _ (Submodule.span_mono hle hmem)
        (Submodule.smul_mem _ k (Submodule.subset_span (by simp)))

/-! ## 8. The Davenport triple -/

/-- The data produced by Davenport's construction for a rank-`3` lattice `L`: a shortest vector
`b₀`, a vector `b₁` minimising the distance to `ℝb₀`, and a vector `b₂` minimising the distance to
`span(b₀,b₁)` and normalised modulo `b₁`. -/
structure IsGeomTriple (L : Submodule ℤ (ι → ℤ)) (b₀ b₁ b₂ : ι → ℤ) : Prop where
  mem₀ : b₀ ∈ L
  ne₀ : b₀ ≠ 0
  min₀ : ∀ x ∈ L, x ≠ 0 → eNorm b₀ ≤ eNorm x
  mem₁ : b₁ ∈ L
  ne₁ : projScale b₀ b₁ ≠ 0
  min₁ : ∀ x ∈ L, projScale b₀ x ≠ 0 →
    eNorm (projScale b₀ b₁) ≤ eNorm (projScale b₀ x)
  mem₂ : b₂ ∈ L
  ne₂ : projScale (projScale b₀ b₁) (projScale b₀ b₂) ≠ 0
  min₂ : ∀ x ∈ L, projScale (projScale b₀ b₁) (projScale b₀ x) ≠ 0 →
    eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂)) ≤
      eNorm (projScale (projScale b₀ b₁) (projScale b₀ x))
  norm : |((dotZ (projScale b₀ b₂) (projScale b₀ b₁) : ℤ) : ℝ)| ≤
    ((dotZ (projScale b₀ b₁) (projScale b₀ b₁) : ℤ) : ℝ) / 2
  linIndep : LinearIndependent ℤ ![b₀, b₁, b₂]
  span_eq : Submodule.span ℤ ({b₀, b₁, b₂} : Set (ι → ℤ)) = L

/-- **Existence of a Davenport triple.** -/
theorem exists_geomTriple (L : Submodule ℤ (ι → ℤ)) (hL : rk L = 3) :
    ∃ b₀ b₁ b₂ : ι → ℤ, IsGeomTriple L b₀ b₁ b₂ := by
  classical
  have hLne : L ≠ ⊥ := by
    intro h; rw [h, rk] at hL; simp at hL
  obtain ⟨b₀, hb₀L, hb₀0, hmin₀⟩ := BCS.shortest_vec L hLne
  have hex : ∃ x ∈ L, projScale b₀ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨f, hfL, hfI⟩ := exists_linIndep_card L (i := 2) (by omega)
    exact not_both_projScale_zero hb₀L hb₀0 hmin₀ hfL hfI (fun i => hcon (f i) (hfL i))
  have hL₁ne : Submodule.map (projScale b₀) L ≠ ⊥ := by
    intro h
    obtain ⟨x, hxL, hxne⟩ := hex
    have hx0 : projScale b₀ x = 0 := by
      have : projScale b₀ x ∈ (⊥ : Submodule ℤ (ι → ℤ)) := by
        rw [← h]; exact Submodule.mem_map_of_mem hxL
      simpa using this
    exact hxne hx0
  obtain ⟨u, huL₁, hu0, humin⟩ := BCS.shortest_vec (Submodule.map (projScale b₀) L) hL₁ne
  obtain ⟨b₁, hb₁L, hb₁eq⟩ := Submodule.mem_map.mp huL₁
  have hrk₁ : rk (Submodule.map (projScale b₀) L) = 2 := by
    rw [MDEstimates.rk_projScale L b₀ hb₀L hb₀0 hmin₀, hL]
  have hL₂ne : Submodule.map (projScale u) (Submodule.map (projScale b₀) L) ≠ ⊥ := by
    intro h
    have h0 : rk (Submodule.map (projScale u) (Submodule.map (projScale b₀) L)) = 0 := by
      rw [h, rk]; simp
    rw [MDEstimates.rk_projScale (Submodule.map (projScale b₀) L) u huL₁ hu0 humin, hrk₁] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨v, hvL₂, hv0, hvmin⟩ := BCS.shortest_vec _ hL₂ne
  obtain ⟨w, hwL₁, hweq⟩ := Submodule.mem_map.mp hvL₂
  obtain ⟨b₂', hb₂'L, hb₂'eq⟩ := Submodule.mem_map.mp hwL₁
  let m : ℤ := ⌊inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 + 1 / 2⌋
  refine ⟨b₀, b₁, b₂' - m • b₁, ?_⟩
  have hA : projScale b₀ (b₂' - m • b₁) = w - m • u := by
    rw [map_sub, map_smul, hb₂'eq, hb₁eq]
  have hB : projScale u (projScale b₀ (b₂' - m • b₁)) = v := by
    rw [hA, map_sub, map_smul, hweq, projScale_self_apply, smul_zero, sub_zero]
  have hmclose : |inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2
      - (m : ℝ)| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 + 1 / 2 := by
      show ((⌊inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 + 1 / 2⌋ : ℤ) : ℝ) ≤ _
      exact Int.floor_le _
    have h2 : inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 + 1 / 2
        < (m : ℝ) + 1 := by
      show _ < ((⌊inner ℝ (Work.HP.toEZ w) (Work.HP.toEZ u) / ‖Work.HP.toEZ u‖ ^ 2 + 1 / 2⌋ : ℤ) : ℝ)
        + 1
      exact Int.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith
  have hbpos : 0 < ((dotZ u u : ℤ) : ℝ) := by
    rw [← norm_toE_sq_dotZ' u]
    have hne : Work.HP.toEZ u ≠ 0 := by
      rw [← norm_pos_iff, Work.HP.norm_toEZ]
      exact eNorm_pos_of_ne_zero hu0
    positivity
  have hkey : |((dotZ w u : ℤ) : ℝ) - (m : ℝ) * ((dotZ u u : ℤ) : ℝ)|
      ≤ ((dotZ u u : ℤ) : ℝ) / 2 := by
    have h1 : |((dotZ w u : ℤ) : ℝ) / ((dotZ u u : ℤ) : ℝ) - (m : ℝ)| ≤ 1 / 2 := by
      have h := hmclose
      rw [inner_toE_dotZ' w u, norm_toE_sq_dotZ' u] at h
      exact h
    have h4 : |((dotZ w u : ℤ) : ℝ) - (m : ℝ) * ((dotZ u u : ℤ) : ℝ)|
        = |((dotZ u u : ℤ) : ℝ)|
          * |((dotZ w u : ℤ) : ℝ) / ((dotZ u u : ℤ) : ℝ) - (m : ℝ)| := by
      rw [← abs_mul]
      congr 1
      field_simp
    rw [h4, abs_of_pos hbpos]
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt hbpos)
    linarith
  refine ⟨hb₀L, hb₀0, hmin₀, hb₁L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb₁eq]; exact hu0
  · intro x hxL hxne
    have h := humin (projScale b₀ x) (Submodule.mem_map_of_mem hxL) hxne
    rw [hb₁eq]; exact h
  · exact L.sub_mem hb₂'L (L.smul_mem m hb₁L)
  · rw [hb₁eq]; rw [hB]; exact hv0
  · intro x hxL hxne
    rw [hb₁eq] at hxne
    have h := hvmin (projScale u (projScale b₀ x))
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hxL)) hxne
    rw [hb₁eq]; rw [hB]; exact h
  · rw [hA, hb₁eq, dotZ_sub_smul, Int.cast_sub, Int.cast_mul]
    exact hkey
  · exact linIndep_of_geom hb₀0 (by rw [hb₁eq]; exact hu0) (by rw [hb₁eq]; rw [hB]; exact hv0)
  · refine span_eq_of_geom L hb₀L hb₀0 hmin₀ hb₁L ?_ ?_ (L.sub_mem hb₂'L (L.smul_mem m hb₁L))
      ?_ ?_ hL
    · rw [hb₁eq]; exact hu0
    · intro x hxL hxne
      have h := humin (projScale b₀ x) (Submodule.mem_map_of_mem hxL) hxne
      rw [hb₁eq]; exact h
    · rw [hb₁eq]; rw [hB]; exact hv0
    · intro x hxL hxne
      rw [hb₁eq] at hxne
      have h := hvmin (projScale u (projScale b₀ x))
        (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hxL)) hxne
      rw [hb₁eq]; rw [hB]; exact h

/-! ## 9. The coefficient bounds -/

/-- **The two coefficient bounds of a Davenport triple.**  Writing `x = t₀b₀ + t₁b₁ + t₂b₂`,
`t₁² λ₂(L)² ≤ 16‖x‖²` and `t₂² λ₃(L)² ≤ 16‖x‖²`.

The proof combines the successive-minima comparison `lam_projScale_le` for `L` and for its first
scaled projection (giving `‖projScale b₀ b₁‖ ≥ (√3/2)‖b₀‖²λ₂(L)` and
`‖projScale b₀ b₁‖ ≤ ‖b₀‖²λ₂(L)`, together with `λ₃(L) ≤ (4/3) dist(b₂, span(b₀,b₁))`)
with the Pythagoras identity for the normalised two-step decomposition. -/
theorem geomTriple_bounds (L : Submodule ℤ (ι → ℤ)) (hL : rk L = 3) {b₀ b₁ b₂ : ι → ℤ}
    (h : IsGeomTriple L b₀ b₁ b₂) (t : Fin 3 → ℤ) :
    (t 1 : ℝ) ^ 2 * lam L 2 ^ 2 ≤ 16 * eNorm (∑ j, t j • (![b₀, b₁, b₂] : Fin 3 → ι → ℤ) j) ^ 2 ∧
    (t 2 : ℝ) ^ 2 * lam L 3 ^ 2 ≤ 16 * eNorm (∑ j, t j • (![b₀, b₁, b₂] : Fin 3 → ι → ℤ) j) ^ 2 := by
  classical
  set x : ι → ℤ := ∑ j, t j • (![b₀, b₁, b₂] : Fin 3 → ι → ℤ) j with hx
  have hx' : x = t 0 • b₀ + t 1 • b₁ + t 2 • b₂ := by
    rw [hx, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  have hlam2 : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
  have hlam3 : 0 < lam L 3 := lam_pos L (by norm_num) (by omega)
  have hlam23 : lam L 2 ≤ lam L 3 := lam_mono L (by norm_num) (by omega)
  have hA2pos : 0 < eNorm b₀ ^ 2 := by
    have := eNorm_pos_of_ne_zero h.ne₀; positivity
  have huL₁ : projScale b₀ b₁ ∈ Submodule.map (projScale b₀) L :=
    Submodule.mem_map_of_mem h.mem₁
  have humin : ∀ y ∈ Submodule.map (projScale b₀) L, y ≠ 0 →
      eNorm (projScale b₀ b₁) ≤ eNorm y := by
    intro y hy hy0
    obtain ⟨z, hzL, hz⟩ := Submodule.mem_map.mp hy
    rw [← hz]
    exact h.min₁ z hzL (by rw [hz]; exact hy0)
  have hrk₁ : rk (Submodule.map (projScale b₀) L) = 2 := by
    rw [MDEstimates.rk_projScale L b₀ h.mem₀ h.ne₀ h.min₀, hL]
  have hlow1 : Real.sqrt 3 / 2 * eNorm b₀ ^ 2 * lam L 2 ≤ eNorm (projScale b₀ b₁) := by
    have hstep := lam_projScale_le' L b₀ h.mem₀ h.ne₀ h.min₀ 1 (by norm_num)
      (by omega : 1 ≤ rk L - 1)
    have h2 : lam (Submodule.map (projScale b₀) L) 1 ≤ eNorm (projScale b₀ b₁) :=
      lam_one_le_eNorm _ huL₁ h.ne₁
    linarith
  have hmid : Real.sqrt 3 / 2 * eNorm b₀ ^ 2 * lam L 3 ≤
      lam (Submodule.map (projScale b₀) L) 2 := by
    have hstep := lam_projScale_le' L b₀ h.mem₀ h.ne₀ h.min₀ 2 (by norm_num)
      (by omega : 2 ≤ rk L - 1)
    simpa using hstep
  have hlow2 : Real.sqrt 3 / 2 * eNorm (projScale b₀ b₁) ^ 2 *
      lam (Submodule.map (projScale b₀) L) 2 ≤
      eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂)) := by
    have hstep := lam_projScale_le' (Submodule.map (projScale b₀) L)
      (projScale b₀ b₁) huL₁ h.ne₁ humin 1 (by norm_num)
      (by omega : 1 ≤ rk (Submodule.map (projScale b₀) L) - 1)
    have h2 : lam (Submodule.map (projScale (projScale b₀ b₁))
        (Submodule.map (projScale b₀) L)) 1
        ≤ eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂)) :=
      lam_one_le_eNorm _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem h.mem₂)) h.ne₂
    linarith
  have hupper1 : eNorm (projScale b₀ b₁) ≤ eNorm b₀ ^ 2 * lam L 2 :=
    dist_proj_le_lam_two L h.mem₀ h.ne₀ h.min₀ h.mem₁ h.min₁ (by omega)
  set U : EuclideanSpace ℝ ι := Work.HP.toEZ (projScale b₀ b₁) with hU
  set W : EuclideanSpace ℝ ι := Work.HP.toEZ (projScale b₀ b₂) with hW
  have hUne : U ≠ 0 := by
    rw [hU, ← norm_pos_iff, Work.HP.norm_toEZ]
    exact eNorm_pos_of_ne_zero h.ne₁
  have hnormUW : |inner ℝ W U| ≤ ‖U‖ ^ 2 / 2 := by
    rw [hW, hU, inner_toE_dotZ', norm_toE_sq_dotZ']
    exact h.norm
  have hZ : Work.HP.toEZ (projScale b₀ x) = (t 1 : ℝ) • U + (t 2 : ℝ) • W := by
    have hstep : projScale b₀ x = t 1 • (projScale b₀ b₁) + t 2 • (projScale b₀ b₂) := by
      rw [hx', map_add, map_add, map_smul, map_smul, map_smul, projScale_self_apply, smul_zero,
        zero_add]
    rw [hstep]
    change Work.HP.toEHom (t 1 • (projScale b₀ b₁) + t 2 • (projScale b₀ b₂))
      = (t 1 : ℝ) • U + (t 2 : ℝ) • W
    rw [map_add, map_smul, map_smul]
    simp only [Work.HP.toEHom_apply, hU, hW, Int.cast_smul_eq_zsmul]
  have hZle : ‖Work.HP.toEZ (projScale b₀ x)‖ ≤ eNorm b₀ ^ 2 * eNorm x := by
    rw [Work.HP.norm_toEZ, eNorm_projScale' b₀ x h.ne₀, ← Work.HP.norm_toEZ x]
    exact mul_le_mul_of_nonneg_left (Work.HP.norm_projU_le (Work.HP.toEZ b₀) (Work.HP.toEZ x))
      (by positivity)
  have hcb := projU_coord_bounds hUne hnormUW (t 1 : ℝ) (t 2 : ℝ)
  have hb1 : |(t 2 : ℝ)| * ‖Work.HP.projU U W‖ ≤ eNorm b₀ ^ 2 * eNorm x := by
    rw [← hZ] at hcb
    exact hcb.1.trans hZle
  have hb2 : |(t 1 : ℝ)| * ‖U‖ ≤ eNorm b₀ ^ 2 * eNorm x + |(t 2 : ℝ)| * ‖U‖ / 2 := by
    rw [← hZ] at hcb
    linarith [hcb.2, hZle]
  have hd₂pos : 0 < ‖Work.HP.projU U W‖ := by
    have huv := eNorm_projScale' (projScale b₀ b₁) (projScale b₀ b₂) h.ne₁
    rw [← hU, ← hW] at huv
    have h2 : 0 < eNorm (projScale b₀ b₁) ^ 2 * ‖Work.HP.projU U W‖ := by
      rw [← huv]
      exact eNorm_pos_of_ne_zero h.ne₂
    exact pos_of_mul_pos_right h2 (by positivity)
  set τ₁ : ℝ := ‖U‖ / eNorm b₀ ^ 2 with hτ₁
  set τ₂ : ℝ := ‖Work.HP.projU U W‖ / eNorm b₀ ^ 2 with hτ₂
  have hτ1low : Real.sqrt 3 / 2 * lam L 2 ≤ τ₁ := by
    rw [hτ₁, hU, Work.HP.norm_toEZ, le_div_iff₀ hA2pos]
    linarith [hlow1]
  have hτ1up : τ₁ ≤ lam L 2 := by
    rw [hτ₁, hU, Work.HP.norm_toEZ, div_le_iff₀ hA2pos]
    linarith [hupper1]
  have hτ2pos : 0 < τ₂ := by rw [hτ₂]; positivity
  have hτ2low : 3 / 4 * lam L 3 ≤ τ₂ := by
    have huv : eNorm (projScale (projScale b₀ b₁) (projScale b₀ b₂))
        = eNorm (projScale b₀ b₁) ^ 2 * ‖Work.HP.projU U W‖ := by
      rw [hU, hW]
      exact eNorm_projScale' (projScale b₀ b₁) (projScale b₀ b₂) h.ne₁
    have hulor : (0:ℝ) < eNorm (projScale b₀ b₁) ^ 2 := by
      have := eNorm_pos_of_ne_zero h.ne₁; positivity
    have hstep : Real.sqrt 3 / 2 * lam (Submodule.map (projScale b₀) L) 2
        ≤ ‖Work.HP.projU U W‖ := by
      have h3 : Real.sqrt 3 / 2 * eNorm (projScale b₀ b₁) ^ 2 *
          lam (Submodule.map (projScale b₀) L) 2
          ≤ eNorm (projScale b₀ b₁) ^ 2 * ‖Work.HP.projU U W‖ := by
        rw [← huv]; exact hlow2
      have h5 : Real.sqrt 3 / 2 * lam (Submodule.map (projScale b₀) L) 2
          ≤ (eNorm (projScale b₀ b₁) ^ 2 * ‖Work.HP.projU U W‖) /
            eNorm (projScale b₀ b₁) ^ 2 :=
        (le_div_iff₀ hulor).mpr (by nlinarith [h3])
      rwa [mul_div_cancel_left₀ _ (ne_of_gt hulor)] at h5
    have hs : 0 < Real.sqrt 3 / 2 := by positivity
    have hsq : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3 / 4 := by
      have h0 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
      nlinarith [h0]
    have hmul := mul_le_mul_of_nonneg_left hmid (le_of_lt hs)
    have hcomb : 3 / 4 * (eNorm b₀ ^ 2 * lam L 3) ≤ ‖Work.HP.projU U W‖ := by
      have h1 : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2 * eNorm b₀ ^ 2 * lam L 3)
          = 3 / 4 * (eNorm b₀ ^ 2 * lam L 3) := by
        rw [show Real.sqrt 3 / 2 * (Real.sqrt 3 / 2 * eNorm b₀ ^ 2 * lam L 3)
            = (Real.sqrt 3 / 2 * (Real.sqrt 3 / 2)) * (eNorm b₀ ^ 2 * lam L 3) by ring, hsq]
      rw [← h1]
      exact hmul.trans hstep
    rw [hτ₂, le_div_iff₀ hA2pos]
    linarith [hcomb]
  have ht2 : |(t 2 : ℝ)| * τ₂ ≤ eNorm x := by
    rw [hτ₂, show |(t 2 : ℝ)| * (‖Work.HP.projU U W‖ / eNorm b₀ ^ 2)
        = (|(t 2 : ℝ)| * ‖Work.HP.projU U W‖) / eNorm b₀ ^ 2 by ring]
    rw [div_le_iff₀ hA2pos]
    linarith [hb1]
  have ht1 : |(t 1 : ℝ)| * τ₁ ≤ eNorm x * (1 + τ₁ / (2 * τ₂)) := by
    have h1 : |(t 1 : ℝ)| * τ₁ ≤ eNorm x + |(t 2 : ℝ)| * τ₁ / 2 := by
      rw [hτ₁]
      rw [show |(t 1 : ℝ)| * (‖U‖ / eNorm b₀ ^ 2)
            = (|(t 1 : ℝ)| * ‖U‖) / eNorm b₀ ^ 2 by ring,
          show |(t 2 : ℝ)| * (‖U‖ / eNorm b₀ ^ 2) / 2
            = (|(t 2 : ℝ)| * ‖U‖ / 2) / eNorm b₀ ^ 2 by ring,
          div_le_iff₀ hA2pos, add_mul, div_mul_cancel₀ _ (ne_of_gt hA2pos)]
      linarith [hb2]
    have h2 : |(t 2 : ℝ)| * τ₁ / 2 ≤ eNorm x * (τ₁ / (2 * τ₂)) := by
      have h3 : |(t 2 : ℝ)| * τ₁ / 2 = (|(t 2 : ℝ)| * τ₂) * (τ₁ / (2 * τ₂)) := by
        field_simp
      rw [h3]
      exact mul_le_mul_of_nonneg_right ht2 (by positivity)
    linarith [h1, h2]
  exact arith_bounds hlam2 hlam23 hτ2pos (eNorm_nonneg x) hτ1low hτ1up hτ2low ht1 ht2

/-! ## 10. The target theorem -/

/-- **Geometry of numbers input for `latZero_bound`** (Browning--Le Boudec--Sawin, §3.4,
the bound `N_c(Z;L) ≪ (Z/s_1)(Z/s_2)` in the non-degenerate case `L ∈ T_{3,4}`).

There is an absolute constant `K` such that every rank-`3` sublattice `L ⊆ ℤ^5` possesses an
ordered `ℤ`-basis `b = (b₀,b₁,b₂)` with the following *coefficient bounds*: writing an element of
`L` as `x = t₀b₀ + t₁b₁ + t₂b₂` with `t ∈ ℤ³`, we have `t₁² λ₂(L)² ≤ K ‖x‖²` and
`t₂² λ₃(L)² ≤ K ‖x‖²`, where `λ_j(L) = lam L j` is the `j`-th successive minimum of `L` for the
Euclidean unit ball.  (`K = 16` suffices.)

Proof route (Davenport's construction).  Take `b₀ ∈ L∖{0}` of minimal norm
(`eNorm b₀ = lam L 1`); let `π₀ = projPerp (toEZ b₀)` and `π₀₁ = projPerp (π₀ b₁) ∘ π₀`.  Let
`b₁ ∈ L∖ℝb₀` minimise `‖π₀ ‖` and `b₂ ∈ L∖span(b₀,b₁)` minimise `‖π₀₁‖`; after replacing `b₂` by
`b₂ - m b₁` with `m` nearest to the `π₀(b₁)`-coefficient of `π₀(b₂)`, the three vectors form a
`ℤ`-basis of `L` (each is "saturated": a non-integral real coefficient would produce a shorter
projection, contradicting the minimality).  Finally `‖π₀ b₁‖ ≥ λ₂/2` (lifting lemma: reduce a
short `x ∉ ℝb₀` modulo `b₀` and contradict `λ₂`) and `‖π₀₁ b₂‖ ≥ λ₃/4` (reduce further modulo
`b₁` and contradict `λ₃`), whence `|t₂|‖π₀₁(b₂)‖ ≤ ‖x‖` and `|t₁|‖π₀(b₁)‖ ≤ ‖x‖ + |t₂|/2` give the
two bounds. -/
theorem latZeroGeom :
    ∃ K : ℝ, 0 < K ∧
    ∀ (L : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk L = 3 →
      ∃ b : Fin 3 → (Fin 5 → ℤ),
        LinearIndependent ℤ b ∧
        Submodule.span ℤ (Set.range b) = L ∧
        ∀ t : Fin 3 → ℤ,
          (t 1 : ℝ) ^ 2 * Work.HP.lam L 2 ^ 2 ≤ K * Work.HP.eNorm (∑ j, t j • b j) ^ 2 ∧
          (t 2 : ℝ) ^ 2 * Work.HP.lam L 3 ^ 2 ≤ K * Work.HP.eNorm (∑ j, t j • b j) ^ 2 := by
  refine ⟨16, by norm_num, ?_⟩
  intro L hL
  obtain ⟨b₀, b₁, b₂, h⟩ := exists_geomTriple L hL
  have hrange : Set.range (![b₀, b₁, b₂] : Fin 3 → (Fin 5 → ℤ)) = {b₀, b₁, b₂} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  refine ⟨![b₀, b₁, b₂], h.linIndep, ?_, ?_⟩
  · rw [hrange, h.span_eq]
  · intro t
    exact geomTriple_bounds L hL h t

end Work.HP.Q44Child
