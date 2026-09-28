import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.lamR_witness
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Vero.lamR_dual_Gam_two
import Submission.Work.HP.Vero.lam_Gam_veronese_le
import Submission.Work.HP.HP3.discreteTopology_realify
import Submission.Work.HP.Transf.lamR_dual_le
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.exists_rk_three
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.lam_attained

/-!
# The two-vector key lemma (`Work.HP.Sig2.key_lemma_two_vectors`)

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 197 (2023),
Lemma "Key lemma two vectors": for `d, n ≥ 2` and primitive `x, y ∈ ℤ^{n+1}` which are linearly
independent,

`λ_{N_{d,n}-2}(Λ_{ν_d(x)} ∩ Λ_{ν_d(y)}) ≤ 3n² max{𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²}`,

where `Λ_v = {a : ⟨a, v⟩ = 0}`, `𝔡_r = 𝔡_r(x,y) = dmin r {x,y}` and `N_{d,n} = NN d n`.

This file proves the *sharpened-hypotheses* form requested by the caller: the hypothesis
`LinearIndependent ℤ ![x,y]` is replaced by `x ≠ y`, `x ≠ -y` (equivalent for primitive vectors,
by `li_of_prim_ne_pm`), and the constant is only asserted to exist.  The proof is assembled from
three shared pieces:

* `Vero.lamR_dual_Gam_two` : the paper's two-case lower bound for `λ₁(Γ_{x,y}*)` at `d = 2`;
* `Transf.lamR_dual_le` : a transference bound `λ_r(L) ≤ C / λ₁(L*)` (constant depending on `r`,
  which is harmless here);
* `Vero.lam_Gam_veronese_le` : the `Ψ`-lift, deducing the general `d` statement from `d = 2`.

The single quantity that has to be computed by hand is the elementary identity
`(1/3)·min{𝔡₃/𝔡₂, 𝔡₂²/(‖x‖‖y‖)} · μ(x,y) = n²`, which is `B_mul_muXY` below.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Sig2

open Work.HP

/-! ## Elementary real arithmetic -/

/-- `min a b * max a⁻¹ b⁻¹ = 1` for `a, b > 0` (so `max a⁻¹ b⁻¹ = 1/min a b`). -/
lemma min_mul_max_inv (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b * max a⁻¹ b⁻¹ = 1 := by
  rcases le_total a b with h | h
  · have h1 : b⁻¹ ≤ a⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le ha h
    rw [min_eq_left h, max_eq_left h1, mul_inv_cancel₀ (ne_of_gt ha)]
  · have h1 : a⁻¹ ≤ b⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hb h
    rw [min_eq_right h, max_eq_right h1, mul_inv_cancel₀ (ne_of_gt hb)]

/-- `rNorm` is nonnegative. -/
lemma rNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v := Real.sqrt_nonneg _

/-- `dmin` is nonnegative: it is an infimum of covolumes. -/
lemma dmin_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  have hdef : dmin r S = sInf {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ),
      rk L = r ∧ S ⊆ L ∧ detL L = D} := rfl
  rw [hdef]
  by_cases h : ({D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} :
      Set ℝ).Nonempty
  · exact le_csInf h (by rintro D ⟨L, -, -, rfl⟩; exact detL_nonneg L)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- `muXY` is nonnegative. -/
lemma muXY_nonneg (n : ℕ) (x y : Fin (n + 1) → ℤ) : 0 ≤ muXY n x y := by
  rw [muXY]
  refine mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  refine le_trans (div_nonneg (dmin_nonneg' 2 _) (dmin_nonneg' 3 _)) (le_max_left _ _)

/-- The key arithmetic identity of the `d = 2` step:
`(1/3)·min{𝔡₃/𝔡₂, 𝔡₂²/(‖x‖‖y‖)} · μ(x,y) = n²`. -/
lemma B_mul_muXY (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hx : 0 < eNorm x) (hy : 0 < eNorm y)
    (hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) :
    (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
          dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) * muXY n x y
      = (n : ℝ) ^ 2 := by
  have hA : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := div_pos hd3 hd2
  have hB : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y) :=
    div_pos (pow_pos hd2 2) (mul_pos hx hy)
  have hkey := min_mul_max_inv (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) hA hB
  have hμ : muXY n x y = 3 * (n : ℝ) ^ 2 *
      max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹ := by
    rw [muXY]
    simp only [inv_div]
  rw [hμ]
  calc (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
          dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) *
        (3 * (n : ℝ) ^ 2 * max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
          (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹)
      = (n : ℝ) ^ 2 * (min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
          (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) *
          max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
            (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹) := by
        ring
    _ = (n : ℝ) ^ 2 := by rw [hkey]; ring

/-! ## Positivity of `𝔡₂` and `𝔡₃` -/

/-- `1 ≤ dmin 2 {x,y}` for `ℤ`-linearly independent `x, y`. -/
lemma one_le_dmin_two_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : 1 ≤ dmin 2 ({x, y} : Set (ι → ℤ)) := by
  set L : Submodule ℤ (ι → ℤ) := Submodule.span ℤ ({x, y} : Set (ι → ℤ)) with hL
  have hspan : Submodule.span ℤ ({x, y} : Set (ι → ℤ))
      = Submodule.span ℤ (Set.range ![x, y]) := by
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hrk : rk L = 2 := by
    rw [hL, rk, hspan, finrank_span_eq_card h, Fintype.card_fin]
  have hsub : ({x, y} : Set (ι → ℤ)) ⊆ L := by
    rw [hL]
    exact fun z hz => Submodule.subset_span hz
  rw [dmin]
  refine le_csInf ⟨detL L, L, hrk, hsub, rfl⟩ ?_
  rintro D ⟨L', -, -, rfl⟩
  exact Lat.detL_ge_one L'

/-- `1 ≤ dmin 3 {x,y}` for `ℤ`-linearly independent `x, y` in dimension `≥ 3`. -/
lemma one_le_dmin_three_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) (hcard : 3 ≤ Fintype.card ι) :
    1 ≤ dmin 3 ({x, y} : Set (ι → ℤ)) := by
  obtain ⟨L, hLrk, hxL, hyL⟩ := Lat.exists_rk_three x y h hcard
  have hsub : ({x, y} : Set (ι → ℤ)) ⊆ L := by
    rintro z (rfl | rfl)
    · exact hxL
    · exact hyL
  rw [dmin]
  refine le_csInf ⟨detL L, L, hLrk, hsub, rfl⟩ ?_
  rintro D ⟨L', -, -, rfl⟩
  exact Lat.detL_ge_one L'

/-! ## The `d = 2` case -/

/-- The `d = 2` case of the two-vector key lemma, with a constant that is uniform in `(x,y)`:
given a transference bound with constant `C` for lattices in `Mon 2 n → ℝ`, the second successive
minimum of `Gam 2 n x y` is at most `(C/n²)·μ(x,y)`. -/
theorem lam_Gam_two_le (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C)
    (htr : ∀ L : Submodule ℤ (Mon 2 n → ℝ), DiscreteTopology L →
      NN 2 n - 2 ≤ Module.finrank ℝ (Submodule.span ℝ (L : Set (Mon 2 n → ℝ))) →
      ∃ f : Fin (NN 2 n - 2) → (Mon 2 n → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
        ∀ j, rNorm (f j) * lamR (dualLat L) 1 ≤ C)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : x ≠ y) (hxy' : x ≠ -y) :
    lam (Gam 2 n x y) (NN 2 n - 2) ≤ (C / (n : ℝ) ^ 2) * muXY n x y := by
  classical
  have hli : LinearIndependent ℤ ![x, y] := li_of_prim_ne_pm x y hx hy hxy hxy'
  have hν : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    nu_indep 2 n (by norm_num) x y hx hy hxy hxy'
  -- positivity
  have hxpos : 0 < eNorm x := eNorm_pos_iff.mpr (isPrim_ne_zero hx)
  have hypos : 0 < eNorm y := eNorm_pos_iff.mpr (isPrim_ne_zero hy)
  have hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_two_pair x y hli)
  have hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_three_pair x y hli (by rw [Fintype.card_fin]; omega))
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hBpos : 0 < 1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
      (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) :=
    mul_pos (by norm_num) (lt_min (div_pos hd3 hd2) (div_pos (pow_pos hd2 2) (mul_pos hxpos hypos)))
  -- the paper's two-case lower bound for the first minimum of the dual
  have hdual := Vero.lamR_dual_Gam_two n hn x y hx hy hli
  -- the rank of `Gam 2 n x y` and the dimension of the span of its realification
  have hrk2 : Module.finrank ℤ (Gam 2 n x y) = NN 2 n - 2 := (gam_rank_det 2 n x y hν).1
  have hdim : Module.finrank ℝ
      (Submodule.span ℝ ((realify (Gam 2 n x y) : Submodule ℤ (Mon 2 n → ℝ)) :
        Set (Mon 2 n → ℝ))) = NN 2 n - 2 := by
    have hset : ((realify (Gam 2 n x y) : Submodule ℤ (Mon 2 n → ℝ)) : Set (Mon 2 n → ℝ))
        = intCastPi '' ((Gam 2 n x y) : Set (Mon 2 n → ℤ)) := rfl
    rw [hset, Vero.finrank_span_image_intCastPi, hrk2]
  -- transference
  have hdisc : DiscreteTopology (realify (Gam 2 n x y)) := HP3.discreteTopology_realify _
  obtain ⟨f, hfL, hfLI, hfb⟩ := htr (realify (Gam 2 n x y)) hdisc (le_of_eq hdim.symm)
  -- every witness has norm at most `(C/n²)·μ`
  have hbound : ∀ j, rNorm (f j) ≤ (C / (n : ℝ) ^ 2) * muXY n x y := by
    intro j
    have h1 : rNorm (f j) * (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
        dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) ≤ C :=
      le_trans (mul_le_mul_of_nonneg_left hdual (rNorm_nonneg' (f j))) (hfb j)
    have h2 : (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
        dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) * muXY n x y
        = (n : ℝ) ^ 2 := B_mul_muXY n x y hxpos hypos hd2 hd3
    have h3 : rNorm (f j) * (n : ℝ) ^ 2 ≤ C * muXY n x y := by
      calc rNorm (f j) * (n : ℝ) ^ 2
          = rNorm (f j) * ((1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
              dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
              (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) * muXY n x y) := by
            rw [h2]
        _ = (rNorm (f j) * (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
              dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
              (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)))) * muXY n x y := by
            ring
        _ ≤ C * muXY n x y := mul_le_mul_of_nonneg_right h1 (muXY_nonneg n x y)
    rw [div_mul_eq_mul_div, le_div_iff₀ hn2]
    exact h3
  -- extract integral witnesses and bound the successive minimum
  have hmem : (C / (n : ℝ) ^ 2) * muXY n x y ∈ lamSet (Gam 2 n x y) (NN 2 n - 2) :=
    Vero.realify_subset_lamSet (Gam 2 n x y) (NN 2 n - 2)
      ⟨mul_nonneg (le_of_lt (div_pos hC hn2)) (muXY_nonneg n x y), f, hfL, hfLI, hbound⟩
  rw [lam_eq_sInf]
  exact csInf_le (bddBelow_lamSet _ _) hmem

/-! ## The main theorem -/

theorem key_lemma_two_vectors (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      lam (Gam d n x y) (NN d n - 2) ≤ C * muXY n x y := by
  have hn : 2 ≤ n := le_trans hd hdn
  -- the transference bound, uniform in `(x,y)`
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Transf.lamR_dual_le (ι := Mon 2 n) (NN 2 n - 2)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hCn : 0 < C₁ / (n : ℝ) ^ 2 := div_pos hC₁pos hn2
  refine ⟨C₁ / (n : ℝ) ^ 2, hCn, ?_⟩
  intro x y hx hy hxy hxy'
  have hli : LinearIndependent ℤ ![x, y] := li_of_prim_ne_pm x y hx hy hxy hxy'
  have hν2 : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    nu_indep 2 n (by norm_num) x y hx hy hxy hxy'
  have hrk2 : Module.finrank ℤ (Gam 2 n x y) = NN 2 n - 2 := (gam_rank_det 2 n x y hν2).1
  -- the `d = 2` bound
  have h2 : lam (Gam 2 n x y) (NN 2 n - 2) ≤ (C₁ / (n : ℝ) ^ 2) * muXY n x y :=
    lam_Gam_two_le n hn C₁ hC₁pos hC₁ x y hx hy hxy hxy'
  -- the `Ψ`-lift to general `d`
  obtain ⟨a, ha, hai, han⟩ :=
    Q44Child.lamAttained_aux (Gam 2 n x y) (i := NN 2 n - 2) (le_of_eq hrk2.symm)
  refine Vero.lam_Gam_veronese_le d n hd hn x y hx hy hli _
    (mul_nonneg (le_of_lt hCn) (muXY_nonneg n x y)) a ha hai (fun j => le_trans (han j) h2)

end Work.HP.Sig2
