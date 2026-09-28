import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.EE.wedgeNorm_veronese
import Submission.Work.HP.EEupper.gcdMinors_veronese
import Submission.Work.HP.evaldefs
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.span_pair_lattice

/-!
# `Work.HP.detGam_pt`: the pointwise bounds for `det Γ_{x,y}`

Browning--Le Boudec--Sawin, "Lemma upper and lower bounds det" (Annals 2023): for primitive
`x, y ∈ ℤ^{n+1}` with `x ≠ ±y`, there is an absolute constant `C` (depending only on `d, n`) with

* `1 / det Γ_{x,y} ≤ C / (𝔡₂(x,y) ‖x‖^{d-1} ‖y‖^{d-1})`, and
* `Δ(x,y) · 𝔡₂(x,y) ≤ C ‖x‖ ‖y‖`,

where `Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)} = Gam d n x y`, `𝔡₂(x,y) = dmin 2 {x,y}` and
`Δ(x,y) = ‖ν(x)‖‖ν(y)‖ / ‖ν(x) ∧ ν(y)‖`.

The ingredients are
* `det_gam_gen`: `det(Γ_{x,y}) = ‖ν(x)∧ν(y)‖ / 𝓖(νx,νy)` and `𝔡₂(x,y) = ‖x∧y‖ / 𝓖(x,y)`;
* `EEupper.gcdMinors_veronese` (Lemma G): `𝓖(νx,νy) = 𝓖(x,y)`;
* `EE.wedgeNorm_veronese`: `‖ν(x)∧ν(y)‖ ≫ ‖x‖^{d-1}‖y‖^{d-1}‖x∧y‖`;
* `𝓖(x,y) ≥ 1` and `𝔡₂(x,y) ≥ 1`, plus `‖ν(x)‖ ≪ ‖x‖^d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Finset

namespace Work.HP

/-! ## Elementary auxiliary facts -/

section Aux

variable {ι : Type*} [Fintype ι]

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
private lemma one_le_eNorm_of_ne_zero' {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi0 : v i ≠ 0 := by simpa using hi
  have hi' : (1 : ℝ) ≤ ((v i : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |v i| := by
      have h2 : (0 : ℤ) < |v i| := abs_pos.mpr hi0
      omega
    have h3 : (1 : ℝ) ≤ |((v i : ℤ) : ℝ)| := by exact_mod_cast h1
    rw [← sq_abs]
    nlinarith [abs_nonneg ((v i : ℤ) : ℝ)]
  have hle : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  rw [eNorm]
  exact (Real.one_le_sqrt).mpr (le_trans hi' hle)

end Aux

section Aux2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `1 ≤ 𝔡₂(x,y)` for `ℤ`-linearly independent `x, y`: every rank-two lattice containing `x, y`
has covolume at least `1`. -/
private lemma one_le_dmin_two' (x y : ι → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    1 ≤ dmin 2 ({x, y} : Set (ι → ℤ)) := by
  rw [dmin]
  refine le_csInf ⟨detL (Submodule.span ℤ (Set.range ![x, y])),
    Submodule.span ℤ (Set.range ![x, y]), ?_, ?_, rfl⟩ ?_
  · rw [rk, Module.finrank_eq_card_basis (Module.Basis.span h)]; simp
  · rintro z (rfl | rfl)
    · exact Submodule.subset_span (Set.mem_range_self 0)
    · exact Submodule.subset_span (Set.mem_range_self 1)
  · rintro D ⟨L, -, -, rfl⟩
    exact Lat.detL_ge_one L

end Aux2

/-! ## The upper bound `‖ν(x)‖ ≪ ‖x‖^d` -/

/-- For a real vector, `‖ν_{d,n}(u)‖ ≤ √(N_{d,n}) · ‖u‖^d`: monomial by monomial,
`|u^m| ≤ ‖u‖^d`. -/
private lemma rNorm_veronese_upper' (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    rNorm (veronese d n u) ≤ Real.sqrt (NN d n) * rNorm u ^ d := by
  set R := rNorm u with hR
  have hR0 : 0 ≤ R := rNorm_nonneg u
  have hcoord : ∀ i, |u i| ≤ R := fun i => abs_coord_le_rNorm u i
  have hbnd : ∀ m : Mon d n, |veronese d n u m| ≤ R ^ d := by
    intro m
    have h := abs_prod_pow_le (fun i => (m.1 i : ℕ)) u hcoord
    rw [m.2] at h
    simpa [veronese] using h
  have hsum : ∑ m, (veronese d n u m) ^ 2 ≤ (NN d n : ℝ) * (R ^ d) ^ 2 := by
    calc ∑ m, (veronese d n u m) ^ 2 ≤ ∑ _m : Mon d n, (R ^ d) ^ 2 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hbnd m) 2
      _ = (NN d n : ℝ) * (R ^ d) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc rNorm (veronese d n u) = Real.sqrt (∑ m, (veronese d n u m) ^ 2) := rfl
    _ ≤ Real.sqrt ((NN d n : ℝ) * (R ^ d) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (NN d n) * Real.sqrt ((R ^ d) ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
    _ = Real.sqrt (NN d n) * R ^ d := by rw [Real.sqrt_sq (pow_nonneg hR0 d)]

/-- There is a constant `c > 0` with `‖ν_{d,n}(x)‖ ≤ c ‖x‖^d` for every integer vector. -/
private lemma veronese_eNorm_upper' (d n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin (n + 1) → ℤ, eNorm (veronese d n x) ≤ c * eNorm x ^ d := by
  have hNN : (0 : ℝ) < NN d n := by
    have h := one_le_NN d n
    exact_mod_cast (by omega : (0 : ℕ) < NN d n)
  refine ⟨Real.sqrt (NN d n), Real.sqrt_pos_of_pos hNN, fun x => ?_⟩
  rw [← rNorm_veronese_toR d n x, eNorm_eq_rNorm_toR_W x]
  exact rNorm_veronese_upper' d n (toR x)

/-! ## The pointwise bounds -/

theorem detGam_pt (d n : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → x ≠ y → x ≠ -y →
      (1 / detL (Gam d n x y)
          ≤ C / (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1)
              * eNorm y ^ (d - 1))) ∧
      (DeltaXY d n x y * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ C * (eNorm x * eNorm y)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hcpos, hc⟩ := EE.wedgeNorm_veronese d n hd
  obtain ⟨c₂, hc₂pos, hc₂⟩ := veronese_eNorm_upper' d n
  have hCpos : 0 < max (1 / c) (c₂ ^ 2 / c) :=
    lt_of_lt_of_le (one_div_pos.mpr hcpos) (le_max_left _ _)
  refine ⟨max (1 / c) (c₂ ^ 2 / c), hCpos, ?_⟩
  intro x y hx hy h1 h2
  have hind : LinearIndependent ℤ ![x, y] := Sig2.li_of_prim_ne_pm x y hx hy h1 h2
  have hnu : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy h1 h2
  have hdet : detL (Gam d n x y)
      = wedgeNorm (veronese d n x) (veronese d n y) / (gcdMinors2 x y : ℝ) := by
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl,
      (det_gam_gen (veronese d n x) (veronese d n y) hnu).1,
      EEupper.gcdMinors_veronese d n hd1 x y hx hy]
  have hdmin : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
      = wedgeNorm x y / (gcdMinors2 x y : ℝ) := by
    rw [(det_gam_gen x y hind).2, (det_gam_gen x y hind).1]
  have hgpos : 0 < (gcdMinors2 x y : ℝ) := by
    exact_mod_cast DGG.gcdMinors2_pos x y hind
  have hg1 : 1 ≤ (gcdMinors2 x y : ℝ) := by
    have h : (1 : ℤ) ≤ gcdMinors2 x y := by
      have hp := DGG.gcdMinors2_pos x y hind
      omega
    exact_mod_cast h
  have hWv_eq : wedgeNorm (veronese d n x) (veronese d n y)
      = (gcdMinors2 x y : ℝ) * detL (Gam d n x y) := by
    rw [hdet, mul_div_cancel₀ _ (ne_of_gt hgpos)]
  have hW_eq : wedgeNorm x y
      = (gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
    rw [hdmin, mul_div_cancel₀ _ (ne_of_gt hgpos)]
  have hx1 : 1 ≤ eNorm x := one_le_eNorm_of_ne_zero' (isPrim_ne_zero hx)
  have hy1 : 1 ≤ eNorm y := one_le_eNorm_of_ne_zero' (isPrim_ne_zero hy)
  have hx0 : 0 < eNorm x := lt_of_lt_of_le zero_lt_one hx1
  have hy0 : 0 < eNorm y := lt_of_lt_of_le zero_lt_one hy1
  have hXne : eNorm x ^ (d - 1) ≠ 0 := ne_of_gt (pow_pos hx0 _)
  have hYne : eNorm y ^ (d - 1) ≠ 0 := ne_of_gt (pow_pos hy0 _)
  have hXYpos : 0 < eNorm x ^ (d - 1) * eNorm y ^ (d - 1) :=
    mul_pos (pow_pos hx0 _) (pow_pos hy0 _)
  have hDpos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le zero_lt_one (one_le_dmin_two' x y hind)
  -- the crucial multiplicative lower bound for `det Γ`
  have hkey : c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
      * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))) ≤ detL (Gam d n x y) := by
    have h := hc x y
    rw [hW_eq, hWv_eq] at h
    have h2 : (gcdMinors2 x y : ℝ) * (c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1)))) ≤ (gcdMinors2 x y : ℝ) * detL (Gam d n x y) := by
      nlinarith [h]
    exact (mul_le_mul_iff_of_pos_left hgpos).mp h2
  constructor
  · -- (i) the reciprocal determinant bound
    have hprod : 0 < c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))) :=
      mul_pos hcpos (mul_pos hDpos hXYpos)
    have step1 : 1 / detL (Gam d n x y) ≤ 1 / (c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1)))) :=
      one_div_le_one_div_of_le hprod hkey
    have hZn : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) :=
      mul_pos (mul_pos hDpos (pow_pos hx0 _)) (pow_pos hy0 _)
    have step2 : 1 / (c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))))
        ≤ max (1 / c) (c₂ ^ 2 / c) / (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)) := by
      have heq : 1 / (c * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))))
          = (1 / c) / (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
            * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)) := by
        rw [div_div]
        congr 1
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hZn)
    linarith [step1, step2]
  · -- (ii) the `Delta` bound
    have hnum : eNorm (veronese d n x) * eNorm (veronese d n y)
        * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        ≤ (c₂ * eNorm x ^ d) * (c₂ * eNorm y ^ d)
          * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
      have hmul : eNorm (veronese d n x) * eNorm (veronese d n y)
          ≤ (c₂ * eNorm x ^ d) * (c₂ * eNorm y ^ d) :=
        mul_le_mul (hc₂ x) (hc₂ y) (eNorm_nonneg _) (mul_nonneg hc₂pos.le (pow_nonneg (eNorm_nonneg x) d))
      exact mul_le_mul_of_nonneg_right hmul hDpos.le
    have hden : 0 < c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))) :=
      mul_pos hcpos (mul_pos (mul_pos hgpos hDpos) hXYpos)
    have hle : c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1)))
        ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
      have h := hc x y
      rw [hW_eq] at h
      nlinarith [h]
    have hDelta : DeltaXY d n x y * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        = eNorm (veronese d n x) * eNorm (veronese d n y)
          * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          / wedgeNorm (veronese d n x) (veronese d n y) := by
      rw [DeltaXY]; ring
    rw [hDelta]
    have hstep1 : eNorm (veronese d n x) * eNorm (veronese d n y)
        * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        / wedgeNorm (veronese d n x) (veronese d n y)
        ≤ eNorm (veronese d n x) * eNorm (veronese d n y)
          * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          / (c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
            * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1)))) :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (eNorm_nonneg _) (eNorm_nonneg _)) hDpos.le) hden hle
    have hstep2 : eNorm (veronese d n x) * eNorm (veronese d n y)
        * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        / (c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))))
        ≤ (c₂ * eNorm x ^ d) * (c₂ * eNorm y ^ d)
          * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          / (c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
            * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1)))) :=
      div_le_div_of_nonneg_right hnum hden.le
    have hfinal : (c₂ * eNorm x ^ d) * (c₂ * eNorm y ^ d)
        * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
        / (c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))))
        ≤ max (1 / c) (c₂ ^ 2 / c) * (eNorm x * eNorm y) := by
      have hdx : eNorm x ^ d = eNorm x ^ (d - 1) * eNorm x := by
        rw [← pow_succ, Nat.sub_add_cancel hd1]
      have hdy : eNorm y ^ d = eNorm y ^ (d - 1) * eNorm y := by
        rw [← pow_succ, Nat.sub_add_cancel hd1]
      rw [hdx, hdy]
      have hcancel : (c₂ * (eNorm x ^ (d - 1) * eNorm x)) * (c₂ * (eNorm y ^ (d - 1) * eNorm y))
          * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
          / (c * ((gcdMinors2 x y : ℝ) * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
            * (eNorm x ^ (d - 1) * eNorm y ^ (d - 1))))
          = c₂ ^ 2 * (eNorm x * eNorm y) / (c * (gcdMinors2 x y : ℝ)) := by
        field_simp
      rw [hcancel]
      have hcg : 0 < c * (gcdMinors2 x y : ℝ) := mul_pos hcpos hgpos
      have hxy : 0 < eNorm x * eNorm y := mul_pos hx0 hy0
      have hbound : c₂ ^ 2 * (eNorm x * eNorm y) / (c * (gcdMinors2 x y : ℝ))
          ≤ (c₂ ^ 2 / c) * (eNorm x * eNorm y) := by
        have hinv : 1 / (c * (gcdMinors2 x y : ℝ)) ≤ 1 / c :=
          one_div_le_one_div_of_le hcpos (le_mul_of_one_le_right hcpos.le hg1)
        calc c₂ ^ 2 * (eNorm x * eNorm y) / (c * (gcdMinors2 x y : ℝ))
            = c₂ ^ 2 * (eNorm x * eNorm y) * (1 / (c * (gcdMinors2 x y : ℝ))) := by ring
          _ ≤ c₂ ^ 2 * (eNorm x * eNorm y) * (1 / c) :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = (c₂ ^ 2 / c) * (eNorm x * eNorm y) := by ring
      have hC2 : c₂ ^ 2 / c ≤ max (1 / c) (c₂ ^ 2 / c) := le_max_right _ _
      have h2 : (c₂ ^ 2 / c) * (eNorm x * eNorm y)
          ≤ max (1 / c) (c₂ ^ 2 / c) * (eNorm x * eNorm y) :=
        mul_le_mul_of_nonneg_right hC2 hxy.le
      linarith [hbound, h2]
    linarith [hstep1, hstep2, hfinal]

end Work.HP
